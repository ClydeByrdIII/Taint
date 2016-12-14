#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Constants.h"
#include "llvm/Analysis/ProfileInfo.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/DataTypes.h"
#include <queue>
#include <set>
#include <algorithm>
#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <vector>

// #define D
#ifdef D
#define PRINT(x) llvm::errs() << x
#else
#define PRINT(x)
#endif

#define UNTAINT
#define ALLSOURCE

#define SOURCE_CONFIG_FILE "src.cfg"
#define SINK_CONFIG_FILE "sink.cfg"
#define UNTAINT_CONFIG_FILE "untaint.cfg"

// function name and # of which argument can be tainted
// -1 if var args
struct source {
    std::string name;
    int argc;
};

using namespace llvm;

namespace {
    struct taint: public ModulePass { 
        static char ID;
        taint() : ModulePass(ID) { }
        virtual bool runOnModule(Module &M) {
            
            numPaths = 0;
            MustAlias = 0;
            MayAlias = 0;
            PartialAlias = 0;
            NoAlias = 0;
            
            AA = &getAnalysis<AliasAnalysis>();
            CG = &getAnalysis<CallGraph>();

            /* TODO: ADD global instructions in to the analaysis */
            for (Module::global_iterator glob = M.global_begin(), globe = M.global_end(); glob != globe; glob++ ) {
                PRINT("Global instruction: " << *glob << "\n");
            }

            // read in source, sink, taint configuration files
            readConfigs();

            // find sources and sinks
            for (CallGraph::iterator i = CG->begin(), ie = CG->end(); i != ie; i++) {
                Function *func = const_cast<Function *>(i->first);
                
                
                // only work on source code
                if (!func || func->isDeclaration())
                    continue;

                std::string name(func->getName().str());

                // arguments 
                for (Function::arg_iterator args = func->arg_begin(), argse = func->arg_end(); args != argse; args++) {
                    Value *inst = dyn_cast<Value>(args);
                    if (inst) {
                        addToSources(*inst, name);
                    }
                }


                funcMap[name] = func;
                funcTP.push_back(func);
                pointerAnalysis(*func);
                identifySrcsAndSinks(func);
            }
           
            // get reverse topological order
            funcRTP.insert(funcRTP.begin(), funcTP.begin(), funcTP.end());
            std::reverse(funcRTP.begin(), funcRTP.end());
            
            for (std::vector<Function *>::iterator l = funcRTP.begin(), le = funcRTP.end(); l != le; l++) {
                // find path from l's srcs to l's sinks
                std::string fname = (*l)->getName().str();
                for (std::vector<Value *>::iterator I = funcSrcs[fname].begin(), IE = funcSrcs[fname].end(); I != IE; I++ ) {
                    PRINT(fname << " has " << **I << " as a source\n");
                    Instruction *v = dyn_cast<Instruction>(*I);
                    if (v)
                        taintTrack(*v);
                }

            }
		// Count Insts that propagate taint
		llvm::errs() << "# Tainting Instructions = " << taintedInstructions.size() << "\n";
        llvm::errs() << "# of Paths = " << numPaths << "\n";
		
            return false; // return true if you modified the code
        }

        void getAnalysisUsage(AnalysisUsage &AU) const {
            AU.addRequired<CallGraph>(); 
            AU.addRequired<AliasAnalysis>();
            AU.setPreservesAll();
        }

        void taintTrack(Instruction &I);
        
        void identifySrcsAndSinks(Function *);
        
        void identifySource(Instruction &I);
        
        bool isSink(std::string str);
        bool isSource(std::string str);
        void addToSources(Value &I, std::string name);
        void addToSinks(Value &I, std::string name);

        std::string get_function_name(CallInst *call);
        int getSourceOperand(std::string str); 
        bool sinkSearch(Value * I, std::string fname);

        void pointerAnalysis(Function &F);

        bool isInterestingPointer(Value *V);

        void readConfigs(void);
        void processSource(std::string line);
        void processSink(std::string line);
        void processUntaint(std::string line);

        private:
            size_t numPaths;
            CallGraph *CG;  // shows topological ordering of functions
            AliasAnalysis *AA;
            std::vector<Function *> funcTP;  // topological ordering of functions; used to reverse ordering
            std::vector<Function *> funcRTP; // reverse topological ordering of functions
            std::vector<struct source> sinks;
            std::vector<struct source> sources;
            std::vector<struct source> untaints;
            std::map<std::string, Function *> funcMap;
            std::set<Instruction *> taintedInstructions;
            std::map<Value*, std::set<Value *> > ptr2Set;
            std::map<std::string, std::vector<Value *> > funcSrcs;
            std::map<std::string, std::vector<Value *> > funcSinks;

            size_t MustAlias ;
            size_t MayAlias ;
            size_t PartialAlias;
            size_t NoAlias;

    };
}
char taint::ID = 0;
static RegisterPass<taint> X("taint", "Static Taint Analysis", false, false);

// If an instance of I being tainted is found, add it to sources and return

static void split(const std::string &s, char delim, std::vector<std::string> &elems) {
    std::stringstream ss;
    ss.str(s);
    std::string item;
    while (std::getline(ss, item, delim)) {
        elems.push_back(item);
    }
}


static std::vector<std::string> split(const std::string &s, char delim) {
    std::vector<std::string> elems;
    split(s, delim, elems);
    return elems;
}

void taint::processSource(std::string line) {
    std::vector<std::string> srcs;
    struct source src;

    srcs = split(line, ',');

    if (srcs.empty())
        return;

    if (srcs.size() == 2) {
        src.name = srcs[0];
        std::istringstream istr(srcs[1]);

        istr >> src.argc;
        sources.push_back(src);
        // Print("Source " << src.name << " tainting operand " << src.argc << "\n");
    }
}

void taint::processSink(std::string line) {
    std::vector<std::string> snks;
    struct source sink;

    snks = split(line, ',');

    if (snks.empty())
        return;

    if (snks.size() == 2) {
        sink.name = snks[0];
        std::istringstream istr(snks[1]);

        istr >> sink.argc;
        sinks.push_back(sink);
        // Print("Sink " << sink.name << " tainted operand " << sink.argc << "\n");
    }
}

void taint::processUntaint(std::string line) {
    std::vector<std::string> untnts;
    struct source untaint;

    untnts = split(line, ',');

    if (untnts.empty())
        return;

    if (untnts.size() == 2) {
        untaint.name = untnts[0];
        std::istringstream istr(untnts[1]);

        istr >> untaint.argc;
        untaints.push_back(untaint);
        // Print("Untaint " << untaint.name << " untainting operand " << untaint.argc << "\n");
    }
}

void taint::readConfigs(void) {
    std::ifstream srcFile;
    std::ifstream sinkFile;
    std::ifstream untaintFile;
    std::string line;

    // SOURCE list
    srcFile.open(SOURCE_CONFIG_FILE);

    PRINT("Source\n");

    if (!srcFile.is_open()) {
        PRINT("Error while opening " SOURCE_CONFIG_FILE " \n");
    } else {
        while(getline(srcFile, line)) {
            processSource(line);
        }
    }

    if (srcFile.bad()) {
        PRINT("Error Reading " SOURCE_CONFIG_FILE "\n");
    }

    srcFile.close();

    // Sink List
    sinkFile.open(SINK_CONFIG_FILE);

    if (!sinkFile.is_open()) {
        PRINT("Error while opening " SINK_CONFIG_FILE "\n");
    } else {
        while(getline(sinkFile, line)) {
            processSink(line);
        }
    }

    if (sinkFile.bad()) {
       PRINT("Error Reading " SINK_CONFIG_FILE " \n");
    }

    sinkFile.close();

    // Untaint List
    untaintFile.open(UNTAINT_CONFIG_FILE);

    if (!untaintFile.is_open()) {
        PRINT("Error while opening " UNTAINT_CONFIG_FILE "\n");
    } else {
        while(getline(untaintFile, line)) {
            processUntaint(line);
        }
    }

    if (untaintFile.bad()) {
        PRINT("Error Reading " UNTAINT_CONFIG_FILE "\n");
    }

    untaintFile.close();

}

void taint::identifySource(Instruction &I) {

    bool foundSource = false;
    Function *f = I.getParent()->getParent();
    std::string name = f->getName().str();

    PRINT(I << " of function " << name << " is being identified\n");

    #ifdef ALLSOURCE
    Value *v = dyn_cast<Value>(&I);
    addToSources(*v, name);
    return;
    #endif

    // check all operands for tainted source calls
    size_t operandNum = I.getNumOperands();
    for (size_t i = 0; i < operandNum; i++) {
        Value * op = I.getOperand(i);
        CallInst *call = dyn_cast<CallInst>(op);
        if (call && (isSource(get_function_name(call)))) {
            // untrusted source; I is now tainted
            Value *v = dyn_cast<Value>(&I);
            addToSources(*v, name);
            PRINT(I << " was tainted by " << *call << "\n");
            foundSource = true;
            break;
        }
    }

    // if a source hasn't been found keep looking
    if (!foundSource) {

        // look for the values being stored to a I
        for(Value::use_iterator UI = I.use_begin(), E = I.use_end(); UI != E; ++UI) {
            Instruction *User = dyn_cast<Instruction>(*UI);
            if(User) {
                if (User->getOpcode() == Instruction::Store) {
                    Value *first = User->getOperand(0);
                    // if it's not a constant it's probably used as a source of input
                    if (!dyn_cast<Constant>(first)) {
                        Instruction *var = dyn_cast<Instruction>(first);
                        if (!var) {
                            // usually means it's a function argument; which are already added
                            continue;
                        }
                        
                        // if the the value of a call is being stored see if it's from untrusted sources
                        CallInst *call = dyn_cast<CallInst>(var);
                        if (call && (isSource(get_function_name(call)))) {
                            Value *v = dyn_cast<Value>(&I);
                            addToSources(*v, name);
                            PRINT(I << " was not a constant; was tainted by " << *first << "\n");
                            return;
                        }

                    } 
                } else if (User->getOpcode() == Instruction::Call) {
                    // check if the variable is being modified by an untrusted sources
                    PRINT(I << " is used in call " << *User << "\n");

                    CallInst *call = dyn_cast<CallInst>(User);
                    if (call && (isSource(get_function_name(call)))) {
                        std::string fn(get_function_name(call));

                        // if it's scanf family functions any usage of I is possibly tainted 
                        if (!fn.compare("__isoc99_scanf") || !fn.compare("__isoc99_fscanf")) {
                            Value *v = dyn_cast<Value>(&I);
                            addToSources(*v, name);
                            break;
                        } else {

                            // check and see if I is being used as a taintable operand in the tainted source
                            int pos;
                            bool found = false;
                            int argc = getSourceOperand(get_function_name(call));
                            int num = call->getNumArgOperands();
                            for (pos = 0; pos < num; pos++) {
                                Value *operand = call->getArgOperand(pos);
                                Value *ival = dyn_cast<Value>(&I);
                                if (operand == ival) {
                                    found = true;
                                    // the arg value in the tainted sources structure is not 0 based
                                    // increment pos to align with that
                                    pos++;
                                    break;
                                }
                            }

                            // if we found tainted source and I was being used in a taintable spot
                            // end loop and return
                            if (found == true && pos == argc) {
                                 Value *v = dyn_cast<Value>(&I);
                                 addToSources(*v, name);
                                 break;
                            }
                        }
                    }
                }
            }
        }
    }
}

void taint::identifySrcsAndSinks(Function * f) {
    std::string name = f->getName().str();

    for (Function::iterator b = f->begin(); b != f->end(); b++) {
        for (BasicBlock::iterator i = b->begin(); i != b->end(); i++) { 
            // find variables that use non-constant values
            if (i->getOpcode() == Instruction::Call || i->getOpcode() == Instruction::Ret || i->getOpcode() == Instruction::Br) {
                // potentially a sink
                CallInst *call = dyn_cast<CallInst>(i);
                ReturnInst *ret = dyn_cast<ReturnInst>(i);
                BranchInst *br = dyn_cast<BranchInst>(i);

                if (call) {
                    if (!isSink(get_function_name(call)))
                        continue;
                    PRINT(*i << " is a sink call\n");
                } else if (ret) {
                    PRINT(*i << " is a return instruction\n");
                } else if (br) {
                    PRINT(*i << " is a branch instruction\n");
                }
                addToSinks(*i, name);
            } else {
                identifySource(*i);
            }
        }
    }
}

// get the function's name 
std::string taint::get_function_name(CallInst *call) {
    Function * f = call->getCalledFunction();
    if (f) 
        return f->getName().str();
    return std::string("Indirect Call");
}

// compare with list of all sinks
bool taint::isSink(std::string str) {
    size_t i;
    size_t len = sinks.size();
    for (i = 0; i < len; i++) {
        if (!(sinks[i].name.compare(str))) {
            return true;
        }
    }
    return false;
}

// compare with list of all sources
bool taint::isSource(std::string str) {
    size_t i;
    size_t len = sources.size();

    for (i = 0; i < len; i++) {
        if (!(sources[i].name.compare(str))) {
            return true;
        }
    }
    return false;
}

int taint::getSourceOperand(std::string str) {
    size_t i;
    size_t len = sources.size();
    for (i = 0; i < len; i++) {
        if (!(sources[i].name.compare(str))) {
            return sources[i].argc;
        }
    }
    return -1;
}

void taint::addToSources(Value &I, std::string name) {
    if (std::find(funcSrcs[name].begin(), funcSrcs[name].end(), &I) == funcSrcs[name].end()) {
        funcSrcs[name].push_back(&I);
    }
}

void taint::addToSinks(Value &I, std::string name) {
    if (std::find(funcSinks[name].begin(), funcSinks[name].end(), &I) == funcSinks[name].end()) {
        funcSinks[name].push_back(&I);
    }
}

void taint::taintTrack(Instruction &I) {
    std::vector<Instruction *> taint;
    std::list<Instruction *> tq;
    std::list<Instruction *> currPath;
    std::string name = I.getParent()->getParent()->getName().str();
    std::set<Instruction*> dup;

    taint.push_back(&I);
    tq.push_back(&I);
    while(!tq.empty()) {
        Instruction *node = tq.front();
        PRINT(*node << " is examined\n");
        tq.pop_front();
	if(node==NULL)
		currPath.pop_back();
	else {
		currPath.push_back(node);

		tq.push_front(NULL);
#ifdef UNTAINT
		// Untaint constant stores
		// TODO: Also conjuctions of untainted values
		if (dyn_cast<StoreInst>(node))
			if (dyn_cast<Constant>(node->getOperand(0)))
				continue;
#endif
		// enqueue all children
		for(Value::use_iterator UI = node->use_begin(), E = node->use_end(); UI != E; ++UI) {
			Instruction *user = dyn_cast<Instruction>(*UI);
            if (dup.find(user) == dup.end()){
                tq.push_front(user);
                dup.insert(user);
            }
		}

        // enqueue all aliases

        if (node->getType()->isPointerTy())  {// Add all pointer instructions.
            Value *v = dyn_cast<Value>(&(*node));
            for (std::set<Value*>::iterator it = ptr2Set[v].begin(), ite = ptr2Set[v].end(); it != ite; it++) {
                Instruction* inst = dyn_cast<Instruction>(*it);
                if (inst) {
                    if (dup.find(inst) == dup.end()){
                        PRINT(*v << " aliases " << **it << "\n");
                        tq.push_front(inst);
                        dup.insert(inst);
                    }
                }
            }
        }

        StoreInst *store = dyn_cast<StoreInst>(node);
        
        // TODO: will need to be modified for global vars
        if (store) {
            Value *des = store->getOperand(1);
            Instruction *dest = dyn_cast<Instruction>(des);
            if (dest) {
                for(Value::use_iterator UI = dest->use_begin(), E = dest->use_end(); UI != E; ++UI) {
                    Instruction *user = dyn_cast<Instruction>(*UI);
                    if (user) {
                        if (dup.find(user) == dup.end()){
                            tq.push_front(user);
                            dup.insert(user);
                        }
                    }
                }
            }
        }

		// analyze node 
		if(sinkSearch(node, name)) {
			// we found a sink
			PRINT(I << " has a path to " << *node << "\n");
            numPaths++;
			for (std::list<Instruction*>::iterator it=currPath.begin(), et=currPath.end(); it!=et; it++)
				taintedInstructions.insert(*it);
		}
	}   
    }
}

// return true if I is a sink
bool taint::sinkSearch(Value *I, std::string fname) {

    for (std::vector<Value*>::iterator s = funcSinks[fname].begin(), se = funcSinks[fname].end(); s != se; s++) {
        if (I == *s)
            return true;
    }
    return false;
}

void taint::pointerAnalysis(Function &F) {
    SetVector<Value *> Pointers;
    SetVector<CallSite> CallSites;

    for (Function::arg_iterator I = F.arg_begin(), E = F.arg_end(); I != E; ++I)
      if (I->getType()->isPointerTy())    // Add all pointer arguments.
        Pointers.insert(I);

    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
      if (I->getType()->isPointerTy()) // Add all pointer instructions.
        Pointers.insert(&*I);
      Instruction &Inst = *I;
      if (CallSite CS = cast<Value>(&Inst)) {
        Value *Callee = CS.getCalledValue();
        // Skip actual functions for direct function calls.
        if (!isa<Function>(Callee) && isInterestingPointer(Callee))
          Pointers.insert(Callee);
        // Consider formals.
        for (CallSite::arg_iterator AI = CS.arg_begin(), AE = CS.arg_end();
             AI != AE; ++AI)
          if (isInterestingPointer(*AI))
            Pointers.insert(*AI);
        CallSites.insert(CS);
      } else {
        // Consider all operands.
        for (Instruction::op_iterator OI = Inst.op_begin(), OE = Inst.op_end();
             OI != OE; ++OI)
          if (isInterestingPointer(*OI))
            Pointers.insert(*OI);
      }
    }

    // iterate over the worklist, and run the full (n^2)/2 disambiguations
    for (SetVector<Value *>::iterator I1 = Pointers.begin(), E = Pointers.end();
         I1 != E; ++I1) {
        uint64_t I1Size = AliasAnalysis::UnknownSize;
        Type *I1ElTy = cast<PointerType>((*I1)->getType())->getElementType();
        if (I1ElTy->isSized()) I1Size = AA->getTypeStoreSize(I1ElTy);

        for (SetVector<Value *>::iterator I2 = Pointers.begin(); I2 != I1; ++I2) {
            uint64_t I2Size = AliasAnalysis::UnknownSize;
            Type *I2ElTy =cast<PointerType>((*I2)->getType())->getElementType();
            if (I2ElTy->isSized()) I2Size = AA->getTypeStoreSize(I2ElTy);

            switch (AA->alias(*I1, I1Size, *I2, I2Size)) {
            case AliasAnalysis::NoAlias:
                ++NoAlias; break;
            case AliasAnalysis::MayAlias:
                ptr2Set[*I1].insert(*I2);
                ptr2Set[*I2].insert(*I1);
                ++MayAlias; break;
            case AliasAnalysis::PartialAlias:
                ptr2Set[*I1].insert(*I2);
                ptr2Set[*I2].insert(*I1);
                ++PartialAlias; break;
            case AliasAnalysis::MustAlias:
                ptr2Set[*I1].insert(*I2);
                ptr2Set[*I2].insert(*I1);
                ++MustAlias; break;
            }
        }
    }
}

bool taint::isInterestingPointer(Value *V)
 {
  return V->getType()->isPointerTy()
      && !isa<ConstantPointerNull>(V);
}

