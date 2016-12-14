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

// if UNTAINT is defined the untainting policy will be in effect
#define UNTAINT

// ALLSOURCE will classify all instructions that aren't sinks as sources
#define ALLSOURCE


#define SOURCE_CONFIG_FILE "src.cfg"
#define SINK_CONFIG_FILE "sink.cfg"
#define UNTAINT_CONFIG_FILE "untaint.cfg"

// function name and # of which argument can be tainted
// -1 if it's a functon that uses varargs
// 0 if it's result can be tainted

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
            std::vector<Function *> funcTP;  // topological ordering of functions; used to reverse ordering
            std::vector<Function *> funcRTP; // reverse topological ordering of functions

            numPaths = 0;
            MustAlias = 0;
            MayAlias = 0;
            
            AA = &getAnalysis<AliasAnalysis>();
            CG = &getAnalysis<CallGraph>();

            // GlobalVariables are different than instances of the Instruction class and must be handled slighlty differently
            for (Module::global_iterator glob = M.global_begin(), globe = M.global_end(); glob != globe; glob++ ) {
                // they aren't modified so skip them
                if (glob->isConstant()) {
                    continue;
                }
                identifySource(*glob);
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
        
        void identifySource(Instruction &I);
        void identifySource(GlobalVariable &I);
        void identifySrcsAndSinks(Function *);
        
        void addToSources(Value &I, std::string name);
        void addToSinks(Value &I, std::string name);
        bool sinkSearch(Value * I, std::string fname);

        void pointerAnalysis(Function &F);

        void readConfigs(void);
        bool isInterestingPointer(Value *V);
        int  getOperandNo(std::string str, std::vector<struct source> &vec);
        void processSource(std::string line, std::vector<struct source> &vec);
        bool isInPolicy(std::string str, std::vector<struct source> &vec);
        bool isOperand(Value *I, Value *user, std::vector<struct source> &vec);
        std::string get_function_name(CallInst *call);

        private:
            size_t numPaths;
            size_t MustAlias;
            size_t MayAlias;

            CallGraph *CG;          // shows topological ordering of functions
            AliasAnalysis *AA;      // used for querying pointer relationship

            std::vector<struct source> sinks;       // stores the taint policy sinks
            std::vector<struct source> sources;     // stores the taint policy sources
            std::vector<struct source> untaints;    // stores the taint policy sanitizer

            std::set<Instruction *> taintedInstructions;  // stores all tainted instructions
            std::map<Value*, std::set<Value *> > ptr2Set; // contains alias relationship amongst pointers

            std::map<std::string, std::vector<Value *> > funcSrcs;      // stores a function's local sources
            std::map<std::string, std::vector<Value *> > funcSinks;     // stores a function's local sinks
    };
}

char taint::ID = 0;
static RegisterPass<taint> X("taint", "Static Taint Analysis", false, false);

void taint::readConfigs(void) {
    std::ifstream srcFile;
    std::ifstream sinkFile;
    std::ifstream untaintFile;
    std::string line;

    // SOURCE list
    srcFile.open(SOURCE_CONFIG_FILE);

    if (!srcFile.is_open()) {
        PRINT("Error while opening " SOURCE_CONFIG_FILE " \n");
    } else {
        while(getline(srcFile, line)) {
            processSource(line, sources);
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
            processSource(line, sinks);
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
            processSource(line, untaints);
        }
    }

    if (untaintFile.bad()) {
        PRINT("Error Reading " UNTAINT_CONFIG_FILE "\n");
    }

    untaintFile.close();
}

// If an instance of I being tainted is found, add it to sources and return
void taint::identifySource(Instruction &I) {

    bool foundSource = false;
    Function *f = I.getParent()->getParent();
    std::string name = f->getName().str();
    Value *v = dyn_cast<Value>(&I);

    PRINT(I << " of function " << name << " is being identified\n");

    #ifdef ALLSOURCE
    addToSources(*v, name);
    return;
    #endif

    // check all operands for tainted source calls
    size_t operandNum = I.getNumOperands();
    for (size_t i = 0; i < operandNum; i++) {
        Value * op = I.getOperand(i);
        CallInst *call = dyn_cast<CallInst>(op);
        if (call && (isInPolicy(get_function_name(call), sources))) {
            // untrusted source; I is now tainted
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
                            continue;
                        }
                        
                        // if the the value of a call is being stored see if it's from untrusted sources
                        CallInst *call = dyn_cast<CallInst>(var);
                        if (call && (isInPolicy(get_function_name(call), sources))) {
                            addToSources(*v, name);
                            PRINT(I << " was not a constant; was tainted by " << *first << "\n");
                            return;
                        }

                    } 
                } else if (User->getOpcode() == Instruction::Call) {
                    // check if the variable is being modified by an untrusted sources
                    PRINT(I << " is used in call " << *User << "\n");

                    CallInst *call = dyn_cast<CallInst>(User);
                    if (call && (isInPolicy(get_function_name(call), sources))) {
                        std::string fn(get_function_name(call));

                        // if it's scanf family functions any usage of I is possibly tainted 
                        if (!fn.compare("__isoc99_scanf") || !fn.compare("__isoc99_fscanf")) {
                            addToSources(*v, name);
                            break;
                        } else {

                            // check and see if I is being used as a taintable operand in the tainted source
                            if (isOperand(v, *UI, sources)) {
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

// If an instance of I being tainted is found, add it to sources and return
// in hindsight instead of overloading the  dentifySource function I could have
// I could have handled the special cases of global variable instructions in one function
void taint::identifySource(GlobalVariable &I) {

    Function *f;
    Value *v = dyn_cast<Value>(&I);

    #ifdef ALLSOURCE
    // Go through all uses which may be cross multiple functions
    // and add them to their respective function's source vector

    for(Value::use_iterator UI = I.use_begin(), E = I.use_end(); UI != E; ++UI) {
        Instruction *User = dyn_cast<Instruction>(*UI);
        if(User) {
            f = User->getParent()->getParent();
            std::string name = f->getName().str();
            addToSources(*v, name);
        }
    }

    return;
    #endif

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
                        continue;
                    }

                    // if the the value of a call is being stored see if it's from untrusted sources
                    CallInst *call = dyn_cast<CallInst>(var);
                    if (call && (isInPolicy(get_function_name(call), sources))) {
                        f = User->getParent()->getParent();
                        std::string name = f->getName().str();
                        addToSources(*v, name);
                        PRINT(I << " was not a constant; was tainted by " << *first << "\n");
                        return;
                    }

                }
            } else if (User->getOpcode() == Instruction::Call) {

                // check if the variable is being modified by an untrusted sources
                PRINT(I << " is used in call " << *User << "\n");

                CallInst *call = dyn_cast<CallInst>(User);
                if (call && (isInPolicy(get_function_name(call), sources))) {
                    std::string fn(get_function_name(call));

                    // if it's scanf family functions any usage of I is possibly tainted
                    if (!fn.compare("__isoc99_scanf") || !fn.compare("__isoc99_fscanf")) {
                        f = User->getParent()->getParent();
                        std::string name = f->getName().str();
                        addToSources(*v, name);
                        break;
                    } else {

                        // check and see if I is being used as a taintable operand in the tainted source
                        if (isOperand(v, *UI, sources)) {
                             f = User->getParent()->getParent();
                             std::string name = f->getName().str();
                             addToSources(*v, name);
                             break;
                        }
                    }
                }
            }
        }
    }
}

// for function f check all instructions and identify instructions as sinks and sources
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
                    if (!isInPolicy(get_function_name(call), sinks))
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
    		if (dyn_cast<StoreInst>(node)) {
                // globalvariables need to be tested for constant values separately from normal values
                GlobalVariable *g = dyn_cast<GlobalVariable>(node->getOperand(0));
                if (g) {
                    if (g->isConstant()) {
                        continue;
                    }
                } else if (dyn_cast<Constant>(node->getOperand(0))) {
    				continue;
                }
            }


            bool untainted = false;
            // check if it's untainted via an untaint call
            for(Value::use_iterator UI = node->use_begin(), E = node->use_end(); UI != E; ++UI) {
                Instruction *user = dyn_cast<Instruction>(*UI);
                if (user) {
                    if (dyn_cast<CallInst>(user)) {
                        if (isOperand(node, user, untaints)) {
                            untainted = true;
                            break;
                        }
                    }
                }
            }

            // skip further processing
            if (untainted) {
                continue;
            }
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

            if (node->getType()->isPointerTy())  {
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

            if (store) {

                Value *des = store->getOperand(1);
                if (des) {
                    for(Value::use_iterator UI = des->use_begin(), E = des->use_end(); UI != E; ++UI) {
                        Instruction *user = dyn_cast<Instruction>(*UI);
                        if (user) {
                            // user could be a global variable;
                            // only add uses of the global variable if it's in the same function
                            if (user->getParent()->getParent() != store->getParent()->getParent())
                                continue;

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

// process pointer alias relationships and store them in map
// where the key is the pointer and value is a set of the pointers 
// that alias the key
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
                break;
            case AliasAnalysis::MayAlias:
                ptr2Set[*I1].insert(*I2);
                ptr2Set[*I2].insert(*I1);
                ++MayAlias; break;
            case AliasAnalysis::PartialAlias:
                ptr2Set[*I1].insert(*I2);
                ptr2Set[*I2].insert(*I1);
                break;
            case AliasAnalysis::MustAlias:
                ptr2Set[*I1].insert(*I2);
                ptr2Set[*I2].insert(*I1);
                ++MustAlias; break;
            }
        }
    }
}

/* UTILITY FUNCTIONS */

// utility functions for splitting a string by a character
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

// line should be in a "string", integer format
// split it and create a source struct
void taint::processSource(std::string line, std::vector<struct source> &vec) {
    std::vector<std::string> srcs;
    struct source src;

    srcs = split(line, ',');

    if (srcs.empty())
        return;
    // there should only be two values per line
    if (srcs.size() == 2) {
        src.name = srcs[0];
        std::istringstream istr(srcs[1]);

        istr >> src.argc;
        vec.push_back(src);
    }
}

// get the function's name
std::string taint::get_function_name(CallInst *call) {
    Function * f = call->getCalledFunction();
    if (f)
        return f->getName().str();
    return std::string("Indirect Call");
}

// used for pointer analysis; used to check if a value is a pointer doesn't point to NULL
bool taint::isInterestingPointer(Value *V)
 {
  return V->getType()->isPointerTy()
      && !isa<ConstantPointerNull>(V);
}


// compare with list of all vec's elements
bool taint::isInPolicy(std::string str, std::vector<struct source> &vec) {
    size_t i;
    size_t len = vec.size();
    for (i = 0; i < len; i++) {
        if (!(vec[i].name.compare(str))) {
            return true;
        }
    }
    return false;
}

// get the corruptible/sanitizable operand number for a function
int taint::getOperandNo(std::string str, std::vector<struct source> &vec) {
    size_t i;
    size_t len = vec.size();
    for (i = 0; i < len; i++) {
        if (!(vec[i].name.compare(str))) {
            return vec[i].argc;
        }
    }
    return -1;
}

// check if I is an corruptible/sanitizable operand in user
bool taint::isOperand(Value *I, Value *user, std::vector<struct source> &vec) {
    bool ret = false;
    CallInst *call = dyn_cast<CallInst>(user);
    if (call && (isInPolicy(get_function_name(call), vec))) {
        std::string fn(get_function_name(call));
        // check and see if I is being used as an Operand
        int pos;
        int argc = getOperandNo(get_function_name(call), vec);
        int num = call->getNumArgOperands();
        for (pos = 0; pos < num; pos++) {
            Value *operand = call->getArgOperand(pos);
            Value *ival = dyn_cast<Value>(I);
            if (operand == ival) {
                // the arg value in the source structure is not 0 based
                // increment pos to align with that
                pos++;
                break;
            }
        }

        if (pos == argc) {
            ret = true;
        }
    }
    return ret;
}

// make sure no duplicates are inserted
void taint::addToSources(Value &I, std::string name) {
    if (std::find(funcSrcs[name].begin(), funcSrcs[name].end(), &I) == funcSrcs[name].end()) {
        funcSrcs[name].push_back(&I);
    }
}

// make sure no duplicates are inserted
void taint::addToSinks(Value &I, std::string name) {
    if (std::find(funcSinks[name].begin(), funcSinks[name].end(), &I) == funcSinks[name].end()) {
        funcSinks[name].push_back(&I);
    }
}