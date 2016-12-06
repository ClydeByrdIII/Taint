#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Constants.h"
#include "llvm/Analysis/ProfileInfo.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/DataTypes.h"
#include "llvm/Analysis/LoopPass.h"
#include <queue>
#include <set>
#include <algorithm>

#define UNTAINT
// #define ALLSOURCE

// function name and # of which argument can be tainted
// -1 if var args
struct source {
    std::string name;
    int argc;
};

struct source srcs[] =
{
    {"getchar", 0},
    {"read", 2},
    {"pread", 2},
    {"fread", 1},
    {"scanf", -1},
    {"__isoc99_scanf", -1},
    {"__isoc99_fscanf", -1},
    {"fscanf", -1},
    {"fgetc", 1},
    {"gets", 1},
    {"getc", 0},
    {"fgets", 1},
    {"fopen", 0},
    {"freopen", 0},
    {"recv", 2},
    {"recvfrom", 2},
};

struct source sinks[] =
{
    {"strcpy", 2},
    {"strncpy", 2},
    {"strcat", 2},
    {"strncat", 2},
    {"strdup", 1},
    {"memcpy", 2},
    {"memmove", 2},
    {"putc", 1},
    {"putchar", 1},
    {"fputc", 1},
    {"puts", 1},
    {"fputs", 2},
    {"printf", -1},
    {"fprintf", -1},
    {"sprintf",  1},
    {"snprintf", 1},
    {"vfprintf", 1},
    {"vsnprintf", 1},
    {"vsprintf", 1},
    {"write", 2},
    {"fwrite", 1},
    {"pwrite", 2},
    {"send", 2},
    {"sendto", 2},
};


using namespace llvm;

namespace {
    struct taint: public ModulePass { 
        static char ID;
        taint() : ModulePass(ID) { }
        virtual bool runOnModule(Module &M) {
            
            numPaths = 0;
            /* TODO: ADD global instructions in to the analaysis */
            for (Module::global_iterator glob = M.global_begin(), globe = M.global_end(); glob != globe; glob++ ) {
                errs() << "Global instruction: " << *glob << "\n";
            }

            CG = &getAnalysis<CallGraph>();
            
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
                
                if(!main && !name.compare("main")) 
                    main = func;

                identifySrcsAndSinks(func);
            }
           
            // get reverse topological order
            funcRTP.insert(funcRTP.begin(), funcTP.begin(), funcTP.end());
            std::reverse(funcRTP.begin(), funcRTP.end());
            
            for (std::vector<Function *>::iterator l = funcRTP.begin(), le = funcRTP.end(); l != le; l++) {
                // find path from l's srcs to l's sinks
                std::string fname = (*l)->getName().str();
                for (std::vector<Value *>::iterator I = funcSrcs[fname].begin(), IE = funcSrcs[fname].end(); I != IE; I++ ) {
                    errs() << fname << " has " << **I << " as a source\n";
                    Instruction *v = dyn_cast<Instruction>(*I);
                    if (v)
                        taintTrack(*v);
 
                }

            }
		// Count Insts that propagate taint
		llvm::errs()<< "# Tainting Instructions = " << taintedInstructions.size() << "\n";
        llvm::errs()<< "# of Paths = " << numPaths << "\n";
		
            return false; // return true if you modified the code
        }

        void getAnalysisUsage(AnalysisUsage &AU) const {
            AU.addRequired<CallGraph>(); 
        }

        void taintTrack(Instruction &I);
        
        void identifySrcsAndSinks(Function *);
        
        void identifySource(Instruction &I);
        
        bool isSink(std::string str);
        bool isSource(std::string str);
        void addToSources(Value &I, std::string name);
        void addToSinks(Value &I, std::string name);

        std::string get_function_name(CallInst *call);
        int isSourceOperand(std::string str); 
        bool sinkSearch(Value * I, std::string fname);

        private:
            std::map<Instruction *, std::vector<Value *> > taintMap;
            std::queue<Instruction *> taintedQueue;
            std::set<Instruction *> taintedInstructions;
            size_t numPaths;
            std::map<std::string, Function *> funcMap;
            std::vector<Function *> funcRTP;
            std::vector<Function *> funcTP;
            std::map<std::string, std::vector<Value *> > funcSrcs;
            std::map<std::string, std::vector<Value *> > funcSinks;
            std::map<std::string, Function *> taintedFunctions;
            Function *main;
            CallGraph *CG;

    };
}
char taint::ID = 0;
static RegisterPass<taint> X("taint", "Static Taint Analysis", false, false);

void taint::identifySource(Instruction &I) {

    Function *f = I.getParent()->getParent();
    std::string name = f->getName().str();
    // look for the values being stored in to a variable
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
                    
                    #ifdef ALLSOURCE
                        Value *v = dyn_cast<Value>(&I);
                        addToSources(*v, name);
                        continue;
                    #endif

                    // if the the value of a call is being stored see if it's from untrusted sources
                    CallInst *call = dyn_cast<CallInst>(var);
                    if (call && (isSource(get_function_name(call)))) {
                        // untrusted source; I is now tainted
                        Value *v = dyn_cast<Value>(&I);
                        addToSources(*v, name);
                        errs() << I << " was not a constant; was tainted by " << *first << "\n";
                    }

                } 
            } else if (User->getOpcode() == Instruction::Call) {
                // check if the variable is being modified by an untrusted sources

                CallInst *call = dyn_cast<CallInst>(User);
                if (call && (isSource(get_function_name(call)))) {
                    std::string fn(get_function_name(call));
                    errs() << "fn is " << fn << "\n";
                    // if scanf functions any usage of I is tainted 
                    if (!fn.compare("__isoc99_scanf") || !fn.compare("__isoc99_fscanf")) {
                        Value *v = dyn_cast<Value>(&I);
                        addToSources(*v, name);
                        
                    } else {

                        // check and see if I is being used as a taintable operand in User
                        int pos;
                        bool found = false;
                        int argc = isSourceOperand(get_function_name(call));
                        int num = call->getNumArgOperands();
                        for (pos = 0; pos < num; pos++) {
                            Value *operand = call->getArgOperand(pos);
                            if ((operand)->getValueID() == I.getValueID()) {
                                found = true;
                                pos++;
                                break;
                            }
                        }

                        if (found == true && pos == argc) {
                             Value *v = dyn_cast<Value>(&I);
                             addToSources(*v, name);
                        }

                    }
                    errs() << I << " is used in call " << *User << "\n";
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
            if (i->getOpcode() == Instruction::Alloca || i->getOpcode() == Instruction::GetElementPtr) {
                identifySource(*i);
            } else if (i->getOpcode() == Instruction::Call || i->getOpcode() == Instruction::Ret || i->getOpcode() == Instruction::Br) {
                // potentially a sink
                CallInst *call = dyn_cast<CallInst>(i);
                ReturnInst *ret = dyn_cast<ReturnInst>(i);
                BranchInst *br = dyn_cast<BranchInst>(i);

                if (call) {
                    if (!isSink(get_function_name(call)))
                        continue;
                    errs() << *i << " is a sink call\n";
                } else if (ret) {
                    errs() << *i << " is a return instruction\n";
                } else if (br) {
                    errs() << *i << " is a branch instruction\n";
                }
                addToSinks(*i, name);
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
    size_t len = *(&sinks + 1) - sinks;
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
    size_t len = *(&srcs + 1) - srcs;
    for (i = 0; i < len; i++) {
        if (!(srcs[i].name.compare(str))) {
            return true;
        }
    }
    return false;
}

int taint::isSourceOperand(std::string str) {
    size_t i;
    size_t len = *(&srcs + 1) - srcs;
    for (i = 0; i < len; i++) {
        if (!(srcs[i].name.compare(str))) {
            return srcs[i].argc;
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

        StoreInst *store = dyn_cast<StoreInst>(node);
        
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

        //errs() << *node << " is examined\n";
		// analyze node 
		if(sinkSearch(node, name)) {
			// we found a sink
			errs() << I << " has a path to " << *node << "\n";
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
