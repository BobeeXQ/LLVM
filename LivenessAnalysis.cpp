#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/CFG.h"
#include <string>
#include <fstream>
#include <unordered_map>
#include <set>
#include <queue>
#include <typeinfo>

using namespace llvm;
using namespace std;

#define DEBUG_TYPE "LivenessAnalysis"

namespace
{
struct LivenessAnalysis : public FunctionPass
{
  static char ID;
  LivenessAnalysis() : FunctionPass(ID) {}

  //start of modification 

  unordered_map<int, set<StringRef>> gen_map;
  unordered_map<int, set<StringRef>> kill_map;
  unordered_map<int, set<StringRef>> liveIn;
  unordered_map<int, set<StringRef>> liveOut;
  unordered_map<int, StringRef> dict;
  unordered_map<int, set<int>> suc_map;

  bool runOnFunction(Function &F) override
  {
    errs() << "LivenessAnalysis: ";
    errs() << F.getName() << "\n";

    if (F.getName() == "main") {
      return false;
    }

    int index = 1;

    for (auto &basic_block : F)
    {
      StringRef block_name = basic_block.getName();
      set<StringRef> curr_gen;
      set<StringRef> kill;
      set<StringRef> in;
      set<StringRef> out;
      dict[index] = block_name;
      stack<StringRef> s;
      
      for (auto &inst : basic_block)
      {
        int i = 0;
        for (auto op = inst.op_begin(); op != inst.op_end(); op++ ){
              
              StringRef name = op->get()->getName();
            
              //find kill, if store, insert them into gen
              if ((inst.getOpcode() == Instruction::Store) && op != inst.op_begin()){
                while (!s.empty()){
                  StringRef curr_name = s.top();
                  curr_gen.insert(curr_name);
                  s.pop();
                }
                kill.insert(name);
              }
              
              //push to stack
              if (inst.getOpcode() == Instruction::Load){
                s.push(name);
              }

              //if binary op, add them to set
              if (inst.isBinaryOp()){
                while (!s.empty()){
                  StringRef curr_name = s.top();
                  curr_gen.insert(curr_name);
                  s.pop();
                }
              }

              //if cmp, clear stak
              if (inst.getOpcode() == Instruction::ICmp){
                s = stack<StringRef>();
              }
        }
      }

      s = stack<StringRef>();
      set<StringRef> gen;

      for (auto it = curr_gen.begin(); it != curr_gen.end(); ++it){
        auto pos = kill.find(*it);
        if (pos == kill.end()){
          //gen.erase(*it);
          gen.insert(*it);
          in.insert(*it);
        }
      }

      gen_map[index] = gen;
      kill_map[index] = kill;
      liveIn[index] = in;
      liveOut[index] = out;
      index ++;
    }

    index = 1;

    //find the successors of each block
    for (auto &basic_block : F)
    {
      set<int> suc;
      int num = basic_block.getTerminator()->getNumSuccessors();
      for (int i = 0; i < num; i++) {
        StringRef sucName = basic_block.getTerminator()->getSuccessor(i)->getName();
        int sucNum;
        for (auto x : dict){
          if (x.second == sucName){
            sucNum = x.first;
            break;
          }
        }
        suc.insert(sucNum);
      }
      suc_map[index] = suc;
      index++;
    }

    index --;
    //OUT[B] = U IN[s]
    //IN[B] = GEN[B] U (OUT[B] - KILL[B])

    bool change = true;
    while (change){
       change = false;
       for (int i = index; i; i--){

        //saving original live-in variables to old_in
        set<StringRef> old_in = liveIn[i];

        //finding union of all live-in variables from successors and update to liveOut
        set<StringRef> union_in;
       // set<int> suc = suc_map[i];
        for (auto it = suc_map[i].begin(); it != suc_map[i].end(); it++){
          int n = *it;
          for (auto m = liveIn[n].begin(); m != liveIn[n].end(); m++){
            auto p = union_in.find(*m);
            if (p == union_in.end()){
              union_in.insert(*m);
            }
          }
        }
        liveOut[i] = union_in;

        //find new live-in using GEN[B] U (OUT[B] - KILL[B])

        //OUT[B] - KILL[B]
        set<StringRef> new_in;
        for (auto k = liveOut[i].begin(); k != liveOut[i].end(); k++){
          auto pos = kill_map[i].find(*k);
          if (pos == kill_map[i].end()){
            new_in.insert(*k);
          }
        }

        //GEN[B] U (OUT[B] - KILL[B])
        for (auto t = gen_map[i].begin(); t != gen_map[i].end(); t++){
          new_in.insert(*t);
        }

        liveIn[i] = new_in;

        if (old_in != new_in){
          change = true;
        }

       }
    }

    //output final result in style
    for (int i = 1; i <= index; i++){
      errs() << dict[i] << ":";
      for (auto x = liveOut[i].begin(); x != liveOut[i].end(); x ++){
        errs() << " " << *x;
      }
      errs() << "\n";
    }
    
    // errs() << "gen: " << "\n";
    // for (auto x : gen_map){
    //   errs() << x.first << ":";
    //   for (auto elem : x.second){
    //     errs() << " " << elem;
    //   }
    //   errs() << "\n";
    // }

    // errs() << "kill: " << "\n";
    // for (auto x : kill_map){
    //   errs() << x.first << ":";
    //   for (auto elem : x.second){
    //     errs() << " " << elem;
    //   }
    //   errs() << "\n";
    // }

    // errs() << "in: " << "\n";
    // for (auto x : liveIn){
    //   errs() << x.first << ":";
    //   for (auto elem : x.second){
    //     errs() << " " << elem;
    //   }
    //   errs() << "\n";
    // }

    // errs() << "out: " << "\n";
    // for (auto x : liveOut){
    //   errs() << x.first << ":";
    //   for (auto elem : x.second){
    //     errs() << " " << elem;
    //   }
    //   errs() << "\n";
    // } 

    // errs() << "suc_map: " << "\n";
    // for (auto x : suc_map){
    //   errs() << x.first << ":";
    //   for (auto elem : x.second){
    //     errs() << " " << elem;
    //   }
    //   errs() << "\n";
    // } 

    //end of modification

    return false;
  }
}; // end of struct LivenessAnalysis
} // end of anonymous namespace

char LivenessAnalysis::ID = 0;
static RegisterPass<LivenessAnalysis> X("LivenessAnalysis", "LivenessAnalysis Pass",
                                      false /* Only looks at CFG */,
                                      false /* Analysis Pass */);
