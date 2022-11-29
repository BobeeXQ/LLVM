#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <string>
#include <fstream>
#include <unordered_map>
#include <set>
#include <queue>
// #include <llvm/IR/Constant.h>
// #include <llvm/IR/Use.h>
// #include <typeinfo>

using namespace llvm;
using namespace std;

#define DEBUG_TYPE "AvailExpression"

namespace
{
struct AvailExpression : public FunctionPass
{
  static char ID;
  AvailExpression() : FunctionPass(ID) {}

  //printMap() helps checking codes and fixing bugs during processes
  void printMap(unordered_map<string, set<string>> m, string name){
    errs() << "This is the map storing info of " << name << ":" << "\n";
    for (auto x : m){
      errs() << x.first << ":";
      for (auto elem : x.second){
        errs() << " " << elem;
      }
      errs() << "\n";
    }
    errs() << "\n";
  }

  bool runOnFunction(Function &F) override
  {
    errs() << "AvailExpression: ";
    errs() << F.getName() << "\n";

    if (F.getName() == "main") {
      return false;
    }

    //non trivial expression map according to each operand
    unordered_map<string, set<string>> exp_map;

    //set including all expressions;
    set<string> all_exp;

    for (auto &basic_block : F)
    {
      for (auto &inst : basic_block)
      {
        if (inst.isBinaryOp()){
          string exp = "";
          string curr_op;
          set<string> ops;
          int i;

          for (i = 0; i < 2; i++){
            if (ConstantInt * cint = dyn_cast<ConstantInt>(inst.getOperand(i))){
             string s;
             raw_string_ostream * strm = new raw_string_ostream(s);
             cint->getValue().print(*strm,true);
             exp += strm->str();
            }
            else{
              string s;
              raw_string_ostream * strm = new raw_string_ostream(s);
              inst.getOperand(i)->print(*strm);
              string temp = strm->str();
              size_t idx1 = temp.find("%");
              size_t idx2 = temp.substr(idx1+1).find("%");
              exp += temp.substr(idx1+idx2+2,1);
              curr_op = temp.substr(idx1+idx2+2,1);
              ops.insert(curr_op);
            }
            if (i == 0){
              if (inst.getOpcode() == Instruction::Add) exp += "+";
              if (inst.getOpcode() == Instruction::Sub) exp += "-";
              if (inst.getOpcode() == Instruction::Mul) exp += "*";
              if (inst.getOpcode() == Instruction::SDiv) exp += "/";
            }
          }

          //save all expressions matching the variables into a map
          for (auto it = ops.begin(); it != ops.end(); ++ it){
            auto pos = exp_map.find(*it);
            if (pos == exp_map.end()){
              set<string> a;
              a.insert(exp);
              exp_map[*it] = a;
            }
            else{
              exp_map[*it].insert(exp);
            }
          }

          all_exp.insert(exp);
        }   
      }
    }

    unordered_map<string, set<string>> gen_map;
    unordered_map<string, set<string>> kill_map;
    unordered_map<string, set<string>> in_map;
    unordered_map<string, set<string>> out_map;

    //save gen and kill of each block
    int index = 0;
    for (auto &basic_block : F){
      set<string> gen, kill;
      string bk_name = basic_block.getName().str();

      for (auto &inst : basic_block){

        //if binary operation, means an expression generated
        if (inst.isBinaryOp()){

          //find the generated expression and insert it into gen
          string exp = "";
          int i;
          for (i = 0; i < 2; i++){
            if (ConstantInt * cint = dyn_cast<ConstantInt>(inst.getOperand(i))){
             string s;
             raw_string_ostream * strm = new raw_string_ostream(s);
             cint->getValue().print(*strm,true);
             exp += strm->str();
            }
            else{
              string s;
              raw_string_ostream * strm = new raw_string_ostream(s);
              inst.getOperand(i)->print(*strm);
              string temp = strm->str();
              size_t idx1 = temp.find("%");
              size_t idx2 = temp.substr(idx1+1).find("%");
              exp += temp.substr(idx1+idx2+2,1);
            }
            if (i == 0){
              if (inst.getOpcode() == Instruction::Add) exp += "+";
              if (inst.getOpcode() == Instruction::Sub) exp += "-";
              if (inst.getOpcode() == Instruction::Mul) exp += "*";
              if (inst.getOpcode() == Instruction::SDiv) exp += "/";
            }
          }
          gen.insert(exp);

          //if this generated expression in kill, remove it
          if (kill.find(exp) != kill.end()){
            kill.erase(exp);
          }
        }
        else if (inst.getOpcode() == Instruction::Store){

          //find variable to kill
          string to_kill;
          for (auto op = inst.op_begin(); op != inst.op_end(); op++ ){
            if (op != inst.op_begin()){
              to_kill = op->get()->getName().str();
            }
          }
        
          //from exp_map, insert exp_map[to_kill] to kill, remove from gen if match
          for (auto it = exp_map[to_kill].begin(); it != exp_map[to_kill].end(); ++it ){
            kill.insert(*it);
            if (gen.find(*it) != gen.end()){
              gen.erase(*it);
            }
          }
        }
      }

      gen_map[bk_name] = gen;
      kill_map[bk_name] = kill;

      //initialize in_map and out_map
      //IN[Bs] = 0; OUT[Bs] = GEN[Bs];
      //for B != Bs: OUT[B] = all_exp;
      if (index == 0){
        set<string> in;
        in_map[bk_name] = in;
        out_map[bk_name] = gen;
      }
      else {
        out_map[bk_name] = all_exp;
      }
      index++;
    }

    unordered_map<string, set<string>> pred_map;

    //find a set of predecessors for each block
    for (auto &basic_block : F){
      set<string> pred;
      string bk_name = basic_block.getName().str();
      for (BasicBlock *p : predecessors(&basic_block)) {
        pred.insert(p->getName().str());
      }
      pred_map[bk_name] = pred;
    }

    // printMap(exp_map,"exp_map");
    // printMap(gen_map,"gen_map");
    // printMap(kill_map, "kill_map");
    // printMap(pred_map,"pred_map");
    // printMap(in_map,"in_map");
    // printMap(out_map, "out_map");

    //IN[B] = intersection of all pred's out - OUT[P]
    //OUT[B] = GEN[B] U (IN[B] - KILL[B])
    bool change = true;

    while (change){
      change = false;
      index = 0;

      //for each B != Bs
      for (auto &basic_block : F){
        if (index != 0){
          string bk_name = basic_block.getName().str();

          //OLDOUT = OUT[B]
          set<string> old_out = out_map[bk_name];

          //IN[B] = intersection of all pred's out - OUT[P]
          set<string> in = all_exp;
          for (auto it = pred_map[bk_name].begin(); it != pred_map[bk_name].end(); it++){
            set<string> intersect;
            set_intersection(in.begin(), in.end(), out_map[*it].begin(), out_map[*it].end(), inserter(intersect, intersect.begin()));
            in = intersect;
          }

          in_map[bk_name] = in;

          //OUT[B] = GEN[B] U (IN[B] - KILL[B])
          set<string> new_out = gen_map[bk_name];
          for (auto it = in.begin(); it != in.end(); it++){
            auto pos = kill_map[bk_name].find(*it);
            if (pos == kill_map[bk_name].end()){
              new_out.insert(*it);
            }
          }

          out_map[bk_name] = new_out;

          if (old_out != new_out){
            change = true;
          }
        }
        index++;
      }
    }

    //printMap(in_map, "in_map");

    //output final result in style
    for (auto &basic_block : F){
      string name = basic_block.getName().str();
      errs() << "----- " << name << " -----" << "\n";
      errs() << "Available:";
      for (auto it = out_map[name].begin(); it != out_map[name].end(); it++){
        errs() << " " << *it;
      }
      errs() << "\n";
    }

    return true;
  }
}; // end of struct AvailExpression
} // end of anonymous namespace

char AvailExpression::ID = 0;
static RegisterPass<AvailExpression> X("AvailExpression", "AvailExpression Pass",
                                      false /* Only looks at CFG */,
                                      true /* Analysis Pass */);
