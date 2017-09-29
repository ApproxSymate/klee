//===------- EdgeProbability.cpp ------------------------------------------===//
//
// The KLEE Symbolic Virtual Machine with Numerical Error Analysis Extension
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "../../include/klee/Internal/Module/EdgeProbability.h"

#define DEBUG_TYPE "edge-probability"

#include "llvm/DebugInfo.h"
#include "llvm/Pass.h"

#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
#if LLVM_VERSION_CODE > LLVM_VERSION(3, 2)
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#else
#include "llvm/Module.h"
#include "llvm/Function.h"
#include "llvm/Instructions.h"
#include "llvm/Instruction.h"
#endif
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/SourceMgr.h"

#include <set>
#include <vector>

using namespace klee;

bool EdgeProbability::runOnModule(llvm::Module &M) {
  for (llvm::Module::iterator func = M.begin(), fe = M.end(); func != fe;
       ++func) {
    if (func->isDeclaration())
      continue;

    const llvm::BranchProbabilityInfo &BPI =
        getAnalysis<llvm::BranchProbabilityInfo>(*func);

    for (llvm::Function::iterator bi = func->begin(), be = func->end();
         bi != be; ++bi) {
      llvm::TerminatorInst *ti = bi->getTerminator();
      unsigned numSuccessors = ti->getNumSuccessors();
      for (unsigned i = 0; i < numSuccessors; ++i) {
        llvm::BasicBlock *succ = ti->getSuccessor(i);
        llvm::BranchProbability prob = BPI.getEdgeProbability(&(*bi), i);
        double floatProb =
            ((double)prob.getNumerator()) / ((double)prob.getDenominator());
        edgeProbability[&(*bi)] =
            std::pair<llvm::BasicBlock *, double>(succ, floatProb);
      }
    }
  }

  return false; // does not modify program
}

void EdgeProbability::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<llvm::BranchProbabilityInfo>();
}

double EdgeProbability::getEdgeProbability(llvm::BasicBlock *dst,
                                           llvm::BasicBlock *src) const {
  std::map<llvm::BasicBlock *,
           std::pair<llvm::BasicBlock *, double> >::const_iterator it =
      edgeProbability.find(src);
  if (it != edgeProbability.end()) {
    return it->second.second;
  }
  return 0;
}

char EdgeProbability::ID = 0;
EdgeProbability *EdgeProbability::instance = 0;

static llvm::RegisterPass<EdgeProbability> X("edge-probability",
                                             "Extract CFG edge probability");
