//===------- TripCounter.cpp ----------------------------------------------===//
//
// The KLEE Symbolic Virtual Machine with Numerical Error Analysis Extension
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "../../include/klee/Internal/Module/TripCounter.h"

#define DEBUG_TYPE "trip-counter"

#include "klee/CommandLine.h"

#include "llvm/DebugInfo.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"

#if LLVM_VERSION_CODE > LLVM_VERSION(3, 2)
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/GlobalVariable.h"
#else
#include "llvm/BasicBlock.h"
#include "llvm/Constants.h"
#include "llvm/Function.h"
#include "llvm/Module.h"
#include "llvm/GlobalVariable.h"
#endif
#include "llvm/Support/raw_ostream.h"

#include <set>

using namespace klee;

TripCounter *TripCounter::instance = 0;

void TripCounter::analyzeSubLoops(llvm::ScalarEvolution &se,
                                  const llvm::Loop *l) {
  const std::vector<llvm::Loop *> &v = l->getSubLoops();
  const llvm::SCEV *scev = se.getBackedgeTakenCount(l);
  llvm::BasicBlock *header = l->getHeader();

  headerBlocks.insert(header);

  realFirstInstruction.insert(header->begin());

  if (const llvm::SCEVConstant *scevConstant =
          llvm::dyn_cast<llvm::SCEVConstant>(scev)) {
    llvm::Instruction *headerFirstInst =
        header->getFirstNonPHIOrDbgOrLifetime();
    llvm::Instruction *exitFirstInst =
        l->getExitBlock()->getFirstNonPHIOrDbgOrLifetime();

    if (DebugPrecision) {
      llvm::errs() << "Loop trip count [";
      llvm::errs() << headerFirstInst->getParent()->getParent()->getName().str()
                   << ": ";
      if (llvm::MDNode *n = headerFirstInst->getMetadata("dbg")) {
        llvm::DILocation loc(n);
        llvm::errs() << "Line " << loc.getLineNumber();
      }
      llvm::errs() << "]: " << scevConstant->getValue()->getSExtValue() << "\n";
    }

    tripCount[headerFirstInst] = scevConstant->getValue()->getSExtValue();
    exitBlock[headerFirstInst] = l->getExitBlock();
    for (llvm::Loop::block_iterator it = l->block_begin(), ie = l->block_end();
         it != ie; ++it) {
      blockToFirstInstruction[*it] = headerFirstInst;
    }
    firstInstructionOfExit[exitFirstInst] = headerFirstInst;
  }

  for (std::vector<llvm::Loop *>::const_iterator it = v.begin(), ie = v.end();
       it != ie; ++it) {
    analyzeSubLoops(se, *it);
  }
}

bool TripCounter::getTripCount(llvm::Instruction *inst, int64_t &count,
                               llvm::BasicBlock *&exit) const {
  std::map<llvm::Instruction *, int64_t>::const_iterator it =
      tripCount.find(inst);
  exit = 0;
  if (it != tripCount.end()) {
    count = it->second;
    std::map<llvm::Instruction *, llvm::BasicBlock *>::const_iterator it1 =
        exitBlock.find(inst);
    if (it1 != exitBlock.end()) {
      exit = it1->second;
    }
    return true;
  }

  count = -1;
  if (llvm::BasicBlock *bb = inst->getParent()) {
    std::map<llvm::BasicBlock *, llvm::Instruction *>::const_iterator it =
        blockToFirstInstruction.find(bb);
    if (it != blockToFirstInstruction.end()) {
      std::map<llvm::Instruction *, int64_t>::const_iterator it1 =
          tripCount.find(it->second);
      if (it1 != tripCount.end()) {
        count = it1->second;
        std::map<llvm::Instruction *, llvm::BasicBlock *>::const_iterator it2 =
            exitBlock.find(inst);
        if (it2 != exitBlock.end()) {
          exit = it2->second;
        }
      }
    }
  }
  return false;
}

bool TripCounter::runOnModule(llvm::Module &m) {
  for (llvm::Module::iterator func = m.begin(), fe = m.end(); func != fe;
       ++func) {

    if (func->isDeclaration())
      continue;

    const llvm::LoopInfo &LI = getAnalysis<llvm::LoopInfo>(*func);

    llvm::ScalarEvolution &SE = getAnalysis<llvm::ScalarEvolution>(*func);

    for (llvm::LoopInfo::iterator it = LI.begin(), ie = LI.end(); it != ie;
         ++it) {
      analyzeSubLoops(SE, *it);
    }
  }
  return false;
}

void TripCounter::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<llvm::LoopInfo>();
  AU.addRequired<llvm::ScalarEvolution>();
}

char TripCounter::ID = 0;

static llvm::RegisterPass<TripCounter>
X("trip-counter", "Pass to collect loop trip counts");
