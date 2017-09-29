//===------- EdgeProbability.h --------------------------------------------===//
//
// The KLEE Symbolic Virtual Machine with Numerical Error Analysis Extension
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef EDGEPROBABILITY_H_
#define EDGEPROBABILITY_H_

#include "klee/Config/Version.h"

#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"
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

#include <map>

namespace klee {

class EdgeProbability : public llvm::ModulePass {

  std::map<llvm::BasicBlock *, std::pair<llvm::BasicBlock *, double> >
  edgeProbability;

public:
  static char ID;

  static EdgeProbability *instance;

  EdgeProbability() : ModulePass(ID) {}

  virtual bool runOnModule(llvm::Module &M);

  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const;

  double getEdgeProbability(llvm::BasicBlock *dst, llvm::BasicBlock *src) const;
};
}

#endif /* EDGEPROBABILITY_H_ */
