//===-- SymbolicError.cpp -------------------------------------------------===//
//
// The KLEE Symbolic Virtual Machine with Numerical Error Analysis Extension
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "SymbolicError.h"

#include "klee/Config/Version.h"
#include "klee/Internal/Module/TripCounter.h"

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#else
#include "llvm/BasicBlock.h"
#include "llvm/Instructions.h"
#endif

using namespace klee;

bool SymbolicError::addBasicBlock(llvm::Instruction *inst) {
  if (llvm::BasicBlock *bb = inst->getParent()) {
    if (lastBasicBlock == bb)
      return false;

    int64_t tripCount;
    if (TripCounter::instance &&
        TripCounter::instance->getTripCount(bb, tripCount)) {
      llvm::errs() << "TRIP COUNT FOUND: " << tripCount << "\n";
    }

    lastBasicBlock = bb;

    std::map<llvm::BasicBlock *, uint64_t>::iterator it = nonExited.find(bb);

    bool ret = (it != nonExited.end() && it->second > 0);
    if (ret) {
      --(it->second);
    } else {
      nonExited[bb] = 1;
    }
    return ret;
  }
  return false;
}

SymbolicError::~SymbolicError() {
  delete errorState;
  nonExited.clear();
}
