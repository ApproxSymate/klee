//===-- SymbolicError.cpp -------------------------------------------------===//
//
// The KLEE Symbolic Virtual Machine with Numerical Error Analysis Extension
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "SymbolicError.h"
#include "klee/util/PrettyExpressionBuilder.h"

#include "Executor.h"
#include "klee/CommandLine.h"
#include "klee/Config/Version.h"
#include "klee/Internal/Module/TripCounter.h"
#include "klee/Internal/Module/KInstruction.h"

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#else
#include "llvm/BasicBlock.h"
#include "llvm/Instructions.h"
#endif

using namespace klee;

uint64_t SymbolicError::freshVariableId = 0;

ref<Expr> SymbolicError::computeLoopError(int64_t tripCount,
                                          ref<Expr> initError,
                                          ref<Expr> endError) {
  if (llvm::isa<ConstantExpr>(endError)) {
    // In case the second stored error was a constant, then the resulting error
    // is the constant.
    return endError;
  }
  if (llvm::isa<ConstantExpr>(initError)) {
    // In case the first stored error was a constant and the second stored error
    // was a non-constant symbolic expression, then the resulting error was the
    // symbolic expression.
    return endError;
  }
  // In case both the first and the second stored errors were non-constant
  // symbolic expressions, then the error amount is: the first stored error +
  // (trip count - 1) * (second stored error - first stored error).
  ref<Expr> error = ExtractExpr::create(
      AddExpr::create(
          ZExtExpr::create(initError, Expr::Int64),
          MulExpr::create(
              ConstantExpr::create(tripCount - 1, Expr::Int64),
              SubExpr::create(ZExtExpr::create(endError, Expr::Int64),
                              ZExtExpr::create(initError, Expr::Int64)))),
      0, Expr::Int8);
  return error;
}

bool SymbolicError::breakLoop(Executor *executor, ExecutionState &state,
                              llvm::Instruction *inst,
                              llvm::BasicBlock *&exit) {
  if (!LoopBreaking) {
    deregisterLoopIfExited(executor, state, inst);
    return false;
  }

  int64_t tripCount;
  if (TripCounter::instance &&
      TripCounter::instance->getTripCount(inst, tripCount, exit)) {
    // Loop is entered
    std::map<llvm::Instruction *, uint64_t>::iterator it = nonExited.find(inst);

    bool ret = (it != nonExited.end() && it->second > 0);
    if (ret) {
      --(it->second);
      if ((it->second) % 2 == 0) {
        std::map<ref<Expr>, ref<Expr> > &initErrorStackElem =
            initWritesErrorStack.back();

        // We are exiting the loop
        for (std::map<ref<Expr>, ref<Expr> >::iterator
                 it1 = writesStack.back().begin(),
                 ie1 = writesStack.back().end();
             it1 != ie1; ++it1) {
          Cell addressCell;
          addressCell.value = it1->first;

          // We retrieve the error stored in the address
          std::pair<ref<Expr>, ref<Expr> > errorAndMore =
              errorState->retrieveStoredError(it1->first);

          // We retrieve the initial error stored in the address
          std::map<ref<Expr>, ref<Expr> >::iterator initErrorIter =
              initErrorStackElem.find(it1->first);
          ref<Expr> initError = ConstantExpr::create(0, Expr::Int8);
          if (initErrorIter != initErrorStackElem.end()) {
            initError = initErrorIter->second;
          }
          ref<Expr> error =
              computeLoopError(tripCount, initError, errorAndMore.first);
          ref<Expr> freshRead =
              createFreshRead(executor, state, it1->second->getWidth());

          // We actually perform an update to KLEE's shadow memory to store the
          // error and an unknown value (freshRead) of the value itself.
          executor->executeMemoryOperation(state, true, addressCell, freshRead,
                                           error, errorAndMore.second, 0);
        }

        // Here we simply retrieve the error amounts for PHIs already stored in
        // phiResultErrorInitStack, that was computed in the previous iteration.
        // So differently to memory store above, we no longer call
        // computeLoopError.
        std::map<KInstruction *, ref<Expr> > &phiResultInitErrorStackElem =
            phiResultInitErrorStack.back();

        for (std::map<KInstruction *, unsigned int>::iterator
                 it1 = phiResultWidthList.begin(),
                 ie1 = phiResultWidthList.end();
             it1 != ie1; ++it1) {
          ref<Expr> error = ConstantExpr::create(0, Expr::Int8);
          ref<Expr> nullExpr;

          std::map<KInstruction *, ref<Expr> >::iterator initErrorIter =
              phiResultInitErrorStackElem.find(it1->first);

          if (initErrorIter != phiResultInitErrorStackElem.end()) {
            error = initErrorIter->second;
          }

          executor->bindLocal(
              it1->first, state, createFreshRead(executor, state, it1->second),
              std::pair<ref<Expr>, ref<Expr> >(error, nullExpr));
        }

        // Pop the last memory writes record
        writesStack.pop_back();

        // Pop the top memory writes initial error record
        initWritesErrorStack.pop_back();

        // Pop the top phi result initial errors
        phiResultInitErrorStack.pop_back();

        // Erase the loop from not-yet-exited loops map
        nonExited.erase(it);
        return true;
      } else if (!phiResultInitErrorStack.empty()) {
        // After the first iteration, entering the second iteration; we compute
        // the errors for the returns of the PHI instructions. This is the right
        // time to do this, since when we iterate twice, the PHIs are visited
        // three times.
        std::map<KInstruction *, ref<Expr> > &phiResultInitErrorStackElem =
            phiResultInitErrorStack.back();

        for (std::map<KInstruction *, ref<Expr> >::iterator
                 it1 = phiResultInitErrorStackElem.begin(),
                 ie1 = phiResultInitErrorStackElem.end();
             it1 != ie1; ++it1) {
          ref<Expr> error = it1->second;

          // We store the computed error amount to be used outside the loop, and
          // store it
          error = computeLoopError(tripCount, it1->second, error);
          phiResultInitErrorStackElem[it1->first] = error;
        }
      }
    } else {
      // Loop is entered for the first time

      // Add element to write record
      writesStack.push_back(std::map<ref<Expr>, ref<Expr> >());

      // Add element to init writes error stack
      initWritesErrorStack.push_back(std::map<ref<Expr>, ref<Expr> >());

      // Add element to the phi result initial errors stack
      std::map<KInstruction *, ref<Expr> > phiResultInitError =
          tmpPhiResultInitError;
      phiResultInitErrorStack.push_back(phiResultInitError);

      // Set the iteration reverse count.
      nonExited[inst] += 2;
    }
  }

  deregisterLoopIfExited(executor, state, inst);
  return false;
}

ref<Expr> SymbolicError::createFreshRead(Executor *executor,
                                         ExecutionState &state,
                                         unsigned int width) {
  return executor->createFreshArray(state, SymbolicError::freshVariableId,
                                    width);
}

void SymbolicError::deregisterLoopIfExited(Executor *executor,
                                           ExecutionState &state,
                                           llvm::Instruction *inst) {
  llvm::Instruction *firstLoopInst =
      TripCounter::instance->getFirstInstructionOfExit(inst);
  std::map<llvm::Instruction *, uint64_t>::iterator it =
      nonExited.find(firstLoopInst);
  if (it != nonExited.end()) {
    // We are exiting the loop

    // Pop the last memory writes record
    writesStack.pop_back();

    // Pop the top memory writes initial error record
    initWritesErrorStack.pop_back();

    // Pop the top phi result initial errors
    phiResultInitErrorStack.pop_back();

    // Erase the loop from not-yet-exited loops map
    nonExited.erase(it);
  }
}

std::pair<ref<Expr>, ref<Expr> >
SymbolicError::propagateError(Executor *executor, KInstruction *ki,
                              ref<Expr> result, std::vector<Cell> &arguments,
                              unsigned int phiResultWidth) {
  std::pair<ref<Expr>, ref<Expr> > error =
      errorState->propagateError(executor, ki->inst, result, arguments);

  if (LoopBreaking) {
    if (TripCounter::instance &&
        TripCounter::instance->isRealFirstInstruction(ki->inst)) {
      phiResultWidthList.clear();
      tmpPhiResultInitError.clear();
    }

    if (ki->inst->getOpcode() == llvm::Instruction::PHI &&
        TripCounter::instance &&
        TripCounter::instance->isInHeaderBlockWithTripCount(ki->inst)) {
      if (phiResultWidthList.find(ki) == phiResultWidthList.end()) {
        phiResultWidthList[ki] = phiResultWidth;
      }
      tmpPhiResultInitError[ki] = error.first;
    }
  }

  return error;
}

SymbolicError::~SymbolicError() {
  nonExited.clear();
}

void SymbolicError::executeStore(ref<Expr> base, ref<Expr> address,
                                 ref<Expr> value, ref<Expr> error,
                                 ref<Expr> valueWithError,
                                 llvm::Instruction *inst) {
    if (LoopBreaking && !writesStack.empty()) {
      // Record the error at each store at each iteration.
      if (llvm::isa<ConstantExpr>(address)) {
        std::map<ref<Expr>, ref<Expr> > &writesMap = writesStack.back();
        writesMap[address] = value;

        std::map<ref<Expr>, ref<Expr> > &initErrorMap =
            initWritesErrorStack.back();
        if (initWritesErrorStack.back().find(address) ==
            initWritesErrorStack.back().end()) {
          initErrorMap[address] = error;
        }
      } else {
        assert(!"non-constant address");
      }
    }
    if (llvm::isa<ConstantExpr>(value)) {
      base = value;
    }
    storeError(base, address, error, valueWithError, inst);
}

void SymbolicError::print(llvm::raw_ostream &os) const {
  errorState->print(os);

  os << "\nNon-Exited Loops:";
  if (!nonExited.empty()) {
    for (std::map<llvm::Instruction *, uint64_t>::const_iterator
             it = nonExited.begin(),
             ie = nonExited.end();
         it != ie; ++it) {
      os << "\nheader: ";
      it->first->print(os);
      os << ", iterations left: " << it->second;
    }
  } else {
    os << " (none)";
  }

  os << "\nWrites stack:";
  if (!writesStack.empty()) {
    bool stackPrinted = false;
    for (std::vector<std::map<ref<Expr>, ref<Expr> > >::const_iterator
             it = writesStack.begin(),
             ie = writesStack.end();
         it != ie; ++it) {
      if (!(*it).empty()) {
        stackPrinted = true;
        os << "\n-----------------------------";
        for (std::map<ref<Expr>, ref<Expr> >::const_iterator it1 = it->begin(),
                                                             ie1 = it->end();
             it1 != ie1; ++it1) {
          os << "\n[";
          it1->first->print(os);
          os << "] -> [";
          it1->second->print(os);
          os << "]";
        }
      }
    }
    if (!stackPrinted)
      os << " (empty frames)";
  } else {
    os << " (empty)";
  }

  os << "\nErrors Initially Written:";
  if (!initWritesErrorStack.empty()) {
    bool stackPrinted = false;
    for (std::vector<std::map<ref<Expr>, ref<Expr> > >::const_iterator
             it = initWritesErrorStack.begin(),
             ie = initWritesErrorStack.end();
         it != ie; ++it) {
      if (!(*it).empty()) {
        stackPrinted = true;
        os << "\n-----------------------------";
        for (std::map<ref<Expr>, ref<Expr> >::const_iterator it1 = it->begin(),
                                                             ie1 = it->end();
             it1 != ie1; ++it1) {
          os << "\n[";
          it1->first->print(os);
          os << "] -> [";
          it1->second->print(os);
          os << "]";
        }
      }
    }
    if (!stackPrinted)
      os << " (empty frames)";
  } else {
    os << " (empty)";
  }

  os << "\nLoop header PHI results widths:";
  if (!phiResultWidthList.empty()) {
    for (std::map<KInstruction *, unsigned int>::const_iterator
             it = phiResultWidthList.begin(),
             ie = phiResultWidthList.end();
         it != ie; ++it) {
      os << "\n[";
      it->first->inst->print(os);
      os << "," << it->second << "]";
    }
  } else {
    os << " (empty)";
  }

  os << "\nLoop header PHI results initial error values:";
  if (!phiResultInitErrorStack.empty()) {
    bool stackPrinted = false;
    for (std::vector<std::map<KInstruction *, ref<Expr> > >::const_iterator
             it = phiResultInitErrorStack.begin(),
             ie = phiResultInitErrorStack.end();
         it != ie; ++it) {
      if (!(*it).empty()) {
        stackPrinted = true;
        os << "\n-----------------------------";
        for (std::map<KInstruction *, ref<Expr> >::const_iterator
                 it1 = it->begin(),
                 ie1 = it->end();
             it1 != ie1; ++it1) {
          os << "\n[";
          it1->first->inst->print(os);
          os << ",";
          it1->second->print(os);
          os << "]";
        }
      }
    }
    if (!stackPrinted)
      os << " (empty frames)";
  } else {
    os << " (empty)";
  }
}
