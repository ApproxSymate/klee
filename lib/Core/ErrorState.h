//===----- ErrorState.h ---------------------------------------------------===//
//
// The KLEE Symbolic Virtual Machine with Numerical Error Analysis Extension
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_ERRORSTATE_H_
#define KLEE_ERRORSTATE_H_

#include "klee/Constraints.h"
#include "klee/Expr.h"
#include "klee/util/ArrayCache.h"
#include "klee/Internal/Module/Cell.h"

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Instructions.h"
#else
#include "llvm/Instructions.h"
#endif

namespace klee {
class Executor;

class ErrorState {
public:
  unsigned refCount;

private:
  std::map<const Array *, const Array *> arrayErrorArrayMap;

  ref<Expr> getError(Executor *executor, ref<Expr> valueExpr,
                     llvm::Value *value = 0);

  ArrayCache errorArrayCache;

  std::string outputString;

  std::map<uintptr_t, ref<Expr> > declaredInputError;

  std::map<uintptr_t, ref<Expr> > storedError;

  std::vector<ref<Expr> > inputErrorList;

public:
  ErrorState() : refCount(0) {}

  ErrorState(ErrorState &errorState) : refCount(0) {
    declaredInputError = errorState.declaredInputError;
    storedError = errorState.storedError;
    inputErrorList = errorState.inputErrorList;
  }

  ~ErrorState();

  void outputComputedErrorBound(std::vector<double> doublePrecision);

  ConstraintManager outputErrorBound(llvm::Instruction *inst, ref<Expr> error,
                                     double bound,
                                     std::vector<ref<Expr> > &_inputErrorList);

  ref<Expr> propagateError(Executor *executor, llvm::Instruction *instr,
                           ref<Expr> result, std::vector<Cell> &arguments);

  std::string &getOutputString() { return outputString; }

  void registerInputError(ref<Expr> error);

  void executeStoreSimple(ref<Expr> address, ref<Expr> error);

  void declareInputError(ref<Expr> address, ref<Expr> error);

  ref<Expr> retrieveStoredError(ref<Expr> address) const;

  ref<Expr> retrieveDeclaredInputError(ref<Expr> address) const;

  bool hasStoredError(ref<Expr> address) const;

  ref<Expr> executeLoad(llvm::Value *value, ref<Expr> base, ref<Expr> address,
                        ref<Expr> offset);

  /// \brief Overwrite the contents of the current error state with another
  void overwriteWith(ref<ErrorState> overwriting);

  /// print - Print the object content to stream
  void print(llvm::raw_ostream &os) const;

  /// dump - Print the object content to stderr
  void dump() const {
    print(llvm::errs());
    llvm::errs() << "\n";
  }
};
}

#endif /* KLEE_ERRORSTATE_H_ */
