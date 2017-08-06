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

#include "klee/Expr.h"
#include "klee/util/ArrayCache.h"

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

  class CallFrame {
  public:
    unsigned refCount;

  private:
    llvm::Instruction *call;

    std::map<llvm::Value *, ref<Expr> > argumentErrors;

  public:
    CallFrame(llvm::Instruction *inst, std::vector<ref<Expr> > &_errors);

    ~CallFrame() {}

    ref<Expr> getError(llvm::Value *v) const;

    llvm::Instruction *getInstruction() const { return call; }
  };

private:
  std::map<llvm::Value *, ref<Expr> > valueErrorMap;

  std::map<const Array *, const Array *> arrayErrorArrayMap;

  ref<Expr> getError(Executor *executor, ref<Expr> valueExpr,
                     llvm::Value *value = 0);

  ArrayCache errorArrayCache;

  std::string outputString;

  std::map<uintptr_t, ref<Expr> > storedError;

  /// \brief This is where we store the call error values of call arguments
  std::vector<ref<CallFrame> > callStack;

public:
  ErrorState() : refCount(0) {}

  ErrorState(ErrorState &symErr) : refCount(0) {
    storedError = symErr.storedError;
    // FIXME: Simple copy for now.
    valueErrorMap = symErr.valueErrorMap;
  }

  ~ErrorState();

  void outputErrorBound(llvm::Instruction *inst, double bound);

  ref<Expr> propagateError(Executor *executor, llvm::Instruction *instr,
                           ref<Expr> result,
                           std::vector<ref<Expr> > &arguments);

  ref<Expr> retrieveError(llvm::Value *value) { return valueErrorMap[value]; }

  std::string &getOutputString() { return outputString; }

  void executeStoreSimple(llvm::Instruction *inst, ref<Expr> address,
                          ref<Expr> error);

  ref<Expr> retrieveStoredError(ref<Expr> address) const;

  ref<Expr> executeLoad(llvm::Value *value, ref<Expr> address);

  /// \brief Overwrite the contents of the current error state with another
  void overwriteWith(ref<ErrorState> overwriting);

  /// print - Print the object content to stream
  void print(llvm::raw_ostream &os) const;

  /// dump - Print the object content to stderr
  void dump() const { print(llvm::errs()); }
};
}

#endif /* KLEE_ERRORSTATE_H_ */
