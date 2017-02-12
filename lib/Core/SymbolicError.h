/*
 * SymbolicError.h
 *
 *  Created on: 18 Aug 2016
 *      Author: himeshi
 */

#ifndef KLEE_SYMBOLICERROR_H_
#define KLEE_SYMBOLICERROR_H_

#include "klee/Expr.h"
#include "klee/util/ArrayCache.h"

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Instructions.h"
#else
#include "llvm/Instructions.h"
#endif

namespace klee {
class Executor;

class SymbolicError {

  std::map<llvm::Value *, ref<Expr> > valueErrorMap;

  std::map<const Array *, const Array *> arrayErrorArrayMap;

  ref<Expr> getError(Executor *executor, ref<Expr> valueExpr,
                     llvm::Value *value = 0);

  ArrayCache errorArrayCache;

  std::string outputString;

  std::map<uintptr_t, ref<Expr> > storedError;

public:
  SymbolicError() {}

  SymbolicError(SymbolicError &symErr) { storedError = symErr.storedError; }

  ~SymbolicError();

  void addOutput(llvm::Instruction *inst);

  ref<Expr> propagateError(Executor *executor, llvm::Instruction *instr,
                           ref<Expr> result,
                           std::vector<ref<Expr> > &arguments);

  std::string getOutputString() { return outputString; }

  void executeStore(ref<Expr> address, ref<Expr> error);

  ref<Expr> executeLoad(ref<Expr> address);

  /// print - Print the object content to stream
  void print(llvm::raw_ostream &os) const;

  /// dump - Print the object content to stderr
  void dump() const { print(llvm::errs()); }
};
}

#endif /* KLEE_SYMBOLICERROR_H_ */
