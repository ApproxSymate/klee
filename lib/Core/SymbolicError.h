//===-- SymbolicError.h ---------------------------------------------------===//
//
// The KLEE Symbolic Virtual Machine with Numerical Error Analysis Extension
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_SYMBOLICERROR_H_
#define KLEE_SYMBOLICERROR_H_

#include "../../include/klee/Internal/Module/EdgeProbability.h"

#include "ErrorState.h"

#include "klee/Expr.h"
#include "klee/Internal/Module/Cell.h"
#include "klee/util/ArrayCache.h"
#include "klee/Constraints.h"

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Instructions.h"
#else
#include "llvm/Instructions.h"
#endif

namespace klee {
class Executor;
class ExecutionState;
class KInstruction;

class SymbolicError {
  static uint64_t freshVariableId;

  ref<ErrorState> errorState;

  /// \brief This map implements a stacking of cascading loops: This records the
  /// current loops not yet exited, and their corresponding virtual iteration
  /// counts.
  std::map<llvm::Instruction *, uint64_t> nonExited;

  /// \brief Record addresses used for writes to memory within each loop
  std::vector<std::map<ref<Expr>, ref<Expr> > > writesStack;

  /// \brief Record initial errors written into memory addresses within each
  /// loop
  std::vector<std::map<ref<Expr>, ref<Expr> > > initWritesErrorStack;

  /// \brief This data structure records the width of the results of phi
  /// instructions at the header block of a loop
  std::map<KInstruction *, unsigned int> phiResultWidthList;

  /// \brief This data structure records the initial
  std::vector<std::map<KInstruction *, ref<Expr> > > phiResultInitErrorStack;

  /// \brief Temporary PHI result initial error amount
  std::map<KInstruction *, ref<Expr> > tmpPhiResultInitError;

  /// \brief Temporary storage to store the error expression for
  /// klee_bound_error call
  ref<Expr> kleeBoundErrorExpr;

  /// \brief Contains the path conditions with propagated error
  std::vector<ref<Expr> > constraintsWithError;

  /// \brief The path probability
  double pathProbability;

  /// \brief The path length
  int branchCount;

public:
  SymbolicError(ArrayCache *arrayCache)
      : pathProbability(-1.0), branchCount(0) {
    errorState = ref<ErrorState>(new ErrorState(arrayCache));
  }

  SymbolicError(SymbolicError &symErr)
      : errorState(new ErrorState(*(symErr.errorState))),
        nonExited(symErr.nonExited), writesStack(symErr.writesStack),
        initWritesErrorStack(symErr.initWritesErrorStack),
        phiResultWidthList(symErr.phiResultWidthList),
        phiResultInitErrorStack(symErr.phiResultInitErrorStack),
        tmpPhiResultInitError(symErr.tmpPhiResultInitError),
        constraintsWithError(symErr.constraintsWithError),
        pathProbability(symErr.pathProbability),
        branchCount(symErr.branchCount) {}

  ~SymbolicError();

  /// \brief Compute the error introduced by the loop's computation, which
  /// is (initError + (tripCount - 1) * (endError - initError)). initError
  /// is the error at the first iteration of the loop, while endError is
  /// the error at the second iteration of the loop (e.g., between same target
  /// store instructions).
  static ref<Expr> computeLoopError(int64_t tripCount, ref<Expr> initError,
                                    ref<Expr> endError);

  /// \brief Detect if we should exit the loop (when about to execute the third
  /// iteration). This member function maintains a virtual iteration count for
  /// each executed loop in the notExited map. The count is incremented by 2
  /// upon first entry of the loop, and decremented at each iteration. When the
  /// virtual iteration count is a multiply of 2, the loop should be broken so
  /// that we exit to the exit block.
  bool breakLoop(Executor *executor, ExecutionState &state,
                 llvm::Instruction *inst, llvm::BasicBlock *&exit);

  /// \brief Create a read expression of a fresh variable
  ref<Expr> createFreshRead(Executor *executor, ExecutionState &state,
                            unsigned int width);

  /// \brief Deregister the loop in nonExited if it is exited due to iteration
  /// numbers too small (< 2).
  void deregisterLoopIfExited(Executor *executor, ExecutionState &state,
                              llvm::Instruction *inst);

  void outputComputedErrorBound(std::vector<std::pair<int, double> > bounds) {
    errorState->outputComputedErrorBound(bounds);
  }

  ConstraintManager outputErrorBound(llvm::Instruction *inst, double bound,
                                     std::string name,
                                     std::vector<ref<Expr> > &inputErrorList) {
    return errorState->outputErrorBound(inst, kleeBoundErrorExpr, bound, name,
                                        inputErrorList);
  }

  std::pair<ref<Expr>, ref<Expr> >
  propagateError(Executor *executor, KInstruction *ki, ref<Expr> result,
                 std::vector<Cell> &arguments, unsigned int phiResultWidth = 0);

  bool checkStoredError(ref<Expr> address) {
    return errorState->hasStoredError(address);
  }

  std::pair<ref<Expr>, ref<Expr> > retrieveStoredError(ref<Expr> address) {
    return errorState->retrieveStoredError(address);
  }

  std::string &getOutputString() { return errorState->getOutputString(); }

  void executeStore(ref<Expr> address, ref<Expr> value, ref<Expr> error,
                    ref<Expr> valueWithError, llvm::Instruction *inst);

  void storeError(ref<Expr> address, ref<Expr> error, ref<Expr> errorWithValue,
                  llvm::Instruction *inst) {
    errorState->executeStoreSimple(address, error, errorWithValue, inst);
  }

  void declareInputError(ref<Expr> address, ref<Expr> error) {
    errorState->declareInputError(address, error);
  }

  std::pair<ref<Expr>, ref<Expr> > executeLoad(llvm::Instruction *inst,
                                               ref<Expr> base,
                                               ref<Expr> address,
                                               ref<Expr> offset) {
    return errorState->executeLoad(inst, base, address, offset);
  }

  void setKleeBoundErrorExpr(ref<Expr> error) { kleeBoundErrorExpr = error; }

  void recomputePathProbability(llvm::BasicBlock *dst, llvm::BasicBlock *src) {
    branchCount++;
    if (pathProbability < 0) {
      pathProbability = EdgeProbability::instance->getEdgeProbability(dst, src);
      return;
    }
    pathProbability *= EdgeProbability::instance->getEdgeProbability(dst, src);
  }

  double getPathProbability() const { return pathProbability; }

  double getBranchCount() const { return branchCount; }

  std::vector<ref<Expr> > &getConstraintsWithError() {
    return constraintsWithError;
  }

  std::map<std::string, ref<Expr> > &getErrorExpressions() {
    return errorState->getStateErrorExpressions();
  }

  void addErrorConstraint(ref<Expr> error) {
    constraintsWithError.push_back(error);
  }

  /// print - Print the object content to stream
  void print(llvm::raw_ostream &os) const;

  /// dump - Print the object content to stderr
  void dump() const {
    print(llvm::errs());
    llvm::errs() << "\n";
  }

  ref<Expr> getScalingConstraint() {
    ref<Expr> scalingConstraint = errorState->getScalingConstraint();
    addErrorConstraint(scalingConstraint);
    return scalingConstraint;
  }
};
}

#endif /* KLEE_SYMBOLICERROR_H_ */
