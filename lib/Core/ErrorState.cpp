//===----- ErrorState.cpp -------------------------------------------------===//
//
// The KLEE Symbolic Virtual Machine with Numerical Error Analysis Extension
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "ErrorState.h"

#include "klee/CommandLine.h"
#include "klee/Config/Version.h"
#include "klee/Internal/Module/TripCounter.h"
#include "klee/util/PrettyExpressionBuilder.h"

#include "llvm/DebugInfo.h"

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Metadata.h"
#else
#include "llvm/BasicBlock.h"
#include "llvm/Function.h"
#include "llvm/Instructions.h"
#include "llvm/Metadata.h"
#endif

using namespace klee;

ref<Expr> ErrorState::getError(Executor *executor, ref<Expr> valueExpr,
                               llvm::Value *value) {
  ref<Expr> ret = ConstantExpr::create(0, Expr::Int8);

  if (ConcatExpr *concatExpr = llvm::dyn_cast<ConcatExpr>(valueExpr)) {
    const Array *concatArray =
        llvm::dyn_cast<ReadExpr>(concatExpr->getLeft())->updates.root;
    const Array *errorArray = arrayErrorArrayMap[concatArray];
    if (!errorArray) {
      // The error expression is not found; use an unspecified value
      std::string errorName(
          "_unspecified_error_" +
          llvm::dyn_cast<ReadExpr>(concatExpr->getLeft())->updates.root->name);
      const Array *newErrorArray =
          errorArrayCache.CreateArray(errorName, Expr::Int8);
      UpdateList ul(newErrorArray, 0);
      arrayErrorArrayMap[concatArray] = newErrorArray;
      ret = ReadExpr::create(ul, ConstantExpr::alloc(0, Expr::Int8));
    } else {
      UpdateList ul(errorArray, 0);
      ret = ReadExpr::create(ul, ConstantExpr::alloc(0, Expr::Int8));
    }
  } else if (ReadExpr *readExpr = llvm::dyn_cast<ReadExpr>(valueExpr)) {
    const Array *readArray = readExpr->updates.root;
    const Array *errorArray = arrayErrorArrayMap[readArray];
    if (!errorArray) {
      // The error expression is not found; use an unspecified value
      std::string errorName("_unspecified_error_" +
                            readExpr->updates.root->name);
      const Array *newErrorArray =
          errorArrayCache.CreateArray(errorName, Expr::Int8);
      UpdateList ul(newErrorArray, 0);
      arrayErrorArrayMap[readArray] = newErrorArray;
      ret = ReadExpr::create(ul, ConstantExpr::alloc(0, Expr::Int8));
    } else {
      UpdateList ul(errorArray, 0);
      ret = ReadExpr::create(ul, ConstantExpr::alloc(0, Expr::Int8));
    }
  } else if (SExtExpr *sExtExpr = llvm::dyn_cast<SExtExpr>(valueExpr)) {
    ret = getError(executor, sExtExpr->getKid(0));
  } else if (llvm::isa<AddExpr>(valueExpr)) {
    ref<Expr> lhsError = getError(executor, valueExpr->getKid(0));
    ref<Expr> rhsError = getError(executor, valueExpr->getKid(1));
    // TODO: Add correct error expression here
    ret = AddExpr::create(lhsError, rhsError);
  } else if (!llvm::isa<ConstantExpr>(valueExpr)) {
    // FIXME: We assume all other symbolic expressions have an error which is
    // the sum of all of the errors of its reads
    for (unsigned i = 0; i < valueExpr->getNumKids(); ++i) {
      ret = AddExpr::create(getError(executor, valueExpr->getKid(i)), ret);
    }
  }
  return ret;
}

ErrorState::~ErrorState() {}

ConstraintManager
ErrorState::outputErrorBound(llvm::Instruction *inst, ref<Expr> error,
                             double bound,
                             std::vector<ref<Expr> > &_inputErrorList) {
  ConstraintManager ret;

  std::string errorVar;
  llvm::raw_string_ostream errorVarStream(errorVar);
  errorVarStream << "__error__" << reinterpret_cast<uint64_t>(error.get());
  errorVarStream.flush();

  ref<Expr> errorVarExpr = ReadExpr::create(
      UpdateList(errorArrayCache.CreateArray(errorVar, Expr::Int8), 0),
      ConstantExpr::createPointer(0));

  ret.addConstraint(EqExpr::create(errorVarExpr, error));

  // We assume a simple rational bound, not more than 4 fractional digits
  unsigned divisor = 10000;
  int dividend = (int)floor(bound * divisor);
  dividend = (dividend < 0) ? -dividend : dividend;

  ref<Expr> lowerBound = ExtractExpr::create(
      SDivExpr::create(
          SubExpr::alloc(ConstantExpr::create(0, Expr::Int64),
                         ConstantExpr::create(dividend, Expr::Int64)),
          ConstantExpr::create(divisor, Expr::Int64)),
      0, Expr::Int8);
  ref<Expr> upperBound = ExtractExpr::create(
      SDivExpr::alloc(ConstantExpr::create(dividend, Expr::Int64),
                      ConstantExpr::create(divisor, Expr::Int64)),
      0, Expr::Int8);

  ret.addConstraint(SgeExpr::create(errorVarExpr, lowerBound));
  ret.addConstraint(SleExpr::create(errorVarExpr, upperBound));

  llvm::raw_string_ostream stream(outputString);
  if (!outputString.empty()) {
    stream << "\n------------------------\n";
  }
  if (llvm::MDNode *n = inst->getMetadata("dbg")) {
    llvm::DILocation loc(n);
    unsigned line = loc.getLineNumber();
    llvm::StringRef file = loc.getFilename();
    llvm::StringRef dir = loc.getDirectory();
    stream << "Line " << line << " of " << dir.str() << "/" << file.str();
    if (llvm::BasicBlock *bb = inst->getParent()) {
      if (llvm::Function *func = bb->getParent()) {
        stream << " (" << func->getName() << ")";
      }
    }
    stream << ": ";
  } else if (llvm::BasicBlock *bb = inst->getParent()) {
    if (llvm::Function *func = bb->getParent()) {
      stream << func->getName() << ": ";
    }
  }

  stream << "\nOutput Error: ";
  stream << PrettyExpressionBuilder::construct(error);
  stream << "\nAbsolute Bound: " << bound << "\n";
  stream.flush();

  _inputErrorList = inputErrorList;
  return ret;
}

ref<Expr> ErrorState::propagateError(Executor *executor,
                                     llvm::Instruction *instr, ref<Expr> result,
                                     std::vector<Cell> &arguments) {
  switch (instr->getOpcode()) {
  case llvm::Instruction::PHI: { return arguments.at(0).error; }
  case llvm::Instruction::Call:
  case llvm::Instruction::Invoke: {
    // Return a dummy error
    return ConstantExpr::create(0, Expr::Int8);
  }
  case llvm::Instruction::FAdd:
  case llvm::Instruction::Add: {
    llvm::Value *lOp = instr->getOperand(0);
    llvm::Value *rOp = instr->getOperand(1);

    ref<Expr> lError = arguments.at(0).error;
    ref<Expr> lValue = arguments.at(0).value;
    ref<Expr> rError = arguments.at(1).error;
    ref<Expr> rValue = arguments.at(1).value;
    if (lError.isNull()) {
      lError = getError(executor, lValue, lOp);
    }
    if (rError.isNull()) {
      rError = getError(executor, rValue, rOp);
    }

    ref<Expr> extendedLeft = lError;
    if (lError->getWidth() != lValue->getWidth()) {
      extendedLeft = ZExtExpr::create(lError, lValue->getWidth());
    }
    ref<Expr> extendedRight = rError;
    if (rError->getWidth() != rValue->getWidth()) {
      extendedRight = ZExtExpr::create(rError, rValue->getWidth());
    }
    ref<Expr> errorLeft = MulExpr::create(extendedLeft, lValue);
    ref<Expr> errorRight = MulExpr::create(extendedRight, rValue);
    ref<Expr> resultError = AddExpr::create(errorLeft, errorRight);

    result = ExtractExpr::create(
        result->isZero() ? result : UDivExpr::create(resultError, result), 0,
        Expr::Int8);
    return result;
  }
  case llvm::Instruction::FSub:
  case llvm::Instruction::Sub: {
    llvm::Value *lOp = instr->getOperand(0);
    llvm::Value *rOp = instr->getOperand(1);

    ref<Expr> lError = arguments.at(0).error;
    ref<Expr> lValue = arguments.at(0).value;
    ref<Expr> rError = arguments.at(1).error;
    ref<Expr> rValue = arguments.at(1).value;

    if (lError.isNull()) {
      lError = getError(executor, lValue, lOp);
    }
    if (rError.isNull()) {
      rError = getError(executor, rValue, rOp);
    }

    ref<Expr> extendedLeft = lError;
    if (lError->getWidth() != lValue->getWidth()) {
      extendedLeft = ZExtExpr::create(lError, lValue->getWidth());
    }
    ref<Expr> extendedRight = rError;
    if (rError->getWidth() != rValue->getWidth()) {
      extendedRight = ZExtExpr::create(rError, rValue->getWidth());
    }

    ref<Expr> errorLeft = MulExpr::create(extendedLeft, lValue);
    ref<Expr> errorRight = MulExpr::create(extendedRight, rValue);
    ref<Expr> resultError = AddExpr::create(errorLeft, errorRight);

    result = ExtractExpr::create(
        result->isZero() ? result : UDivExpr::create(resultError, result), 0,
        Expr::Int8);
    return result;
  }
  case llvm::Instruction::FMul:
  case llvm::Instruction::Mul: {
    llvm::Value *lOp = instr->getOperand(0);
    llvm::Value *rOp = instr->getOperand(1);

    ref<Expr> lError = arguments.at(0).error;
    ref<Expr> lValue = arguments.at(0).value;
    ref<Expr> rError = arguments.at(1).error;
    ref<Expr> rValue = arguments.at(1).value;

    if (lError.isNull()) {
      lError = getError(executor, lValue, lOp);
    }
    if (rError.isNull()) {
      rError = getError(executor, rValue, rOp);
    }

    result = AddExpr::create(lError, rError);
    return result;
  }
  case llvm::Instruction::FDiv:
  case llvm::Instruction::UDiv: {
    llvm::Value *lOp = instr->getOperand(0);
    llvm::Value *rOp = instr->getOperand(1);

    ref<Expr> lError = arguments.at(0).error;
    ref<Expr> lValue = arguments.at(0).value;
    ref<Expr> rError = arguments.at(1).error;
    ref<Expr> rValue = arguments.at(1).value;

    if (lError.isNull()) {
      lError = getError(executor, lValue, lOp);
    }
    if (rError.isNull()) {
      rError = getError(executor, rValue, rOp);
    }

    result = AddExpr::create(lError, rError);
    return result;
  }
  case llvm::Instruction::SDiv: {
    llvm::Value *lOp = instr->getOperand(0);
    llvm::Value *rOp = instr->getOperand(1);

    ref<Expr> lError = arguments.at(0).error;
    ref<Expr> lValue = arguments.at(0).value;
    ref<Expr> rError = arguments.at(1).error;
    ref<Expr> rValue = arguments.at(1).value;

    if (lError.isNull()) {
      lError = getError(executor, lValue, lOp);
    }
    if (rError.isNull()) {
      rError = getError(executor, rValue, rOp);
    }

    result = AddExpr::create(lError, rError);
    return result;
  }
  case llvm::Instruction::GetElementPtr: {
    // Simply propagate error of the first argument
    ref<Expr> error = arguments.at(0).error;
    if (error.isNull()) {
      error = ConstantExpr::create(0, Expr::Int8);
    }

    if (!hasStoredError(result)) {
      ref<Expr> baseError = retrieveStoredError(arguments[0].value);
      // The following also performs nullity check on the result of the cast. If
      // the type does not match, re is NULL
      if (ReadExpr *re = llvm::dyn_cast<ReadExpr>(baseError)) {
        std::string errorName = re->updates.root->name;
        const Array *newErrorArray =
            errorArrayCache.CreateArray(errorName, Expr::Int8);
        UpdateList ul(newErrorArray, 0);
        ref<Expr> offset = SubExpr::create(result, arguments[0].value);
        ref<Expr> newError = ReadExpr::create(ul, offset);
        executeStoreSimple(instr, result, newError);
      }
    }
    return error;
  }
  case llvm::Instruction::FCmp:
  case llvm::Instruction::ICmp: {
    // We assume that decision is precisely made
    return ConstantExpr::create(0, Expr::Int8);
  }
  case llvm::Instruction::FRem:
  case llvm::Instruction::SRem:
  case llvm::Instruction::URem:
  case llvm::Instruction::And:
  case llvm::Instruction::Or:
  case llvm::Instruction::Xor: {
    // Result in summing up of the errors of its arguments
    ref<Expr> error0 = arguments.at(0).error;
    ref<Expr> error1 = arguments.at(1).error;

    if (error0.isNull()) {
      error0 = ConstantExpr::create(0, Expr::Int8);
    }

    if (error1.isNull()) {
      error1 = ConstantExpr::create(0, Expr::Int8);
    }
    return ExtractExpr::create(AddExpr::create(error0, error1), 0, Expr::Int8);
  }
  case llvm::Instruction::AShr:
  case llvm::Instruction::FPExt:
  case llvm::Instruction::FPTrunc:
  case llvm::Instruction::LShr:
  case llvm::Instruction::Shl:
  case llvm::Instruction::SExt:
  case llvm::Instruction::Trunc:
  case llvm::Instruction::ZExt:
  case llvm::Instruction::FPToSI:
  case llvm::Instruction::FPToUI:
  case llvm::Instruction::SIToFP:
  case llvm::Instruction::UIToFP:
  case llvm::Instruction::IntToPtr:
  case llvm::Instruction::PtrToInt:
  case llvm::Instruction::BitCast: {
    // Simply propagate error of the first argument
    ref<Expr> error = arguments.at(0).error;
    if (error.isNull()) {
      error = ConstantExpr::create(0, Expr::Int8);
    }
    return error;
  }
  default: { assert(!"unhandled instruction"); }
  }
  return ConstantExpr::create(0, Expr::Int8);
}

void ErrorState::executeStoreSimple(llvm::Instruction *inst, ref<Expr> address,
                                    ref<Expr> error) {
  if (error.isNull())
    return;

  // At store instruction, we store new error by a multiply of the stored error
  // with the loop trip count.
  if (ConstantExpr *cp = llvm::dyn_cast<ConstantExpr>(address)) {
    uint64_t intAddress = cp->getZExtValue();
    storedError[intAddress] = error;
    return;
  }
  assert(!"non-constant address");
}

ref<Expr> ErrorState::retrieveStoredError(ref<Expr> address) const {
  ref<Expr> error = ConstantExpr::create(0, Expr::Int8);

  if (ConstantExpr *cp = llvm::dyn_cast<ConstantExpr>(address)) {
    std::map<uintptr_t, ref<Expr> >::const_iterator it =
        storedError.find(cp->getZExtValue());
    if (it != storedError.end()) {
      error = it->second;
    }
  } else {
    // it is possible that the address is non-constant
    // in that case assume the error to be zero
    // assert(!"non-constant address");
    error = ConstantExpr::create(0, Expr::Int8);
  }
  return error;
}

bool ErrorState::hasStoredError(ref<Expr> address) const {
  if (ConstantExpr *cp = llvm::dyn_cast<ConstantExpr>(address)) {
    std::map<uintptr_t, ref<Expr> >::const_iterator it =
        storedError.find(cp->getZExtValue());
    if (it != storedError.end()) {
      return true;
    } else
      return false;
  } else
    return false;
}

ref<Expr> ErrorState::executeLoad(llvm::Value *value, ref<Expr> address) {
  return retrieveStoredError(address);
}

void ErrorState::overwriteWith(ref<ErrorState> overwriting) {
  for (std::map<uintptr_t, ref<Expr> >::iterator
           it = overwriting->storedError.begin(),
           ie = overwriting->storedError.end();
       it != ie; ++it) {
    storedError[it->first] = it->second;
  }
}

void ErrorState::print(llvm::raw_ostream &os) const {
  os << "Array->Error Array:\n";
  for (std::map<const Array *, const Array *>::const_iterator
           it = arrayErrorArrayMap.begin(),
           ie = arrayErrorArrayMap.end();
       it != ie; ++it) {
    os << "[" << it->first->name << "," << it->second->name << "]\n";
  }

  os << "Store:\n";
  for (std::map<uintptr_t, ref<Expr> >::const_iterator it = storedError.begin(),
                                                       ie = storedError.end();
       it != ie; ++it) {
    os << it->first << ": ";
    it->second->print(os);
    os << "\n";
  }

  os << "Output String: ";
  if (outputString.empty())
    os << "(empty)";
  else
    os << outputString;

  os << "\nInput Errors: ";
  if (inputErrorList.empty())
    os << "(empty)";
  else {
    for (std::vector<ref<Expr> >::const_iterator it = inputErrorList.begin(),
                                                 ie = inputErrorList.end();
         it != ie; ++it) {
      os << "\n";
      (*it)->print(os);
    }
  }
}
