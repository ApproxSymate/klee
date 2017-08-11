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

  if (value) {
    ref<Expr> errorAmount = valueErrorMap[value];

    if (!errorAmount.isNull())
      return errorAmount;
  }

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

  if (value) {
    valueErrorMap[value] = ret;
  }
  return ret;
}

ErrorState::~ErrorState() {}

void ErrorState::outputErrorBound(llvm::Instruction *inst, double bound) {
  ref<Expr> e =
      valueErrorMap[llvm::dyn_cast<llvm::Instruction>(inst->getOperand(0))];
  if (e.isNull()) {
    e = ConstantExpr::create(0, Expr::Int8);
  }

  std::string errorVar;
  llvm::raw_string_ostream errorVarStream(errorVar);
  errorVarStream << "__error__" << reinterpret_cast<uint64_t>(e.get());
  errorVarStream.flush();

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

  stream << "\nAbsolute bound = ";
  stream << PrettyExpressionBuilder::construct(e);
  stream.flush();
}

ref<Expr> ErrorState::propagateError(Executor *executor,
                                     llvm::Instruction *instr, ref<Expr> result,
                                     std::vector<Cell> &arguments) {
  switch (instr->getOpcode()) {
  case llvm::Instruction::PHI: {
    ref<Expr> error = arguments.at(0).error;
    valueErrorMap[instr] = error;
    return error;
  }
  case llvm::Instruction::Call:
  case llvm::Instruction::Invoke: {
    ref<Expr> dummyError = ConstantExpr::create(0, Expr::Int8);
    if (llvm::CallInst *ci = llvm::dyn_cast<llvm::CallInst>(instr)) {
      if (llvm::Function *callee = ci->getCalledFunction()) {
        llvm::Function::ArgumentListType &argList = callee->getArgumentList();
        unsigned i = 0;
        for (llvm::Function::ArgumentListType::iterator it1 = argList.begin(),
                                                        ie1 = argList.end();
             it1 != ie1; ++it1) {
          llvm::Value *formalOp = &(*it1);
          valueErrorMap[formalOp] = arguments.at(i).error;
          ++i;
        }
      }
    }
    return dummyError;
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
    valueErrorMap[instr] = result;
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
    valueErrorMap[instr] = result;
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

    ref<Expr> extendedLeft = lError;
    if (lError->getWidth() != lValue->getWidth()) {
      extendedLeft = ZExtExpr::create(lError, lValue->getWidth());
    }
    ref<Expr> extendedRight = rError;
    if (rError->getWidth() != rValue->getWidth()) {
      extendedRight = ZExtExpr::create(rError, rValue->getWidth());
    }

    result = ExtractExpr::create(AddExpr::create(extendedLeft, extendedRight),
                                 0, Expr::Int8);
    valueErrorMap[instr] = result;
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

    ref<Expr> extendedLeft = lError;
    if (lError->getWidth() != lValue->getWidth()) {
      extendedLeft = ZExtExpr::create(lError, lValue->getWidth());
    }
    ref<Expr> extendedRight = rError;
    if (rError->getWidth() != rValue->getWidth()) {
      extendedRight = ZExtExpr::create(rError, rValue->getWidth());
    }

    result = ExtractExpr::create(AddExpr::create(extendedLeft, extendedRight),
                                 0, Expr::Int8);
    valueErrorMap[instr] = result;
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

    ref<Expr> extendedLeft = lError;
    if (lError->getWidth() != lValue->getWidth()) {
      extendedLeft = ZExtExpr::create(lError, lValue->getWidth());
    }
    ref<Expr> extendedRight = rError;
    if (rError->getWidth() != rValue->getWidth()) {
      extendedRight = ZExtExpr::create(rError, rValue->getWidth());
    }

    result = ExtractExpr::create(AddExpr::create(extendedLeft, extendedRight),
                                 0, Expr::Int8);
    valueErrorMap[instr] = result;
    return result;
  }
  case llvm::Instruction::GetElementPtr: {
    // Check if base is symbolic and whether a symbolic error value already
    // exists for the newly pointed element
    ref<Expr> newError;
    if (isInStoredError(result)) {
      newError = retrieveStoredError(result);
    } else {
      ref<Expr> error = retrieveStoredError(arguments[0].value);
      std::string errorName =
          llvm::dyn_cast<ReadExpr>(error)->updates.root->name;
      const Array *newErrorArray =
          errorArrayCache.CreateArray(errorName, Expr::Int8);
      UpdateList ul(newErrorArray, 0);
      ref<Expr> offset = SubExpr::create(result, arguments[0].value);
      newError = ReadExpr::create(ul, offset);
      executeStoreSimple(instr, result, newError);
    }
    return newError;
  }
  case llvm::Instruction::FCmp:
  case llvm::Instruction::ICmp: {
    // We assume that decision is precisely made
    ref<Expr> error = ConstantExpr::create(0, Expr::Int8);
    valueErrorMap[instr] = error;
    return error;
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
      ref<Expr> noError = ConstantExpr::create(0, Expr::Int8);
      std::map<llvm::Value *, ref<Expr> >::iterator opIt0 =
          valueErrorMap.find(instr->getOperand(0));
      error0 = (opIt0 == valueErrorMap.end() ? noError : opIt0->second);
    }

    if (error1.isNull()) {
      ref<Expr> noError = ConstantExpr::create(0, Expr::Int8);
      std::map<llvm::Value *, ref<Expr> >::iterator opIt1 =
          valueErrorMap.find(instr->getOperand(1));
      error1 = (opIt1 == valueErrorMap.end() ? noError : opIt1->second);
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
      llvm::Value *v = instr->getOperand(0);
      std::map<llvm::Value *, ref<Expr> >::iterator it = valueErrorMap.find(v);
      if (it != valueErrorMap.end()) {
        error = valueErrorMap[v];
      }
      if (error->getWidth() > Expr::Int8)
        error = ExtractExpr::create(error, 0, Expr::Int8);
    }
    valueErrorMap[instr] = error;
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

ref<Expr> ErrorState::executeLoad(llvm::Value *value, ref<Expr> address) {
  ref<Expr> error = retrieveStoredError(address);
  valueErrorMap[value] = error;
  return error;
}

void ErrorState::overwriteWith(ref<ErrorState> overwriting) {
  for (std::map<uintptr_t, ref<Expr> >::iterator
           it = overwriting->storedError.begin(),
           ie = overwriting->storedError.end();
       it != ie; ++it) {
    storedError[it->first] = it->second;
  }

  for (std::map<llvm::Value *, ref<Expr> >::iterator
           it = overwriting->valueErrorMap.begin(),
           ie = overwriting->valueErrorMap.end();
       it != ie; ++it) {
    valueErrorMap[it->first] = it->second;
  }
}

void ErrorState::print(llvm::raw_ostream &os) const {
  os << "Value->Expression:\n";
  for (std::map<llvm::Value *, ref<Expr> >::const_iterator
           it = valueErrorMap.begin(),
           ie = valueErrorMap.end();
       it != ie; ++it) {
    os << "[";
    it->first->print(os);
    os << ",";
    it->second->print(os);
    os << "]\n";
  }

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
}
