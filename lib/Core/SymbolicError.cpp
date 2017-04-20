//===-- SymbolicError.cpp -------------------------------------------------===//
//
// The KLEE Symbolic Virtual Machine with Numerical Error Analysis Extension
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#include "SymbolicError.h"

#include "llvm/DebugInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Metadata.h"

using namespace klee;

ref<Expr> SymbolicError::getError(Executor *executor, ref<Expr> valueExpr,
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
        std::string errorName("_unspecified_error_" +
                              llvm::dyn_cast<ReadExpr>(concatExpr->getLeft())
                                  ->updates.root->name);
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
      assert(!"malformed expression");
  }

  if (value) {
    valueErrorMap[value] = ret;
  }
  return ret;
}

SymbolicError::~SymbolicError() {}

void SymbolicError::outputErrorBound(llvm::Instruction *inst, double bound) {
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

  stream << errorVar << " == (";
  e->print(stream);
  stream << ") && ";
  stream << "(" << errorVar << " <= " << bound << ") && ";
  stream << "(" << errorVar << " >= -" << bound << ")\n";
  stream.flush();
}

ref<Expr> SymbolicError::propagateError(Executor *executor,
                                        llvm::Instruction *instr,
                                        ref<Expr> result,
                                        std::vector<ref<Expr> > &arguments) {
  switch (instr->getOpcode()) {
  case llvm::Instruction::FAdd:
  case llvm::Instruction::Add: {
    llvm::Value *lOp = instr->getOperand(0);
    llvm::Value *rOp = instr->getOperand(1);

    ref<Expr> lError = getError(executor, arguments[0], lOp);
    ref<Expr> rError = getError(executor, arguments[1], rOp);

    ref<Expr> extendedLeft = lError;
    if (lError->getWidth() != arguments[0]->getWidth()) {
      extendedLeft = ZExtExpr::create(lError, arguments[0]->getWidth());
    }
    ref<Expr> extendedRight = rError;
    if (rError->getWidth() != arguments[1]->getWidth()) {
      extendedRight = ZExtExpr::create(rError, arguments[1]->getWidth());
    }
    ref<Expr> errorLeft = MulExpr::create(extendedLeft, arguments[0]);
    ref<Expr> errorRight = MulExpr::create(extendedRight, arguments[1]);
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

      ref<Expr> lError = getError(executor, arguments[0], lOp);
      ref<Expr> rError = getError(executor, arguments[1], rOp);

      ref<Expr> extendedLeft = lError;
      if (lError->getWidth() != arguments[0]->getWidth()) {
        extendedLeft = ZExtExpr::create(lError, arguments[0]->getWidth());
      }
      ref<Expr> extendedRight = rError;
      if (rError->getWidth() != arguments[1]->getWidth()) {
        extendedRight = ZExtExpr::create(rError, arguments[1]->getWidth());
      }

      ref<Expr> errorLeft = MulExpr::create(extendedLeft, arguments[0]);
      ref<Expr> errorRight = MulExpr::create(extendedRight, arguments[1]);
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

      ref<Expr> lError = getError(executor, arguments[0], lOp);
      ref<Expr> rError = getError(executor, arguments[1], rOp);

      ref<Expr> extendedLeft = lError;
      if (lError->getWidth() != arguments[0]->getWidth()) {
        extendedLeft = ZExtExpr::create(lError, arguments[0]->getWidth());
      }
      ref<Expr> extendedRight = rError;
      if (rError->getWidth() != arguments[1]->getWidth()) {
        extendedRight = ZExtExpr::create(rError, arguments[1]->getWidth());
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

      ref<Expr> lError = getError(executor, arguments[0], lOp);
      ref<Expr> rError = getError(executor, arguments[1], rOp);

      ref<Expr> extendedLeft = lError;
      if (lError->getWidth() != arguments[0]->getWidth()) {
        extendedLeft = ZExtExpr::create(lError, arguments[0]->getWidth());
      }
      ref<Expr> extendedRight = rError;
      if (rError->getWidth() != arguments[1]->getWidth()) {
        extendedRight = ZExtExpr::create(rError, arguments[1]->getWidth());
      }

      result = ExtractExpr::create(AddExpr::create(extendedLeft, extendedRight),
                                   0, Expr::Int8);
      valueErrorMap[instr] = result;
      return result;
    }
    case llvm::Instruction::SDiv: {
      llvm::Value *lOp = instr->getOperand(0);
      llvm::Value *rOp = instr->getOperand(1);

      ref<Expr> lError = getError(executor, arguments[0], lOp);
      ref<Expr> rError = getError(executor, arguments[1], rOp);

      ref<Expr> extendedLeft = lError;
      if (lError->getWidth() != arguments[0]->getWidth()) {
        extendedLeft = ZExtExpr::create(lError, arguments[0]->getWidth());
      }
      ref<Expr> extendedRight = rError;
      if (rError->getWidth() != arguments[1]->getWidth()) {
        extendedRight = ZExtExpr::create(rError, arguments[1]->getWidth());
      }

      result = ExtractExpr::create(AddExpr::create(extendedLeft, extendedRight),
                                   0, Expr::Int8);
      valueErrorMap[instr] = result;
      return result;
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
      std::map<llvm::Value *, ref<Expr> >::iterator opIt0 = valueErrorMap.find(
                                                        instr->getOperand(0)),
                                                    opIt1 = valueErrorMap.find(
                                                        instr->getOperand(1));
      ref<Expr> noError = ConstantExpr::create(0, Expr::Int8);
      ref<Expr> error0 =
          (opIt0 == valueErrorMap.end() ? noError : opIt0->second);
      ref<Expr> error1 =
          (opIt1 == valueErrorMap.end() ? noError : opIt1->second);
      return ExtractExpr::create(AddExpr::create(error0, error1), 0,
                                 Expr::Int8);
    }
    case llvm::Instruction::AShr:
    case llvm::Instruction::FPExt:
    case llvm::Instruction::FPTrunc:
    case llvm::Instruction::GetElementPtr:
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
      ref<Expr> error = ConstantExpr::create(0, Expr::Int8);
      llvm::Value *v = instr->getOperand(0);
      std::map<llvm::Value *, ref<Expr> >::iterator it = valueErrorMap.find(v);
      if (it != valueErrorMap.end()) {
        error = valueErrorMap[v];
      }
      if (error->getWidth() > Expr::Int8)
        error = ExtractExpr::create(error, 0, Expr::Int8);
      valueErrorMap[instr] = error;
      return error;
    }
    default: { assert(!"unhandled instruction"); }
  }
  return ConstantExpr::create(0, Expr::Int8);
}

void SymbolicError::executeStore(ref<Expr> address, ref<Expr> error) {
  if (error.isNull())
    return;

  if (ConstantExpr *cp = llvm::dyn_cast<ConstantExpr>(address)) {
    storedError[cp->getZExtValue()] = error;
    return;
  }
  assert(!"non-constant address");
}

ref<Expr> SymbolicError::executeLoad(llvm::Value *value, ref<Expr> address) {
  ref<Expr> error = ConstantExpr::create(0, Expr::Int8);
  if (ConstantExpr *cp = llvm::dyn_cast<ConstantExpr>(address)) {
    std::map<uintptr_t, ref<Expr> >::iterator it =
        storedError.find(cp->getZExtValue());
    if (it != storedError.end()) {
      error = it->second;
    }
  } else {
    assert(!"non-constant address");
  }
  valueErrorMap[value] = error;
  return error;
}

void SymbolicError::print(llvm::raw_ostream &os) const {
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

  os << "Output String:\n";
  os << outputString;
}
