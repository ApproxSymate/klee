/*
 * SymbolicError.cpp
 *
 *  Created on: 18 Aug 2016
 *      Author: himeshi
 */
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
        std::string errorName("_fractional_error_" +
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
        std::string errorName("_fractional_error_" +
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

void SymbolicError::outputErrorBound(llvm::Instruction *inst) {
  ref<Expr> e =
      valueErrorMap[llvm::dyn_cast<llvm::Instruction>(inst->getOperand(0))];
  if (e.isNull()) {
    e = ConstantExpr::create(0, Expr::Int8);
  }
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
  e->print(stream);
  stream.flush();
}

ref<Expr> SymbolicError::propagateError(Executor *executor,
                                        llvm::Instruction *instr,
                                        ref<Expr> result,
                                        std::vector<ref<Expr> > &arguments) {
  switch (instr->getOpcode()) {
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
    ref<Expr> errorLeft =
        MulExpr::create(extendedLeft.get(), arguments[0].get());
    ref<Expr> errorRight =
        MulExpr::create(extendedRight.get(), arguments[1].get());
    ref<Expr> resultError = AddExpr::create(errorLeft, errorRight);
    valueErrorMap[instr] = UDivExpr::create(resultError, result);
    return valueErrorMap[instr];
    }
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

      ref<Expr> errorLeft = MulExpr::create(extendedLeft.get(), arguments[0]);
      ref<Expr> errorRight = MulExpr::create(extendedRight.get(), arguments[1]);
      ref<Expr> resultError = AddExpr::create(errorLeft, errorRight);
      valueErrorMap[instr] = UDivExpr::create(resultError, result);
      return valueErrorMap[instr];
    }
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

      valueErrorMap[instr] = AddExpr::create(extendedLeft, extendedRight);
      return valueErrorMap[instr];
    }
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

      valueErrorMap[instr] = AddExpr::create(extendedLeft, extendedRight);
      return valueErrorMap[instr];
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

      valueErrorMap[instr] = AddExpr::create(extendedLeft, extendedRight);
      return valueErrorMap[instr];
    }
  }
  return ConstantExpr::create(0, Expr::Int8);
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

  os << "Output String:\n";
  os << outputString;
}
