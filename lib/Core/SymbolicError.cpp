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

ref<Expr> SymbolicError::getError(Executor *executor, Expr *value) {
  ref<Expr> errorAmount = valueErrorMap[value];
  llvm::errs() << "In get error\n";
  if (!errorAmount.get()) {
    if (llvm::isa<ConcatExpr>(*value)) {
      ConcatExpr *concatExpr = llvm::dyn_cast<ConcatExpr>(value);
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
        ref<Expr> newReadExpr =
            ReadExpr::create(ul, ConstantExpr::alloc(0, Expr::Int8));
        valueErrorMap[value] = newReadExpr;
        return newReadExpr;
      }
      UpdateList ul(errorArray, 0);
      ref<Expr> newReadExpr =
          ReadExpr::create(ul, ConstantExpr::alloc(0, Expr::Int8));
      valueErrorMap[value] = newReadExpr;
      return newReadExpr;

    } else if (llvm::isa<ReadExpr>(*value)) {
      ReadExpr *readExpr = llvm::dyn_cast<ReadExpr>(value);
      const Array *readArray = readExpr->updates.root;
      const Array *errorArray = arrayErrorArrayMap[readArray];
      if (!errorArray) {
        std::string errorName("_fractional_error_" +
                              readExpr->updates.root->name);
        const Array *newErrorArray =
            errorArrayCache.CreateArray(errorName, Expr::Int8);
        UpdateList ul(newErrorArray, 0);
        arrayErrorArrayMap[readArray] = newErrorArray;
        ref<Expr> newReadExpr =
            ReadExpr::create(ul, ConstantExpr::alloc(0, Expr::Int8));
        valueErrorMap[value] = newReadExpr;
        return newReadExpr;
      }
      UpdateList ul(errorArray, 0);
      ref<Expr> newReadExpr =
          ReadExpr::create(ul, ConstantExpr::alloc(0, Expr::Int8));
      valueErrorMap[value] = newReadExpr;
      return newReadExpr;

    } else if (llvm::isa<ConstantExpr>(value)) {
      return ConstantExpr::alloc(0, Expr::Int8);
    } else if (llvm::isa<SExtExpr>(value)) {
      llvm::errs() << "In sext\n";
      value->dump();
      SExtExpr *sExtExpr = llvm::dyn_cast<SExtExpr>(value);
      return getError(executor, sExtExpr->getKid(0).get());
    } else if (llvm::isa<AddExpr>(value)) {
      ref<Expr> lhsError = getError(executor, value->getKid(0).get());
      ref<Expr> rhsError = getError(executor, value->getKid(1).get());
      // TODO: Add correct error expression here
      return AddExpr::create(lhsError, rhsError);
    } else {
      assert(!"malformed expression");
    }
  }

  return errorAmount;
}

SymbolicError::~SymbolicError() {}

ref<Expr> SymbolicError::getCurrentError() {
  return ConstantExpr::create(0, Expr::Int8);
}

void SymbolicError::addOutput(llvm::Instruction *inst) {
  ref<Expr> e = getCurrentError();
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
    ref<Expr> lError = valueErrorMap[arguments[0].get()];
    ref<Expr> rError = valueErrorMap[arguments[1].get()];
    if (!lError.get()) {
      lError = getError(executor, arguments[0].get());
    }
    if (!rError.get()) {
      rError = getError(executor, arguments[1].get());
    }

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
    valueErrorMap[result.get()] = UDivExpr::create(resultError, result.get());
    return valueErrorMap[result.get()];
  }
  case llvm::Instruction::Sub: {
    ref<Expr> lError = valueErrorMap[arguments[0].get()];
    ref<Expr> rError = valueErrorMap[arguments[1].get()];
    if (!lError.get()) {
      lError = getError(executor, arguments[0].get());
    }
    if (!rError.get()) {
      rError = getError(executor, arguments[1].get());
    }

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
    valueErrorMap[result.get()] = UDivExpr::create(resultError, result.get());
    return valueErrorMap[result.get()];
  }
  case llvm::Instruction::Mul: {
    ref<Expr> lError = valueErrorMap[arguments[0].get()];
    ref<Expr> rError = valueErrorMap[arguments[1].get()];
    if (!lError.get()) {
      lError = getError(executor, arguments[0].get());
    }
    if (!rError.get()) {
      rError = getError(executor, arguments[1].get());
    }

    ref<Expr> extendedLeft = lError;
    if (lError->getWidth() != arguments[0]->getWidth()) {
      extendedLeft = ZExtExpr::create(lError, arguments[0]->getWidth());
    }
    ref<Expr> extendedRight = rError;
    if (rError->getWidth() != arguments[1]->getWidth()) {
      extendedRight = ZExtExpr::create(rError, arguments[1]->getWidth());
    }

    valueErrorMap[result.get()] =
        AddExpr::create(extendedLeft.get(), extendedRight.get());
    return valueErrorMap[result.get()];
    }
    case llvm::Instruction::UDiv: {
      ref<Expr> lError = valueErrorMap[arguments[0].get()];
      ref<Expr> rError = valueErrorMap[arguments[1].get()];
      if (!lError.get()) {
        lError = getError(executor, arguments[0].get());
      }
      if (!rError.get()) {
        rError = getError(executor, arguments[1].get());
      }

      ref<Expr> extendedLeft = lError;
      if (lError->getWidth() != arguments[0]->getWidth()) {
        extendedLeft = ZExtExpr::create(lError, arguments[0]->getWidth());
      }
      ref<Expr> extendedRight = rError;
      if (rError->getWidth() != arguments[1]->getWidth()) {
        extendedRight = ZExtExpr::create(rError, arguments[1]->getWidth());
      }

      valueErrorMap[result.get()] =
          AddExpr::create(extendedLeft.get(), extendedRight.get());
      return valueErrorMap[result.get()];
    }
    case llvm::Instruction::SDiv: {
      ref<Expr> lError = valueErrorMap[arguments[0].get()];
      ref<Expr> rError = valueErrorMap[arguments[1].get()];
      if (!lError.get()) {
        lError = getError(executor, arguments[0].get());
      }
      if (!rError.get()) {
        rError = getError(executor, arguments[1].get());
      }

      ref<Expr> extendedLeft = lError;
      if (lError->getWidth() != arguments[0]->getWidth()) {
        extendedLeft = ZExtExpr::create(lError, arguments[0]->getWidth());
      }
      ref<Expr> extendedRight = rError;
      if (rError->getWidth() != arguments[1]->getWidth()) {
        extendedRight = ZExtExpr::create(rError, arguments[1]->getWidth());
      }

      valueErrorMap[result.get()] =
          AddExpr::create(extendedLeft.get(), extendedRight.get());
      return valueErrorMap[result.get()];
    }
  }
  return ConstantExpr::create(0, Expr::Int8);
}
