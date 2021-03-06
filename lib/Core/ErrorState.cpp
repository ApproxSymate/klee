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
          errorArrayCache->CreateArray(errorName, Expr::Int8);
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
          errorArrayCache->CreateArray(errorName, Expr::Int8);
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

void ErrorState::outputComputedErrorBound(
    std::vector<std::pair<int, double> > bounds) {
  llvm::raw_string_ostream stream(outputString);

  uint64_t size = inputErrorList.size();
  for (unsigned i = 0; i < size; ++i) {
    stream << "Error Bound for ";
    stream << PrettyExpressionBuilder::construct(inputErrorList.at(i));
    stream << " is ";
    std::pair<int, double> p(bounds.at(i));

    switch (p.first) {
    case 1:
      stream << "infinity";
      break;
    case 2:
      stream << "epsilon";
      break;
    default:
      stream << p.second;
      break;
    }
    stream << "\n";
  }
  stream.flush();
}

ConstraintManager
ErrorState::outputErrorBound(llvm::Instruction *inst, ref<Expr> error,
                             double bound, std::string name,
                             std::vector<ref<Expr> > &_inputErrorList) {
  ConstraintManager ret;

  std::string errorVar;
  ref<Expr> errorVarExpr = ReadExpr::create(
      UpdateList(errorArrayCache->CreateArray(errorVar, Expr::Int8), 0),
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

  stream << "\nOutput Error of " << name << " : ";
  stream << PrettyExpressionBuilder::construct(error);
  stream << "\nAbsolute Bound: " << bound << "\n";
  stream.flush();

  _inputErrorList = inputErrorList;
  return ret;
}

std::pair<ref<Expr>, ref<Expr> >
ErrorState::propagateError(Executor *executor, llvm::Instruction *instr,
                           ref<Expr> result, std::vector<Cell> &arguments) {
  ref<Expr> nullExpr;
  switch (instr->getOpcode()) {
  case llvm::Instruction::PHI: {
    return std::pair<ref<Expr>, ref<Expr> >(arguments.at(0).error, nullExpr);
  }
  case llvm::Instruction::Call:
  case llvm::Instruction::Invoke: {
    // Return a dummy error
    return std::pair<ref<Expr>, ref<Expr> >(ConstantExpr::create(0, Expr::Int8),
                                            nullExpr);
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

    int leftWidth = errorLeft->getWidth();
    int rightWidth = errorRight->getWidth();
    if (leftWidth < rightWidth) {
      errorLeft = ZExtExpr::create(errorLeft, rightWidth);
    } else if (leftWidth > rightWidth) {
      errorRight = ZExtExpr::create(errorRight, leftWidth);
    }

    ref<Expr> resultError = AddExpr::create(errorLeft, errorRight);

    result = ExtractExpr::create(
        result->isZero() ? result : UDivExpr::create(resultError, result), 0,
        Expr::Int8);
    return std::pair<ref<Expr>, ref<Expr> >(result, nullExpr);
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

    int leftWidth = errorLeft->getWidth();
    int rightWidth = errorRight->getWidth();
    if (leftWidth < rightWidth) {
      errorLeft = ZExtExpr::create(errorLeft, rightWidth);
    } else if (leftWidth > rightWidth) {
      errorRight = ZExtExpr::create(errorRight, leftWidth);
    }

    ref<Expr> resultError = SubExpr::create(errorLeft, errorRight);

    result = ExtractExpr::create(
        result->isZero() ? result : UDivExpr::create(resultError, result), 0,
        Expr::Int8);
    return std::pair<ref<Expr>, ref<Expr> >(result, nullExpr);
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

    ref<Expr> product = MulExpr::create(rError, lError);
    result = AddExpr::create(lError, rError);
    result = SubExpr::create(result, product);
    return std::pair<ref<Expr>, ref<Expr> >(result, nullExpr);
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

    ref<Expr> divisor = ConstantExpr::create(1, Expr::Int8);
    divisor = SubExpr::create(divisor, rError);
    result = SubExpr::create(lError, rError);
    result = ExtractExpr::create(
        divisor->isZero() ? result : UDivExpr::create(result, divisor), 0,
        Expr::Int8);
    return std::pair<ref<Expr>, ref<Expr> >(result, nullExpr);
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

    ref<Expr> divisor = ConstantExpr::create(1, Expr::Int8);
    divisor = SubExpr::create(divisor, rError);
    result = SubExpr::create(lError, rError);
    result = ExtractExpr::create(
        divisor->isZero() ? result : UDivExpr::create(result, divisor), 0,
        Expr::Int8);
    return std::pair<ref<Expr>, ref<Expr> >(result, nullExpr);
  }
  case llvm::Instruction::FCmp:
  case llvm::Instruction::ICmp: {
    llvm::CmpInst *ci = cast<llvm::CmpInst>(instr);

    //(1 - ex)
    ref<Expr> lError = SubExpr::create(ConstantExpr::create(1, Expr::Int8),
                                       arguments.at(0).error);
    ref<Expr> rError = SubExpr::create(ConstantExpr::create(1, Expr::Int8),
                                       arguments.at(1).error);

    // x * (1 - ex)
    ref<Expr> extendedLeft = lError;
    if (lError->getWidth() != arguments.at(0).value->getWidth()) {
      extendedLeft =
          ZExtExpr::create(lError, arguments.at(0).value->getWidth());
    }
    ref<Expr> extendedRight = rError;
    if (rError->getWidth() != arguments.at(1).value->getWidth()) {
      extendedRight =
          ZExtExpr::create(rError, arguments.at(1).value->getWidth());
    }
    ref<Expr> leftMul = MulExpr::create(arguments.at(0).value, extendedLeft);
    ref<Expr> rightMul = MulExpr::create(arguments.at(1).value, extendedRight);

    ref<Expr> conditionWithError;

    if (llvm::ICmpInst *ii = llvm::dyn_cast<llvm::ICmpInst>(ci)) {
      switch (ii->getPredicate()) {
      case llvm::ICmpInst::ICMP_EQ: {
        conditionWithError = EqExpr::create(leftMul, rightMul);
        break;
      }

      case llvm::ICmpInst::ICMP_NE: {
        conditionWithError = NeExpr::create(leftMul, rightMul);
        break;
      }

      case llvm::ICmpInst::ICMP_UGT: {
        conditionWithError = UgtExpr::create(leftMul, rightMul);
        break;
      }

      case llvm::ICmpInst::ICMP_UGE: {
        conditionWithError = UgeExpr::create(leftMul, rightMul);
        break;
      }

      case llvm::ICmpInst::ICMP_ULT: {
        conditionWithError = UltExpr::create(leftMul, rightMul);
        break;
      }

      case llvm::ICmpInst::ICMP_ULE: {
        conditionWithError = UleExpr::create(leftMul, rightMul);
        break;
      }

      case llvm::ICmpInst::ICMP_SGT: {

        int leftWidth = leftMul->getWidth();
        int rightWidth = rightMul->getWidth();

        if (leftWidth > rightWidth) {
          rightMul = ZExtExpr::create(rightMul, leftWidth);
        } else if (leftWidth < rightWidth) {
          leftMul = ZExtExpr::create(leftMul, rightWidth);
        }
        conditionWithError = SgtExpr::create(leftMul, rightMul);
        break;
      }

      case llvm::ICmpInst::ICMP_SGE: {
        int leftWidth = leftMul->getWidth();
        int rightWidth = rightMul->getWidth();

        if (leftWidth > rightWidth) {
          rightMul = ZExtExpr::create(rightMul, leftWidth);
        } else if (leftWidth < rightWidth) {
          leftMul = ZExtExpr::create(leftMul, rightWidth);
        }
        conditionWithError = SgeExpr::create(leftMul, rightMul);
        break;
      }

      case llvm::ICmpInst::ICMP_SLT: {
        conditionWithError = SltExpr::create(leftMul, rightMul);
        break;
      }

      case llvm::ICmpInst::ICMP_SLE: {
        conditionWithError = SleExpr::create(leftMul, rightMul);
        break;
      }

      default:
        conditionWithError = ConstantExpr::create(1, Expr::Bool);
        break;
      }

    } else if (llvm::FCmpInst *fi = llvm::dyn_cast<llvm::FCmpInst>(ci)) {
      switch (fi->getPredicate()) {
      case llvm::FCmpInst::FCMP_ORD: {
        conditionWithError = ConstantExpr::create(1, Expr::Bool);
        break;
      }
      case llvm::FCmpInst::FCMP_UNO: {
        conditionWithError = ConstantExpr::create(0, Expr::Bool);
        break;
      }
      case llvm::FCmpInst::FCMP_UEQ:
      case llvm::FCmpInst::FCMP_OEQ: {
        conditionWithError = EqExpr::create(leftMul, rightMul);
        break;
      }
      case llvm::FCmpInst::FCMP_UGT:
      case llvm::FCmpInst::FCMP_OGT: {
        conditionWithError = SgtExpr::create(leftMul, rightMul);
        break;
      }
      case llvm::FCmpInst::FCMP_UGE:
      case llvm::FCmpInst::FCMP_OGE: {
        conditionWithError = SgeExpr::create(leftMul, rightMul);
        break;
      }
      case llvm::FCmpInst::FCMP_ULT:
      case llvm::FCmpInst::FCMP_OLT: {
        conditionWithError = SltExpr::create(leftMul, rightMul);
        break;
      }
      case llvm::FCmpInst::FCMP_ULE:
      case llvm::FCmpInst::FCMP_OLE: {
        conditionWithError = SleExpr::create(leftMul, rightMul);
        break;
      }
      case llvm::FCmpInst::FCMP_UNE:
      case llvm::FCmpInst::FCMP_ONE: {
        conditionWithError = NeExpr::create(leftMul, rightMul);
        break;
      }
      case llvm::FCmpInst::FCMP_FALSE: {
        conditionWithError = ConstantExpr::create(0, Expr::Bool);
        break;
      }
      case llvm::FCmpInst::FCMP_TRUE: {
        conditionWithError = ConstantExpr::create(1, Expr::Bool);
        break;
      }
      default:
        assert(!"Invalid FCMP predicate!");
      }
    }

    return std::pair<ref<Expr>, ref<Expr> >(ConstantExpr::create(0, Expr::Int8),
                                            conditionWithError);
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

    ref<Expr> addExpr;
    if (error0->getWidth() != error1->getWidth())
      addExpr =
          AddExpr::create(ZExtExpr::create(error0, error1->getWidth()), error1);
    else
      addExpr = AddExpr::create(error0, error1);

    if (addExpr->getWidth() > 1)
      return std::pair<ref<Expr>, ref<Expr> >(
          ExtractExpr::create(addExpr, 0, Expr::Int8), nullExpr);
    else
      return std::pair<ref<Expr>, ref<Expr> >(
          ConstantExpr::create(0, Expr::Int8), nullExpr);
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
    ref<Expr> error = arguments.at(0).error;
    if (error.isNull()) {
      error = ConstantExpr::create(0, Expr::Int8);
    }
    return std::pair<ref<Expr>, ref<Expr> >(error, nullExpr);
  }
  default: { assert(!"unhandled instruction"); }
  }
  return std::pair<ref<Expr>, ref<Expr> >(ConstantExpr::create(0, Expr::Int8),
                                          nullExpr);
}

void ErrorState::registerInputError(ref<Expr> error) {
  if (UniformInputError && inputErrorList.empty()) {
    inputErrorList.push_back(error);
    return;
  }
  std::vector<ref<Expr> >::iterator it =
      std::find(inputErrorList.begin(), inputErrorList.end(), error);
  if (it == inputErrorList.end())
    inputErrorList.push_back(error);
}

void ErrorState::executeStoreSimple(ref<Expr> base, ref<Expr> address,
                                    ref<Expr> value, ref<Expr> error,
                                    ref<Expr> valueWithError,
                                    llvm::Instruction *inst) {
  if (error.isNull())
    return;

  if (ConstantExpr *cp = llvm::dyn_cast<ConstantExpr>(address)) {
	// We only store the error of concrete addresses
    uint64_t intAddress = cp->getZExtValue();
    storedError[intAddress] =
        std::pair<ref<Expr>, ref<Expr> >(error, valueWithError);

    unsigned line = 0;
    llvm::StringRef file = "";
    llvm::StringRef dir = "";
    if (ConstantExpr *cpBase = llvm::dyn_cast<ConstantExpr>(base)) {
      uint64_t intBaseAddress = cpBase->getZExtValue();
      if (inst) {
        std::string str = "";
        llvm::raw_string_ostream stream(str);
        inst->print(stream);
        stream.str().erase(
            std::remove(stream.str().begin(), stream.str().end(), ','),
            stream.str().end());
        stream.str().erase(
            std::remove(stream.str().begin(), stream.str().end(), '%'),
            stream.str().end());
        std::vector<std::string> tokens;
        std::stringstream ss(stream.str());
        while (ss >> stream.str())
          tokens.push_back(stream.str());
        if (llvm::MDNode *n = inst->getMetadata("dbg")) {
          llvm::DILocation loc(n);
          line = loc.getLineNumber();
          file = loc.getFilename();
          dir = loc.getDirectory();
        } else {
          line = 0;
          file = "unknown";
          dir = "unknown";
        }

        std::string funcName = "";
        if (llvm::BasicBlock *bb = inst->getParent()) {
          if (llvm::Function *func = bb->getParent()) {
            funcName = func->getName();
          }
        }

        // update/save error expression
        if (tokens.size() > 5) {
          std::string name;
          if (tokens.size() > 7) {
            name = tokens[4];
          } else {
            name = tokens[2];
          }

          if (name == "null")
            return;

          std::ostringstream keyStream;
          keyStream << intBaseAddress << " " << funcName << " " << name;
          std::string key = keyStream.str();

          if (ApproximatePointers) {
            // In case of a pointer address, check if whatever it is pointing to
            // has error associated with it
            // This is needed to get the error of function call arguments
            if (ConstantExpr *cpError = llvm::dyn_cast<ConstantExpr>(error)) {
              if (cpError->getZExtValue() == 0) {
                base = value;
                if (hasStoredError(base))
                  error = retrieveStoredError(base).first;
                else if (hasDeclaredInputError(base))
                  error = retrieveDeclaredInputError(base);
              }
            }
          }

          if (funcName == "memcpy") {
            std::pair<unsigned, std::string> memcpyInfo =
                retrieveMemcpyStoreInfo();
            line = memcpyInfo.first;
            funcName = memcpyInfo.second;
          }

          stream << " Line " << line << " of " << dir.str() << "/"
                 << file.str();
          stream << " (" << funcName << ")";
          stream << ", " << name << ", " << intBaseAddress;

          std::map<std::string,
                   std::pair<std::string, ref<Expr> > >::const_iterator it =
              errorExpressions.find(key);
          if (it != errorExpressions.end()) {
            errorExpressions[key] =
                std::pair<std::string, ref<Expr> >(stream.str(), error);
          } else {
            errorExpressions.insert(
                std::pair<std::string, std::pair<std::string, ref<Expr> > >(
                    key,
                    std::pair<std::string, ref<Expr> >(stream.str(), error)));
          }
        }
      }
    }
  }
}

void ErrorState::declareInputError(ref<Expr> address, ref<Expr> error) {
  if (error.isNull())
    return;

  if (UniformInputError && !declaredInputError.empty())
    return;

  // At store instruction, we store new error by a multiply of the stored error
  // with the loop trip count.
  if (ConstantExpr *cp = llvm::dyn_cast<ConstantExpr>(address)) {
    uint64_t intAddress = cp->getZExtValue();
    declaredInputError[intAddress] = error;
    return;
  }
  assert(!"non-constant address");
}

std::pair<ref<Expr>, ref<Expr> >
ErrorState::retrieveStoredError(ref<Expr> address) const {
  ref<Expr> error = ConstantExpr::create(0, Expr::Int8);
  ref<Expr> valueWithError;

  if (ConstantExpr *cp = llvm::dyn_cast<ConstantExpr>(address)) {
    std::map<uintptr_t, std::pair<ref<Expr>, ref<Expr> > >::const_iterator it =
        storedError.find(cp->getZExtValue());
    if (it != storedError.end()) {
      error = it->second.first;
      valueWithError = it->second.second;
    }
  }

  // It is possible that the address is non-constant in that case assume the
  // error to be zero assert(!"non-constant address");
  return std::pair<ref<Expr>, ref<Expr> >(error, valueWithError);
}

ref<Expr> ErrorState::retrieveDeclaredInputError(ref<Expr> address) const {
  if (UniformInputError && !declaredInputError.empty()) {
    return declaredInputError.begin()->second;
  }
  if (ConstantExpr *cp = llvm::dyn_cast<ConstantExpr>(address)) {
    std::map<uintptr_t, ref<Expr> >::const_iterator it =
        declaredInputError.find(cp->getZExtValue());
    if (it != declaredInputError.end()) {
      return it->second;
    }
  }

  ref<Expr> nullError;
  return nullError;
}

bool ErrorState::hasStoredError(ref<Expr> address) const {
  if (ConstantExpr *cp = llvm::dyn_cast<ConstantExpr>(address)) {
    std::map<uintptr_t, std::pair<ref<Expr>, ref<Expr> > >::const_iterator it =
        storedError.find(cp->getZExtValue());
    if (it != storedError.end()) {
      return true;
    } else
      return false;
  } else
    return false;
}

bool ErrorState::hasDeclaredInputError(ref<Expr> address) const {
  if (ConstantExpr *cp = llvm::dyn_cast<ConstantExpr>(address)) {
    std::map<uintptr_t, ref<Expr> >::const_iterator it =
        declaredInputError.find(cp->getZExtValue());
    if (it != declaredInputError.end()) {
      return true;
    } else
      return false;
  } else
    return false;
}

std::pair<ref<Expr>, ref<Expr> >
ErrorState::executeLoad(llvm::Instruction *inst, ref<Expr> base,
                        ref<Expr> address, ref<Expr> offset) {
  ref<Expr> nullExpr;
  ref<Expr> error = ConstantExpr::create(0, Expr::Int8);

  if (hasStoredError(address)) {
    return retrieveStoredError(address);
  }

  ref<Expr> baseError = retrieveDeclaredInputError(base);

  if (baseError.isNull()) {
    if (hasStoredError(base))
      baseError = retrieveStoredError(base).first;
  }

  if (baseError.isNull()) {
    executeStoreSimple(base, address, nullExpr, error, nullExpr, 0);
    return std::pair<ref<Expr>, ref<Expr> >(error, nullExpr);
  }

  // The following also performs nullity check on the result of the cast. If
  // the type does not match, re is NULL
  if (ReadExpr *re = llvm::dyn_cast<ReadExpr>(baseError)) {
      std::string errorName = re->updates.root->name;

      const std::string array_prefix8 = ARRAY_PREFIX8;
      const std::string array_prefix16 = ARRAY_PREFIX16;
      const std::string array_prefix32 = ARRAY_PREFIX32;
      const std::string array_prefix64 = ARRAY_PREFIX64;

      if (!errorName.compare(0, array_prefix8.size(), array_prefix8)) {
        errorName.erase(0, 8);
        if (!UniformInputError) {
          if (ConstantExpr *ce = llvm::dyn_cast<ConstantExpr>(offset)) {
            std::ostringstream so;
            uint64_t array_index = ce->getZExtValue();
            so << array_index;
            errorName += "__index__" + so.str();
            offset = Expr::createPointer(0);
          }
        } else {
          offset = Expr::createPointer(0);
        }
        const Array *newErrorArray =
            errorArrayCache->CreateArray(errorName, Expr::Int8);
        UpdateList ul(newErrorArray, 0);
        error = ReadExpr::create(ul, offset);
      } else if (!errorName.compare(0, array_prefix16.size(), array_prefix16)) {
        errorName.erase(0, 9);
        if (!UniformInputError) {
          if (ConstantExpr *ce = llvm::dyn_cast<ConstantExpr>(offset)) {
            std::ostringstream so;
            uint64_t array_index = ce->getZExtValue();
            so << array_index / 2;
            errorName += "__index__" + so.str();
            offset = Expr::createPointer(0);
          }
        } else {
          offset = Expr::createPointer(0);
        }
        const Array *newErrorArray =
            errorArrayCache->CreateArray(errorName, Expr::Int8);
        UpdateList ul(newErrorArray, 0);
        error = ReadExpr::create(ul, offset);
      } else if (!errorName.compare(0, array_prefix32.size(), array_prefix32)) {
        errorName.erase(0, 9);
        if (!UniformInputError) {
          if (ConstantExpr *ce = llvm::dyn_cast<ConstantExpr>(offset)) {
            std::ostringstream so;
            uint64_t array_index = ce->getZExtValue();
            so << array_index / 4;
            errorName += "__index__" + so.str();
            offset = Expr::createPointer(0);
          }
        } else {
          offset = Expr::createPointer(0);
        }
        const Array *newErrorArray =
            errorArrayCache->CreateArray(errorName, Expr::Int8);
        UpdateList ul(newErrorArray, 0);
        error = ReadExpr::create(ul, offset);
      } else if (!errorName.compare(0, array_prefix64.size(), array_prefix64)) {
        errorName.erase(0, 9);
        if (!UniformInputError) {
          if (ConstantExpr *ce = llvm::dyn_cast<ConstantExpr>(offset)) {
            std::ostringstream so;
            uint64_t array_index = ce->getZExtValue();
            so << array_index / 8;
            errorName += "__index__" + so.str();
            offset = Expr::createPointer(0);
          }
        } else {
          offset = Expr::createPointer(0);
        }
        const Array *newErrorArray =
            errorArrayCache->CreateArray(errorName, Expr::Int8);
        UpdateList ul(newErrorArray, 0);
        error = ReadExpr::create(ul, offset);
      } else {
        error = baseError;
      }
  }
  registerInputError(error);

  if (ConstantExpr *cp = llvm::dyn_cast<ConstantExpr>(address)) {
    uint64_t intAddress = cp->getZExtValue();
    if (inst) {
      if (llvm::MDNode *n = inst->getMetadata("dbg")) {
        std::string str = "";
        llvm::raw_string_ostream stream(str);
        inst->print(stream);
        stream.str().erase(
            std::remove(stream.str().begin(), stream.str().end(), ','),
            stream.str().end());
        stream.str().erase(
            std::remove(stream.str().begin(), stream.str().end(), '%'),
            stream.str().end());
        std::vector<std::string> tokens;
        std::stringstream ss(stream.str());
        while (ss >> stream.str())
          tokens.push_back(stream.str());
        llvm::DILocation loc(n);
        unsigned line = loc.getLineNumber();
        llvm::StringRef file = loc.getFilename();
        llvm::StringRef dir = loc.getDirectory();
        stream << " Line " << line << " of " << dir.str() << "/" << file.str();

        std::string funcName = "";
        if (llvm::BasicBlock *bb = inst->getParent()) {
          if (llvm::Function *func = bb->getParent()) {
            funcName = func->getName();
            stream << " (" << funcName << ")";
          }
        }

        std::ostringstream keyStream;
        keyStream << intAddress << " " << funcName << " " << tokens[4];
        std::string key = keyStream.str();

        // update/save error expression
        stream << ", " << tokens[4] << ", " << intAddress;
        std::map<std::string,
                 std::pair<std::string, ref<Expr> > >::const_iterator it =
            errorExpressions.find(key);
        if (it != errorExpressions.end()) {
          errorExpressions[key] =
              std::pair<std::string, ref<Expr> >(stream.str(), error);
        }
      }
    }
  }
  return std::pair<ref<Expr>, ref<Expr> >(error, nullExpr);
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
  for (std::map<uintptr_t, std::pair<ref<Expr>, ref<Expr> > >::const_iterator
           it = storedError.begin(),
           ie = storedError.end();
       it != ie; ++it) {
    os << it->first << ": ";
    it->second.first->print(os);
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

ref<Expr> ErrorState::getScalingConstraint() {
  const Array *array = errorArrayCache->CreateArray("scaling", Expr::Int8);
  ref<Expr> scalingVal = ReadExpr::create(
      UpdateList(array, 0), ConstantExpr::create(0, array->getDomain()));
  return NeExpr::create(scalingVal, ConstantExpr::create(0, Expr::Int8));
}

std::map<std::string, std::pair<std::string, ref<Expr> > > &
ErrorState::getStateErrorExpressions() {
  return errorExpressions;
}

std::map<std::string, std::vector<Cell> > &ErrorState::getMathExpressions() {
  return mathCallArgs;
}

ref<Expr> ErrorState::createNewMathErrorVar(ref<Expr> mathVar,
                                            std::string mathVarName) {
  const std::string errorVarName = mathVarName + "_err";
  const Array *array = errorArrayCache->CreateArray(errorVarName, Expr::Int8);
  ref<Expr> mathErrorVar = ReadExpr::create(
      UpdateList(array, 0), ConstantExpr::create(0, array->getDomain()));
  // ref<Expr> mathErrorVar = ZExtExpr::create(mathErrorVarTemp, Expr::Int32);
  return mathErrorVar;
}

void ErrorState::storeMathCallArgs(std::string varName,
                                   std::vector<Cell> &arguments) {
  // save the function call args
  mathCallArgs[varName] = arguments;
}

std::string ErrorState::createNewMathVarName(std::string mathFunctionName) {
  mathVarCount++;
  std::ostringstream str;
  str << mathVarCount;
  return mathFunctionName + "_" + str.str();
}

void ErrorState::saveMemcpyStoreInfo(llvm::Instruction *inst,
                                     unsigned lineNumber,
                                     std::string functionName) {
  memcpyStoreInfo.clear();
  memcpyStoreInfo.push_back(
      std::pair<unsigned, std::string>(lineNumber, functionName));
}

std::pair<unsigned, std::string> ErrorState::retrieveMemcpyStoreInfo() {
  if (!memcpyStoreInfo.empty())
    return memcpyStoreInfo.back();
  else
    return std::pair<unsigned, std::string>(0, "not found");
}
