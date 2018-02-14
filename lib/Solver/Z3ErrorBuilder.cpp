//===-- Z3ErrorBuilder.cpp -------------------------------------*- C++ -*-====//
//
// The KLEE Symbolic Virtual Machine with Numerical Error Analysis Extension
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#include "klee/Config/config.h"
#ifdef ENABLE_Z3
#include "Z3ErrorBuilder.h"

#include "klee/Expr.h"
#include "klee/Solver.h"
#include "klee/util/Bits.h"
#include "klee/util/PrettyExpressionBuilder.h"
#include "ConstantDivision.h"

#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/CommandLine.h"

using namespace klee;

namespace {
llvm::cl::opt<bool> UseConstructHashZ3Error(
    "use-construct-hash-z3-error",
    llvm::cl::desc("Use hash-consing during Z3 query construction for "
                   "reasoning about error expression."),
    llvm::cl::init(true));
}

void custom_z3_error_error_handler(Z3_context ctx, Z3_error_code ec) {
  ::Z3_string errorMsg =
#ifdef HAVE_Z3_GET_ERROR_MSG_NEEDS_CONTEXT
      // Z3 > 4.4.1
      Z3_get_error_msg(ctx, ec);
#else
      // Z3 4.4.1
      Z3_get_error_msg(ec);
#endif
  // FIXME: This is kind of a hack. The value comes from the enum
  // Z3_CANCELED_MSG but this isn't currently exposed by Z3's C API
  if (strcmp(errorMsg, "canceled") == 0) {
    // Solver timeout is not a fatal error
    return;
  }
  llvm::errs() << "Error: Incorrect use of Z3. [" << ec << "] " << errorMsg
               << "\n";
  abort();
}

Z3ErrorArrayExprHash::~Z3ErrorArrayExprHash() {}

void Z3ErrorArrayExprHash::clear() {
  _update_node_hash.clear();
  _array_hash.clear();
}

Z3ErrorBuilder::Z3ErrorBuilder(bool _viaIntegerSolving,
                               bool autoClearConstructCache)
    : viaIntegerSolving(_viaIntegerSolving),
      autoClearConstructCache(autoClearConstructCache) {
  // FIXME: Should probably let the client pass in a Z3_config instead
  Z3_config cfg = Z3_mk_config();
  // It is very important that we ask Z3 to let us manage memory so that
  // we are able to cache expressions and sorts.
  ctx = Z3_mk_context_rc(cfg);
  // Make sure we handle any errors reported by Z3.
  Z3_set_error_handler(ctx, custom_z3_error_error_handler);
  // When emitting Z3 expressions make them SMT-LIBv2 compliant
  Z3_set_ast_print_mode(ctx, Z3_PRINT_SMTLIB2_COMPLIANT);
  Z3_del_config(cfg);
}

Z3ErrorBuilder::~Z3ErrorBuilder() {
  // Clear caches so exprs/sorts gets freed before the destroying context
  // they aren associated with.
  clearConstructCache();
  _arr_hash.clear();
  Z3_del_context(ctx);
}

Z3SortHandle Z3ErrorBuilder::getRealSort() {
  // FIXME: cache these
  return Z3SortHandle(Z3_mk_real_sort(ctx), ctx);
}

Z3SortHandle Z3ErrorBuilder::getIntSort() {
  // FIXME: cache these
  return Z3SortHandle(Z3_mk_int_sort(ctx), ctx);
}

Z3SortHandle Z3ErrorBuilder::getArraySort(Z3SortHandle domainSort,
                                          Z3SortHandle rangeSort) {
  // FIXME: cache these
  return Z3SortHandle(Z3_mk_array_sort(ctx, domainSort, rangeSort), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::buildArray(const char *name) {
  Z3SortHandle domainSort = getIntSort();
  Z3SortHandle rangeSort;
  if (viaIntegerSolving) {
    rangeSort = getIntSort();
  } else {
    rangeSort = getRealSort();
  }
  Z3SortHandle t = getArraySort(domainSort, rangeSort);
  Z3_symbol s = Z3_mk_string_symbol(ctx, const_cast<char *>(name));
  return Z3ErrorASTHandle(Z3_mk_const(ctx, s, t), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::buildReal(const char *name) {
  Z3_symbol s = Z3_mk_string_symbol(ctx, const_cast<char *>(name));
  return Z3ErrorASTHandle(Z3_mk_const(ctx, s, getRealSort()), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::buildInteger(const char *name) {
  Z3_symbol s = Z3_mk_string_symbol(ctx, const_cast<char *>(name));
  return Z3ErrorASTHandle(Z3_mk_const(ctx, s, getIntSort()), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::getTrue() {
  return Z3ErrorASTHandle(Z3_mk_true(ctx), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::getFalse() {
  return Z3ErrorASTHandle(Z3_mk_false(ctx), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::one() { return intConst(1); }

Z3ErrorASTHandle Z3ErrorBuilder::zero() { return intConst(0); }

Z3ErrorASTHandle Z3ErrorBuilder::minusOne() { return intConst(-1); }

Z3ErrorASTHandle Z3ErrorBuilder::realConst(uint64_t value) {
  return Z3ErrorASTHandle(Z3_mk_real(ctx, value, 1), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::intConst(uint64_t value) {
  Z3SortHandle t = getIntSort();
  return Z3ErrorASTHandle(Z3_mk_int(ctx, value, t), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::zExtConst(uint64_t value) {
  return intConst(value);
}

Z3ErrorASTHandle Z3ErrorBuilder::sExtConst(uint64_t value) {
  return intConst(value);
}

Z3ErrorASTHandle Z3ErrorBuilder::boolExtract(Z3ErrorASTHandle expr) {
  return expr;
}

Z3ErrorASTHandle Z3ErrorBuilder::extract(Z3ErrorASTHandle expr, unsigned top,
                                         unsigned bottom) {
  return Z3ErrorASTHandle(Z3_mk_extract(ctx, top, bottom, expr), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::eqExpr(Z3ErrorASTHandle a,
                                        Z3ErrorASTHandle b) {
  return Z3ErrorASTHandle(Z3_mk_eq(ctx, a, b), ctx);
}

// logical right shift
Z3ErrorASTHandle Z3ErrorBuilder::rightShift(Z3ErrorASTHandle expr,
                                            unsigned shift) {
  return Z3ErrorASTHandle(Z3_mk_div(ctx, expr, intConst(2 ^ shift)), ctx);
}

// logical left shift
Z3ErrorASTHandle Z3ErrorBuilder::leftShift(Z3ErrorASTHandle expr,
                                           unsigned shift) {
  const Z3_ast args[2] = { expr, intConst(2 ^ shift) };
  return Z3ErrorASTHandle(Z3_mk_mul(ctx, 2, args), ctx);
}

// left shift by a variable amount on an expression of the specified width
Z3ErrorASTHandle Z3ErrorBuilder::varLeftShift(Z3ErrorASTHandle expr,
                                              Z3ErrorASTHandle shift) {
  const Z3_ast args[2] = { expr, Z3_mk_power(ctx, intConst(2), shift) };
  return Z3ErrorASTHandle(Z3_mk_mul(ctx, 2, args), ctx);
}

// logical right shift by a variable amount on an expression of the specified
// width
Z3ErrorASTHandle Z3ErrorBuilder::varRightShift(Z3ErrorASTHandle expr,
                                               Z3ErrorASTHandle shift) {
  return Z3ErrorASTHandle(
      Z3_mk_div(ctx, expr, Z3_mk_power(ctx, intConst(2), shift)), ctx);
}

// arithmetic right shift by a variable amount on an expression of the specified
// width
Z3ErrorASTHandle Z3ErrorBuilder::varArithRightShift(Z3ErrorASTHandle expr,
                                                    Z3ErrorASTHandle shift) {
  return varRightShift(expr, shift);
}

Z3ErrorASTHandle Z3ErrorBuilder::notExpr(Z3ErrorASTHandle expr) {
  return Z3ErrorASTHandle(Z3_mk_not(ctx, expr), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::andExpr(Z3ErrorASTHandle lhs,
                                         Z3ErrorASTHandle rhs) {
  ::Z3_ast args[2] = { lhs, rhs };
  return Z3ErrorASTHandle(Z3_mk_and(ctx, 2, args), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::orExpr(Z3ErrorASTHandle lhs,
                                        Z3ErrorASTHandle rhs) {
  ::Z3_ast args[2] = { lhs, rhs };
  return Z3ErrorASTHandle(Z3_mk_or(ctx, 2, args), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::writeExpr(Z3ErrorASTHandle array,
                                           Z3ErrorASTHandle index,
                                           Z3ErrorASTHandle value) {
  return Z3ErrorASTHandle(Z3_mk_store(ctx, array, index, value), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::readExpr(Z3ErrorASTHandle array,
                                          Z3ErrorASTHandle index) {
  return Z3ErrorASTHandle(Z3_mk_select(ctx, array, index), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::iteExpr(Z3ErrorASTHandle condition,
                                         Z3ErrorASTHandle whenTrue,
                                         Z3ErrorASTHandle whenFalse) {
  return Z3ErrorASTHandle(Z3_mk_ite(ctx, condition, whenTrue, whenFalse), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::ltExpr(Z3ErrorASTHandle lhs,
                                        Z3ErrorASTHandle rhs) {
  return Z3ErrorASTHandle(Z3_mk_lt(ctx, lhs, rhs), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::leExpr(Z3ErrorASTHandle lhs,
                                        Z3ErrorASTHandle rhs) {
  return Z3ErrorASTHandle(Z3_mk_le(ctx, lhs, rhs), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::sLtExpr(Z3ErrorASTHandle lhs,
                                         Z3ErrorASTHandle rhs) {
  return Z3ErrorASTHandle(Z3_mk_lt(ctx, lhs, rhs), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::sLeExpr(Z3ErrorASTHandle lhs,
                                         Z3ErrorASTHandle rhs) {
  return Z3ErrorASTHandle(Z3_mk_le(ctx, lhs, rhs), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::getInitialArray(const Array *root) {

  assert(root);
  Z3ErrorASTHandle array_expr;
  bool hashed = _arr_hash.lookupArrayExpr(root, array_expr);

  if (!hashed) {
    // Unique arrays by name, so we make sure the name is unique by
    // using the size of the array hash as a counter.
    std::string unique_id = llvm::itostr(_arr_hash._array_hash.size());
    unsigned const uid_length = unique_id.length();
    unsigned const space = (root->name.length() > 32 - uid_length)
                               ? (32 - uid_length)
                               : root->name.length();
    std::string unique_name = root->name.substr(0, space) + unique_id;

    array_expr = buildArray(unique_name.c_str());

    if (root->isConstantArray()) {
      // FIXME: Flush the concrete values into Z3. Ideally we would do this
      // using assertions, which might be faster, but we need to fix the caching
      // to work correctly in that case.
      for (unsigned i = 0, e = root->size; i != e; ++i) {
        Z3ErrorASTHandle prev = array_expr;
        array_expr = writeExpr(
            prev, constructInternal(ConstantExpr::alloc(i, root->getDomain())),
            constructInternal(root->constantValues[i]));
      }
    }

    _arr_hash.hashArrayExpr(root, array_expr);
  }

  return (array_expr);
}

Z3ErrorASTHandle Z3ErrorBuilder::getInitialRead(const Array *root,
                                                unsigned index) {
  return readExpr(getInitialArray(root), intConst(index));
}

Z3ErrorASTHandle Z3ErrorBuilder::getArrayForUpdate(const Array *root,
                                                   const UpdateNode *un) {
  if (!un) {
    return (getInitialArray(root));
  } else {
    // FIXME: This really needs to be non-recursive.
    Z3ErrorASTHandle un_expr;
    bool hashed = _arr_hash.lookupUpdateNodeExpr(un, un_expr);

    if (!hashed) {
      un_expr =
          writeExpr(getArrayForUpdate(root, un->next),
                    constructInternal(un->index), constructInternal(un->value));

      _arr_hash.hashUpdateNodeExpr(un, un_expr);
    }

    return (un_expr);
  }
}

/** if *width_out!=1 then result is a bitvector,
    otherwise it is a bool */
Z3ErrorASTHandle Z3ErrorBuilder::constructInternal(ref<Expr> e) {
  // TODO: We could potentially use Z3_simplify() here
  // to store simpler expressions.
  if (!UseConstructHashZ3Error || isa<ConstantExpr>(e)) {
    return constructActual(e);
  } else {
    ExprHashMap<Z3ErrorASTHandle>::iterator it = constructed.find(e);
    if (it != constructed.end()) {
      return it->second;
    } else {
      Z3ErrorASTHandle res = constructActual(e);
      constructed.insert(std::make_pair(e, res));
      return res;
    }
  }
}

/** if *width_out!=1 then result is a bitvector,
    otherwise it is a bool */
Z3ErrorASTHandle Z3ErrorBuilder::constructActual(ref<Expr> e) {
  switch (e->getKind()) {
  case Expr::Constant: {
    ConstantExpr *CE = cast<ConstantExpr>(e);

    if (e->getWidth() == Expr::Bool) {
      if (e->isFalse())
        return Z3ErrorASTHandle(Z3_mk_false(ctx), ctx);
      return Z3ErrorASTHandle(Z3_mk_true(ctx), ctx);
    }
    ref<ConstantExpr> Tmp = CE;
    return intConst(Tmp->Extract(0, 64)->getZExtValue());
  }

  // Special
  case Expr::NotOptimized: {
    NotOptimizedExpr *noe = cast<NotOptimizedExpr>(e);
    return constructInternal(noe->src);
  }

  case Expr::Read: {
    ReadExpr *re = cast<ReadExpr>(e);
    assert(re && re->updates.root);

    std::string name(re->updates.root->name);

    if (ConstantExpr *ce = llvm::dyn_cast<ConstantExpr>(re->index)) {
      uint64_t index = ce->getZExtValue();
      const std::string array_prefix8 = ARRAY_PREFIX8;
      const std::string array_prefix16 = ARRAY_PREFIX16;
      const std::string array_prefix32 = ARRAY_PREFIX32;
      const std::string array_prefix64 = ARRAY_PREFIX64;

      if (!name.compare(0, array_prefix8.size(), array_prefix8)) {
        std::ostringstream so;
        so << index;
        name.erase(0, 8);
        name += "__index__" + so.str();
      } else if (!name.compare(0, array_prefix16.size(), array_prefix16)) {
        std::ostringstream so;
        so << index / 2;
        name.erase(0, 9);
        name += "__index__" + so.str();
      } else if (!name.compare(0, array_prefix32.size(), array_prefix32)) {
        std::ostringstream so;
        so << index / 4;
        name.erase(0, 9);
        name += "__index__" + so.str();
      } else if (!name.compare(0, array_prefix64.size(), array_prefix64)) {
        std::ostringstream so;
        so << index / 8;
        name.erase(0, 9);
        name += "__index__" + so.str();
      }
      if (viaIntegerSolving) {
        return buildInteger(name.c_str());
      }
      return buildReal(name.c_str());
    }
    return readExpr(getArrayForUpdate(re->updates.root, re->updates.head),
                    constructInternal(re->index));
  }

  case Expr::Select: {
    SelectExpr *se = cast<SelectExpr>(e);
    Z3ErrorASTHandle cond = constructInternal(se->cond);
    Z3ErrorASTHandle tExpr = constructInternal(se->trueExpr);
    Z3ErrorASTHandle fExpr = constructInternal(se->falseExpr);
    return iteExpr(cond, tExpr, fExpr);
  }

  case Expr::Concat: {
    ConcatExpr *ce = cast<ConcatExpr>(e);
    unsigned numKids = ce->getNumKids();

    // Note here that concat may have more children, but we ignore them
    Z3ErrorASTHandle res = constructInternal(ce->getKid(numKids - 1));
    return res;
  }

  case Expr::Extract: {
    ExtractExpr *ee = cast<ExtractExpr>(e);
    return constructInternal(ee->expr);
  }

  // Casting

  case Expr::ZExt: {
    CastExpr *ce = cast<CastExpr>(e);
    return constructInternal(ce->src);
  }

  case Expr::SExt: {
    CastExpr *ce = cast<CastExpr>(e);
    return constructInternal(ce->src);
  }

  // Arithmetic
  case Expr::Add: {
    AddExpr *ae = cast<AddExpr>(e);
    Z3ErrorASTHandle left = constructInternal(ae->left);
    Z3ErrorASTHandle right = constructInternal(ae->right);
    const Z3_ast args[2] = { left.as_ast(), right.as_ast() };
    Z3ErrorASTHandle result = Z3ErrorASTHandle(Z3_mk_add(ctx, 2, args), ctx);
    return result;
  }

  case Expr::Sub: {
    SubExpr *se = cast<SubExpr>(e);
    Z3ErrorASTHandle left = constructInternal(se->left);
    Z3ErrorASTHandle right = constructInternal(se->right);
    const Z3_ast args[2] = { left.as_ast(), right.as_ast() };
    Z3ErrorASTHandle result = Z3ErrorASTHandle(Z3_mk_sub(ctx, 2, args), ctx);
    return result;
  }

  case Expr::Mul: {
    MulExpr *me = cast<MulExpr>(e);
    Z3ErrorASTHandle right = constructInternal(me->right);
    Z3ErrorASTHandle left = constructInternal(me->left);
    const Z3_ast args[2] = { left.as_ast(), right.as_ast() };
    Z3ErrorASTHandle result = Z3ErrorASTHandle(Z3_mk_mul(ctx, 2, args), ctx);
    return result;
  }

  case Expr::UDiv: {
    UDivExpr *de = cast<UDivExpr>(e);
    Z3ErrorASTHandle left = constructInternal(de->left);
    Z3ErrorASTHandle right = constructInternal(de->right);
    Z3ErrorASTHandle result =
        Z3ErrorASTHandle(Z3_mk_div(ctx, left, right), ctx);
    return result;
  }

  case Expr::SDiv: {
    SDivExpr *de = cast<SDivExpr>(e);
    Z3ErrorASTHandle left = constructInternal(de->left);
    Z3ErrorASTHandle right = constructInternal(de->right);
    Z3ErrorASTHandle result =
        Z3ErrorASTHandle(Z3_mk_div(ctx, left, right), ctx);
    return result;
  }

  case Expr::URem: {
    URemExpr *de = cast<URemExpr>(e);
    Z3ErrorASTHandle left = construct(de->left);

    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(de->right)) {
      return Z3ErrorASTHandle(
          Z3_mk_rem(ctx, left, intConst(CE->getZExtValue())), ctx);
    }

    Z3ErrorASTHandle right = constructInternal(de->right);
    return Z3ErrorASTHandle(Z3_mk_rem(ctx, left, right), ctx);
  }

  case Expr::SRem: {
    SRemExpr *de = cast<SRemExpr>(e);
    Z3ErrorASTHandle left = constructInternal(de->left);
    Z3ErrorASTHandle right = constructInternal(de->right);
    Z3ErrorASTHandle result =
        Z3ErrorASTHandle(Z3_mk_rem(ctx, left, right), ctx);
    return result;
  }

  // Bitwise
  case Expr::Not: {
    NotExpr *ne = cast<NotExpr>(e);
    Z3ErrorASTHandle expr = constructInternal(ne->expr);
    return notExpr(expr);
  }

  case Expr::And: {
    AndExpr *ae = cast<AndExpr>(e);
    Z3ErrorASTHandle left = constructInternal(ae->left);
    Z3ErrorASTHandle right = constructInternal(ae->right);
    return andExpr(left, right);
  }

  case Expr::Or: {
    OrExpr *oe = cast<OrExpr>(e);
    Z3ErrorASTHandle left = constructInternal(oe->left);
    Z3ErrorASTHandle right = constructInternal(oe->right);
    return orExpr(left, right);
  }

  case Expr::Xor: {
    XorExpr *xe = cast<XorExpr>(e);
    Z3ErrorASTHandle left = constructInternal(xe->left);
    Z3ErrorASTHandle right = constructInternal(xe->right);

    // XXX check for most efficient?
    return iteExpr(left, Z3ErrorASTHandle(notExpr(right)), right);
  }

  case Expr::Shl: {
    ShlExpr *se = cast<ShlExpr>(e);
    Z3ErrorASTHandle left = constructInternal(se->left);

    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(se->right)) {
      return leftShift(left, (unsigned)CE->getLimitedValue());
    } else {
      Z3ErrorASTHandle amount = constructInternal(se->right);
      return varLeftShift(left, amount);
    }
  }

  case Expr::LShr: {
    LShrExpr *lse = cast<LShrExpr>(e);
    Z3ErrorASTHandle left = constructInternal(lse->left);

    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(lse->right)) {
      return rightShift(left, (unsigned)CE->getLimitedValue());
    } else {
      Z3ErrorASTHandle amount = constructInternal(lse->right);
      return varRightShift(left, amount);
    }
  }

  case Expr::AShr: {
    AShrExpr *ase = cast<AShrExpr>(e);
    Z3ErrorASTHandle left = constructInternal(ase->left);

    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(ase->right)) {
      unsigned shift = (unsigned)CE->getLimitedValue();
      return rightShift(left, shift);
    } else {
      Z3ErrorASTHandle amount = constructInternal(ase->right);
      return varArithRightShift(left, amount);
    }
  }

  // Comparison

  case Expr::Eq: {
    EqExpr *ee = cast<EqExpr>(e);
    Z3ErrorASTHandle left = constructInternal(ee->left);
    Z3ErrorASTHandle right = constructInternal(ee->right);
    return Z3ErrorASTHandle(Z3_mk_eq(ctx, left, right), ctx);
  }

  case Expr::Ult: {
    UltExpr *ue = cast<UltExpr>(e);
    Z3ErrorASTHandle left = constructInternal(ue->left);
    Z3ErrorASTHandle right = constructInternal(ue->right);
    return ltExpr(left, right);
  }

  case Expr::Ule: {
    UleExpr *ue = cast<UleExpr>(e);
    Z3ErrorASTHandle left = constructInternal(ue->left);
    Z3ErrorASTHandle right = constructInternal(ue->right);
    return leExpr(left, right);
  }

  case Expr::Slt: {
    SltExpr *se = cast<SltExpr>(e);
    Z3ErrorASTHandle left = constructInternal(se->left);
    Z3ErrorASTHandle right = constructInternal(se->right);
    return sLtExpr(left, right);
  }

  case Expr::Sle: {
    SleExpr *se = cast<SleExpr>(e);
    Z3ErrorASTHandle left = constructInternal(se->left);
    Z3ErrorASTHandle right = constructInternal(se->right);
    return sLeExpr(left, right);
  }

// unused due to canonicalization
#if 0
  case Expr::Ne:
  case Expr::Ugt:
  case Expr::Uge:
  case Expr::Sgt:
  case Expr::Sge:
#endif

  default:
    assert(0 && "unhandled Expr type");
    return getTrue();
  }
}
#endif // ENABLE_Z3
