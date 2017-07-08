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
#include "ConstantDivision.h"

#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/CommandLine.h"

using namespace klee;

namespace {
llvm::cl::opt<bool> UseConstructHashZ3(
    "use-construct-hash-z3",
    llvm::cl::desc("Use hash-consing during Z3 query construction."),
    llvm::cl::init(true));
}

void custom_z3_error_handler(Z3_context ctx, Z3_error_code ec) {
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

Z3ErrorBuilder::Z3ErrorBuilder(bool autoClearConstructCache)
    : autoClearConstructCache(autoClearConstructCache) {
  // FIXME: Should probably let the client pass in a Z3_config instead
  Z3_config cfg = Z3_mk_config();
  // It is very important that we ask Z3 to let us manage memory so that
  // we are able to cache expressions and sorts.
  ctx = Z3_mk_context_rc(cfg);
  // Make sure we handle any errors reported by Z3.
  Z3_set_error_handler(ctx, custom_z3_error_handler);
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
  Z3SortHandle rangeSort = getRealSort();
  Z3SortHandle t = getArraySort(domainSort, rangeSort);
  Z3_symbol s = Z3_mk_string_symbol(ctx, const_cast<char *>(name));
  return Z3ErrorASTHandle(Z3_mk_const(ctx, s, t), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::getTrue() {
  return Z3ErrorASTHandle(Z3_mk_true(ctx), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::getFalse() {
  return Z3ErrorASTHandle(Z3_mk_false(ctx), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::bvOne() { return intConst(1); }

Z3ErrorASTHandle Z3ErrorBuilder::bvZero() { return intConst(0); }

Z3ErrorASTHandle Z3ErrorBuilder::bvMinusOne() { return intConst(-1); }

Z3ErrorASTHandle Z3ErrorBuilder::realConst(uint64_t value) {
  return Z3ErrorASTHandle(Z3_mk_real(ctx, value, 1), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::intConst(uint64_t value) {
  Z3SortHandle t = getIntSort();
  return Z3ErrorASTHandle(Z3_mk_int(ctx, value, t), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::bvZExtConst(uint64_t value) {
  return intConst(value);
}

Z3ErrorASTHandle Z3ErrorBuilder::bvSExtConst(uint64_t value) {
  return intConst(value);
}

Z3ErrorASTHandle Z3ErrorBuilder::bvBoolExtract(Z3ErrorASTHandle expr) {
  return expr;
}

Z3ErrorASTHandle Z3ErrorBuilder::bvExtract(Z3ErrorASTHandle expr, unsigned top,
                                           unsigned bottom) {
  return Z3ErrorASTHandle(Z3_mk_extract(ctx, top, bottom, expr), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::eqExpr(Z3ErrorASTHandle a,
                                        Z3ErrorASTHandle b) {
  return Z3ErrorASTHandle(Z3_mk_eq(ctx, a, b), ctx);
}

// logical right shift
Z3ErrorASTHandle Z3ErrorBuilder::bvRightShift(Z3ErrorASTHandle expr,
                                              unsigned shift) {
  return Z3ErrorASTHandle(Z3_mk_div(ctx, expr, intConst(2 ^ shift)), ctx);
}

// logical left shift
Z3ErrorASTHandle Z3ErrorBuilder::bvLeftShift(Z3ErrorASTHandle expr,
                                             unsigned shift) {
  const Z3_ast args[2] = { expr, intConst(2 ^ shift) };
  return Z3ErrorASTHandle(Z3_mk_mul(ctx, 2, args), ctx);
}

// left shift by a variable amount on an expression of the specified width
Z3ErrorASTHandle Z3ErrorBuilder::bvVarLeftShift(Z3ErrorASTHandle expr,
                                                Z3ErrorASTHandle shift) {
  const Z3_ast args[2] = { expr, Z3_mk_power(ctx, intConst(2), shift) };
  return Z3ErrorASTHandle(Z3_mk_mul(ctx, 2, args), ctx);
}

// logical right shift by a variable amount on an expression of the specified
// width
Z3ErrorASTHandle Z3ErrorBuilder::bvVarRightShift(Z3ErrorASTHandle expr,
                                                 Z3ErrorASTHandle shift) {
  return Z3ErrorASTHandle(
      Z3_mk_div(ctx, expr, Z3_mk_power(ctx, intConst(2), shift)), ctx);
}

// arithmetic right shift by a variable amount on an expression of the specified
// width
Z3ErrorASTHandle Z3ErrorBuilder::bvVarArithRightShift(Z3ErrorASTHandle expr,
                                                      Z3ErrorASTHandle shift) {
  return bvVarRightShift(expr, shift);
}

Z3ErrorASTHandle Z3ErrorBuilder::notExpr(Z3ErrorASTHandle expr) {
  return Z3ErrorASTHandle(Z3_mk_not(ctx, expr), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::bvNotExpr(Z3ErrorASTHandle expr) {
  return Z3ErrorASTHandle(Z3_mk_bvnot(ctx, expr), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::andExpr(Z3ErrorASTHandle lhs,
                                         Z3ErrorASTHandle rhs) {
  ::Z3_ast args[2] = { lhs, rhs };
  return Z3ErrorASTHandle(Z3_mk_and(ctx, 2, args), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::bvAndExpr(Z3ErrorASTHandle lhs,
                                           Z3ErrorASTHandle rhs) {
  return Z3ErrorASTHandle(Z3_mk_bvand(ctx, lhs, rhs), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::orExpr(Z3ErrorASTHandle lhs,
                                        Z3ErrorASTHandle rhs) {
  ::Z3_ast args[2] = { lhs, rhs };
  return Z3ErrorASTHandle(Z3_mk_or(ctx, 2, args), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::bvOrExpr(Z3ErrorASTHandle lhs,
                                          Z3ErrorASTHandle rhs) {
  return Z3ErrorASTHandle(Z3_mk_bvor(ctx, lhs, rhs), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::iffExpr(Z3ErrorASTHandle lhs,
                                         Z3ErrorASTHandle rhs) {
  Z3SortHandle lhsSort = Z3SortHandle(Z3_get_sort(ctx, lhs), ctx);
  Z3SortHandle rhsSort = Z3SortHandle(Z3_get_sort(ctx, rhs), ctx);
  assert(Z3_get_sort_kind(ctx, lhsSort) == Z3_get_sort_kind(ctx, rhsSort) &&
         "lhs and rhs sorts must match");
  assert(Z3_get_sort_kind(ctx, lhsSort) == Z3_BOOL_SORT &&
         "args must have BOOL sort");
  return Z3ErrorASTHandle(Z3_mk_iff(ctx, lhs, rhs), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::bvXorExpr(Z3ErrorASTHandle lhs,
                                           Z3ErrorASTHandle rhs) {
  return Z3ErrorASTHandle(Z3_mk_bvxor(ctx, lhs, rhs), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::bvSignExtend(Z3ErrorASTHandle src,
                                              unsigned width) {
  unsigned src_width =
      Z3_get_bv_sort_size(ctx, Z3SortHandle(Z3_get_sort(ctx, src), ctx));
  assert(src_width <= width && "attempted to extend longer data");

  return Z3ErrorASTHandle(Z3_mk_sign_ext(ctx, width - src_width, src), ctx);
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

unsigned Z3ErrorBuilder::getBVLength(Z3ErrorASTHandle expr) {
  return Z3_get_bv_sort_size(ctx, Z3SortHandle(Z3_get_sort(ctx, expr), ctx));
}

Z3ErrorASTHandle Z3ErrorBuilder::bvLtExpr(Z3ErrorASTHandle lhs,
                                          Z3ErrorASTHandle rhs) {
  return Z3ErrorASTHandle(Z3_mk_bvult(ctx, lhs, rhs), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::bvLeExpr(Z3ErrorASTHandle lhs,
                                          Z3ErrorASTHandle rhs) {
  return Z3ErrorASTHandle(Z3_mk_bvule(ctx, lhs, rhs), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::sbvLtExpr(Z3ErrorASTHandle lhs,
                                           Z3ErrorASTHandle rhs) {
  return Z3ErrorASTHandle(Z3_mk_bvslt(ctx, lhs, rhs), ctx);
}

Z3ErrorASTHandle Z3ErrorBuilder::sbvLeExpr(Z3ErrorASTHandle lhs,
                                           Z3ErrorASTHandle rhs) {
  return Z3ErrorASTHandle(Z3_mk_bvsle(ctx, lhs, rhs), ctx);
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
  if (!UseConstructHashZ3 || isa<ConstantExpr>(e)) {
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
    Z3ErrorASTHandle res = constructInternal(ce->getKid(numKids - 1));
    for (int i = numKids - 2; i >= 0; i--) {
      res = Z3ErrorASTHandle(
          Z3_mk_concat(ctx, constructInternal(ce->getKid(i)), res), ctx);
    }
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
    Z3ErrorASTHandle result =
        Z3ErrorASTHandle(Z3_mk_bvadd(ctx, left, right), ctx);
    return result;
  }

  case Expr::Sub: {
    SubExpr *se = cast<SubExpr>(e);
    Z3ErrorASTHandle left = constructInternal(se->left);
    Z3ErrorASTHandle right = constructInternal(se->right);
    Z3ErrorASTHandle result =
        Z3ErrorASTHandle(Z3_mk_bvsub(ctx, left, right), ctx);
    return result;
  }

  case Expr::Mul: {
    MulExpr *me = cast<MulExpr>(e);
    Z3ErrorASTHandle right = constructInternal(me->right);
    Z3ErrorASTHandle left = constructInternal(me->left);
    Z3ErrorASTHandle result =
        Z3ErrorASTHandle(Z3_mk_bvmul(ctx, left, right), ctx);
    return result;
  }

  case Expr::UDiv: {
    UDivExpr *de = cast<UDivExpr>(e);
    Z3ErrorASTHandle left = constructInternal(de->left);

    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(de->right)) {
      if (CE->getWidth() <= 64) {
        uint64_t divisor = CE->getZExtValue();
        if (bits64::isPowerOfTwo(divisor))
          return bvRightShift(left, bits64::indexOfSingleBit(divisor));
      }
    }

    Z3ErrorASTHandle right = constructInternal(de->right);
    Z3ErrorASTHandle result =
        Z3ErrorASTHandle(Z3_mk_bvudiv(ctx, left, right), ctx);
    return result;
  }

  case Expr::SDiv: {
    SDivExpr *de = cast<SDivExpr>(e);
    Z3ErrorASTHandle left = constructInternal(de->left);
    Z3ErrorASTHandle right = constructInternal(de->right);
    Z3ErrorASTHandle result =
        Z3ErrorASTHandle(Z3_mk_bvsdiv(ctx, left, right), ctx);
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
    // LLVM's srem instruction says that the sign follows the dividend
    // (``left``).
    // Z3's C API says ``Z3_mk_bvsrem()`` does this so these seem to match.
    Z3ErrorASTHandle result =
        Z3ErrorASTHandle(Z3_mk_bvsrem(ctx, left, right), ctx);
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
      return bvLeftShift(left, (unsigned)CE->getLimitedValue());
    } else {
      Z3ErrorASTHandle amount = constructInternal(se->right);
      return bvVarLeftShift(left, amount);
    }
  }

  case Expr::LShr: {
    LShrExpr *lse = cast<LShrExpr>(e);
    Z3ErrorASTHandle left = constructInternal(lse->left);

    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(lse->right)) {
      return bvRightShift(left, (unsigned)CE->getLimitedValue());
    } else {
      Z3ErrorASTHandle amount = constructInternal(lse->right);
      return bvVarRightShift(left, amount);
    }
  }

  case Expr::AShr: {
    AShrExpr *ase = cast<AShrExpr>(e);
    Z3ErrorASTHandle left = constructInternal(ase->left);

    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(ase->right)) {
      unsigned shift = (unsigned)CE->getLimitedValue();
      return bvRightShift(left, shift);
    } else {
      Z3ErrorASTHandle amount = constructInternal(ase->right);
      return bvVarArithRightShift(left, amount);
    }
  }

  // Comparison

  case Expr::Eq: {
    EqExpr *ee = cast<EqExpr>(e);
    Z3ErrorASTHandle left = constructInternal(ee->left);
    Z3ErrorASTHandle right = constructInternal(ee->right);
    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(ee->left)) {
        if (CE->isTrue())
          return right;
        return notExpr(right);
    } else {
      return iffExpr(left, right);
    }
  }

  case Expr::Ult: {
    UltExpr *ue = cast<UltExpr>(e);
    Z3ErrorASTHandle left = constructInternal(ue->left);
    Z3ErrorASTHandle right = constructInternal(ue->right);
    return bvLtExpr(left, right);
  }

  case Expr::Ule: {
    UleExpr *ue = cast<UleExpr>(e);
    Z3ErrorASTHandle left = constructInternal(ue->left);
    Z3ErrorASTHandle right = constructInternal(ue->right);
    return bvLeExpr(left, right);
  }

  case Expr::Slt: {
    SltExpr *se = cast<SltExpr>(e);
    Z3ErrorASTHandle left = constructInternal(se->left);
    Z3ErrorASTHandle right = constructInternal(se->right);
    return sbvLtExpr(left, right);
  }

  case Expr::Sle: {
    SleExpr *se = cast<SleExpr>(e);
    Z3ErrorASTHandle left = constructInternal(se->left);
    Z3ErrorASTHandle right = constructInternal(se->right);
    return sbvLeExpr(left, right);
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
