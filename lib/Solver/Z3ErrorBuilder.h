//===-- Z3ErrorBuilder.h ---------------------------------------*- C++ -*-====//
//
// The KLEE Symbolic Virtual Machine with Numerical Error Analysis Extension
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef __UTIL_Z3BUILDER_H__
#define __UTIL_Z3BUILDER_H__

#include "klee/util/ExprHashMap.h"
#include "klee/util/ArrayExprHash.h"
#include "klee/Config/config.h"
#include <z3.h>

namespace klee {

template <typename T> class Z3ErrorNodeHandle {
  // Internally these Z3 types are pointers
  // so storing these should be cheap.
  // It would be nice if we could infer the Z3_context from the node
  // but I can't see a way to do this from Z3's API.
protected:
  T node;
  ::Z3_context context;

private:
  // To be specialised
  inline ::Z3_ast as_ast();

public:
  Z3ErrorNodeHandle() : node(NULL), context(NULL) {}
  Z3ErrorNodeHandle(const T _node, const ::Z3_context _context)
      : node(_node), context(_context) {
    if (node && context) {
      ::Z3_inc_ref(context, as_ast());
    }
  };
  ~Z3ErrorNodeHandle() {
    if (node && context) {
      ::Z3_dec_ref(context, as_ast());
    }
  }
  Z3ErrorNodeHandle(const Z3ErrorNodeHandle &b)
      : node(b.node), context(b.context) {
    if (node && context) {
      ::Z3_inc_ref(context, as_ast());
    }
  }
  Z3ErrorNodeHandle &operator=(const Z3ErrorNodeHandle &b) {
    if (node == NULL && context == NULL) {
      // Special case for when this object was constructed
      // using the default constructor. Try to inherit a non null
      // context.
      context = b.context;
    }
    assert(context == b.context && "Mismatched Z3 contexts!");
    // node != nullptr ==> context != NULL
    assert((node == NULL || context) &&
           "Can't have non nullptr node with nullptr context");

    if (node && context) {
      ::Z3_dec_ref(context, as_ast());
    }
    node = b.node;
    if (node && context) {
      ::Z3_inc_ref(context, as_ast());
    }
    return *this;
  }
  // To be specialised
  void dump();

  operator T() { return node; }
};

// Specialise for Z3_sort
template <> inline ::Z3_ast Z3ErrorNodeHandle<Z3_sort>::as_ast() {
  // In Z3 internally this call is just a cast. We could just do that
  // instead to simplify our implementation but this seems cleaner.
  return ::Z3_sort_to_ast(context, node);
}
template <> inline void Z3ErrorNodeHandle<Z3_sort>::dump() {
  llvm::errs() << "Z3SortHandle:\n" << ::Z3_sort_to_string(context, node)
               << "\n";
}
typedef Z3ErrorNodeHandle<Z3_sort> Z3SortHandle;

// Specialise for Z3_ast
template <> inline ::Z3_ast Z3ErrorNodeHandle<Z3_ast>::as_ast() { return node; }
template <> inline void Z3ErrorNodeHandle<Z3_ast>::dump() {
  llvm::errs() << "Z3ASTHandle:\n" << ::Z3_ast_to_string(context, as_ast())
               << "\n";
}
typedef Z3ErrorNodeHandle<Z3_ast> Z3ErrorASTHandle;

class Z3ErrorArrayExprHash : public ArrayExprHash<Z3ErrorASTHandle> {

  friend class Z3ErrorBuilder;

public:
  Z3ErrorArrayExprHash() {};
  virtual ~Z3ErrorArrayExprHash();
  void clear();
};

class Z3ErrorBuilder {
  ExprHashMap<Z3ErrorASTHandle> constructed;
  Z3ErrorArrayExprHash _arr_hash;

private:
  Z3ErrorASTHandle bvOne();
  Z3ErrorASTHandle bvZero();
  Z3ErrorASTHandle bvMinusOne();
  Z3ErrorASTHandle realConst(uint64_t value);
  Z3ErrorASTHandle intConst(uint64_t value);
  Z3ErrorASTHandle bvZExtConst(uint64_t value);
  Z3ErrorASTHandle bvSExtConst(uint64_t value);
  Z3ErrorASTHandle bvBoolExtract(Z3ErrorASTHandle expr);
  Z3ErrorASTHandle bvExtract(Z3ErrorASTHandle expr, unsigned top,
                             unsigned bottom);
  Z3ErrorASTHandle eqExpr(Z3ErrorASTHandle a, Z3ErrorASTHandle b);

  // logical left and right shift (not arithmetic)
  Z3ErrorASTHandle bvLeftShift(Z3ErrorASTHandle expr, unsigned shift);
  Z3ErrorASTHandle bvRightShift(Z3ErrorASTHandle expr, unsigned shift);
  Z3ErrorASTHandle bvVarLeftShift(Z3ErrorASTHandle expr,
                                  Z3ErrorASTHandle shift);
  Z3ErrorASTHandle bvVarRightShift(Z3ErrorASTHandle expr,
                                   Z3ErrorASTHandle shift);
  Z3ErrorASTHandle bvVarArithRightShift(Z3ErrorASTHandle expr,
                                        Z3ErrorASTHandle shift);

  Z3ErrorASTHandle notExpr(Z3ErrorASTHandle expr);
  Z3ErrorASTHandle bvNotExpr(Z3ErrorASTHandle expr);
  Z3ErrorASTHandle andExpr(Z3ErrorASTHandle lhs, Z3ErrorASTHandle rhs);
  Z3ErrorASTHandle bvAndExpr(Z3ErrorASTHandle lhs, Z3ErrorASTHandle rhs);
  Z3ErrorASTHandle orExpr(Z3ErrorASTHandle lhs, Z3ErrorASTHandle rhs);
  Z3ErrorASTHandle bvOrExpr(Z3ErrorASTHandle lhs, Z3ErrorASTHandle rhs);
  Z3ErrorASTHandle iffExpr(Z3ErrorASTHandle lhs, Z3ErrorASTHandle rhs);
  Z3ErrorASTHandle bvXorExpr(Z3ErrorASTHandle lhs, Z3ErrorASTHandle rhs);
  Z3ErrorASTHandle bvSignExtend(Z3ErrorASTHandle src, unsigned width);

  // Array operations
  Z3ErrorASTHandle writeExpr(Z3ErrorASTHandle array, Z3ErrorASTHandle index,
                             Z3ErrorASTHandle value);
  Z3ErrorASTHandle readExpr(Z3ErrorASTHandle array, Z3ErrorASTHandle index);

  // ITE-expression constructor
  Z3ErrorASTHandle iteExpr(Z3ErrorASTHandle condition,
                           Z3ErrorASTHandle whenTrue,
                           Z3ErrorASTHandle whenFalse);

  // Bitvector length
  unsigned getBVLength(Z3ErrorASTHandle expr);

  // Bitvector comparison
  Z3ErrorASTHandle bvLtExpr(Z3ErrorASTHandle lhs, Z3ErrorASTHandle rhs);
  Z3ErrorASTHandle bvLeExpr(Z3ErrorASTHandle lhs, Z3ErrorASTHandle rhs);
  Z3ErrorASTHandle sbvLtExpr(Z3ErrorASTHandle lhs, Z3ErrorASTHandle rhs);
  Z3ErrorASTHandle sbvLeExpr(Z3ErrorASTHandle lhs, Z3ErrorASTHandle rhs);

  Z3ErrorASTHandle getInitialArray(const Array *os);
  Z3ErrorASTHandle getArrayForUpdate(const Array *root, const UpdateNode *un);

  Z3ErrorASTHandle constructActual(ref<Expr> e);
  Z3ErrorASTHandle constructInternal(ref<Expr> e);

  Z3ErrorASTHandle buildArray(const char *name);

  Z3SortHandle getRealSort();
  Z3SortHandle getIntSort();
  Z3SortHandle getArraySort(Z3SortHandle domainSort, Z3SortHandle rangeSort);
  bool autoClearConstructCache;

public:
  Z3_context ctx;

  Z3ErrorBuilder(bool autoClearConstructCache = true);
  ~Z3ErrorBuilder();

  Z3ErrorASTHandle getTrue();
  Z3ErrorASTHandle getFalse();
  Z3ErrorASTHandle getInitialRead(const Array *os, unsigned index);

  Z3ErrorASTHandle construct(ref<Expr> e) {
    Z3ErrorASTHandle res = constructInternal(e);
    if (autoClearConstructCache)
      clearConstructCache();
    return res;
  }

  void clearConstructCache() { constructed.clear(); }
};
}

#endif
