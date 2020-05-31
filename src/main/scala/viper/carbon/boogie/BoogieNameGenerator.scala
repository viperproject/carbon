// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.carbon.boogie

import viper.silver.utility.DefaultNameGenerator

class BoogieNameGenerator extends DefaultNameGenerator {
  // in principle, some others would also be allowed, but this is good enough for now
  private val otherChars = "_.$#'`~^\\?a-zA-Z"
  def firstCharacter = s"[$otherChars]".r
  def otherCharacter = s"[0-9$otherChars]".r
  def separator = "_"
  def reservedNames = allReservedNames
  val boogieReservedNames: Set[String] = Set("div", "mod", "const", "procedure", "type", "function", "lambda", "uniqu", "complete", "if", "else", "free",
    "invariant", "goto", "break", "return", "call", "forall", "assert", "havoc", "assume", "returns", "var", "implementation",
    "axiom", "exists", "old", "false", "real", "int", "true", "bool", "finite", "ensures", "requires", "where", "par") ++
    Set("Set", "MultiSet", "Seq")
  val SMTreservedNames: Set[String] = Set(
    // Basic symbols:
    "", "!", "_", "as", "DECIMAL", "exists", "forall", "let", "NUMERAL", "par", "STRING",
    // Commands:
    "assert", "check-sat", "declare-sort", "declare-fun", "define-sort,", "define-fun", "exit",
    "get-assertions", "get-assignment", "get-info", "get-option,", "get-proof", "get-unsat-core",
    "get-value", "pop", "push", "set-logic", "set-info", "set-option",
    // Core theory:
    "and", "or", "not", "iff", "true", "false", "xor", "distinct", "ite", "=", "Bool",
    "=>", // implies (sic!)
    // Integers and reals
    "Int", "Real", "*", "/", "-", "~", "+", "<", "<=", ">", ">=", "div", "mod", "rem",
    "^", "sin", "cos", "tan", "asin", "acos", "atan", "sinh", "cosh", "tanh", "asinh", "acosh", "atanh", "pi", "euler",
    "to_real", "to_int", "is_int",
    // Bitvectors
    "extract", "concat",
    "bvnot", "bvneg", "bvand", "bvor", "bvadd", "bvmul", "bvudiv", "bvurem", "bvshl", "bvlshr", "bvult",
    // arrays
    "store", "select", "const", "default", "map", "union", "intersect", "difference", "complement",
    "subset", "array-ext", "as-array", "Array",
    // Z3 (and not only?) extensions to bitvectors
    "bit1", "bit0", "bvsub", "bvsdiv", "bvsrem", "bvsmod", "bvsdiv0", "bvudiv0", "bvsrem0", "bvurem0",
    "bvsmod0", "bvsdiv_i", "bvudiv_i", "bvsrem_i", "bvurem_i", "bvumod_i", "bvule", "bvsle", "bvuge",
    "bvsge", "bvslt", "bvugt", "bvsgt", "bvxor", "bvnand", "bvnor", "bvxnor", "sign_extend", "zero_extend",
    "repeat", "bvredor", "bvredand", "bvcomp", "bvumul_noovfl", "bvsmul_noovfl", "bvsmul_noudfl", "bvashr",
    "rotate_left", "rotate_right", "ext_rotate_left", "ext_rotate_right", "int2bv", "bv2int", "mkbv",
    // floating point (FIXME: Legacy, remove this)
    "plusInfinity", "minusInfinity",
    "+", "-", "/", "*", "==", "<", ">", "<=", ">=",
    "abs", "remainder", "fusedMA", "squareRoot", "roundToIntegral",
    "isZero", "isNZero", "isPZero", "isSignMinus", "min", "max", "asFloat",
    // SMT v1 stuff (FIXME: Legacy, remove this)
    "flet", "implies", "!=", "if_then_else",
    // Z3 extensions
    "lblneg", "lblpos", "lbl-lit",
    "if", "&&", "||", "equals", "equiv", "bool", "minimize", "maximize",
    // Boogie-defined
    "real_pow", "UOrdering2", "UOrdering3",
    // Floating point (final draft SMTLIB-v2.5)
    "NaN",
    "fp.abs", "fp.neg", "fp.add", "fp.sub", "fp.mul", "fp.div", "fp.fma", "fp.sqrt", "fp.rem", "fp.roundToIntegral",
    "fp.min", "fp.max", "fp.leq", "fp.lt", "fp.geq", "fp.gt", "fp.eq",
    "fp.isNormal", "fp.isSubnormal", "fp.isZero", "fp.isInfinite", "fp.isNaN", "fp.isNegative", "fp.isPositive",
    "fp", "fp.to_ubv", "fp.to_sbv", "to_fp",
    // Rounding mode
    "rmode",
    "roundNearestTiesToEven", "roundNearestTiesToAway", "roundTowardPositive", "roundTowardNegative", "roundTowardZero",
    "RNE", "RNA", "RTP", "RTN", "RTZ",
  )
  val allReservedNames = boogieReservedNames.union(SMTreservedNames)
}
