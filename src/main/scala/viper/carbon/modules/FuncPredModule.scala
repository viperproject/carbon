/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules

import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.silver.ast.PredicateAccessPredicate

/**
 * A module for translating functions and predicates.

 */
trait FuncPredModule extends Module {
  def translateFunction(f: sil.Function): Seq[Decl]

  def translateFuncApp(fa: sil.FuncApp): Exp

  // wrap an expression in a dummy function with "true" value (sometimes useful for triggering)
  def dummyFuncApp(e: Exp): Exp

  def translatePredicate(p: sil.Predicate): Seq[Decl]

  def predicateVersionType : Type

  def assumeAllFunctionDefinitions: Stmt

  def translateResult(r: sil.Result): Exp

  // code to go first, and code to go last (other modules may contribute in between)
  /**
    * statesStack is the stack of states used (to exhale from) during packaging a magic wand (it carries the current state, left-hand side state).
    * statesStack also carries the left-hand side states of the outer magic wands in case of nested package statements
    *
    * inWand distinguishes whether this method is called during a package statement or not.
    *
    * Both 'statesStack' and 'inWand' are passed to the 'exhale' and 'inhale' methods that are called during the translation of the fold
    */
  def translateFold(fold: sil.Fold, statesStack: List[Any] = null, inWand: Boolean = false): (Stmt,Stmt)

  /**
    * statesStack is the stack of states used (to exhale from) during packaging a magic wand (it carries the current state, left-hand side state).
    * statesStack also carries the left-hand side states of the outer magic wands in case of nested package statements
    *
    * inWand distinguishes whether this method is called during a package statement or not.
    *
    * Both 'statesStack' and 'inWand' are passed to the 'exhale' and 'inhale' methods that are called during the translation of the unfold
    */
  def translateUnfold(unfold: sil.Unfold, statesStack: List[Any] = null, inWand: Boolean = false): Stmt

  def toExpressionsUsedInTriggers(e: Exp): Seq[Exp]
  def toExpressionsUsedInTriggers(e: Seq[Exp]): Seq[Seq[Exp]]
}
