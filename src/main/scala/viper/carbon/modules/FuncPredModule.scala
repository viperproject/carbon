/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules

import viper.silver.{ast => sil}
import viper.carbon.boogie.{Stmt, Decl, Exp, Type}

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
  def translateFold(fold: sil.Fold): (Stmt,Stmt)

  def translateUnfold(unfold: sil.Unfold): Stmt

  def toExpressionsUsedInTriggers(e: Exp): Seq[Exp]
  def toExpressionsUsedInTriggers(e: Seq[Exp]): Seq[Seq[Exp]]
}
