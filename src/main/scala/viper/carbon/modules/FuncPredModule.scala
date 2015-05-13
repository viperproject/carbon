/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules

import viper.silver.{ast => sil}
import viper.carbon.boogie.{Stmt, Decl, Exp}

/**
 * A module for translating functions and predicates.

 */
trait FuncPredModule extends Module {
  def translateFunction(f: sil.Function): Seq[Decl]

  def translateFuncApp(fa: sil.FuncApp): Exp

  def translatePredicate(p: sil.Predicate): Seq[Decl]

  def assumeAllFunctionDefinitions: Stmt

  def translateResult(r: sil.Result): Exp

  // code to go first, and code to go last (other modules may contribute in between)
  def translateFold(fold: sil.Fold): (Stmt,Stmt)

  def translateUnfold(unfold: sil.Unfold): Stmt

  def toTriggers(e: Exp): Exp
}
