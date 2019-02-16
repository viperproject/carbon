/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules

import viper.silver.{ast => sil}
import viper.carbon.boogie._

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
    * statesStackForPackageStmt: stack of states used in translating statements during packaging a wand (carries currentState and LHS of wands)
    * insidePackageStmt: Boolean that represents whether this method is being called during packaging a wand or not.
    * The 'statesStackForPackageStmt' and 'insidePackageStmt' are used when translating statements during packaging a wand.
    * For more details refer to the general note in 'wandModule'.
    */
  def translateFold(fold: sil.Fold, statesStackForPackageStmt: List[Any] = null, insidePackageStmt: Boolean = false): (Stmt,Stmt)

  /**
    * statesStackForPackageStmt: stack of states used in translating statements during packaging a wand (carries currentState and LHS of wands)
    * insidePackageStmt: Boolean that represents whether this method is being called during packaging a wand or not.
    * The 'statesStackForPackageStmt' and 'insidePackageStmt' are used when translating statements during packaging a wand.
    * For more details refer to the general note in 'wandModule'.
    */
  def translateUnfold(unfold: sil.Unfold, statesStackForPackageStmt: List[Any] = null, insidePackageStmt: Boolean = false): Stmt

  def toExpressionsUsedInTriggers(e: Exp): Seq[Exp]
  def toExpressionsUsedInTriggers(e: Seq[Exp]): Seq[Seq[Exp]]
}
