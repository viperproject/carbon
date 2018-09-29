/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules

import viper.carbon.modules.components.{ComponentRegistry, DefinednessComponent, StmtComponent}
import viper.silver.{ast => sil}
import viper.carbon.boogie.{Exp, Stmt, TrueLit}

/**
 * A module for translating Viper statements.
 */

/**
  * statesStack is the stack of states used during packaging a magic wand (it carries the current state, left-hand side state).
  * statesStack also carries the left-hand side states of the outer magic wands in case of nested package statements
  *
  * inWand distinguishes whether this method is called during a package statement or not.
  *
  * allStateAssms is a boolean expression that carries the conjunction for all the assumptions made about all states on statesStack
  *
  * These wand-related parameters (mentioned above) are passed to the called methods (exhale, fold, inhale, ...) when translating
  * a statement during packaging a magic wand
  */
trait StmtModule extends Module with ComponentRegistry[StmtComponent] {
  def translateStmt(stmt: sil.Stmt, statesStack: List[Any] = null, allStateAssms: Exp = TrueLit(), inWand: Boolean = false): Stmt
}
