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
trait StmtModule extends Module with ComponentRegistry[StmtComponent] {
  def translateStmt(stmt: sil.Stmt, statesStack: List[Any] = null, allStateAssms: Exp = TrueLit(), inWand: Boolean = false): Stmt
}
