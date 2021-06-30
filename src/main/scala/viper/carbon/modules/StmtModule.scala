// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.modules

import viper.carbon.modules.components.{ComponentRegistry, StmtComponent}
import viper.silver.{ast => sil}
import viper.carbon.boogie.{Exp, Namespace, Stmt, TrueLit}

/**
 * A module for translating Viper statements.
 */

/**
  * statesStackForPackageStmt: stack of states used in translating statements during packaging a wand (carries currentState and LHS of wands)
  * insidePackageStmt: Boolean that represents whether this method is being called during packaging a wand or not.
  * allStateAssms: is a boolean expression that carries the conjunction for all the assumptions made about all states on 'statesStackForPackageStmt'
  *
  * These wand-related parameters (mentioned above) are used when translating statements during packaging a wand.
  * For more details refer to the general note in 'wandModule'.
  */
trait StmtModule extends Module with ComponentRegistry[StmtComponent] {

  /**
    * Return initial statement to be used at the beginning of the method body encoding (for example, code for labels).
    * This method also sets up the internal state of the module and should thus be invoked before any statements are
    * translated
    */
  def initStmt(methodBody: sil.Stmt) : Stmt

  def translateStmt(stmt: sil.Stmt, statesStackForPackageStmt: List[Any] = null, allStateAssms: Exp = TrueLit(), insidePackageStmt: Boolean = false): Stmt

  def labelNamespace: Namespace
}
