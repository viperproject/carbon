// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.modules.components

import viper.silver.{ast => sil}
import viper.carbon.boogie._

/**
 * A statement component that only contributes at the end.

 */
trait SimpleStmtComponent extends StmtComponent {

  /**
   * Potentially contributes to the translation of a statement.  If no contribution
   * is desired, then [[viper.carbon.boogie.Statements.EmptyStmt]] can be used as a
   * return value.
   */
  def simpleHandleStmt(s: sil.Stmt, statesStackForPackageStmt: List[Any] = null, allStateAssms: Exp = TrueLit(), insidePackageStmt: Boolean = false): Stmt

  /**
    * statesStackForPackageStmt: stack of states used in translating statements during packaging a wand (carries currentState and LHS of wands)
    * insidePackageStmt: Boolean that represents whether this method is being called during packaging a wand or not.
    * allStateAssms: is a boolean expression that carries the conjunction for all the assumptions made about all states on 'statesStackForPackageStmt'
    *
    * These wand-related parameters (mentioned above) are used when translating statements during packaging a wand.
    * For more details refer to the general note in 'wandModule'.
    */
  override def handleStmt(s: sil.Stmt, statesStackForPackageStmt: List[Any] = null, allStateAssms: Exp = TrueLit(), insidePackageStmt: Boolean = false) : (Seqn => Seqn)
//  = (simpleHandleStmt(s),Statements.EmptyStmt )
}
