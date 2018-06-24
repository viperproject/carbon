/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

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
  def simpleHandleStmt(s: sil.Stmt, statesStack: List[Any] = null, allStateAssms: Exp = TrueLit(), inWand: Boolean = false): Stmt

  override def handleStmt(s: sil.Stmt, statesStack: List[Any] = null, allStateAssms: Exp = TrueLit(), inWand: Boolean = false) : (Seqn => Seqn)
//  = (simpleHandleStmt(s),Statements.EmptyStmt )
}
