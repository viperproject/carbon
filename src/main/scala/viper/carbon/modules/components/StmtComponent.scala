/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules.components

import viper.silver.{ast => sil}
import viper.carbon.boogie.{Statements, Stmt}
import viper.silver.ast.LocalVar

/**
 * Contributes to the translation of one or several statements.
 */
trait StmtComponent extends Component {

  /**
   * Potentially contributes to the translation of a statement.  If no contribution
   * is desired, then [[viper.carbon.boogie.Statements.EmptyStmt]] can be used as a
   * return value.
   *
   * The pair (a,b) is used as follows: a is used at the beginning of the translation so
   * far, and b at the end.
   */
  def handleStmt(s: sil.Stmt): (Stmt, Stmt)

  /**
   * This method is called when translating a "fresh" statement, and by default does nothing
   */
  def freshReads(fb: Seq[LocalVar]): Stmt = Statements.EmptyStmt

  /**
   * This method is called at the beginning of translating a constraining read permission block,
   * and by default does nothing.
   */
  def enterConstrainingBlock(fb: sil.Constraining): Stmt = Statements.EmptyStmt

  /**
   * This method is called at the end of translating a constaining read permission block,
   * and by default does nothing.
   */
  def leaveConstrainingBlock(fb: sil.Constraining): Stmt = Statements.EmptyStmt
}
