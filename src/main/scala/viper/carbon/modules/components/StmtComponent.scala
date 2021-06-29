// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.modules.components

import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.silver.ast.LocalVar

/**
 * Contributes to the translation of one or several statements.
 */
trait StmtComponent extends Component {

  /**
    * Potentially contributes to the translation of a statement.  If no contribution
    * is desired, then [[viper.carbon.boogie.Statements.EmptyStmt]] can be used as a
    * return value.
    * The return is a function that shows how the returned statemenst should be merged with the translation for other components
    * e.g., Some statements is added to the beginning of the translation and others at the end
    *
    *
    * statesStackForPackageStmt: stack of states used in translating statements during packaging a wand (carries currentState and LHS of wands)
    * insidePackageStmt: Boolean that represents whether this method is being called during packaging a wand or not.
    * allStateAssms: is a boolean expression that carries the conjunction for all the assumptions made about all states on 'statesStackForPackageStmt'
    *
    * These wand-related parameters (mentioned above) are used when translating statements during packaging a wand.
    * For more details refer to the general note in 'wandModule'.
   */
  def handleStmt(s: sil.Stmt, statesStackOfPackageStmt: List[Any] = null, allStateAssms: Exp = TrueLit(), insidePackageStmt: Boolean = false): (Seqn => Seqn)

  /**
   * This method is called when translating a "fresh" statement, and by default does nothing
   */
  def freshReads(fb: Seq[LocalVar]): Stmt = Statements.EmptyStmt
}
