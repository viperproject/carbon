// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.modules.components

import viper.carbon.boogie.{Statements, Stmt}
import viper.silver.{ast => sil}
import viper.silver.verifier.PartialVerificationError

/**
 * Takes care of exhaling one or several kinds of expressions.

 */
trait ExhaleComponent extends Component {

  /**
   * Exhale a single expression.
   */
  def exhaleExp(e: sil.Exp, error: PartialVerificationError): Stmt = Statements.EmptyStmt

  /**
    * The first part of the result is used before exhaling the expression, and finally after exhaling the expression
    * the second part of the result is used.
    */
  def exhaleExpBeforeAfter(e: sil.Exp, error: PartialVerificationError): (() => Stmt, () => Stmt) =
    (() => exhaleExp(e, error), () => Statements.EmptyStmt)

}
