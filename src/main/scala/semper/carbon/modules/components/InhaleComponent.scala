/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package semper.carbon.modules.components

import semper.carbon.boogie.Stmt
import semper.sil.{ast => sil}
import semper.sil.verifier.PartialVerificationError

/**
 * Takes care of inhaling one or several kinds of expressions.

 */
trait InhaleComponent extends Component {

  /**
   * Exhale a single expression.
   */
  def inhaleExp(exp: sil.Exp): Stmt
}
