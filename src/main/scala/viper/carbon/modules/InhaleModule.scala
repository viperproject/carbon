/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules

import components.{ComponentRegistry, InhaleComponent}
import viper.silver.{ast => sil}
import viper.carbon.boogie.Stmt

/**
 * A module for translating inhale statements.  The module takes care of the basic
 * structure of inhaling as well as inhaling boolean connectives
 * such as logical and or logical implication.  Other modules can register themselves
 * as [[viper.carbon.modules.components.InhaleComponent]]s to perform the inhale
 * operation of certain expressions.
 *
 * The module also implements [[viper.carbon.modules.components.InhaleComponent]]
 * and performs some default behavior for most expressions.

 */
trait InhaleModule extends Module with InhaleComponent with ComponentRegistry[InhaleComponent] {
  /**
    * statesStackForPackageStmt: stack of states used in translating statements during packaging a wand (carries currentState and LHS of wands)
    * insidePackageStmt: Boolean that represents whether this method is being called during packaging a wand or not.
    * The 'statesStackForPackageStmt' and 'insidePackageStmt' are used when translating statements during packaging a wand.
    * For more details refer to the general note in 'wandModule'.
    */
  def inhale(exp: Seq[sil.Exp], statesStackForPackageStmt: List[Any] = null, insidePackageStmt: Boolean = false): Stmt
}
