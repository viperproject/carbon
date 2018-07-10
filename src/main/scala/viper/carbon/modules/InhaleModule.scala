/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules

import components.{ComponentRegistry, InhaleComponent}
import viper.silver.{ast => sil}
import viper.carbon.boogie.{Exp, LocalVar, Stmt, TrueLit}

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
    * @param statesStack stack of states used in translating package statement (carries currentState and LHS of wands)
    * @param inWand Boolean that represents whether this exhale is inside package statement or not
    */
  def inhale(exp: Seq[sil.Exp], statesStack: List[Any] = null, inWand: Boolean = false): Stmt
}
