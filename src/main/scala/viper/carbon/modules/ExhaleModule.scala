/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules

import components.{ComponentRegistry, ExhaleComponent}
import viper.silver.{ast => sil}
import viper.carbon.boogie.{Exp, LocalVar, Stmt, TrueLit}
import viper.silver.verifier.PartialVerificationError

/**
 * A module for translating exhale statements.  The module takes care of the basic
 * structure of exhaling (like multiple phases) and exhaling boolean connectives
 * such as logical and or logical implication.  Other modules can register themselves
 * as [[viper.carbon.modules.components.ExhaleComponent]]s to perform the exhale
 * operation of certain expressions.
 *
 * The module also implements [[viper.carbon.modules.components.ExhaleComponent]]
 * and performs some default behavior for most expressions.

 */
trait ExhaleModule extends Module with ExhaleComponent with ComponentRegistry[ExhaleComponent] {

  /**
    * @param statesStack stack of states used in translating package statements (carries currentState and LHS of wands)
    * @param inWand Boolean that represents whether this exhale is inside package statement or not
    * @return
    */
  def exhale(exp: Seq[(sil.Exp, PartialVerificationError)], havocHeap: Boolean = true, isAssert: Boolean = false
             , statesStack: List[Any] = null, inWand: Boolean = false): Stmt

  def currentPhaseId: Int
}
