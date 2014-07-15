/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules

import components.{InhaleComponent, ComponentRegistry}
import viper.silver.{ast => sil}
import viper.carbon.boogie.{Stmt, Exp}

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
  def inhale(exp: Seq[sil.Exp]): Stmt
}
