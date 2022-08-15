// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.modules

import components.{ComponentRegistry, InhaleComponent}
import viper.silver.{ast => sil}
import viper.carbon.boogie.Stmt
import viper.silver.ast.utility.Expressions.{whenExhaling, whenInhaling}
import viper.silver.verifier.PartialVerificationError

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
    * Inhale assertions and pure expressions with potential definedness checks made along the way.
    * Special case: If definedness checks are added and if the input Viper state has no permissions, then the returned
    * Boogie statement checks whether the input assertions are self-framing.
    * @param exps
    * @param addDefinednessChecks enables definedness checks iff set to true
    * @param statesStackForPackageStmt stack of states used in translating statements during packaging a wand (carries currentState and LHS of wands)
    * @param insidePackageStmt indicates whether this method is being called during a package of a wand (true) or not (false)
    * @return
    */
  def inhale(exps: Seq[(sil.Exp, PartialVerificationError)], addDefinednessChecks: Boolean, statesStackForPackageStmt: List[Any] = null, insidePackageStmt: Boolean = false): Stmt

  def inhaleWithDefinednessCheck(exp: sil.Exp, error: PartialVerificationError, statesStack: List[Any] = null, inWand: Boolean = false): Stmt =
    inhale(Seq((exp, error)), addDefinednessChecks = true, statesStack, inWand)

  /**
    * Convert all InhaleExhale expressions to their exhale part and inhale with definedness checks.
    */
  def inhaleExhaleSpecWithDefinednessCheck(expressions: Seq[sil.Exp],
                                            errorConstructor: sil.Exp => PartialVerificationError): Seq[Stmt] = {
    expressions map (e => {
      inhaleWithDefinednessCheck(whenExhaling(e), errorConstructor(e))
    })
  }

  /**
    * Convert all InhaleExhale expressions to their inhale part and inhale with definedness checks.
    */
  def inhaleInhaleSpecWithDefinednessCheck(expressions: Seq[sil.Exp],
                                            errorConstructor: sil.Exp => PartialVerificationError): Seq[Stmt] = {
    expressions map (e => {
      inhaleWithDefinednessCheck(whenInhaling(e), errorConstructor(e))
    })
  }
}
