// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.modules

import viper.silver.{ast => sil}
import viper.carbon.boogie.{Exp, LocalVar, Stmt}
import viper.carbon.modules.components.{ComponentRegistry, DefinednessComponent}
import viper.silver.verifier.PartialVerificationError

/**
 * A module for translating Viper expressions.
 */
trait ExpModule extends Module with ComponentRegistry[DefinednessComponent] {
  def translateExp(exp: sil.Exp): Exp

  /**
    * Used to translate expressions during packaging a wand.
    * This method Prepares the correct state in which translating an expression takes place then calls translateExp
    */
  def translateExpInWand(exp: sil.Exp): Exp

  def translateLocalVar(l: sil.LocalVar): LocalVar

  /**
   * Free assumptions about an expression.
   */
  def allFreeAssumptions(e: sil.Exp): Stmt

    /**
      * Check definedness of Viper expressions as they occur in the program.
      *
      * makeChecks provides the possibility of switching off most checks, to get
      * only the side-effects (unfoldings) of unravelling the expression. Note that
      * the parameter should be passed down through recursive calls (default true)
      *
      * ignoreIfInWand gives the option to ignore the definedness check if it is called during a package statement
      *
      * inWand distinguish when check definedness is called during a package statement.
      */
  def checkDefinedness(e: sil.Exp, error: PartialVerificationError, makeChecks: Boolean = true,
                       insidePackageStmt: Boolean = false, ignoreIfInWand: Boolean = false): Stmt

  /**
   * Check definedness of Viper assertions such as pre-/postconditions or invariants.
   * The implementation works by exhaling 'e' and checking the necessary properties
   * along the way.
   *
   * statesStackForPackageStmt stack of states used in translating statements during packaging a wand (carries currentState and LHS of wands)
   * insidePackageStmt      Boolean that represents whether this method is being called during packaging a wand or not.
   * The 'statesStackForPackageStmt' and 'insidePackageStmt' are used when translating statements during packaging a wand.
   * For more details refer to the general note in 'wandModule'.
   */
  def checkDefinednessOfSpecAndExhale(e: sil.Exp, definednessError: PartialVerificationError, exhaleError: PartialVerificationError,
                                      statesStackForPackageStmt: List[Any] = null, insidePackageStmt: Boolean = false): Stmt
}
