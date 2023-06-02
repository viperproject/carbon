// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.modules

import viper.silver.{ast => sil}
import viper.carbon.boogie.{Exp, LocalVar, Stmt}
import viper.carbon.modules.components.{ComponentRegistry, DefinednessComponent, DefinednessState}
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

  /***
    * Check well-definedness of Viper expressions. This method should only be invoked on pure Viper expressions or
    * impure *atomic* Viper assertions (e.g., accessibility predicates, quantified permissions).
    * For other kinds of impure assertions such as separating conjunctions where one conjunct is impure, well-definedness
    * is always tied to an inhale or exhale (or assert) operation. In those cases, the corresponding inhale and exhale
    * methods should be invoked, which permit switching on well-definedness checks.
    *
    * @param e
    * @param error
    * @param makeChecks provides the possibility of switching off most checks, to get only the side-effects (unfoldings)
    *                   of unravelling the expression. Note that the parameter should be passed down through recursive
    *                   calls (default true)
    * @param definednessStateOpt If defined, then represents the state in which permission checks that are part of the definedness
    *                            check should be made, otherwise these checks should be made in the currently active state.
    *                            Expressions should be evaluated in the currently active state.
    * @param insidePackageStmt true if call is made during a package statement
    * @param ignoreIfInWand gives the option to ignore the definedness check if it is called during a package statement
    * @return
    */
  def checkDefinedness(e: sil.Exp, error: PartialVerificationError, makeChecks: Boolean = true,
                       definednessStateOpt: Option[DefinednessState] = None,
                       insidePackageStmt: Boolean = false, ignoreIfInWand: Boolean = false): Stmt

}
