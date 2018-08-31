/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules

import viper.silver.{ast => sil}
import viper.silver.ast.utility.Expressions.{whenExhaling, whenInhaling}
import viper.carbon.boogie.{Exp, LocalVar, Stmt, TrueLit}
import viper.carbon.modules.components.{ComponentRegistry, DefinednessComponent}
import viper.silver.verifier.PartialVerificationError

/**
 * A module for translating Viper expressions.
 */
trait ExpModule extends Module with ComponentRegistry[DefinednessComponent] {
  def translateExp(exp: sil.Exp): Exp

  /**
    * Prepares the correct state in which translating an expression takes place then calls translateExp
    * The states in which the expressions are evaluated during a package statement is 'wandModuel.UNIONState'
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
      * If 'inWand is true', the current state is replaced with the 'wandModule.UNIONState' state
      * while checking definedness
      *
      */
  def checkDefinedness(e: sil.Exp, error: PartialVerificationError, makeChecks: Boolean = true,
                        inWand: Boolean = false, ignoreIfInWand: Boolean = false): Stmt

  /**
   * Check definedness of Viper assertions such as pre-/postconditions or invariants.
   * The implementation works by inhaling 'e' and checking the necessary properties
   * along the way.
    *
    *
    * inWand distinguishes whether check definedness is called during a package statement or not.
    *
    * statesStack is the stack of states used during packaging a magic wand (it carries the current state, left-hand side state).
    * statesStack also carries the left-hand side states of the outer magic wands in case of nested package statements.
   */
  def checkDefinednessOfSpecAndInhale(e: sil.Exp, error: PartialVerificationError, statesStack: List[Any] = null, inWand: Boolean = false): Stmt

  /**
   * Convert all InhaleExhale expressions to their exhale part and call checkDefinednessOfSpecAndInhale.
   */
  def checkDefinednessOfExhaleSpecAndInhale(expressions: Seq[sil.Exp],
                                            errorConstructor: (sil.Exp) => PartialVerificationError): Seq[Stmt] = {
    expressions map (e => {
      checkDefinednessOfSpecAndInhale(whenExhaling(e), errorConstructor(e))
    })
  }

  /**
   * Convert all InhaleExhale expressions to their inhale part and call checkDefinednessOfSpecAndInhale.
   */
  def checkDefinednessOfInhaleSpecAndInhale(expressions: Seq[sil.Exp],
                                            errorConstructor: (sil.Exp) => PartialVerificationError): Seq[Stmt] = {
    expressions map (e => {
      checkDefinednessOfSpecAndInhale(whenInhaling(e), errorConstructor(e))
    })
  }

  /**
   * Check definedness of Viper assertions such as pre-/postconditions or invariants.
   * The implementation works by exhaling 'e' and checking the necessary properties
   * along the way.
   *
   * inWand distinguishes whether check definedness is called during a package statement or not.
   *
   * statesStack is the stack of states used during packaging a magic wand (it carries the current state, left-hand side state).
   * statesStack also carries the left-hand side states of the outer magic wands in case of nested package statements.
   *
   */
  def checkDefinednessOfSpecAndExhale(e: sil.Exp, definednessError: PartialVerificationError, exhaleError: PartialVerificationError,
                                      statesStack: List[Any] = null, inWand: Boolean = false): Stmt
}
