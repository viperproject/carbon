package semper.carbon.modules

import semper.sil.{ast => sil}
import semper.carbon.boogie.{Stmt, LocalVar, Exp}
import semper.carbon.modules.components.{ComponentRegistry, DefinednessComponent}
import semper.sil.verifier.PartialVerificationError

/**
 * A module for translating SIL expressions.
 */
trait ExpModule extends Module with ComponentRegistry[DefinednessComponent] {
  def translateExp(exp: sil.Exp): Exp
  def translateLocalVar(l: sil.LocalVar): LocalVar

  /**
   * Free assumptions about an expression.
   */
  def allFreeAssumptions(e: sil.Exp): Stmt

  /**
   * Check definedness of SIL expressions as they occur in the program.
   *
   * makeChecks provides the possibility of switching off most checks, to get 
   * only the side-effects (unfoldings) of unravelling the expression. Note that
   * the parameter should be passed down through recursive calls (default true)
   */
  def checkDefinedness(e: sil.Exp, error: PartialVerificationError, makeChecks: Boolean = true): Stmt

  /**
   * Check definedness of SIL assertions such as pre-/postconditions or invariants.
   * The implementation works by inhaling 'e' and checking the necessary properties
   * along the way.
   */
  def checkDefinednessOfSpecAndInhale(e: sil.Exp, error: PartialVerificationError): Stmt

  /**
   * Check definedness of SIL assertions such as pre-/postconditions or invariants.
   * The implementation works by exhaling 'e' and checking the necessary properties
   * along the way.
   */
  def checkDefinednessOfSpecAndExhale(e: sil.Exp, definednessError: PartialVerificationError, exhaleError: PartialVerificationError): Stmt
}
