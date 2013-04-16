package semper.carbon.modules

import semper.sil.{ast => sil}
import semper.carbon.boogie.{Stmt, LocalVar, Exp}
import semper.carbon.modules.components.{ComponentRegistry, DefinednessComponent}
import semper.sil.verifier.PartialVerificationError

/**
 * A module for translating SIL expressions.
 *
 * @author Stefan Heule
 */
trait ExpModule extends Module with ComponentRegistry[DefinednessComponent] {
  def translateExp(exp: sil.Exp): Exp
  def translateLocalVar(l: sil.LocalVar): LocalVar

  /**
   * Check definedness of SIL expressions as they occur in the program.
   */
  def checkDefinedness(e: sil.Exp, error: PartialVerificationError): Stmt
}
