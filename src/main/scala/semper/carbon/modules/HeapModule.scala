package semper.carbon.modules

import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.modules.components.StateComponent

/**
 * A module for translating heap expressions (access, updating) and determining
 * the heap encoding.
 *
 * @author Stefan Heule
 */
trait HeapModule extends Module with StateComponent {

  /**
   * The type used for references.
   */
  def refType: Type

  /**
   * The type used for fields.
   */
  def fieldType: Type

  /**
   * Definitions for a field.
   */
  def translateField(f: sil.Field): Seq[Decl]

  /**
   * Definitions for the ghost field of a predicate.
   */
  def predicateGhostFieldDecl(f: sil.Predicate): Seq[Decl]

  /**
   * Translation of a field read.
   */
  def translateFieldAccess(f: sil.FieldAccess): Exp

  def locationMaskIndex(f: sil.LocationAccess): Exp

  /**
   * Translation of the null literal.
   */
  def translateNull: Exp

  /**
   * Check that the receiver of a location access is non-null.
   */
  def checkNonNullReceiver(loc: sil.LocationAccess): Exp = {
    verifier.expModule.translateExp(loc.rcv) !== translateNull
  }

  /**
   * Begin of exhale.
   */
  def beginExhale: Stmt

  /**
   * End of exhale
   */
  def endExhale: Stmt
}
