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
   * The type used for fields of type t.
   */
  def fieldTypeOf(t: Type): Type

  /**
   * The type used for predicates.
   */
  def predicateVersionFieldType(genericT: String = "A"): Type

  /**
   * The type used for predicates mask fields.
   */
  def predicateMaskFieldType: Type

  /**
   * The type used for predicates mask fields of a given predicate family.
   */
  def predicateMaskFieldTypeOf(p: sil.Predicate): Type

  /**
   * The type used for predicates of a given family.
   */
  def predicateVersionFieldTypeOf(p: sil.Predicate): Type

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
  def translateLocationAccess(f: sil.LocationAccess): Exp

  def translateLocation(f: sil.LocationAccess): Exp

  /**
   * Translation of the null literal.
   */
  def translateNull: Exp

  /**
   * Check that the receiver of a location access is non-null.
   */
  def checkNonNullReceiver(loc: sil.LocationAccess): Exp = {
    loc match {
      case sil.FieldAccess(rcv, _) =>
        verifier.expModule.translateExp(rcv) !== translateNull
      case _ => TrueLit()
    }
  }

  /**
   * Begin of exhale.
   */
  def beginExhale: Stmt

  /**
   * End of exhale
   */
  def endExhale: Stmt

  /**
   * Is the given field a predicate field?
   */
  def isPredicateField(f: Exp): Exp

  /**
   * Generate a trigger for a given predicate.
   */
  def predicateTrigger(pred: sil.PredicateAccess): Stmt
}
