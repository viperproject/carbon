package semper.carbon.modules

import semper.sil.{ast => sil}
import semper.carbon.boogie.{Decl, Type, Exp}

/**
 * A module for translating heap expressions (access, updating) and determining
 * the heap encoding.
 *
 * @author Stefan Heule
 */
trait HeapModule extends Module {

  /**
   * The type used for references.
   */
  def refType: Type

  /**
   * Definitions for a field.
   */
  def translateField(f: sil.Field): Seq[Decl]

  /**
   * Translation of a field read.
   */
  def translateFieldAccess(f: sil.FieldAccess): Exp

  /**
   * Translation of the this literal.
   */
  def translateThis(): Exp
}
