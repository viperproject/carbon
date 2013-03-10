package semper.carbon.modules

import semper.sil.{ast => sil}
import semper.carbon.boogie._

/**
 * A module for translating SIL programs by invoking the right modules and
 * gathering all the preambles, etc.
 *
 * @author Stefan Heule
 */
trait MainModule extends Module {
  /**
   * Translate a SIL program into a Boogie program.
   */
  def translate(p: sil.Program): Program

  def translateFunction(f: sil.Function): Seq[Decl]
  def translateDomain(d: sil.Domain): Seq[Decl]
  def translateFieldDecl(f: sil.Field): Seq[Decl]
  def translatePredicate(p: sil.Predicate): Seq[Decl]
  def translateMethod(m: sil.Method): Seq[Decl]
}
