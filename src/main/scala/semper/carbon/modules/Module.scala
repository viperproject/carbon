package semper.carbon.modules

import semper.sil.{ast => sil}
import semper.carbon.boogie.Decl
import semper.carbon.verifier.Verifier

/**
 * Common trait for modules.
 *
 * @author Stefan Heule
 */
trait Module {
  /** The verifier to interact with other modules. */
  def verifier: Verifier

  /**
   * The name of this module, e.g., "Heap module"
   */
  def name: String

  /**
   * The Boogie code that this module will insert into the preamble (optional).
   *
   * The convention is that the verifier will first translate the full SIL program, and only after the
   * translation ask all the modules to give preamble definitions.  This allows modules to first see
   * if certain features are needed, and only output parts of the preamble that are used.
   */
  def preamble: Seq[Decl] = Nil
}
