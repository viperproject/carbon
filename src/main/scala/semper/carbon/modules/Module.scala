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
   * Initialize this module and register any potential components with other modules.  At the point
   * where this method is called, all modules in Verifier have been set, but the other modules
   * might not have been fully initialized (by calling this method).
   */
  def initialize() {}

  /**
   * The Boogie code that this module will insert into the preamble (optional).
   *
   * The convention is that the verifier will first translate the full SIL program, and only after the
   * translation ask all the modules to give preamble definitions.  This allows modules to first see
   * if certain features are needed, and only output parts of the preamble that are used.
   */
  def preamble: Seq[Decl] = Nil

  /**
   * Returns true for variables and constants that this module might declare.  Note all elements
   * for which true is returned need to actually occur in the end, but every variable or constant that
   * does occur, it must returns true here.
   *
   * By default, no names are defined.
   */
  def definesGlobalVar(s: String): Boolean = false

  /**
   * Returns true for functions that this module might declare.  Note all elements
   * for which true is returned need to actually occur in the end, but every function that
   * does occur, it must returns true here.
   *
   * By default, no names are defined.
   */
  def definesGlobalFunc(s: String): Boolean = false
}
