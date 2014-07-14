package semper.carbon.modules

import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.Environment

/**
 * A module for translating SIL programs by invoking the right modules and
 * gathering all the preambles, etc.
 */
trait MainModule extends Module {
  /**
   * Translate a SIL program into a Boogie program.
   */
  def translate(p: sil.Program): Program

  /**
   * Translate a local variable along with its type (into a boogie declaration).  Assumes that the variable is already
   * defined in the current environment.
   */
  def translateLocalVarSig(typ:sil.Type, v:sil.LocalVar): LocalVarDecl
  def translateLocalVarDecl(l: sil.LocalVarDecl): LocalVarDecl = {
    translateLocalVarSig(l.typ,l.localVar)
  }


  /** The current environment. */
  var env: Environment = null

  /** The namespace for SIL local variables. */
  def silVarNamespace: Namespace

  /** Used to encode assumptions made about valid values of a given type (e.g. allocation of non-null references) */
  /** the "isParameter" flag can be used to select assumptions which only apply to parameters */
  def allAssumptionsAboutValue(typ:sil.Type, arg: LocalVarDecl, isParameter: Boolean): Stmt
  def allAssumptionsAboutValue(arg:sil.LocalVarDecl, isParameter: Boolean) : Stmt = {
    allAssumptionsAboutValue(arg.typ,translateLocalVarDecl(arg),isParameter)
  }

}
