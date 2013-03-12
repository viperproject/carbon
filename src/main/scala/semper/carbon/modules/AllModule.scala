package semper.carbon.modules

import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.Environment

/**
 * A trait that has most methods of all modules and forwards calls to the correct module
 * from the verifier.  This is used for convenience to simplify module implementations
 * by allowing to directly call `translate` and other methods.
 */
trait AllModule extends Module {
  /**
   * The environment currently used.
   */
  def env: Environment = verifier.mainModule.env

  def translateStmt(s: sil.Stmt): Stmt = verifier.stmtModule.translateStmt(s)
  def translateExp(e: sil.Exp): Exp = verifier.expModule.translateExp(e)
  def translateType(t: sil.Type): Type = verifier.typeModule.translateType(t)
  def translate(p: sil.Program): Program = verifier.mainModule.translate(p)
}
