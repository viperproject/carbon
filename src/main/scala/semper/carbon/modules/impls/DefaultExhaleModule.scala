package semper.carbon.modules.impls

import semper.carbon.modules._
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.Verifier
import Implicits._

/**
 * The default implementation of a [[semper.carbon.modules.ExhaleModule]].
 *
 * @author Stefan Heule
 */
class DefaultExhaleModule(val verifier: Verifier) extends ExhaleModule {

  import verifier.expModule._

  def name = "Exhale module"

  override def initialize() {
    register(this)
  }

  override def exhale(exps: Seq[sil.Exp]): Stmt = {
    exps map exhaleConnective
  }

  /**
   * Inhales SIL expression connectives (such as logical and/or) and forwards the
   * translation of other expressions to the exhale components.
   */
  def exhaleConnective(e: sil.Exp): Stmt = {
    e match {
      case sil.And(e1, e2) =>
        exhaleConnective(e1) ::
          exhaleConnective(e2) ::
          Nil
      case sil.Implies(e1, e2) =>
        If(translateExp(e1), exhaleConnective(e2), Statements.EmptyStmt)
      case sil.CondExp(c, e1, e2) =>
        If(translateExp(c), exhaleConnective(e1), exhaleConnective(e2))
      case _ =>
        components map (_.exhaleExp(e))
    }
  }

  override def exhaleExp(e: sil.Exp): Stmt = {
    // TODO: only do this for expressions that are known to be handled by the expression module
    // and return the empty statement otherwise
    Assert(translateExp(e))
  }
}
