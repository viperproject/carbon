package semper.carbon.modules.impls

import semper.carbon.modules._
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.Verifier
import Implicits._
import semper.sil.verifier.PartialVerificationError
import semper.sil.verifier.reasons._

/**
 * The default implementation of a [[semper.carbon.modules.ExhaleModule]].
 *
 * @author Stefan Heule
 */
class DefaultExhaleModule(val verifier: Verifier) extends ExhaleModule {

  import verifier._
  import expModule._
  import permModule._

  def name = "Exhale module"

  override def initialize() {
    register(this)
  }

  override def exhale(exps: Seq[(sil.Exp, PartialVerificationError)]): Stmt = {
    for (phase <- 1 to numberOfPhases) yield {
      val stmts = exps map (e => exhaleConnective(e._1, e._2, phase - 1))
      if (stmts.children.isEmpty) {
        Statements.EmptyStmt
      } else {
        (Comment(s"Phase $phase: ${phaseDescription(phase-1)}") ++ stmts): Stmt
      }
    }
  }

  /**
   * Exhales SIL expression connectives (such as logical and/implication) and forwards the
   * translation of other expressions to the exhale components.
   */
  def exhaleConnective(e: sil.Exp, error: PartialVerificationError, phase: Int): Stmt = {
    e match {
      case sil.And(e1, e2) =>
        exhaleConnective(e1, error, phase) ::
          exhaleConnective(e2, error, phase) ::
          Nil
      case sil.Implies(e1, e2) =>
        If(translateExp(e1), exhaleConnective(e2, error, phase), Statements.EmptyStmt)
      case sil.CondExp(c, e1, e2) =>
        If(translateExp(c), exhaleConnective(e1, error, phase), exhaleConnective(e2, error, phase))
      case _ if phaseOf(e) == phase =>
        val stmt = components map (_.exhaleExp(e, error))
        if (stmt.children.isEmpty) sys.error(s"missing translation for exhaling of $e")
        stmt
      case _ =>
        Nil // nothing to do in this phase
    }
  }

  override def exhaleExp(e: sil.Exp, error: PartialVerificationError): Stmt = {
    if (e.isPure) {
      Assert(translateExp(e), error.dueTo(AssertionFalse(e)))
    } else {
      Nil
    }
  }
}
