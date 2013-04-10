package semper.carbon.modules.impls

import semper.carbon.modules._
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.Verifier
import semper.carbon.boogie.Implicits._

/**
 * The default implementation of a [[semper.carbon.modules.InhaleModule]].
 *
 * @author Stefan Heule
 */
class DefaultInhaleModule(val verifier: Verifier) extends InhaleModule {

  import verifier.expModule._

  def name = "Inhale module"

  override def initialize() {
    register(this)
  }

  override def inhale(exps: Seq[sil.Exp]): Stmt = {
    exps map (inhaleConnective(_))
  }

  /**
   * Inhales SIL expression connectives (such as logical and/or) and forwards the
   * translation of other expressions to the inhale components.
   */
  def inhaleConnective(e: sil.Exp): Stmt = {
    e match {
      case sil.And(e1, e2) =>
        inhaleConnective(e1) ::
          inhaleConnective(e2) ::
          Nil
      case sil.Implies(e1, e2) =>
        If(translateExp(e1), inhaleConnective(e2), Statements.EmptyStmt)
      case sil.CondExp(c, e1, e2) =>
        If(translateExp(c), inhaleConnective(e1), inhaleConnective(e2))
      case _ =>
        val stmt = components map (_.inhaleExp(e))
        if (stmt.children.isEmpty) sys.error(s"missing translation for inhaling of $e")
        stmt
    }
  }

  override def inhaleExp(e: sil.Exp): Stmt = {
    if (e.isPure) {
      Assume(translateExp(e))
    } else {
      Nil
    }
  }
}
