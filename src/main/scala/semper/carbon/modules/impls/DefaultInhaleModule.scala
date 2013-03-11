package semper.carbon.modules.impls

import semper.carbon.modules._
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.Verifier

/**
 * The default implementation of a [[semper.carbon.modules.InhaleModule]].
 *
 * @author Stefan Heule
 */
class DefaultInhaleModule(val verifier: Verifier) extends InhaleModule {
  def name = "Inhale module"
  override def inhale(t: sil.Exp): Stmt = {
    ???
  }
}
