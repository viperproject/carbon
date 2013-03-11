package semper.carbon.modules.impls

import semper.carbon.modules._
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.Verifier

/**
 * The default implementation of a [[semper.carbon.modules.ExhaleModule]].
 *
 * @author Stefan Heule
 */
class DefaultExhaleModule(val verifier: Verifier) extends ExhaleModule {
  def name = "Exhale module"
  override def exhale(t: sil.Exp): Stmt = {
    ???
  }
}
