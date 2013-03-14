package semper.carbon.modules.impls

import semper.carbon.modules._
import semper.sil.{ast => sil}
import semper.carbon.verifier.Verifier
import semper.carbon.boogie.{Seqn, Stmt, LocalVarDecl, Exp}

/**
 * The default implementation of a [[semper.carbon.modules.StateModule]].
 *
 * @author Stefan Heule
 */
class DefaultStateModule(val verifier: Verifier) extends StateModule {
  def name = "State module"

  def initState: Stmt = Seqn(components map (_.initState))
  def stateContributions: Seq[LocalVarDecl] = components flatMap (_.stateContributions)
  def currentStateContributions: Seq[Exp] = components flatMap (_.currentStateContributions)
}
