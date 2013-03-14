package semper.carbon.modules.impls

import semper.carbon.modules._
import semper.sil.{ast => sil}
import semper.carbon.verifier.Verifier
import semper.carbon.boogie._
import semper.carbon.boogie.Implicits._

/**
 * The default implementation of a [[semper.carbon.modules.StateModule]].
 *
 * @author Stefan Heule
 */
class DefaultStateModule(val verifier: Verifier) extends StateModule {
  def name = "State module"
  private val isGoodState = "IsGoodState"

  override def preamble = {
    Func(isGoodState, stateContributions, Bool)
  }

  def initState: Stmt = {
    Seqn(
      (components map (_.initState)) :+
        Assume(FuncApp(isGoodState, currentStateContributions))
    )
  }
  def stateContributions: Seq[LocalVarDecl] = components flatMap (_.stateContributions)
  def currentStateContributions: Seq[Exp] = components flatMap (_.currentStateContributions)
}
