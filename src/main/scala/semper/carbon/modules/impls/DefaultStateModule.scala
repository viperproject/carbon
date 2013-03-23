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

  implicit val stateNamespace = verifier.freshNamespace("state")

  override def assumeGoodState = Assume(FuncApp(Identifier(isGoodState), currentStateContributions))

  override def preamble = {
    Func(Identifier(isGoodState), stateContributions, Bool)
  }

  def initState: Stmt = {
    // initialize the state of all components and assume that afterwards the
    // whole state is good
    Seqn(
      (components map (_.initState)) :+
        assumeGoodState
    )
  }
  def stateContributions: Seq[LocalVarDecl] = components flatMap (_.stateContributions)
  def currentStateContributions: Seq[Exp] = components flatMap (_.currentStateContributions)
}
