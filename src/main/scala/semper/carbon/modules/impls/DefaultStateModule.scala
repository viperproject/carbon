package semper.carbon.modules.impls

import semper.carbon.modules._
import semper.sil.{ast => sil}
import semper.carbon.verifier.Verifier
import semper.carbon.boogie._
import semper.carbon.boogie.Implicits._
import semper.carbon.modules.components.StateComponent

/**
 * The default implementation of a [[semper.carbon.modules.StateModule]].
 *
 * @author Stefan Heule
 */
class DefaultStateModule(val verifier: Verifier) extends StateModule {
  def name = "State module"
  private val isGoodState = "state"

  implicit val stateNamespace = verifier.freshNamespace("state")

  override def assumeGoodState = Assume(FuncApp(Identifier(isGoodState), currentStateContributions, Bool))

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

  def staticGoodState: Exp = {
    FuncApp(Identifier(isGoodState), stateContributions map (v => LocalVar(v.name, v.typ)), Bool)
  }

  override type StateSnapshot = java.util.IdentityHashMap[StateComponent, Any]

  override def freshTempState: (Stmt, StateSnapshot) = {
    val snapshot = new java.util.IdentityHashMap[StateComponent, Any]()
    val s = (for (c <- components) yield {
      val (stmt, snap) = c.freshTempState
      snapshot.put(c, snap)
      stmt
    })
    (s, snapshot)
  }

  override def restoreState(snapshot: StateSnapshot): Stmt = {
    for (c <- components) yield {
      c.throwAwayTempState(snapshot.get(c).asInstanceOf[c.StateSnapshot])
    }
  }
}
