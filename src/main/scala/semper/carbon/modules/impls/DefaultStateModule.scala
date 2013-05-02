package semper.carbon.modules.impls

import semper.carbon.modules._
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
  def initOldState: Stmt = {
    curOldState = new java.util.IdentityHashMap[StateComponent, Seq[Exp]]()
    for (c <- components) yield {
      val exps = curState.get(c)
      curOldState.put(c, exps map (e => Old(e)))
      exps map (e => Assume(e === Old(e))): Stmt
    }
  }
  def stateContributions: Seq[LocalVarDecl] = components flatMap (_.stateContributions)
  def currentStateContributions: Seq[Exp] = components flatMap (_.currentState)

  def staticGoodState: Exp = {
    FuncApp(Identifier(isGoodState), stateContributions map (v => LocalVar(v.name, v.typ)), Bool)
  }

  override type StateSnapshot = java.util.IdentityHashMap[StateComponent, Seq[Exp]]

  private var curOldState: StateSnapshot = null
  private var curState: StateSnapshot = {
    val res = new java.util.IdentityHashMap[StateComponent, Seq[Exp]]()
    for (c <- components) {
      res.put(c, c.currentState)
    }
    res
  }

  override def freshTempState: (Stmt, StateSnapshot) = {
    val snapshot = new java.util.IdentityHashMap[StateComponent, Seq[Exp]]()
    val s = (for (c <- components) yield {
      val snap = c.freshTempState
      val curExps = curState.get(c)
      val stmt: Stmt = (curExps zip snap) map (x => (x._1 := x._2))
      snapshot.put(c, curExps)
      stmt
    })
    (s, snapshot)
  }

  override def restoreState(snapshot: StateSnapshot) {
    curState = snapshot
    for (c <- components) {
      c.restoreState(snapshot.get(c))
    }
  }

  override def useOldState() {
    for (c <- components) {
      c.restoreState(curOldState.get(c))
    }
  }

  override def useRegularState() {
    for (c <- components) {
      c.restoreState(curState.get(c))
    }
  }

  override def oldState: StateSnapshot = {
    curOldState
  }

  override def restoreOldState(snapshot: StateSnapshot) {
    curOldState = snapshot
  }

  override def state: StateSnapshot = {
    curState
  }
}
