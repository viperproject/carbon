/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package semper.carbon.modules.impls

import semper.carbon.modules._
import semper.carbon.verifier.Verifier
import semper.carbon.boogie._
import semper.carbon.boogie.Implicits._
import semper.carbon.modules.components.StateComponent

/**
 * The default implementation of a [[semper.carbon.modules.StateModule]].
 */
class DefaultStateModule(val verifier: Verifier) extends StateModule {
  def name = "State module"
  private val isGoodState = "state"

  implicit val stateNamespace = verifier.freshNamespace("state")

  override def assumeGoodState = {
    Assume(FuncApp(Identifier(isGoodState), currentStateContributions, Bool))
  }

  override def preamble = {
    Func(Identifier(isGoodState), stateContributions, Bool)
  }

  def initState: Stmt = {
    curState = new java.util.IdentityHashMap[StateComponent, Seq[Exp]]()
    for (c <- components) {
      curState.put(c, c.currentState)
    }
    // initialize the state of all components and assume that afterwards the
    // whole state is good
    (components map (_.initState)) :+
      assumeGoodState
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
  private var curState: StateSnapshot = null

  override def freshTempState(name: String): (Stmt, StateSnapshot) = {
    val previousState = new java.util.IdentityHashMap[StateComponent, Seq[Exp]]()
    val s = (for (c <- components) yield {
      val tmpExps = c.freshTempState(name)
      val curExps = curState.get(c)
      val stmt: Stmt = (tmpExps zip curExps) map (x => (x._1 := x._2))
      previousState.put(c, curExps)
      curState.put(c, tmpExps)
      c.restoreState(tmpExps)
      stmt
    })
    (s, previousState)
  }

  override def restoreState(snapshot: StateSnapshot) {
    curState = snapshot
    for (c <- components) {
      c.restoreState(snapshot.get(c))
    }
  }

  var usingOldState = false
  override def useOldState() {
    usingOldState = true
    for (c <- components) {
      c.restoreState(curOldState.get(c))
    }
  }

  override def useRegularState() {
    usingOldState = false
    for (c <- components) {
      c.restoreState(curState.get(c))
    }
  }

  override def isUsingOldState: Boolean = {
    usingOldState
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
