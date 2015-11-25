/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules.impls

import viper.carbon.modules._
import viper.carbon.verifier.Verifier
import viper.carbon.boogie._
import viper.carbon.boogie.Implicits._
import viper.carbon.modules.components.CarbonStateComponent

/**
 * The default implementation of a [[viper.carbon.modules.StateModule]].
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

  def initBoogieState: Stmt = {
    curState = new StateComponentMapping()
    // note: it is important that these are set before calling e.g. initState on components
    usingOldState = false
    treatOldAsCurrent = false

    // initialize the state of all components and assume that afterwards the
    // whole state is good
  val stmt =  (components map (_.initBoogieState)) :+
      assumeGoodState
    // note: this code should come afterwards, to allow the components to reset their state variables
    for (c <- components) {
      curState.put(c, c.currentStateVars)
    }
    stmt
  }
  def resetBoogieState: Stmt = {
    usingOldState = false
    treatOldAsCurrent = false
    curState = new StateComponentMapping()

    // initialize the state of all components and assume that afterwards the
    // whole state is good
    val stmt = (components map (_.resetBoogieState)) :+
      assumeGoodState
    // note: this code should come afterwards, to allow the components to reset their state variables
    for (c <- components) {
      curState.put(c, c.currentStateVars)
    }
    stmt
  }
  def initOldState: Stmt = {
    curOldState = new StateComponentMapping()
    for (c <- components) yield {
      val exps = curState.get(c)
      curOldState.put(c, exps) // Logic: whenever we *get* on the old state, we should wrap in "Old"
      exps map (e => Assume(e === Old(e))): Stmt
    }
  }
  def stateContributions: Seq[LocalVarDecl] = components flatMap (_.stateContributions)
  def currentStateContributions: Seq[Exp] = components flatMap (_.currentStateExps)

  def staticGoodState: Exp = {
    FuncApp(Identifier(isGoodState), stateContributions map (v => LocalVar(v.name, v.typ)), Bool)
  }

  // Note: For "old" state, these variables should be wrapped in "Old(.)" before use
  type StateComponentMapping = java.util.IdentityHashMap[CarbonStateComponent, Seq[Var]]
  override type StateSnapshot = (StateComponentMapping,Boolean,Boolean)

  private var curOldState: StateComponentMapping = null
  private var curState: StateComponentMapping = null

  override def freshTempState(name: String): (Stmt, StateSnapshot) = {
    val previousState = new StateSnapshot(new StateComponentMapping(),usingOldState,treatOldAsCurrent)

    curState = new StateComponentMapping() // essentially, the code below "clones" what curState should represent anyway. But, if we omit this line, we inadvertently alias the previous hash map.

    val s = for (c <- components) yield {
      val tmpExps = c.freshTempState(name)
      val curExps = c.currentStateExps // note: this will wrap them in "Old" as necessary for correct initialisation
      val stmt: Stmt = (tmpExps zip curExps) map (x => (x._1 := x._2))
      previousState._1.put(c, c.currentStateVars) // reconstruct information from previous state (this is logically similar to a clone of what curState used to represent)
      curState.put(c, tmpExps) // repopulate current state
      c.restoreState(tmpExps)

      stmt
    }
    treatOldAsCurrent = usingOldState
    usingOldState = false // we have now set up a temporary state in terms of "old" - this could happen when an unfolding expression is inside an "old"
    (s, previousState)
  }

  override def replaceState(snapshot: StateSnapshot) {
    curState = snapshot._1
    for (c <- components) {
      c.restoreState(snapshot._1.get(c))
    }
    usingOldState = snapshot._2
    treatOldAsCurrent = snapshot._3
  }

  // initialisation in principle not needed - one should call initState
  var usingOldState = false
  var treatOldAsCurrent = false

  override def stateModuleIsUsingOldState: Boolean = {
    usingOldState
  }

  override def oldState: StateSnapshot = {
    if (treatOldAsCurrent) state else (curOldState,true,false) // boolean values here seem sensible, but they probably shouldn't be used anyway
  }

  override def replaceOldState(snapshot: StateSnapshot) {
    curOldState = snapshot._1
  }

  override def state: StateSnapshot = {
    (curState,usingOldState,treatOldAsCurrent)
  }
}
