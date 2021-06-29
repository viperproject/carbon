// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.modules.impls

import viper.carbon.modules._
import viper.carbon.verifier.Verifier
import viper.carbon.boogie._
import viper.carbon.boogie.Implicits._
import viper.carbon.modules.components.CarbonStateComponent

import scala.collection.mutable
import scala.jdk.CollectionConverters.CollectionHasAsScala

/**
 * The default implementation of a [[viper.carbon.modules.StateModule]].
 */
class DefaultStateModule(val verifier: Verifier) extends StateModule {
  import verifier._

  def name = "State module"

  private val isGoodState = "state"

  implicit val stateNamespace = verifier.freshNamespace("state")

  override def assumeGoodState = {
    Assume(currentGoodState)
  }

  override def preamble = {
    Func(Identifier(isGoodState), staticStateContributions(), Bool)
  }

  override def reset : Unit = {
    curOldState = null
    curState = null
    //usingOldState = false
    //treatOldAsCurrent = false
    resetBoogieState
  }

  def initBoogieState: Stmt = {
    curState = new StateComponentMapping()
    // note: it is important that these are set before calling e.g. initState on components
    usingOldState = false

    // initialize the state of all components and assume that afterwards the
    // whole state is good
  val firstStmt =  components map (_.initBoogieState)
    // note: this code should come afterwards, to allow the components to reset their state variables
    for (c <- components) {
      curState.put(c, c.currentStateVars)
    }
    firstStmt ++ assumeGoodState // assumeGoodState needs the state components to be in place
  }
  def resetBoogieState: Stmt = {
    usingOldState = false
    curState = new StateComponentMapping()

    // initialize the state of all components and assume that afterwards the
    // whole state is good
    val firstStmt = components map (_.resetBoogieState)
    // note: this code should come afterwards, to allow the components to reset their state variables
    for (c <- components) {
      curState.put(c, c.currentStateVars)
    }
    firstStmt ++ assumeGoodState // assumeGoodState should come after the state vars have been updated
  }

  def initOldState: Stmt = {
    curOldState = new StateComponentMapping()
    for (c <- components) yield {
      val exps = curState.get(c)
      curOldState.put(c, exps) // Logic: whenever we *get* on the old state, we should wrap in "Old"
      exps map (e => Assume(e === Old(e))): Stmt
    }
  }


  def staticStateContributions(withHeap : Boolean = true, withPermissions : Boolean = true) : Seq[LocalVarDecl] = components flatMap (_.staticStateContributions(withHeap, withPermissions))
//  def currentStateContributions: Seq[LocalVarDecl] = components flatMap (_.currentStateContributions)
  def stateContributionValues(snap: StateSnapshot): Seq[Exp] = {
    var res : Seq[Exp] = Seq()
    val hashMap = snap._1
    for (c <- components) yield {
      if (hashMap.containsKey(c)) {
        res ++= hashMap.get(c)
      }
    }
    if(usingOldState) (res map (v => Old(v))) else res // ALEX: I think this conditional should be on the element of the StateSnapshot
  }


  // Note: For "old" state, these variables should be wrapped in "Old(.)" before use
  type StateComponentMapping = java.util.IdentityHashMap[CarbonStateComponent, Seq[Var]]
  override type StateSnapshot = (StateComponentMapping, Boolean, Boolean) // mapping to vars, using old state, treating old state as current

  private var curOldState: StateComponentMapping = null
  private var curState: StateComponentMapping = null

  def staticGoodState: Exp = {
    FuncApp(Identifier(isGoodState), staticStateContributions() map (v => LocalVar(v.name, v.typ)), Bool)
  }

  def currentGoodState: Exp = {
    FuncApp(Identifier(isGoodState), currentStateContributionValues, Bool)
  }

  private lazy val stateRepository = new mutable.HashMap[String, StateSnapshot]()

  override def stateRepositoryPut(name:String, snapshot: StateSnapshot) = stateRepository.put(name,snapshot)

  override def stateRepositoryGet(name:String) : Option[StateSnapshot] = stateRepository.get(name)

  override def freshTempState(name: String, discardCurrent: Boolean = false, initialise: Boolean = false): (Stmt, StateSnapshot) = {
    val previousState = new StateSnapshot(new StateComponentMapping(), usingOldState, false)

    curState = new StateComponentMapping() // essentially, the code below "clones" what curState should represent anyway. But, if we omit this line, we inadvertently alias the previous hash map.

    val s = for (c <- components) yield {
      val tmpExps = c.freshTempState(name)
      val curExps = c.currentStateExps // note: this will wrap them in "Old" as necessary for correct initialisation
      val stmt: Stmt = if (discardCurrent) Nil else (tmpExps zip curExps) map (x => (x._1 := x._2))
      previousState._1.put(c, c.currentStateVars) // reconstruct information from previous state (this is logically similar to a clone of what curState used to represent)
      curState.put(c, tmpExps) // repopulate current state
      c.restoreState(tmpExps)

      (if (initialise) c.resetBoogieState else stmt)
    }
    usingOldState = false // we have now set up a temporary state in terms of "old" - this could happen when an unfolding expression is inside an "old"
    (s, previousState)
  }

  override def freshTempStateKeepCurrent(name: String) : StateSnapshot = {
    val freshState = new StateComponentMapping()

    for (c <- components) yield {
      val tmpExps = c.freshTempState(name)
      freshState.put(c, tmpExps)
    }

    (freshState, false, false)
  }

  override def initToCurrentStmt(snapshot: StateSnapshot) : Stmt = {
    for (e <- snapshot._1.entrySet().asScala.toSeq) yield {
      val s: Stmt = (e.getValue zip e.getKey.currentStateExps) map (x => x._1 := x._2)
      s
    }
  }

  def freshEmptyState(name: String, init: Boolean = false): (Stmt, StateSnapshot) =
  {
    freshTempState(name, true, init)
  }

  override def replaceState(snapshot: StateSnapshot): Unit = {
    curState = snapshot._1
        for (c <- components) {
      c.restoreState(snapshot._1.get(c))
    }
    usingOldState = snapshot._2
  }

  override def equateHeaps(snapshot: StateSnapshot, c: CarbonStateComponent):Stmt =
  {
    heapModule.equateWithCurrentHeap(snapshot._1.get(c))
  }

  // initialisation in principle not needed - one should call initState
  var usingOldState = false

  override def stateModuleIsUsingOldState: Boolean = {
    usingOldState
  }

  override def oldState: StateSnapshot = {
    (curOldState,true,false) // the chosen boolean values here seem sensible, but they probably shouldn't be used anyway
  }

  override def replaceOldState(snapshot: StateSnapshot): Unit = {
    curOldState = snapshot._1
  }

  override def state: StateSnapshot = {
    (curState,usingOldState,false)
  }

  override def getCopyState:StateSnapshot = {
    val currentCopy = new StateComponentMapping()
    val s = for (c <- components) yield {
                currentCopy.put(c, c.currentStateVars)
            }
    (currentCopy, usingOldState, false)
  }
}
