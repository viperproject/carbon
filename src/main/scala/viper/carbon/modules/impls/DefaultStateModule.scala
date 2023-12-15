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

  override def preamble: Seq[Decl] = {
    Func(Identifier(isGoodState), staticStateContributions(), Bool) ++
    {
      val prevState = stateModule.state
      stateModule.replaceState(stateModule.pureState)
      // TODO: It would be great if we could use StateModule.currentStateContributionValues, but that will not
      // give us the pure state (see comment there). Once that is fixed, this should be changed accordingly.
      val stateExps = components flatMap (_.currentStateExps)
      val res = FuncApp(Identifier(isGoodState), stateExps, Bool)
      stateModule.replaceState(prevState)
      // This axiom corresponds to the Boogie expression "state(dummyHeap, emptyMask)",
      // which is necessary since function definitional axioms trigger on "state(heap, mask), f(heap, args)",
      // so without this assumption, function calls with dummyHeap and emptyMask won't trigger the definition.
      Axiom(res)
    }
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
    val freshSnapshot = freshTempStateKeepCurrentAux("old", true)
    curOldState = freshSnapshot._1
    initToCurrentStmt(freshSnapshot)
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
    res
  }


  // Note: For "old" state, these variables should be wrapped in "Old(.)" before use
  type StateComponentMapping = java.util.IdentityHashMap[CarbonStateComponent, Seq[Var]]
  override type StateSnapshot = (StateComponentMapping, Boolean, Boolean) // mapping to vars, using old state, using pure state

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
    if(name == "old") {
      sys.error("freshTempState invoked with reserved \"old\" name")
    }

    val previousState = new StateSnapshot(new StateComponentMapping(), usingOldState, usingPureState)

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
    freshTempStateKeepCurrentAux(name, false)
  }

  private def freshTempStateKeepCurrentAux(name: String, usedForOldState: Boolean) : StateSnapshot = {
    if(name == "old" && !usedForOldState) {
      sys.error("freshTempStateKeepCurrent invoked with reserved \"old\" name")
    }

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
    usingPureState = snapshot._3
  }

  override def equateHeaps(snapshot: StateSnapshot, c: CarbonStateComponent):Stmt =
  {
    heapModule.equateWithCurrentHeap(snapshot._1.get(c))
  }

  // initialisation in principle not needed - one should call initState
  var usingOldState = false
  var usingPureState = false

  override def stateModuleIsUsingOldState: Boolean = {
    usingOldState
  }

  override def stateModuleIsUsingPureState: Boolean = {
    usingPureState
  }

  override def oldState: StateSnapshot = {
    (curOldState, true, false) // the chosen boolean values here seem sensible, but they probably shouldn't be used anyway
  }

  override def pureState: StateSnapshot = {
    (curState, false, true)
  }

  override def replaceOldState(snapshot: StateSnapshot): Unit = {
    curOldState = snapshot._1
  }

  override def state: StateSnapshot = {
    (curState, usingOldState, usingPureState)
  }

  override def getCopyState:StateSnapshot = {
    val currentCopy = new StateComponentMapping()
    val s = for (c <- components) yield {
                currentCopy.put(c, c.currentStateVars)
            }
    (currentCopy, usingOldState, usingPureState)
  }
}
