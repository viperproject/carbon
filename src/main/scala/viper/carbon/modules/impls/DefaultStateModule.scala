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

import scala.collection.mutable


/**
 * The default implementation of a [[viper.carbon.modules.StateModule]].
 */
class DefaultStateModule(val verifier: Verifier) extends StateModule {
  def name = "State module"

  private val isGoodState = "state"

  implicit val stateNamespace = verifier.freshNamespace("state")

  override def assumeGoodState = {
    Assume(currentGoodState)
  }

  override def preamble = {
    Func(Identifier(isGoodState), staticStateContributions, Bool)
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
  def staticStateContributions: Seq[LocalVarDecl] = components flatMap (_.staticStateContributions)
  def currentStateContributions: Seq[LocalVarDecl] = components flatMap (_.currentStateContributions)
  def currentStateContributionValues: Seq[Exp] = components flatMap (_.currentStateExps)


  def staticGoodState: Exp = {
    FuncApp(Identifier(isGoodState), staticStateContributions map (v => LocalVar(v.name, v.typ)), Bool)
  }

  def currentGoodState: Exp = {
    FuncApp(Identifier(isGoodState), currentStateContributionValues, Bool)
  }

  // Note: For "old" state, these variables should be wrapped in "Old(.)" before use
  type StateComponentMapping = java.util.IdentityHashMap[CarbonStateComponent, Seq[Var]]
  override type StateSnapshot = (StateComponentMapping, Boolean, Boolean)


  private var curOldState: StateComponentMapping = null
  private var curState: StateComponentMapping = null

  private lazy val stateRepository = new mutable.HashMap[String, StateSnapshot]()

  override def stateRepositoryPut(name:String, snapshot: StateSnapshot) = stateRepository.put(name,snapshot)

  override def stateRepositoryGet(name:String) : Option[StateSnapshot] = stateRepository.get(name)

  override def freshTempState(name: String, discardCurrent: Boolean = false, initialise: Boolean = false): (Stmt, StateSnapshot) = {
    val previousState = new StateSnapshot(new StateComponentMapping(), usingOldState, treatOldAsCurrent)

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
    treatOldAsCurrent = usingOldState
    usingOldState = false // we have now set up a temporary state in terms of "old" - this could happen when an unfolding expression is inside an "old"
    (s, previousState)
  }

  def freshEmptyState(name: String, init: Boolean = false): (Stmt, StateSnapshot) =
  {
    freshTempState(name, true, init)
   // val (stmt,snapshot) = freshTempState(name)

   // (stmt ++ resetState ++ (if(init) initState else Nil), snapshot)
  }
//
//  {
//    val emptyState = new java.util.IdentityHashMap[StateComponent, Seq[Exp]]()
//    val s = (for (c <- components) yield {
//      val tmpExps = c.freshTempState(name)
//      val curExps = curState.get(c)
//      emptyState.put(c, tmpExps)
//      val stmt: Stmt  =
//        (tmpExps) map (x => x match {
//          case v@LocalVar(_,_) => Havoc(v)
//          //Gaurav: should this be implemented by the components themselves?
//          case _ => Statements.EmptyStmt
//        })
//      /*Gaurav 05.04.15: kind of a "hack" since init is only defined on the current state, hence here I temporarily
//        *change the current state but then reset it, which goes against the initial intent of freshEmptyState that
//        *it shouldn't have an effect on the current state since it assumes changing the current state and then resetting
//        *it doesn't change the end result */
//      c.restoreState(tmpExps)
//      val initStmt = if(init) { c.initState} else { Statements.EmptyStmt}
//      c.restoreState(curExps)
//      stmt ++ initStmt
//    }).flatten
//    (s, emptyState)
//  }

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

  override def getCopyState:StateSnapshot = {
    val currentCopy = new StateComponentMapping()
    val s = for (c <- components) yield {
                currentCopy.put(c, c.currentStateVars)
            }
    (currentCopy, usingOldState, treatOldAsCurrent)
  }
}
