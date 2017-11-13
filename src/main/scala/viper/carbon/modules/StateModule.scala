/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules

import components.{CarbonStateComponent, ComponentRegistry}
import viper.silver.components.StatefulComponent
import viper.silver.{ast => sil}
import viper.carbon.boogie.{LocalVarDecl, Exp, Stmt}

/**
 * A module for dealing with the state of a program during execution.  Allows other modules
 * to register [[viper.carbon.modules.components.CarbonStateComponent]]s that contribute to the
 * state.

 */
trait StateModule extends Module with ComponentRegistry[CarbonStateComponent] with StatefulComponent {

  /**
   * Returns an assumption that the current state is 'good', or well-formed.
   */
  def assumeGoodState: Stmt

  /**
   * Returns a static invocation of the 'is good state' function with the arguments from
   * `stateContributions`.
   */
  def staticGoodState: Exp

  /**
   * Returns invocation of the 'is good state' function with the arguments from
   * `currentStateContributions`.
   */
  def currentGoodState: Exp

  /**
   * The statements necessary to initialize the Boogie state of all CarbonStateComponent modules.
   * This will also set the variable names used in the current state to the initial ones.
   */
  def initBoogieState: Stmt

  /**
   * The statements necessary to reset the Boogie state of all CarbonStateComponent modules.
   * Note that this should modify the *current* state (i.e. reassign all Boogie state in use), not create a fresh state
   */
  def resetBoogieState: Stmt

  def reset() = {initBoogieState; initOldState} // make the call to reset all Boogie state (e.g. variable names) - the latter call is probably not necessary, since it always gets called before relevant, but the former can affect the translation of many features (e.g. axioms)

  /**
   * The statements necessary to initialize old(state).
   */
  def initOldState: Stmt

  /**
   * The name and type of the static contribution of the state components registered with this module to the state. The returned value should remain the
   * same even if the state is changed.
   */
  def staticStateContributions: Seq[LocalVarDecl]

/* ALEX: It seems this function should be deprecated from the interface - it was never used anywhere!
  /**
   *
   * The name and type of the current contribution of the state components associated with this module to the state.
   */
  def currentStateContributions: Seq[LocalVarDecl] = stateContributions(state)

  def stateContributions(snap : StateSnapshot): Seq[LocalVarDecl]
*/

  /**
   * The current values for all registered components' state contributions.  The number of elements
   * in the list and the types must correspond to the ones given in `stateContributions`.
    *
    * Compared to the currentStateContributions [ALEX: maybe to be deprecated], these expressions may include e.g. old(..) around a heap variable.
   */
  def currentStateContributionValues: Seq[Exp] = stateContributionValues(state)

  def stateContributionValues(snap : StateSnapshot): Seq[Exp]

  type StateSnapshot// used to abstractly capture the Boogie variables, old expressions etc. used to represent a current state in the translation

  /**
   * Backup the current state and return enough information such that it can
   * be restored again at a later point.
   *
   * Replace the current state with a version named after the provided String (the returned Stmt includes the necessary setup code)
   * The returned state is the *previous* state (useful for restoring this later)
    *
    * This code is typically used in the following pattern:
    *   val tmpStateName = // choose some name
    *   val (stmt, state) = stateModule.freshTempState(tmpStateName)
    *   val resultingStatements = stmt ++ // something which generates a statement with respect to the temp state
    *   stateModule.replaceState(state) // go back to the original state
    *
    *
   */
  def freshTempState(name: String, discardCurrent: Boolean = false, initialise: Boolean = false): (Stmt, StateSnapshot)

  /**
   * Create a state without any information and return a snapshot of the created state.
   * if init is true then the Stmt returned will contain the initialization according to the state
   * components
   * Note: the current state is not affected by this in contrast to "freshTempState"
   *
   * ALEX: to get rid of - this seems redundant
   */
  def freshEmptyState(name: String,init:Boolean): (Stmt, StateSnapshot)

  /**
   * Restore the state to a given snapshot.
   */
  def replaceState(snapshot: StateSnapshot)

  /**
   * Get the current old state.
   */
  def oldState: StateSnapshot

  /**
   * Replace the old state with a given snapshot.
   */
  def replaceOldState(snapshot: StateSnapshot)

  def setTreatOldAsCurrentState(b: Boolean)

  /**
   * Get the current state.
   */
  def state: StateSnapshot

  /**
   * Get a copy of the current state's snapshot. Should guarantee that if the current state changes then the
   * returned copy is not affected.
   * Gaurav: I think "def state" should do this, since it doesn't make sense to me that the client sees updates of
   * the current state without making additional queries.
    * ALEX: I agree, and in practice it does do this, I believe - the underlying map is reassigned before any updates, and the "state" method just returns an alias of this map.
    * We could try refactoring this to just be one method (I'm not sure whether the explicit copy is necessary or not).
    */
  def getCopyState:StateSnapshot

  /**
   * Are we currently using an 'old' state? Implies that we should wrap relevant state components in "Old"
   */
  def stateModuleIsUsingOldState: Boolean

  /**
   * * Store a StateSnapshot in a retrievable map, with the given name as key
   * @param name the key to associate with this StateSnapshot
   * @param snapshot the StateSnapshot to store
   */
  def stateRepositoryPut(name:String, snapshot: StateSnapshot)

  /*
   * Analogous get operation to the put above.
   */
  def stateRepositoryGet(name:String) : Option[StateSnapshot]
}

