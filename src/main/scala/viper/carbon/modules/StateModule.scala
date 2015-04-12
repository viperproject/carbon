/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules

import components.{StateComponent, ComponentRegistry}
import viper.silver.{ast => sil}
import viper.carbon.boogie.{LocalVarDecl, Exp, Stmt}

/**
 * A module for dealing with the state of a program during execution.  Allows other modules
 * to register [[viper.carbon.modules.components.StateComponent]]s that contribute to the
 * state.

 */
trait StateModule extends Module with ComponentRegistry[StateComponent] {

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
   * The statements necessary to initialize the part of the state belonging to this module.
   */
  def initState: Stmt

  /**
   * The statements necessary to initialize old(state).
   */
  def initOldState: Stmt

  /**
   * The name and type of the contribution of this components to the state.
   */
  def stateContributions: Seq[LocalVarDecl]

  /**
   * The current values for this components state contributions.  The number of elements
   * in the list and the types must correspond to the ones given in `stateContributions`.
   */
  def currentStateContributions: Seq[Exp]

  type StateSnapshot

  /**
   * Backup the current state and return enough information such that it can
   * be restored again at a later point.
   */
  def freshTempState(name: String): (Stmt, StateSnapshot)

  /**
   * Create a state without any information and return a snapshot of the created state.
   * if init is true then the Stmt returned will contain the initialization according to the state
   * components
   * Note: the current state is not affected by this in contrast to "freshTempState"
   */
  def freshEmptyState(name: String,init:Boolean): (Stmt, StateSnapshot)

  /**
   * Restore the state to a given snapshot.
   */
  def restoreState(snapshot: StateSnapshot)

  /**
   * Get the current old state.
   */
  def oldState: StateSnapshot

  /**
   * Restore the old state to a given snapshot.
   */
  def restoreOldState(snapshot: StateSnapshot)

  /**
   * Get the current state.
   */
  def state: StateSnapshot

  /**
   * Get a copy of the current state's snapshot. Should guarantee that if the current state changes then the
   * returned copy is not affected.
   * Gaurav: I think "def state" should do this, since it doesn't make sense to me that the client sees updates of
   * the current state without making additional queries.
   */
  def getCopyState:StateSnapshot

  /**
   * Change the state for all state components to the old state.
   */
  def useOldState()

  /**
   * Change the state for all state components to the regular (non-old) state.
   */
  def useRegularState()

  /**
   * Are we currently using the 'old' state?
   */
  def isUsingOldState: Boolean
}
