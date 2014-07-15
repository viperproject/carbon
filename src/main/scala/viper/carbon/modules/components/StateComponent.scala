/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules.components

import viper.carbon.boogie.{Exp, LocalVarDecl, Stmt}

/**
 * The [[viper.carbon.modules.StateModule]] allows to register state components that
 * contribute to the state of the execution of the program.  In the rest of this class,
 * we use 'state' to refer to the program state during execution.

 */
trait StateComponent extends Component {

  /**
   * The statements necessary to initialize the part of the state belonging to this module.
   */
  def initState: Stmt

  /**
   * The name and type of the contribution of this components to the state.
   */
  def stateContributions: Seq[LocalVarDecl]

  /**
   * The current values for this components state contributions.  The number of elements
   * in the list and the types must correspond to the ones given in `stateContributions`.
   */
  def currentState: Seq[Exp]

  /**
   * Set up a fresh temporary state and returns that new state.
   */
  def freshTempState(name: String): Seq[Exp]

  /**
   * Throw away the current state and go back to a snapshot.
   */
  def restoreState(previousState: Seq[Exp])
}
