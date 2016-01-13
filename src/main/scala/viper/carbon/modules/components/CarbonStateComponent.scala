/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules.components

import viper.carbon.boogie._

/**
 * The [[viper.carbon.modules.StateModule]] allows to register state components that
 * contribute to the state of the execution of the program.  In the rest of this class,
 * we use 'state' to refer to the program state during execution.

 */
trait CarbonStateComponent extends Component {

  /**
   * The statements necessary to initialize the part of the state belonging to this module.
   */
  def initBoogieState: Stmt

  /**
   * The statements necessary to reset the part of the state belonging to this module.
   */
  def resetBoogieState: Stmt

  /**
   * The name and type of the static contribution of this component to the state. The returned value should remain the
   * same even if the state is changed.
   */
  def staticStateContributions: Seq[LocalVarDecl]


  /**
   * The name and type of the current contribution of this component to the state. The numbers of elements in the list and
   * the types must correspond to the ones given in `staticStateContributions`.
   */
  def currentStateContributions: Seq[LocalVarDecl]


  /**
   * The current values for this components state contributions.  The number of elements
   * in the list and the types must correspond to the ones given in `staticStateContributions`.
   *
   * NOTE: these variables may need wrapping in Old(.) when used, as according to usingOldState etc. To do this wrapping internally, call instead currentStateExps below
   */
  def currentStateVars: Seq[Var]

  /**
   * The current values for this components state contributions, adjusted for "old".  The number of elements
   * in the list and the types must correspond to the ones given in `stateContributions`.
   */
  def currentStateExps: Seq[Exp]

  /**
   * Set up a fresh temporary state and returns that new state.
   */
  def freshTempState(name: String): Seq[Var]

  /**
   * Throw away the current state and go back to a snapshot.
   */
  def restoreState(previousState: Seq[Var])

  /**
   * Are we currently using an "old" state? Note: this is mainly as documentation that the states passed to other methods above will need wrapping in "olD2 when *used*, if we are currently using an old state. This method would typically be implemented by querying the corresponding StateModule
   *
   * Note in particular that variable passed in via "replaceState" above will typically need wrapping in old(.) if this is set to true
   */
  def usingOldState: Boolean
}
