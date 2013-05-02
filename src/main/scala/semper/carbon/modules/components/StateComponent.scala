package semper.carbon.modules.components

import semper.carbon.boogie.{Exp, LocalVarDecl, Stmt}

/**
 * The [[semper.carbon.modules.StateModule]] allows to register state components that
 * contribute to the state of the execution of the program.  In the rest of this class,
 * we use 'state' to refer to the program state during execution.
 *
 * @author Stefan Heule
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
  def freshTempState: Seq[Exp]

  /**
   * Throw away the current state and go back to a snapshot.
   */
  def restoreState(previousState: Seq[Exp])
}
