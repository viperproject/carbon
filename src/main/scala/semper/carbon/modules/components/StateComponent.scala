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
  def currentStateContributions: Seq[Exp]

  type StateSnapshot

  /**
   * Set up a fresh temporary state (no need to initialize it yet) and return enough
   * information such that the previous state can be restored later.
   */
  def freshTempState: (Stmt, StateSnapshot)

  /**
   * Throw away the current (temporary) state and go back to the previous state.
   */
  def throwAwayTempState(previousState: StateSnapshot): Stmt
}
