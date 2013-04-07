package semper.carbon.modules

import components.{StateComponent, ComponentRegistry}
import semper.sil.{ast => sil}
import semper.carbon.boogie.{Exp, Stmt}

/**
 * A module for dealing with the state of a program during execution.  Allows other modules
 * to register [[semper.carbon.modules.components.StateComponent]]s that contribute to the
 * state.
 *
 * This module is itself a [[semper.carbon.modules.components.StateComponent]] that just
 * aggregates all the registered components.
 *
 * @author Stefan Heule
 */
trait StateModule extends Module with StateComponent with ComponentRegistry[StateComponent] {

  /**
   * Returns an assumption that the current state is 'good', or well-formed.
   */
  def assumeGoodState: Stmt

  /**
   * Returns a static invocation of the 'is good state' function with the arguments from
   * `stateContributions`.
   */
  def staticGoodState: Exp
}
