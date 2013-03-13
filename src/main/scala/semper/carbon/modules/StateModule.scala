package semper.carbon.modules

import components.{StateComponent, ComponentRegistry}
import semper.sil.{ast => sil}

/**
 * A module for dealing with the state of a program during execution.  Allows other modules
 * to register [[semper.carbon.modules.components.StateComponent]]s that contribute to the
 * state.
 *
 * @author Stefan Heule
 */
trait StateModule extends Module with ComponentRegistry[StateComponent] {

}
