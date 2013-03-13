package semper.carbon.modules.components

/**
 * A trait to allow registering of components.
 *
 * @author Stefan Heule
 */
trait ComponentRegistry[C <: Component] {

  protected var _components: Seq[C] = Nil

  /** All currently registered components. */
  def components: Seq[C] = _components

  /** Register a new component. */
  def register(component: C) {
    _components = _components :+ component
  }
}
