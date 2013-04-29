package semper.carbon.modules.components

import semper.carbon.utility.PartialSort
import semper.carbon.modules.Module

/**
 * A trait to allow registering of components.
 *
 * @author Stefan Heule
 */
trait ComponentRegistry[C <: Component] {

  protected var _components: Seq[C] = Nil

  /** All currently registered components. */
  lazy val components: Seq[C] = {
    PartialSort.sort(_components, ordering).asInstanceOf[Seq[C]]
  }

  /** Register a new component. */
  def register(component: C, before: Seq[Any] = Nil, after: Seq[Any] = Nil) {
    _components = _components :+ component
    component.comesBefore = before
    component.comesAfter = after
  }

  /** The partial ordering of components based on before and after. */
  def ordering: PartialOrdering[Any] = new PartialOrdering[Any] {
    def tryCompare(x: Any, y: Any): Option[Int] = {
      if (x == y) Some(0)
      else if (lteq(x, y)) Some(-1)
      else if (lteq(y, x)) Some(1)
      else None
    }
    def lteq(x: Any, y: Any): Boolean = {
      if (x == y) return true
      if (!(x.isInstanceOf[Component] && y.isInstanceOf[Component])) return false
      val xc = x.asInstanceOf[Component]
      val yc = y.asInstanceOf[Component]
      if (xc.comesBefore.contains(yc)) return true
      if (yc.comesAfter.contains(xc)) return true
      false
    }
  }
}
