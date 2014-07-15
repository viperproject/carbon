/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules.components

import viper.carbon.utility.PartialSort
import viper.carbon.modules.Module

/**
 * A trait to allow registering of components.

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
