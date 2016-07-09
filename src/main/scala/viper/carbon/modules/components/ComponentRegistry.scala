/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules.components

import viper.carbon.utility.PartialSort
import viper.carbon.modules.Module

import scala.collection.mutable

/**
 * A trait to allow registering of components.

 */
trait ComponentRegistry[C <: Component] {

   var _components: Seq[C] = Nil
   val beforePairs: mutable.HashSet[(Component,Component)] = mutable.HashSet.empty[(Component,Component)]

  /** All currently registered components. */
  /** NOTE: this should only be called once all components have been added! */
  lazy val components: Seq[C] = {
    // complete transitive closure of beforePairs (Warshall's algorithm)
    for(c <- _components) {
      for (x <- _components; y <- _components if x != c && y != c && beforePairs.contains(x,c) && beforePairs.contains(c,y)) {
        beforePairs.add((x,y))
      }
    }
    PartialSort.sort(_components, ordering)
  }

  /** Register a new component. */
  def register(component: C, before: Seq[Component] = Nil, after: Seq[Component] = Nil) {
    _components = _components :+ component
    beforePairs.add(component,component)
    for(c <- before) beforePairs.add((c,component))
    for(c <- after) beforePairs.add((component,c))
  }

  /** The partial ordering of components based on before and after. */
  def ordering: PartialOrdering[C] = new PartialOrdering[C] {
    def tryCompare(x: C, y: C): Option[Int] = {
      if (x == y) Some(0)
      else if (lteq(x, y)) (if (lteq(y,x)) sys.error("Internal Error: Carbon modules are incorrectly configured - module " + x.toString + " is in cyclic ordering with module " + y.toString + "\n" + "The complete ordering was: " + beforePairs.toString) else Some(-1))
      else if (lteq(y, x)) Some(1)
      else None
    }
    def lteq(x: C, y: C): Boolean = {
      if (x == y) return true
      if (beforePairs.contains((x,y))) (if(beforePairs.contains((y,x))) sys.error("Internal Error: Carbon modules are incorrectly configured - module " + x.toString + " is in cyclic ordering with module " + y.toString + "\n" + "The complete ordering was: " + beforePairs.toString) else return true)
      false
    }
  }
}
