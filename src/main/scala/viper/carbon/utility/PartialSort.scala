/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.utility

import org.jgrapht.graph.DefaultDirectedGraph
import viper.silver.ast.utility.Functions.{Edge, Factory}
import org.jgrapht.traverse.TopologicalOrderIterator
import scala.collection.mutable.ListBuffer

/**
 * A utility object for sorting based on a partial order.

 */
object PartialSort {

  /**
   * Returns a sequence with the same elements as `s`, but sorted according to a given partial order.
   */
  def sort[T](s: Seq[T], ordering: PartialOrdering[T]): Seq[T] = {
    val g = new DefaultDirectedGraph[T, Edge[T]](Factory[T]())
    for (e <- s) {
      g.addVertex(e)
    }
    for (e1 <- s; e2 <- s if e1 != e2) {
      if (ordering.lteq(e1, e2)) {
        g.addEdge(e1, e2)
      }
    }
    val topo = new TopologicalOrderIterator[T, Edge[T]](g)
    val res = ListBuffer[T]()
    while (topo.hasNext) {
      res += topo.next()
    }
    res.toSeq
  }
}
