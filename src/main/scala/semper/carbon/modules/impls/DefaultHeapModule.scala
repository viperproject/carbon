package semper.carbon.modules.impls

import semper.carbon.modules._
import semper.sil.{ast => sil}
import semper.carbon.boogie._

/**
 * The default implementation of a [[semper.carbon.modules.HeapModule]].
 *
 * @author Stefan Heule
 */
class DefaultHeapModule(val verifier: Verifier) extends HeapModule {
  def name = "Heap module"
}
