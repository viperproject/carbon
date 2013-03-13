package semper.carbon.modules.impls

import semper.carbon.modules._
import components.StateComponent
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.boogie.Implicits._
import semper.carbon.verifier.Verifier

/**
 * The default implementation of a [[semper.carbon.modules.HeapModule]].
 *
 * @author Stefan Heule
 */
class DefaultHeapModule(val verifier: Verifier) extends HeapModule with StateComponent {
  def name = "Heap module"

  private val refTypeName = "ref"

  var heap: LocalVar = null

  override def refType = NamedType(refTypeName)

  override def preamble = {
    TypeDecl(refTypeName)
  }

  def initState: Stmt = Havoc(heap)
  def stateContributions: Seq[LocalVarDecl] = Seq(LocalVarDecl(heap.name, heap.typ))
  def currentStateContributions: Seq[Exp] = Seq(heap)
}
