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

  import verifier.mainModule._

  def name = "Heap module"

  override def initialize() {
    verifier.stateModule.register(this)
  }

  private val refTypeName = "ref"
  private val heapTyp = Bool
  private var heap: LocalVar = null

  override def refType = NamedType(refTypeName)

  override def preamble = {
    TypeDecl(refTypeName)
  }

  def initState: Stmt = {
    heap = env.define("Heap", heapTyp)
    Havoc(heap)
  }
  def stateContributions: Seq[LocalVarDecl] = Seq(LocalVarDecl("Heap", heapTyp))
  def currentStateContributions: Seq[Exp] = Seq(heap)
}
