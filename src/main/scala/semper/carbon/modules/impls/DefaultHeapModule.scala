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
  import verifier.typeModule._

  def name = "Heap module"

  override def initialize() {
    verifier.stateModule.register(this)
  }

  private val fieldType = NamedType("Field", TypeVar("T"))
  private val heapTyp = NamedType("HeapType")
  private var heap: LocalVar = null
  override def refType = NamedType("ref")

  override def preamble = {
    TypeDecl(refType) ::
      TypeDecl(fieldType) ::
      TypeAlias(heapTyp, MapType(Seq(refType, fieldType), TypeVar("T"), Seq(TypeVar("T")))) ::
      Nil
  }

  override def translateField(f: sil.Field) = {
    Const(f.name, NamedType("Field", translateType(f.typ)))
  }

  def initState: Stmt = {
    heap = env.define("Heap", heapTyp)
    Havoc(heap)
  }
  def stateContributions: Seq[LocalVarDecl] = Seq(LocalVarDecl("Heap", heapTyp))
  def currentStateContributions: Seq[Exp] = Seq(heap)
}
