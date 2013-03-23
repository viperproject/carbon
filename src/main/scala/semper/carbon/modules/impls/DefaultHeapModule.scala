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

  import verifier.typeModule._

  def name = "Heap module"
  implicit val heapNamespace = verifier.freshNamespace("heap")
  val fieldNamespace = verifier.freshNamespace("heap.fields")

  override def initialize() {
    verifier.stateModule.register(this)
  }

  private val fieldTypeName = "Field"
  private val fieldType = NamedType(fieldTypeName, TypeVar("T"))
  private val heapTyp = NamedType("HeapType")
  private val heapName = "Heap"
  private var heap: LocalVar = null
  override def refType = NamedType("ref")

  override def preamble = {
    TypeDecl(refType) ::
      TypeDecl(fieldType) ::
      TypeAlias(heapTyp, MapType(Seq(refType, fieldType), TypeVar("T"), Seq(TypeVar("T")))) ::
      Nil
  }

  override def translateField(f: sil.Field) = {
    Const(Identifier(f.name)(fieldNamespace), NamedType(fieldTypeName, translateType(f.typ)))
  }

  def initState: Stmt = {
    heap = LocalVar(Identifier(heapName), heapTyp)
    Havoc(heap)
  }
  def stateContributions: Seq[LocalVarDecl] = Seq(LocalVarDecl(Identifier(heapName), heapTyp))
  def currentStateContributions: Seq[Exp] = Seq(heap)
}
