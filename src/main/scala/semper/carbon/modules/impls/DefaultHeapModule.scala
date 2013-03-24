package semper.carbon.modules.impls

import semper.carbon.modules._
import components.{StmtComponent, StateComponent}
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.boogie.Implicits._
import semper.carbon.verifier.Verifier

/**
 * The default implementation of a [[semper.carbon.modules.HeapModule]].
 *
 * @author Stefan Heule
 */
class DefaultHeapModule(val verifier: Verifier) extends HeapModule with StateComponent with StmtComponent {

  import verifier.typeModule._
  import verifier.expModule._

  def name = "Heap module"
  implicit val heapNamespace = verifier.freshNamespace("heap")
  val fieldNamespace = verifier.freshNamespace("heap.fields")

  override def initialize() {
    verifier.stateModule.register(this)
    verifier.stmtModule.register(this)
  }

  private val fieldTypeName = "Field"
  private val fieldType = NamedType(fieldTypeName, TypeVar("T"))
  private val selfName = Identifier("self")
  private val self = LocalVar(selfName, refType)
  private val heapTyp = NamedType("HeapType")
  private val heapName = Identifier("Heap")
  private var heap: LocalVar = null
  private val nullName = Identifier("null")
  private val nullLit = ConstUse(nullName)
  private val freshObjectVar = LocalVar(Identifier("freshObj"), refType)
  override def refType = NamedType("Ref")

  override def preamble = {
    TypeDecl(refType) ::
      Const(nullName, refType) ::
      TypeDecl(fieldType) ::
      TypeAlias(heapTyp, MapType(Seq(refType, fieldType), TypeVar("T"), Seq(TypeVar("T")))) ::
      Nil
  }

  override def translateField(f: sil.Field) = {
    Const(fieldIdentifier(f), NamedType(fieldTypeName, translateType(f.typ)), unique = true)
  }

  /** Return the identifier corresponding to a SIL field. */
  private def fieldIdentifier(f: sil.Field): Identifier = {
    Identifier(f.name)(fieldNamespace)
  }

  override def translateFieldAccess(f: sil.FieldAccess): Exp = {
    MapSelect(heap, Seq(translateExp(f.rcv), ConstUse(fieldIdentifier(f.field))))
  }

  override def handleStmt(stmt: sil.Stmt): Stmt = {
    stmt match {
      case sil.FieldAssign(lhs, rhs) =>
        translateFieldAccess(lhs) := translateExp(rhs)
      case sil.NewStmt(target) =>
        Havoc(freshObjectVar) ::
          Assume(freshObjectVar !== nullLit) ::
          (translateExp(target) := freshObjectVar) ::
          Nil
      case _ => Statements.EmptyStmt
    }
  }

  override def translateThis(): Exp = self

  def initState: Stmt = {
    heap = LocalVar(heapName, heapTyp)
    Havoc(heap)
  }
  def stateContributions: Seq[LocalVarDecl] = Seq(LocalVarDecl(heapName, heapTyp))
  def currentStateContributions: Seq[Exp] = Seq(heap)
}
