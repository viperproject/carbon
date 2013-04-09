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

  import verifier._
  import typeModule._
  import expModule._
  import stateModule._

  def name = "Heap module"
  implicit val heapNamespace = verifier.freshNamespace("heap")
  val fieldNamespace = verifier.freshNamespace("heap.fields")
  // a fresh namespace for every axiom
  def axiomNamespace = verifier.freshNamespace("heap.axiom")

  override def initialize() {
    verifier.stateModule.register(this)
    verifier.stmtModule.register(this)
  }

  private val fieldTypeName = "Field"
  private def fieldTypeOf(t: Type) = NamedType(fieldTypeName, t)
  override def fieldType = NamedType(fieldTypeName, TypeVar("T"))
  private val heapTyp = NamedType("HeapType")
  private val heapName = Identifier("Heap")
  private var heap: Var = GlobalVar(heapName, heapTyp)
  private val nullName = Identifier("null")
  private val nullLit = Const(nullName)
  private val freshObjectName = Identifier("freshObj")
  private val freshObjectVar = LocalVar(freshObjectName, refType)
  private val allocName = Identifier("$allocated")(fieldNamespace)
  override def refType = NamedType("Ref")

  override def preamble = {
    val obj = LocalVarDecl(Identifier("o")(axiomNamespace), refType)
    val field = LocalVarDecl(Identifier("f")(axiomNamespace), fieldTypeOf(refType))
    val obj_field = lookup(LocalVar(heapName, heapTyp), obj.l, field.l)
    TypeDecl(refType) ::
      GlobalVarDecl(heapName, heapTyp) ::
      ConstDecl(nullName, refType) ::
      TypeDecl(fieldType) ::
      TypeAlias(heapTyp, MapType(Seq(refType, fieldType), TypeVar("T"), Seq(TypeVar("T")))) ::
      ConstDecl(allocName, NamedType(fieldTypeName, Bool), unique = true) ::
      // all heap-lookups yield allocated objects or null
      Axiom(Forall(
        obj ++
          field ++
          stateModule.stateContributions,
        Trigger(Seq(staticGoodState, obj_field)),
        obj_field === nullLit || alloc(obj_field))) ::
      Nil
  }

  override def translateField(f: sil.Field) = {
    ConstDecl(fieldIdentifier(f), NamedType(fieldTypeName, translateType(f.typ)), unique = true)
  }

  /** Return the identifier corresponding to a SIL field. */
  private def fieldIdentifier(f: sil.Field): Identifier = {
    Identifier(f.name)(fieldNamespace)
  }

  /** Returns a heap-lookup of the allocated field of an object. */
  private def alloc(o: Exp) = lookup(heap, o, Const(allocName))

  /** Returns a heap-lookup for o.f in a given heap h. */
  private def lookup(h: Exp, o: Exp, f: Exp) = MapSelect(h, Seq(o, f))

  override def translateFieldAccess(f: sil.FieldAccess): Exp = {
    MapSelect(heap, Seq(translateExp(f.rcv), Const(fieldIdentifier(f.field))))
  }

  override def handleStmt(stmt: sil.Stmt): Stmt = {
    stmt match {
      case sil.FieldAssign(lhs, rhs) =>
        translateFieldAccess(lhs) := translateExp(rhs)
      case sil.NewStmt(target) =>
        Havoc(freshObjectVar) ::
          // assume the fresh object is non-null and not allocated yet.
          // this means that whenever we allocate a new object and havoc freshObjectVar, we
          // assume that we consider a newly allocated cell, which gives the prover
          // the information that this object is different from anything allocated
          // earlier.
          Assume(freshObjectVar !== nullLit && alloc(freshObjectVar).not) ::
          (alloc(freshObjectVar) := TrueLit()) ::
          (translateExp(target) := freshObjectVar) ::
          Nil
      case sil.MethodCall(_, _, targets) =>
        targets filter (_.typ == sil.Ref) map translateExp map {
          t =>
            Assume(t === nullLit || alloc(t))
        }
      case _ => Statements.EmptyStmt
    }
  }

  override def whereClause(typ: sil.Type, variable: LocalVar): Option[Exp] = {
    typ match {
      case sil.Ref => Some(variable === nullLit || alloc(variable))
      case _ => None
    }
  }

  override def translateNull: Exp = nullLit

  def initState: Stmt = {
    Nil
  }

  def stateContributions: Seq[LocalVarDecl] = Seq(LocalVarDecl(heapName, heapTyp))
  def currentStateContributions: Seq[Exp] = Seq(heap)

  override type StateSnapshot = (Int, Var)
  private var curTmpStateId = -1

  override def freshTempState: (Stmt, StateSnapshot) = {
    curTmpStateId += 1
    val oldHeap = heap
    val tmpHeapName = if (curTmpStateId == 0) "tmpHeap" else s"tmpHeap$curTmpStateId"
    heap = LocalVar(Identifier(tmpHeapName), heapTyp)
    val s = Assign(heap, oldHeap)
    (s, (curTmpStateId, oldHeap))
  }

  override def throwAwayTempState(s: StateSnapshot): Stmt = {
    heap = s._2
    curTmpStateId = s._1 - 1
    Statements.EmptyStmt
  }
}
