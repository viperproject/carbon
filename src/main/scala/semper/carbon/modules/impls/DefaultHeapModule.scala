package semper.carbon.modules.impls

import semper.carbon.modules._
import semper.carbon.modules.components.{SimpleStmtComponent, DefinednessComponent}
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.boogie.Implicits._
import semper.carbon.verifier.Verifier
import semper.sil.verifier.{reasons, PartialVerificationError}

/**
 * The default implementation of a [[semper.carbon.modules.HeapModule]].
 *
 * @author Stefan Heule
 */
class DefaultHeapModule(val verifier: Verifier) extends HeapModule with SimpleStmtComponent with DefinednessComponent {

  import verifier._
  import typeModule._
  import expModule._
  import stateModule._
  import permModule._

  def name = "Heap module"
  implicit val heapNamespace = verifier.freshNamespace("heap")
  val fieldNamespace = verifier.freshNamespace("heap.fields")
  // a fresh namespace for every axiom
  def axiomNamespace = verifier.freshNamespace("heap.axiom")

  override def initialize() {
    stateModule.register(this)
    stmtModule.register(this, before = Seq(verifier.permModule))
    expModule.register(this)
  }

  private val fieldTypeName = "Field"
  override def fieldTypeOf(t: Type) = NamedType(fieldTypeName, t)
  override def fieldType = NamedType(fieldTypeName, TypeVar("T"))
  private val heapTyp = NamedType("HeapType")
  private val heapName = Identifier("Heap")
  private val exhaleHeapName = Identifier("ExhaleHeap")
  private val exhaleHeap = LocalVar(exhaleHeapName, heapTyp)
  private var heap: Exp = GlobalVar(heapName, heapTyp)
  private val nullName = Identifier("null")
  private val nullLit = Const(nullName)
  private val freshObjectName = Identifier("freshObj")
  private val freshObjectVar = LocalVar(freshObjectName, refType)
  private val allocName = Identifier("$allocated")(fieldNamespace)
  private val identicalOnKnownLocsName = Identifier("IdenticalOnKnownLocations")
  private val isPredicateFieldName = Identifier("IsPredicateField")
  override def refType = NamedType("Ref")

  override def preamble = {
    val obj = LocalVarDecl(Identifier("o")(axiomNamespace), refType)
    val refField = LocalVarDecl(Identifier("f")(axiomNamespace), fieldTypeOf(refType))
    val obj_refField = lookup(LocalVar(heapName, heapTyp), obj.l, refField.l)
    val field = LocalVarDecl(Identifier("f")(axiomNamespace), fieldType)
    TypeDecl(refType) ++
      GlobalVarDecl(heapName, heapTyp) ++
      ConstDecl(nullName, refType) ++
      TypeDecl(fieldType) ++
      TypeAlias(heapTyp, MapType(Seq(refType, fieldType), TypeVar("T"), Seq(TypeVar("T")))) ++
      ConstDecl(allocName, NamedType(fieldTypeName, Bool), unique = true) ++
      // all heap-lookups yield allocated objects or null
      Axiom(Forall(
        obj ++
          refField ++
          stateModule.stateContributions,
        Trigger(Seq(staticGoodState, obj_refField)),
        validReference(obj_refField))) ++
      Func(identicalOnKnownLocsName,
        Seq(LocalVarDecl(heapName, heapTyp), LocalVarDecl(exhaleHeapName, heapTyp)) ++ staticMask,
        Bool) ++
      Func(isPredicateFieldName,
        Seq(LocalVarDecl(Identifier("f"), fieldType)),
        Bool) ++ {
      val h = LocalVarDecl(heapName, heapTyp)
      val eh = LocalVarDecl(exhaleHeapName, heapTyp)
      val vars = Seq(h, eh) ++ staticMask
      val identicalFuncApp = FuncApp(identicalOnKnownLocsName, vars map (_.l), Bool)
      Axiom(Forall(
        vars ++ Seq(obj, field),
        Trigger(Seq(identicalFuncApp, lookup(h.l, obj.l, field.l))) ++
          Trigger(Seq(identicalFuncApp, lookup(eh.l, obj.l, field.l))),
        identicalFuncApp ==>
          staticPermissionPositive(obj.l, field.l) ==>
          (lookup(h.l, obj.l, field.l) === lookup(eh.l, obj.l, field.l))
      )
      )
    }
  }

  override def isPredicateField(f: Exp): Exp = {
    FuncApp(isPredicateFieldName, Seq(f), Bool)
  }

  override def translateField(f: sil.Field) = {
    val field = locationIdentifier(f)
    ConstDecl(field, NamedType(fieldTypeName, translateType(f.typ)), unique = true) ++
      Axiom(UnExp(Not, isPredicateField(Const(field))))
  }

  override def predicateGhostFieldDecl(f: sil.Predicate): Seq[Decl] = {
    val predicate = locationIdentifier(f)
    val pmField = predicateMaskIdentifer(f)
    ConstDecl(predicate, NamedType(fieldTypeName, Int), unique = true) ++
      ConstDecl(pmField, NamedType(fieldTypeName, pmaskType), unique = true) ++
      Axiom(predicateMaskField(Const(predicate)) === Const(pmField)) ++
      Axiom(isPredicateField(Const(predicate))) ++
      Func(predicateTriggerIdentifer(f), Seq(LocalVarDecl(Identifier("this"), refType)), Bool)
  }

  /** Return the identifier corresponding to a SIL location. */
  private def locationIdentifier(f: sil.Location): Identifier = {
    Identifier(f.name)(fieldNamespace)
  }

  private def predicateMaskIdentifer(f: sil.Location): Identifier = {
    Identifier(f.name + "#sm")(fieldNamespace)
  }

  private def predicateTriggerIdentifer(f: sil.Location): Identifier = {
    Identifier(f.name + "#trigger")(fieldNamespace)
  }

  /** Returns a heap-lookup of the allocated field of an object. */
  private def alloc(o: Exp) = lookup(heap, o, Const(allocName))

  /** Returns a heap-lookup for o.f in a given heap h. */
  private def lookup(h: Exp, o: Exp, f: Exp) = MapSelect(h, Seq(o, f))

  override def translateFieldAccess(f: sil.FieldAccess): Exp = {
    MapSelect(heap, Seq(translateExp(f.rcv), locationMaskIndex(f)))
  }

  override def locationMaskIndex(l: sil.LocationAccess): Const = {
    Const(locationIdentifier(l.loc))
  }

  override def simpleHandleStmt(stmt: sil.Stmt): Stmt = {
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
          Assume((freshObjectVar !== nullLit) && alloc(freshObjectVar).not) ::
          (alloc(freshObjectVar) := TrueLit()) ::
          (translateExp(target) := freshObjectVar) ::
          Nil
      case sil.MethodCall(_, _, targets) =>
        targets filter (_.typ == sil.Ref) map translateExp map {
          t =>
            Assume(validReference(t))
        }
      case _ => Statements.EmptyStmt
    }
  }

  override def assumptionAboutParameter(typ: sil.Type, variable: LocalVar): Option[Exp] = {
    typ match {
      case sil.Ref => Some(validReference(variable))
      case _ => None
    }
  }

  private def validReference(exp: Exp): Exp = {
    exp === nullLit || alloc(exp)
  }

  override def translateNull: Exp = nullLit

  def initState: Stmt = {
    Nil
  }
  def initOldState: Stmt = {
    Assume(Old(heap) === heap)
  }

  def stateContributions: Seq[LocalVarDecl] = Seq(LocalVarDecl(heapName, heapTyp))
  def currentState: Seq[Exp] = Seq(heap)

  override def freshTempState(name: String): Seq[Exp] = {
    Seq(LocalVar(Identifier(s"${name}Heap"), heapTyp))
  }

  override def restoreState(s: Seq[Exp]) {
    heap = s(0)
  }

  private var allowHeapDeref = false
  override def simplePartialCheckDefinedness(e: sil.Exp, error: PartialVerificationError): Stmt = {
    e match {
      case sil.AccessPredicate(loc, perm) =>
        allowHeapDeref = true
        Nil
      case fa@sil.LocationAccess(rcv, field) =>
        if (allowHeapDeref) {
          allowHeapDeref = false
          Nil
        } else {
          Assert(translateExp(rcv) !== nullLit, error.dueTo(reasons.ReceiverNull(fa)))
        }
      case _ => Nil
    }
  }

  override def beginExhale: Stmt = {
    Havoc(exhaleHeap)
  }

  override def endExhale: Stmt = {
    Assume(FuncApp(identicalOnKnownLocsName, Seq(heap, exhaleHeap) ++ currentMask, Bool)) ++
      (heap := exhaleHeap)
  }
}
