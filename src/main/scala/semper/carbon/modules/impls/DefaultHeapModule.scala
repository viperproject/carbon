package semper.carbon.modules.impls

import semper.carbon.modules._
import semper.carbon.modules.components.{InhaleComponent, ExhaleComponent, SimpleStmtComponent, DefinednessComponent}
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
class DefaultHeapModule(val verifier: Verifier) extends HeapModule with SimpleStmtComponent with DefinednessComponent with ExhaleComponent with InhaleComponent {

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
    exhaleModule.register(this)
    inhaleModule.register(this)
  }

  private val fieldTypeName = "Field"
  private val normalFieldTypeName = "NormalField"
  private val normalFieldType = NamedType(normalFieldTypeName)
  override def fieldTypeOf(t: Type) = NamedType(fieldTypeName, Seq(normalFieldType, t))
  override def fieldType = NamedType(fieldTypeName, Seq(TypeVar("A"), TypeVar("B")))
  override def predicateVersionFieldTypeOf(p: sil.Predicate) =
    NamedType(fieldTypeName, Seq(predicateMetaTypeOf(p), Int))
  private def predicateMetaTypeOf(p: sil.Predicate) = NamedType("PredicateType_" + p.name)
  override def predicateVersionFieldType(genericT: String = "A") =
    NamedType(fieldTypeName, Seq(TypeVar(genericT), Int))
  override def predicateMaskFieldType: Type =
    NamedType(fieldTypeName, Seq(TypeVar("A"), pmaskType))
  override def predicateMaskFieldTypeOf(p: sil.Predicate): Type =
    NamedType(fieldTypeName, Seq(predicateMetaTypeOf(p), pmaskType))
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
    val obj2 = LocalVarDecl(Identifier("o2")(axiomNamespace), refType)
    val refField = LocalVarDecl(Identifier("f")(axiomNamespace), fieldTypeOf(refType))
    val obj_refField = lookup(LocalVar(heapName, heapTyp), obj.l, refField.l)
    val field = LocalVarDecl(Identifier("f")(axiomNamespace), fieldType)
    val predField = LocalVarDecl(Identifier("pm_f")(axiomNamespace),
      predicateVersionFieldType("C"))
    TypeDecl(refType) ++
      GlobalVarDecl(heapName, heapTyp) ++
      ConstDecl(nullName, refType) ++
      TypeDecl(fieldType) ++
      TypeDecl(normalFieldType) ++
      TypeAlias(heapTyp, MapType(Seq(refType, fieldType), TypeVar("B"), Seq(TypeVar("A"), TypeVar("B")))) ++
      ConstDecl(allocName, NamedType(fieldTypeName, Seq(normalFieldType, Bool)), unique = true) ++
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
      // frame all locations with direct permission
      MaybeCommentedDecl("Frame all locations with direct permissions", Axiom(Forall(
        vars ++ Seq(obj, field),
        Trigger(Seq(identicalFuncApp, lookup(h.l, obj.l, field.l))) ++
          Trigger(Seq(identicalFuncApp, lookup(eh.l, obj.l, field.l))),
        identicalFuncApp ==>
          (staticPermissionPositive(obj.l, field.l) ==>
            (lookup(h.l, obj.l, field.l) === lookup(eh.l, obj.l, field.l)))
      )), size = 1) ++
        // frame all predicate masks
        MaybeCommentedDecl("Frame all predicate mask locations of predicates with direct permission", Axiom(Forall(
          vars ++ Seq(obj, predField),
          Trigger(Seq(identicalFuncApp, isPredicateField(predField.l), lookup(eh.l, obj.l, predicateMaskField(predField.l)))),
          identicalFuncApp ==>
            ((staticPermissionPositive(obj.l, predField.l) && isPredicateField(predField.l)) ==>
              (lookup(h.l, obj.l, predicateMaskField(predField.l)) === lookup(eh.l, obj.l, predicateMaskField(predField.l))))
        )), size = 1) ++
        // frame all locations with direct permission
        MaybeCommentedDecl("Frame all locations with known folded permissions", Axiom(Forall(
          vars ++ Seq(obj, predField),
          Trigger(Seq(identicalFuncApp, lookup(h.l, obj.l, predicateMaskField(predField.l)), isPredicateField(predField.l))) ++
            Trigger(Seq(identicalFuncApp, lookup(eh.l, obj.l, predicateMaskField(predField.l)), isPredicateField(predField.l))) ++
            (verifier.program.predicates map (pred =>
              Trigger(Seq(identicalFuncApp, predicateTrigger(pred, obj.l), isPredicateField(predField.l))))
              ),
          identicalFuncApp ==>
            (
              (staticPermissionPositive(obj.l, predField.l) && isPredicateField(predField.l)) ==>
                Forall(Seq(obj2, field),
                  Trigger(Seq(lookup(h.l, obj2.l, field.l))) ++
                    Trigger(Seq(lookup(eh.l, obj2.l, field.l))),
                  (lookup(lookup(h.l, obj.l, predicateMaskField(predField.l)), obj2.l, field.l) ==>
                    (lookup(h.l, obj2.l, field.l) === lookup(eh.l, obj2.l, field.l))),
                  field.typ.freeTypeVars
                )
              )
        )), size = 1)
    }
  }

  override def isPredicateField(f: Exp): Exp = {
    FuncApp(isPredicateFieldName, Seq(f), Bool)
  }

  override def translateField(f: sil.Field) = {
    val field = locationIdentifier(f)
    ConstDecl(field, NamedType(fieldTypeName, Seq(normalFieldType, translateType(f.typ))), unique = true) ++
      Axiom(UnExp(Not, isPredicateField(Const(field))))
  }

  override def predicateGhostFieldDecl(p: sil.Predicate): Seq[Decl] = {
    val predicate = locationIdentifier(p)
    val pmField = predicateMaskIdentifer(p)
    val t = predicateVersionFieldTypeOf(p)
    val pmT = predicateMaskFieldTypeOf(p)
    val varDecls = p.formalArgs.tail map mainModule.translateLocalVarDecl
    val vars = varDecls map (_.l)
    val f0 = FuncApp(predicate, vars, t)
    val f1 = predicateMaskField(f0)
    val f2 = FuncApp(pmField, vars, pmT)
    TypeDecl(predicateMetaTypeOf(p)) ++
      Func(predicate, varDecls, t) ++
      Func(pmField, varDecls, pmT) ++
      Axiom(MaybeForall(varDecls, Trigger(f1), f1 === f2)) ++
      Axiom(MaybeForall(varDecls, Trigger(f0), isPredicateField(f0))) ++
      Func(predicateTriggerIdentifer(p), Seq(LocalVarDecl(Identifier("this"), refType)), Bool) ++
      {
        // axiom that two predicate identifiers can only be the same, if all arguments
        // are the same (e.g., we immediatly know that valid(1) != valid(2))
        if (vars.size == 0) Nil
        else {
          val varDecls2 = varDecls map (
            v => LocalVarDecl(Identifier(v.name.name + "2")(v.name.namespace), v.typ))
          val vars2 = varDecls2 map (_.l)
          var varsEqual = All((vars zip vars2) map {
            case (v1, v2) => v1 === v2
          })
          val f0_2 = FuncApp(predicate, vars2, t)
          val f2_2 = FuncApp(pmField, vars2, t)
          Axiom(Forall(varDecls ++ varDecls2, Trigger(Seq(f0, f0_2)),
            (f0 === f0_2) ==> varsEqual)) ++
            Axiom(Forall(varDecls ++ varDecls2, Trigger(Seq(f2, f2_2)),
              (f2 === f2_2) ==> varsEqual))
        }
      }
  }

  /** Return the identifier corresponding to a SIL location. */
  private def locationIdentifier(f: sil.Location): Identifier = {
    Identifier(f.name)(fieldNamespace)
  }

  private def predicateMaskIdentifer(f: sil.Location): Identifier = {
    Identifier(f.name + "#sm")(fieldNamespace)
  }

  private def predicateMask(loc: sil.PredicateAccess) = {
    val t = predicateMaskFieldTypeOf(loc.predicate)
    MapSelect(heap, Seq(translateExp(loc.rcv),
      FuncApp(predicateMaskIdentifer(loc.predicate),
        loc.args.tail map translateExp, t)))
  }

  private def predicateTriggerIdentifer(f: sil.Location): Identifier = {
    Identifier(f.name + "#trigger")(fieldNamespace)
  }
  private def predicateTrigger(f: sil.Location, rcv: Exp): Exp = {
    FuncApp(predicateTriggerIdentifer(f), Seq(rcv), Bool)
  }
  override def predicateTrigger(pred: sil.PredicateAccess): Stmt = {
    Assume(FuncApp(predicateTriggerIdentifer(pred.predicate), Seq(translateExp(pred.rcv)), Bool))
  }

  /** Returns a heap-lookup of the allocated field of an object. */
  private def alloc(o: Exp) = lookup(heap, o, Const(allocName))

  /** Returns a heap-lookup for o.f in a given heap h. */
  private def lookup(h: Exp, o: Exp, f: Exp) = MapSelect(h, Seq(o, f))

  override def translateLocationAccess(f: sil.LocationAccess): Exp = {
    translateLocationAccess(f, heap)
  }
  private def translateLocationAccess(f: sil.LocationAccess, heap: Exp): Exp = {
    MapSelect(heap, Seq(translateExp(f.rcv), translateLocation(f)))
  }

  override def translateLocation(l: sil.LocationAccess): Exp = {
    l match {
      case sil.PredicateAccess(args, pred) =>
        val t = predicateMetaTypeOf(pred)
        FuncApp(locationIdentifier(pred), args.tail map translateExp, t)
      case sil.FieldAccess(rcv, field) =>
        Const(locationIdentifier(field))
    }
  }

  override def simpleHandleStmt(stmt: sil.Stmt): Stmt = {
    stmt match {
      case sil.FieldAssign(lhs, rhs) =>
        translateLocationAccess(lhs) := translateExp(rhs)
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
      case sil.Fold(sil.PredicateAccessPredicate(loc, perm)) =>
        val newVersion = LocalVar(Identifier("freshVersion"), Int)
        (predicateMask(loc) := zeroPMask) ++
          Havoc(newVersion) ++
          (translateLocationAccess(loc) := newVersion) ++
          addPermissionToPMask(loc)
      case _ => Statements.EmptyStmt
    }
  }

  override def freeAssumptions(e: sil.Exp): Stmt = {
    e match {
      case sil.Unfolding(sil.PredicateAccessPredicate(loc, perm), exp) if !isUsingOldState =>
        addPermissionToPMask(loc)
      case _ => Nil
    }
  }

  /**
   * Adds the permissions from an expression to a permission mask.
   */
  private def addPermissionToPMask(loc: sil.PredicateAccess): Stmt = {
    addPermissionToPMaskHelper(loc.predicateBody, predicateMask(loc))
  }
  private def addPermissionToPMaskHelper(e: sil.Exp, pmask: Exp): Stmt = {
    e match {
      case sil.FieldAccessPredicate(loc, perm) =>
        translateLocationAccess(loc, pmask) := TrueLit()
      case sil.PredicateAccessPredicate(loc, perm) =>
        val newPMask = LocalVar(Identifier("newPMask"), pmaskType)
        val obj = LocalVarDecl(Identifier("o")(axiomNamespace), refType)
        val field = LocalVarDecl(Identifier("f")(axiomNamespace), fieldType)
        val pm1 = MapSelect(pmask, Seq(obj.l, field.l))
        val pm2 = MapSelect(predicateMask(loc), Seq(obj.l, field.l))
        val pm3 = MapSelect(newPMask, Seq(obj.l, field.l))
        Havoc(newPMask) ++
          Assume(Forall(Seq(obj, field), Seq(Trigger(pm3)), (pm1 || pm2) ==> pm3)) ++
          (pmask := newPMask)
      case sil.And(e1, e2) =>
        addPermissionToPMaskHelper(e1, pmask) ::
          addPermissionToPMaskHelper(e2, pmask) ::
          Nil
      case sil.Implies(e1, e2) =>
        If(translateExp(e1), addPermissionToPMaskHelper(e2, pmask), Statements.EmptyStmt)
      case sil.CondExp(c, e1, e2) =>
        If(translateExp(c), addPermissionToPMaskHelper(e1, pmask), addPermissionToPMaskHelper(e2, pmask))
      case _ => Nil
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
    if (!isUsingOldState) Assume(FuncApp(identicalOnKnownLocsName, Seq(heap, exhaleHeap) ++ currentMask, Bool)) ++
      (heap := exhaleHeap)
    else Nil
  }

  override def exhaleExp(e: sil.Exp, error: PartialVerificationError): Stmt = {
    e match {
      case _ => Nil
    }
  }

  override def inhaleExp(e: sil.Exp): Stmt = {
    e match {
      case sil.Unfolding(sil.PredicateAccessPredicate(loc, perm), exp) =>
        addPermissionToPMask(loc)
      case _ => Nil
    }
  }
}
