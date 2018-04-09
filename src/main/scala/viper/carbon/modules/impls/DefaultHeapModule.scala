/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules.impls

import viper.carbon.modules._
import viper.carbon.modules.components.{DefinednessComponent, InhaleComponent, SimpleStmtComponent}
import viper.silver.ast.utility.Expressions
import viper.silver.components.StatefulComponent
import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.boogie.Implicits._
import viper.silver.verifier.{PartialVerificationError, reasons}
import viper.carbon.verifier.Verifier
import viper.silver.ast.NullLit
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion

/**
 * The default implementation of a [[viper.carbon.modules.HeapModule]].
 */
class DefaultHeapModule(val verifier: Verifier)
    extends HeapModule
    with SimpleStmtComponent
    with DefinednessComponent
    with InhaleComponent {

  import verifier._
  import typeModule._
  import expModule._
  import stateModule._
  import permModule._
  import mainModule._

  def name = "Heap module"
  implicit val heapNamespace = verifier.freshNamespace("heap")
  val fieldNamespace = verifier.freshNamespace("heap.fields")
  // a fresh namespace for every axiom
  def axiomNamespace = verifier.freshNamespace("heap.axiom")

  override def start() {
    stateModule.register(this)
    stmtModule.register(this)
    expModule.register(this)
    inhaleModule.register(this)
  }

  private val fieldTypeName = "Field"
  private val normalFieldTypeName = "NormalField"
  private val normalFieldType = NamedType(normalFieldTypeName)
  override def fieldTypeOf(t: Type) = NamedType(fieldTypeName, Seq(normalFieldType, t))
  override def fieldType = NamedType(fieldTypeName, Seq(TypeVar("A"), TypeVar("B")))
  override def predicateVersionFieldTypeOf(p: sil.Predicate) =
    NamedType(fieldTypeName, Seq(predicateMetaTypeOf(p), funcPredModule.predicateVersionType))
  private def predicateMetaTypeOf(p: sil.Predicate) = NamedType("PredicateType_" + p.name)
  override def predicateVersionFieldType(genericT: String = "A") =
    NamedType(fieldTypeName, Seq(TypeVar(genericT), funcPredModule.predicateVersionType))
  override def predicateMaskFieldType: Type =
    NamedType(fieldTypeName, Seq(TypeVar("A"), pmaskType))
  override def predicateMaskFieldTypeOf(p: sil.Predicate): Type =
    NamedType(fieldTypeName, Seq(predicateMetaTypeOf(p), pmaskType))
  override def wandBasicType(wand: String): Type = NamedType("WandType_" + wand)
  override def wandFieldType(wand: String) : Type = NamedType(fieldTypeName, Seq(wandBasicType(wand),Int))
  private val heapTyp = NamedType("HeapType")
  private val heapName = Identifier("Heap")
  private val exhaleHeapName = Identifier("ExhaleHeap")
  private val exhaleHeap = LocalVar(exhaleHeapName, heapTyp)
  private val originalHeap = GlobalVar(heapName, heapTyp)
  private val qpHeapName = Identifier("QPHeap")
  private val qpHeap = LocalVar(qpHeapName, heapTyp)
  private var heap: Var = originalHeap
  private def heapVar: Var = {assert (!usingOldState); heap}
  private def heapExp: Exp = (if (usingOldState) Old(heap) else heap)
  private val nullName = Identifier("null")
  private val nullLit = Const(nullName)
  private val freshObjectName = Identifier("freshObj")
  private val freshObjectVar = LocalVar(freshObjectName, refType)
  private val allocName = Identifier("$allocated")(fieldNamespace)
  private val identicalOnKnownLocsName = Identifier("IdenticalOnKnownLocations")
  private val isPredicateFieldName = Identifier("IsPredicateField")
  private var PredIdMap:Map[String, BigInt] = Map()
  private var NextPredicateId:BigInt = 0
  private val isWandFieldName = Identifier("IsWandField")
  private val getPredicateIdName = Identifier("getPredicateId")

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
      // Heap Type Definition :
      TypeAlias(heapTyp, MapType(Seq(refType, fieldType), TypeVar("B"), Seq(TypeVar("A"), TypeVar("B")))) ++
      ConstDecl(allocName, NamedType(fieldTypeName, Seq(normalFieldType, Bool)), unique = true) ++
      // all heap-lookups yield allocated objects or null
      Axiom(Forall(
        obj ++
          refField ++
          stateModule.staticStateContributions,
        Trigger(Seq(staticGoodState, obj_refField)),
        validReference(obj_refField))) ++
      Func(identicalOnKnownLocsName,
        Seq(LocalVarDecl(heapName, heapTyp), LocalVarDecl(exhaleHeapName, heapTyp)) ++ staticMask,
        Bool) ++
      Func(isPredicateFieldName,
        Seq(LocalVarDecl(Identifier("f"), fieldType)),
        Bool) ++
      Func(isWandFieldName,
        Seq(LocalVarDecl(Identifier("f"), fieldType)),
        Bool) ++
      Func(getPredicateIdName,
        Seq(LocalVarDecl(Identifier("f"), fieldType)),
        Int) ++ {
      val h = LocalVarDecl(heapName, heapTyp)
      val eh = LocalVarDecl(exhaleHeapName, heapTyp)
      val vars = Seq(h, eh) ++ staticMask
      val identicalFuncApp = FuncApp(identicalOnKnownLocsName, vars map (_.l), Bool)
      // frame all locations with direct permission
      MaybeCommentedDecl("Frame all locations with direct permissions", Axiom(Forall(
        vars ++ Seq(obj, field),
//        Trigger(Seq(identicalFuncApp, lookup(h.l, obj.l, field.l))) ++
          Trigger(Seq(identicalFuncApp, lookup(eh.l, obj.l, field.l))),
        identicalFuncApp ==>
          (staticPermissionPositive(obj.l, field.l) ==>
            (lookup(h.l, obj.l, field.l) === lookup(eh.l, obj.l, field.l)))
      )), size = 1) ++
        // frame all predicate masks
        MaybeCommentedDecl("Frame all predicate mask locations of predicates with direct permission", Axiom(Forall(
          vars ++ Seq(predField),
          Trigger(Seq(identicalFuncApp, isPredicateField(predField.l), lookup(eh.l, nullLit, predicateMaskField(predField.l)))),
          identicalFuncApp ==>
            ((staticPermissionPositive(nullLit, predField.l) && isPredicateField(predField.l)) ==>
              (lookup(h.l, nullLit, predicateMaskField(predField.l)) === lookup(eh.l, nullLit, predicateMaskField(predField.l))))
        )), size = 1) ++
        // frame all locations with direct permission
        MaybeCommentedDecl("Frame all locations with known folded permissions", Axiom(Forall(
          vars ++ Seq(predField),
          Trigger(Seq(identicalFuncApp, lookup(h.l, nullLit, predicateMaskField(predField.l)), isPredicateField(predField.l))) ++
            Trigger(Seq(identicalFuncApp, lookup(eh.l, nullLit, predicateMaskField(predField.l)), isPredicateField(predField.l))) ++
            (verifier.program.predicates map (pred =>
              Trigger(Seq(identicalFuncApp, predicateTriggerAnyState(pred, predField.l), isPredicateField(predField.l))))
              ),
          identicalFuncApp ==>
            (
              (staticPermissionPositive(nullLit, predField.l) && isPredicateField(predField.l)) ==>
                Forall(Seq(obj2, field),
                  Trigger(Seq(lookup(h.l, obj2.l, field.l))) ++
                    Trigger(Seq(lookup(eh.l, obj2.l, field.l))),
                  (lookup(lookup(h.l, nullLit, predicateMaskField(predField.l)), obj2.l, field.l) ==>
                    (lookup(h.l, obj2.l, field.l) === lookup(eh.l, obj2.l, field.l))),
                  field.typ.freeTypeVars
                )
              )
        )), size = 1)  ++
        // preserve "allocated" knowledge, where already true
        MaybeCommentedDecl("All previously-allocated references are still allocated", Axiom(Forall(
          vars ++ Seq(obj),
          Trigger(Seq(identicalFuncApp, lookup(h.l, obj.l, Const(allocName)))) ++
            Trigger(Seq(identicalFuncApp, lookup(eh.l, obj.l, Const(allocName)))),
          identicalFuncApp ==>
              (lookup(h.l, obj.l, Const(allocName)) ==> lookup(eh.l, obj.l, Const(allocName)))
        )), size = 1)
    }
  }

  override def isPredicateField(f: Exp): Exp = {
    FuncApp(isPredicateFieldName, Seq(f), Bool)
  }

  override def isWandField(f: Exp) : Exp = {
    FuncApp(isWandFieldName, Seq(f), Bool)
  }

  // returns predicate Id
  override def getPredicateId(f:Exp): Exp = {
    FuncApp(getPredicateIdName,Seq(f), Int)
  }

  override def getPredicateId(s:String): BigInt = {
    if (!PredIdMap.contains(s)) {
      val predId:BigInt = getNewPredId;
      PredIdMap += (s -> predId)
    }
    PredIdMap(s)
  }

  def getNewPredId : BigInt = {
    val id = NextPredicateId
    NextPredicateId = NextPredicateId + 1
    id
  }

  override def translateField(f: sil.Field) = {
    val field = locationIdentifier(f)
    ConstDecl(field, NamedType(fieldTypeName, Seq(normalFieldType, translateType(f.typ))), unique = true) ++
      Axiom(UnExp(Not, isPredicateField(Const(field)))) ++
      Axiom(UnExp(Not, isWandField(Const(field))))
  }


// AS: Seems that many concerns here would be better addressed in / delegated to the FuncPredModule
  override def predicateGhostFieldDecl(p: sil.Predicate): Seq[Decl] = {
    val predicate = locationIdentifier(p)
    val pmField = predicateMaskIdentifer(p)
    val t = predicateVersionFieldTypeOf(p)
    val pmT = predicateMaskFieldTypeOf(p)
    val varDecls = p.formalArgs map mainModule.translateLocalVarDecl
    val vars = varDecls map (_.l)
    val predId:BigInt = getPredicateId(p.name)
    val f0 = FuncApp(predicate, vars, t)
    val f1 = predicateMaskField(f0)
    val f2 = FuncApp(pmField, vars, pmT)
    TypeDecl(predicateMetaTypeOf(p)) ++
      Func(predicate, varDecls, t) ++
      Func(pmField, varDecls, pmT) ++
      Axiom(MaybeForall(varDecls, Trigger(f1), f1 === f2)) ++
      Axiom(MaybeForall(varDecls, Trigger(f0), isPredicateField(f0))) ++
      Axiom(MaybeForall(varDecls, Trigger(f0), getPredicateId(f0) === IntLit(predId))) ++
      Func(predicateTriggerIdentifier(p), Seq(LocalVarDecl(heapName, heapTyp), LocalVarDecl(Identifier("pred"), predicateVersionFieldType())), Bool) ++
      Func(predicateTriggerAnyStateIdentifier(p), Seq(LocalVarDecl(Identifier("pred"), predicateVersionFieldType())), Bool) ++
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

  /** Return the identifier corresponding to a Viper location. */
  private def locationIdentifier(f: sil.Location): Identifier = {
    Identifier(f.name)(fieldNamespace)
  }

  private def predicateMaskIdentifer(f: sil.Location): Identifier = {
    Identifier(f.name + "#sm")(fieldNamespace)
  }

  private def predicateMask(loc: sil.PredicateAccess):Exp = {
    predicateMask(loc, heap)
  }

  private def predicateMask(loc: sil.PredicateAccess, heap: Exp) = {
    val predicate = verifier.program.findPredicate(loc.predicateName)
    val t = predicateMaskFieldTypeOf(predicate)
    MapSelect(heapExp, Seq(nullLit,
      FuncApp(predicateMaskIdentifer(predicate),
        loc.args map translateExp, t)))
  }

  private def predicateTriggerIdentifier(f: sil.Predicate): Identifier = {
    Identifier(f.name + "#trigger")(fieldNamespace)
  }
  private def predicateTriggerAnyStateIdentifier(f: sil.Predicate): Identifier = {
    Identifier(f.name + "#everUsed")(fieldNamespace)
  }
  private def predicateTrigger(extras : Seq[Exp], predicate: sil.Predicate, predicateField: Exp): Exp = {
    FuncApp(predicateTriggerIdentifier(predicate), extras ++ Seq(predicateField), Bool)
  }
  private def predicateTriggerAnyState( predicate: sil.Predicate, predicateField: Exp): Exp = {
    FuncApp(predicateTriggerAnyStateIdentifier(predicate), Seq(predicateField), Bool)
  }
  override def predicateTrigger(extras : Seq[Exp], pred: sil.PredicateAccess, anyState : Boolean = false): Exp = {
    val predicate = verifier.program.findPredicate(pred.predicateName)
    val location = translateLocation(pred)
    if (anyState) predicateTriggerAnyState(predicate, location) else predicateTrigger(extras, predicate, location)
  }

  /** Returns a heap-lookup of the allocated field of an object. */
  /** (should only be used for known-non-null references) */
  private def alloc(o: Exp) = lookup(heapExp, o, Const(allocName))

  /** Returns a heap-lookup for o.f in a given heap h. */
  private def lookup(h: Exp, o: Exp, f: Exp) = MapSelect(h, Seq(o, f))

  override def translateLocationAccess(f: sil.LocationAccess): Exp = {
    translateLocationAccess(f, heapExp)
  }
  private def translateLocationAccess(f: sil.LocationAccess, heap: Exp): Exp = {
    f match {
      case sil.FieldAccess(rcv, field) =>
        MapSelect(heap, Seq(translateExp(rcv), translateLocation(f)))
      case sil.PredicateAccess(_, _) =>
        MapSelect(heap, Seq(nullLit, translateLocation(f)))
    }
  }

  override def translateLocationAccess(rcv: Exp, loc:Exp):Exp = {
    MapSelect(heap, Seq(rcv, loc))
  }

  override def translateLocation(l: sil.LocationAccess): Exp = {
    l match {
      case sil.PredicateAccess(args, predName) =>
        val pred = verifier.program.findPredicate(predName)
        val t = predicateMetaTypeOf(pred)
        FuncApp(locationIdentifier(pred), args map translateExp, t)
      case sil.FieldAccess(rcv, field) =>
        Const(locationIdentifier(field))
    }
  }

  override def translateLocation(pred: sil.Predicate, args: Seq[Exp]): Exp = {
    val t = predicateMetaTypeOf(pred)
    FuncApp(locationIdentifier(pred), args, t)
  }

  override def simpleHandleStmt(stmt: sil.Stmt): Stmt = {
    stmt match {
      case sil.FieldAssign(lhs, rhs) =>
        translateLocationAccess(lhs) := translateExp(rhs)
      case sil.NewStmt(target,fields) =>
        Havoc(freshObjectVar) ::
          // assume the fresh object is non-null and not allocated yet.
          // this means that whenever we allocate a new object and havoc freshObjectVar, we
          // assume that we consider a newly allocated cell, which gives the prover
          // the information that this object is different from anything allocated
          // earlier. Note that "validReference" must be used in appropriate places
          // in the encoding to get this fact (e.g. below for method targets, and also
          // for loops (see the StateModule implementation)
          Assume((freshObjectVar !== nullLit) && alloc(freshObjectVar).not) ::
          (alloc(freshObjectVar) := TrueLit()) ::
          (translateExp(target) := freshObjectVar) ::
          Nil
      case sil.MethodCall(_, _, targets) =>
        targets filter (_.typ == sil.Ref) map translateExp map {
          t =>
            Assume(validReference(t))
        }
      case sil.Fold(sil.PredicateAccessPredicate(loc, perm)) => // AS: this should really be taken care of in the FuncPredModule (and factored out to share code with unfolding case, if possible)
        val newVersion = LocalVar(Identifier("freshVersion"), funcPredModule.predicateVersionType)
        val resetPredicateInfo : Stmt = (predicateMask(loc) := zeroPMask) ++
          Havoc(newVersion) ++
          (translateLocationAccess(loc) := newVersion)

          If(UnExp(Not,hasDirectPerm(loc)), resetPredicateInfo, Nil) ++
          addPermissionToPMask(loc)
      case _ => Statements.EmptyStmt
    }
  }

  override def freeAssumptions(e: sil.Exp): Stmt = {
    e match {
      case sil.Unfolding(sil.PredicateAccessPredicate(loc, _), _) if !usingOldState =>
        addPermissionToPMask(loc)
      case _ => Nil
    }
  }

  /**
   * Adds the permissions from the body of a predicate to its permission mask.
   */
  private def addPermissionToPMask(loc: sil.PredicateAccess): Stmt = {
    val predBody = loc.predicateBody(verifier.program).get
    addPermissionToPMaskHelper(predBody, loc, predicateMask(loc,heap))
  }
  /**
   * Adds the permissions from an expression to a permission mask.
   */
  private def addPermissionToPMaskHelper(e: sil.Exp, loc: sil.PredicateAccess, pmask: Exp): Stmt = {
    e match {
      case QuantifiedPermissionAssertion(forall, cond, acc: sil.FieldAccessPredicate) =>
        val v = forall.variables.head // TODO: Generalise to multiple quantified variables
        val fieldAccess = acc.loc

        // alpha renaming, to avoid clashes in context
        val vFresh = env.makeUniquelyNamed(v);
        env.define(vFresh.localVar);

        def renaming[E <: sil.Exp] = (e:E) => Expressions.instantiateVariables(e, v.localVar,  vFresh.localVar)

        val (renamingCond,renamingFieldAccess) = (renaming(cond),renaming(fieldAccess))
        val translatedCond = translateExp(renamingCond)

        val newPMask = LocalVar(Identifier("newPMask"), pmaskType)
        val obj = LocalVarDecl(Identifier("o")(axiomNamespace), refType)
        val field = LocalVarDecl(Identifier("f")(axiomNamespace), fieldType)
        val pm1 = MapSelect(pmask, Seq(obj.l, field.l))
        val pm2 = MapSelect(newPMask, Seq(obj.l, field.l))
          MaybeComment("register all known folded permissions guarded by predicate " + loc.predicateName,
            Havoc(newPMask) ++
              Assume(Forall(Seq(obj, field), Seq(Trigger(pm2)), (pm1 ==> pm2))) ++
                Assume(Forall(translateLocalVarDecl(vFresh),Seq(),translatedCond ==> (translateLocationAccess(renamingFieldAccess, newPMask) === TrueLit()) ))) ++
            (pmask := newPMask)
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
        addPermissionToPMaskHelper(e1, loc, pmask) ::
          addPermissionToPMaskHelper(e2, loc, pmask) ::
          Nil
      case sil.Implies(e1, e2) =>
        If(translateExp(e1), addPermissionToPMaskHelper(e2, loc, pmask), Statements.EmptyStmt)
      case sil.CondExp(c, e1, e2) =>
        If(translateExp(c), addPermissionToPMaskHelper(e1, loc, pmask), addPermissionToPMaskHelper(e2, loc, pmask))
      case _ => Nil
    }
  }

  override def validValue(typ: sil.Type, variable: LocalVar, isParameter: Boolean): Option[Exp] = {
    typ match {
      case sil.Ref => Some(validReference(variable))
      case _ => None
    }
  }

  private def validReference(exp: Exp): Exp = {
    exp === nullLit || alloc(exp)
  }

  override def translateNull: Exp = nullLit

  def initBoogieState: Stmt = {
    heap = originalHeap
    Nil
  }
  def resetBoogieState: Stmt = {
    Havoc(heapVar)
  }
  def initOldState: Stmt = {
    val hVar = heapVar
    Assume(Old(hVar) === hVar)
  }

  def staticStateContributions: Seq[LocalVarDecl] = Seq(LocalVarDecl(heapName, heapTyp))
  def currentStateContributions: Seq[LocalVarDecl] = Seq(LocalVarDecl(heap.name, heapTyp))
  def currentStateVars: Seq[Var] = Seq(heap)
  def currentStateExps: Seq[Exp] = Seq(heapExp)


  override def freshTempState(name: String): Seq[Var] = {
    Seq(LocalVar(Identifier(s"${name}Heap"), heapTyp))
  }

  override def restoreState(s: Seq[Var]) {
    heap = s(0) // note: this should be accessed via heapVar or heapExp as appropriate (whether a variable is essential or not)
  }

  override def usingOldState = stateModuleIsUsingOldState


  override def beginExhale: Stmt = {
    Havoc(exhaleHeap)
  }

  override def endExhale: Stmt = {
    if (!usingOldState) Assume(FuncApp(identicalOnKnownLocsName, Seq(heapExp, exhaleHeap) ++ currentMask, Bool)) ++
      (heapVar := exhaleHeap)
    else Nil
  }

  override def inhaleExp(e: sil.Exp): Stmt = {
    e match {
      case sil.Unfolding(sil.PredicateAccessPredicate(loc, perm), exp) =>
        addPermissionToPMask(loc)
      case _ => Nil
    }
  }

  /**
   * Reset the state of this module so that it can be used for new program. This method is called
   * after verifier gets a new program.
   */
  override def reset = {
    PredIdMap = Map()
    NextPredicateId = 0
    heap = originalHeap
  }

  override def currentHeap = Seq(heap)

  override def identicalOnKnownLocations(otherHeap:Seq[Exp],otherMask:Seq[Exp]):Exp =
    FuncApp(identicalOnKnownLocsName,otherHeap ++ heap ++ otherMask, Bool)
}
