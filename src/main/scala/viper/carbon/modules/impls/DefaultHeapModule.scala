// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.modules.impls

import viper.carbon.modules._
import viper.carbon.modules.components.{DefinednessComponent, InhaleComponent, SimpleStmtComponent}
import viper.silver.ast.utility.Expressions
import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.boogie.Implicits._
import viper.carbon.verifier.Verifier
import viper.carbon.utility.{PolyMapDesugarHelper, PolyMapRep}
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion
import viper.silver.verifier.PartialVerificationError

/**
 * The default implementation of a [[viper.carbon.modules.HeapModule]].
 */
class DefaultHeapModule(val verifier: Verifier)
    extends HeapModule
    with SimpleStmtComponent
    with DefinednessComponent {

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

  override def start(): Unit = {
    stateModule.register(this)
    stmtModule.register(this)
    expModule.register(this)
  }

  var enableAllocationEncoding : Boolean = true // note: this may be modified on configuration, so should only be used e.g. in method defs which will be called later (e.g. during verification)


  def cmpResources: Seq[sil.Resource] = Seq(allocField) ++ verifier.program.fields ++ verifier.program.predicates ++ verifier.program.magicWandStructures

  var resources: Seq[sil.Resource] = _

  def getHeapType(r: sil.Resource): Type = r match {
    case f: sil.Field => fheapTyp(translateType(f.typ)) //MapType(Seq(refType), translateType(f.typ), Seq())
    case _: sil.Predicate => pheapTyp // MapType(Seq(funcPredModule.snapType()), funcPredModule.snapType(), Seq())
    case _: sil.MagicWand => pheapTyp // MapType(Seq(funcPredModule.snapType()), funcPredModule.snapType(), Seq())
  }

  def cmpHeapTypes = resources.map(r => r -> getHeapType(r)).toMap

  var heapTypes: Map[sil.Resource, Type] = _

  def heapTypeMap = heapTypes

  def getResourceName(r: sil.Resource) = r match {
    case f: sil.Field => f.name
    case p: sil.Predicate => p.name
    case w: sil.MagicWand => verifier.program.magicWandStructures.indexOf(w.structure(verifier.program))
  }

  def cmpHeapMap: Map[sil.Resource, Var] = resources.map(r => r -> GlobalVar(Identifier(s"Heap_${getResourceName(r)}"), heapTypes(r))).toMap

  var heapMap: Map[sil.Resource, Var]  = _

  def cmpExhaleHeapMap: Map[sil.Resource, Var] = resources.map(r => r -> GlobalVar(Identifier(s"ExhaleHeap_${getResourceName(r)}"), heapTypes(r))).toMap

  var exhaleHeapMap: Map[sil.Resource, Var] = _

  override def predicateVersionFieldTypeOf(p: sil.Predicate) = ???
  private def predicateMetaTypeOf(p: sil.Predicate) = ???
  override def predicateVersionFieldType(genericT: String = "A") = ???
  override def predicateMaskFieldType: Type = ???
  override def predicateMaskFieldTypeOf(p: sil.Predicate): Type = ???


  override def predicateMaskFieldTypeOfWand(wand: String): Type = ???
  override def predicateVersionFieldTypeOfWand(wand: String) = ???


  override def wandBasicType(wand: String): Type = ???
  override def wandFieldType(wand: String) : Type = ???
  private val genfheapTyp = NamedType("HeapType", Seq(TypeVar("B")))
  def genfheapType = genfheapTyp
  private def fheapTyp(ta: Type) = NamedType("HeapType", Seq(ta))
  private val pheapTyp = NamedType("PHeapType")
  private val heapName = Identifier("Heap")
  private val heap0Name = Identifier("Heap0")
  private val heap1Name = Identifier("Heap1")
  private val heap2Name = Identifier("Heap2")
  private val exhaleHeapName = Identifier("ExhaleHeap")
  //private val exhaleHeap = LocalVar(exhaleHeapName, heapTyp)
  private val qpHeapName = Identifier("QPHeap")
  //private val qpHeap = LocalVar(qpHeapName, heapTyp)
  private var heaps: Map[sil.Resource, Var] = _
  private val nullName = Identifier("null")
  private val nullLit = Const(nullName)
  private val fidenticalOnKnownLocsName = Identifier("IdenticalOnKnownLocations")
  private val allocidenticalOnKnownLocsName = Identifier("allocIdenticalOnKnownLocations")
  private val pidenticalOnKnownLocsName = Identifier("PIdenticalOnKnownLocations")
  private lazy val allocField = if(enableAllocationEncoding) sil.Field("$allocated", sil.Bool)() else null
  private val fsumHeapName = Identifier("SumHeap")
  private val psumHeapName = Identifier("PSumHeap")
  private val freshObjectName = Identifier("freshObj")
  private val freshObjectVar = LocalVar(freshObjectName, refType)
  private def heapVars: Map[sil.Resource, Var] = {assert (!usingOldState); heaps}
  private def heapVar(r: sil.Resource): Var = {assert (!usingOldState); heaps(r)}

  private def heapExps: Seq[Exp] = (if (usingOldState) heaps.values.map(Old(_)).toSeq else heaps.values.toSeq)
  private def heapExp(r: sil.Resource): Exp = if (usingOldState) Old(heaps(r)) else heaps(r)

  /*



  private val succHeapName = Identifier("succHeap")
  private val succHeapTransName = Identifier("succHeapTrans")

  private val identicalOnKnownLocsLiberalName = Identifier("IdenticalOnKnownLocationsLiberal")
  private val isPredicateFieldName = Identifier("IsPredicateField")
  private var PredIdMap:Map[String, BigInt] = Map()
  private var NextPredicateId:BigInt = 0
  private val isWandFieldName = Identifier("IsWandField")
  private val getPredicateIdName = Identifier("getPredicateId")

  private val readHeapName = Identifier("readHeap")
  private val updateHeapName = Identifier("updHeap")
  private val dummyHeapName = Identifier("dummyHeap")
  private val dummyHeap = Const(dummyHeapName)

   */

  override def refType = NamedType("Ref")

  override def fieldTypeConstructor = ???

  override def preamble = {
    val obj = LocalVarDecl(Identifier("o")(axiomNamespace), refType)
    val obj2 = LocalVarDecl(Identifier("o2")(axiomNamespace), refType)
    val useSumOfStatesAxioms = loopModule.sumOfStatesAxiomRequired

    TypeDecl(refType) ++
      // Re-translating types so the type module knows those types are used.
      heaps.map(v => GlobalVarDecl(v._2.name, if (v._1.isInstanceOf[sil.Field]) fheapTyp(translateType(v._1.asInstanceOf[sil.Field].typ)) else v._2.typ)) ++
      exhaleHeapMap.map(v => GlobalVarDecl(v._2.name, v._2.typ)) ++
      ConstDecl(nullName, refType) ++
      TypeAlias(genfheapTyp, MapType(Seq(refType), TypeVar("B"))) ++
      TypeAlias(pheapTyp, MapType(Seq(funcPredModule.snapType()), funcPredModule.snapType())) ++
      // TODO: allocationEncoding
    /*(if(enableAllocationEncoding) ConstDecl(allocName, NamedType(fieldTypeName, Seq(normalFieldType, Bool)), unique = true) ++*/
      {
        val relevantHeaps = heaps.filter(h => h._1.isInstanceOf[sil.Field] && h._1.asInstanceOf[sil.Field].typ == sil.Ref)
        val triggers = relevantHeaps.map(h => Trigger(Seq(staticGoodState, validReference(lookup(h._2, obj.l)))))
        // all heap-lookups yield allocated objects or null
        Axiom(Forall(
          obj ++
            stateModule.staticStateContributions(),
          triggers.toSeq,
          validReference(obj.l) ==> All(relevantHeaps.map(h => validReference(lookup(heaps(h._1), obj.l))).toSeq)))
      }  ++
      // TODO: succHeap?
    /*Func(succHeapName,
        Seq(LocalVarDecl(heap0Name, heapTyp), LocalVarDecl(heap1Name, heapTyp)),
        Bool) ++
      Func(succHeapTransName,
        Seq(LocalVarDecl(heap0Name, heapTyp), LocalVarDecl(heap1Name, heapTyp)),
        Bool) ++ */
      Func(fidenticalOnKnownLocsName,
        Seq(LocalVarDecl(heapName, genfheapTyp), LocalVarDecl(exhaleHeapName, genfheapTyp), LocalVarDecl(Identifier("msk"), maskType)),
        Bool) ++
      Func(allocidenticalOnKnownLocsName,
        Seq(LocalVarDecl(heapName, genfheapTyp), LocalVarDecl(exhaleHeapName, genfheapTyp), LocalVarDecl(Identifier("msk"), maskType)),
        Bool) ++
      Func(pidenticalOnKnownLocsName,
        Seq(LocalVarDecl(heapName, pheapTyp), LocalVarDecl(exhaleHeapName, pheapTyp), LocalVarDecl(Identifier("msk"), pmaskType)),
        Bool) ++
      {
        if(useSumOfStatesAxioms)
          (Func(fsumHeapName,
            Seq(LocalVarDecl(heapName, genfheapTyp), LocalVarDecl(heap1Name, genfheapTyp), LocalVarDecl(Identifier("mask1"), maskType),
              LocalVarDecl(heap2Name, genfheapTyp), LocalVarDecl(Identifier("mask2"), maskType)),
            Bool) ++
            Func(psumHeapName,
              Seq(LocalVarDecl(heapName, pheapTyp), LocalVarDecl(heap1Name, pheapTyp), LocalVarDecl(Identifier("mask1"), pmaskType),
                LocalVarDecl(heap2Name, pheapTyp), LocalVarDecl(Identifier("mask2"), pmaskType)),
              Bool))
        else Nil
      } ++ {
      val h = LocalVarDecl(heapName, genfheapTyp)
      val ph = LocalVarDecl(heapName, pheapTyp)
      val eh = LocalVarDecl(exhaleHeapName, genfheapTyp)
      val h0 = LocalVarDecl(heap0Name, genfheapTyp)
      val h1 = LocalVarDecl(heap1Name, genfheapTyp)
      val h2 = LocalVarDecl(heap2Name, genfheapTyp)
      val peh = LocalVarDecl(exhaleHeapName, pheapTyp)
      val ph0 = LocalVarDecl(heap0Name, pheapTyp)
      val ph1 = LocalVarDecl(heap1Name, pheapTyp)
      val ph2 = LocalVarDecl(heap2Name, pheapTyp)
      val m = LocalVarDecl(Identifier("mask"), maskType)
      val vars = Seq(h, eh, m)
      val identicalFuncApp = FuncApp(fidenticalOnKnownLocsName, vars map (_.l), Bool)

      identicalOnKnownLocsAxioms() ++ pidenticalOnKnownLocsAxioms() ++ allocidenticalOnKnownLocsAxioms() ++
       /* MaybeCommentedDecl("Updated Heaps are Successor Heaps", {
          val value = LocalVarDecl(Identifier("v"), TypeVar("B"));
          val upd = heapUpdate(h.l, obj.l, field.l, value.l)
          Axiom(Forall(
            Seq(h, obj, field, value),
            Trigger(Seq(upd))
            ,
            FuncApp(succHeapName, Seq(h.l, upd), Bool)
          ))
        }, size = 1) ++
        MaybeCommentedDecl("IdenticalOnKnownLocations Heaps are Successor Heaps",
          Axiom(Forall(
            vars,
            Trigger(Seq(identicalFuncApp))
            ,
            identicalFuncApp ==> FuncApp(succHeapName, Seq(h.l, eh.l), Bool)
          )), size = 1) ++
        {
          if (useSumOfStatesAxioms) {
            MaybeCommentedDecl("IdenticalOnKnownLiberalLocations Heaps are Successor Heaps",
              Axiom(Forall(
                vars,
                Trigger(Seq(identicalLiberalFuncApp))
                ,
                identicalLiberalFuncApp ==> FuncApp(succHeapName, Seq(h.l, eh.l), Bool)
              )), size = 1)
          } else {
            Nil
          }
        } ++
      MaybeCommentedDecl("Successor Heaps are Transitive Successor Heaps", {
              val succHeapApp = FuncApp(succHeapName, Seq(h0.l, h1.l), Bool)
              Axiom(Forall(
                Seq(h0, h1),
                Trigger(Seq(succHeapApp))
                ,
                succHeapApp ==> FuncApp(succHeapTransName, Seq(h0.l, h1.l), Bool)
              ))
            }, size = 1) ++
        MaybeCommentedDecl("Transitivity of Transitive Successor Heaps", {
          val succHeapTransApp = FuncApp(succHeapTransName, Seq(h0.l, h1.l), Bool)
          val succHeapApp = FuncApp(succHeapName, Seq(h1.l, h2.l), Bool)
          Axiom(Forall(
            Seq(h0, h1, h2),
            Trigger(Seq(succHeapTransApp,succHeapApp))
            ,
            (succHeapTransApp && succHeapApp) ==> FuncApp(succHeapTransName, Seq(h0.l, h2.l), Bool) // NOTE: ignore IDE warning - these parentheses are NOT spurious, due to how the overloaded && and ==> get desugared
          ))
        }, size = 1) ++*/
        {
          if (useSumOfStatesAxioms) {
              MaybeCommentedDecl("Sum of heaps", {
                val mask1 = LocalVarDecl(Identifier("Mask1"),maskType)
                val mask2 = LocalVarDecl(Identifier("Mask2"),maskType)

                val sumStateApp = sumFHeap(h.l, h1.l, mask1.l, h2.l, mask2.l)

                Axiom(Forall(
                  Seq(h, h1, mask1, h2, mask2),
                  Trigger(sumStateApp),
                  sumStateApp <==> (
                    FuncApp(fidenticalOnKnownLocsName, Seq(h1.l, h.l, mask1.l), Bool) &&
                      FuncApp(fidenticalOnKnownLocsName, Seq(h2.l, h.l, mask2.l), Bool)
                    )))
              }) ++
                MaybeCommentedDecl("Sum of predicate heaps", {
                  val pmask1 = LocalVarDecl(Identifier("pMask1"), pmaskType)
                  val pmask2 = LocalVarDecl(Identifier("pMask2"), pmaskType)

                  val sumStateApp = sumPHeap(ph.l, ph1.l, pmask1.l, ph2.l, pmask2.l)

                  Axiom(Forall(
                    Seq(ph, ph1, pmask1, ph2, pmask2),
                    Trigger(sumStateApp),
                    sumStateApp <==> (
                      FuncApp(pidenticalOnKnownLocsName, Seq(ph1.l, ph.l, pmask1.l), Bool) &&
                        FuncApp(pidenticalOnKnownLocsName, Seq(ph2.l, ph.l, pmask2.l), Bool)
                      )))
                })
          } else {
            Nil
          }
        }
      }
    }

  /* The liberal version does not equate the known-folded permission masks, but instead just propagates the information
   * that known-folded locations remain known-folded (while locations that are not known-folded are underspecified).
   * This permits taking the sum of two heaps that record different known-folded permission masks.
   */
  private def identicalOnKnownLocsAxioms():Seq[Decl] = {
    // for fields
    val obj = LocalVarDecl(Identifier("o")(axiomNamespace), refType)
    val h = LocalVarDecl(heapName, genfheapTyp)
    val eh = LocalVarDecl(exhaleHeapName, genfheapTyp)
    val m = LocalVarDecl(Identifier("mask"), maskType)
    val vars = Seq(h, eh, m)

    val funcName = fidenticalOnKnownLocsName


    val identicalFuncApp = FuncApp(funcName, vars map (_.l), Bool)
    // frame all locations with direct permission
    MaybeCommentedDecl("Frame all locations with direct permissions", Axiom(Forall(
      vars ++ Seq(obj),
      //        Trigger(Seq(identicalFuncApp, lookup(h.l, obj.l, field.l))) ++
      Trigger(Seq(identicalFuncApp, lookup(eh.l, obj.l))),
      identicalFuncApp ==>
        (currentPermission(m.l, obj.l) > noPerm ==>
          (lookup(h.l, obj.l) === lookup(eh.l, obj.l))), TypeVar("B")
    )), size = 1)

  }

  private def allocidenticalOnKnownLocsAxioms(): Seq[Decl] = {
    // for fields
    val obj = LocalVarDecl(Identifier("o")(axiomNamespace), refType)
    val ht = fheapTyp(Bool)
    val h = LocalVarDecl(heapName, ht)
    val eh = LocalVarDecl(exhaleHeapName, ht)
    val m = LocalVarDecl(Identifier("mask"), maskType)
    val vars = Seq(h, eh, m)

    val funcName = allocidenticalOnKnownLocsName


    val identicalFuncApp = FuncApp(funcName, vars map (_.l), Bool)
    // frame all locations with direct permission
    MaybeCommentedDecl("Frame all locations with direct permissions", Axiom(Forall(
      vars ++ Seq(obj),
      //        Trigger(Seq(identicalFuncApp, lookup(h.l, obj.l, field.l))) ++
      Trigger(Seq(identicalFuncApp, lookup(eh.l, obj.l))),
      identicalFuncApp ==>
        ((lookup(h.l, obj.l) ==> lookup(eh.l, obj.l)))
    )), size = 1)

  }

  private def pidenticalOnKnownLocsAxioms(): Seq[Decl] = {
    // for fields
    val args = LocalVarDecl(Identifier("o")(axiomNamespace), funcPredModule.snapType())
    val h = LocalVarDecl(heapName, pheapTyp)
    val eh = LocalVarDecl(exhaleHeapName, pheapTyp)
    val m = LocalVarDecl(Identifier("pmask"), pmaskType)
    val vars = Seq(h, eh, m)

    val funcName = pidenticalOnKnownLocsName


    val identicalFuncApp = FuncApp(funcName, vars map (_.l), Bool)
    // frame all locations with direct permission
    MaybeCommentedDecl("Frame all locations with direct permissions", Axiom(Forall(
      vars ++ Seq(args),
      //        Trigger(Seq(identicalFuncApp, lookup(h.l, obj.l, field.l))) ++
      Trigger(Seq(identicalFuncApp, lookup(eh.l, args.l))),
      identicalFuncApp ==>
        (currentPermission(m.l, args.l) > noPerm ==>
          (lookup(h.l, args.l) === lookup(eh.l, args.l)))
    )), size = 1)

  }

  override def sumFHeap(resultHeap: Exp, heap1: Exp, mask1: Exp, heap2: Exp, mask2: Exp): Exp = {
    FuncApp(fsumHeapName, Seq(resultHeap, heap1, mask1, heap2, mask2), Bool)
  }

  override def sumPHeap(resultHeap: Exp, heap1: Exp, mask1: Exp, heap2: Exp, mask2: Exp): Exp = {
    FuncApp(psumHeapName, Seq(resultHeap, heap1, mask1, heap2, mask2), Bool)
  }

  override def fheapType(ta: Type): Type = fheapTyp(ta)

  override def pheapType: Type = pheapTyp

  override def successorHeapState(first: Seq[LocalVarDecl], second: Seq[LocalVarDecl]): Exp = ???

  override def isPredicateField(f: Exp): Exp = ???

  override def isWandField(f: Exp) : Exp = ???

  // returns predicate Id
  override def getPredicateId(f:Exp): Exp = ???

  override def getPredicateId(s:String): BigInt = ???

  def getNewPredId : BigInt = ???

  override def translateField(f: sil.Field) = ???


// AS: Seems that many concerns here would be better addressed in / delegated to the FuncPredModule
  override def predicateGhostFieldDecl(p: sil.Predicate): Seq[Decl] = Seq(Func(predicateTriggerIdentifier(p), staticStateContributions(true, false) ++ Seq(LocalVarDecl(Identifier("args"), funcPredModule.snapType())), Bool))

  def wandMaskIdentifier(f: Identifier) = ???

  def wandFtIdentifier(f: Identifier) = ???


  /**
    * @param maskField the field with which the predicate mask is accessed in the heap
    * @param mask the predicate mask itself (for example, Heap[null, [[maskField]]])
    */
  case class PredicateMask(maskField: Exp, mask: Exp)

  private def predicateMask(loc: sil.PredicateAccess) : PredicateMask = ???

  private def predicateMask(loc: sil.PredicateAccess, heap: Exp) : PredicateMask = ???

  private def curHeapAssignUpdatePredWandMask(maskField: Exp, newMask: Exp): Stmt = ??? /* {
    heap := heapUpdate(heap, nullLit, maskField, newMask)
  }*/

  private def wandMask(wandMaskRep: Exp) = ???

  private def predicateTriggerIdentifier(f: sil.Predicate): Identifier = {
    Identifier(f.name + "#trigger")(fieldNamespace)
  }
  private def predicateTriggerAnyStateIdentifier(f: sil.Predicate): Identifier = {
    Identifier(f.name + "#everUsed")(fieldNamespace)
  }
  private def predicateTrigger(extras : Seq[Exp], predicate: sil.Predicate, predicateArgSnap: Exp): Exp = {
    FuncApp(predicateTriggerIdentifier(predicate), extras ++ Seq(predicateArgSnap), Bool)
  }
  override def predicateTrigger(extras : Seq[Exp], pred: sil.PredicateAccess): Exp = {
    val predicate = verifier.program.findPredicate(pred.predicateName)
    val receiver = translateReceiver(pred)
    predicateTrigger(extras, predicate, receiver)
  }

  /** Returns a heap-lookup of the allocated field of an object. */
  /** (should only be used for known-non-null references) */
  private def alloc(o: Exp): Exp = lookup(heaps(allocField), o)

  /** Returns assignment that updates heap to reflect that @{code ref} is assigned  */
  private def allocUpdateRef(ref: Exp) : Stmt = currentHeapAssignUpdate(ref, allocField, TrueLit())

  /** Returns a heap-lookup for o.f in a given heap h. */
  private def lookup(h: Exp, o: Exp, isPMask: Boolean = false): Exp =  {
    if(verifier.usePolyMapsInEncoding) {
      MapSelect(h, Seq(o))
    } else {
      ??? // FuncApp( if(isPMask) { permModule.pmaskTypeDesugared.selectId } else { readHeapName }, Seq(h,o,f), Bool)
    }
  }

  override def currentHeapAssignUpdate(f: sil.LocationAccess, newVal: Exp): Stmt = {
    val rcvExp = translateReceiver(f)
    currentHeapAssignUpdate(rcvExp, f.loc(program), newVal)
  }

  private def currentHeapAssignUpdate(rcv: Exp, res: sil.Resource, newVal: Exp): Stmt = {
    val heap = heaps(res)
    (heap := heapUpdate(heap, rcv, newVal))
  }

  private def heapUpdateLoc(heap: Exp, f: sil.LocationAccess, newVal: Exp, isPMask: Boolean = false): Exp = {
    val rcvExp = translateReceiver(f)
    heapUpdate(heap, rcvExp, newVal, isPMask)
  }

  def translateReceiver(la: sil.LocationAccess): Exp = {
    la match {
      case sil.FieldAccess(rcv, _) => translateExp(rcv)
      case sil.PredicateAccess(args, _) => funcPredModule.silExpsToSnap(args)
    }
  }

  private def heapUpdate(heap: Exp, rcv: Exp, newVal: Exp, isPMask: Boolean = false): Exp = {
    if(verifier.usePolyMapsInEncoding)
      MapUpdate(heap, Seq(rcv), newVal)
    else
      ???
  }

  override def translateLocationAccess(f: sil.LocationAccess): Exp = {
    translateLocationAccess(f, heapExp(f.res(program)))
  }

  override def translateLocationAccess(rcv: Exp, res: sil.Resource): Exp = {
    lookup(heapExp(res), rcv, !res.isInstanceOf[sil.Field])
  }

  private def translateLocationAccess(f: sil.LocationAccess, heap: Exp, isPMask: Boolean = false): Exp = {
    val res = f.loc(program)
    val rcvExp = translateReceiver(f)
    lookup(heap, rcvExp, isPMask)
  }

  override def handleStmt(s: sil.Stmt, statesStack: List[Any] = null, allStateAssms: Exp = TrueLit(), insidePackageStmt: Boolean = false) : (Seqn => Seqn) = {

      stmt => (
        s match {
          case sil.MethodCall(_, _, targets) if enableAllocationEncoding =>
            stmt ++ (targets filter (_.typ == sil.Ref) map translateExp map {
              t =>
                Assume(validReference(t))
            })
          case sil.Fold(sil.PredicateAccessPredicate(loc, perm)) => // AS: this should really be taken care of in the FuncPredModule (and factored out to share code with unfolding case, if possible)
            if(usingOldState) sys.error("heap module: fold is executed while using old state")
            stmt ++ ({val newVersion = LocalVar(Identifier("freshVersion"), funcPredModule.predicateVersionType)
              val resetPredicateInfo : Stmt =
                Havoc(newVersion) ++
                currentHeapAssignUpdate(loc, newVersion)

              If(UnExp(Not,hasDirectPerm(loc)), resetPredicateInfo, Nil) ++
                stateModule.assumeGoodState}  )
          case sil.FieldAssign(lhs, rhs) =>
            if(usingOldState) sys.error("heap module: field is assigned while using old state")
            stmt ++ (currentHeapAssignUpdate(lhs, translateExp(rhs))) // after all checks
          case _ => simpleHandleStmt(s) ++ stmt
        }
      )

  }

  override def simpleHandleStmt(stmt: sil.Stmt, statesStack: List[Any] = null, allStateAssms: Exp = TrueLit(), insidePackageStmt: Boolean = false): Stmt = {
    stmt match {
      case sil.NewStmt(target,fields) =>
        Havoc(freshObjectVar) ::
          // assume the fresh object is non-null and not allocated yet.
          // this means that whenever we allocate a new object and havoc freshObjectVar, we
          // assume that we consider a newly allocated cell, which gives the prover
          // the information that this object is different from anything allocated
          // earlier. Note that "validReference" must be used in appropriate places
          // in the encoding to get this fact (e.g. below for method targets, and also
          // for loops (see the StateModule implementation)
          Assume(if(enableAllocationEncoding) (freshObjectVar !== nullLit) && alloc(freshObjectVar).not else (freshObjectVar !== nullLit)) ::
          (if(enableAllocationEncoding) allocUpdateRef(freshObjectVar) :: (translateExp(target) := freshObjectVar) :: Nil else (translateExp(target) := freshObjectVar) :: Nil)
      case _ => Statements.EmptyStmt
    }
  }

  override def freeAssumptions(e: sil.Exp): Stmt = {
    e match {
      case sil.Unfolding(sil.PredicateAccessPredicate(loc, _), _) if !usingOldState =>
        assumeGoodState
      case _ => Nil
    }
  }

  override def addPermissionToWMask(wMaskField: Exp, e: sil.Exp): Stmt = ??? /*{
    if(usingOldState) { sys.error("Updating wand mask while using old state") }
    e match {
      case sil.FieldAccessPredicate(loc, perm) =>
        curHeapAssignUpdatePredWandMask(wMaskField, heapUpdateLoc(wandMask(wMaskField), loc, TrueLit(), true))
      case sil.PredicateAccessPredicate(loc, perm) =>
        val newPMask = LocalVar(Identifier("newPMask"), pmaskType)
        val obj = LocalVarDecl(Identifier("o")(axiomNamespace), refType)
        val field = LocalVarDecl(Identifier("f")(axiomNamespace), fieldType)
        val pm1 = lookup(wandMask(wMaskField), obj.l, field.l, true)
        val pm3 = lookup(newPMask, obj.l, field.l, true)
        Havoc(newPMask) ++
          Assume(Forall(Seq(obj, field), Seq(Trigger(pm3)), (pm1) ==> pm3)) ++
          curHeapAssignUpdatePredWandMask(wMaskField, newPMask)

      case _ =>
        Statements.EmptyStmt
    }
  }*/
  /**
   * Adds the permissions from an expression to a permission mask.
   */
    /*
  private def addPermissionToPMaskHelper(e: sil.Exp, loc: sil.PredicateAccess, pmask: PredicateMask): Stmt = {
    if(usingOldState) { sys.error("Updating wand mask while using old state") }
    e match {
      case QuantifiedPermissionAssertion(forall, cond, acc: sil.FieldAccessPredicate) =>
        val vs = forall.variables // TODO: Generalise to multiple quantified variables
        val fieldAccess = acc.loc

        // alpha renaming, to avoid clashes in context
        val vsFresh = vs.map(v => env.makeUniquelyNamed(v))
        vsFresh.foreach(vFresh => env.define(vFresh.localVar))

        def renaming[E <: sil.Exp] = (e:E) => Expressions.instantiateVariables(e, vs.map(_.localVar),  vsFresh.map(_.localVar))

        val (renamingCond,renamingFieldAccess) = (renaming(cond),renaming(fieldAccess))
        val translatedCond = translateExp(renamingCond)

        val newPMask = LocalVar(Identifier("newPMask"), pmaskType)
        val obj = LocalVarDecl(Identifier("o")(axiomNamespace), refType)
        val field = LocalVarDecl(Identifier("f")(axiomNamespace), fieldType)
        val pm1 = lookup(pmask.mask, obj.l, field.l, true)
        val pm2 = lookup(newPMask, obj.l, field.l, true)
        val res =
          MaybeComment("register all known folded permissions guarded by predicate " + loc.predicateName,
            Havoc(newPMask) ++
              Assume(Forall(Seq(obj, field), Seq(Trigger(pm2)), (pm1 ==> pm2))) ++
                Assume(Forall(vsFresh.map(vFresh => translateLocalVarDecl(vFresh)),Seq(),translatedCond ==> (translateLocationAccess(renamingFieldAccess, newPMask, true) === TrueLit()) ))) ++
            curHeapAssignUpdatePredWandMask(pmask.maskField, newPMask)
        vsFresh.foreach(vFresh => env.undefine(vFresh.localVar))
        res
      case sil.FieldAccessPredicate(loc, perm) =>
        curHeapAssignUpdatePredWandMask(pmask.maskField, heapUpdateLoc(pmask.mask, loc, TrueLit(), true))
      case sil.PredicateAccessPredicate(loc, perm) =>
        val newPMask = LocalVar(Identifier("newPMask"), pmaskType)
        val obj = LocalVarDecl(Identifier("o")(axiomNamespace), refType)
        val field = LocalVarDecl(Identifier("f")(axiomNamespace), fieldType)
        val pm1 = lookup(pmask.mask, obj.l, field.l, true)
        val pm3 = lookup(newPMask, obj.l, field.l, true)
        Havoc(newPMask) ++
          Assume(Forall(Seq(obj, field), Seq(Trigger(pm3)), (pm1) ==> pm3)) ++
          curHeapAssignUpdatePredWandMask(pmask.maskField, newPMask)
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
  }*/

  override def validValue(typ: sil.Type, variable: LocalVar, isParameter: Boolean): Option[Exp] = {
    if(enableAllocationEncoding) typ match {
      case sil.Ref => Some(validReference(variable))
      case _ => None
    } else None
  }

  private def validReference(exp: Exp): Exp = {
    /*exp === nullLit ||*/ alloc(exp)
  }

  override def nullLiteral: Exp = nullLit

  def initBoogieState: Stmt = {
    heaps = heapMap
    Nil
  }
  def resetBoogieState: Stmt = {
    if (resources == null)
      reset()
    heaps.values.map(Havoc(_)).toSeq
  }
  def initOldState: Stmt = {
    heaps.values.map(h => Assume(Old(h) === h)).toSeq
  }

  def staticStateContributions(withHeap: Boolean, withPermissions: Boolean): Seq[LocalVarDecl] = if (withHeap) heapMap.values.map(h => LocalVarDecl(h.name, h.typ)).toSeq else Seq()

  def currentStateContributions: Seq[LocalVarDecl] = heaps.values.map(h => LocalVarDecl(h.name, h.typ)).toSeq
  def currentStateVars: Seq[Var] = heaps.values.toSeq
  def currentStateExps: Seq[Exp] = heapExps


  override def freshTempState(name: String): Seq[Var] = {
    //Seq(LocalVar(Identifier(s"${name}Heap"), heapTyp))
    heapMap.map(h => LocalVar(Identifier(s"${name}Heap_${getResourceName(h._1)}"), if (h._1.isInstanceOf[sil.Field]) fheapTyp(translateType(h._1.asInstanceOf[sil.Field].typ)) else pheapTyp)).toSeq
  }

  override def restoreState(s: Seq[Var]): Unit = {
    heaps = heaps.zipWithIndex.map(z => z._1._1 -> s(z._2)).toMap // note: this should be accessed via heapVar or heapExp as appropriate (whether a variable is essential or not)
  }

  def equateWithCurrentHeap(s: Seq[Var]): Stmt ={
    Assume(All(heaps.values.zip(s).map(p => p._1 === p._2).toSeq))
  }

  override def usingOldState = stateModuleIsUsingOldState

  override def usingPureState = stateModuleIsUsingPureState

  override def beginExhale: Stmt = {
//    Havoc(exhaleHeap)
    Statements.EmptyStmt
  }

  override def endExhale: Stmt = {
    if (!usingOldState) exhaleHeapMap.map(eh => {
      val fname = if (eh._1.isInstanceOf[sil.Field]) (if (eh._1 == allocField) allocidenticalOnKnownLocsName else fidenticalOnKnownLocsName) else pidenticalOnKnownLocsName
      val ehStmt: Stmt  = (Havoc(eh._2) ++ Assume(FuncApp(fname, Seq(heapExp(eh._1), eh._2) ++ currentMask(eh._1), Bool)) ++ (heapVar(eh._1) := eh._2)).toSeq
      ehStmt
    }
    ).toSeq
    else Nil
  }

  /**
   * Reset the state of this module so that it can be used for new program. This method is called
   * after verifier gets a new program.
   */
  override def reset = {
    resources = cmpResources
    heapTypes = cmpHeapTypes
    heapMap = cmpHeapMap
    exhaleHeapMap = cmpExhaleHeapMap
    heaps = heapMap
  }

  override def currentHeap(r: sil.Resource) = heaps(r)

  override def identicalOnKnownLocations(r: sil.Resource, otherHeap: Seq[Exp], otherMask: Seq[Exp]): Exp = {
    val fname = if (r.isInstanceOf[sil.Field]) fidenticalOnKnownLocsName else pidenticalOnKnownLocsName
    FuncApp(fname, otherHeap ++ heapVars(r) ++ otherMask, Bool)
  }
}
