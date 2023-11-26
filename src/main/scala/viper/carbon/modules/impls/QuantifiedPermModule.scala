// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.modules.impls

import viper.carbon.modules._
import viper.carbon.modules.components._
import viper.silver.ast.utility.Expressions
import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.boogie.Implicits._
import viper.silver.verifier._
import viper.carbon.boogie.NamedType
import viper.carbon.boogie.MapSelect
import viper.carbon.boogie.LocalVarWhereDecl
import viper.carbon.boogie.Trigger
import viper.silver.verifier.PartialVerificationError
import viper.carbon.boogie.LocalVarDecl
import viper.carbon.boogie.Assume
import viper.carbon.boogie.RealLit
import viper.carbon.boogie.GlobalVar
import viper.carbon.boogie.GlobalVarDecl
import viper.carbon.boogie.Axiom
import viper.carbon.boogie.BinExp
import viper.carbon.boogie.MapType
import viper.carbon.boogie.Assert
import viper.carbon.boogie.ConstDecl
import viper.carbon.boogie.Const
import viper.carbon.boogie.LocalVar
import viper.silver.ast.{LocationAccess, PermMul, PredicateAccess, PredicateAccessPredicate, ResourceAccess, WildcardPerm}
import viper.carbon.boogie.Forall
import viper.carbon.boogie.Assign
import viper.carbon.boogie.Func
import viper.carbon.boogie.TypeAlias
import viper.carbon.boogie.FuncApp
import viper.carbon.utility.PolyMapDesugarHelper
import viper.carbon.verifier.Verifier
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.Implies

import scala.collection.mutable.ListBuffer
import viper.silver.ast.utility.QuantifiedPermissions.SourceQuantifiedPermissionAssertion
import viper.silver.verifier.errors.{ContractNotWellformed, PostconditionViolated}

/**
 * An implementation of [[viper.carbon.modules.PermModule]] supporting quantified permissions.
 */
class QuantifiedPermModule(val verifier: Verifier)
  extends PermModule
  with CarbonStateComponent
  with InhaleComponent
  with ExhaleComponent
  with TransferComponent
  with StmtComponent
  with DefinednessComponent {

  import verifier._
  import heapModule._
  import mainModule._
  import expModule._
  import stateModule._

  def name = "Permission module"

  override def start(): Unit = {
    stateModule.register(this)
    exhaleModule.register(this)
    inhaleModule.register(this)
    stmtModule.register(this, before = Seq(verifier.heapModule)) // allows this module to make checks for field write permission should before the operation itself (but adding permissions for new stmts is done afterwards - this is handled by the Heap module injecting code earlier)
    expModule.register(this)
    wandModule.register(this)
  }

  implicit val namespace = verifier.freshNamespace("perm")
  private val axiomNamespace = verifier.freshNamespace("perm.axiom")
  private val permTypeName = "Perm"
  private val maskTypeName = "MaskType"
  override val maskType = NamedType(maskTypeName)
  private val pmaskTypeName = "PMaskType"
  override val pmaskType = NamedType(pmaskTypeName)
  private val anyMaskName = Identifier("Mask")
  private val anyPMaskName = Identifier("PMask")
  //private val originalMask = GlobalVar(maskName, maskType)
  private var masks: Map[sil.Resource, Var] = _ // When reading, don't use this directly: use either maskVar or maskExp as needed
  private def maskVars : Map[sil.Resource, Var] = {assert (!usingOldState); masks}
  private def maskExps : Map[sil.Resource, Exp] = if (usingPureState) resources.map(r => r -> zeroMask).toMap else (if (usingOldState) resources.map(r => r -> Old(masks(r))).toMap else masks)
  private val zeroMaskName = Identifier("ZeroMask")
  private val zeroMask = Const(zeroMaskName)
  private val zeroPMaskName = Identifier("ZeroPMask")
  override val zeroPMask = Const(zeroPMaskName)
  private val noPermName = Identifier("NoPerm")
  val noPerm = Const(noPermName)
  private val fullPermName = Identifier("FullPerm")
  private val fullPerm = Const(fullPermName)
  private val permAddName = Identifier("PermAdd")
  private val permSubName = Identifier("PermSub")
  private val permDivName = Identifier("PermDiv")
  private val permConstructName = Identifier("Perm")
  private val goodMaskName = Identifier("GoodMask")
  private val goodFieldMaskName = Identifier("GoodFieldMask")


  private val resultMask = LocalVarDecl(Identifier("ResultMask"),maskType)
  private val summandMask1 = LocalVarDecl(Identifier("SummandMask1"),maskType)
  private val summandMask2 = LocalVarDecl(Identifier("SummandMask2"),maskType)
  private val sumMasks = Identifier("sumMask")
  private val presultMask = LocalVarDecl(Identifier("pResultMask"), pmaskType)
  private val psummandMask1 = LocalVarDecl(Identifier("pSummandMask1"), pmaskType)
  private val psummandMask2 = LocalVarDecl(Identifier("pSummandMask2"), pmaskType)
  private val psumMasks = Identifier("psumMask")
  private val tempMask = LocalVar(Identifier("TempMask"),maskType)
  private val ptempMask = LocalVar(Identifier("PTempMask"),pmaskType)

  private val qpMaskName = Identifier("QPMask")
  private val pqpMaskName = Identifier("pQPMask")
  private val qpMask = LocalVar(qpMaskName, maskType)
  private val pqpMask = LocalVar(pqpMaskName, pmaskType)
  private var qpId = 0 //incremented each time a quantified permission expression is inhaled/exhaled, used to deal with
  // wildcards, inverse functions of receiver expressions

  private val inverseFunName = "invRecv" //prefix of function name for inverse functions used for inhale/exhale of qp
  private val rangeFunName = "qpRange" //prefix of function name for range functions (image of receiver expressions) used for inhale/exhale of qp
  private val triggerFunName = "neverTriggered" //prefix of function name for trigger function used for inhale/exhale of qp
  private var inverseFuncs: ListBuffer[Func] = new ListBuffer[Func](); //list of inverse functions used for inhale/exhale qp
  private var rangeFuncs: ListBuffer[Func] = new ListBuffer[Func](); //list of inverse functions used for inhale/exhale qp
  private var triggerFuncs: ListBuffer[Func] = new ListBuffer[Func](); //list of inverse functions used for inhale/exhale qp
  private val addToMaskName = Identifier("addMask")
  private val paddToMaskName = Identifier("addPMask")

  private val readMaskName = Identifier("readMask")
  private val updateMaskName = Identifier("updMask")

  private val readPMaskName = Identifier("readPMask")
  private val updatePMaskName = Identifier("updPMask")
  private lazy val allocField = sil.Field("$allocated", sil.Bool)()

  override val pmaskTypeDesugared = PMaskDesugaredRep(readPMaskName, updatePMaskName)

  def cmpResources: Seq[sil.Resource] = Seq(allocField) ++  verifier.program.fields ++ verifier.program.predicates ++ verifier.program.magicWandStructures

  var resources: Seq[sil.Resource] = _

  def getMaskType(r: sil.Resource): Type = r match {
    case f: sil.Field => MapType(Seq(refType), permType, Seq())
    case _: sil.Predicate => MapType(Seq(funcPredModule.snapType()), permType, Seq())
    case _: sil.MagicWand => MapType(Seq(funcPredModule.snapType()), permType, Seq())
  }

  def cmpMaskTypes = resources.map(r => r -> getMaskType(r)).toMap

  var maskTypes: Map[sil.Resource, Type] = _

  def maskTypeMap: Map[sil.Resource, Type] = maskTypes

  def getResourceName(r: sil.Resource): String = r match {
    case f: sil.Field => f.name
    case p: sil.Predicate => p.name
    case w: sil.MagicWand => verifier.program.magicWandStructures.indexOf(w.structure(verifier.program)).toString
  }

  def cmpMaskMap: Map[sil.Resource, Var] = resources.map(r => r -> GlobalVar(Identifier(s"Mask_${getResourceName(r)}"), maskTypes(r))).toMap

  var maskMap: Map[sil.Resource, Var] = _



  def maskTypeForKey(t: Type) = MapType(Seq(t), permType, t.freeTypeVars)

  override def preamble = {
    val obj = LocalVarDecl(Identifier("o")(axiomNamespace), refType)
    val pred = LocalVarDecl(Identifier("p")(axiomNamespace), funcPredModule.snapType())
    val permInZeroMask = currentPermission(zeroMask, obj.l)
    val permInZeroPMask = currentPermission(zeroPMask, pred.l)

    // permission type
    TypeAlias(permType, Real) ::
      // mask and mask type
      (if (verifier.usePolyMapsInEncoding)
        TypeAlias(maskType, MapType(Seq(refType), permType))
      else TypeDecl(maskType)) ::
      (if (verifier.usePolyMapsInEncoding)
        TypeAlias(pmaskType, MapType(Seq(funcPredModule.snapType()), permType))
      else TypeDecl(pmaskType)) ::
      // zero mask
      ConstDecl(zeroMaskName, maskType) ::
      Axiom(Forall(
        Seq(obj),
        Trigger(permInZeroMask),
        (permInZeroMask === noPerm))) ::
      // zero pmask
      ConstDecl(zeroPMaskName, pmaskType) ::
      Axiom(Forall(
        Seq(pred),
        Trigger(permInZeroPMask),
        permInZeroPMask === noPerm)) ::
      // permission amount constants
      ConstDecl(noPermName, permType) ::
      Axiom(noPerm === RealLit(0)) ::
      ConstDecl(fullPermName, permType) ::
      Axiom(fullPerm === RealLit(1)) ::
      // permission constructor
      Func(permConstructName, Seq(LocalVarDecl(Identifier("a"), Real), LocalVarDecl(Identifier("b"), Real)), permType) :: Nil ++
      //read and update mask/pmask
      (if(!verifier.usePolyMapsInEncoding) {
        val maskPolyMapDesugarHelper = PolyMapDesugarHelper(refType, fieldTypeConstructor, namespace)
        val maskRep = maskPolyMapDesugarHelper.desugarPolyMap(maskType, (readMaskName, updateMaskName), _ => permType)
        val pmaskRep = maskPolyMapDesugarHelper.desugarPolyMap(pmaskType, (readPMaskName, updatePMaskName), _ => Bool)

        MaybeCommentedDecl("read and update permission mask",
          maskRep.select ++ maskRep.store ++ maskRep.axioms) ++
        MaybeCommentedDecl("read and update known-folded mask",
            pmaskRep.select ++ pmaskRep.store ++ pmaskRep.axioms)
      } else {
        Nil
      }) ++
      maskMap.map(m => GlobalVarDecl(m._2.name, m._2.typ)).toSeq ++
      {
        val h = LocalVarDecl(anyMaskName, maskType)
        val ph = LocalVarDecl(anyPMaskName, pmaskType)
        val obj = LocalVarDecl(Identifier("obj"), refType)
        val obj2 = LocalVarDecl(Identifier("obj2"), refType)
        val pred = LocalVarDecl(Identifier("pred"), funcPredModule.snapType())
        val pred2 = LocalVarDecl(Identifier("pred2"), funcPredModule.snapType())
        val prm = LocalVarDecl(Identifier("prm"), permType)


        val storeFun =
          Func(addToMaskName,
            Seq(h, obj, prm),
            maskType)


        val storeDefInner = Forall(Seq(obj2), Seq(Trigger(Seq(currentPermission(FuncApp(addToMaskName, Seq(h.l, obj.l, prm.l), maskType), obj2.l)))),  // , Trigger(Seq(currentPermission(h.l, obj2.l, field2.l)))), /// ME: trying, doesnt seem to help?
          currentPermission(FuncApp(addToMaskName, Seq(h.l, obj.l, prm.l), maskType), obj2.l) === BinExp(currentPermission(h.l, obj2.l), Add, CondExp(obj.l === obj2.l, prm.l, RealLit(0))))
        val storeDef = Axiom(Forall(Seq(h, obj, prm),
          Trigger(Seq(FuncApp(addToMaskName, Seq(h.l, obj.l, prm.l), maskType))),
          storeDefInner))

        val pstoreFun =
          Func(paddToMaskName,
            Seq(ph, pred, prm),
            pmaskType)


        val pstoreDefInner = Forall(Seq(pred2), Seq(Trigger(Seq(currentPermission(FuncApp(paddToMaskName, Seq(ph.l, pred.l, prm.l), pmaskType), pred2.l)))), // , Trigger(Seq(currentPermission(h.l, obj2.l, field2.l)))), /// ME: trying, doesnt seem to help?
          currentPermission(FuncApp(paddToMaskName, Seq(ph.l, pred.l, prm.l), pmaskType), pred2.l) === BinExp(currentPermission(ph.l, pred2.l), Add, CondExp(pred.l === pred2.l, prm.l, RealLit(0))))
        val pstoreDef = Axiom(Forall(Seq(ph, pred, prm),
          Trigger(Seq(FuncApp(paddToMaskName, Seq(ph.l, pred.l, prm.l), pmaskType))),
          pstoreDefInner))


        MaybeCommentedDecl("add to mask",
          storeFun ++ storeDef ++ pstoreFun ++ pstoreDef)
      } ++ {
      // good mask
      val mask = LocalVarDecl(anyMaskName, maskType)
      val pmask = LocalVarDecl(anyPMaskName, pmaskType)
      val goodMasks = resources.map {
        case r@(f: sil.Field) => FuncApp(goodFieldMaskName, Seq(maskMap(r)), Bool)
        case r => FuncApp(goodMaskName, Seq(maskMap(r)), Bool)
      }
      Func(goodMaskName, pmask, Bool) ++
      Func(goodFieldMaskName, mask, Bool) ++
      Axiom(Forall(stateModule.staticStateContributions(),
        Trigger(Seq(staticGoodState)),
        staticGoodState ==> All(goodMasks))) ++ {
      val m = LocalVarDecl(anyMaskName, maskType)
      val objPerm =  currentPermission(m.l, obj.l) //currentPermission(obj.l, field.l)
      val gfm = FuncApp(goodFieldMaskName, Seq(m.l), Bool)
      val pred = LocalVarDecl(Identifier("pred"), funcPredModule.snapType())
        val predPerm = currentPermission(pmask.l, pred.l) //currentPermission(obj.l, field.l)
        val gm = FuncApp(goodMaskName, Seq(pmask.l), Bool)
      Axiom(Forall(Seq(m, obj),
        Trigger(Seq(gfm, objPerm)),
        // permissions are non-negative
        (gfm ==> ( objPerm >= noPerm && objPerm <= fullPerm))
      ) && Forall(Seq(pmask, pred),
        Trigger(Seq(gm, predPerm)),
        // permissions are non-negative
        (gm ==> (predPerm >= noPerm))
      ))    }} ++
    {
      val obj = LocalVarDecl(Identifier("o")(axiomNamespace), refType)
      val pred = LocalVarDecl(Identifier("o")(axiomNamespace), funcPredModule.snapType())
      val args = Seq(resultMask,summandMask1,summandMask2)
      val pargs = Seq(presultMask,psummandMask1,psummandMask2)
      val funcApp = FuncApp(sumMasks, args map (_.l), Bool)
      val pfuncApp = FuncApp(psumMasks, pargs map (_.l), Bool)
      val permResult = currentPermission(resultMask.l, obj.l)
      val permSummand1 = currentPermission(summandMask1.l,obj.l)
      val permSummand2 = currentPermission(summandMask2.l,obj.l)
      val ppermResult = currentPermission(presultMask.l, pred.l)
      val ppermSummand1 = currentPermission(psummandMask1.l, pred.l)
      val ppermSummand2 = currentPermission(psummandMask2.l, pred.l)
      Func(sumMasks,args,Bool) ++
        Axiom(Forall(
          args++Seq(obj),
          Trigger(Seq(funcApp,permResult)) ++ Trigger(Seq(funcApp,permSummand1)) ++
            Trigger(Seq(funcApp,permSummand2)),
          funcApp ==> (permResult === (permSummand1 + permSummand2))
        )) ++
        Func(psumMasks, pargs, Bool) ++
        Axiom(Forall(
          pargs ++ Seq(pred),
          Trigger(Seq(pfuncApp, ppermResult)) ++ Trigger(Seq(pfuncApp, ppermSummand1)) ++
            Trigger(Seq(pfuncApp, ppermSummand2)),
          pfuncApp ==> (ppermResult === (ppermSummand1 + ppermSummand2))
        ))
    } ++ {
      MaybeCommentedDecl("Function for trigger used in checks which are never triggered",
        triggerFuncs.toSeq)
    } ++ {
      MaybeCommentedDecl("Functions used as inverse of receiver expressions in quantified permissions during inhale and exhale",
        inverseFuncs.toSeq)
    } ++ {
      MaybeCommentedDecl("Functions used to represent the range of the projection of each QP instance onto its receiver expressions for quantified permissions during inhale and exhale",
        rangeFuncs.toSeq)
    }
  }

  def permType = NamedType(permTypeName)

  def staticStateContributions(withHeap: Boolean, withPermissions: Boolean): Seq[LocalVarDecl] = if (withPermissions) maskMap.values.map(h => LocalVarDecl(h.name, h.typ)).toSeq else Seq()

  def staticStateContributions(withHeap: Boolean, withPermissions: Boolean, res: Set[sil.Resource]): Seq[LocalVarDecl] = if (withPermissions) maskMap.filter(m => res.contains(m._1)).values.map(h => LocalVarDecl(h.name, h.typ)).toSeq else Seq()

  def currentStateContributions: Seq[LocalVarDecl] = masks.values.map(h => LocalVarDecl(h.name, h.typ)).toSeq
  def currentStateVars : Seq[Var] = masks.values.toSeq
  def currentStateExps: Seq[Exp] = maskExps.values.toSeq

  def initBoogieState: Stmt = {
    masks = maskMap
    resetBoogieState
  }
  def resetBoogieState: Stmt = {
    if (resources == null)
      reset()
    val res : Stmt = masks.map{
      case (_: sil.Field, m) => m := zeroMask
      case (_, m) => m := zeroPMask
    }.toSeq
    res
  }
  def initOldState: Stmt = {
    maskVars.values.map(v => Assume(Old(v) === v)).toSeq
  }

  override def reset = {
    resources = cmpResources
    maskTypes = cmpMaskTypes
    maskMap = cmpMaskMap
    masks = maskMap
    qpId = 0
    inverseFuncs = new ListBuffer[Func]();
    rangeFuncs = new ListBuffer[Func]();
    triggerFuncs = new ListBuffer[Func]();
  }

  override def usingOldState = stateModuleIsUsingOldState

  override def usingPureState: Boolean = stateModuleIsUsingPureState

  //def staticGoodMask = FuncApp(goodMaskName, LocalVar(maskName, maskType), Bool)

  def goodMask(mask: Exp): Exp = FuncApp(goodMaskName, Seq(mask), Bool)
  def goodFieldMask(mask: Exp): Exp = FuncApp(goodFieldMaskName, Seq(mask), Bool)

  def assumeGoodMask(r: sil.Resource): Stmt = {
    val actualRes = r match {
      case mw: sil.MagicWand => mw.structure(program)
      case _ => r
    }
    val mask = maskExps(actualRes)
    val isGoodMask = r match {
      case _: sil.Field => goodFieldMask(mask)
      case _ => goodMask(mask)
    }
    Assume(isGoodMask)
  }

  private def permAdd(a: Exp, b: Exp): Exp = a + b
  private def permSub(a: Exp, b: Exp): Exp = a - b
  private def permDiv(a: Exp, b: Exp): Exp = a / b

  override def freshTempState(name: String): Seq[Var] = {
    ///Seq(LocalVar(Identifier(s"${name}Mask"), maskType))
    maskMap.map(m => LocalVar(Identifier(s"${name}Mask_${getResourceName(m._1)}"), if (m._1.isInstanceOf[sil.Field]) maskType else pmaskType)).toSeq
  }

  override def restoreState(s: Seq[Var]): Unit = {
    masks = masks.zipWithIndex.map(z => z._1._1 -> s(z._2)).toMap
  }

  override def hasDirectPerm(la: sil.ResourceAccess): Exp = {
    currentPermission(la) > noPerm
  }

  def hasDirectPerm(rcv: Exp, r: sil.Resource): Exp = {
    val mask = maskExps(r)
    currentPermission(mask, rcv) > noPerm
  }

  /**
    * Returns Boolean expression checking whether there is nonzero permission to the input location in the provided permission state.
    * The input location itself is translated in the original state (not in the provided permission state)
    * @param la input location
    * @param setToPermState permission state in which the permission is checked
    * @return
    */
  private def hasDirectPerm(la: sil.ResourceAccess, setToPermState: () => Unit): Exp = {
    val state = stateModule.state
    setToPermState()
    val res = hasDirectPerm(la)
    stateModule.replaceState(state)

    res
  }

  private def translateReceiver(la: sil.ResourceAccess) : Exp  = {
    la match {
      case sil.FieldAccess(rcv, _) => translateExp(rcv)
      case sil.PredicateAccess(args, _) => funcPredModule.silExpsToSnap(args)
      case w: sil.MagicWand => funcPredModule.silExpsToSnap(w.subexpressionsToEvaluate(program))
    }
  }

  /**
   * Expression that expresses that 'permission' is positive. 'silPerm' is used to
   * optimize the check if possible.
   */
  override def permissionPositive(permission: Exp, zeroOK : Boolean = false): Exp = permissionPositiveInternal(permission, None, zeroOK)

  private def permissionPositiveInternal(permission: Exp, silPerm: Option[sil.Exp] = None, zeroOK : Boolean = false): Exp = {
    (permission, silPerm) match {
      case (x, _) if permission == fullPerm => TrueLit()
      case (_, Some(sil.FullPerm())) => TrueLit()
      case (_, Some(sil.WildcardPerm())) => TrueLit()
      case (_, Some(sil.NoPerm())) => if (zeroOK) TrueLit() else FalseLit()
      case _ => if(zeroOK) permission >= noPerm else permission > noPerm
    }
  }

  override def issumMask(r: sil.Resource, summandMask1: Seq[Exp], summandMask2: Seq[Exp]): Exp = {
    val curMask = currentMask(r)
    if (r.isInstanceOf[sil.Field])
      fsumMask(curMask, summandMask1, summandMask2)
    else
      psumMask(curMask, summandMask1, summandMask2)
  }

  override def fsumMask(resultMask: Seq[Exp], summandMask1: Seq[Exp], summandMask2: Seq[Exp]): Exp =
    FuncApp(sumMasks, resultMask++summandMask1++summandMask2,Bool)

  override def psumMask(resultMask: Seq[Exp], summandMask1: Seq[Exp], summandMask2: Seq[Exp]): Exp =
    FuncApp(psumMasks, resultMask ++ summandMask1 ++ summandMask2, Bool)

  override def containsWildCard(e: sil.Exp): Boolean = {
    e match {
      case sil.AccessPredicate(loc, prm) =>
        val p = PermissionHelper.normalizePerm(prm)
        p.isInstanceOf[sil.WildcardPerm]
      case _ => false
    }
  }

  override def exhaleExp(e: sil.Exp, error: PartialVerificationError, definednessCheckOpt: Option[DefinednessState]): Stmt = {
    e match {
      case sil.AccessPredicate(loc: LocationAccess, prm) =>
        val curPerm = currentPermission(loc)
        val p = PermissionHelper.normalizePerm(prm)

        def subtractFromMask(permToExhale: Exp) : Stmt =
          (if (!usingOldState) currentMaskAssignUpdate(loc, permSub(curPerm, permToExhale)) else Nil)

        val permVar = LocalVar(Identifier("perm"), permType)
        if (!p.isInstanceOf[sil.WildcardPerm]) {
          val prmTranslated = translatePerm(p)
          val permValToUse = prmTranslated match {
            case `fullPerm` => prmTranslated
            case l: RealLit => prmTranslated
            case _ => permVar
          }

            (permVar := prmTranslated) ++
              Assert(permissionPositiveInternal(permVar, Some(p), true), error.dueTo(reasons.NegativePermission(p))) ++
            If(permVar !== noPerm,
              Assert(permLe(permVar, curPerm), error.dueTo(reasons.InsufficientPermission(loc))),
              Nil) ++
            subtractFromMask(permValToUse) ++
            assumeGoodMask(loc.res(program))
        } else {
          val curPerm = currentPermission(loc)
          val wildcard = LocalVar(Identifier("wildcard"), Real)

          Assert(curPerm > noPerm, error.dueTo(reasons.InsufficientPermission(loc))) ++
            LocalVarWhereDecl(wildcard.name, wildcard > noPerm) ++
            Havoc(wildcard) ++
            Assume(wildcard < curPerm) ++
            subtractFromMask(wildcard) ++
            assumeGoodMask(loc.res(program))
        }
      case w@sil.MagicWand(_,_) =>
        val args = w.subexpressionsToEvaluate(program).map(translateExp)
        val rcv = funcPredModule.toSnap(args)
        val wstruct = w.structure(program)
        val curPerm = currentPermission(rcv, wstruct)
        Comment("permLe")++
          Assert(permLe(fullPerm, curPerm), error.dueTo(reasons.MagicWandChunkNotFound(w))) ++
          (if (!usingOldState) currentMaskAssignUpdate(rcv, wstruct, permSub(curPerm, fullPerm)) ++ assumeGoodMask(w) else Nil)

      case fa@sil.Forall(v, cond, expr) =>

        if (fa.isPure) {
          Nil
        } else {
          //Quantified Permission
          val stmt = translateExhale(fa, error)
          stmt
        }
      case _ => Nil
    }
  }


  /*For QP \forall x:T :: c(x) ==> acc(e(x),p(x)) this case class describes an instantiation of the QP where
   * cond = c(expr), recv = e(expr) and perm = p(expr) and expr is of type T and may be dependent on the variable given by v. */
  case class QuantifiedFieldComponents( translatedVar:LocalVarDecl,
                                        translatedCondcond: Exp,
                                        translatedRcv: Exp,
                                        translatedPerm: Exp,
                                        translatedLoc:sil.Resource)
  case class QuantifiedFieldInverseComponents(condInv: Exp,
                                             recvInv: Exp,
                                              invFun:Exp,
                                              obj:Exp,
                                              field:Exp)

  private def conservativeIsWildcardPermission(perm: sil.Exp) : Boolean = {
    perm match {
      case WildcardPerm() | PermMul(WildcardPerm(), WildcardPerm()) => true
      case PermMul(e, WildcardPerm()) => conservativeIsPositivePerm(e)
      case PermMul(WildcardPerm(), e)  => conservativeIsPositivePerm(e)
      case _ => false
    }
  }

  /**
    * translates given quantified field access predicate to Boogie components needed for translation of the statement
    */
  def translateFieldAccessComponents(v:sil.LocalVarDecl, cond:sil.Exp, fieldAccess:sil.FieldAccess, perms:sil.Exp): (QuantifiedFieldComponents, Boolean, LocalVar, Stmt) = {
        val newV = env.makeUniquelyNamed(v);
        env.define(newV.localVar);

        //replaces components with unique localVar
        def renaming[E <: sil.Exp] = (e:E) => Expressions.renameVariables(e, v.localVar, newV.localVar)

        //translate components
        val translatedLocal = translateLocalVarDecl(newV)
        val translatedCond = translateExp(renaming(cond))
        val translatedRcv = translateExp(renaming(fieldAccess.rcv))
        //val translatedLocation = translateLocation(renaming(fieldAccess))

        //translate Permission and create Stmts and Local Variable if wildcard permission
        var isWildcard = false
        val (translatedPerms, stmts, wildcard) = {
          if (conservativeIsWildcardPermission(perms)) {
            isWildcard = true
            val w = LocalVar(Identifier("wildcard"), Real)
            (w, LocalVarWhereDecl(w.name, w > RealLit(0)) :: Havoc(w) :: Nil, w)
          } else {
            (translateExp(renaming(perms)), Nil, null)
          }
        }

        //return values: Quantified Field Components, wildcard
        (QuantifiedFieldComponents(translateLocalVarDecl(newV), translatedCond, translatedRcv, translatedPerms, fieldAccess.field),
          isWildcard,
          wildcard,
          stmts)
  }

  def translateExhale(e: sil.Forall, error: PartialVerificationError): Stmt =  {
    val stmt = e match {
      case SourceQuantifiedPermissionAssertion(forall, Implies(cond, expr))  =>
        val vs = forall.variables

        val res = expr match {
          case sil.FieldAccessPredicate(fieldAccess@sil.FieldAccess(recv, f), perms) =>
            // alpha renaming, to avoid clashes in context, use vFresh instead of v
            val vsFresh = vs.map(v => {
              val vFresh = env.makeUniquelyNamed(v)
              env.define(vFresh.localVar)
              vFresh
            })

            var isWildcard = false
            def renaming[E <: sil.Exp] = (e:E) => Expressions.renameVariables(e, vs.map(v => v.localVar), vsFresh.map(v => v.localVar))
            val (renamingCond, renamingRecv, renamingPerms, renamingFieldAccess) = (renaming(cond), renaming(recv), renaming(perms), renaming(fieldAccess))
            val renamedTriggers:Seq[sil.Trigger] = e.triggers.map(trigger => sil.Trigger(trigger.exps.map(x => renaming(x)))(trigger.pos, trigger.info))

            //translate components
            val (translatedCond, translatedRecv) = (translateExp(renamingCond), translateExp(renamingRecv))
            val translatedLocals = vsFresh.map(v => translateLocalVarDecl(v))
            val (translatedPerms, stmts, wildcard) = {
              if (conservativeIsWildcardPermission(perms)) {
                isWildcard = true
                val w = LocalVar(Identifier("wildcard"), Real)
                (w, LocalVarWhereDecl(w.name, w > RealLit(0)) :: Havoc(w) :: Nil, w)
              } else {
                (translateExp(renamingPerms), Nil, null)
              }
            }
            val translatedTriggers:Seq[Trigger] = renamedTriggers.map(trigger => (Trigger(trigger.exps.map(x => translateExp(x)))))

            val obj = LocalVarDecl(Identifier("o"), refType) // ref-typed variable, representing arbitrary receiver
            val curPerm:Exp = currentPermission(obj.l,f)
            val (invFuns,rangeFun,triggerFun) = addQPFunctions(translatedLocals)
            val invFunApps = invFuns.map(ifun => FuncApp(ifun.name, Seq(obj.l), ifun.typ) )
            val rangeFunApp = FuncApp(rangeFun.name, Seq(obj.l), rangeFun.typ) // range(o): used to test whether an element of the mapped-to type is in the image of the QP's domain, projected by the receiver expression
            val rangeFunRecvApp = FuncApp(rangeFun.name, Seq(translatedRecv), rangeFun.typ) // range(e(v))
            //define new function, for expressions which do not need to be triggered (injectivity assertion)
            val triggerFunApp = FuncApp(triggerFun.name,translatedLocals.map(v => LocalVar(v.name, v.typ)), triggerFun.typ)

            // applications of the functions with v replaced by inv(o)
            var condInv = translatedCond
            var rcvInv = translatedRecv
            var permInv = translatedPerms
            for (i <- 0 until (invFuns.length)){
              condInv = condInv.replace(env.get(vsFresh(i).localVar), invFunApps(i))
              rcvInv = rcvInv.replace(env.get(vsFresh(i).localVar), invFunApps(i))
              permInv = permInv.replace(env.get(vsFresh(i).localVar), invFunApps(i))
            }

            //Trigger for first inverse function. If user-defined triggers are provided, (only) these are used. Otherwise, those auto-generated + triggers corresponding to looking up the location are chosen
            val recvTrigger = Trigger(Seq(translatedRecv))

            lazy val candidateTriggers : Seq[Trigger] = if (validateTrigger(translatedLocals,recvTrigger).isEmpty) // if we can't use the receiver, maybe we can use H[recv,field] etc..
              validateTriggers(translatedLocals,Seq(Trigger(Seq(translateLocationAccess(translatedRecv, f))),Trigger(Seq(currentPermission(qpMask,translatedRecv))))) else Seq(recvTrigger)

            val providedTriggers : Seq[Trigger] = validateTriggers(translatedLocals, translatedTriggers)

            val tr1: Seq[Trigger] = funcPredModule.rewriteTriggersToExpressionsUsedInTriggers(candidateTriggers ++ providedTriggers)


            //inverse assumptions
            var assm1Rhs : Exp = rangeFunRecvApp
            for (i <- 0 until invFuns.length) {
              assm1Rhs = assm1Rhs && FuncApp(invFuns(i).name, Seq(translatedRecv), invFuns(i).typ) === translatedLocals(i).l
            }
            // b(x) && p(x) > 0 ==> inv(e(x)) == x && range(e(x))
            val invAssm1 = Forall(translatedLocals, tr1, (translatedCond && permGt(translatedPerms, noPerm)) ==> assm1Rhs)
            // b(inv(r)) && p(inv(r)) > 0 && range(r) ==> (e(inv(r)) == r
            val invAssm2 = Forall(Seq(obj), Trigger(invFuns.map(invFun => FuncApp(invFun.name, Seq(obj.l), invFun.typ))), (condInv && (permGt(permInv, noPerm) && rangeFunApp)) ==> (rcvInv === obj.l) )


            //check that given the condition, the permission held should be non-negative
            val permPositive = Assert(Forall(vsFresh.map(v => translateLocalVarDecl(v)),tr1, (translatedCond && funcPredModule.dummyFuncApp(translateLocationAccess(translatedRecv, f))) ==> permissionPositiveInternal(translatedPerms,None,true)),
              error.dueTo(reasons.NegativePermission(perms)))

            //define permission requirement
            val permNeeded =
              if(isWildcard) {
            currentPermission(translatedRecv, f) > noPerm
              } else {
                currentPermission(translatedRecv, f) >= translatedPerms
              }

            //assert that we possess enough permission to exhale the permission indicated
            val enoughPerm = Assert(Forall(vsFresh.map(vFresh => translateLocalVarDecl(vFresh)), tr1, translatedCond ==> permNeeded),
              error.dueTo(reasons.InsufficientPermission(fieldAccess)))

            //if the permission is a wildcard, we check that we have some permission > 0 for all locations and assume that the permission substracted is smaller than the permission held.
            val wildcardAssms:Stmt =
              if(isWildcard) {
                (Assert(Forall(vsFresh.map(v => translateLocalVarDecl(v)), Seq(), translatedCond ==> (currentPermission(translatedRecv, f) > noPerm)), error.dueTo(reasons.InsufficientPermission(fieldAccess))))++
                  (Assume(Forall(vsFresh.map(v => translateLocalVarDecl(v)), Seq(), translatedCond ==> (wildcard < currentPermission(translatedRecv, f)))))
              } else {
                Nil
              }

            //assumptions for locations that gain permission
            val condTrueLocations = (condInv && (permGt(permInv, noPerm) && rangeFunApp)) ==> ((rcvInv === obj.l) && (
              (if (!usingOldState) {
                (  currentPermission(qpMask,obj.l) === curPerm - permInv )
              } else {
                currentPermission(qpMask,obj.l) === curPerm
              } )
              ))

            //assumption for locations that don't gain permission
            val condFalseLocations = ((condInv && (permGt(permInv, noPerm) && rangeFunApp)).not ==> (currentPermission(qpMask,obj.l) === curPerm))

            val triggersForPermissionUpdateAxiom = Seq(Trigger(currentPermission(qpMask,obj.l)))

            //injectivity assertion
            val v2s = translatedLocals.map(translatedLocal => LocalVarDecl(Identifier(translatedLocal.name.name), translatedLocal.typ))
            var triggerFunApp2 : FuncApp = triggerFunApp
            var notEquals : Exp = TrueLit()
            var translatedPerms2 = translatedPerms
            var translatedCond2 = translatedCond
            var translatedRecv2 = translatedRecv
            for (i <- 0 until translatedLocals.length){
              triggerFunApp2 = triggerFunApp2.replace(translatedLocals(i).l, v2s(i).l)
              translatedPerms2 = translatedPerms2.replace(translatedLocals(i).l, v2s(i).l)
              translatedCond2 = translatedCond2.replace(translatedLocals(i).l, v2s(i).l)
              translatedRecv2 = translatedRecv2.replace(translatedLocals(i).l, v2s(i).l)
              notEquals = notEquals && (translatedLocals(i).l !== v2s(i).l)
            }
            val is_injective = Forall( translatedLocals++v2s,validateTriggers(translatedLocals++v2s, Seq(Trigger(Seq(triggerFunApp, triggerFunApp2)))),(  notEquals &&  translatedCond && translatedCond2 && permGt(translatedPerms, noPerm) && permGt(translatedPerms2, noPerm)) ==> (translatedRecv !== translatedRecv2))
            val reas = reasons.QPAssertionNotInjective(fieldAccess)
            var err = error.dueTo(reas)
            err = err match {
              case PostconditionViolated(_, _, _, _) => ContractNotWellformed(e, reas)
              case _ => err
            }
            val injectiveAssertion = Assert(is_injective, err)

            val res1 = Havoc(qpMask) ++
              MaybeComment("wild card assumptions", stmts ++
              wildcardAssms) ++
              CommentBlock("check that the permission amount is positive", permPositive) ++
              CommentBlock("check if receiver " + recv.toString() + " is injective",injectiveAssertion) ++
              CommentBlock("check if sufficient permission is held", enoughPerm) ++
              CommentBlock("assumptions for inverse of receiver " + recv.toString(), Assume(invAssm1)++ Assume(invAssm2)) ++
              CommentBlock("assume permission updates for field " + f.name, Assume(Forall(obj,triggersForPermissionUpdateAxiom, condTrueLocations && condFalseLocations ))) ++
              (masks(f) := qpMask)

            vsFresh.foreach(v => env.undefine(v.localVar))

            res1
          //Predicate access
          case accPred: sil.AccessPredicate =>
            val qpMask = LocalVar(Identifier("pqpMask"), pmaskType)
            // alpha renaming, to avoid clashes in context, use vFresh instead of v
            val vsFresh = vs.map(v => env.makeUniquelyNamed(v))
            val vsFreshBoogie = vsFresh.map(vFresh => env.define(vFresh.localVar))
            // create fresh variables for the formal arguments of the predicate definition
            val (formals, args, resource) = accPred match {
              case sil.PredicateAccessPredicate(sil.PredicateAccess(args, predname), _) =>
                val predicate = program.findPredicate(predname)
                (predicate.formalArgs, args, predicate)
              case w: sil.MagicWand =>
                val subExps = w.subexpressionsToEvaluate(program)
                val formals = subExps.zipWithIndex.map { case (arg, i) => sil.LocalVarDecl(s"arg_$i", arg.typ)() }
                (formals, subExps, w.structure(program))
            }
            val perms = accPred.perm
            val freshFormalDecls : Seq[sil.LocalVarDecl] = formals.map(env.makeUniquelyNamed)
            var freshFormalVars : Seq[sil.LocalVar] = freshFormalDecls.map(d => d.localVar)
            val freshFormalBoogieVars = freshFormalVars.map(x => env.define(x))
            val freshFormalBoogieDecls = freshFormalVars.map(x => LocalVarDecl(env.get(x).name, typeModule.translateType(x.typ)))

            var isWildcard = false
            def renamingQuantifiedVar[E <: sil.Exp] = (e:E) => Expressions.renameVariables(e, vs.map(v => v.localVar), vsFresh.map(vFresh => vFresh.localVar))
            def renamingIncludingFormals[E <: sil.Exp] = (e:E) => Expressions.renameVariables(e, (vs.map(v => v.localVar) ++ formals.map(_.localVar)), (vsFresh.map(vFresh => vFresh.localVar) ++ freshFormalVars))
            val (renamedCond,renamedPerms) = (renamingQuantifiedVar(cond),renamingQuantifiedVar(perms))
            var renamedArgs = args.map(a => renamingQuantifiedVar(a))
            var renamedTriggers = e.triggers.map(trigger => sil.Trigger(trigger.exps.map(x => renamingQuantifiedVar(x)))(trigger.pos, trigger.info))

            //translate components
            val translatedLocals = vsFresh.map(vFresh => translateLocalVarDecl(vFresh))  // quantified variable
            val translatedCond = translateExp(renamedCond)
            val translatedArgs = renamedArgs.map(translateExp)
            val argSnap = funcPredModule.toSnap(translatedArgs)
            val (translatedPerms, stmts, wildcard) = {
              if (conservativeIsWildcardPermission(perms)) {
                isWildcard = true
                val w = LocalVar(Identifier("wildcard"), Real)
                (w, LocalVarWhereDecl(w.name, w > RealLit(0)) :: Havoc(w) :: Nil, w)
              } else {
                (translateExp(renamedPerms), Nil, null)
              }
            }
            val translatedTriggers : Seq[Trigger] = renamedTriggers.map(trigger => Trigger(trigger.exps.map(x => translateExp(x))))

            //define inverse function
            val (invFuns, rangeFun, triggerFun) = addQPFunctions(translatedLocals, freshFormalBoogieDecls)

            val funApps = invFuns.map(invFun => FuncApp(invFun.name, translatedArgs, invFun.typ))
            val invFunApps = invFuns.map(invFun => FuncApp(invFun.name, freshFormalBoogieVars, invFun.typ))

            //define new function, for expressions which do not need to be triggered (injectivity assertion)
            val triggerFunApp = FuncApp(triggerFun.name, translatedLocals.map(translatedLocal => LocalVar(translatedLocal.name, translatedLocal.typ)), triggerFun.typ)

            //replace all occurrences of the originally-bound variable with occurrences of the inverse function application
            var condInv = translatedCond
            var argsInv = translatedArgs
            var permInv = translatedPerms
            for (i <- 0 until (invFuns.length)){
              condInv = condInv.replace(translatedLocals(i).l, invFunApps(i))
              argsInv = argsInv.map(a => a.replace(translatedLocals(i).l, invFunApps(i)))
              permInv = permInv.replace(translatedLocals(i).l, invFunApps(i))
            }
            val curPerm = currentPermission(accPred.loc)
            //val translatedLocation = translateLocation(predAccPred.loc)

            val rangeFunApp = FuncApp(rangeFun.name, freshFormalBoogieVars, rangeFun.typ) // range(o,...): used to test whether an element of the mapped-to type is in the image of the QP's domain, projected by the receiver expression
            val rangeFunRecvApp = FuncApp(rangeFun.name, translatedArgs, rangeFun.typ) // range(e(v),...)

            //define inverse functions
            lazy val candidateTriggers : Seq[Trigger] = validateTriggers(translatedLocals, Seq(Trigger(translateLocationAccess(accPred.loc)),Trigger(currentPermission(argSnap, accPred.res(program)))))

            val providedTriggers : Seq[Trigger] = validateTriggers(translatedLocals, translatedTriggers)

            val tr1: Seq[Trigger] = funcPredModule.rewriteTriggersToExpressionsUsedInTriggers(candidateTriggers ++ providedTriggers)

            var equalities : Exp =  TrueLit()
            for (i <- 0 until funApps.length) {
              equalities = equalities && (funApps(i) === translatedLocals(i).l)
            }

            val invAssm1 = Forall(translatedLocals, tr1, (translatedCond && permGt(translatedPerms, noPerm)) ==> (equalities && rangeFunRecvApp))
            //for each argument, define the second inverse function
            val eqExpr = (argsInv zip freshFormalBoogieVars).map(x => x._1 === x._2)
            val conjoinedInverseAssumptions = eqExpr.foldLeft(TrueLit():Exp)((soFar,exp) => BinExp(soFar,And,exp))
            val invAssm2 = Forall(freshFormalBoogieDecls, Trigger(invFunApps), ((condInv && permGt(permInv, noPerm)) && rangeFunApp) ==> conjoinedInverseAssumptions)

            //check that the permission expression is non-negative for all predicates satisfying the condition
            val permPositive = Assert(Forall(freshFormalBoogieDecls, Trigger(invFunApps), (condInv && rangeFunApp) ==> permissionPositive(permInv, true)),
              error.dueTo(reasons.NegativePermission(perms)))

            //check that sufficient permission is held
            val permNeeded =
              if(isWildcard) {
                (currentPermission(argSnap, accPred.res(program)) > RealLit(0))
              } else {
                (currentPermission(argSnap, accPred.res(program)) >= translatedPerms)
              }

            val reason = accPred match {
              case pap: sil.PredicateAccessPredicate =>
                reasons.InsufficientPermission(pap.loc)
              case w: sil.MagicWand =>
                reasons.MagicWandChunkNotFound(w)
            }
            val enoughPerm = Assert(Forall(translatedLocals, tr1, translatedCond ==> permNeeded),
              error.dueTo(reason))

            //if we exhale a wildcard permission, assert that we hold some permission to all affected locations and restrict the wildcard value
            val wildcardAssms:Stmt =
              if(isWildcard) {
                Assert(Forall(translatedLocals, Seq(), translatedCond ==> (currentPermission(argSnap, resource) > noPerm)), error.dueTo(reason)) ++
                  Assume(Forall(translatedLocals, Seq(), translatedCond ==> (wildcard < currentPermission(argSnap, resource))))
              } else {
                Nil
              }

            //Assume map update for affected locations
            val general_snap = funcPredModule.toSnap(freshFormalBoogieVars)//LocalVarDecl(Identifier("general_snap"), funcPredModule.snapType())

            //trigger:
            val triggerForPermissionUpdateAxioms = Seq(Trigger(currentPermission(qpMask,general_snap)) /*,Trigger(currentPermission(mask, translateNull, general_location)),Trigger(invFunApp)*/ )
            val permissionsMap = Assume(Forall(freshFormalBoogieDecls,triggerForPermissionUpdateAxioms, ((condInv && (permGt(permInv, noPerm)) && rangeFunApp) ==> (conjoinedInverseAssumptions && (currentPermission(qpMask,general_snap) === currentPermission(general_snap, resource) - permInv)))))

            //Assume no change for independent locations: different predicate or no predicate
            val independentLocations = Assume(Forall(freshFormalBoogieDecls, Seq(Trigger(currentPermission(general_snap, resource)), Trigger(currentPermission(qpMask, general_snap))),
              ((general_snap !== argSnap ))  ==>
                (currentPermission(argSnap, resource) === currentPermission(qpMask,argSnap))))
            //same predicate, but not satisfying the condition
            val independentPredicate = Assume(Forall(freshFormalBoogieDecls, triggerForPermissionUpdateAxioms, ((condInv && (permGt(permInv, noPerm)) && rangeFunApp).not) ==> (currentPermission(qpMask,general_snap) === currentPermission(general_snap, resource))))


            //AS: TODO: it would be better to use the Boogie representation of a predicate instance as the canonical representation here (i.e. the function mapping to a field in the Boogie heap); this would avoid the disjunction of arguments used below. In addition, this could be used as a candidate trigger in tr1 code above. See issue 242
            //assert injectivity of inverse function:
            val translatedLocals2 = translatedLocals.map(translatedLocal => LocalVarDecl(Identifier(translatedLocal.name.name), translatedLocal.typ)) //new varible

            var unequalities : Exp = TrueLit()
            var translatedCond2 = translatedCond
            var translatedPerms2 = translatedPerms
            var translatedArgs2 = translatedArgs
            var triggerFunApp2 = triggerFunApp
            for (i <- 0 until translatedLocals.length) {
              unequalities = unequalities && (translatedLocals(i).l.!==(translatedLocals2(i).l))
              translatedCond2 = translatedCond2.replace(translatedLocals(i).l, translatedLocals2(i).l)
              translatedPerms2 = translatedPerms2.replace(translatedLocals(i).l, translatedLocals2(i).l)
              translatedArgs2 = translatedArgs2.map(a => a.replace(translatedLocals(i).l, translatedLocals2(i).l))
              triggerFunApp2 = triggerFunApp2.replace(translatedLocals(i).l, translatedLocals2(i).l)
            }

            val injectiveCond = unequalities && translatedCond && translatedCond2 && permGt(translatedPerms, noPerm) && permGt(translatedPerms2, noPerm);
            //val translatedArgs2= translatedArgs.map(x => x.replace(translatedLocal.l, translatedLocal2.l))
            val ineqs = (translatedArgs zip translatedArgs2).map(x => x._1 !== x._2)
            val ineqExpr = {
              if (ineqs.isEmpty) FalseLit()
              else ineqs.reduce((expr1, expr2) => (expr1) || (expr2))
            }
            val injectTrigger = Seq(Trigger(Seq(triggerFunApp, triggerFunApp2)))

            val reas = reasons.QPAssertionNotInjective(accPred.loc)
            var err = error.dueTo(reas)
            err = err match {
              case PostconditionViolated(_, _, _, _) => ContractNotWellformed(e, reas)
              case _ => err
            }
            val injectiveAssertion = Assert(Forall((translatedLocals ++ translatedLocals2), injectTrigger,injectiveCond ==> ineqExpr), err)

            val res1 = Havoc(qpMask) ++
              MaybeComment("wildcard assumptions", stmts ++
              wildcardAssms) ++
              CommentBlock("check that the permission amount is positive", permPositive) ++
              CommentBlock("check if receiver " + accPred.toString() + " is injective",injectiveAssertion) ++
              CommentBlock("check if sufficient permission is held", enoughPerm) ++
              CommentBlock("assumptions for inverse of receiver " + accPred.toString(), Assume(invAssm1)++ Assume(invAssm2)) ++
              CommentBlock("assume permission updates for resource ", permissionsMap ++
              independentPredicate) ++
              CommentBlock("assume permission updates for independent locations ", independentLocations) ++
              (masks(resource) := qpMask)

            vsFresh.foreach(vFresh => env.undefine(vFresh.localVar))
            freshFormalDecls.foreach(x => env.undefine(x.localVar))
            res1
          case _ =>
            if (expr.isPure) {
              val forall = sil.Forall(vs, Seq(), sil.Implies(cond, expr)(cond.pos, cond.info))(expr.pos, expr.info)
              Assert(translateExp(forall), error.dueTo(reasons.AssertionFalse(expr))) ++ Nil
            } else {
              Nil
            }
        }
        val resource = expr match {
          case w: sil.MagicWand => w.structure(program)
          case ap: sil.AccessPredicate => ap.res(program)
        }
        res ++ assumeGoodMask(resource)
      case _ => Nil
      //Field Access

    }
    stmt
  }

  /*
* Gaurav (03.04.15): this basically is a simplified exhale so some code is duplicated,
* I haven't yet found a nice way of avoiding the code duplication
*/
  override def transferRemove(e:TransferableEntity, cond:Exp): Stmt = {
    val permVar = LocalVar(Identifier("perm"), permType)
    val curPerm = currentPermission(e.rcv,e.resource)
    currentMaskAssignUpdate(e.rcv, e.resource, permSub(curPerm,e.transferAmount))
  }

  override def transferValid(e:TransferableEntity):Seq[(Stmt,Exp)] = {
    Nil
  }

  override def inhaleExp(e: sil.Exp, error: PartialVerificationError): Stmt = {
    inhaleAux(e, Assume, error)
  }

  override def inhaleWandFt(w: sil.MagicWand): Stmt = {
    val rcv = funcPredModule.toSnap(w.args.map(translateExp))
    val res = w.structure(program)
    val curPerm = currentPermission(maskExps(res), rcv)
    if (!usingOldState) currentMaskAssignUpdate(rcv, res, permAdd(curPerm, fullPerm)) else Nil
  }

  override def exhaleWandFt(w: sil.MagicWand): Stmt = {
    val rcv = funcPredModule.toSnap(w.args.map(translateExp))
    val res = w.structure(program)
      val curPerm = currentPermission(maskExps(res), rcv)
      (if (!usingOldState) currentMaskAssignUpdate(rcv, res, permSub(curPerm, fullPerm)) else Nil)
  }

  /*
   * same as the original inhale except that it abstracts over the way assumptions are expressed in the
   * Boogie program
   * Note: right now (05.04.15) inhale AND transferAdd both use this function
   */
  private def inhaleAux(e: sil.Exp, assmsToStmt: Exp => Stmt, error: PartialVerificationError):Stmt = {
    e match {
      case sil.AccessPredicate(loc: LocationAccess, prm) =>
        val perm = PermissionHelper.normalizePerm(prm)
        val curPerm = currentPermission(loc)
        val permVar = LocalVar(Identifier("perm"), permType)

        /*
      case sil.AccessPredicate(loc: LocationAccess, prm) =>
        val p = PermissionSplitter.normalizePerm(prm)
        val perms = PermissionSplitter.splitPerm(p) filter (x => x._1 - 1 == exhaleModule.currentPhaseId)
        (if (exhaleModule.currentPhaseId == 0)
          (if (!p.isInstanceOf[sil.WildcardPerm])
            Assert(permissionPositiveInternal(translatePerm(p), Some(p), true), error.dueTo(reasons.NegativePermission(p))) else Nil: Stmt) ++ Nil // check amount is non-negative
        else Nil) ++
         */



        val (permVal, stmts): (Exp, Stmt) =
          if (perm.isInstanceOf[WildcardPerm]) {
            val w = LocalVar(Identifier("wildcard"), Real)
            (w, LocalVarWhereDecl(w.name, w > noPerm) :: Havoc(w) :: Nil)
          } else {
            (translatePerm(perm), Nil)
          }
        val permValToUse = permVal match {
          case `fullPerm` => permVal
          case l: RealLit => permVal
          case _ => permVar
        }
        stmts ++
         (permVar := permVal) ++
          (if (perm.isInstanceOf[WildcardPerm])
            assmsToStmt(checkNonNullReceiver(loc))
          else
            Assert(permissionPositiveInternal(permVar, Some(perm), true), error.dueTo(reasons.NegativePermission(perm))) ++
            assmsToStmt(permissionPositiveInternal(permVar, Some(perm), false) ==> checkNonNullReceiver(loc))
          ) ++
          (if (!usingOldState) currentMaskAssignUpdate(loc, permAdd(curPerm, permValToUse)) else Nil) ++
          (assumeGoodMask(loc.res(program)))
      case w@sil.MagicWand(left,right) =>
        val args = funcPredModule.silExpsToSnap(w.subexpressionsToEvaluate(program))
        val wandStruct = w.structure(program)
        val curPerm = currentPermission(args, wandStruct)
        (if (!usingOldState) currentMaskAssignUpdate(args, wandStruct, permAdd(curPerm, fullPerm)) ++ assumeGoodMask(w) else Nil)
      //Quantified Permission Expression
      case fa@sil.Forall(_, _, _) =>
        if (fa.isPure) {
          Nil
        } else {
          //Quantified Permission
          val stmt:Stmt = translateInhale(fa, error)
          stmt ++ Nil
        }
      case _ => Nil

    }
  }

  var varMap:Map[Identifier,Boolean] = Map()

  def containVars(n:Node): Unit = {
    if (n.isInstanceOf[Var]) {
      varMap+= (n.asInstanceOf[Var].name -> true)
    }

    for (sub <- n.subnodes ) {
      containVars(sub)
    }
  }

  /*
      Checks whether the trigger is of a type accepted by Boogie. These can be: any Var and Constants, MapSelect and Function App (considering their arguments itself are valid)
      and Binary Expressions
   */
  def validTriggerTypes(exp:Exp): Boolean = {
    exp match {
      case LocalVar(_, _) => true
      case GlobalVar(_, _) => true
      case Const(_) => true
      case IntLit(_) => true
      case RealLit(_) => true
      case BoolLit(_) => true

      case MapSelect(_, idxs) => idxs.map(validTriggerTypes).reduce((b1, b2) => b1 && b2)
      case MapUpdate(_, idxs, value) => idxs.map(validTriggerTypes).reduce((b1, b2) => b1 && b2) && validTriggerTypes(value)
      case FuncApp(_, args, _) => if (args.isEmpty) false else args.map(validTriggerTypes).reduce((b1, b2) => b1 && b2)
      /* BinExp should be refined to Add, Sub, Mul, Div, Mod. user-triggers will not be allowed invalid types.
         other triggers should not be generated.
      */
      //case BinExp(_, _, _) => false // operators cause unreliable behaviour in Z3
      case _ => false
    }
  }

  /*
       checks if the set of expressions conforms to a valid trigger in Boogie:
       - A matching pattern/expression must be more than just a variable by itself
       - only contains permitted types of expressions

   */
  def validTrigger(vars:Seq[LocalVarDecl], exps:Seq[Exp]) : Boolean = {
    varMap = Map()
    //Main-Node
    var validType = true
    for (expr <- exps) {
      //not only LocalVar
      if (expr.isInstanceOf[LocalVar]) {
        validType = false;
      }
      if (!validTriggerTypes(expr)) {
        validType = false
      }
      //map occurring LocalVars
      containVars(expr)
    }
    var containsVars = (vars.map(x => varMap.contains(x.name))).reduce((var1, var2) => var1 && var2)
    validType && containsVars
  }

  /*
      filter invalid Trigger
   */
  def validateTrigger(vars:Seq[LocalVarDecl], trigger:Trigger): Seq[Trigger] = {
    //any trigger expression only LocalVar -> invalid
    if (validTrigger(vars, trigger.exps))  {
      Seq(trigger)
    } else {
      Seq()
    }
  }

  /*
       filter invalid Triggers
  */
  def validateTriggers(vars:Seq[LocalVarDecl], triggers:Seq[Trigger]):Seq[Trigger] = {
    if (triggers.isEmpty) {
      Seq()
    } else {
      val validatedTriggers = triggers.map(validateTrigger(vars, _))
      validatedTriggers.reduce((t1, t2) => t1 ++ t2)
    }
  }

  /*
      translate inhaling a forall expressions
   */
  def translateInhale(e: sil.Forall, error: PartialVerificationError): Stmt = e match{
    case SourceQuantifiedPermissionAssertion(forall, Implies(cond, expr)) =>
      val vs = forall.variables // TODO: Generalise to multiple quantified variables

       val res = expr match {
         //Quantified Field Permission
         case sil.FieldAccessPredicate(fieldAccess@sil.FieldAccess(recv, f), perms) =>
           // alpha renaming, to avoid clashes in context, use vFresh instead of v
           var isWildcard = false
           val vsFresh = vs.map(v => env.makeUniquelyNamed(v))
           vsFresh.foreach(vFresh => env.define(vFresh.localVar))

           def renaming[E <: sil.Exp] = (e: E) => Expressions.renameVariables(e, vs.map(v => v.localVar), vsFresh.map(vFresh => vFresh.localVar))

           val (renamingCond, renamingRecv, renamingPerms, renamingFieldAccess) = (renaming(cond), renaming(recv), renaming(perms), renaming(fieldAccess))
           val renamedTriggers = e.triggers.map(t => sil.Trigger(t.exps.map(x => renaming(x)))(t.pos, t.info))

           //translate sub-expressions
           val (translatedCond, translatedRecv) = (translateExp(renamingCond), translateExp(renamingRecv))
           val translatedLocals = vsFresh.map(vFresh => translateLocalVarDecl(vFresh))
           val (translatedPerms, stmts) = {
             //define wildcard if necessary
             if (conservativeIsWildcardPermission(perms)) {
               // Wildcards over quantified permissions should not be represented as a single existential fraction > 0.
               // Representig them this way implies that all quantified fields have the same amount of permission which is not the
               // correct abstraction
               isWildcard = true;
               val w = LocalVar(Identifier("wildcard"), Real)
               (w, Nil)
             } else {
               (translateExp(renamingPerms), Nil)
             }
           }
           val translatedTriggers = renamedTriggers.map(t => Trigger(t.exps.map(x => translateExp(x))))
           //val translatedLocation = translateLocation(Expressions.instantiateVariables(fieldAccess, vs.map(v => v.localVar), vsFresh.map(vFresh => vFresh.localVar)))

           //define inverse function and inverse terms
           val obj = LocalVarDecl(Identifier("o"), refType)
           val curPerm: Exp = currentPermission(obj.l, f)

           val (invFuns, rangeFun, triggerFun) = addQPFunctions(translatedLocals) // for the moment, the injectivity check is not made on inhale, so we don't need the third (trigger) function
           val invFunApps = invFuns.map(invFun => FuncApp(invFun.name, Seq(obj.l), invFun.typ))
           val rangeFunApp = FuncApp(rangeFun.name, Seq(obj.l), rangeFun.typ) // range(o): used to test whether an element of the mapped-to type is in the image of the QP's domain, projected by the receiver expression
           val rangeFunRecvApp = FuncApp(rangeFun.name, Seq(translatedRecv), rangeFun.typ) // range(e(v))
           var condInv = translatedCond
           var rcvInv = translatedRecv
           var permInv = translatedPerms
           for (i <- 0 until vsFresh.length) {
             condInv = condInv.replace(env.get(vsFresh(i).localVar), invFunApps(i))
             rcvInv = rcvInv.replace(env.get(vsFresh(i).localVar), invFunApps(i))
             permInv = permInv.replace(env.get(vsFresh(i).localVar), invFunApps(i))
           }

           //Define inverse Assumptions:
           //Trigger for first inverse function. If user-defined triggers are provided, (only) these are used. Otherwise, those auto-generated + triggers corresponding to looking up the location are chosen
           val recvTrigger = Trigger(Seq(translatedRecv))

           lazy val candidateTriggers: Seq[Trigger] = if (validateTrigger(translatedLocals, recvTrigger).isEmpty) // if we can't use the receiver, maybe we can use H[recv,field] etc..
             validateTriggers(translatedLocals, Seq(Trigger(Seq(translateLocationAccess(translatedRecv, f))), Trigger(Seq(currentPermission(qpMask, translatedRecv))))) else Seq(recvTrigger)

           val providedTriggers: Seq[Trigger] = validateTriggers(translatedLocals, translatedTriggers)

           val tr1: Seq[Trigger] = funcPredModule.rewriteTriggersToExpressionsUsedInTriggers(candidateTriggers ++ providedTriggers)

           val assm1Rhs = (0 until invFuns.length).foldLeft(rangeFunRecvApp: Exp)((soFar, i) => BinExp(soFar, And, FuncApp(invFuns(i).name, Seq(translatedRecv), invFuns(i).typ) === translatedLocals(i).l))

          // wildcards are per definition positive, thus no need to check for positivity
           val invAssm1 =
            if (isWildcard)
              (Forall(translatedLocals, tr1, translatedCond ==> assm1Rhs))
            else (Forall(translatedLocals, tr1, (translatedCond && permGt(translatedPerms, noPerm)) ==> assm1Rhs))
           val invAssm2 =
            if (isWildcard)
              Forall(Seq(obj), Trigger(invFuns.map(invFun => FuncApp(invFun.name, Seq(obj.l), invFun.typ))), (condInv && rangeFunApp) ==> (rcvInv === obj.l) )
            else Forall(Seq(obj), Trigger(invFuns.map(invFun => FuncApp(invFun.name, Seq(obj.l), invFun.typ))), ((condInv && permGt(permInv, noPerm))&&rangeFunApp) ==> (rcvInv === obj.l) )

           //Define non-null Assumptions:
           val nonNullAssumptions =
             Assume(Forall(translatedLocals, tr1, (translatedCond && permissionPositiveInternal(translatedPerms, Some(renamingPerms), false)) ==>
               (translatedRecv !== nullLiteral)))

           val translatedLocalVarDecl = vsFresh.map(vFresh => translateLocalVarDecl(vFresh))

         // TD: Positive permissions are not assumed anymore
           // val permPositive = Assume(Forall(translatedLocalVarDecl, tr1, translatedCond ==> permissionPositiveInternal(translatedPerms,None,true)))
           //check that given the condition, the permission held should be non-negative

         val permPositive = Assert(Forall(translatedLocalVarDecl, tr1, translatedCond ==> permissionPositiveInternal(translatedPerms, None, true)),
             error.dueTo(reasons.NegativePermission(perms)))

          //Define Permission to all locations of field f for locations where condition applies: add permission defined
           val condTrueLocations =
            if (isWildcard) (
              // for wildcards
              (condInv && rangeFunApp) ==>
                ((rcvInv === obj.l) && (
                  if (!usingOldState)
                    permGt(currentPermission(qpMask,obj.l), curPerm)
                  else
                    (currentPermission(qpMask,obj.l) === curPerm)
                ))
            )
            else (
              // for non wildcards
              ((condInv && permGt(permInv, noPerm))&&rangeFunApp) ==>
                ((permGt(permInv, noPerm) ==> (rcvInv === obj.l)) && (
                  if (!usingOldState)
                    (currentPermission(qpMask,obj.l) === curPerm + permInv)
                  else
                    (currentPermission(qpMask,obj.l) === curPerm)
                ))
            )
           //Define Permission to all locations of field f for locations where condition does not applies: no change
           val condFalseLocations =
            if (isWildcard)
              ((condInv && rangeFunApp).not ==> (currentPermission(qpMask,obj.l) === curPerm))
            else
              (((condInv && permGt(permInv, noPerm))&&rangeFunApp).not ==> (currentPermission(qpMask,obj.l) === curPerm))

           val triggerForPermissionUpdateAxiom = Seq(/*Trigger(curPerm),*/ Trigger(currentPermission(qpMask, obj.l)) /*,Trigger(invFunApp)*/)

           /*
           val v2s = translatedLocals.map(translatedLocal => LocalVarDecl(Identifier("v2"),translatedLocal.typ))
           val injectiveTrigger = tr1.map(trigger => Trigger(trigger.exps ++ trigger.exps.map(exp => replaceAll(exp, translatedLocals.map(translatedLocal => translatedLocal.l), v2s.map(v2 => v2.l)))))
           val injectiveCheck = Assert(Forall( translatedLocal++v2,injectiveTrigger,((translatedLocal.l !== v2.l) &&  translatedCond && translatedCond.replace(translatedLocal.l, v2.l) ) ==> (translatedRecv !== translatedRecv.replace(translatedLocal.l, v2.l))),
             error.dueTo(reasons.ReceiverNotInjective(fieldAccess)))
            */


           //injectivity assertion
           val v2s = translatedLocals.map(translatedLocal => LocalVarDecl(Identifier(translatedLocal.name.name), translatedLocal.typ))
           var triggerFunApp2 = FuncApp(triggerFun.name, translatedLocals.map(v => LocalVar(v.name, v.typ)), triggerFun.typ)
           var notEquals: Exp = TrueLit()
           var translatedPerms2 = translatedPerms
           var translatedCond2 = translatedCond
           var translatedRecv2 = translatedRecv
           for (i <- 0 until translatedLocals.length) {
             triggerFunApp2 = triggerFunApp2.replace(translatedLocals(i).l, v2s(i).l)
             translatedPerms2 = translatedPerms2.replace(translatedLocals(i).l, v2s(i).l)
             translatedCond2 = translatedCond2.replace(translatedLocals(i).l, v2s(i).l)
             translatedRecv2 = translatedRecv2.replace(translatedLocals(i).l, v2s(i).l)
             notEquals = notEquals && (translatedLocals(i).l !== v2s(i).l)
           }
           val is_injective = Forall(translatedLocals ++ v2s, validateTriggers(translatedLocals ++ v2s, Seq(Trigger(Seq(triggerFunApp2)))), (notEquals && translatedCond && translatedCond2 && permGt(translatedPerms, noPerm) && permGt(translatedPerms2, noPerm)) ==> (translatedRecv !== translatedRecv2))

           val reas = reasons.QPAssertionNotInjective(fieldAccess)
           var err = error.dueTo(reas)
           val injectiveAssertion = Assert(is_injective, err)

           val res1 = Havoc(qpMask) ++
             stmts ++
             (if (!verifier.assumeInjectivityOnInhale) injectiveAssertion
             else Nil) ++
             CommentBlock("Define Inverse Function", Assume(invAssm1) ++
               Assume(invAssm2)) ++
             (if (!isWildcard) MaybeComment("Check that permission expression is non-negative for all fields", permPositive) else Nil) ++
             CommentBlock("Assume set of fields is nonNull", nonNullAssumptions) ++
            // CommentBlock("Assume injectivity", injectiveAssumption) ++
             CommentBlock("Define permissions", Assume(Forall(obj,triggerForPermissionUpdateAxiom, condTrueLocations&&condFalseLocations ))) ++
             (masks(f) := qpMask)

           vsFresh.foreach(vFresh => env.undefine(vFresh.localVar))

           res1
         //Predicate access
         case accPred: sil.AccessPredicate =>
           val qpMask = LocalVar(Identifier("pqpMask"), pmaskType)
           // alpha renaming, to avoid clashes in context, use vFresh instead of v
           val vsFresh = vs.map(v => env.makeUniquelyNamed(v))
           vsFresh.map(vFresh => env.define(vFresh.localVar))
           // create fresh variables for the formal arguments of the predicate definition
           // create fresh variables for the formal arguments of the predicate/wand definition
           val (formals, args, resource) = accPred match {
             case sil.PredicateAccessPredicate(sil.PredicateAccess(args, predname), _) =>
               val predicate = program.findPredicate(predname)
               (predicate.formalArgs, args, predicate)
             case w: sil.MagicWand =>
               val subExps = w.subexpressionsToEvaluate(program)
               val formals = subExps.zipWithIndex.map { case (arg, i) => sil.LocalVarDecl(s"arg_$i", arg.typ)() }
               (formals, subExps, w.structure(program))
           }
           val perms = accPred.perm
           val freshFormalDecls : Seq[sil.LocalVarDecl] = formals.map(env.makeUniquelyNamed)
           val freshFormalVars : Seq[sil.LocalVar] = freshFormalDecls.map(d => d.localVar)
           val freshFormalBoogieVars = freshFormalVars.map(x => env.define(x))
           val freshFormalBoogieDecls = freshFormalVars.map(x => LocalVarDecl(env.get(x).name, typeModule.translateType(x.typ)))

           var isWildcard = false
           def renamingQuantifiedVar[E <: sil.Exp] = (e:E) => Expressions.renameVariables(e, vs.map(v => v.localVar), vsFresh.map(vFresh => vFresh.localVar))
           val (renamedCond,renamedPerms) = (renamingQuantifiedVar(cond),renamingQuantifiedVar(perms))
           val renamedArgs = args.map(renamingQuantifiedVar)
           val renamedTriggers = e.triggers.map(trigger => sil.Trigger(trigger.exps.map(x => renamingQuantifiedVar(x)))(trigger.pos, trigger.info))

           //translate components
           val translatedLocals = vsFresh.map(vFresh => translateLocalVarDecl(vFresh))
           val translatedCond = translateExp(renamedCond)
           val translatedArgs = renamedArgs.map(translateExp)
           val argSnap = funcPredModule.toSnap(translatedArgs)
           val (translatedPerms, stmts, _) = {
             if (conservativeIsWildcardPermission(perms)) {
               isWildcard = true
               val w = LocalVar(Identifier("wildcard"), Real)
               (w, LocalVarWhereDecl(w.name, w > RealLit(0)) :: Havoc(w) :: Nil, w)
             } else {
               (translateExp(renamedPerms), Nil, null)
             }
           }
           val translatedTriggers : Seq[Trigger] = renamedTriggers.map(trigger => Trigger(trigger.exps.map(x => translateExp(x))))

           //define inverse function
           val (invFuns,rangeFun,triggerFun) = addQPFunctions(translatedLocals, freshFormalBoogieDecls) // for the moment, the injectivity check is not made on inhale, so we don't need the third (trigger) function

           val funApps = invFuns.map(invFun => FuncApp(invFun.name, translatedArgs, invFun.typ))
           val invFunApps = invFuns.map(invFun => FuncApp(invFun.name, freshFormalBoogieVars, invFun.typ))

           //replace all occurrences of the originally-bound variable with occurrences of the inverse function application
           val condInv = replaceAll(translatedCond, translatedLocals.map(translatedLocal => translatedLocal.l), invFunApps)
           val argsInv = translatedArgs.map(x => replaceAll(x, translatedLocals.map(translatedLocal => translatedLocal.l), invFunApps))
           val permInv = replaceAll(translatedPerms, translatedLocals.map(translatedLocal => translatedLocal.l), invFunApps)

           val rangeFunApp = FuncApp(rangeFun.name, freshFormalBoogieVars, rangeFun.typ) // range(o,...): used to test whether an element of the mapped-to type is in the image of the QP's domain, projected by the receiver expression
           val rangeFunRecvApp = FuncApp(rangeFun.name, translatedArgs, rangeFun.typ) // range(e(v),...)

           //define inverse functions
           lazy val candidateTriggers : Seq[Trigger] = validateTriggers(translatedLocals, Seq(Trigger(translateLocationAccess(accPred.loc)),Trigger(currentPermission(argSnap, resource))))

           val providedTriggers : Seq[Trigger] = validateTriggers(translatedLocals, translatedTriggers)

           val tr1: Seq[Trigger] = funcPredModule.rewriteTriggersToExpressionsUsedInTriggers(candidateTriggers ++ providedTriggers)

           val equalities = (0 until funApps.length).foldLeft(TrueLit(): Exp)((soFar, i) => BinExp(soFar, And, funApps(i) === translatedLocals(i).l))

           val invAssm1 = Forall(translatedLocals, tr1, (translatedCond && permGt(translatedPerms, noPerm)) ==> (equalities && rangeFunRecvApp))
           //for each argument, define the second inverse function
           val eqExpr = (argsInv zip freshFormalBoogieVars).map(x => x._1 === x._2)
           val conjoinedInverseAssumptions = eqExpr.foldLeft(TrueLit():Exp)((soFar,exp) => BinExp(soFar,And,exp))
           val invAssm2 = Forall(freshFormalBoogieDecls, Trigger(invFunApps), ((condInv && permGt(permInv, noPerm)) && rangeFunApp) ==> conjoinedInverseAssumptions)


           val generalSnap = funcPredModule.silExpsToSnap(freshFormalVars)

            //trigger for both map descriptions
           val triggerForPermissionUpdateAxioms = Seq(Trigger(currentPermission(qpMask,generalSnap))/*, Trigger(invFunApp)*/)

           // TD: We do not assume anymore that the permissions are non-negative, and we need to check them
           // permissions non-negative
           // val permPositive = Assume(Forall(translatedLocals, tr1, translatedCond ==> permissionPositiveInternal(translatedPerms,None,true)))
           //check that given the condition, the permission held should be non-negative
           val permPositive = Assert(Forall(translatedLocals, tr1, translatedCond ==> permissionPositiveInternal(translatedPerms,None,true)),
             error.dueTo(reasons.NegativePermission(perms)))


         //assumptions for predicates that gain permission
           val permissionsMap = Assume(
             {
               val exp = ((condInv && permGt(permInv, noPerm)) && rangeFunApp) ==> ((permGt(permInv, noPerm) ==> conjoinedInverseAssumptions) && (currentPermission(qpMask,generalSnap) === currentPermission(generalSnap, resource) + permInv))
               if (freshFormalBoogieDecls.isEmpty)
                 exp
               else
                 Forall(freshFormalBoogieDecls,triggerForPermissionUpdateAxioms, exp)
             })
           //assumptions for predicates of the same type which do not gain permission
           val independentPredicate = Assume(
             {
               val exp = (((condInv && permGt(permInv, noPerm)) && rangeFunApp).not) ==> (currentPermission(qpMask,generalSnap) === currentPermission(generalSnap, resource))
               if (freshFormalBoogieDecls.isEmpty)
                 exp
               else
                 Forall(freshFormalBoogieDecls, triggerForPermissionUpdateAxioms, exp)
             })

           /*
                assumption for locations that are definitely independent of the locations defined by the quantified predicate permission. Independent locations include:
                  - field is not a predicate
                  - not the same predicate (have a different predicate id)
            */
           val obj = LocalVarDecl(Identifier("o"), refType)


           //define second variable and other arguments needed to express injectivity
           val v2s = vs.map(v => env.makeUniquelyNamed(v))
           v2s.foreach(v2 => env.define(v2.localVar))

           //assert injectivity of inverse function:
           val translatedLocals2 = translatedLocals.map(translatedLocal => LocalVarDecl(Identifier(translatedLocal.name.name), translatedLocal.typ)) //new varible

           val triggerFunApp = FuncApp(triggerFun.name, translatedLocals.map(translatedLocal => LocalVar(translatedLocal.name, translatedLocal.typ)), triggerFun.typ)

           var unequalities : Exp = TrueLit()
           var translatedCond2 = translatedCond
           var translatedPerms2 = translatedPerms
           var translatedArgs2 = translatedArgs
           var triggerFunApp2 = triggerFunApp
           for (i <- 0 until translatedLocals.length) {
             unequalities = unequalities && (translatedLocals(i).l.!==(translatedLocals2(i).l))
             translatedCond2 = translatedCond2.replace(translatedLocals(i).l, translatedLocals2(i).l)
             translatedPerms2 = translatedPerms2.replace(translatedLocals(i).l, translatedLocals2(i).l)
             translatedArgs2 = translatedArgs2.map(a => a.replace(translatedLocals(i).l, translatedLocals2(i).l))
             triggerFunApp2 = triggerFunApp2.replace(translatedLocals(i).l, translatedLocals2(i).l)
           }

           val injectiveCond = unequalities && translatedCond && translatedCond2 && permGt(translatedPerms, noPerm) && permGt(translatedPerms2, noPerm);
           //val translatedArgs2= translatedArgs.map(x => x.replace(translatedLocal.l, translatedLocal2.l))
           val ineqs = (translatedArgs zip translatedArgs2).map(x => x._1 !== x._2)
           val ineqExpr = {
             if (ineqs.isEmpty) FalseLit()
             else ineqs.reduce((expr1, expr2) => (expr1) || (expr2))
           }
           val injectTrigger = Seq(Trigger(Seq(triggerFunApp, triggerFunApp2)))
           val err = error.dueTo(reasons.QPAssertionNotInjective(accPred.loc))
           val injectiveAssertion = Assert(Forall((translatedLocals ++ translatedLocals2), injectTrigger,injectiveCond ==> ineqExpr), err)


           val res1 = Havoc(qpMask) ++
             stmts ++
             (if (!verifier.assumeInjectivityOnInhale) CommentBlock("check if receiver " + accPred.toString() + " is injective",injectiveAssertion)
             else Nil) ++
             CommentBlock("Define Inverse Function", Assume(invAssm1) ++
               Assume(invAssm2)) ++
             (if (!isWildcard) (MaybeComment("Check that permission expression is non-negative for all fields", permPositive)) else Nil) ++
             CommentBlock("Define updated permissions", permissionsMap) ++
             CommentBlock("Define independent locations", (independentPredicate)) ++
             (masks(resource) := qpMask)

           vsFresh.foreach(vFresh => env.undefine(vFresh.localVar))
           v2s.foreach(v2 => env.undefine(v2.localVar))
           freshFormalVars.foreach(x => env.undefine(x))

           res1
         case _ =>
           Nil
       }
       val resource = expr match {
         case mw: sil.MagicWand => mw.structure(program)
         case ap: sil.AccessPredicate => ap.res(program)
       }
       res ++ assumeGoodMask(resource)
    case _ => Nil
  }


  def replaceAll[T <: Exp](e: T, nodes: Seq[Node], by: Seq[Node]): T = {
    var res : T = e
    for (i <- 0 until nodes.length){
      res = res.replace(nodes(i), by(i))
    }
    res
  }



  //renamed Localvariable and Condition
  def getMapping(v: sil.LocalVarDecl, cond:sil.Exp, expr:sil.Exp): Seq[Exp] = {
    val res = expr match {
      case SourceQuantifiedPermissionAssertion(forall, Implies(cond, expr))  =>
        Nil
      case sil.FieldAccessPredicate(fa@sil.FieldAccess(rcvr, f), gain) =>
        Nil
      case predAccPred@sil.PredicateAccessPredicate(PredicateAccess(args, predname), perm) =>
        Nil
      case sil.And(e0, e1) =>
        Nil
      case sil.Implies(e0, e1) =>
        //e0 must be pure
        Nil
      case sil.Or(e0, e1) =>
        //e0 must be pure
        Nil
      case _ => Nil
    }
    res
  }

  override def transferAdd(e:TransferableEntity, cond:Exp): Stmt = {
    val curPerm = currentPermission(e.rcv,e.resource)
    /* GP: probably redundant in current transfer as these assumputions are implied

      (cond := cond && permissionPositive(e.transferAmount, None,true)) ++
      {
      e match {
        case TransferableFieldAccessPred(rcv,_,_,_) => (cond := cond && checkNonNullReceiver(rcv))
        case _ => Nil
      }
    } ++ */
    if (!usingOldState) currentMaskAssignUpdate(e.rcv, e.resource, permAdd(curPerm, e.transferAmount)) else Nil
  }

  override def tempInitMask(rcv: Exp, loc:sil.Resource):(Seq[Exp], Stmt) = {
    val isField = loc.isInstanceOf[sil.Field]
    val zrMsk = if (isField) zeroMask else zeroPMask
    val tmpMsk = if (isField) tempMask else ptempMask
    val setMaskStmt = tmpMsk := maskUpdate(zrMsk, rcv, fullPerm, isField)
    (tmpMsk, setMaskStmt)
  }

  def currentPermission(loc: sil.ResourceAccess): Exp = {
    loc match {
      case sil.FieldAccess(rcv, field) =>
        currentPermission(translateExp(rcv), field)
      case sil.PredicateAccess(args, pname) =>
        currentPermission(funcPredModule.silExpsToSnap(args), program.findPredicate(pname))
      case w: sil.MagicWand =>
        currentPermission(funcPredModule.silExpsToSnap(w.subexpressionsToEvaluate(program)), w.structure(program))
    }
  }

  def currentPermission(rcv: Exp, location: sil.Resource): Exp = {
    currentPermission(maskExps(location), rcv)
  }
  def currentPermission(mask: Exp, rcv: Exp): Exp = {
    if(verifier.usePolyMapsInEncoding) {
      MapSelect(mask, Seq(rcv))
    } else {
      /*FuncApp( if(isPMask) { readPMaskName } else { readMaskName },
               Seq(mask, rcv, location),
               if(isPMask) { Bool } else { permType })*/
      ???

    }
  }

  override def permissionLookup(la: sil.ResourceAccess) : Exp = {
    currentPermission(la)
  }

  private def currentMaskAssignUpdate(loc: ResourceAccess, newPerm: Exp) : Stmt = {
    val rcv = translateReceiver(loc)
    currentMaskAssignUpdate(rcv, loc.res(program), newPerm)
  }

  private def currentMaskAssignUpdate(rcv: Exp, r: sil.Resource, newPerm: Exp) : Stmt = {
    val msk = masks(r)
    val isField = r.isInstanceOf[sil.Field]
    newPerm match {
      case BinExp(MapSelect(`msk`, Seq(`rcv`)), Add, addition) if isField && addition == fullPerm =>
        Assume(currentPermission(msk, rcv) === noPerm) ++ (msk := maskUpdate(msk, rcv, addition, isField))
      case BinExp(MapSelect(`msk`, Seq(`rcv`)), Sub, addition) if isField && addition == fullPerm =>
        msk := maskUpdate(msk, rcv, noPerm, isField)
      case _ => msk := maskUpdate(msk, rcv, newPerm, isField)
    }
  }

  /*private def maskUpdate(mask: Exp, loc: LocationAccess, newPerm: Exp) : Exp = {
    val (rcv, field) = rcvAndFieldExp(loc)
    maskUpdate(mask, rcv, field, newPerm)
  }*/

  private def maskUpdate(mask: Exp, rcv: Exp, newPerm: Exp, isField: Boolean) : Exp = {
    val (addFuncName, mskTyp) = if (isField) (addToMaskName, maskType) else (paddToMaskName, pmaskType)
    newPerm match {
      case BinExp(MapSelect(`mask`, Seq(`rcv`)), Add, addition) => FuncApp(addFuncName, Seq(mask, rcv, addition), mskTyp)
      case BinExp(MapSelect(`mask`, Seq(`rcv`)), Sub, addition) => FuncApp(addFuncName, Seq(mask, rcv, addition.neg), mskTyp)
      case _ => actualMaskUpdate(mask, rcv, newPerm)
    }
  }

  private def actualMaskUpdate(mask: Exp, rcv: Exp, newPerm: Exp): Exp = {
    if (verifier.usePolyMapsInEncoding)
      MapUpdate(mask, Seq(rcv), newPerm)
    else
      ??? // FuncApp(updateMaskName, Seq(mask, rcv, field, newPerm), maskType)
  }

  override def currentMask(r: sil.Resource) = maskExps(r)
  override def staticMask = maskVars.values.map(v => LocalVarDecl(v.name, v.typ)).toSeq
  override def staticPermissionPositive(rcv: Exp, loc: sil.Resource) = {
    hasDirectPerm(rcv, loc)
  }

  def translatePerm(e: sil.Exp): Exp = {
    require(e isSubtype sil.Perm)
    e match {
      case sil.NoPerm() =>
        noPerm
      case sil.FullPerm() =>
        fullPerm
      case sil.WildcardPerm() =>
        sys.error("cannot translate wildcard at an arbitrary position (should only occur directly in an accessibility predicate)")
      case sil.EpsilonPerm() =>
        sys.error("epsilon permissions are not supported by this permission module")
      case sil.CurrentPerm(loc: ResourceAccess) =>
        currentPermission(loc)
      case sil.FractionalPerm(left, right) =>
        BinExp(translateExp(left), Div, translateExp(right))
      case sil.PermMinus(a) =>
        UnExp(Minus,translatePerm(a))
      case sil.PermAdd(a, b) =>
        permAdd(translatePerm(a), translatePerm(b))
      case sil.PermSub(a, b) =>
        permSub(translatePerm(a), translatePerm(b))
      case sil.PermMul(a, b) =>
        BinExp(translatePerm(a), Mul, translatePerm(b))
      case sil.PermDiv(a,b) =>
        permDiv(translatePerm(a), translateExp(b))
      case sil.PermPermDiv(a,b) =>
        permDiv(translatePerm(a), translatePerm(b))
      case sil.IntPermMul(a, b) =>
        val i = translateExp(a)
        val p = translatePerm(b)
        BinExp(RealConv(i), Mul, p)
      case sil.CondExp(cond, thn, els) =>
        CondExp(translateExp(cond), translatePerm(thn), translatePerm(els))
      case _ //sil.LocalVar | _: sil.FuncLikeApp | _:sil.FieldAccess
      =>
        translateExp(e) // any permission-typed expression should be translatable
      //case _ => sys.error(s"not a permission expression: $e")
    }
  }

  def translatePermComparison(e: sil.Exp): Exp = {
    val t = translateExp(_)
    e match {
      case sil.EqCmp(a, b) => permEq(t(a), t(b))
      case sil.NeCmp(a, b) => permNe(t(a), t(b))
      case sil.DomainBinExp(a, sil.PermGeOp, b) => permGe(t(a), t(b))
      case sil.DomainBinExp(a, sil.PermGtOp, b) => permGt(t(a), t(b))
      case sil.DomainBinExp(a, sil.PermLeOp, b) => permLe(t(a), t(b))
      case sil.DomainBinExp(a, sil.PermLtOp, b) => permLt(t(a), t(b))
      case _ => sys.error("not a permission comparison")
    }
  }

  val currentAbstractReads = collection.mutable.ListBuffer[String]()

  override def getCurrentAbstractReads(): ListBuffer[String] = {
    currentAbstractReads
  }

  private def isAbstractRead(exp: sil.Exp) = {
    exp match {
      case sil.LocalVar(name, _) => currentAbstractReads.contains(name)
      case _ => false
    }
  }

  override def freshReads(vars: Seq[viper.silver.ast.LocalVar]): Stmt = {
    val bvs = vars map translateLocalVar
    Havoc(bvs) ++
      (bvs map (v => Assume((v > noPerm) && (v < fullPerm))))
  }

  override def handleStmt(s: sil.Stmt, statesStack: List[Any] = null, allStateAssms: Exp = TrueLit(), insidePackageStmt: Boolean = false) : (Seqn => Seqn) = {
    stmts =>
      s match {
        case n@sil.NewStmt(target, fields) =>
          stmts ++ (for (field <- fields) yield {
            Seqn(Seq(currentMaskAssignUpdate(sil.FieldAccess(target, field)(), currentPermission(sil.FieldAccess(target, field)()) + fullPerm), assumeGoodMask(field)))
          })
        case assign@sil.FieldAssign(fa, rhs) =>
           stmts ++ Assert(permGe(currentPermission(fa), fullPerm, true), errors.AssignmentFailed(assign).dueTo(reasons.InsufficientPermission(fa))) // add the check after the definedness checks for LHS/RHS (in heap module)
        case _ =>
          //        (Nil, Nil)
          stmts
      }
  }

  private def permEq(a: Exp, b: Exp): Exp = {
    a === b
  }
  private def permNe(a: Exp, b: Exp): Exp = {
    a !== b
  }
  private def permLt(a: Exp, b: Exp): Exp = {
    a < b
  }
  private def permLe(a: Exp, b: Exp, forField : Boolean = false): Exp = {
    // simple optimization that helps in many cases
    if (forField && a == fullPerm) permEq(a, b)
    else a <= b
  }
  private def permGt(a: Exp, b: Exp, forField : Boolean = false): Exp = {
    // simple optimization that helps in many cases
    if (forField && b == fullPerm) permEq(a, b)
    else permLt(b, a)
  }
  private def permGe(a: Exp, b: Exp, forField : Boolean = false): Exp = {
    permLe(b, a, forField)
  }

  override def simplePartialCheckDefinednessAfter(e: sil.Exp, error: PartialVerificationError, makeChecks: Boolean, definednessStateOpt: Option[DefinednessState]): Stmt = {

    val stmt: Stmt = if(makeChecks) (
      e match {
        case fa@sil.LocationAccess(_) =>
          val hasDirectPermExp = definednessStateOpt.fold(hasDirectPerm(fa))(defState => hasDirectPerm(fa, defState.setDefState))
          Assert(hasDirectPermExp, error.dueTo(reasons.InsufficientPermission(fa)))
        case sil.PermDiv(a, b) =>
          Assert(translateExp(b) !== IntLit(0), error.dueTo(reasons.DivisionByZero(b)))
        case sil.PermPermDiv(a, b) =>
          Assert(translatePerm(b) !== RealLit(0.0), error.dueTo(reasons.DivisionByZero(b)))
        case _ => Nil
      }
      ) else Nil

    stmt
  }

  /*For QP \forall x:T :: c(x) ==> acc(e(x),p(x)) this case class describes an instantiation of the QP where
   * cond = c(expr), recv = e(expr) and perm = p(expr) and expr is of type T and may be dependent on the variable given by v. */
  case class QPComponents(v:LocalVarDecl,cond: Exp, recv: Exp, perm: Exp)

  /*For QP \forall x:T :: c(x) ==> acc(pred(e1(x), ....., en(x),p(x)) this case class describes an instantiation of the QP where
 * cond = c(expr), e1(x), ...en(x) = args and perm = p(expr) and expr is of type T and may be dependent on the variable given by v. */
  case class QPPComponents(v:LocalVarDecl, cond: Exp, predname:String, args:Seq[Exp], perm:Exp, predAcc:PredicateAccessPredicate)

  /* records a fresh function which represents the inverse function of a receiver expression in a qp, if the qp is
   given by \forall x:: T. c(x) ==> acc(e(x).f,p(x)) then "outputType" is T. The returned function takes values of type
   Ref and returns value of type T.
   argumentDecls gives the names and types of the formal parameters (recv:Ref by default, but different for e.g. predicates under qps)
   The second function is a boolean function to represent the image of e(x) for all instances x to which permission is denoted
   */
  private def addQPFunctions(qvars: Seq[LocalVarDecl], argumentDecls : Seq[LocalVarDecl] = LocalVarDecl(Identifier("recv"), refType)):(Seq[Func],Func,Func) = {
    val invFuns = new ListBuffer[Func]
    for (qvar <- qvars) {
      qpId = qpId+1;
      val invFun = Func(Identifier(inverseFunName+qpId), argumentDecls, qvar.typ)
      inverseFuncs += invFun
      invFuns.append(invFun)
    }

    val rangeFun = Func(Identifier(rangeFunName+qpId), argumentDecls , Bool)
    rangeFuncs += rangeFun
    val triggerFun = Func(Identifier(triggerFunName+qpId), qvars,  Bool)
    triggerFuncs += triggerFun
    (invFuns.toSeq, rangeFun, triggerFun)
  }

  override def conservativeIsPositivePerm(e: sil.Exp): Boolean = PermissionHelper.conservativeStaticIsStrictlyPositivePerm(e)

  override def isStrictlyPositivePerm(e: sil.Exp): Exp = PermissionHelper.isStrictlyPositivePerm(e)

  object PermissionHelper {

    def isStrictlyPositivePerm(e: sil.Exp): Exp = {
      require(e isSubtype sil.Perm, s"found ${e.typ} ($e), but required Perm")
      // Use backup lazily when needed only. This allows the function to work on WildcardPerms for which
      // translatePerm would throw an exception.
      val backup = () => permissionPositiveInternal(translatePerm(e), Some(e))
      e match {
        case sil.NoPerm() => FalseLit()
        case sil.FullPerm() => TrueLit()
        case sil.WildcardPerm() => TrueLit()
        case sil.EpsilonPerm() =>  sys.error("epsilon permissions are not supported by this permission module")
        case x: sil.LocalVar if isAbstractRead(x) => TrueLit()
        case sil.CurrentPerm(loc) => backup()
        case sil.FractionalPerm(left, right) =>
          val (l, r) = (translateExp(left), translateExp(right))
          ((l > IntLit(0)) && (r > IntLit(0))) || ((l < IntLit(0)) && (r < IntLit(0)))
        case sil.PermMinus(a) =>
          isStrictlyNegativePerm(a)
        case sil.PermAdd(left, right) =>
          (isStrictlyPositivePerm(left) && isStrictlyPositivePerm(right)) || backup()
        case sil.PermSub(left, right) => backup()
        case sil.PermMul(a, b) =>
          (isStrictlyPositivePerm(a) && isStrictlyPositivePerm(b)) || (isStrictlyNegativePerm(a) && isStrictlyNegativePerm(b))
        case sil.PermDiv(a, b) =>
          isStrictlyPositivePerm(a) // note: b should be ruled out from being non-positive
        case sil.PermPermDiv(a, b) =>
          (isStrictlyPositivePerm(a) && isStrictlyPositivePerm(b)) ||
            (isStrictlyNegativePerm(a) && isStrictlyNegativePerm(b))
        case sil.IntPermMul(a, b) =>
          val n = translateExp(a)
          ((n > IntLit(0)) && isStrictlyPositivePerm(b)) || ((n < IntLit(0)) && isStrictlyNegativePerm(b))
        case sil.CondExp(cond, thn, els) =>
          CondExp(translateExp(cond), isStrictlyPositivePerm(thn), isStrictlyPositivePerm(els))
        case _ => backup()
      }
    }

    def conservativeStaticIsStrictlyPositivePerm(e: sil.Exp): Boolean = {
      require(e isSubtype sil.Perm, s"found ${e.typ} ($e), but required Perm")
      e match {
        case sil.NoPerm() => false
        case sil.FullPerm() => true
        case sil.WildcardPerm() => true
        case sil.EpsilonPerm() =>  sys.error("epsilon permissions are not supported by this permission module")
        case x: sil.LocalVar if isAbstractRead(x) => true
        case sil.CurrentPerm(loc) => false // conservative
        case sil.FractionalPerm(sil.IntLit(m), sil.IntLit(n)) =>
          m > 0 && n > 0 || m < 0 && n < 0
        case sil.FractionalPerm(left, right) => false // conservative
        case sil.PermMinus(a) =>
          conservativeStaticIsStrictlyNegativePerm(a)
        case sil.PermAdd(left, right) =>
          conservativeStaticIsStrictlyPositivePerm(left) && conservativeStaticIsStrictlyPositivePerm(right)
        case sil.PermSub(left, right) => false // conservative
        case sil.PermMul(a, b) =>
          (conservativeStaticIsStrictlyPositivePerm(a) && conservativeStaticIsStrictlyPositivePerm(b)) || (conservativeStaticIsStrictlyNegativePerm(a) && conservativeStaticIsStrictlyNegativePerm(b))
        case sil.PermDiv(a, b) =>
          conservativeStaticIsStrictlyPositivePerm(a) // note: b should be guaranteed ruled out from being non-positive
        case sil.PermPermDiv(a, b) =>
          (conservativeStaticIsStrictlyPositivePerm(a) && conservativeStaticIsStrictlyPositivePerm(b)) ||
            (conservativeStaticIsStrictlyNegativePerm(a) && conservativeStaticIsStrictlyNegativePerm(b))
        case sil.IntPermMul(sil.IntLit(n), b) =>
          n > 0 && conservativeStaticIsStrictlyPositivePerm(b) || n < 0 && conservativeStaticIsStrictlyNegativePerm(b)
        case sil.IntPermMul(a, b) => false // conservative
        case sil.CondExp(cond, thn, els) => // conservative
          conservativeStaticIsStrictlyPositivePerm(thn) && conservativeStaticIsStrictlyPositivePerm(els)
        case _ => false // conservative?
      }
    }

    def conservativeStaticIsStrictlyNegativePerm(e: sil.Exp): Boolean = {
      require(e isSubtype sil.Perm, s"found ${e.typ} ($e), but required Perm")
      e match {
        case sil.NoPerm() => false // strictly negative
        case sil.FullPerm() => false
        case sil.WildcardPerm() => false
        case sil.EpsilonPerm() =>  sys.error("epsilon permissions are not supported by this permission module")
        case x: sil.LocalVar => false // conservative
        case sil.CurrentPerm(loc) => false // conservative
        case sil.FractionalPerm(sil.IntLit(m), sil.IntLit(n)) =>
          m > 0 && n < 0 || m < 0 && n > 0
        case sil.FractionalPerm(left, right) => false // conservative
        case sil.PermMinus(a) =>
          conservativeStaticIsStrictlyPositivePerm(a)
        case sil.PermAdd(left, right) =>
          conservativeStaticIsStrictlyNegativePerm(left) && conservativeStaticIsStrictlyNegativePerm(right)
        case sil.PermSub(left, right) => false // conservative
        case sil.PermMul(a, b) =>
          (conservativeStaticIsStrictlyPositivePerm(a) && conservativeStaticIsStrictlyNegativePerm(b)) || (conservativeStaticIsStrictlyNegativePerm(a) && conservativeStaticIsStrictlyPositivePerm(b))
        case sil.PermDiv(a, b) =>
          conservativeStaticIsStrictlyNegativePerm(a) // note: b should be guaranteed ruled out from being non-positive
        case sil.PermPermDiv(a, b) =>
          (conservativeStaticIsStrictlyNegativePerm(a) && conservativeStaticIsStrictlyPositivePerm(b)) ||
            (conservativeStaticIsStrictlyPositivePerm(a) && conservativeStaticIsStrictlyNegativePerm(b))
        case sil.IntPermMul(sil.IntLit(n), b) =>
          n > 0 && conservativeStaticIsStrictlyNegativePerm(b) || n < 0 && conservativeStaticIsStrictlyPositivePerm(b)
        case sil.IntPermMul(a, b) => false // conservative
        case sil.CondExp(cond, thn, els) => // conservative
          conservativeStaticIsStrictlyNegativePerm(thn) && conservativeStaticIsStrictlyNegativePerm(els)
        case _ => false // conservative?
      }
    }

    def isStrictlyNegativePerm(e: sil.Exp): Exp = {
      require(e isSubtype sil.Perm)
      // Use backup lazily when needed only. This allows the function to work on WildcardPerms for which
      // translatePerm would throw an exception.
      val backup = () => UnExp(Not,permissionPositiveInternal(translatePerm(e), Some(e), true))
      e match {
        case sil.NoPerm() => FalseLit() // strictly negative
        case sil.FullPerm() => FalseLit()
        case sil.WildcardPerm() => FalseLit()
        case sil.EpsilonPerm() =>  sys.error("epsilon permissions are not supported by this permission module")
        case x: sil.LocalVar if isAbstractRead(x) => FalseLit()
        case sil.CurrentPerm(loc) => backup()
        case sil.FractionalPerm(left, right) =>
          val (l, r) = (translateExp(left), translateExp(right))
          ((l < IntLit(0)) && (r > IntLit(0))) || ((l > IntLit(0)) && (r < IntLit(0)))
        case sil.PermMinus(a) =>
          isStrictlyPositivePerm(a)
        case sil.PermAdd(left, right) =>
          (isStrictlyNegativePerm(left) && isStrictlyNegativePerm(right)) || backup()
        case sil.PermSub(left, right) => backup()
        case sil.PermMul(a, b) =>
          (isStrictlyPositivePerm(a) && isStrictlyNegativePerm(b)) || (isStrictlyNegativePerm(a) && isStrictlyPositivePerm(b))
        case sil.PermDiv(a, b) =>
          isStrictlyNegativePerm(a) // note: b should be guaranteed ruled out from being non-positive
        case sil.PermPermDiv(a, b) =>
          (isStrictlyNegativePerm(a) && isStrictlyPositivePerm(b)) ||
            (isStrictlyPositivePerm(a) && isStrictlyNegativePerm(b))
        case sil.IntPermMul(a, b) =>
          val n = translateExp(a)
          ((n > IntLit(0)) && isStrictlyNegativePerm(b)) || ((n < IntLit(0)) && isStrictlyPositivePerm(b))
        case sil.CondExp(cond, thn, els) =>
          CondExp(translateExp(cond), isStrictlyNegativePerm(thn), isStrictlyNegativePerm(els))
        case _ => backup()
      }
    }

    // Does this permission amount definitely denote a statically-known constant amount?
    // NOTE: this is conservative and so always returns false for local variables
    def isFixedPerm(e: sil.Exp): Boolean = {
      require(e isSubtype sil.Perm)
      e match {
        case sil.NoPerm() => true
        case sil.FullPerm() => true
        case sil.WildcardPerm() => false
        case sil.EpsilonPerm() =>  sys.error("epsilon permissions are not supported by this permission module")
        //case sil.CurrentPerm(loc) => true
        case sil.FractionalPerm(left, right) => { // AS: this seems a reasonable way to catch the possibilities - if no free variables and no heap dependence, I think the expression must be made up of statically-known parts? Trying to avoid writing a whole extra method for the purpose of correctly supporting this case..
          if(left.existsDefined({case _:sil.LocalVar => }) || left.existsDefined({case _:sil.LocalVar => })) false else {
            val prog: sil.Program = verifier.program
            !left.isHeapDependent(prog) && !right.isHeapDependent(prog)
          }
        }
        case sil.PermMinus(a) =>
          isFixedPerm(a)
        case sil.PermAdd(left, right) =>
          isFixedPerm(left) && isFixedPerm(right)
        case sil.PermSub(left, right) =>
          isFixedPerm(left) && isFixedPerm(right)
        case sil.PermMul(left, right) =>
          isFixedPerm(left) && isFixedPerm(right)
        case sil.PermDiv(left, right) =>
          isFixedPerm(left)
        case sil.PermPermDiv(left, right) =>
          isFixedPerm(left) && isFixedPerm(right)
        case sil.IntPermMul(a, b) =>
          isFixedPerm(b)
        case sil.CondExp(cond, thn, els) =>
          isFixedPerm(thn) && isFixedPerm(els) // note: this doesn't take account of condition (due to being a syntactic check) - in theory could be overly-restrictive
        //case _: sil.FuncLikeApp => true
        case _ => (currentAbstractReads.isEmpty) // if using abstract reads, we must be conservative for local variables, field dereferences etc.
      }
    }

    def normalizePerm(e0: sil.Exp): sil.Exp = {
      var r = normalizePermHelper(e0)
      while (!r._1) {
        r = normalizePermHelper(r._2)
      }
      r._2
    }

    // Applies the following rewrite rules (a,b,c are perms, m,n are ints):
    //1 (a - b) --> (a + (-1*b))
    //2 (a+b)*c --> ((a*c) + (b*c))
    //2 a*(b+c) --> ((a*b) + (a*c))
    //2b (a+b)/n --> ((a/n) + (b/n))
    //3 (n*(b+c)) --> (n*b + n*c)
    //4 (m*(n*c)) --> ((m*n)*c)
    // (a*b) --> (b*a) if b is a "fixedPerm" and a is not
    // (a*wildcard) --> wildcard if isStrictlyPositivePerm(a)
    // a*(x?b:c) --> (x?(a*b):(a*c)) etc.
    // (x?b:c)/n --> (x?(b/n):(c/n)) etc.

    def normalizePermHelper(e0: sil.Exp): (Boolean, sil.Exp) = {
      // we use this flag to indicate whether something changed
      var done = true
      if (isFixedPerm(e0)) {
        // no rewriting of fixed permission necessary
        (true, e0)
      } else {
        // remove permission subtraction
        val e1 =
          e0.transform(
            { case sil.PermSub(left, right) => done = false
                sil.PermAdd(left, sil.IntPermMul(sil.IntLit(-1)(), right)())() },
            Traverse.BottomUp)

        // remove unary minus
        val e1a =
          e1.transform(
            { case sil.PermMinus(a) => done = false
                sil.IntPermMul(sil.IntLit(-1)(), a)() },
            Traverse.BottomUp)

        // move permission multiplications all the way to the inside
        val e2 = e1a.transform({
          case sil.PermMul(sil.PermAdd(a, b), c) => done = false
            sil.PermAdd(sil.PermMul(a, c)(), sil.PermMul(b, c)())()
          case sil.PermMul(a, sil.PermAdd(b, c)) => done = false
            sil.PermAdd(sil.PermMul(a, b)(), sil.PermMul(a, c)())()
        }, Traverse.BottomUp)

        // move permission divisions all the way to the inside
        val e2b = e2.transform({
          case sil.PermDiv(sil.PermAdd(a, b), n) => done = false
            sil.PermAdd(sil.PermDiv(a,n)(),sil.PermDiv(b,n)())()
        }, Traverse.BottomUp)

        // move permission divisions all the way to the inside
        val e2c = e2b.transform({
          case sil.PermPermDiv(sil.PermAdd(a, b), n) => done = false
            sil.PermAdd(sil.PermPermDiv(a,n)(),sil.PermDiv(b,n)())()
        }, Traverse.BottomUp)

        // move integer permission multiplications all the way to the inside
        val e3 = e2c.transform({
          case x@sil.IntPermMul(a, sil.PermAdd(b, c)) => done = false
            sil.PermAdd(sil.IntPermMul(a, b)(), sil.IntPermMul(a, c)())()
          case sil.IntPermMul(a, sil.PermMul(b, c)) => done = false
            sil.PermMul(b, sil.IntPermMul(a, c)())()
        }, Traverse.BottomUp)

        // group integer permission multiplications
        val e4 = e3.transform({
          case sil.IntPermMul(a, sil.IntPermMul(b, c)) => done = false
            sil.IntPermMul(sil.Mul(a, b)(), c)()
        }, Traverse.BottomUp)

        // move non-fixed part of permission multiplication to right-hand side
        val e5 = e4.transform({
          case sil.PermMul(a, b) if isFixedPerm(b) && !isFixedPerm(a) => done = false
            sil.PermMul(b, a)()
        }, Traverse.BottomUp)

        // collapse a*wildcard or wildcard*a to just wildcard, if a is known to be positive
        val e5a = e5.transform({
          case sil.PermMul(a, wp@sil.WildcardPerm()) if conservativeStaticIsStrictlyPositivePerm(a) => done = false
            sil.WildcardPerm()(wp.pos,wp.info)
          case sil.PermMul(wp@sil.WildcardPerm(),a) if conservativeStaticIsStrictlyPositivePerm(a) => done = false
            sil.WildcardPerm()(wp.pos,wp.info)
        }, Traverse.BottomUp)

        // propagate multiplication and division into conditional expressions
        val e6 = e5a.transform({
          case sil.IntPermMul(a, sil.CondExp(cond, thn, els)) => done = false
            sil.CondExp(cond, sil.IntPermMul(a,thn)(), sil.IntPermMul(a,els)())()
          case sil.IntPermMul(sil.CondExp(cond, thn, els),a) => done = false
            sil.CondExp(cond, sil.IntPermMul(thn,a)(), sil.IntPermMul(els,a)())()
          case sil.PermMul(a, sil.CondExp(cond, thn, els)) => done = false
            sil.CondExp(cond, sil.PermMul(a,thn)(), sil.PermMul(a,els)())()
          case sil.PermMul(sil.CondExp(cond, thn, els),a) => done = false
            sil.CondExp(cond, sil.PermMul(thn,a)(), sil.PermMul(els,a)())()
          case sil.PermDiv(sil.CondExp(cond, thn, els),n) => done = false
            sil.CondExp(cond, sil.PermDiv(thn,n)(), sil.PermDiv(els,n)())()
          case sil.PermPermDiv(sil.CondExp(cond, thn, els),n) => done = false
            sil.CondExp(cond, sil.PermPermDiv(thn,n)(), sil.PermDiv(els,n)())()
        }, Traverse.BottomUp)

        // propagate addition into conditional expressions
        val e7 = e6.transform({
          case sil.PermAdd(a, sil.CondExp(cond, thn, els)) => done = false
            sil.CondExp(cond, sil.PermAdd(a,thn)(), sil.PermAdd(a,els)())()
          case sil.PermAdd(sil.CondExp(cond, thn, els),a) => done = false
            sil.CondExp(cond, sil.PermAdd(thn,a)(), sil.PermAdd(els,a)())()
        }, Traverse.BottomUp)


        (done, e7)
      }
    }

  }
}
