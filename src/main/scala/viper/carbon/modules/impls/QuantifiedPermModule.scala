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
  private val maskName = Identifier("Mask")
  private val originalMask = GlobalVar(maskName, maskType)
  private var mask: Var = originalMask // When reading, don't use this directly: use either maskVar or maskExp as needed
  private def maskVar : Var = {assert (!usingOldState); mask}
  private def maskExp : Exp = (if (usingOldState) Old(mask) else mask)
  private val zeroMaskName = Identifier("ZeroMask")
  private val zeroMask = Const(zeroMaskName)
  private val zeroPMaskName = Identifier("ZeroPMask")
  override val zeroPMask = Const(zeroPMaskName)
  private val noPermName = Identifier("NoPerm")
  private val noPerm = Const(noPermName)
  private val fullPermName = Identifier("FullPerm")
  private val fullPerm = Const(fullPermName)
  private val permAddName = Identifier("PermAdd")
  private val permSubName = Identifier("PermSub")
  private val permDivName = Identifier("PermDiv")
  private val permConstructName = Identifier("Perm")
  private val goodMaskName = Identifier("GoodMask")
  private val hasDirectPermName = Identifier("HasDirectPerm")
  private val predicateMaskFieldName = Identifier("PredicateMaskField")
  private val wandMaskFieldName = Identifier("WandMaskField")


  private val resultMask = LocalVarDecl(Identifier("ResultMask"),maskType)
  private val summandMask1 = LocalVarDecl(Identifier("SummandMask1"),maskType)
  private val summandMask2 = LocalVarDecl(Identifier("SummandMask2"),maskType)
  private val sumMasks = Identifier("sumMask")
  private val tempMask = LocalVar(Identifier("TempMask"),maskType)

  private val qpMaskName = Identifier("QPMask")
  private val qpMask = LocalVar(qpMaskName, maskType)
  private var qpId = 0 //incremented each time a quantified permission expression is inhaled/exhaled, used to deal with
  // wildcards, inverse functions of receiver expressions

  private val inverseFunName = "invRecv" //prefix of function name for inverse functions used for inhale/exhale of qp
  private val rangeFunName = "qpRange" //prefix of function name for range functions (image of receiver expressions) used for inhale/exhale of qp
  private val triggerFunName = "neverTriggered" //prefix of function name for trigger function used for inhale/exhale of qp
  private var inverseFuncs: ListBuffer[Func] = new ListBuffer[Func](); //list of inverse functions used for inhale/exhale qp
  private var rangeFuncs: ListBuffer[Func] = new ListBuffer[Func](); //list of inverse functions used for inhale/exhale qp
  private var triggerFuncs: ListBuffer[Func] = new ListBuffer[Func](); //list of inverse functions used for inhale/exhale qp

  private val readMaskName = Identifier("readMask")
  private val updateMaskName = Identifier("updMask")

  private val readPMaskName = Identifier("readPMask")
  private val updatePMaskName = Identifier("updPMask")

  override val pmaskTypeDesugared = PMaskDesugaredRep(readPMaskName, updatePMaskName)

  override def preamble = {
    val obj = LocalVarDecl(Identifier("o")(axiomNamespace), refType)
    val field = LocalVarDecl(Identifier("f")(axiomNamespace), fieldType)
    val permInZeroMask = currentPermission(zeroMask, obj.l, field.l)
    val permInZeroPMask = currentPermission(zeroPMask, obj.l, field.l, true)

    // permission type
    TypeAlias(permType, Real) ::
      // mask and mask type
      (if (verifier.usePolyMapsInEncoding)
        TypeAlias(maskType, MapType(Seq(refType, fieldType), permType, fieldType.freeTypeVars))
      else TypeDecl(maskType)) ::
      GlobalVarDecl(maskName, maskType) ::
      // zero mask
      ConstDecl(zeroMaskName, maskType) ::
      Axiom(Forall(
        Seq(obj, field),
        Trigger(permInZeroMask),
        (permInZeroMask === noPerm))) ::
      // pmask type
      (if(verifier.usePolyMapsInEncoding)
        TypeAlias(pmaskType, MapType(Seq(refType, fieldType), Bool, fieldType.freeTypeVars))
      else TypeDecl(pmaskType)) ::
      // zero pmask
      ConstDecl(zeroPMaskName, pmaskType) ::
      Axiom(Forall(
        Seq(obj, field),
        Trigger(permInZeroPMask),
        permInZeroPMask === FalseLit())) ::
      // predicate mask function
      Func(predicateMaskFieldName,
        Seq(LocalVarDecl(Identifier("f"), predicateVersionFieldType())),
        predicateMaskFieldType) ::
      Func(wandMaskFieldName,
        Seq(LocalVarDecl(Identifier("f"), predicateVersionFieldType())),
        predicateMaskFieldType) ::
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
      // good mask
      Func(goodMaskName, LocalVarDecl(maskName, maskType), Bool) ++
      Axiom(Forall(stateModule.staticStateContributions(),
        Trigger(Seq(staticGoodState)),
        staticGoodState ==> staticGoodMask)) ++ {
      val perm = currentPermission(obj.l, field.l)
      Axiom(Forall(staticStateContributions(true, true) ++ obj ++ field,
        Trigger(Seq(staticGoodMask, perm)),
        // permissions are non-negative
        (staticGoodMask ==> ( perm >= noPerm &&
          // permissions for fields which aren't predicates are smaller than 1
          // permissions for fields which aren't predicates or wands are smaller than 1
          ((staticGoodMask && heapModule.isPredicateField(field.l).not && heapModule.isWandField(field.l).not) ==> perm <= fullPerm )))
      ))    } ++ {
      val obj = LocalVarDecl(Identifier("o")(axiomNamespace), refType)
      val field = LocalVarDecl(Identifier("f")(axiomNamespace), fieldType)
      val args = staticMask ++ Seq(obj, field)
      val funcApp = FuncApp(hasDirectPermName, args map (_.l), Bool)
      val permission = currentPermission(staticMask(0).l, obj.l, field.l)
      Func(hasDirectPermName, args, Bool) ++
        Axiom(Forall(
          staticMask ++ Seq(obj, field),
          Trigger(funcApp),
          funcApp <==> permissionPositive(permission)
        ))
    } ++ {
      val obj = LocalVarDecl(Identifier("o")(axiomNamespace), refType)
      val field = LocalVarDecl(Identifier("f")(axiomNamespace), fieldType)
      val args = Seq(resultMask,summandMask1,summandMask2)
      val funcApp = FuncApp(sumMasks, args map (_.l), Bool)
      val permResult = currentPermission(resultMask.l, obj.l, field.l)
      val permSummand1 = currentPermission(summandMask1.l,obj.l,field.l)
      val permSummand2 = currentPermission(summandMask2.l,obj.l,field.l)
      Func(sumMasks,args,Bool) ++
        Axiom(Forall(
          args++Seq(obj,field),
          Trigger(Seq(funcApp,permResult)) ++ Trigger(Seq(funcApp,permSummand1)) ++
            Trigger(Seq(funcApp,permSummand2)),
          funcApp ==> (permResult === (permSummand1 + permSummand2))
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

  def staticStateContributions(withHeap: Boolean, withPermissions: Boolean): Seq[LocalVarDecl] = if (withPermissions) Seq(LocalVarDecl(maskName, maskType)) else Seq()
  def currentStateContributions: Seq[LocalVarDecl] = Seq(LocalVarDecl(mask.name, maskType))
  def currentStateVars : Seq[Var] = Seq(mask)
  def currentStateExps: Seq[Exp] = Seq(maskExp)

  def initBoogieState: Stmt = {
    mask = originalMask
    resetBoogieState
  }
  def resetBoogieState = {
    (maskVar := zeroMask)
  }
  def initOldState: Stmt = {
    val mVar = maskVar
    Assume(Old(mVar) === mVar)
  }

  override def reset = {
    mask = originalMask
    qpId = 0
    inverseFuncs = new ListBuffer[Func]();
    rangeFuncs = new ListBuffer[Func]();
    triggerFuncs = new ListBuffer[Func]();
  }

  override def usingOldState = stateModuleIsUsingOldState

  override def predicateMaskField(pred: Exp): Exp = {
    FuncApp(predicateMaskFieldName, Seq(pred), pmaskType)
  }

  override def wandMaskField(wand: Exp): Exp = {
    FuncApp(wandMaskFieldName, Seq(wand), pmaskType)
  }

  def staticGoodMask = FuncApp(goodMaskName, LocalVar(maskName, maskType), Bool)

  private def permAdd(a: Exp, b: Exp): Exp = a + b
  private def permSub(a: Exp, b: Exp): Exp = a - b
  private def permDiv(a: Exp, b: Exp): Exp = a / b

  override def freshTempState(name: String): Seq[Var] = {
    Seq(LocalVar(Identifier(s"${name}Mask"), maskType))
  }

  override def restoreState(s: Seq[Var]): Unit = {
    mask = s(0)
  }

  /**
   * Can a location on a given receiver be read?
   */
  private def hasDirectPerm(mask: Exp, obj: Exp, loc: Exp): Exp =
    FuncApp(hasDirectPermName, Seq(maskExp, obj, loc), Bool)
  private def hasDirectPerm(obj: Exp, loc: Exp): Exp = hasDirectPerm(maskExp, obj, loc)
  override def hasDirectPerm(la: sil.LocationAccess): Exp = {
    la match {
      case sil.FieldAccess(rcv, field) =>
        hasDirectPerm(translateExp(rcv), translateLocation(la))
      case sil.PredicateAccess(_, _) =>
        hasDirectPerm(translateNull, translateLocation(la))
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

  override def sumMask(summandMask1: Seq[Exp], summandMask2: Seq[Exp]): Exp =
    FuncApp(sumMasks, currentMask++summandMask1++summandMask2,Bool)

  override def sumMask(resultMask: Seq[Exp], summandMask1: Seq[Exp], summandMask2: Seq[Exp]): Exp =
    FuncApp(sumMasks, resultMask++summandMask1++summandMask2,Bool)

  override def containsWildCard(e: sil.Exp): Boolean = {
    e match {
      case sil.AccessPredicate(loc, prm) =>
        val p = PermissionHelper.normalizePerm(prm)
        p.isInstanceOf[sil.WildcardPerm]
      case _ => false
    }
  }

  override def exhaleExp(e: sil.Exp, error: PartialVerificationError): Stmt = {
    e match {
      case sil.AccessPredicate(loc: LocationAccess, prm) =>
        val curPerm = currentPermission(loc)
        val p = PermissionHelper.normalizePerm(prm)

        def subtractFromMask(permToExhale: Exp) : Stmt =
          (if (!usingOldState) currentMaskAssignUpdate(loc, permSub(curPerm, permToExhale)) else Nil)

        val permVar = LocalVar(Identifier("perm"), permType)
        if (!p.isInstanceOf[sil.WildcardPerm]) {
          val prmTranslated = translatePerm(p)

          Assert(permissionPositiveInternal(prmTranslated, Some(p), true), error.dueTo(reasons.NegativePermission(p))) ++
            (permVar := prmTranslated) ++
            If(permVar !== noPerm,
              Assert(permLe(permVar, curPerm), error.dueTo(reasons.InsufficientPermission(loc))),
              Nil) ++
            subtractFromMask(permVar)
        } else {
          val curPerm = currentPermission(loc)
          val wildcard = LocalVar(Identifier("wildcard"), Real)

          Assert(curPerm > noPerm, error.dueTo(reasons.InsufficientPermission(loc))) ++
            LocalVarWhereDecl(wildcard.name, wildcard > noPerm) ++
            Havoc(wildcard) ++
            Assume(wildcard < curPerm) ++
            subtractFromMask(wildcard)
        }
      case w@sil.MagicWand(_,_) =>
        val wandRep = wandModule.getWandRepresentation(w)
        val curPerm = currentPermission(translateNull, wandRep)
        Comment("permLe")++
          Assert(permLe(fullPerm, curPerm), error.dueTo(reasons.MagicWandChunkNotFound(w))) ++
          (if (!usingOldState) currentMaskAssignUpdate(translateNull, wandRep, permSub(curPerm, fullPerm)) else Nil)

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
                                        translatedLoc:Exp)
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
        val translatedLocation = translateLocation(renaming(fieldAccess))

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
        (QuantifiedFieldComponents(translateLocalVarDecl(newV), translatedCond, translatedRcv, translatedPerms, translatedLocation),
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
            val translatedLocation = translateLocation(renamingFieldAccess)
            val translatedTriggers:Seq[Trigger] = renamedTriggers.map(trigger => (Trigger(trigger.exps.map(x => translateExp(x)))))

            val obj = LocalVarDecl(Identifier("o"), refType) // ref-typed variable, representing arbitrary receiver
            val field = LocalVarDecl(Identifier("f"), fieldType)
            val curPerm:Exp = currentPermission(obj.l,translatedLocation)
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
              validateTriggers(translatedLocals,Seq(Trigger(Seq(translateLocationAccess(translatedRecv, translatedLocation))),Trigger(Seq(currentPermission(qpMask,translatedRecv , translatedLocation))))) else Seq(recvTrigger)

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
            val permPositive = Assert(Forall(vsFresh.map(v => translateLocalVarDecl(v)),tr1, (translatedCond && funcPredModule.dummyFuncApp(translateLocationAccess(translatedRecv, translatedLocation))) ==> permissionPositiveInternal(translatedPerms,None,true)),
              error.dueTo(reasons.NegativePermission(perms)))

            //define permission requirement
            val permNeeded =
              if(isWildcard) {
            currentPermission(translatedRecv, translatedLocation) > noPerm
              } else {
                currentPermission(translatedRecv, translatedLocation) >= translatedPerms
              }

            //assert that we possess enough permission to exhale the permission indicated
            val enoughPerm = Assert(Forall(vsFresh.map(vFresh => translateLocalVarDecl(vFresh)), tr1, translatedCond ==> permNeeded),
              error.dueTo(reasons.InsufficientPermission(fieldAccess)))

            //if the permission is a wildcard, we check that we have some permission > 0 for all locations and assume that the permission substracted is smaller than the permission held.
            val wildcardAssms:Stmt =
              if(isWildcard) {
                (Assert(Forall(vsFresh.map(v => translateLocalVarDecl(v)), Seq(), translatedCond ==> (currentPermission(translatedRecv, translatedLocation) > noPerm)), error.dueTo(reasons.InsufficientPermission(fieldAccess))))++
                  (Assume(Forall(vsFresh.map(v => translateLocalVarDecl(v)), Seq(), translatedCond ==> (wildcard < currentPermission(translatedRecv, translatedLocation)))))
              } else {
                Nil
              }

            //assumptions for locations that gain permission
            val condTrueLocations = (condInv && (permGt(permInv, noPerm) && rangeFunApp)) ==> ((rcvInv === obj.l) && (
              (if (!usingOldState) {
                (  currentPermission(qpMask,obj.l,translatedLocation) === curPerm - permInv )
              } else {
                currentPermission(qpMask,obj.l,translatedLocation) === curPerm
              } )
              ))

            //assumption for locations that don't gain permission
            val condFalseLocations = ((condInv && (permGt(permInv, noPerm) && rangeFunApp)).not ==> (currentPermission(qpMask,obj.l,translatedLocation) === curPerm))

            //assumption for locations that are definitely independent of any of the locations part of the QP (i.e. different
            //field)
            val independentLocations = Assume(Forall(Seq(obj,field), //Trigger(currentPermission(obj.l,field.l))++
              Trigger(currentPermission(qpMask,obj.l,field.l)),(field.l !== translatedLocation) ==>
              (currentPermission(obj.l,field.l) === currentPermission(qpMask,obj.l,field.l))) )
            val triggersForPermissionUpdateAxiom = Seq(Trigger(currentPermission(qpMask,obj.l,translatedLocation)))

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
              CommentBlock("assume permission updates for independent locations", independentLocations) ++
              (mask := qpMask)

            vsFresh.foreach(v => env.undefine(v.localVar))

            res1
          //Predicate access
          case predAccPred@sil.PredicateAccessPredicate(PredicateAccess(args, predname), perms) =>
            // alpha renaming, to avoid clashes in context, use vFresh instead of v
            val vsFresh = vs.map(v => env.makeUniquelyNamed(v))
            val vsFreshBoogie = vsFresh.map(vFresh => env.define(vFresh.localVar))
            // create fresh variables for the formal arguments of the predicate definition
            val predicate = program.findPredicate(predname)
            val formals = predicate.formalArgs
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
            val curPerm = currentPermission(predAccPred.loc)
            val translatedLocation = translateLocation(predAccPred.loc)

            val rangeFunApp = FuncApp(rangeFun.name, freshFormalBoogieVars, rangeFun.typ) // range(o,...): used to test whether an element of the mapped-to type is in the image of the QP's domain, projected by the receiver expression
            val rangeFunRecvApp = FuncApp(rangeFun.name, translatedArgs, rangeFun.typ) // range(e(v),...)

            //define inverse functions
            lazy val candidateTriggers : Seq[Trigger] = validateTriggers(translatedLocals, Seq(Trigger(translateLocationAccess(predAccPred.loc)),Trigger(currentPermission(translateNull, translatedLocation))))

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
                (currentPermission(translateNull, translatedLocation) > RealLit(0))
              } else {
                (currentPermission(translateNull, translatedLocation) >= translatedPerms)
              }

            val enoughPerm = Assert(Forall(translatedLocals, tr1, translatedCond ==> permNeeded),
              error.dueTo(reasons.InsufficientPermission(predAccPred.loc)))

            //if we exhale a wildcard permission, assert that we hold some permission to all affected locations and restrict the wildcard value
            val wildcardAssms:Stmt =
              if(isWildcard) {
                Assert(Forall(translatedLocals, Seq(), translatedCond ==> (currentPermission(translateNull, translatedLocation) > noPerm)), error.dueTo(reasons.InsufficientPermission(predAccPred.loc))) ++
                  Assume(Forall(translatedLocals, Seq(), translatedCond ==> (wildcard < currentPermission(translateNull, translatedLocation))))
              } else {
                Nil
              }

            //Assume map update for affected locations
            val gl = new PredicateAccess(freshFormalVars, predname) (predicate.pos, predicate.info, predicate.errT)
            val general_location = translateLocation(gl)

            //trigger:
            val triggerForPermissionUpdateAxioms = Seq(Trigger(currentPermission(qpMask,translateNull, general_location)) /*,Trigger(currentPermission(mask, translateNull, general_location)),Trigger(invFunApp)*/ )
            val permissionsMap = Assume(Forall(freshFormalBoogieDecls,triggerForPermissionUpdateAxioms, ((condInv && (permGt(permInv, noPerm)) && rangeFunApp) ==> (conjoinedInverseAssumptions && (currentPermission(qpMask,translateNull, general_location) === currentPermission(translateNull, general_location) - permInv)))))

            //Assume no change for independent locations: different predicate or no predicate
            val obj = LocalVarDecl(Identifier("o"), refType)
            val field = LocalVarDecl(Identifier("f"), fieldType)
            val fieldVar = LocalVar(Identifier("f"), fieldType)
            val independentLocations = Assume(Forall(Seq(obj,field), Seq(Trigger(currentPermission(obj.l, field.l)), Trigger(currentPermission(qpMask, obj.l, field.l))),
              ((obj.l !== translateNull) ||  isPredicateField(fieldVar).not || (getPredicateId(fieldVar) !== IntLit(getPredicateId(predname)) ))  ==>
                (currentPermission(obj.l,field.l) === currentPermission(qpMask,obj.l,field.l))))
            //same predicate, but not satisfying the condition
            val independentPredicate = Assume(Forall(freshFormalBoogieDecls, triggerForPermissionUpdateAxioms, ((condInv && (permGt(permInv, noPerm)) && rangeFunApp).not) ==> (currentPermission(qpMask,translateNull, general_location) === currentPermission(translateNull, general_location))))


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

            val reas = reasons.QPAssertionNotInjective(predAccPred.loc)
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
              CommentBlock("check if receiver " + predAccPred.toString() + " is injective",injectiveAssertion) ++
              CommentBlock("check if sufficient permission is held", enoughPerm) ++
              CommentBlock("assumptions for inverse of receiver " + predAccPred.toString(), Assume(invAssm1)++ Assume(invAssm2)) ++
              CommentBlock("assume permission updates for predicate " + predicate.name, permissionsMap ++
              independentPredicate) ++
              CommentBlock("assume permission updates for independent locations ", independentLocations) ++
              (mask := qpMask)

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
        res
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
    val curPerm = currentPermission(e.rcv,e.loc)
    currentMaskAssignUpdate(e.rcv, e.loc, permSub(curPerm,e.transferAmount))
  }

  override def transferValid(e:TransferableEntity):Seq[(Stmt,Exp)] = {
    Nil
  }

  override def inhaleExp(e: sil.Exp, error: PartialVerificationError): Stmt = {
    inhaleAux(e, Assume, error)
  }

  override def inhaleWandFt(w: sil.MagicWand): Stmt = {
    val wandRep = wandModule.getWandFtSmRepresentation(w, 0)
    val curPerm = currentPermission(translateNull, wandRep)
    if (!usingOldState) currentMaskAssignUpdate(translateNull, wandRep, permAdd(curPerm, fullPerm)) else Nil
  }

  override def exhaleWandFt(w: sil.MagicWand): Stmt = {
      val wandRep = wandModule.getWandFtSmRepresentation(w, 0)
      val curPerm = currentPermission(translateNull, wandRep)
      (if (!usingOldState) currentMaskAssignUpdate(translateNull, wandRep, permSub(curPerm, fullPerm)) else Nil)
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
        stmts ++
         (permVar := permVal) ++
          (if (perm.isInstanceOf[WildcardPerm])
            assmsToStmt(checkNonNullReceiver(loc))
          else
            Assert(permissionPositiveInternal(permVar, Some(perm), true), error.dueTo(reasons.NegativePermission(perm))) ++
            assmsToStmt(permissionPositiveInternal(permVar, Some(perm), false) ==> checkNonNullReceiver(loc))
          ) ++
          (if (!usingOldState) currentMaskAssignUpdate(loc, permAdd(curPerm, permVar)) else Nil)
      case w@sil.MagicWand(left,right) =>
        val wandRep = wandModule.getWandRepresentation(w)
        val curPerm = currentPermission(translateNull, wandRep)
        if (!usingOldState) currentMaskAssignUpdate(translateNull, wandRep, permAdd(curPerm, fullPerm)) else Nil

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
           val translatedLocation = translateLocation(Expressions.instantiateVariables(fieldAccess, vs.map(v => v.localVar), vsFresh.map(vFresh => vFresh.localVar)))

           //define inverse function and inverse terms
           val obj = LocalVarDecl(Identifier("o"), refType)
           val field = LocalVarDecl(Identifier("f"), fieldType)
           val curPerm: Exp = currentPermission(obj.l, translatedLocation)

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
             validateTriggers(translatedLocals, Seq(Trigger(Seq(translateLocationAccess(translatedRecv, translatedLocation))), Trigger(Seq(currentPermission(qpMask, translatedRecv, translatedLocation))))) else Seq(recvTrigger)

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
               (translatedRecv !== translateNull)))

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
                    permGt(currentPermission(qpMask,obj.l,translatedLocation), curPerm)
                  else
                    (currentPermission(qpMask,obj.l,translatedLocation) === curPerm)
                ))
            )
            else (
              // for non wildcards
              ((condInv && permGt(permInv, noPerm))&&rangeFunApp) ==>
                ((permGt(permInv, noPerm) ==> (rcvInv === obj.l)) && (
                  if (!usingOldState)
                    (currentPermission(qpMask,obj.l,translatedLocation) === curPerm + permInv)
                  else
                    (currentPermission(qpMask,obj.l,translatedLocation) === curPerm)
                ))
            )
           //Define Permission to all locations of field f for locations where condition does not applies: no change
           val condFalseLocations =
            if (isWildcard)
              ((condInv && rangeFunApp).not ==> (currentPermission(qpMask,obj.l,translatedLocation) === curPerm))
            else
              (((condInv && permGt(permInv, noPerm))&&rangeFunApp).not ==> (currentPermission(qpMask,obj.l,translatedLocation) === curPerm))

           //Define Permissions to all independent locations: no change
           val independentLocations = Assume(Forall(Seq(obj, field), Trigger(currentPermission(obj.l, field.l)) ++
             Trigger(currentPermission(qpMask, obj.l, field.l)), (field.l !== translatedLocation) ==>
             (currentPermission(obj.l, field.l) === currentPermission(qpMask, obj.l, field.l))))

           val triggerForPermissionUpdateAxiom = Seq(/*Trigger(curPerm),*/ Trigger(currentPermission(qpMask, obj.l, translatedLocation)) /*,Trigger(invFunApp)*/)

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
             CommentBlock("Define permissions", Assume(Forall(obj,triggerForPermissionUpdateAxiom, condTrueLocations&&condFalseLocations )) ++
               independentLocations) ++
             (mask := qpMask)

           vsFresh.foreach(vFresh => env.undefine(vFresh.localVar))

           res1
         //Predicate access
         case predAccPred@sil.PredicateAccessPredicate(PredicateAccess(args, predname), perms) =>
           // alpha renaming, to avoid clashes in context, use vFresh instead of v
           val vsFresh = vs.map(v => env.makeUniquelyNamed(v))
           vsFresh.map(vFresh => env.define(vFresh.localVar))
           // create fresh variables for the formal arguments of the predicate definition
           val predicate = program.findPredicate(predname)
           val formals = predicate.formalArgs
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
           val translatedLocation = translateLocation(predAccPred.loc)

           val rangeFunApp = FuncApp(rangeFun.name, freshFormalBoogieVars, rangeFun.typ) // range(o,...): used to test whether an element of the mapped-to type is in the image of the QP's domain, projected by the receiver expression
           val rangeFunRecvApp = FuncApp(rangeFun.name, translatedArgs, rangeFun.typ) // range(e(v),...)

           //define inverse functions
           lazy val candidateTriggers : Seq[Trigger] = validateTriggers(translatedLocals, Seq(Trigger(translateLocationAccess(predAccPred.loc)),Trigger(currentPermission(translateNull, translatedLocation))))

           val providedTriggers : Seq[Trigger] = validateTriggers(translatedLocals, translatedTriggers)

           val tr1: Seq[Trigger] = funcPredModule.rewriteTriggersToExpressionsUsedInTriggers(candidateTriggers ++ providedTriggers)

           val equalities = (0 until funApps.length).foldLeft(TrueLit(): Exp)((soFar, i) => BinExp(soFar, And, funApps(i) === translatedLocals(i).l))

           val invAssm1 = Forall(translatedLocals, tr1, (translatedCond && permGt(translatedPerms, noPerm)) ==> (equalities && rangeFunRecvApp))
           //for each argument, define the second inverse function
           val eqExpr = (argsInv zip freshFormalBoogieVars).map(x => x._1 === x._2)
           val conjoinedInverseAssumptions = eqExpr.foldLeft(TrueLit():Exp)((soFar,exp) => BinExp(soFar,And,exp))
           val invAssm2 = Forall(freshFormalBoogieDecls, Trigger(invFunApps), ((condInv && permGt(permInv, noPerm)) && rangeFunApp) ==> conjoinedInverseAssumptions)

           //define arguments needed to describe map updates
           val formalPredicate = new PredicateAccess(freshFormalVars, predname) (predicate.pos, predicate.info, predicate.errT)
           val general_location = translateLocation(formalPredicate)

            //trigger for both map descriptions
           val triggerForPermissionUpdateAxioms = Seq(Trigger(currentPermission(qpMask,translateNull, general_location))/*, Trigger(invFunApp)*/)

           // TD: We do not assume anymore that the permissions are non-negative, and we need to check them
           // permissions non-negative
           // val permPositive = Assume(Forall(translatedLocals, tr1, translatedCond ==> permissionPositiveInternal(translatedPerms,None,true)))
           //check that given the condition, the permission held should be non-negative
           val permPositive = Assert(Forall(translatedLocals, tr1, translatedCond ==> permissionPositiveInternal(translatedPerms,None,true)),
             error.dueTo(reasons.NegativePermission(perms)))


         //assumptions for predicates that gain permission
           val permissionsMap = Assume(
             {
               val exp = ((condInv && permGt(permInv, noPerm)) && rangeFunApp) ==> ((permGt(permInv, noPerm) ==> conjoinedInverseAssumptions) && (currentPermission(qpMask,translateNull, general_location) === currentPermission(translateNull, general_location) + permInv))
               if (freshFormalBoogieDecls.isEmpty)
                 exp
               else
                 Forall(freshFormalBoogieDecls,triggerForPermissionUpdateAxioms, exp)
             })
           //assumptions for predicates of the same type which do not gain permission
           val independentPredicate = Assume(
             {
               val exp = (((condInv && permGt(permInv, noPerm)) && rangeFunApp).not) ==> (currentPermission(qpMask,translateNull, general_location) === currentPermission(translateNull, general_location))
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
           val field = LocalVarDecl(Identifier("f"), fieldType)
           val fieldVar = LocalVar(Identifier("f"), fieldType)
           val independentLocations = Assume(Forall(Seq(obj,field), Seq(Trigger(currentPermission(obj.l, field.l)), Trigger(currentPermission(qpMask, obj.l, field.l))),
             ((obj.l !== translateNull) ||  isPredicateField(fieldVar).not || (getPredicateId(fieldVar) !== IntLit(getPredicateId(predname)) ))  ==>
               (currentPermission(obj.l,field.l) === currentPermission(qpMask,obj.l,field.l))))


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
           val err = error.dueTo(reasons.QPAssertionNotInjective(predAccPred.loc))
           val injectiveAssertion = Assert(Forall((translatedLocals ++ translatedLocals2), injectTrigger,injectiveCond ==> ineqExpr), err)


           val res1 = Havoc(qpMask) ++
             stmts ++
             (if (!verifier.assumeInjectivityOnInhale) CommentBlock("check if receiver " + predAccPred.toString() + " is injective",injectiveAssertion)
             else Nil) ++
             CommentBlock("Define Inverse Function", Assume(invAssm1) ++
               Assume(invAssm2)) ++
             (if (!isWildcard) (MaybeComment("Check that permission expression is non-negative for all fields", permPositive)) else Nil) ++
             CommentBlock("Define updated permissions", permissionsMap) ++
             CommentBlock("Define independent locations", (independentLocations ++
             independentPredicate)) ++
             (mask := qpMask)

           vsFresh.foreach(vFresh => env.undefine(vFresh.localVar))
           v2s.foreach(v2 => env.undefine(v2.localVar))
           freshFormalVars.foreach(x => env.undefine(x))

           res1
         case _ =>
           Nil
       }
       res
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
    val curPerm = currentPermission(e.rcv,e.loc)
    /* GP: probably redundant in current transfer as these assumputions are implied

      (cond := cond && permissionPositive(e.transferAmount, None,true)) ++
      {
      e match {
        case TransferableFieldAccessPred(rcv,_,_,_) => (cond := cond && checkNonNullReceiver(rcv))
        case _ => Nil
      }
    } ++ */
    if (!usingOldState) currentMaskAssignUpdate(e.rcv, e.loc, permAdd(curPerm, e.transferAmount)) else Nil
  }

  override def tempInitMask(rcv: Exp, loc:Exp):(Seq[Exp], Stmt) = {
    val setMaskStmt = tempMask := maskUpdate(zeroMask, rcv, loc, fullPerm)
    (tempMask, setMaskStmt)
  }

  def rcvAndFieldExp(f: sil.LocationAccess) : (Exp, Exp) =
    f match {
      case sil.FieldAccess(rcv, _) => (translateExp(rcv), translateLocation(f))
      case sil.PredicateAccess(_, _) => (translateNull, translateLocation(f))
    }

  def currentPermission(loc: sil.LocationAccess): Exp = {
    loc match {
      case sil.FieldAccess(rcv, field) =>
        currentPermission(translateExp(rcv), translateLocation(loc))
      case sil.PredicateAccess(_, _) =>
        currentPermission(translateNull, translateLocation(loc))
    }
  }

  def currentPermission(rcv: Exp, location: Exp): Exp = {
    currentPermission(maskExp, rcv, location)
  }
  def currentPermission(mask: Exp, rcv: Exp, location: Exp, isPMask: Boolean = false): Exp = {
    if(verifier.usePolyMapsInEncoding) {
      MapSelect(mask, Seq(rcv, location))
    } else {
      FuncApp( if(isPMask) { readPMaskName } else { readMaskName },
               Seq(mask, rcv, location),
               if(isPMask) { Bool } else { permType }
      )
    }
  }

  override def permissionLookup(la: sil.LocationAccess) : Exp = {
    currentPermission(la)
  }

  private def currentMaskAssignUpdate(loc: LocationAccess, newPerm: Exp) : Stmt = {
    val (rcv, field) = rcvAndFieldExp(loc)
    currentMaskAssignUpdate(rcv, field, newPerm)
  }

  private def currentMaskAssignUpdate(rcv: Exp, field: Exp, newPerm: Exp) : Stmt = {
    mask := maskUpdate(mask, rcv, field, newPerm)
  }

  private def maskUpdate(mask: Exp, loc: LocationAccess, newPerm: Exp) : Exp = {
    val (rcv, field) = rcvAndFieldExp(loc)
    maskUpdate(mask, rcv, field, newPerm)
  }

  private def maskUpdate(mask: Exp, rcv: Exp, field: Exp, newPerm: Exp) : Exp = {
    if(verifier.usePolyMapsInEncoding)
      MapUpdate(mask, Seq(rcv, field), newPerm)
    else
      FuncApp(updateMaskName, Seq(mask, rcv, field, newPerm), maskType)
  }

  override def currentMask = Seq(maskExp)
  override def staticMask = Seq(LocalVarDecl(maskName, maskType))
  override def staticPermissionPositive(rcv: Exp, loc: Exp) = {
    hasDirectPerm(staticMask(0).l, rcv, loc)
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
      case sil.CurrentPerm(loc: LocationAccess) =>
        currentPermission(loc)
      case sil.CurrentPerm(res: ResourceAccess) =>
        //Magic wands
        sys.error("Carbon does not support magic wands in perm expressions, see Carbon issue #243")
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
            currentMaskAssignUpdate(sil.FieldAccess(target, field)(), currentPermission(sil.FieldAccess(target, field)()) + fullPerm)
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

  override def simplePartialCheckDefinednessAfter(e: sil.Exp, error: PartialVerificationError, makeChecks: Boolean): Stmt = {

    val stmt: Stmt = if(makeChecks) (
      e match {
        case fa@sil.LocationAccess(_) =>
          Assert(hasDirectPerm(fa), error.dueTo(reasons.InsufficientPermission(fa)))
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

  object PermissionHelper {

    def isStrictlyPositivePerm(e: sil.Exp): Exp = {
      require(e isSubtype sil.Perm, s"found ${e.typ} ($e), but required Perm")
      val backup = permissionPositiveInternal(translatePerm(e), Some(e))
      e match {
        case sil.NoPerm() => FalseLit()
        case sil.FullPerm() => TrueLit()
        case sil.WildcardPerm() => TrueLit()
        case sil.EpsilonPerm() =>  sys.error("epsilon permissions are not supported by this permission module")
        case x: sil.LocalVar if isAbstractRead(x) => TrueLit()
        case sil.CurrentPerm(loc) => backup
        case sil.FractionalPerm(left, right) =>
          val (l, r) = (translateExp(left), translateExp(right))
          ((l > IntLit(0)) && (r > IntLit(0))) || ((l < IntLit(0)) && (r < IntLit(0)))
        case sil.PermMinus(a) =>
          isStrictlyNegativePerm(a)
        case sil.PermAdd(left, right) =>
          (isStrictlyPositivePerm(left) && isStrictlyPositivePerm(right)) || backup
        case sil.PermSub(left, right) => backup
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
        case _ => backup
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
      val backup = UnExp(Not,permissionPositiveInternal(translatePerm(e), Some(e), true))
      e match {
        case sil.NoPerm() => FalseLit() // strictly negative
        case sil.FullPerm() => FalseLit()
        case sil.WildcardPerm() => FalseLit()
        case sil.EpsilonPerm() =>  sys.error("epsilon permissions are not supported by this permission module")
        case x: sil.LocalVar if isAbstractRead(x) => FalseLit()
        case sil.CurrentPerm(loc) => backup
        case sil.FractionalPerm(left, right) =>
          val (l, r) = (translateExp(left), translateExp(right))
          ((l < IntLit(0)) && (r > IntLit(0))) || ((l > IntLit(0)) && (r < IntLit(0)))
        case sil.PermMinus(a) =>
          isStrictlyPositivePerm(a)
        case sil.PermAdd(left, right) =>
          (isStrictlyNegativePerm(left) && isStrictlyNegativePerm(right)) || backup
        case sil.PermSub(left, right) => backup
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
        case _ => backup
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
