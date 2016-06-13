/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules.impls

import viper.carbon.modules._
import viper.carbon.modules.components._
import viper.silver.ast.utility.Expressions
import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.boogie.Implicits._
import viper.silver.verifier._
import viper.silver.verifier.PartialVerificationError
import viper.silver.ast.{Literal, NoInfo, NoPosition, NullLit, PredicateAccess, PredicateAccessPredicate, WildcardPerm}
import viper.silver.ast.{And => _, Bool => _, Div => _, Exp => _, Int => _, LocalVar => _, LocalVarDecl => _, Mul => _, Not => _, Stmt => _}
import viper.carbon.verifier.Verifier

import scala.collection.mutable.ListBuffer

/**
 * An implementation of [[viper.carbon.modules.PermModule]] supporting quantified permissions.
 */
class QuantifiedPermModule(val verifier: Verifier)
  extends PermModule
  with CarbonStateComponent
  with InhaleComponent
  with ExhaleComponent
  with TransferComponent
  with SimpleStmtComponent
  with DefinednessComponent {

  import verifier._
  import heapModule._
  import mainModule._
  import expModule._
  import stateModule._

  def name = "Permission module (with quantified permission support)"

  override def start() {
    stateModule.register(this)
    exhaleModule.register(this)
    inhaleModule.register(this)
    stmtModule.register(this)
    expModule.register(this)
    wandModule.register(this)
  }

  implicit val namespace = verifier.freshNamespace("perm")
  private val axiomNamespace = verifier.freshNamespace("perm.axiom")
  private val permTypeName = "Perm"
  private val maskTypeName = "MaskType"
  private val maskType = NamedType(maskTypeName)
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
  private var inverseFuncs: ListBuffer[Func] = new ListBuffer[Func](); //list of inverse functions used for inhale/exhale qp


  override def preamble = {
    val obj = LocalVarDecl(Identifier("o")(axiomNamespace), refType)
    val field = LocalVarDecl(Identifier("f")(axiomNamespace), fieldType)
    val permInZeroMask = MapSelect(zeroMask, Seq(obj.l, field.l))
    val permInZeroPMask = MapSelect(zeroPMask, Seq(obj.l, field.l))
    // permission type
    TypeAlias(permType, Real) ::
      // mask and mask type
      TypeAlias(maskType, MapType(Seq(refType, fieldType), permType, fieldType.freeTypeVars)) ::
      GlobalVarDecl(maskName, maskType) ::
      // zero mask
      ConstDecl(zeroMaskName, maskType) ::
      Axiom(Forall(
        Seq(obj, field),
        Trigger(permInZeroMask),
        (permInZeroMask === RealLit(0)))) ::
      // pmask type
      TypeAlias(pmaskType, MapType(Seq(refType, fieldType), Bool, fieldType.freeTypeVars)) ::
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
      // permission amount constants
      ConstDecl(noPermName, permType) ::
      Axiom(noPerm === RealLit(0)) ::
      ConstDecl(fullPermName, permType) ::
      Axiom(fullPerm === RealLit(1)) ::
      // permission constructor
      Func(permConstructName, Seq(LocalVarDecl(Identifier("a"), Real), LocalVarDecl(Identifier("b"), Real)), permType) :: Nil ++
      // good mask
      Func(goodMaskName, LocalVarDecl(maskName, maskType), Bool) ++
      Axiom(Forall(stateModule.staticStateContributions,
        Trigger(Seq(staticGoodState)),
        staticGoodState ==> staticGoodMask)) ++ {
      val perm = currentPermission(obj.l, field.l)
      Axiom(Forall(staticStateContributions ++ obj ++ field,
        Trigger(Seq(staticGoodMask, perm)),
        // permissions are non-negative
        (staticGoodMask ==> ( perm >= RealLit(0) &&
          // permissions for fields which aren't predicates are smaller than 1
          // permissions for fields which aren't predicates or wands are smaller than 1
          ((staticGoodMask && heapModule.isPredicateField(field.l).not && heapModule.isWandField(field.l).not) ==> perm <= RealLit(1) )))
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
      MaybeCommentedDecl("Functions used as inverse of receiver expressions in quantified permissions during inhale and exhale",
        inverseFuncs)
    } 
  }

  def permType = NamedType(permTypeName)

  def staticStateContributions: Seq[LocalVarDecl] = Seq(LocalVarDecl(maskName, maskType))
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
    allowLocationAccessWithoutPerm = false
    qpId = 0
    inverseFuncs = new ListBuffer[Func]();
  }

  override def usingOldState = stateModuleIsUsingOldState

  override def predicateMaskField(pred: Exp): Exp = {
    FuncApp(predicateMaskFieldName, Seq(pred), pmaskType)
  }

  def staticGoodMask = FuncApp(goodMaskName, LocalVar(maskName, maskType), Bool)

  private def permAdd(a: Exp, b: Exp): Exp = a + b
  private def permSub(a: Exp, b: Exp): Exp = a - b
  private def permDiv(a: Exp, b: Exp): Exp = a / b

  override def freshTempState(name: String): Seq[Var] = {
    Seq(LocalVar(Identifier(s"${name}Mask"), maskType))
  }

  override def restoreState(s: Seq[Var]) {
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
  private def permissionPositive(permission: Exp, silPerm: Option[sil.Exp] = None, zeroOK : Boolean = false): Exp = {
    (permission, silPerm) match {
      case (x, _) if permission == fullPerm => TrueLit()
      case (_, Some(sil.FullPerm())) => TrueLit()
      case (_, Some(sil.WildcardPerm())) => TrueLit()
      case (_, Some(sil.NoPerm())) => if (zeroOK) TrueLit() else FalseLit()
      case _ => if(zeroOK) permission >= RealLit(0) else permission > RealLit(0)
    }
  }

  def sumMask(summandMask1: Seq[Exp], summandMask2: Seq[Exp]): Exp =
    FuncApp(sumMasks, currentMask++summandMask1++summandMask2,Bool)

  override def exhaleExp(e: sil.Exp, error: PartialVerificationError): Stmt = {
    e match {
      case sil.AccessPredicate(loc, prm) =>
        val p = PermissionSplitter.normalizePerm(prm)
        val perms = PermissionSplitter.splitPerm(p) filter (x => x._1 - 1 == exhaleModule.currentPhaseId)
        (if (exhaleModule.currentPhaseId == 0)
          (if (!p.isInstanceOf[WildcardPerm])
            Assert(permissionPositive(translatePerm(p), Some(p), true), error.dueTo(reasons.NegativePermission(p))) else Nil: Stmt) ++ Nil // check amount is non-negative
        else Nil) ++
          (if (perms.size == 0) {
            Nil
          } else {
            val permVar = LocalVar(Identifier("perm"), permType)
            val curPerm = currentPermission(loc)
            var onlyWildcard = true
            (permVar := noPerm) ++
              (for ((_, cond, perm) <- perms) yield {
                val (permVal, wildcard, stmts): (Exp, Exp, Stmt) =
                  if (perm.isInstanceOf[WildcardPerm]) {
                    val w = LocalVar(Identifier("wildcard"), Real)
                    (w, w, LocalVarWhereDecl(w.name, w > RealLit(0)) :: Havoc(w) :: Nil)
                  } else {
                    onlyWildcard = false
                    (translatePerm(perm), null, Nil)
                  }
                If(cond,
                  stmts ++
                    (permVar := permAdd(permVar, permVal)) ++
                    (if (perm.isInstanceOf[WildcardPerm]) {
                      (Assert(curPerm > RealLit(0), error.dueTo(reasons.InsufficientPermission(loc))) ++
                        Assume(wildcard < curPerm)): Stmt
                    } else {
                      Nil
                    }),
                  Nil)
              }).flatten ++
              (if (onlyWildcard) Nil else if (exhaleModule.currentPhaseId + 1 == 2) {
                If(permVar !== noPerm,
                  (Assert(curPerm > RealLit(0), error.dueTo(reasons.InsufficientPermission(loc))) ++
                    Assume(permVar < curPerm)): Stmt, Nil)
              } else {
                If(permVar !== noPerm,
                  Assert(permLe(permVar, curPerm), error.dueTo(reasons.InsufficientPermission(loc))), Nil)
              }) ++
              (if (!usingOldState) curPerm := permSub(curPerm, permVar) else Nil)
          })
      case w@sil.MagicWand(_,_) =>
        val wandRep = wandModule.getWandRepresentation(w)
        val curPerm = currentPermission(translateNull, wandRep)
        Comment("permLe")++ //using RealLit(1.0) instead of FullPerm due to permLe's implementation
          Assert(permLe(RealLit(1.0), curPerm), error.dueTo(reasons.MagicWandChunkNotFound(w))) ++
          (if (!usingOldState) curPerm := permSub(curPerm, RealLit(1.0)) else Nil)

      case qp@sil.utility.QuantifiedPermissions.QuantifiedPermission(v, cond, expr) =>

        //quantified permissions
        val res = {
          if (qp.isPure) {
          Nil
          } else {
            evaluateExhale(v, cond, expr, error)++Nil
          }
        }
        res
      case _ => Nil
    }
  }

  def evaluateExhale(v: sil.LocalVarDecl, cond:sil.Exp, expr:sil.Exp, error: PartialVerificationError): Stmt = {
    val res = expr match {

      case qp@sil.utility.QuantifiedPermissions.QuantifiedPermission(v, cond, expr)  =>
        //TODO: nested quantifier
        Nil
      //Field Access
      case sil.FieldAccessPredicate(fieldAccess@sil.FieldAccess(recv, f), perms) =>
        // alpha renaming, to avoid clashes in context, use vFresh instead of v
        val vFresh = env.makeUniquelyNamed(v); env.define(vFresh.localVar);
        var isWildcard = false
        def renaming[E <: sil.Exp] = (e:E) => Expressions.renameVariables(e, v.localVar, vFresh.localVar)

        val (renamingCond, renamingRecv, renamingPerms, renamingFieldAccess) = (renaming(cond), renaming(recv), renaming(perms), renaming(fieldAccess))
        val (translatedCond, translatedRecv) = (translateExp(renamingCond), translateExp(renamingRecv))

        val translatedLocal = translateLocalVarDecl(vFresh)

        val (translatedPerms, stmts, wildcard) = {
          if (perms.isInstanceOf[WildcardPerm]) {
            isWildcard = true
            val w = LocalVar(Identifier("wildcard"), Real)
            (w, LocalVarWhereDecl(w.name, w > RealLit(0)) :: Havoc(w) :: Nil, w)
          } else {
            (translateExp(renamingPerms), Nil, null)
          }
        }

        val translatedLocation = translateLocation(renamingFieldAccess)

        val obj = LocalVarDecl(Identifier("o"), refType)
        val field = LocalVarDecl(Identifier("f"), fieldType)

        val curPerm:Exp = currentPermission(obj.l,translatedLocation)
        val invFun = addInverseFunction(vFresh.typ)
        val invFunApp = FuncApp(invFun.name, Seq(obj.l), invFun.typ )

        val (condInv, rcvInv, permInv) = (translatedCond.replace(env.get(vFresh.localVar), invFunApp),translatedRecv.replace(env.get(vFresh.localVar), invFunApp),translatedPerms.replace(env.get(vFresh.localVar), invFunApp) )

        val tr1 =
          if(translatedRecv.isInstanceOf[LocalVar]) {
            Seq()
          } else {
            Seq(Trigger(translatedRecv))
          }

        val invAssm1 = (Forall(Seq(translatedLocal), tr1, translatedCond ==> (FuncApp(invFun.name, Seq(translatedRecv), invFun.typ) === translatedLocal.l )))
        val invAssm2 = Forall(Seq(obj), Seq(Trigger(FuncApp(invFun.name, Seq(obj.l), invFun.typ))), condInv ==> (rcvInv === obj.l) )

        //val notNull = Assert(Forall(translateLocalVarDecl(vFresh), Seq(), translatedCond && permissionPositive(translatedPerms) ==> checkNonNullReceiver(renamingFieldAccess)),
        //  error.dueTo(reasons.ReceiverNull(fieldAccess)))

        val permPositive = Assert(Forall(translateLocalVarDecl(vFresh), Seq(), translatedCond ==> permissionPositive(translatedPerms,None,true)),
          error.dueTo(reasons.NegativePermission(perms)))

        val permNeeded =
          if(isWildcard) {
            currentPermission(translatedRecv, translatedLocation) > RealLit(0)
          } else {
            currentPermission(translatedRecv, translatedLocation) >= translatedPerms
          }
        val enoughPerm = Assert(Forall(translateLocalVarDecl(vFresh), Seq(), translatedCond ==> permNeeded),
          error.dueTo(reasons.InsufficientPermission(fieldAccess)))

        val wildcardAssms:Stmt =
          if(isWildcard) {
            (Assert(Forall(translateLocalVarDecl(vFresh), Seq(), translatedCond ==> (currentPermission(translatedRecv, translatedLocation) > noPerm)), error.dueTo(reasons.InsufficientPermission(fieldAccess))))++
            (Assume(Forall(translateLocalVarDecl(vFresh), Seq(), translatedCond ==> (wildcard < currentPermission(translatedRecv, translatedLocation)))))
          } else {
            Nil
          }

        //assumptions for locations that gain permission
        val condTrueLocations = (condInv ==> (
          (if (!usingOldState) {
            (  currentPermission(qpMask,obj.l,translatedLocation) === curPerm - permInv )
          } else {
            currentPermission(qpMask,obj.l,translatedLocation) === curPerm
          } )
          ) )

        //assumption for locations that don't gain permission
        val condFalseLocations = (condInv.not ==> (currentPermission(qpMask,obj.l,translatedLocation) === curPerm))

        //assumption for locations that are definitely independent of any of the locations part of the QP (i.e. different
        //field)

        val independentLocations = Assume(Forall(Seq(obj,field), Trigger(currentPermission(obj.l,field.l))++
          Trigger(currentPermission(qpMask,obj.l,field.l)),(field.l !== translatedLocation) ==>
          (currentPermission(obj.l,field.l) === currentPermission(qpMask,obj.l,field.l))) )


        val ts = Seq(Trigger(curPerm),Trigger(currentPermission(qpMask,obj.l,translatedLocation)),Trigger(invFunApp))

        val v2 = LocalVarDecl(Identifier("v2"),translatedLocal.typ)
        val is_injective = Forall( translatedLocal++v2,Seq(),(  (translatedLocal.l !== v2.l) &&  translatedCond && translatedCond.replace(translatedLocal.l, v2.l) ) ==> (translatedRecv !== translatedRecv.replace(translatedLocal.l, v2.l)))
        val injectiveAssertion = Assert(is_injective,error.dueTo(reasons.ReceiverNotInjective(fieldAccess)))

        val res1 = Havoc(qpMask) ++
          stmts ++
          wildcardAssms ++
          permPositive ++
          CommentBlock("check if receiver " + recv.toString() + " is injective",injectiveAssertion) ++
          enoughPerm ++
          CommentBlock("assumptions for inverse of receiver " + recv.toString(), Assume(invAssm1)++Assume(invAssm2)) ++
          Assume(Forall(obj,ts, condTrueLocations&&condFalseLocations )) ++
          independentLocations ++
          (mask := qpMask)

        env.undefine(vFresh.localVar)

        res1
      //Predicate access
      case predAccPred@sil.PredicateAccessPredicate(PredicateAccess(args, predname), perms) =>
        // alpha renaming, to avoid clashes in context, use vFresh instead of v
        var isWildcard = false
        val vFresh = env.makeUniquelyNamed(v); env.define(vFresh.localVar);
        def renaming[E <: sil.Exp] = (e:E) => Expressions.renameVariables(e, v.localVar, vFresh.localVar)

        val (renamingCond,renamingPerms) = (renaming(cond),renaming(perms))

        val translatedLocal = translateLocalVarDecl(vFresh)
        val translatedCond = translateExp(renamingCond)
        val translatedArgs = args.map(translateExp)

        val (translatedPerms, stmts, wildcard) = {
          if (perms.isInstanceOf[WildcardPerm]) {
            isWildcard = true
            val w = LocalVar(Identifier("wildcard"), Real)
            (w, LocalVarWhereDecl(w.name, w > RealLit(0)) :: Havoc(w) :: Nil, w)
          } else {
            (translateExp(renamingPerms), Nil, null)
          }
        }

        //create local variables from arguments of the predicate
        val predicate = program.findPredicate(predname)
        val formalVars = predicate.formalArgs //sil.LocalVarDecl
        val renamedVars = formalVars.map(env.makeUniquelyNamed)
        renamedVars.foreach(x => env.define(x.localVar))
        val locVars = renamedVars.map(x => LocalVarDecl(Identifier(x.name), typeModule.translateType(x.typ)))
        val formalArgsExpr = renamedVars.map(x => sil.LocalVar(x.name)(x.typ))
        val locExpArgs2 = formalArgsExpr.map(translateExp)

        //define inverse function
        qpId = qpId + 1
        val invFun = Func(Identifier(inverseFunName+qpId), locVars , typeModule.translateType(vFresh.typ))
        inverseFuncs += invFun

        val funApp = FuncApp(invFun.name, translatedArgs, invFun.typ)

        val locExpArgs = locVars.map(_.l)
        val invFunApp = FuncApp(invFun.name, locExpArgs, invFun.typ)

        //replace all arguments:
        val condInv = translatedCond.replace(translatedLocal.l, invFunApp)

        val argsInv = translatedArgs.map(x => x.replace(translatedLocal.l, invFunApp))

        val permInv = translatedPerms.replace(translatedLocal.l, invFunApp)

        val curPerm = currentPermission(predAccPred.loc)
        val translatedLocation = translateLocation(predAccPred.loc)


        //define inverse functions
        val tr1 =
          if (translatedArgs.map(x =>  x.contains(translatedLocal)).reduce(_ && _)) {
            Seq(Trigger(translateLocation(predAccPred.loc)))
          } else {
            Seq()
          }
        val invAssm1 = Forall(translatedLocal, tr1, translatedCond ==> (funApp === translatedLocal.l))

        //for each argument, define a inverse function
        val eqExpr = (argsInv zip locVars.map(_.l)).map(x => x._1 === x._2)


        val tr2 = Seq(Trigger(invFunApp))
        val invAssm2 = eqExpr.map(expr => Forall(locVars, tr2, condInv ==> expr))


        val permPositive = Assert(Forall(locVars, Seq(), condInv ==> permissionPositive(permInv)),
          error.dueTo(reasons.NegativePermission(perms)))

        val permNeeded =
          if(isWildcard) {
            (currentPermission(translateNull, translatedLocation) > RealLit(0))
          } else {
            (currentPermission(translateNull, translatedLocation) >= translatedPerms)
          }
        val enoughPerm = Assert(Forall(translatedLocal, Seq(), translatedCond ==> permNeeded),
          error.dueTo(reasons.InsufficientPermission(predAccPred.loc)))

        val wildcardAssms:Stmt =
          if(isWildcard) {
            Assert(Forall(translatedLocal, Seq(), translatedCond ==> (currentPermission(translateNull, translatedLocation) > noPerm)), error.dueTo(reasons.InsufficientPermission(predAccPred.loc))) ++
              Assume(Forall(translatedLocal, Seq(), translatedCond ==> (wildcard < currentPermission(translateNull, translatedLocation))))
          } else {
            Nil
          }


        //assumptions for locations that gain permission
        val condTrueLocations = translatedCond ==> (
          if (!usingOldState) {
            (currentPermission(qpMask, translateNull, translatedLocation) === curPerm - permInv)
          } else {
            (currentPermission(qpMask, translateNull, translatedLocation) === curPerm)
          } )


        //assumption for locations that don't gain permission
        val condFalseLocations = translatedCond.not ==> ((currentPermission(qpMask,translateNull, translatedLocation)) === curPerm)
        val temp = currentPermission(qpMask, translateNull, translatedLocation)
        val trs =
          if (Seq(curPerm, temp).map(x =>  x.contains(translatedLocal)).reduce(_ && _)) {
            Seq(Trigger(curPerm),Trigger(temp))
          } else {
            Seq()
          }
        //final assumption statement
        val permissionsMap = Assume(Forall(translatedLocal,trs, condTrueLocations&&condFalseLocations ))



        //assumption for locations that are definitely independent of any of the locations part of the QP (i.e. different fields)
        val obj = LocalVarDecl(Identifier("o"), refType)
        val field = LocalVarDecl(Identifier("f"), fieldType)
        val fieldVar = LocalVar(Identifier("f"), fieldType)
        val independentLocations = Assume(Forall(Seq(obj,field), Seq(Trigger(currentPermission(obj.l, field.l)), Trigger(currentPermission(qpMask, obj.l, field.l))),
          ((obj.l !== translateNull) ||  isPredicateField(fieldVar).not || (getPredicateId(fieldVar) !== IntLit(getPredicateId(predname)) ))  ==>
            (currentPermission(obj.l,field.l) === currentPermission(qpMask,obj.l,field.l))))


        //assert injectivity of inverse function:
        //define new variable
        val v2 = env.makeUniquelyNamed(v); env.define(v2.localVar)
        //var translatedLocal2 = LocalVarDecl(Identifier(v2.name), translatedLocal.typ);
        val translatedLocal2 = LocalVarDecl(Identifier(translatedLocal.name.name), translatedLocal.typ) //new varible

        val injectiveCond = (translatedLocal.l.!==(translatedLocal2.l)) && translatedCond && translatedCond.replace(translatedLocal.l, translatedLocal2.l);

        val translatedArgs2= translatedArgs.map(x => x.replace(translatedLocal.l, translatedLocal2.l))

        val ineqs = (translatedArgs zip translatedArgs2).map(x => x._1 !== x._2)
        val ineqExpr = ineqs.reduce((expr1, expr2) => (expr1) || (expr2))
        val injectiveAssertion = Assert(Forall((translatedLocal ++ translatedLocal2), Seq(),injectiveCond ==> ineqExpr), error.dueTo(reasons.ReceiverNotInjective(predAccPred.loc)))

        val gl = new PredicateAccess(formalArgsExpr, predname) (predicate.pos, predicate.info)
        val general_location = translateLocation(gl)
        val invFunApp2 = FuncApp(invFun.name, locExpArgs2, invFun.typ)
        val condInv2 = translatedCond.replace(translatedLocal.l, invFunApp2)

        val tr = Seq(Trigger(general_location))
        val mappedVars = formalArgsExpr.map(x => env.get(x))
        val vars = mappedVars.map(x => LocalVarDecl(x.name, x.typ))
        val independentPredicate = Assume(Forall(vars, tr, (condInv2.not) ==> (currentPermission(qpMask,translateNull, general_location) === currentPermission(translateNull, general_location))))



        val res1 = Havoc(qpMask) ++
          stmts ++
          wildcardAssms ++
          permPositive ++
          CommentBlock("check if receiver " + predAccPred.toString() + " is injective",injectiveAssertion) ++
          enoughPerm ++
          CommentBlock("assumptions for inverse of receiver " + predAccPred.toString(), Assume(invAssm1)++ invAssm2.map(Assume)) ++
          permissionsMap ++
          independentPredicate ++
          independentLocations ++
          (mask := qpMask)

        env.undefine(vFresh.localVar)
        env.undefine(v2.localVar)
        renamedVars.foreach(x => env.undefine(x.localVar))

        res1
      //combination and
      case and@sil.And(e0, e1) =>
        evaluateExhale(v, cond, e0, error) ++
          evaluateExhale(v, cond, e1, error)
      //combination: implies
      case implies@sil.Implies(e0, e1) =>
        //TODO e0 must be pure
        val newCond = sil.And(cond, e0)(implies.pos, implies.info)
        evaluateExhale(v, newCond, e0, error) ++ Nil
      //combination: or
      case or@sil.Or(e0, e1) =>
        //TODO e0 must be pure
        val newCond = sil.And(cond, sil.Not(e0)(e0.pos, e0.info))(or.pos, or.info)
        evaluateExhale(v, newCond, e0, error) ++ Nil
      case _ =>
        if (expr.isPure) {
          val forall = sil.Forall(v, Seq(), sil.Implies(cond, expr)(cond.pos, cond.info))(expr.pos, expr.info)
          Assert(translateExp(forall), error.dueTo(reasons.AssertionFalse(expr))) ++ Nil
        } else {
          Nil
        }
    }
    res
  }

  /*
* Gaurav (03.04.15): this basically is a simplified exhale so some code is duplicated,
* I haven't yet found a nice way of avoiding the code duplication
*/
  override def transferRemove(e:TransferableEntity, cond:Exp): Stmt = {
    val permVar = LocalVar(Identifier("perm"), permType)
    val curPerm = currentPermission(e.rcv,e.loc)
    curPerm := permSub(curPerm,e.transferAmount)
  }

  override def transferValid(e:TransferableEntity):Seq[(Stmt,Exp)] = {
    Nil
  }

  override def inhaleExp(e: sil.Exp): Stmt = {
    inhaleAux(e, Assume)
  }

  /*
   * same as the original inhale except that it abstracts over the way assumptions are expressed in the
   * Boogie program
   * Note: right now (05.04.15) inhale AND transferAdd both use this function
   */
  private def inhaleAux(e: sil.Exp, assmsToStmt: Exp => Stmt):Stmt = {
    e match {
      case sil.AccessPredicate(loc, prm) =>
        val perm = PermissionSplitter.normalizePerm(prm)
        val curPerm = currentPermission(loc)
        val permVar = LocalVar(Identifier("perm"), permType)
        val (permVal, stmts): (Exp, Stmt) =
          if (perm.isInstanceOf[WildcardPerm]) {
            val w = LocalVar(Identifier("wildcard"), Real)
            (w, LocalVarWhereDecl(w.name, w > RealLit(0)) :: Havoc(w) :: Nil)
          } else {
            (translatePerm(perm), Nil)
          }
        stmts ++
          (permVar := permVal) ++
          assmsToStmt(permissionPositive(permVar, Some(perm), true)) ++
          assmsToStmt(permissionPositive(permVar, Some(perm), false) ==> checkNonNullReceiver(loc)) ++
          (if (!usingOldState) curPerm := permAdd(curPerm, permVar) else Nil)
      case w@sil.MagicWand(left,right) =>
        val wandRep = wandModule.getWandRepresentation(w)
        val curPerm = currentPermission(translateNull, wandRep)
        (if (!usingOldState) curPerm := permAdd(curPerm, fullPerm) else Nil)

      //Quantified Permission Expression
      case qp@sil.utility.QuantifiedPermissions.QuantifiedPermission(v, cond, expr) =>
        val res = {
          if (qp.isPure) {
            Nil
          } else {
            evaluateInhale(v, cond, expr)++Nil
          }
        }
        res
      case _ => Nil

    }
  }


  def evaluateInhale(v: sil.LocalVarDecl, cond:sil.Exp, expr:sil.Exp): Stmt = {
    val res = expr match {
      case qp@sil.utility.QuantifiedPermissions.QuantifiedPermission(v, cond, expr)  =>
        //TODO: nested quantifier
        Nil
      //Field Access
      case sil.FieldAccessPredicate(fieldAccess@sil.FieldAccess(recv, f), perms) =>
        // alpha renaming, to avoid clashes in context, use vFresh instead of v
        val vFresh = env.makeUniquelyNamed(v); env.define(vFresh.localVar);
        def renaming[E <: sil.Exp] = (e:E) => Expressions.renameVariables(e, v.localVar, vFresh.localVar)

        val (renamingCond, renamingRecv, renamingPerms, renamingFieldAccess) = (renaming(cond), renaming(recv), renaming(perms), renaming(fieldAccess))
        val (translatedCond, translatedRecv) = (translateExp(renamingCond), translateExp(renamingRecv))

        val translatedLocal = translateLocalVarDecl(vFresh)

        val (translatedPerms, stmts) = {
          if (perms.isInstanceOf[WildcardPerm]) {
            val w = LocalVar(Identifier("wildcard"), Real)
            (w, LocalVarWhereDecl(w.name, w > RealLit(0)) :: Havoc(w) :: Nil)
          } else {
            (translateExp(renamingPerms), Nil)
          }
        }
     //   val sil.utility.QuantifiedPermissions.QPForall(_,_,_,_,renamedPerms,_,_) = renamedQP

        val translatedLocation = translateLocation(Expressions.instantiateVariables(fieldAccess, v.localVar,  vFresh.localVar))

        val obj = LocalVarDecl(Identifier("o"), refType)
        val field = LocalVarDecl(Identifier("f"), fieldType)


        val curPerm:Exp = currentPermission(obj.l,translatedLocation)
        val invFun = addInverseFunction(vFresh.typ)
        val invFunApp = FuncApp(invFun.name, Seq(obj.l), invFun.typ )


        val (condInv, rcvInv, permInv) = (translatedCond.replace(env.get(vFresh.localVar), invFunApp),translatedRecv.replace(env.get(vFresh.localVar), invFunApp),translatedPerms.replace(env.get(vFresh.localVar), invFunApp) )

        val tr1 =
          if(translatedRecv.isInstanceOf[LocalVar]) {
            Seq()
          } else {
            Seq(Trigger(translatedRecv))
          }
        val invAssm1 = (Forall(Seq(translatedLocal), tr1, translatedCond ==> (FuncApp(invFun.name, Seq(translatedRecv), invFun.typ) === translatedLocal.l )))
        val invAssm2 = Forall(Seq(obj), Seq(Trigger(FuncApp(invFun.name, Seq(obj.l), invFun.typ))), condInv ==> (rcvInv === obj.l) )

        val nonNullAssumptions =
          Assume(Forall(Seq(translateLocalVarDecl(vFresh)),Seq(),(translatedCond && permissionPositive(translatedPerms, Some(renamingPerms), false)) ==>
            (translatedRecv !== translateNull) ))

        val permPositive = Assume(Forall(translateLocalVarDecl(vFresh), Seq(), translatedCond ==> permissionPositive(translatedPerms,None,true)))


        //assumptions for locations that gain permission
        val condTrueLocations = (condInv ==> (
          (if (!usingOldState) {
            (  currentPermission(qpMask,obj.l,translatedLocation) === curPerm + permInv )
          } else {
            currentPermission(qpMask,obj.l,translatedLocation) === curPerm
          } )
          ) )

        //assumption for locations that don't gain permission
        val condFalseLocations = (condInv.not ==> (currentPermission(qpMask,obj.l,translatedLocation) === curPerm))

        //assumption for locations that are definitely independent of any of the locations part of the QP (i.e. different
        //field)

        val independentLocations = Assume(Forall(Seq(obj,field), Trigger(currentPermission(obj.l,field.l))++
          Trigger(currentPermission(qpMask,obj.l,field.l)),(field.l !== translatedLocation) ==>
          (currentPermission(obj.l,field.l) === currentPermission(qpMask,obj.l,field.l))) )

        val ts = Seq(Trigger(curPerm),Trigger(currentPermission(qpMask,obj.l,translatedLocation)),Trigger(invFunApp))



        val v2 = LocalVarDecl(Identifier("v2"),translatedLocal.typ)
        val injectiveAssumption = Assume(Forall( translatedLocal++v2,Seq(),(  (translatedLocal.l !== v2.l) &&  translatedCond && translatedCond.replace(translatedLocal.l, v2.l) ) ==> (translatedRecv !== translatedRecv.replace(translatedLocal.l, v2.l))))


        val res1 = Havoc(qpMask) ++
          stmts ++
          Assume(invAssm1) ++
          Assume(invAssm2) ++
          nonNullAssumptions ++
          permPositive ++
          injectiveAssumption ++
          Assume(Forall(obj,ts, condTrueLocations&&condFalseLocations )) ++
          independentLocations ++
          (mask := qpMask)

        env.undefine(vFresh.localVar)

        res1
      //Predicate access
      case predAccPred@sil.PredicateAccessPredicate(PredicateAccess(args, predname), perms) =>
        // alpha renaming, to avoid clashes in context, use vFresh instead of v
        val vFresh = env.makeUniquelyNamed(v); env.define(vFresh.localVar);
        def renaming[E <: sil.Exp] = (e:E) => Expressions.renameVariables(e, v.localVar, vFresh.localVar)

        val (renamingCond,renamingPerms) = (renaming(cond),renaming(perms))

        val translatedLocal = translateLocalVarDecl(vFresh)
        val translatedCond = translateExp(renamingCond)
        val translatedArgs = args.map(translateExp)  //TODO: renaming as well? no?

        val (translatedPerms, stmts) = {
          if (perms.isInstanceOf[WildcardPerm]) {
            val w = LocalVar(Identifier("wildcard"), Real)
            (w, LocalVarWhereDecl(w.name, w > RealLit(0)) :: Havoc(w) :: Nil)
          } else {
            (translateExp(renamingPerms), Nil)
          }
        }
        //create local variables from arguments of the predicate
        val predicate = program.findPredicate(predname)
        val formalVars = predicate.formalArgs //sil.LocalVarDecl
        val renamedVars = formalVars.map(env.makeUniquelyNamed)

        renamedVars.foreach(x => env.define(x.localVar))
        val formalArgsExpr = renamedVars.map(x => sil.LocalVar(x.name)(x.typ))
        val locVars = renamedVars.map(x => LocalVarDecl(Identifier(x.name), typeModule.translateType(x.typ)))


        //define inverse function
        qpId = qpId + 1
        val invFun = Func(Identifier(inverseFunName+qpId), locVars , typeModule.translateType(vFresh.typ))
        inverseFuncs += invFun

        val funApp = FuncApp(invFun.name, translatedArgs, invFun.typ)

        val locExpArgs = locVars.map(_.l)
        val locExpArgs2 = formalArgsExpr.map(translateExp)

        val invFunApp = FuncApp(invFun.name, locExpArgs, invFun.typ)

        //replace all arguments:
        val condInv = translatedCond.replace(translatedLocal.l, invFunApp)

        val argsInv = translatedArgs.map(x => x.replace(translatedLocal.l, invFunApp))

        val permInv = translatedPerms.replace(translatedLocal.l, invFunApp)

        //define inverse functions
        val tr1 =
          if (translatedArgs.map(x =>  x.contains(translatedLocal)).reduce(_ && _)) {
            Seq(Trigger(translateLocation(predAccPred.loc)))
          } else {
            Seq()
          }
        val invAssm1 = Forall(translatedLocal, tr1, translatedCond ==> (funApp === translatedLocal.l))

        //for each argument, define a inverse function
        val eqExpr = (argsInv zip locVars.map(_.l)).map(x => x._1 === x._2)


        val tr2 = Seq(Trigger(invFunApp))
        val invAssm2 = eqExpr.map(expr => Forall(locVars, tr2, condInv ==> expr))

        //assumptions for locations that gain permission
        val curPerm = currentPermission(predAccPred.loc)
        val translatedLocation = translateLocation(predAccPred.loc)
        val condTrueLocations = translatedCond ==> (
          if (!usingOldState) {
            (currentPermission(qpMask, translateNull, translatedLocation) === curPerm + permInv)
          } else {
            (currentPermission(qpMask, translateNull, translatedLocation) === curPerm)
          } )



        //assumption for locations that don't gain permission
        val condFalseLocations = translatedCond.not ==> ((currentPermission(qpMask,translateNull, translatedLocation)) === curPerm)
        val temp = currentPermission(qpMask, translateNull, translatedLocation)
        val trs =
          if (Seq(curPerm, temp).map(x =>  x.contains(translatedLocal)).reduce(_ && _)) {
            Seq(Trigger(curPerm),Trigger(temp))
          } else {
            Seq()
          }
        //final assumption statement

        val permissionsMap = Assume(Forall(translatedLocal,trs, condTrueLocations ))


        //assumption for locations that are definitely independent of any of the locations part of the QP (i.e. different fields)
        val obj = LocalVarDecl(Identifier("o"), refType)
        val field = LocalVarDecl(Identifier("f"), fieldType)
        val fieldVar = LocalVar(Identifier("f"), fieldType)
        val independentLocations = Assume(Forall(Seq(obj,field), Seq(Trigger(currentPermission(obj.l, field.l)), Trigger(currentPermission(qpMask, obj.l, field.l))),
          ((obj.l !== translateNull) ||  isPredicateField(fieldVar).not || (getPredicateId(fieldVar) !== IntLit(getPredicateId(predname)) ))  ==>
            (currentPermission(obj.l,field.l) === currentPermission(qpMask,obj.l,field.l))))

        val gl = new PredicateAccess(formalArgsExpr, predname) (predicate.pos, predicate.info)
        val general_location = translateLocation(gl)
        val invFunApp2 = FuncApp(invFun.name, locExpArgs2, invFun.typ)
        val condInv2 = translatedCond.replace(translatedLocal.l, invFunApp2)

        val tr = Seq(Trigger(general_location))
        val mappedVars = formalArgsExpr.map(x => env.get(x))
        val vars = mappedVars.map(x => LocalVarDecl(x.name, x.typ))
        val independentPredicate = Assume(Forall(vars, tr, (condInv2.not) ==> (currentPermission(qpMask,translateNull, general_location) === currentPermission(translateNull, general_location))))


        //assume injectivity of inverse function:
        //define new variable

        val v2 = env.makeUniquelyNamed(v); env.define(v2.localVar)
        val translatedLocal2 = LocalVarDecl(Identifier(translatedLocal.name.name), translatedLocal.typ) //new varible

        val injectiveCond = (translatedLocal.l.!==(translatedLocal2.l)) && translatedCond && translatedCond.replace(translatedLocal.l, translatedLocal2.l);

        val translatedArgs2= translatedArgs.map(x => x.replace(translatedLocal.l, translatedLocal2.l))

        val ineqs = (translatedArgs zip translatedArgs2).map(x => x._1 !== x._2)
        val ineqExpr = ineqs.reduce((expr1, expr2) => (expr1) || (expr2))
        val injectiveAssumption = Assume(Forall((translatedLocal ++ translatedLocal2), Seq(),injectiveCond ==> ineqExpr))

        val res1 = Havoc(qpMask) ++
          stmts ++
          Assume(invAssm1) ++
          invAssm2.map(Assume) ++
          injectiveAssumption ++
          permissionsMap ++
          independentLocations ++
          independentPredicate ++
          (mask := qpMask)

        env.undefine(vFresh.localVar)
        env.undefine(v2.localVar)
        renamedVars.foreach(x => env.undefine(x.localVar))

        res1
      //combination &&
      case and@sil.And(e0, e1) =>
        evaluateInhale(v, cond, e0) ++ evaluateInhale(v, cond, e1)
      //combination: implies
      case implies@sil.Implies(e0, e1) =>
        //e0 must be pure
        val newCond = sil.And(cond, e0)(implies.pos, implies.info)
        evaluateInhale(v, newCond, e0) ++ Nil
      //combination: or
      case or@sil.Or(e0, e1) =>
        //e0 must be pure
        val newCond = sil.And(cond, sil.Not(e0)(e0.pos, e0.info))(or.pos, or.info)
        evaluateInhale(v, newCond, e0) ++ Nil
      case _ =>
        if (expr.isPure) {
          val forall = sil.Forall(v, Seq(), sil.Implies(cond, expr)(cond.pos, cond.info))(expr.pos, expr.info)
          Assume(translateExp(forall)) ++ Nil
        } else {
          Nil
        }
    }
    res
  }



  //renamed Localvariable and Condition
  def getMapping(v: sil.LocalVarDecl, cond:sil.Exp, expr:sil.Exp): Seq[Exp] = {
    val res = expr match {
      case qp@sil.utility.QuantifiedPermissions.QuantifiedPermission(v, cond, expr)  =>
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
    (if (!usingOldState) curPerm := permAdd(curPerm, e.transferAmount) else Nil)
  }

  override def tempInitMask(rcv: Exp, loc:Exp):(Seq[Exp], Stmt) = {
    val curPerm = currentPermission(tempMask,rcv,loc)
    val setMaskStmt = (tempMask := zeroMask) ++ (curPerm := fullPerm)
    (tempMask, setMaskStmt)
  }


  def currentPermission(loc: sil.LocationAccess): MapSelect = {
    loc match {
      case sil.FieldAccess(rcv, field) =>
        currentPermission(translateExp(rcv), translateLocation(loc))
      case sil.PredicateAccess(_, _) =>
        currentPermission(translateNull, translateLocation(loc))
    }
  }

  def currentPermission(rcv: Exp, location: Exp): MapSelect = {
    currentPermission(maskExp, rcv, location)
  }
  def currentPermission(mask: Exp, rcv: Exp, location: Exp): MapSelect = {
    MapSelect(mask, Seq(rcv, location))
  }

  override def permissionLookup(la: sil.LocationAccess) : Exp = {
    currentPermission(la)
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
      case sil.CurrentPerm(loc) =>
        currentPermission(loc)
      case sil.FractionalPerm(left, right) =>
        BinExp(translateExp(left), Div, translateExp(right))
      case sil.PermAdd(a, b) =>
        permAdd(translatePerm(a), translatePerm(b))
      case sil.PermSub(a, b) =>
        permSub(translatePerm(a), translatePerm(b))
      case sil.PermMul(a, b) =>
        BinExp(translatePerm(a), Mul, translatePerm(b))
      case sil.PermDiv(a,b) =>
        permDiv(translatePerm(a), translateExp(b))
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

  private def isAbstractRead(exp: sil.Exp) = {
    exp match {
      case sil.LocalVar(name) => currentAbstractReads.contains(name)
      case _ => false
    }
  }

  override def enterConstrainingBlock(cb: sil.Constraining): Stmt = {
    val vars = cb.vars map translateLocalVar
    currentAbstractReads ++= (cb.vars map (_.name))
    Nil
  }

  override def leaveConstrainingBlock(cb: sil.Constraining): Stmt = {
    val vars = cb.vars map (_.name)
    currentAbstractReads --= vars
    Nil
  }


  override def freshReads(vars: Seq[viper.silver.ast.LocalVar]): Stmt = {
    val bvs = vars map translateLocalVar
    Havoc(bvs) ++
      (bvs map (v => Assume((v > RealLit(0)) && (v < RealLit(1)))))
  }

  override def simpleHandleStmt(s: sil.Stmt): Stmt = {
    s match {
      case n@sil.NewStmt(target,fields) =>
        for (field <- fields) yield {
          Assign(currentPermission(sil.FieldAccess(target, field)()), fullPerm)
        }
      case assign@sil.FieldAssign(fa, rhs) =>
        Assert(permGe(currentPermission(fa), fullPerm), errors.AssignmentFailed(assign).dueTo(reasons.InsufficientPermission(fa)))
      case _ => Nil
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
  private def permLe(a: Exp, b: Exp): Exp = {
    // simple optimization that helps in many cases
    if (a == fullPerm) permEq(a, b)
    else a <= b
  }
  private def permGt(a: Exp, b: Exp): Exp = {
    // simple optimization that helps in many cases
    if (b == fullPerm) permEq(a, b)
    else permLt(b, a)
  }
  private def permGe(a: Exp, b: Exp): Exp = {
    permLe(b, a)
  }

  override val numberOfPhases = 3
  override def isInPhase(e: sil.Exp, phaseId: Int): Boolean = {
    e match {
      case sil.AccessPredicate(loc, perm) => true // do something in all phases
      case _ => phaseId == 0
    }
  }

  override def phaseDescription(phase: Int): String = {
    phase match {
      case 0 => "pure assertions and fixed permissions"
      case 1 => "abstract read permissions (and scaled abstract read permissions)"
      case 2 => "all remaining permissions (containing read permissions, but in a negative context)"
    }
  }

  // AS: this is a trick to avoid well-definedness checks for the outermost heap dereference in an AccessPredicate node (since it describes the location to which permission is provided).
  // The trick is somewhat fragile, in that it relies on the ordering of the calls to this method (but generally works out because of the recursive traversal of the assertion).
  private var allowLocationAccessWithoutPerm = false
  override def simplePartialCheckDefinedness(e: sil.Exp, error: PartialVerificationError, makeChecks: Boolean): Stmt = {
    if(makeChecks) (
      e match {
        case sil.CurrentPerm(loc) =>
          allowLocationAccessWithoutPerm = true
          Nil
        case sil.AccessPredicate(loc, perm) =>
          allowLocationAccessWithoutPerm = true
          Nil
        case sil.PredicateAccess(loc, perm) =>
          allowLocationAccessWithoutPerm = true
          Nil
        case fa@sil.LocationAccess(_) =>
          if (allowLocationAccessWithoutPerm) {
            allowLocationAccessWithoutPerm = false
            Nil
          } else {
            Assert(hasDirectPerm(fa), error.dueTo(reasons.InsufficientPermission(fa)))
          }
        case sil.PermDiv(a, b) =>
          Assert(translateExp(b) !== IntLit(0), error.dueTo(reasons.DivisionByZero(b)))
        case _ => Nil
      }
      ) else Nil
  }

  /*For QP \forall x:T :: c(x) ==> acc(e(x),p(x)) this case class describes an instantiation of the QP where
   * cond = c(expr), recv = e(expr) and perm = p(expr) and expr is of type T and may be dependent on the variable given by v. */
  case class QPComponents(v:LocalVarDecl,cond: Exp, recv: Exp, perm: Exp)
  /**
   *
   * @param qp the quantified permission (i.e. should match object sil.QuantifiedPermissionSupporter.ForallRefPerm
   * @param vFresh the variable which should replace the current bound variable of the qp
   * @return returns a boogie representation of the qp (QPComponents) and a renamed sil node of the  inputted qp
   */
  private def setupQPComponents(qp: sil.Forall, vFresh: sil.LocalVarDecl, permExpr: Option[Exp] = None): (QPComponents,sil.Forall) = {
    qp match {
      case sil.utility.QuantifiedPermissions.QPForall(v, cond, recv, _, perms, forall, fieldAccess) =>
        def renaming[E <: sil.Exp] = (e: E) => Expressions.renameVariables(e, v.localVar, vFresh.localVar)

        val (renamingCond, renamingRecv, renamingPerms, renamingFieldAccess) = (renaming(cond), renaming(recv), renaming(perms), renaming(fieldAccess))
        val (translatedCond, translatedRecv) = (translateExp(renamingCond), translateExp(renamingRecv))

        val translatedPerms = permExpr match {
          case None => translateExp(renamingPerms)
          case Some(p) => p
        }
            //          sil.Forall(Seq(vFresh), Seq(), sil.Implies(renamingCond,sil.FieldAccessPredicate(renamingFieldAccess, renamingPerms)(fieldAccess.pos,fieldAccess.info))(NoPosition,NoInfo))(qp.pos,qp.info))
            //note: we lose the position and info data of the implies
            (QPComponents(translateLocalVarDecl(vFresh), translatedCond, translatedRecv, translatedPerms), renaming(qp))

          case _ => sys.error("setupQPComponents only handles quantified permissions")
        }
    }

  /*For QP \forall x:T :: c(x) ==> acc(pred(e1(x), ....., en(x),p(x)) this case class describes an instantiation of the QP where
 * cond = c(expr), e1(x), ...en(x) = args and perm = p(expr) and expr is of type T and may be dependent on the variable given by v. */
  case class QPPComponents(v:LocalVarDecl, cond: Exp, predname:String, args:Seq[Exp], perm:Exp, predAcc:PredicateAccessPredicate)
  /**
    *
    * @param qp the quantified permission (i.e. should match object sil.QuantifiedPermissionSupporter.ForallRefPerm
    * @param vFresh the variable which should replace the current bound variable of the qp
    * @return returns a boogie representation of the qp (QPComponents) and a renamed sil node of the  inputted qp
    */
  private def setupQPPComponents(qp: sil.Forall, vFresh: sil.LocalVarDecl, permExpr: Option[Exp] = None): (QPPComponents,sil.Forall) = {
    qp match {
      case sil.utility.QuantifiedPermissions.QPPForall(v,cond,args,predname,perms,forall,predAccess) =>
        def renaming[E <: sil.Exp] = (e:E) => Expressions.renameVariables(e, v.localVar, vFresh.localVar)

        val (renamingCond,renamingPerms) = (renaming(cond),renaming(perms))

        val renamingArgs = args.map(translateExp)

        val translatedCond = translateExp(renamingCond)

        val translatedPerms = permExpr match {
          case None => translateExp(renamingPerms)
          case Some(p) => p
        }

        (QPPComponents(translateLocalVarDecl(vFresh),translatedCond, predname, renamingArgs, translatedPerms, predAccess), renaming(qp))
      case _ => sys.error("setupQPPComponents only handles quantified predicate permissions")
    }
  }

  //checks if the receiver expression in qpcomp is injective
  def isInjective(qpcomp: QPComponents):Exp = {
    val QPComponents(v, cond, recv, perm) = qpcomp

    val vFresh = LocalVarDecl(Identifier("v2"),v.typ)
    Forall( v++vFresh,Seq(),
      (  (v.l !== vFresh.l) &&  cond && cond.replace(v.l, vFresh.l) ) ==> (recv !== recv.replace(v.l, vFresh.l)) )
  }

  /*makes assumptions about the inverse of the receiver expression in qpStandard
   *qpcompStandard represents the qp \forall v::T. c(v) ==> acc(e(v).f,p(v))
   *qpcompInverse represents the qp \forall vInv::T. c(inv(v)) ==> e(inv(v)).f, p(inv(v))
   */
  def inverseAssumptions(invFun: Func, qpcompStandard: QPComponents, qpcompInverse: QPComponents):(Exp, Exp) = {
    val QPComponents(v, cond, recv, perm) = qpcompStandard
    val QPComponents(vInv, condInv, recvInv, permInv) = qpcompInverse

    val tr1 =
      if(recv.isInstanceOf[LocalVar]) {
        Seq()
      } else {
        Seq(Trigger(recv))
      }
    val assm1 = (Forall(Seq(v), tr1, cond ==> (FuncApp(invFun.name, Seq(recv), invFun.typ) === v.l )))

    val assm2 = Forall(Seq(vInv), Seq(Trigger(FuncApp(invFun.name, Seq(vInv.l), invFun.typ))), condInv ==> (recvInv === vInv.l) )

    (assm1,assm2)
  }



  /* records a fresh function which represents the inverse function of a receiver expression in a qp, if the qp is
   given by \forall x:: T. c(x) ==> acc(e(x).f,p(x)) then "outputType" is T. The returned function takes values of type
   Ref and returns value of type T.
   */

  private def addInverseFunction(outputType: sil.Type):Func = {
    qpId = qpId+1;
    val res = Func(Identifier(inverseFunName+qpId), LocalVarDecl(Identifier("recv"), refType), typeModule.translateType(outputType))
    inverseFuncs += res
    res
  }

  private def addInversePredicateFunction(outputType: sil.Type):Func = {
    qpId = qpId+1;
    val res = Func(Identifier(inverseFunName+qpId), LocalVarDecl(Identifier("recv"), refType), typeModule.translateType(outputType))
    inverseFuncs += res
    res
  }

  def splitter = PermissionSplitter
  object PermissionSplitter {

    def isStrictlyPositivePerm(e: sil.Exp): Exp = {
      require(e isSubtype sil.Perm, s"found ${e.typ} ($e), but required Perm")
      val backup = permissionPositive(translatePerm(e), Some(e))
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
        case sil.PermAdd(left, right) =>
          (isStrictlyPositivePerm(left) && isStrictlyPositivePerm(right)) || backup
        case sil.PermSub(left, right) => backup
        case sil.PermMul(a, b) =>
          (isStrictlyPositivePerm(a) && isStrictlyPositivePerm(b)) || (isNegativePerm(a) && isNegativePerm(b))
        case sil.PermDiv(a, b) =>
          isStrictlyPositivePerm(a) // note: b should be ruled out from being non-positive
        case sil.IntPermMul(a, b) =>
          val n = translateExp(a)
          ((n > IntLit(0)) && isStrictlyPositivePerm(b)) || ((n < IntLit(0)) && isNegativePerm(b))
        case sil.CondExp(cond, thn, els) =>
          CondExp(translateExp(cond), isStrictlyPositivePerm(thn), isStrictlyPositivePerm(els))
        case _ => backup
      }
    }

    def conservativeIsPositivePerm(e: sil.Exp): Boolean = {
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
        case sil.PermAdd(left, right) =>
          conservativeIsPositivePerm(left) && conservativeIsPositivePerm(right)
        case sil.PermSub(left, right) => false // conservative
        case sil.PermMul(a, b) =>
          (conservativeIsPositivePerm(a) && conservativeIsPositivePerm(b)) || (conservativeIsNegativePerm(a) && conservativeIsNegativePerm(b))
        case sil.PermDiv(a, b) =>
          conservativeIsPositivePerm(a) // note: b should be guaranteed ruled out from being non-positive
        case sil.IntPermMul(sil.IntLit(n), b) =>
          n > 0 && conservativeIsPositivePerm(b) || n < 0 && conservativeIsNegativePerm(b)
        case sil.IntPermMul(a, b) => false // conservative
        case sil.CondExp(cond, thn, els) => // conservative
          conservativeIsPositivePerm(thn) && conservativeIsPositivePerm(els)
        case _ => false // conservative?
      }
    }

    def conservativeIsNegativePerm(e: sil.Exp): Boolean = {
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
        case sil.PermAdd(left, right) =>
          conservativeIsNegativePerm(left) && conservativeIsNegativePerm(right)
        case sil.PermSub(left, right) => false // conservative
        case sil.PermMul(a, b) =>
          (conservativeIsPositivePerm(a) && conservativeIsNegativePerm(b)) || (conservativeIsNegativePerm(a) && conservativeIsPositivePerm(b))
        case sil.PermDiv(a, b) =>
          conservativeIsNegativePerm(a) // note: b should be guaranteed ruled out from being non-positive
        case sil.IntPermMul(sil.IntLit(n), b) =>
          n > 0 && conservativeIsNegativePerm(b) || n < 0 && conservativeIsPositivePerm(b)
        case sil.IntPermMul(a, b) => false // conservative
        case sil.CondExp(cond, thn, els) => // conservative
          conservativeIsNegativePerm(thn) && conservativeIsNegativePerm(els)
        case _ => false // conservative?
      }
    }


    def isNegativePerm(e: sil.Exp): Exp = {
      require(e isSubtype sil.Perm)
      val backup = UnExp(Not,permissionPositive(translatePerm(e), Some(e), true))
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
        case sil.PermAdd(left, right) =>
          (isNegativePerm(left) && isNegativePerm(right)) || backup
        case sil.PermSub(left, right) => backup
        case sil.PermMul(a, b) =>
          (isStrictlyPositivePerm(a) && isNegativePerm(b)) || (isNegativePerm(a) && isStrictlyPositivePerm(b))
        case sil.PermDiv(a, b) =>
          isNegativePerm(a) // note: b should be guaranteed ruled out from being non-positive
        case sil.IntPermMul(a, b) =>
          val n = translateExp(a)
          ((n > IntLit(0)) && isNegativePerm(b)) || ((n < IntLit(0)) && isStrictlyPositivePerm(b))
        case sil.CondExp(cond, thn, els) =>
          CondExp(translateExp(cond), isNegativePerm(thn), isNegativePerm(els))
        case _ => backup
      }
    }

    // NOTE: this is conservative and so always returns false for local variables
    def isFixedPerm(e: sil.Exp): Boolean = {
      require(e isSubtype sil.Perm)
      e match {
        case sil.NoPerm() => true
        case sil.FullPerm() => true
        case sil.WildcardPerm() => false
        case sil.EpsilonPerm() =>  sys.error("epsilon permissions are not supported by this permission module")
        //case sil.CurrentPerm(loc) => true
        case sil.FractionalPerm(left, right) => true
        case sil.PermAdd(left, right) =>
          isFixedPerm(left) && isFixedPerm(right)
        case sil.PermSub(left, right) =>
          isFixedPerm(left) && isFixedPerm(right)
        case sil.PermMul(left, right) =>
          isFixedPerm(left) && isFixedPerm(right)
        case sil.PermDiv(left, right) =>
          isFixedPerm(left)
        case sil.IntPermMul(a, b) =>
          isFixedPerm(b)
        case sil.CondExp(cond, thn, els) =>
          isFixedPerm(thn) && isFixedPerm(els) // note: this doesn't take account of condition (due to being a syntactic check) - in theory could be overly-restrictive
        //case _: sil.FuncLikeApp => true
        case _ => false // conservative for local variables, field dereferences etc.
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
        val e1 = e0.transform()(_ => true, {
          case sil.PermSub(left, right) => done = false
            sil.PermAdd(left, sil.IntPermMul(sil.IntLit(-1)(), right)())()
        })

        // move permission multiplications all the way to the inside
        val e2 = e1.transform()(_ => true, {
          case sil.PermMul(sil.PermAdd(a, b), c) => done = false
            sil.PermAdd(sil.PermMul(a, c)(), sil.PermMul(b, c)())()
          case sil.PermMul(a, sil.PermAdd(b, c)) => done = false
            sil.PermAdd(sil.PermMul(a, b)(), sil.PermMul(a, c)())()
        })

        // move permission divisions all the way to the inside
        val e2b = e2.transform()(_ => true, {
          case sil.PermDiv(sil.PermAdd(a, b), n) => done = false
            sil.PermAdd(sil.PermDiv(a,n)(),sil.PermDiv(b,n)())()
        })

        // move integer permission multiplications all the way to the inside
        val e3 = e2b.transform()(_ => true, {
          case x@sil.IntPermMul(a, sil.PermAdd(b, c)) => done = false
            sil.PermAdd(sil.IntPermMul(a, b)(), sil.IntPermMul(a, c)())()
          case sil.IntPermMul(a, sil.PermMul(b, c)) => done = false
            sil.PermMul(b, sil.IntPermMul(a, c)())()
        })

        // group integer permission multiplications
        val e4 = e3.transform()(_ => true, {
          case sil.IntPermMul(a, sil.IntPermMul(b, c)) => done = false
            sil.IntPermMul(sil.Mul(a, b)(), c)()
        })

        // move non-fixed part of permission multiplication to right-hand side
        val e5 = e4.transform()(_ => true, {
          case sil.PermMul(a, b) if isFixedPerm(b) && !isFixedPerm(a) => done = false
            sil.PermMul(b, a)()
        })

        // collapse a*wildcard to just wildcard, if b is known to be positive
        val e5a = e5.transform()(_ => true, {
          case sil.PermMul(a, wp@sil.WildcardPerm()) if conservativeIsPositivePerm(a) => done = false
            sil.WildcardPerm()(wp.pos,wp.info)
        })

        // propagate multiplication and division into conditional expressions
        val e6 = e5a.transform()(_ => true, {
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
        })

        // propagate addition into conditional expressions
        val e7 = e6.transform()(_ => true, {
          case sil.PermAdd(a, sil.CondExp(cond, thn, els)) => done = false
            sil.CondExp(cond, sil.PermAdd(a,thn)(), sil.PermMul(a,els)())()
          case sil.PermAdd(sil.CondExp(cond, thn, els),a) => done = false
            sil.CondExp(cond, sil.PermAdd(thn,a)(), sil.PermMul(els,a)())()
        })


        (done, e7)
      }
    }

    // decide which phase this permission amount belongs to, and the conditional under which the decision is made
    // Phase 1: isFixedPerm(p)
    // Phase 2: positive occurrences of abstract read permissions (and multiples thereof)
    // Phase 3: everything else (e.g. 1-k where k is abstract read permission)

    // e should be normalised first by calling normalizePerm(e)
    def splitPerm(e: sil.Exp): Seq[(Int, Exp, sil.Exp)] ={
      def addCond(in: Seq[(Int, Exp, sil.Exp)], c: Exp): Seq[(Int, Exp, sil.Exp)] = {
        in map (x => (x._1, BinExp(c, And, x._2), x._3))
      }
      def divideBy(in: Seq[(Int, Exp, sil.Exp)], c: sil.Exp): Seq[(Int, Exp, sil.Exp)] = {
        in map (x => (x._1, x._2, sil.PermDiv(x._3,c)()))
      }
      val zero = IntLit(0)
      e match {
        case sil.PermSub(sil.FullPerm(), p: sil.LocalVar) if isAbstractRead(p) =>
          (3, TrueLit(), e)
        case p if isFixedPerm(p) =>
          (1, TrueLit(), p)
        case p:sil.LocalVar =>
          //assert(isAbstractRead(p)) // doesn't match conservative checking of isFixedPerm
          if (isAbstractRead(p)) {
            (2, TrueLit(), p)
          } else {
            (3, TrueLit(), p)
          }
        case sil.IntPermMul(n, p: sil.LocalVar) if isAbstractRead(p) =>
          val cond = translateExp(n) > zero
          Seq((2, cond, e), (3, UnExp(Not, cond), e))
        case sil.PermMul(left, right: sil.LocalVar) if isAbstractRead(right) =>
          val cond = isStrictlyPositivePerm(left)
          Seq((2, cond, e), (3, UnExp(Not, cond), e))
        case sil.PermMul(left, sil.IntPermMul(n, p: sil.LocalVar)) if isAbstractRead(p) =>
          val cond = isStrictlyPositivePerm(left) && (translateExp(n) > zero)
          Seq((2, cond, e), (3, UnExp(Not, cond), e))
        case sil.PermAdd(left, right) =>
          val splitted = splitPerm(left) ++ splitPerm(right)
          val cond = isStrictlyPositivePerm(left) && isStrictlyPositivePerm(right)
          addCond(splitted, cond) ++ Seq((3, UnExp(Not, cond), e))
        case sil.CondExp(cond,thn,els) =>
          val thncases = splitPerm(thn)
          val elscases = splitPerm(els)
          val transcond = translateExp(cond)
          addCond(thncases,transcond) ++ addCond(elscases,UnExp(Not,transcond))
        case sil.PermDiv(a,n) =>
          val cases = splitPerm(a)
          divideBy(cases,n)
        case _ =>
          (3, TrueLit(), e)
      }
    }
  }
}
