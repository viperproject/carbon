/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules.impls

import viper.carbon.modules._
import viper.carbon.modules.components._
import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.boogie.Implicits._
import viper.silver.verifier._
import viper.carbon.boogie.NamedType
import viper.carbon.boogie.MapSelect
import viper.carbon.boogie.LocalVarWhereDecl
import viper.carbon.boogie.Trigger
import viper.carbon.boogie.TypeDecl
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
import viper.silver.ast.WildcardPerm
import viper.carbon.boogie.Forall
import viper.carbon.boogie.Assign
import viper.carbon.boogie.Func
import viper.carbon.boogie.TypeAlias
import viper.carbon.boogie.FuncApp
import viper.carbon.verifier.Verifier

/**
 * The default implementation of a [[viper.carbon.modules.PermModule]].
 */
class NoEpsilonsPermModule(val verifier: Verifier)
  extends PermModule
  with CarbonStateComponent
  with InhaleComponent
  with ExhaleComponent
  with TransferComponent
  with SimpleStmtComponent
  with DefinednessComponent {

  import verifier._
  import heapModule._
  import expModule._
  import stateModule._

  def name = "Permission module"

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
  private var currentMaskName = maskName
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
        (staticGoodMask ==> perm >= RealLit(0)) &&
        // permissions for fields which aren't predicates or wands are smaller than 1
          ((staticGoodMask && heapModule.isPredicateField(field.l).not && heapModule.isWandField(field.l).not) ==> perm <= RealLit(1) )
        ))
    } ++ {
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
      }
  }

  def permType = NamedType(permTypeName)

  def staticStateContributions: Seq[LocalVarDecl] = Seq(LocalVarDecl(maskName, maskType))
  def currentStateContributions: Seq[LocalVarDecl] = Seq(LocalVarDecl(currentMaskName, maskType))
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

  def reset = {
    mask = originalMask
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
    currentMaskName =
      s(0) match {
        case LocalVar(id,typ) =>  id
        case GlobalVar(id,typ) =>  id
        case _ => sys.error("wrong state representation for perm module")
      }
  }
  /**
   * Can a location on a given receiver be read?
   */
  private def hasDirectPerm(mask: Exp, obj: Exp, loc: Exp): Exp =
    FuncApp(hasDirectPermName, Seq(mask, obj, loc), Bool)
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
            Assert(permissionPositive(translatePerm(p), Some(p), true), error.dueTo(reasons.NegativePermission(p))) else Nil: Stmt) ++
            Assert(checkNonNullReceiver(loc), error.dueTo(reasons.ReceiverNull(loc)))
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
      case w@sil.MagicWand(left,right) =>
        val wandRep = wandModule.getWandRepresentation(w)
        val curPerm = currentPermission(translateNull, wandRep)
        Comment("permLe")++ //using RealLit(1.0) instead of FullPerm due to permLe's implementation
        Assert(permLe(RealLit(1.0), curPerm), error.dueTo(reasons.MagicWandChunkNotFound(w))) ++
        (if (!usingOldState) curPerm := permSub(curPerm, RealLit(1.0)) else Nil)
      case _ => Nil
    }
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



/* old version of inhaleExp (05.04.15)
  override def inhaleExp(e: sil.Exp): Stmt = {
    e match {
      case sil.AccessPredicate(loc, prm) => {
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
          Assume(permissionPositive(permVar, Some(perm), true)) ++
          Assume(checkNonNullReceiver(loc)) ++
          (if (!usingOldState) curPerm := permAdd(curPerm, permVar) else Nil)
      }
      case _ => Nil
    }
  }*/

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
          assmsToStmt(checkNonNullReceiver(loc)) ++
          (if (!usingOldState) curPerm := permAdd(curPerm, permVar) else Nil)
      case w@sil.MagicWand(left,right) =>
        val wandRep = wandModule.getWandRepresentation(w)
        val curPerm = currentPermission(translateNull, wandRep)
        (if (!usingOldState) curPerm := permAdd(curPerm, fullPerm) else Nil)
      case _ => Nil
    }
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

  override def currentPermission(loc: sil.LocationAccess): MapSelect = {
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

  def splitter = PermissionSplitter
  object PermissionSplitter {

    def isPositivePerm(e: sil.Exp): Exp = {
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
          (isPositivePerm(left) && isPositivePerm(right)) || backup
        case sil.PermSub(left, right) => backup
        case sil.PermMul(a, b) =>
          (isPositivePerm(a) && isPositivePerm(b)) || (isNegativePerm(a) && isNegativePerm(b))
        case sil.PermDiv(a, b) =>
          isPositivePerm(a) // note: b should be ruled out from being non-positive
        case sil.IntPermMul(a, b) =>
          val n = translateExp(a)
          ((n > IntLit(0)) && isPositivePerm(b)) || ((n < IntLit(0)) && isNegativePerm(b))
        case sil.CondExp(cond, thn, els) =>
          CondExp(translateExp(cond), isPositivePerm(thn), isPositivePerm(els))
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
          (isPositivePerm(a) && isNegativePerm(b)) || (isNegativePerm(a) && isPositivePerm(b))
        case sil.PermDiv(a, b) =>
          isNegativePerm(a) // note: b should be guaranteed ruled out from being non-positive
        case sil.IntPermMul(a, b) =>
          val n = translateExp(a)
          ((n > IntLit(0)) && isNegativePerm(b)) || ((n < IntLit(0)) && isPositivePerm(b))
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
    // (a*wildcard) --> wildcard if isPositivePerm(a)
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
          val cond = isPositivePerm(left)
          Seq((2, cond, e), (3, UnExp(Not, cond), e))
        case sil.PermMul(left, sil.IntPermMul(n, p: sil.LocalVar)) if isAbstractRead(p) =>
          val cond = isPositivePerm(left) && (translateExp(n) > zero)
          Seq((2, cond, e), (3, UnExp(Not, cond), e))
        case sil.PermAdd(left, right) =>
          val splitted = splitPerm(left) ++ splitPerm(right)
          val cond = isPositivePerm(left) && isPositivePerm(right)
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
