package semper.carbon.modules.impls

import semper.carbon.modules._
import semper.carbon.modules.components._
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.Verifier
import semper.carbon.boogie.Implicits._
import semper.sil.verifier._
import semper.carbon.boogie.NamedType
import semper.carbon.boogie.MapSelect
import semper.carbon.boogie.LocalVarWhereDecl
import semper.carbon.boogie.Trigger
import semper.carbon.boogie.TypeDecl
import semper.sil.verifier.PartialVerificationError
import semper.carbon.boogie.LocalVarDecl
import semper.carbon.boogie.Assume
import semper.carbon.boogie.RealLit
import semper.carbon.boogie.GlobalVar
import semper.carbon.boogie.GlobalVarDecl
import semper.carbon.boogie.Axiom
import semper.carbon.boogie.BinExp
import semper.carbon.boogie.MapType
import semper.carbon.boogie.Assert
import semper.carbon.boogie.ConstDecl
import semper.carbon.boogie.Const
import semper.carbon.boogie.LocalVar
import semper.sil.ast.WildcardPerm
import semper.carbon.boogie.Forall
import semper.carbon.boogie.Assign
import semper.carbon.boogie.Func
import semper.carbon.boogie.TypeAlias
import semper.carbon.boogie.FuncApp

/**
 * The default implementation of a [[semper.carbon.modules.PermModule]].
 *
 * @author Stefan Heule
 */
class DefaultPermModule(val verifier: Verifier)
  extends PermModule
  with StateComponent
  with InhaleComponent
  with ExhaleComponent
  with SimpleStmtComponent
  with DefinednessComponent {

  import verifier._
  import heapModule._
  import expModule._
  import stateModule._

  def name = "Permission module"

  override def initialize() {
    stateModule.register(this)
    exhaleModule.register(this)
    inhaleModule.register(this)
    stmtModule.register(this)
    expModule.register(this)
  }

  implicit val namespace = verifier.freshNamespace("perm")
  private val axiomNamespace = verifier.freshNamespace("perm.axiom")
  private val permTypeName = "Perm"
  private val permCompTypeName = "PermComponent"
  private val permCompType = NamedType(permCompTypeName)
  private val permFracCompName = Identifier("$frac")
  private val permEpsCompName = Identifier("$eps")
  private val permFracComp = Const(permFracCompName)
  private val permEpsComp = Const(permEpsCompName)
  private val maskTypeName = "MaskType"
  private val maskType = NamedType(maskTypeName)
  private val pmaskTypeName = "PMaskType"
  override val pmaskType = NamedType(pmaskTypeName)
  private val maskName = Identifier("Mask")
  private var mask: Exp = GlobalVar(maskName, maskType)
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
  private val permConstructName = Identifier("Perm")
  private val goodMaskName = Identifier("GoodMask")
  private val hasDirectPermName = Identifier("HasDirectPerm")
  private val predicateMaskFieldName = Identifier("PredicateMaskField")

  private def fracComp(perm: Exp) = MapSelect(perm, permFracComp)
  private def epsComp(perm: Exp) = MapSelect(perm, permEpsComp)

  override def preamble = {
    val obj = LocalVarDecl(Identifier("o")(axiomNamespace), refType)
    val field = LocalVarDecl(Identifier("f")(axiomNamespace), fieldType)
    val permInZeroMask = MapSelect(zeroMask, Seq(obj.l, field.l))
    val permInZeroPMask = MapSelect(zeroPMask, Seq(obj.l, field.l))
    // permission type (with permission components)
    TypeDecl(permCompType) ::
      TypeAlias(permType, MapType(permCompType, Real, Nil)) ::
      ConstDecl(permFracCompName, permCompType, unique = true) ::
      ConstDecl(permEpsCompName, permCompType, unique = true) ::
      // mask and mask type
      TypeAlias(maskType, MapType(Seq(refType, fieldType), permType, fieldType.freeTypeVars)) ::
      GlobalVarDecl(maskName, maskType) ::
      // zero mask
      ConstDecl(zeroMaskName, maskType) ::
      Axiom(Forall(
        Seq(obj, field),
        Trigger(permInZeroMask),
        (fracComp(permInZeroMask) === RealLit(0)) && (epsComp(permInZeroMask) === RealLit(0)))) ::
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
        Seq(LocalVarDecl(Identifier("f"), fieldType)),
        fieldTypeOf(pmaskType)) ::
      // permission amount constants
      ConstDecl(noPermName, permType) ::
      Axiom((fracComp(noPerm) === RealLit(0)) && (epsComp(noPerm) === RealLit(0))) ::
      ConstDecl(fullPermName, permType) ::
      Axiom((fracComp(fullPerm) === RealLit(1)) && (epsComp(fullPerm) === RealLit(0))) ::
      // permission addition
      Func(permAddName, Seq(LocalVarDecl(Identifier("a"), permType), LocalVarDecl(Identifier("b"), permType)), permType) :: {
      val a = LocalVarDecl(Identifier("a"), permType)
      val b = LocalVarDecl(Identifier("b"), permType)
      val comp = LocalVarDecl(Identifier("permComp"), permCompType)
      Axiom(Forall(Seq(a, b, comp),
        Trigger(MapSelect(permAdd(a.l, b.l), comp.l)),
        MapSelect(permAdd(a.l, b.l), comp.l) === (MapSelect(a.l, comp.l) + MapSelect(b.l, comp.l))))
    } ::
      // permission subtraction
      Func(permSubName, Seq(LocalVarDecl(Identifier("a"), permType), LocalVarDecl(Identifier("b"), permType)), permType) :: {
      val a = LocalVarDecl(Identifier("a"), permType)
      val b = LocalVarDecl(Identifier("b"), permType)
      val comp = LocalVarDecl(Identifier("permComp"), permCompType)
      Axiom(Forall(Seq(a, b, comp),
        Trigger(MapSelect(permSub(a.l, b.l), comp.l)),
        MapSelect(permSub(a.l, b.l), comp.l) === (MapSelect(a.l, comp.l) - MapSelect(b.l, comp.l))))
    } ::
      // permission constructor
      Func(permConstructName, Seq(LocalVarDecl(Identifier("a"), Real), LocalVarDecl(Identifier("b"), Real)), permType) :: {
      val a = LocalVarDecl(Identifier("a"), Real)
      val b = LocalVarDecl(Identifier("b"), Real)
      val f = FuncApp(permConstructName, Seq(a.l, b.l), permType)
      Axiom(Forall(Seq(a, b),
        Trigger(fracComp(f)),
        fracComp(f) === a.l)) ::
        Axiom(Forall(Seq(a, b),
          Trigger(epsComp(f)),
          epsComp(f) === b.l)) ::
        Nil
    } ++
      // good mask
      Func(goodMaskName, LocalVarDecl(maskName, maskType), Bool) ++
      Axiom(Forall(stateModule.stateContributions,
        Trigger(Seq(staticGoodState)),
        staticGoodState ==> staticGoodMask)) ++ {
      val perm = currentPermission(obj.l, field.l)
      Axiom(Forall(stateContributions ++ obj ++ field,
        Trigger(Seq(staticGoodMask, perm)),
        staticGoodMask ==>
          // permissions are non-negative
          (fracComp(perm) >= RealLit(0)) &&
          ((fracComp(perm) === RealLit(0)) ==> (epsComp(perm) >= RealLit(0))) &&
          // permissions for fields are smaller than 1
          (fracComp(perm) <= RealLit(1)) &&
          ((epsComp(perm) > RealLit(0)) ==> (fracComp(perm) < RealLit(1)))
      ))
    } ++ {
      val obj = LocalVarDecl(Identifier("o")(axiomNamespace), refType)
      val field = LocalVarDecl(Identifier("f")(axiomNamespace), fieldType)
      val args = staticMask ++ Seq(obj, field)
      val funcApp = FuncApp(hasDirectPermName, args map (_.l), Bool)
      val permission = currentPermission(staticMask(0).l, obj.l, field.l)
      val permissionPositive = fracComp(permission) > RealLit(0) ||
        ((fracComp(permission) === RealLit(0)) && epsComp(permission) > RealLit(0))
      Func(hasDirectPermName, args, Bool) ++
        Axiom(Forall(
          staticMask ++ Seq(obj, field),
          Trigger(funcApp),
          funcApp <==> permissionPositive
        ))
    }
  }

  def permType = NamedType(permTypeName)

  def stateContributions: Seq[LocalVarDecl] = Seq(LocalVarDecl(maskName, maskType))
  def currentState: Seq[Exp] = Seq(mask)
  def initState: Stmt = {
    (mask := zeroMask)
  }
  def initOldState: Stmt = {
    Assume(Old(mask) === mask)
  }

  override def predicateMaskField(pred: Exp): Exp = {
    FuncApp(predicateMaskFieldName, Seq(pred), pmaskType)
  }

  def staticGoodMask = FuncApp(goodMaskName, LocalVar(maskName, maskType), Bool)

  private def permAdd(a: Exp, b: Exp): Exp = FuncApp(permAddName, Seq(a, b), permType)
  private def permSub(a: Exp, b: Exp): Exp = FuncApp(permSubName, Seq(a, b), permType)

  private def fracPerm(frac: Exp) = mixedPerm(frac, RealLit(0))
  private def epsPerm(eps: Exp) = mixedPerm(RealLit(0), eps)
  private def mixedPerm(frac: Exp, eps: Exp) = FuncApp(permConstructName, Seq(frac, eps), permType)

  override def freshTempState(name: String): Seq[Exp] = {
    Seq(LocalVar(Identifier(s"${name}Mask"), maskType))
  }

  override def restoreState(s: Seq[Exp]) {
    mask = s(0)
  }

  /**
   * Can a location on a given receiver be read?
   */
  private def hasDirectPerm(mask: Exp, obj: Exp, loc: Exp): Exp =
    FuncApp(hasDirectPermName, Seq(mask, obj, loc), Bool)
  private def hasDirectPerm(obj: Exp, loc: Exp): Exp = hasDirectPerm(mask, obj, loc)
  override def hasDirectPerm(la: sil.LocationAccess): Exp =
    hasDirectPerm(translateExp(la.rcv), locationMaskIndex(la))

  private def permissionPositive(permission: Exp) = {
    fracComp(permission) > RealLit(0) ||
      ((fracComp(permission) === RealLit(0)) && epsComp(permission) > RealLit(0))
  }

  override def exhaleExp(e: sil.Exp, error: PartialVerificationError): Stmt = {
    e match {
      case sil.AccessPredicate(loc, perm) =>
        val curPerm = MapSelect(mask, Seq(translateExp(loc.rcv), locationMaskIndex(loc)))
        val permVar = LocalVar(Identifier("perm"), permType)
        val (permVal, wildcard, stmts): (Exp, Exp, Stmt) =
          if (perm.isInstanceOf[WildcardPerm]) {
            val w = LocalVar(Identifier("wildcard"), Real)
            (fracPerm(w), w, LocalVarWhereDecl(w.name, w > RealLit(0)) :: Havoc(w) :: Nil)
          } else {
            (translatePerm(perm), null, Nil)
          }
        stmts ::
          (permVar := permVal) ::
          Assert(permissionPositive(permVar), error.dueTo(reasons.NonPositivePermission(perm))) ::
          Assert(checkNonNullReceiver(loc), error.dueTo(reasons.ReceiverNull(loc))) ::
          (if (perm.isInstanceOf[WildcardPerm]) {
            (Assert(fracComp(curPerm) > RealLit(0), error.dueTo(reasons.InsufficientPermission(loc))) ::
              Assume(wildcard < fracComp(curPerm)) :: Nil): Stmt
          } else if (isAbstractRead(perm)) {
            (Assert(fracComp(curPerm) > RealLit(0), error.dueTo(reasons.InsufficientPermission(loc))) ::
              Assume(fracComp(permVal) < fracComp(curPerm)) :: Nil): Stmt
          } else {
            Assert(permLe(permVal, curPerm), error.dueTo(reasons.InsufficientPermission(loc)))
          }) ::
          (curPerm := permSub(curPerm, permVar)) ::
          Nil
      case _ => Nil
    }
  }

  override def inhaleExp(e: sil.Exp): Stmt = {
    e match {
      case sil.AccessPredicate(loc, perm) =>
        val curPerm = currentPermission(loc)
        val permVar = LocalVar(Identifier("perm"), permType)
        val (permVal, stmts): (Exp, Stmt) =
          if (perm.isInstanceOf[WildcardPerm]) {
            val w = LocalVar(Identifier("wildcard"), Real)
            (fracPerm(w), LocalVarWhereDecl(w.name, w > RealLit(0)) :: Havoc(w) :: Nil)
          } else {
            (translatePerm(perm), Nil)
          }
        stmts ::
          (permVar := permVal) ::
          Assume(permissionPositive(permVar)) ::
          Assume(checkNonNullReceiver(loc)) ::
          (curPerm := permAdd(curPerm, permVar)) ::
          Nil
      case _ => Nil
    }
  }

  def currentPermission(loc: sil.LocationAccess): MapSelect = {
    currentPermission(translateExp(loc.rcv), locationMaskIndex(loc))
  }
  def currentPermission(rcv: Exp, location: Exp): MapSelect = {
    currentPermission(mask, rcv, location)
  }
  def currentPermission(mask: Exp, rcv: Exp, location: Exp): MapSelect = {
    MapSelect(mask, Seq(rcv, location))
  }

  override def currentMask = Seq(mask)
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
        epsPerm(RealLit(1))
      case sil.CurrentPerm(loc) =>
        MapSelect(mask, Seq(translateExp(loc.rcv), locationMaskIndex(loc)))
      case sil.FractionalPerm(left, right) =>
        fracPerm(BinExp(translateExp(left), Div, translateExp(right)))
      case sil.PermAdd(a, b) =>
        permAdd(translatePerm(a), translatePerm(b))
      case sil.PermSub(a, b) =>
        permSub(translatePerm(a), translatePerm(b))
      case sil.PermMul(a, b) =>
        fracPerm(BinExp(fracComp(translatePerm(a)), Mul, fracComp(translatePerm(b))))
      case sil.IntPermMul(a, b) =>
        val i = translateExp(a)
        val p = translatePerm(b)
        val mul = (x: Exp) => BinExp(i, Mul, x)
        mixedPerm(mul(fracComp(p)), mul(epsComp(p)))
      case _: sil.LocalVar | _: sil.FuncLikeApp =>
        translateExp(e)
      case _ => sys.error(s"not a permission expression: $e")
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

  private val currentAbstractReads = collection.mutable.ListBuffer[String]()

  private def isAbstractRead(exp: sil.Exp) = {
    exp match {
      case sil.LocalVar(name) => currentAbstractReads.contains(name)
      case _ => false
    }
  }

  override def enterFreshBlock(fb: sil.FreshReadPerm): Stmt = {
    val vars = fb.vars map translateLocalVar
    currentAbstractReads ++= (fb.vars map (_.name))
    Havoc(fb.vars map translateLocalVar) ++
      (vars map (v => Assume((fracComp(v) > RealLit(0)) && (fracComp(v) < RealLit(0.001)) && (epsComp(v) === RealLit(0)))))
  }

  override def leaveFreshBlock(fb: sil.FreshReadPerm): Stmt = {
    val vars = fb.vars map (_.name)
    currentAbstractReads --= vars
    Nil
  }

  override def simpleHandleStmt(s: sil.Stmt): Stmt = {
    s match {
      case n@sil.NewStmt(lhs) =>
        for (field <- verifier.program.fields) yield {
          Assign(currentPermission(sil.FieldAccess(lhs, field)()), fullPerm)
        }
      case assign@sil.FieldAssign(fa, rhs) =>
        Assert(permGe(currentPermission(fa), fullPerm), errors.AssignmentFailed(assign).dueTo(reasons.InsufficientPermission(fa)))
      case c@sil.MethodCall(method, args, targets) =>
        for ((formalArg, actualArg) <- method.formalArgs zip args) yield {
          formalArg.typ match {
            case sil.Perm =>
              val e = epsComp(translateExp(actualArg)) === RealLit(0)
              Assert(e, errors.PreconditionInCallFalse(c).dueTo(reasons.EpsilonAsParam(actualArg)))
            case _ => Statements.EmptyStmt
          }
        }
      case _ => Nil
    }
  }

  private def permEq(a: Exp, b: Exp): Exp = {
    (fracComp(a) === fracComp(b)) &&
      (epsComp(a) === epsComp(b))
  }
  private def permNe(a: Exp, b: Exp): Exp = {
    (fracComp(a) !== fracComp(b)) ||
      (epsComp(a) !== epsComp(b))
  }
  private def permLt(a: Exp, b: Exp): Exp = {
    (fracComp(a) < fracComp(b)) ||
      ((fracComp(a) === fracComp(b)) && (epsComp(a) < epsComp(b)))
  }
  private def permLe(a: Exp, b: Exp): Exp = {
    permLt(a, b) || permEq(a, b)
  }
  private def permGt(a: Exp, b: Exp): Exp = {
    permLt(b, a)
  }
  private def permGe(a: Exp, b: Exp): Exp = {
    permLe(b, a)
  }

  override val numberOfPhases = 3
  override def phaseOf(e: sil.Exp): Int = {
    e match {
      case sil.AccessPredicate(loc, sil.LocalVar(name)) if currentAbstractReads.contains(name) => 1
      case sil.AccessPredicate(loc, perm) if !containsAbstractRead(perm) => 0
      case sil.AccessPredicate(loc, perm) => 2
      case _ => 0
    }
  }

  override def phaseDescription(phase: Int): String = {
    phase match {
      case 0 => "pure assertions and fixed permissions"
      case 1 => "abstract read permissions on their own"
      case 2 => "all remaining permissions (containing read permissions, but not on their own)"
    }
  }

  /**
   * Returns true if the given permission contains an abstract read permission.
   */
  private def containsAbstractRead(perm: sil.Exp): Boolean = {
    var res = false
    perm visit {
      case l@sil.LocalVar(name) if (currentAbstractReads.contains(name)) =>
        res = true
    }
    res
  }

  private var allowLocationAccessWithoutPerm = false
  override def simplePartialCheckDefinedness(e: sil.Exp, error: PartialVerificationError): Stmt = {
    e match {
      case sil.CurrentPerm(loc) =>
        allowLocationAccessWithoutPerm = true
        Nil
      case sil.AccessPredicate(loc, perm) =>
        allowLocationAccessWithoutPerm = true
        Nil
      case fa@sil.LocationAccess(rcv, field) =>
        if (allowLocationAccessWithoutPerm) {
          allowLocationAccessWithoutPerm = false
          Nil
        } else {
          Assert(hasDirectPerm(fa), error.dueTo(reasons.InsufficientPermission(fa)))
        }
      case pm@sil.PermMul(a, b) =>
        Assert(epsComp(translatePerm(a)) === RealLit(0), error.dueTo(reasons.InvalidPermMultiplication(pm))) ++
          Assert(epsComp(translatePerm(b)) === RealLit(0), error.dueTo(reasons.InvalidPermMultiplication(pm)))
      case _ => Nil
    }
  }

  override def assumptionAboutParameter(typ: sil.Type, variable: LocalVar) = {
    typ match {
      case sil.Perm => Some(epsComp(variable) === RealLit(0))
      case _ => None
    }
  }
}
