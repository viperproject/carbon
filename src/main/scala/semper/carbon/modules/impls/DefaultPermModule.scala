package semper.carbon.modules.impls

import semper.carbon.modules._
import semper.carbon.modules.components.{InhaleComponent, ExhaleComponent, StateComponent}
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.Verifier
import semper.carbon.boogie.Implicits._
import semper.sil.verifier._
import semper.carbon.boogie.GlobalVarDecl
import semper.carbon.boogie.NamedType
import semper.carbon.boogie.MapSelect
import semper.carbon.boogie.Axiom
import semper.carbon.boogie.TypeDecl
import semper.carbon.boogie.MapType
import semper.carbon.boogie.Assert
import semper.sil.verifier.PartialVerificationError
import semper.carbon.boogie.LocalVarDecl
import semper.carbon.boogie.Assume
import semper.carbon.boogie.ConstDecl
import semper.carbon.boogie.Const
import semper.carbon.boogie.LocalVar
import semper.carbon.boogie.RealLit
import semper.carbon.boogie.Assign
import semper.carbon.boogie.TypeAlias
import semper.carbon.boogie.FuncApp
import semper.carbon.boogie.GlobalVar

/**
 * The default implementation of a [[semper.carbon.modules.PermModule]].
 *
 * @author Stefan Heule
 */
class DefaultPermModule(val verifier: Verifier) extends PermModule with StateComponent with InhaleComponent with ExhaleComponent {

  import verifier._
  import heapModule._
  import expModule._

  def name = "Permission module"

  override def initialize() {
    stateModule.register(this)
    exhaleModule.register(this)
    inhaleModule.register(this)
  }

  implicit val namespace = verifier.freshNamespace("perm")
  private val permTypeName = "Perm"
  private val permCompTypeName = "PermComponent"
  private val permCompType = NamedType(permCompTypeName)
  private val permFracCompName = Identifier("$frac")
  private val permEpsCompName = Identifier("$eps")
  private val permFracComp = Const(permFracCompName)
  private val permEpsComp = Const(permEpsCompName)
  private val maskTypeName = "MaskType"
  private val maskType = NamedType(maskTypeName)
  private val maskName = Identifier("Mask")
  private var mask: Var = GlobalVar(maskName, maskType)
  private val noPermName = Identifier("NoPerm")
  private val noPerm = Const(noPermName)
  private val fullPermName = Identifier("FullPerm")
  private val fullPerm = Const(fullPermName)
  private val permAddName = Identifier("PermAdd")
  private val permSubName = Identifier("PermSub")

  private def fracComp(perm: Exp) = MapSelect(perm, permFracComp)
  private def epsComp(perm: Exp) = MapSelect(perm, permEpsComp)

  override def preamble = {
    // permission type (wieth permission components)
    TypeDecl(permCompType) ::
      TypeAlias(permType, MapType(permCompType, Real, Nil)) ::
      ConstDecl(permFracCompName, permCompType, unique = true) ::
      ConstDecl(permEpsCompName, permCompType, unique = true) ::
      // mask and mask type
      TypeAlias(maskType, MapType(Seq(refType, fieldType), permType, fieldType.freeTypeVars)) ::
      GlobalVarDecl(maskName, maskType) ::
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
      Nil
  }

  def permType = NamedType(permTypeName)

  def stateContributions: Seq[LocalVarDecl] = Seq(LocalVarDecl(maskName, maskType))
  def currentStateContributions: Seq[Exp] = Seq(mask)
  def initState: Stmt = {
    Statements.EmptyStmt
  }

  private def permAdd(a: Exp, b: Exp): Exp = FuncApp(permAddName, Seq(a, b), permType)
  private def permSub(a: Exp, b: Exp): Exp = FuncApp(permSubName, Seq(a, b), permType)

  override type StateSnapshot = (Int, Var)
  private var curTmpStateId = -1

  override def freshTempState: (Stmt, StateSnapshot) = {
    curTmpStateId += 1
    val oldMask = mask
    val tmpHeapName = if (curTmpStateId == 0) "tmpMask" else s"tmpMask$curTmpStateId"
    mask = LocalVar(Identifier(tmpHeapName), maskType)
    val s = Assign(mask, oldMask)
    (s, (curTmpStateId, oldMask))
  }

  override def throwAwayTempState(s: StateSnapshot): Stmt = {
    mask = s._2
    curTmpStateId = s._1 - 1
    Statements.EmptyStmt
  }

  /**
   * An expression stating that the permission is positive.
   */
  private def permissionPositive(permission: Exp) = {
    fracComp(permission) > RealLit(0) ||
      ((fracComp(permission) === RealLit(0)) && epsComp(permission) > RealLit(0))
  }

  override def exhaleExp(e: sil.Exp, error: PartialVerificationError): Stmt = {
    e match {
      case sil.AccessPredicate(loc, perm) =>
        val curPerm = MapSelect(mask, Seq(translateExp(loc.rcv), locationMaskIndex(loc)))
        val permVar = LocalVar(Identifier("perm"), permType)
        (permVar := translatePerm(perm)) ::
          Assert(permissionPositive(permVar), error.dueTo(reasons.NegativeFraction(perm))) ::
          Assert(checkNonNullReceiver(loc), error.dueTo(reasons.ReceiverNull(loc))) ::
          Assert((fracComp(curPerm) >= fracComp(permVar)) && (epsComp(curPerm) >= epsComp(permVar)), error.dueTo(reasons.InsufficientPermissions(loc))) ::
          (curPerm := permAdd(curPerm, permVar)) ::
          Nil
      case _ => Nil
    }
  }

  override def inhaleExp(e: sil.Exp): Stmt = {
    e match {
      case sil.AccessPredicate(loc, perm) =>
        val curPerm = MapSelect(mask, Seq(translateExp(loc.rcv), locationMaskIndex(loc)))
        val permVar = LocalVar(Identifier("perm"), permType)
        (permVar := translatePerm(perm)) ::
          Assume(permissionPositive(permVar)) ::
          Assume(checkNonNullReceiver(loc)) ::
          (curPerm := permAdd(curPerm, permVar)) ::
          Nil
      case _ => Nil
    }
  }

  def translatePerm(e: sil.Exp): Exp = {
    require(e isSubtype sil.Perm)
    e match {
      case sil.NoPerm() =>
        noPerm
      case sil.FullPerm() =>
        fullPerm
      case _ => sys.error("not a permission expression")
    }
  }
}
