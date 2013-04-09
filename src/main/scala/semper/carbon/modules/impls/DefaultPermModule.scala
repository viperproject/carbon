package semper.carbon.modules.impls

import semper.carbon.modules._
import components.StateComponent
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.Verifier
import semper.carbon.boogie.Implicits._

/**
 * The default implementation of a [[semper.carbon.modules.PermModule]].
 *
 * @author Stefan Heule
 */
class DefaultPermModule(val verifier: Verifier) extends PermModule with StateComponent {

  import verifier._
  import heapModule._

  def name = "Permission module"

  override def initialize() {
    verifier.stateModule.register(this)
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

  override def preamble = {
    TypeDecl(permCompType) ::
      TypeAlias(permType, MapType(permCompType, Real, Nil)) ::
      ConstDecl(permFracCompName, permCompType, unique = true) ::
      ConstDecl(permEpsCompName, permCompType, unique = true) ::
      TypeAlias(maskType, MapType(Seq(refType, fieldType), permType, fieldType.freeTypeVars)) ::
      GlobalVarDecl(maskName, maskType) ::
      Nil
  }

  def permType = NamedType(permTypeName)

  def stateContributions: Seq[LocalVarDecl] = Seq(LocalVarDecl(maskName, maskType))
  def currentStateContributions: Seq[Exp] = Seq(mask)
  def initState: Stmt = {
    Statements.EmptyStmt
  }

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
}
