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
  private val mask = GlobalVar(maskName, maskType)

  override def preamble = {
    TypeDecl(permCompType) ::
      TypeAlias(permType, MapType(permCompType, Real, Nil)) ::
      ConstDecl(permFracCompName, permCompType, unique = true) ::
      ConstDecl(permEpsCompName, permCompType, unique = true) ::
      TypeAlias(maskType, MapType(Seq(refType, fieldType), permType, fieldType.freeTypeVars)) ::
      Nil
  }

  def permType = NamedType(permTypeName)

  def stateContributions: Seq[LocalVarDecl] = Seq(LocalVarDecl(maskName, maskType))
  def currentStateContributions: Seq[Exp] = Seq(mask)
  def initState: Stmt = {
    Statements.EmptyStmt
  }
}
