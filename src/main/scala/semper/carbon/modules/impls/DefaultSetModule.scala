package semper.carbon.modules.impls

import semper.carbon.modules.SetModule
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.Verifier
import semper.carbon.boogie.Implicits._

/**
 * The default implementation of [[semper.carbon.modules.SetModule]].
 *
 * @author Stefan Heule
 */
class DefaultSetModule(val verifier: Verifier) extends SetModule {

  import verifier._
  import typeModule._
  import expModule._

  /**
   * Have sets been used so far (to determine if we need to include
   * the set axiomatization in the prelude.
   */
  private var used = false

  def name = "Set module"
  implicit val namespace = verifier.freshNamespace("set")

  override def preamble = {
    if (used) {
      LiteralDecl(SetAxiomatization.value)
    } else {
      Nil
    }
  }

  override def translateSetExp(e: sil.Exp): Exp = {
    def t(e: sil.Exp) = translateExp(e)
    val isMultiset = e.typ match {
      case _: sil.MultisetType => true
      case _ => false
    }
    used = true
    val typ = translateType(e.typ)
    e match {
      case sil.EmptySet(elemTyp) =>
        FuncApp(Identifier("Set#Empty"), Nil, typ)
      case sil.ExplicitSet(elems) =>
        def buildSet(es: Seq[sil.Exp]): Exp = {
          es match {
            case Nil => sys.error("did not expect empty sequence")
            case a :: Nil =>
              FuncApp(Identifier("Set#Singleton"), t(a), typ)
            case a :: as =>
              FuncApp(Identifier("Set#UnionOne"), List(buildSet(as), t(a)), typ)
          }
        }
        buildSet(elems)
      case sil.EmptyMultiset(elemTyp) =>
        FuncApp(Identifier("MultiSet#Empty"), Nil, typ)
      case sil.ExplicitMultiset(elems) =>
        def buildSet(es: Seq[sil.Exp]): Exp = {
          es match {
            case Nil => sys.error("did not expect empty sequence")
            case a :: Nil =>
              FuncApp(Identifier("MultiSet#Singleton"), t(a), typ)
            case a :: as =>
              FuncApp(Identifier("MultiSet#UnionOne"), List(buildSet(as), t(a)), typ)
          }
        }
        buildSet(elems)
      case sil.AnySetUnion(left, right) =>
        if (isMultiset) FuncApp(Identifier("MultiSet#Union"), List(t(left), t(right)), typ)
        else FuncApp(Identifier("Set#Union"), List(t(left), t(right)), typ)
      case sil.AnySetIntersection(left, right) =>
        if (isMultiset) FuncApp(Identifier("MultiSet#Intersection"), List(t(left), t(right)), typ)
        else FuncApp(Identifier("Set#Intersection"), List(t(left), t(right)), typ)
      case sil.AnySetSubset(left, right) =>
        if (left.isInstanceOf[sil.MultisetType]) FuncApp(Identifier("MultiSet#Subset"), List(t(left), t(right)), Bool)
        else FuncApp(Identifier("Set#Subset"), List(t(left), t(right)), Bool)
      case sil.AnySetMinus(left, right) =>
        if (isMultiset) FuncApp(Identifier("MultiSet#Difference"), List(t(left), t(right)), typ)
        else FuncApp(Identifier("Set#Difference"), List(t(left), t(right)), typ)
      case sil.AnySetContains(left, right) =>
        if (left.isInstanceOf[sil.MultisetType])
          FuncApp(Identifier("MultiSet#Subset"), List(FuncApp(Identifier("MultiSet#Singleton"), List(t(left)), typ), t(right)), Bool)
        else
          FuncApp(Identifier("Set#Subset"), List(FuncApp(Identifier("Set#Singleton"), List(t(left)), typ), t(right)), Bool)
      case sil.AnySetCardinality(set) =>
        if (set.isInstanceOf[sil.MultisetType]) FuncApp(Identifier("MultiSet#Card"), t(set), Bool)
        else FuncApp(Identifier("Set#Card"), t(set), Bool)
      case sil.EqCmp(left, right) =>
        if (left.isInstanceOf[sil.MultisetType]) FuncApp(Identifier("MultiSet#Equal"), List(t(left), t(right)), Bool)
        else FuncApp(Identifier("Set#Equal"), List(t(left), t(right)), Bool)
      case sil.NeCmp(left, right) =>
        if (left.isInstanceOf[sil.MultisetType]) UnExp(Not, FuncApp(Identifier("MultiSet#Equal"), List(t(left), t(right)), Bool))
        else UnExp(Not, FuncApp(Identifier("Set#Equal"), List(t(left), t(right)), Bool))
      case _ => sys.error("not a set expression")
    }
  }

  override def translateSetType(setType: sil.SetType): Type = {
    used = true
    NamedType("Set", translateType(setType.elementType))
  }

  override def translateMultisetType(setType: sil.MultisetType): Type = {
    used = true
    NamedType("MultiSet", translateType(setType.elementType))
  }
}
