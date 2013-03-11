package semper.carbon.modules.impls

import semper.carbon.modules.{TypeModule, AllModule}
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.Verifier

/**
 * The default implementation of a [[semper.carbon.modules.StmtModule]].
 *
 * @author Stefan Heule
 */
class DefaultTypeModule(val verifier: Verifier) extends TypeModule {
  def name = "Type module"
  override def translateType(t: sil.Type): Type = {
    t match {
      case sil.Bool =>
        Bool
      case sil.Int =>
        Int
      case sil.Ref =>
        ???
      case sil.Perm =>
        ???
      case sil.Pred =>
        ???
      case sil.TypeVar(v) =>
        sys.error("Did not expect a type variable here.")
      case sil.DomainType(domain, typVarsMap) =>
        ???
    }
  }
}
