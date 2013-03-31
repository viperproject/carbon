package semper.carbon.modules.impls

import semper.carbon.modules.DomainModule
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.Verifier
import semper.carbon.boogie.Implicits._

/**
 * The default implementation of [[semper.carbon.modules.DomainModule]].
 *
 * @author Stefan Heule
 */
class DefaultDomainModule(val verifier: Verifier) extends DomainModule {

  import verifier._
  import typeModule._
  import expModule._

  def name = "Domain module"

  implicit val namespace = verifier.freshNamespace("domain")

  override def translateDomain(domain: sil.Domain): Seq[Decl] = {
    val fs = domain.functions flatMap translateDomainFunction
    val as = domain.axioms flatMap translateDomainAxiom
    val ts = CommentedDecl(s"The type for domain ${domain.name}",
      TypeDecl(NamedType(domain.name, domain.typVars map (tv => TypeVar(tv.name)))), size = 1)
    CommentedDecl(s"Translation of domain ${domain.name}", ts ++ fs ++ as, nLines = 2)
  }

  private def translateDomainFunction(f: sil.DomainFunc): Seq[Decl] = {
    val args = f.formalArgs map (x => LocalVarDecl(Identifier(x.name), translateType(x.typ)))
    val func = Func(Identifier(f.name), args, translateType(f.typ))
    CommentedDecl(s"Translation of domain function ${f.name}", func, size = 1)
  }

  private def translateDomainAxiom(axiom: sil.DomainAxiom): Seq[Decl] = {
    CommentedDecl(s"Translation of domain axiom ${axiom.name}", Axiom(translateExp(axiom.exp)), size = 1)
  }

  override def translateDomainFuncApp(fa: sil.DomainFuncApp): Exp = {
    FuncApp(Identifier(fa.func.name), fa.args map translateExp, translateType(fa.typ))
  }

  override def translateDomainTyp(typ: sil.DomainType): Type = {
    val domain = typ.domain
    val typArgs = domain.typVars map (tv => typ.typVarsMap.getOrElse(tv, tv))
    NamedType(domain.name, typArgs map translateType)
  }

}
