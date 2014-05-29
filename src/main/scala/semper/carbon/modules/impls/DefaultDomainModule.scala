package semper.carbon.modules.impls

import semper.carbon.modules.DomainModule
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.{Environment, Verifier}
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
  import mainModule._

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
    env = Environment(verifier, f)
    val t = translateType(f.typ)
    val res = if (f.unique) {
      val func = ConstDecl(Identifier(f.name), t, unique = true)
      MaybeCommentedDecl(s"Translation of domain unique function ${f.name}", func, size = 1)
    } else {
      val args = f.formalArgs map (x => LocalVarDecl(Identifier(x.name), translateType(x.typ)))
      val func = Func(Identifier(f.name), args, t)
      MaybeCommentedDecl(s"Translation of domain function ${f.name}", func, size = 1)
    }
    env = null
    res
  }

  private def translateDomainAxiom(axiom: sil.DomainAxiom): Seq[Decl] = {
    env = Environment(verifier, axiom)
    //(AS): I believe this is not needed, as locals are introduced in the translation
    //mainModule.defineLocalVars(axiom)
    val res = MaybeCommentedDecl(s"Translation of domain axiom ${axiom.name}", Axiom(translateExp(axiom.exp)), size = 1)
    //mainModule.undefineLocalVars(axiom)
    env = null
    res
  }

  override def translateDomainFuncApp(fa: sil.DomainFuncApp): Exp = {
    if (fa.funct.unique) {
      Const(Identifier(fa.funct.name))
    } else {
      FuncApp(Identifier(fa.funct.name), fa.args map translateExp, translateType(fa.typ))
    }
  }

  override def translateDomainTyp(typ: sil.DomainType): Type = {
    val domain = typ.domain
    val typArgs = domain.typVars map (tv => typ.typVarsMap.getOrElse(tv, tv))
    NamedType(domain.name, typArgs map translateType)
  }

}
