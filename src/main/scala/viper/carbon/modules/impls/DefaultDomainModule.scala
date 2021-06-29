// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.modules.impls

import viper.carbon.modules.{DomainModule, StatelessComponent}
import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.verifier.{Environment, Verifier}
import viper.carbon.boogie.Implicits._
import viper.silver.ast.NamedDomainAxiom

/**
 * The default implementation of [[viper.carbon.modules.DomainModule]].
 */
class DefaultDomainModule(val verifier: Verifier) extends DomainModule with StatelessComponent {

  import verifier._
  import typeModule._
  import expModule._
  import mainModule._

  def name = "Domain module"

  implicit val namespace = verifier.freshNamespace("domain")

  // name for output identifier (to try to avoid clashes - should be improved for robustness (see issue #19)
  def outputName(domain: sil.Domain) : String = domain.name + "DomainType"

  override def translateDomain(domain: sil.Domain): Seq[Decl] = {
    val fs = domain.functions flatMap translateDomainFunction
    val as = domain.axioms flatMap translateDomainAxiom
    val ts = CommentedDecl(s"The type for domain ${domain.name}",
      TypeDecl(NamedType(this.outputName(domain) , domain.typVars map (tv => TypeVar(tv.name)))), size = 1)
    CommentedDecl(s"Translation of domain ${domain.name}", ts ++ fs ++ as, nLines = 2)
  }

  private def translateDomainFunction(f: sil.DomainFunc): Seq[Decl] = {
    env = Environment(verifier, f)
    val t = translateType(f.typ)
    val res = if (f.unique) {
      val func = ConstDecl(Identifier(f.name), t, unique = true)
      MaybeCommentedDecl(s"Translation of domain unique function ${f.name}", func, size = 1)
    } else {
      val args = f.formalArgs map (x => LocalVarDecl(Identifier(if (x.isInstanceOf[sil.LocalVarDecl]) x.asInstanceOf[sil.LocalVarDecl].name else env.uniqueName(f.name + "_param")), translateType(x.typ)))
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
    val res = MaybeCommentedDecl(if (axiom.isInstanceOf[NamedDomainAxiom])
      (s"Translation of domain axiom ${axiom.asInstanceOf[NamedDomainAxiom].name}")
    else
      (s"Translation of anonymous domain axiom")
    , Axiom(translateExp(axiom.exp)), size = 1)
    //mainModule.undefineLocalVars(axiom)
    env = null
    res
  }

  override def translateDomainFuncApp(fa: sil.DomainFuncApp): Exp = {
    val funct = verifier.program.findDomainFunction(fa.funcname)
    if (funct.unique) {
      Const(Identifier(funct.name))
    } else {
      val res = FuncApp(Identifier(funct.name), fa.args map translateExp, translateType(fa.typ))
      res.showReturnType = true
      res
    }
  }

  override def translateDomainTyp(typ: sil.DomainType): Type = {
    val domain = verifier.program.findDomain(typ.domainName)
    val typArgs = domain.typVars map (tv => typ.typVarsMap.getOrElse(tv, tv))
    NamedType(this.outputName(domain), typArgs map translateType)
  }

}
