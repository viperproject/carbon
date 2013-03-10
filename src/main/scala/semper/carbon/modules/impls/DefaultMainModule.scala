package semper.carbon.modules.impls

import semper.carbon.modules._
import semper.sil.{ast => sil}
import semper.carbon.boogie.{Procedure, Decl, Program}
import semper.carbon.boogie.Implicits._

/**
 * The default implementation of a [[semper.carbon.modules.MainModule]].
 *
 * @author Stefan Heule
 */
class DefaultMainModule(val verifier: Verifier) extends MainModule with AllModule {
  def name = "Main module"

  override def translate(p: sil.Program): Program = {
    p match {
      case sil.Program(name, domains, fields, functions, predicates, methods) =>
        // TODO translate domains, fields, functions and predicates

        //
        Program(Nil)
    }
  }

  def translateMethod(m: sil.Method): Seq[Decl] = {
    m match {
      case sil.Method(name, formalArgs, formalReturns, pres, posts, locals, body) =>
        // TODO: handle pre/post
        // TODO: handle arguments
        // TODO: handle locals
        val tBody = translateStmt(body)
        Procedure(name, Nil, Nil, tBody)
    }
  }

  def translateFunction(f: sil.Function): Seq[Decl] = ???
  def translateDomain(d: sil.Domain): Seq[Decl] = ???
  def translateFieldDecl(f: sil.Field): Seq[Decl] = ???
  def translatePredicate(p: sil.Predicate): Seq[Decl] = ???
}
