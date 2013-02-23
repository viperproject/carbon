package semper.carbon.boogie

import org.kiama.output._
import UnicodeString.lift

/**
 * A pretty printer for the Boogie AST.
 *
 * @author Stefan Heule
 */
object PrettyPrinter extends org.kiama.output.PrettyPrinter with ParenPrettyPrinter {

  override val defaultIndent = 2
  /** Pretty-print any AST node. */
  def pretty(n: Node): String = {
    super.pretty(show(n))
  }

  /** Show any AST node. */
  def show(n: Node): Doc = {
    n match {
      case exp: Exp => toParenDoc(exp)
      case stmt: Stmt => showStmt(stmt)
      case typ: Type => showType(typ)
      case p: Program => showProgram(p)
      case m: Decl => showDecl(m)
    }
  }

  def showType(t: Type) = {
    t match {
      case Int => value("int")
      case Bool => value("bool")
      case Real => value("real")
      case _ => empty
    }
  }

  def showStmt(stmt: Stmt) = {
    empty
  }

  def showProgram(p: Program) = {
    empty
  }

  def showDecl(decl: Decl) = {
    empty
  }

  def showVar(variable: LocalVarDecl) = {
    variable.name <> ":" <+> showType(variable.typ) <>
    (variable.where match {
      case Some(e) => space <> "where" <+> show(e)
      case None => empty
    })
  }

  def showTrigger(t: Trigger) = {
    "{" <+> ssep(t.exps map show, comma <> space) <+> "}"
  }

  // Note: pretty-printing expressions is mostly taken care of by kiama
  override def toParenDoc(e: PrettyExpression): Doc = {
    e match {
      case IntLit(i) => value(i)
      case BoolLit(b) => value(b)
      case RealLit(d) => value(d)
      case Forall(vars, triggers, exp) =>
        parens(("∀" or "forall") <+>
          ssep(vars map showVar, comma <> space) <+>
          ("•" or "::") <+>
          ssep(triggers map showTrigger, space) <+>
          show(exp))
      case Exists(vars, exp) =>
        parens(("∃" or "exists") <+>
          ssep(vars map showVar, comma <> space) <+>
          ("•" or "::") <+>
          show(exp))
      case LocalVar(name, typ) => value(name)
      case _: PrettyUnaryExpression | _: PrettyBinaryExpression => super.toParenDoc(e)
    }
  }

}
