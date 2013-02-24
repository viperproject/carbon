package semper.carbon.boogie

import org.kiama.output._
import UnicodeString.string2unicodestring

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

  def showType(t: Type): Doc = {
    t match {
      case Int => value("int")
      case Bool => value("bool")
      case Real => value("real")
      case TypeVar(name) => value(name)
      case MapType(doms, range, typVars) =>
        val tvs = typVars match {
          case Nil => empty
          case _ => ("〈" or "<") <> commasep(typVars) <> ("〉" or ">")
        }
        tvs <> "[" <> commasep(doms) <> "]" <> showType(range)
    }
  }

  def freeTypVars(t: Type): Seq[TypeVar] = t match {
    case Int | Bool | Real => Nil
    case tv@TypeVar(name) => Seq(tv)
    case MapType(doms, range, typVars) =>
      (doms flatMap freeTypVars) ++ freeTypVars(range)
  }

  def showStmt(stmt: Stmt) = {
    def showIf(cond: Doc, thn: Seq[Stmt], els: Seq[Stmt]): Doc = {
      "if" <+> "(" <> cond <> ")" <+> showBlock(thn) <> {
        if (els.size == 0) empty
        else space <> "else" <+> showBlock(els)
      }
    }
    stmt match {
      case Assume(e) =>
        "assume" <+> show(e) <> semi
      case Assert(e) =>
        "assert" <+> show(e) <> semi
      case Havoc(vars) =>
        "assume" <+> commasep(vars) <> semi
      case Goto(dests) =>
        "goto" <+> ssep(dests map value, comma <> space)
      case Assign(lhs, rhs) =>
        show(lhs) <+> ":=" <+> show(rhs) <> semi
      case Label(lbl) =>
        lbl.name <> colon
      case If(cond, thn, els) =>
        showIf(show(cond), thn, els)
      case NondetIf(thn, els) =>
        showIf("*", thn, els)
      case Comment(s) =>
        "//" <+> s
      case CommentBlock(s, stmts) =>
        show(Comment(s)) <>
          nest(
            line <> showStmts(stmts)
          )
    }
  }

  def showBlock(stmts: Seq[Stmt]) = {
    braces(nest(
      (if (stmts.isEmpty) empty else line) <>
        showStmts(stmts)
    ) <> line)
  }

  def showStmts(stmts: Seq[Stmt]) = ssep(stmts map show, line)

  def showProgram(p: Program) = {
    val decls = p.decls
    ssep(decls map show, line <> line)
  }

  def showDecl(decl: Decl) = {
    decl match {
      case Const(name, typ) =>
        "const" <+> name <+> show(typ) <> semi
      case Func(name, args, typ) =>
        "function" <+>
          name <>
          parens(commasep(args)) <>
          colon <+>
          show(typ)
      case GlobalVarDecl(name, typ) =>
        "var" <+> name <> colon <+> show(typ)
      case Axiom(exp) =>
        "axiom" <+> show(exp) <> semi
      case Procedure(name, ins, outs, body) =>
        "procedure" <+>
        name <>
        parens(commasep(ins)) <+>
        "returns" <+>
        parens(commasep(outs)) <+>
        showBlock(body)
    }
  }

  /**
   * Show a list of nodes, separated by a comma and a space.
   */
  def commasep(ns: Seq[Node]) = ssep(ns map show, comma <> space)

  def showVar(variable: LocalVarDecl) = {
    variable.name <> ":" <+> showType(variable.typ) <>
      (variable.where match {
        case Some(e) => space <> "where" <+> show(e)
        case None => empty
      })
  }

  def showTrigger(t: Trigger) = {
    "{" <+> commasep(t.exps) <+> "}"
  }

  // Note: pretty-printing expressions is mostly taken care of by kiama
  override def toParenDoc(e: PrettyExpression): Doc = {
    e match {
      case IntLit(i) => value(i)
      case BoolLit(b) => value(b)
      case RealLit(d) => value(d)
      case Forall(vars, triggers, exp) =>
        parens(("∀" or "forall") <+>
          commasep(vars) <+>
          ("•" or "::") <+>
          commasep(triggers) <+>
          show(exp))
      case Exists(vars, exp) =>
        parens(("∃" or "exists") <+>
          commasep(vars) <+>
          ("•" or "::") <+>
          show(exp))
      case LocalVar(name, typ) => value(name)
      case _: PrettyUnaryExpression | _: PrettyBinaryExpression => super.toParenDoc(e)
    }
  }

}
