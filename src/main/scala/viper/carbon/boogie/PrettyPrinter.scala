/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.boogie

//import org.kiama.output._
import org.kiama.output._
import viper.silver.ast.pretty._
import viper.silver.verifier.VerificationError

/**
 * A pretty printer for the Boogie AST.
 */
object PrettyPrinter {
  def pretty(n: Node): String = {
    new PrettyPrinter(n).pretty
  }
}

/**
 * The class that implements most of the pretty-printing functionality.
 */
class PrettyPrinter(n: Node) extends org.kiama.output.PrettyPrinter with ParenPrettyPrinter {

  lazy val pretty: String = {
    pretty(n)
  }

  /** BoogieNameGenerator instance. */
  private val names = new BoogieNameGenerator()

  /**
   * The current mapping from identifier to names.
   */
  private val idnMap = collection.mutable.HashMap[Identifier, String]()

  /**
   * The current store for where clauses of identifiers.
   */
  private val whereMap = collection.mutable.HashMap[Identifier, Exp]()

  /**
   * The collection of all global variables.
   */
  lazy val globalDecls = {
    val res = collection.mutable.ListBuffer[GlobalVarDecl]()
    n visit {
      case g: GlobalVarDecl => res += g
    }
    res
  }

  import language.implicitConversions

  /**
   * Map an identifier to a string, making it unique first if necessary.
   */
  implicit def ident2doc(i: Identifier): Doc = {
    idnMap.get(i) match {
      case Some(s) => s
      case None =>
        val s = names.createUniqueIdentifier(i.preferredName)
        idnMap.put(i, s)
        s
    }
  }

  override val defaultIndent = 2
  /** Pretty-print any AST node. */
  def pretty(n: Node): String = {
    super.pretty(show(n))
  }

  /** Show any AST node. */
  def show(n: Node) : Doc = { show(n,false) }

  /** Show any AST node, with extra flag to indicate that (in the context), arguments are being parsed via whitespace (e.g., Field A (Seq B) is needed instead of Field A Seq B) */
  def show(n: Node, spaceDelimitedContext : Boolean): Doc = {
    n match {
      case exp: Exp => toParenDoc(exp)
      case stmt: Stmt => showStmt(stmt)
      case typ: Type => showType(typ, spaceDelimitedContext)
      case p: Program => showProgram(p)
      case m: Decl => showDecl(m)
      case t: Trigger => showTrigger(t)
      case l: LocalVarDecl =>
        showVar(l)
    }
  }

  def showType(t: Type, spaceDelimitedContext : Boolean): Doc = {
    t match {
      case Int => "int"
      case Bool => "bool"
      case Real => "real"
      case TypeVar(name) => name
      case NamedType(name, typVars) =>
        (if (typVars.size == 0) name
        else (if (spaceDelimitedContext) "(" else "") <> name <> space <> ssep((typVars map (x => (show(x,true)))).to[collection.immutable.Seq],space) <> (if (spaceDelimitedContext) ")" else "") <> "")
      case MapType(doms, range, typVars) =>
        showTypeVars(typVars) <> "[" <> commasep(doms) <> "]" <> showType(range,false)
    }
  }

  def showStmt(s: Stmt): Doc = {
    def showIf(cond: Doc, thn: Stmt, els: Stmt): Doc = {
      "if" <+> "(" <> cond <> ")" <+> showBlock(thn) <> {
        if (els.children.size == 0) empty
        else space <> "else" <+> showBlock(els)
      }
    }
    s match {
      case Assume(e) =>
        "assume" <+> quantifyOverFreeTypeVars(e) <> char (';')
      case a@Assert(e, error) =>
        "assert" <+>
          "{:msg" <+> "\"  " <> showError(error, a.id) <> "\"}" <> line <>
          space <> space <> quantifyOverFreeTypeVars(e) <>
          char (';')
      case HavocImpl(vars) =>
        "havoc" <+> commasep(vars) <> char (';')
      case Goto(dests) =>
        "goto" <+> ssep((dests map (x => ident2doc(x.name))).to[collection.immutable.Seq], char (',') <> space) <> char (';')
      case Assign(lhs, rhs) =>
        show(lhs) <+> ":=" <+> show(rhs) <> char (';')
      case Label(lbl) =>
        lbl.name <> char (':')
      case If(cond, thn, els) =>
        showIf(show(cond), thn, els)
      case NondetIf(thn, els) =>
        showIf("*", thn, els)
      case Comment(c) =>
        "//" <+> c
      case CommentBlock(c, stmt) =>
        line <> show(Comment(s"-- $c")) <>
          nest(
            line <> showStmt(stmt)
          )
      case Seqn(ss) =>
        showStmts(ss)
      case LocalVarWhereDecl(v, w) => empty
    }
  }

  def showError(error: VerificationError, id: Int) = {
    s"${error.readableMessage} [$id]"
  }

  def showBlock(stmt: Stmt) = {
    braces(nest(
      (if (stmt.children.isEmpty) empty else line) <>
        showStmt(stmt)
    ) <> line)
  }

  def showBlock(d: Doc) = {
    braces(nest(
      line <> d
    ) <> line)
  }

  def showStmts(stmts: Seq[Stmt]) = {
    def needsPrinting(x: Stmt): Boolean = {
      !(x.isInstanceOf[Seqn] && x.children.count(needsPrinting) == 0 ||
        x.isInstanceOf[LocalVarWhereDecl])
    }
    // filter out statements that do not need to be printed such as
    // empty Seqn or LocalVarWhereDecl
    val ss = stmts filter needsPrinting
    ssep(ss.to[collection.immutable.Seq] map show, line)
  }

  def showProgram(p: Program) = {
    ssep((p.header map (s => value("// " + s))).to[collection.immutable.Seq], line) <> line <> line <>
      showDecls(p.decls)
  }

  def showDecls(ds: Seq[Decl], sep: Doc = line <> line): Doc = {
    ssep(ds.to[collection.immutable.Seq] map show, sep)
  }

  /**
   * Return all free type variables from an expression.
   */
  def collectFreeTypeVars(exp: Exp): Seq[TypeVar] = {
    val res = collection.mutable.ListBuffer[TypeVar]()
    val not = collection.mutable.ListBuffer[TypeVar]()
    exp visit {
      case LocalVarDecl(_, t, _) =>
        res ++= t.freeTypeVars
      case FuncApp(_, _, t) =>
        res ++= t.freeTypeVars
      case Forall(_, _, _, tv) =>
        not ++= tv
    }
    (res.toSet -- not.toSet).toSeq
  }

  def showDecl(decl: Decl) = {
    decl match {
      case ConstDecl(name, typ, unique) =>
        "const" <+>
          (if (unique) "unique" <> space else empty) <>
          name <>
          char (':') <+>
          show(typ) <>
          char (';')
      case TypeDecl(name) =>
        "type" <+> show(name) <> char (';')
      case TypeAlias(name, definition) =>
        "type" <+> show(name) <+> "=" <+> show(definition) <> char (';')
      case Func(name, args, typ) =>
        val typVars = (args map (_.typ)) ++ Seq(typ) flatMap (_.freeTypeVars)
        "function" <+>
          name <>
          showTypeVars(typVars, endWithSpace = false) <>
          parens(commasep(args)) <>
          char (':') <+>
          show(typ) <> char (';')
      case GlobalVarDecl(name, typ) =>
        "var" <+> name <> char (':') <+> show(typ) <> char (';')
      case Axiom(exp) =>
        "axiom" <+> quantifyOverFreeTypeVars(exp) <> char (';')
      case Procedure(name, ins, outs, body) =>
        // collect all where clauses
        whereMap.clear()
        body visit {
          case LocalVarWhereDecl(idn, where) =>
            whereMap.put(idn, where)
        }
        // we add a modifies clause that contains all global variables. since we do not actually
        // call any of the Boogie procedures, this works well and avoids the need to have
        // modules declare which variables they want to modify.
        val modifies = globalDecls map (_.name) map ident2doc
        val body2 = show(body)
        val undecl = body.undeclLocalVars filter (v1 => (ins ++ outs).forall(v2 => v2.name != v1.name))
        val vars = undecl map (v => LocalVarDecl(v.name, v.typ, whereMap.get(v.name)))
        val vars2 = vars map (v => "var" <+> show(v) <> ";")
        val vars3 = ssep(vars2.to[collection.immutable.Seq], line) <> (if (vars2.size == 0) empty else line)
        "procedure" <+>
          name <>
          parens(commasep(ins)) <+>
          "returns" <+>
          parens(commasep(outs)) <>
          line <> space <> space <>
          "modifies" <+> ssep(modifies.to[collection.immutable.Seq], char (',') <> space) <> char (';')  <> line <>
          showBlock(vars3 <> body2)
      case CommentedDecl(s, d, size, nlines) =>
        var linesep = empty
        for (i <- 1 to nlines) {
          linesep = line <> linesep
        }
        if (size > 1) {
          val sep = if (size == 3) "=" else "-"
          "// " + sep * 50 <> line <>
            "//" <+> value(s) <> line <>
            "// " + sep * 50 <> line <>
            (if (size == 3) line else empty) <>
            showDecls(d, linesep)
        } else {
          "//" <+> value(s) <> line <>
            showDecls(d, linesep)
        }
      case DeclComment(s) =>
        value(s"// $s")
      case LiteralDecl(s) =>
        value(s)
    }
  }

  /**
   * Quantifies over the free type variables in 'exp' if necessary.
   */
  def quantifyOverFreeTypeVars(exp: Exp): Doc = {
    val t = collectFreeTypeVars(exp)
    val body = t match {
      case Nil => show(exp)
      case _ =>
        exp match {
          case Forall(vars, triggers, _body, tv) =>
            show(Forall(vars, triggers, _body, tv++t))
          case _ =>
            parens("forall" <+> showTypeVars(t) <> "::" <+> show(exp)) // NOTE: no triggers selected! This should be changed, but requires trigger generation code on the level of the Boogie AST.
        }
    }
    body
  }
  /**
   * Show a list of nodes, separated by a comma and a space.
   */
  def commasep(ns: Seq[Node]) = ssep((ns map show).to[collection.immutable.Seq], char (',') <> space)

  def showVar(variable: LocalVarDecl) = {
    variable.name <> ":" <+> showType(variable.typ,true) <>
      (variable.where match {
        case Some(e) => space <> "where" <+> show(e)
        case None => empty
      })
  }

  def showTrigger(t: Trigger) = {
    "{" <+> commasep(t.exps) <+> "}"
  }

  // Note: pretty-printing expressions is mostly taken care of by Kiama
  override def toParenDoc(e: PrettyExpression): Doc = {
    e match {
      case IntLit(i) => value(i)
      case BoolLit(b) => value(b)
      case RealLit(d) =>
        /* Enforcing US locale prevents malformed real literals that would be
         * generated on, e.g., a Windows with German locale, where the decimal
         * separator would be a comma instead of a dot, e.g., "1,2345...".
         */
        value("%.9f".formatLocal(java.util.Locale.US, d))
      case RealConv(exp) => "real" <> parens(show(exp))
//      case Forall(vars, triggers, exp, tv) if triggers.length > 1 => // expands foralls into conjunctions of foralls with single triggers each
//        show(triggers.tail.foldLeft[Exp](Forall(vars, Seq(triggers.head), exp, tv))((soFar,nextTrig) => BinExp(soFar,And,Forall(vars, Seq(nextTrig), exp, tv))))
      case Forall(vars, triggers, exp, Nil) =>
        parens("forall" <+>
          commasep(vars) <+>
          //("•" or "::") <+>
          "::" <>
          nest(
            line <>
              ssep((triggers map show).to[collection.immutable.Seq], space) <> line <>
              show(exp)
          ) <> line)
      case Forall(vars, triggers, exp, tv) =>
        parens("forall" <+>
          "<" <> ssep((tv map show).to[collection.immutable.Seq], char (',') <> space) <> ">" <+>
          commasep(vars) <+>
          //("•" or "::") <+>
          "::" <>
          nest(
            line <>
              ssep((triggers map show).to[collection.immutable.Seq], space) <> line <>
              show(exp)
          ) <> line)
      case Exists(vars, exp) =>
        parens("exists" <+>
          commasep(vars) <+>
          //("•" or "::") <+>
          "::" <>
          nest(
            line <> show(exp)
          ) <> line)
      case LocalVar(name, typ) => name
      case GlobalVar(name, typ) => name
      case Const(name) => name
      case Old(exp) => "old" <> parens(show(exp))
      case MapSelect(map, idxs) =>
        show(map) <> "[" <> commasep(idxs) <> "]"
      case f@FuncApp(name, args, typ) =>
        // if the return type of the function is generic, include a type annotation
        // also, if the FuncApp is explicitly flagged (showReturn
        val fa = name <> parens(commasep(args))
        typ.freeTypeVars match {
          case Nil => if (f.showReturnType) parens(fa <> ":" <+> show(typ)) else fa
          case _ => parens(fa <> ":" <+> show(typ))
        }
      case CondExp(cond, e1, e2) =>
        parens("if" <+> show(cond) <+> "then" <+> show(e1) <+> "else" <+> show(e2))
      case _: PrettyUnaryExpression | _: PrettyBinaryExpression => {
        e match {
          case b: PrettyBinaryExpression =>
            val ld =
              b.left match {
                case l: PrettyOperatorExpression =>
                  bracket(l, b, LeftAssoc)
                case l =>
                  toParenDoc(l)
              }
            val rd =
              b.right match {
                case r: PrettyOperatorExpression =>
                  bracket(r, b, RightAssoc)
                case r =>
                  toParenDoc(r)
              }
            ld <+> text(b.op) <+> rd

          case u: PrettyUnaryExpression =>
            val ed =
              u.exp match {
                case e: PrettyOperatorExpression =>
                  bracket(e, u, NonAssoc)
                case e =>
                  toParenDoc(e)
              }
            if (u.fixity == Prefix)
              text(u.op) <> ed
            else
              ed <> text(u.op)

        }
      }
      case _ => sys.error(s"unknown expression: ${e.getClass}")
    }
  }

  /**
   * Show free type variables (e.g. for a function, a map type or a quantification).
   */
  def showTypeVars(typVars: Seq[TypeVar], endWithSpace: Boolean = true): Doc = {
    if (typVars.size > 0)
      ("<") <> commasep(typVars.distinct) <> (">") <> // AJS: removed non-standard alternate symbols that editor could not display
        (if (endWithSpace) space else empty)
    else empty
  }
}
