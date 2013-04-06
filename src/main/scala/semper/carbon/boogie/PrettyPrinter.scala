package semper.carbon.boogie

import org.kiama.output._
import UnicodeString.string2unicodestring
import semper.sil.verifier.VerificationError

/**
 * A pretty printer for the Boogie AST.
 *
 * @author Stefan Heule
 */
object PrettyPrinter {
  def pretty(n: Node): String = {
    (new PrettyPrinter(n)).pretty
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
  private var idnMap = collection.mutable.HashMap[Identifier, String]()

  /**
   * The current store for where clauses of identifiers.
   */
  private var whereMap = collection.mutable.HashMap[Identifier, Exp]()

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
  def show(n: Node): Doc = {
    n match {
      case exp: Exp => toParenDoc(exp)
      case stmt: Stmt => showStmt(stmt)
      case typ: Type => showType(typ)
      case p: Program => showProgram(p)
      case m: Decl => showDecl(m)
      case t: Trigger => showTrigger(t)
      case l: LocalVarDecl =>
        showVar(l)
    }
  }

  def showType(t: Type): Doc = {
    t match {
      case Int => "int"
      case Bool => "bool"
      case Real => "real"
      case TypeVar(name) => name
      case NamedType(name, typVars) =>
        name <> (if (typVars.size == 0) empty
        else space <> ssep(typVars map show, space))
      case MapType(doms, range, typVars) =>
        showTypeVars(typVars) <> "[" <> commasep(doms) <> "]" <> showType(range)
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
        "assume" <+> quantifyOverFreeTypeVars(e) <> semi
      case a@Assert(e, error) =>
        "assert" <+>
          "{:msg" <+> "\"  " <> showError(error, a.id) <> "\"}" <> line <>
          space <> space <> quantifyOverFreeTypeVars(e) <>
          semi
      case Havoc(vars) =>
        "havoc" <+> commasep(vars) <> semi
      case Goto(dests) =>
        "goto" <+> ssep(dests map (x => ident2doc(x.name)), comma <> space) <> semi
      case Assign(lhs, rhs) =>
        show(lhs) <+> ":=" <+> show(rhs) <> semi
      case Label(lbl) =>
        lbl.name <> colon
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
      !((x.isInstanceOf[Seqn] && (x.children.filter(needsPrinting)).size == 0) ||
        x.isInstanceOf[LocalVarWhereDecl])
    }
    // filter out statements that do not need to be printed such as
    // empty Seqn or LocalVarWhereDecl
    val ss = stmts filter needsPrinting
    ssep(ss map show, line)
  }

  def showProgram(p: Program) = {
    ssep(p.header map (s => value("// " + s)), line) <> line <> line <>
      showDecls(p.decls)
  }

  def showDecls(ds: Seq[Decl], sep: Doc = line <> line): Doc = {
    ssep(ds map show, sep)
  }

  /**
   * Return all free type variables from an expression.
   */
  def collectFreeTypeVars(exp: Exp): Seq[TypeVar] = {
    val res = collection.mutable.ListBuffer[TypeVar]()
    exp visit {
      case LocalVarDecl(_, t, _) =>
        res ++= t.freeTypeVars
      case FuncApp(_, _, t) =>
        res ++= t.freeTypeVars
    }
    res.toSeq
  }

  def showDecl(decl: Decl) = {
    decl match {
      case ConstDecl(name, typ, unique) =>
        "const" <+>
          (if (unique) "unique" <> space else empty) <>
          name <>
          colon <+>
          show(typ) <>
          semi
      case TypeDecl(name) =>
        "type" <+> show(name) <> semi
      case TypeAlias(name, definition) =>
        "type" <+> show(name) <+> "=" <+> show(definition) <> semi
      case Func(name, args, typ) =>
        val typVars = ((args map (_.typ)) ++ Seq(typ)) flatMap (_.freeTypeVars)
        "function" <+>
          name <>
          showTypeVars(typVars, endWithSpace = false) <>
          parens(commasep(args)) <>
          colon <+>
          show(typ) <> semi
      case GlobalVarDecl(name, typ) =>
        "var" <+> name <> colon <+> show(typ) <> semi
      case Axiom(exp) =>
        "axiom" <+> quantifyOverFreeTypeVars(exp) <> semi
      case Procedure(name, ins, outs, body) =>
        // collect all where clauses
        whereMap = collection.mutable.HashMap[Identifier, Exp]()
        body visit {
          case LocalVarWhereDecl(idn, where) =>
            whereMap.put(idn, where)
        }
        // we add a modifies clause that contains all global variables. since we do not actually
        // call any of the Boogie procedures, this works well and avoids the need to have
        // modules declare which variables they want to modify.
        val modifies = globalDecls map (_.name) map (ident2doc(_))
        val body2 = show(body)
        val undecl = body.undeclLocalVars filter (v1 => (ins ++ outs).forall(v2 => v2.name != v1.name))
        val vars = undecl map (v => LocalVarDecl(v.name, v.typ, whereMap.get(v.name)))
        val vars2 = vars map (v => "var" <+> show(v) <> ";")
        val vars3 = ssep(vars2, line) <> (if (vars2.size == 0) empty else line)
        "procedure" <+>
          name <>
          parens(commasep(ins)) <+>
          "returns" <+>
          parens(commasep(outs)) <>
          line <> space <> space <>
          "modifies" <+> ssep(modifies, comma <> space) <> semi <> line <>
          showBlock(vars3 <> body2)
      case CommentedDecl(s, d, size, nlines) =>
        var linesep = empty
        for (i <- 1 to nlines) {
          linesep = line <> linesep
        }
        if (size > 1) {
          val sep = if (size == 3) "=" else "-"
          ("// " + (sep * 50)) <> line <>
            "//" <+> value(s) <> line <>
            ("// " + (sep * 50)) <> line <>
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
      case _ => parens("forall" <+> showTypeVars(t) <> "::" <+> show(exp))
    }
    body
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
        parens("forall" <+> //("∀" or "forall") <+>
          commasep(vars) <+>
          //("•" or "::") <+>
          "::" <+>
          commasep(triggers) <+>
          show(exp))
      case Exists(vars, exp) =>
        parens("exists" <+> //("∃" or "exists") <+>
          commasep(vars) <+>
          //("•" or "::") <+>
          "::" <+>
          show(exp))
      case LocalVar(name, typ) => name
      case GlobalVar(name, typ) => name
      case Const(name) => name
      case MapSelect(map, idxs) =>
        show(map) <> "[" <> commasep(idxs) <> "]"
      case FuncApp(name, args, typ) =>
        // if the return type of the function is generic, include a type annotation
        val fa = name <> parens(commasep(args))
        typ.freeTypeVars match {
          case Nil => fa
          case _ => parens(fa <> ":" <+> show(typ))
        }
      case _: PrettyUnaryExpression | _: PrettyBinaryExpression => super.toParenDoc(e)
    }
  }

  /**
   * Show free type variables (e.g. for a function, a map type or a quantification).
   */
  def showTypeVars(typVars: Seq[TypeVar], endWithSpace: Boolean = true): Doc = {
    (if (typVars.size > 0)
      ("〈" or "<") <> commasep(typVars.distinct) <> ("〉" or ">") <>
        (if (endWithSpace) space else empty)
    else empty)
  }
}
