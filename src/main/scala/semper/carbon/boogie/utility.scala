package semper.carbon.boogie

/**
 * Utility methods for statements.
 *
 * @author Stefan Heule
 * @author Bernhard Brodowsky (parts of the SIL version of the corresponding object)
 */
object Statements {
  /** An empty statement. */
  val EmptyStmt = Seqn(Nil)

  /**
   * Returns a list of all actual statements contained in a given statement.  That
   * is, all statements except `Seqn`, including statements in the branches of
   * if's.
   *
   * Taken from the SIL AST with minimal adaptation.
   */
  def children(s: Stmt): Seq[Stmt] = {
    s match {
      case If(_, thn, els) => Seq(s) ++ children(thn) ++ children(els)
      case NondetIf(thn, els) => Seq(s) ++ children(thn) ++ children(els)
      case Seqn(ss) => ss flatMap children
      case _ => List(s)
    }
  }

  /**
   * Returns a list of all undeclared local variables used in this statement.
   * If the same local variable is used with different
   * types, an exception is thrown.
   *
   * Taken from the SIL AST with minimal adaptation.
   */
  def undeclLocalVars(s: Stmt): Seq[LocalVar] = {
    def extractLocal(n: Node, decls: Seq[LocalVarDecl]) = n match {
      case l: LocalVar => decls.find(_.name == l.name) match {
        case None => List(l)
        case Some(d) if d.typ != l.typ => {
          sys.error("Local variable " + l.name + " is declared with type " + d.typ + " but used with type " + l.typ + ".")
        }
        case _ => Nil
      }
      case _ => Nil
    }
    def combineLists(s1: Seq[LocalVar], s2: Seq[LocalVar]) = {
      for (l1 <- s1; l2 <- s2) {
        if (l1.name == l2.name && l1.typ != l2.typ) {
          sys.error("Local variable " + l1.name + " is used with different types " + l1.typ + " and " + l2.typ)
        }
      }
      (s1 ++ s2).distinct
    }
    def addDecls(n: Node, decls: Seq[LocalVarDecl]) = n match {
      case Exists(v, _) => decls ++ v
      case Forall(v, _, _) => decls ++ v
      case _ => decls
    }
    def combineResults(n: Node, decls: Seq[LocalVarDecl], localss: Seq[Seq[LocalVar]]) = {
      localss.fold(extractLocal(n, decls))(combineLists)
    }
    s.reduce(Nil, addDecls, combineResults)
  }
}

/**
 * Utility methods for AST nodes.
 *
 * @author Stefan Heule
 */
object Nodes {

  /**
   * See Node.subnodes.
   */
  def subnodes(n: Node): Seq[Node] = {
    n match {
      case Program(header, decls) =>
        decls
      case LocalVarDecl(name, typ, where) =>
        where match {
          case Some(e) => Seq(e)
          case None => Nil
        }
      case Trigger(exps) => exps
      case t: Type => Nil
      case d: Decl =>
        d match {
          case Const(name, typ, unique) => Nil
          case TypeDecl(name) => Nil
          case TypeAlias(n, d) => Nil
          case Func(name, args, typ) => args
          case Axiom(exp) => Seq(exp)
          case GlobalVarDecl(name, typ) => Nil
          case Procedure(name, ins, outs, body) => ins ++ outs ++ Seq(body)
          case CommentedDecl(s, ds) => ds
        }
      case s: Stmt =>
        s match {
          case Assign(lhs, rhs) => Seq(lhs, rhs)
          case Assert(e, error) => Seq(e)
          case Assume(e) => Seq(e)
          case Havoc(es) => es
          case Comment(s) => Nil
          case CommentBlock(s, stmt) => Seq(stmt)
          case Seqn(ss) => ss
          case If(cond, thn, els) => Seq(cond, thn, els)
          case NondetIf(thn, els) => Seq(thn, els)
          case Label(name) => Nil
          case Goto(target) => Nil
        }
      case e: Exp =>
        // Note: If you have to update this pattern match to make it exhaustive, it
        // might also be necessary to update the PrettyPrinter.toParenDoc method.
        e match {
          case IntLit(i) => Nil
          case BoolLit(b) => Nil
          case RealLit(b) => Nil
          case LocalVar(n, t) => Nil
          case ConstUse(i) => Nil
          case MapSelect(map, idxs) => Seq(map) ++ idxs
          case Old(exp) => Seq(exp)
          case CondExp(cond, thn, els) => Seq(cond, thn, els)
          case Exists(v, exp) => v ++ Seq(exp)
          case Forall(v, triggers, exp) => v ++ triggers ++ Seq(exp)
          case BinExp(left, binop, right) => Seq(left, right)
          case UnExp(unop, exp) => Seq(exp)
          case FuncApp(func, args) => args
        }
    }
  }
}