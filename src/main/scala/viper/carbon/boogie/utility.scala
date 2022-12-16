// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.boogie


/**
 * Utility methods for statements.
 */
object Statements {
  /** An empty statement. */
  val EmptyStmt = Seqn(Nil)

  /**
   * Returns a list of all actual statements contained in a given statement.  That
   * is, all statements except `Seqn`, including statements in the branches of
   * if's.
   *
   * Taken from the Viper AST with minimal adaptation.
   */
  def children(s: Stmt): Seq[Stmt] = {
    s match {
      case If(_, thn, els) => Seq(s) ++ children(thn) ++ children(els)
      case NondetIf(thn, els) => Seq(s) ++ children(thn) ++ children(els)
      case Seqn(ss) => ss flatMap children
      case CommentBlock(_, stmt) => Seq(stmt)
      case _ => List(s)
    }
  }

  /**
   * Returns a list of all undeclared local variables used in this statement.
   * If the same local variable is used with different
   * types, an exception is thrown.
   *
   * Taken from the Viper AST with minimal adaptation.
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
      case Exists(v, _, _, _) => decls ++ v
      case Forall(v, _, _, _, _) => decls ++ v
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

 */
object Nodes {

  /**
   * See Node.subnodes.
   */
  def subnodes(n: Node): Seq[Node] = {
    n match {
      case Program(_, decls) =>
        decls
      case LocalVarDecl(_, _, where) =>
        where match {
          case Some(e) => Seq(e)
          case None => Nil
        }
      case Trigger(exps) => exps
      case _: Type => Nil
      case d: Decl =>
        d match {
          case ConstDecl(_, _, _) => Nil
          case TypeDecl(_) => Nil
          case TypeAlias(_, _) => Nil
          case Func(_, args, _, _) => args
          case Axiom(exp) => Seq(exp)
          case GlobalVarDecl(_, _) => Nil
          case Procedure(_, ins, outs, body) => ins ++ outs ++ Seq(body)
          case CommentedDecl(_, ds, _, _) => ds
          case DeclComment(_) => Nil
          case LiteralDecl(_) => Nil
        }
      case ss: Stmt =>
        ss match {
          case Assign(lhs, rhs) => Seq(lhs, rhs)
          case Assert(e, _) => Seq(e)
          case Assume(e) => Seq(e)
          case HavocImpl(es) => es
          case Comment(_) => Nil
          case CommentBlock(_, stmt) => Seq(stmt)
          case Seqn(s) => s
          case If(cond, thn, els) => Seq(cond, thn, els)
          case NondetIf(thn, els) => Seq(thn, els)
          case Label(_) => Nil
          case Goto(_) => Nil
          case LocalVarWhereDecl(_, where) => Seq(where)
        }
      case e: Exp =>
        // Note: If you have to update this pattern match to make it exhaustive, it
        // might also be necessary to update the PrettyPrinter.toParenDoc method.
        e match {
          case IntLit(_) => Nil
          case BoolLit(_) => Nil
          case RealLit(_) => Nil
          case RealConv(exp) => Seq(exp)
          case LocalVar(_, _) => Nil
          case GlobalVar(_, _) => Nil
          case Const(_) => Nil
          case MapSelect(map, idxs) => Seq(map) ++ idxs
          case MapUpdate(map, idxs, value) => Seq(map) ++ idxs ++ Seq(value)
          case Old(exp) => Seq(exp)
          case CondExp(cond, thn, els) => Seq(cond, thn, els)
          case Exists(v, triggers, exp, _) => v ++ triggers ++ Seq(exp)
          case Forall(v, triggers, exp, _, _) => v ++ triggers ++ Seq(exp)
          case BinExp(left, _, right) => Seq(left, right)
          case UnExp(_, exp) => Seq(exp)
          case FuncApp(_, args, _) => args
        }
    }
  }

  /**
   * Transforms an expression using the function `f`;  if `f` returns `Some(e)`, then the previous expression
   * is replaced by e, and otherwise the previous expression is reused.
   * The function `f` must produce expressions that are valid in the given context.  For instance, it cannot
   * replace an integer literal by a boolean literal.
   */
  def transform(exp: Exp, f: PartialFunction[Exp, Option[Exp]]): Exp = {
    val func = (e: Exp) => transform(e, f)
    val t = if (f.isDefinedAt(exp)) f(exp) else None
    t match {
      case Some(ee) => ee
      case None =>
        exp match {
          case IntLit(i) => exp
          case BoolLit(b) => exp
          case RealLit(b) => exp
          case RealConv(exp) => RealConv(func(exp))
          case LocalVar(n, tt) => exp
          case GlobalVar(n, tt) => exp
          case Const(i) => exp
          case MapSelect(map, idxs) => MapSelect(func(map), idxs map func)
          case MapUpdate(map, idxs, value) => MapUpdate(func(map), idxs map func, func(value))
          case Old(e) => Old(func(e))
          case CondExp(cond, thn, els) => CondExp(func(cond), func(thn), func(els))
          case Exists(v, triggers, e, w) => Exists(v, (triggers map (_ match {case Trigger(es) => Trigger(es map func)})), func(e), w)
          case Forall(v, triggers, e, tv, w) => Forall(v, (triggers map (_ match {case Trigger(es) => Trigger(es map func)})), func(e), tv, w)
          case BinExp(left, binop, right) => BinExp(func(left), binop, func(right))
          case UnExp(unop, e) => UnExp(unop, func(e))
          case f@FuncApp(ff, args, typ) => {
            val fa = FuncApp(ff, args map func, typ)
            fa.showReturnType = f.showReturnType
            fa
          }
        }
    }
  }
}
