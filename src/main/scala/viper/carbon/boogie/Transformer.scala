/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.boogie


/**
 * An implementation for transformers of the Boogie AST.

 */
object Transformer {

  def transform[A <: Node](node: Node,
                           pre: PartialFunction[Node, Node] = PartialFunction.empty)(
                            recursive: Node => Boolean = !pre.isDefinedAt(_),
                            post: PartialFunction[Node, Node] = PartialFunction.empty): A = {
    def go[B <: Node](root: B): B = {
      transform(root, pre)(recursive, post)
    }

    def recurse(parent: Node): Node = {
      parent match {
        case Program(header, decls) =>
          Program(header, decls map go)
        case LocalVarDecl(name, typ, Some(where)) =>
          LocalVarDecl(name, go(typ), Some(go(where)))
        case LocalVarDecl(name, typ, None) =>
          LocalVarDecl(name, go(typ), None)
        case Trigger(exps) => Trigger(exps map go)
        case t: Type => parent
        case d: Decl =>
          d match {
            case ConstDecl(name, typ, unique) => ConstDecl(name, go(typ), unique)
            case TypeDecl(name) => parent
            case TypeAlias(n, de) => TypeAlias(go(n), go(de))
            case Func(name, args, typ) => Func(name, args map go, go(typ))
            case Axiom(exp) => Axiom(go(exp))
            case GlobalVarDecl(name, typ) => GlobalVarDecl(name, go(typ))
            case Procedure(name, ins, outs, body) => Procedure(name, ins map go, outs map go, go(body))
            case CommentedDecl(s, ds, a, b) => CommentedDecl(s, ds map go, a, b)
            case DeclComment(s) => parent
            case LiteralDecl(s) => parent
          }
        case ss: Stmt =>
          ss match {
            case Assign(lhs, rhs) => Assign(go(lhs), go(rhs))
            case Assert(e, error) => Assert(go(e), error)
            case Assume(e) => Assume(go(e))
            case HavocImpl(es) => HavocImpl(es map go)
            case Comment(s) => parent
            case CommentBlock(s, stmt) => CommentBlock(s, go(stmt))
            case Seqn(s) => Seqn(s map go)
            case If(cond, thn, els) => If(go(cond), go(thn), go(els))
            case NondetIf(thn, els) => NondetIf(go(thn), go(els))
            case Label(name) => parent
            case Goto(target) => parent
            case LocalVarWhereDecl(idn, where) => LocalVarWhereDecl(idn, go(where))
          }
        case e: Exp =>
          // Note: If you have to update this pattern match to make it exhaustive, it
          // might also be necessary to update the PrettyPrinter.toParenDoc method.
          e match {
            case IntLit(i) => parent
            case BoolLit(b) => parent
            case RealLit(b) => parent
            case RealConv(exp) => RealConv(go(exp))
            case LocalVar(n, t) => LocalVar(n, go(t))
            case GlobalVar(n, t) => GlobalVar(n, go(t))
            case Const(i) => parent
            case MapSelect(map, idxs) => MapSelect(go(map), idxs map go)
            case Old(exp) => Old(go(exp))
            case CondExp(cond, thn, els) => CondExp(go(cond), go(thn), go(els))
            case Exists(v, exp) => Exists(v map go, go(exp))
            case Forall(v, triggers, exp, tv) => Forall(v map go, triggers map go, go(exp), tv)
            case BinExp(left, binop, right) => BinExp(go(left), binop, go(right))
            case UnExp(unop, exp) => UnExp(unop, go(exp))
            case f@FuncApp(func, args, typ) => {
              val fa = FuncApp(func, args map go, go(typ))
              fa.showReturnType = f.showReturnType
              fa
            }
          }
      }
    }

    val beforeRecursion = pre.applyOrElse(node, identity[Node])
    val afterRecursion = if (recursive(node)) {
      recurse(beforeRecursion)
    } else {
      beforeRecursion
    }
    post.applyOrElse(afterRecursion, identity[Node]).asInstanceOf[A]
  }
}
