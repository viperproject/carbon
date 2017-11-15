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

  def transform[A <: Node](node: A,
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



object DuplicatingTransformer {

  def transform[A <: Node](node: A,
                           pre: PartialFunction[Node, Node] = PartialFunction.empty)(
                            recursive: Node => Boolean = !pre.isDefinedAt(_),
                            post: (Node => Seq[Node]) = (n => Seq(n))): Seq[A] = {
    def go[B <: Node](root: B): Seq[B] = {
      transform(root, pre)(recursive, post)
    }

    def goSeq[B <: Node](nodes: Seq[B]): Seq[Seq[B]] =
    {
      if (nodes.isEmpty) Seq(Seq()) else if (nodes.size == 1) go(nodes.head) map (Seq(_)) else {
        val headResults = go(nodes.head)
        val tailResults = goSeq(nodes.tail)
        for { hd <- headResults; tl <- tailResults } yield (hd +: tl)
      }
    }

    def recurse(parent: Node): Seq[Node] = {
      parent match {
        case Program(header, declarations) =>
          goSeq(declarations) map (Program(header,_))
        case LocalVarDecl(name, typ, Some(where)) =>
          for {typResult <- go(typ); whereResult <- go(where)} yield
          LocalVarDecl(name, typResult, Some(whereResult))
        case LocalVarDecl(name, typ, None) =>
          go(typ) map (LocalVarDecl(name, _, None))
        case Trigger(exps) =>
          goSeq(exps) map (Trigger(_))
        case t: Type => Seq(parent)
        case d: Decl =>
          d match {
            case ConstDecl(name, typ, unique) => go(typ) map (ConstDecl(name, _, unique))
            case TypeDecl(name) => Seq(parent)
            case TypeAlias(n, de) => for {nResult <- go(n); deResult <- go(de)} yield TypeAlias(nResult, deResult)
            case Func(name, args, typ) => for {argsResult <- goSeq(args); typResult <- go(typ)} yield Func(name, argsResult, typResult)
            case Axiom(exp) => go(exp) map (Axiom(_))
            case GlobalVarDecl(name, typ) => go(typ) map (GlobalVarDecl(name, _))
            case Procedure(name, ins, outs, body) =>
              for {insResult <- goSeq(ins); outsResult <- goSeq(outs); bodyResult <- go(body)} yield
                Procedure(name, insResult, outsResult, bodyResult)
            case CommentedDecl(s, ds, a, b) => goSeq(ds) map (CommentedDecl(s, _, a, b))
            case DeclComment(s) => Seq(parent)
            case LiteralDecl(s) => Seq(parent)
          }
        case ss: Stmt =>
          ss match {
            case Assign(lhs, rhs) => for {lhsResult <- go(lhs); rhsResult <- go(rhs)} yield Assign(lhsResult, rhsResult)
            case Assert(e, error) => go(e) map (Assert(_, error))
            case Assume(e) => go(e) map (Assume(_))
            case HavocImpl(es) => goSeq(es) map (HavocImpl(_))
            case Comment(s) => Seq(parent)
            case CommentBlock(s, stmt) => go(stmt) map (CommentBlock(s, _))
            case Seqn(s) => goSeq(s) map (Seqn(_))
            case If(cond, thn, els) =>
              for {condResult <- go(cond); thnResult <- go(thn); elsResult <- go(els)} yield
                (If(condResult, thnResult, elsResult))
            case NondetIf(thn, els) =>
              for {thnResult <- go(thn); elsResult <- go(els)} yield
                (NondetIf(thnResult, elsResult))
            case Label(name) => Seq(parent)
            case Goto(target) => Seq(parent)
            case LocalVarWhereDecl(idn, where) => go(where) map (LocalVarWhereDecl(idn, _))
          }
        case e: Exp =>
          // Note: If you have to update this pattern match to make it exhaustive, it
          // might also be necessary to update the PrettyPrinter.toParenDoc method.
          e match {
            case IntLit(i) => Seq(parent)
            case BoolLit(b) => Seq(parent)
            case RealLit(b) => Seq(parent)
            case RealConv(exp) => go(exp) map (RealConv(_))
            case LocalVar(n, t) => go(t) map (LocalVar(n, _))
            case GlobalVar(n, t) => go(t) map (GlobalVar(n, _))
            case Const(i) => Seq(parent)
            case MapSelect(map, idxs) =>
              for {mapResult <- go(map); idxsResult <- goSeq(idxs)} yield MapSelect(mapResult, idxsResult)
            case Old(exp) => go(exp) map (Old(_))
            case CondExp(cond, thn, els) =>
              for {condResult <- go(cond); thnResult <- go(thn); elsResult <- go(els)} yield
                (CondExp(condResult, thnResult, elsResult))
            case Exists(v, exp) =>
              for {vResult <- goSeq(v); expResult <- go(exp)} yield Exists(vResult, expResult)

            case Forall(v, triggers, exp, tv) =>
              for {vResult <- goSeq(v); triggersResult <- goSeq(triggers); expResult <- go(exp)} yield
              Forall(vResult, triggersResult, expResult, tv)
            case BinExp(left, binop, right) =>
              for {leftResult <- go(left); rightResult <- go(right)} yield BinExp(leftResult, binop, rightResult)
            case UnExp(unop, exp) => go(exp) map (UnExp(unop, _))
            case f@FuncApp(func, args, typ) => {
              val results =
                for {argsResult <- goSeq(args); typResult <- go(typ)} yield FuncApp(func, argsResult, typResult)
              results.foreach(fa => fa.showReturnType = f.showReturnType)
              results
            }
          }
      }
    }

    val beforeRecursion = pre.applyOrElse(node, identity[Node])
    val afterRecursion = if (recursive(node)) {
      recurse(beforeRecursion)
    } else {
      Seq(beforeRecursion)
    }
    (afterRecursion flatMap post).asInstanceOf[Seq[A]]
  }
}
