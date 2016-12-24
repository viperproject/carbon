
/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.boogie

import UnicodeString.string2unicodestring
import viper.silver.ast.pretty._
import viper.silver.verifier.VerificationError

/** The root of the Boogie AST. */
sealed trait Node {
  /**
   * Returns a list of all direct sub-nodes of this node.
   */
  lazy val subnodes = Nodes.subnodes(this)

  /**
   * Optimize a program or expression
   */
  lazy val optimize: this.type = Optimizer.optimize(this).asInstanceOf[this.type]

  /**
   * Applies the function `f` to the node and the results of the subnodes.
   */
  def reduce[T](f: (Node, Seq[T]) => T) = Visitor.reduce[T](this)(f)

  /**
   * More powerful version of reduce that also carries a context argument through the tree.
   */
  def reduce[C, R](context: C, enter: (Node, C) => C, combine: (Node, C, Seq[R]) => R) = {
    Visitor.reduce[C, R](this)(context, enter, combine)
  }

  /**
   * Applies the function `f` to the AST node, then visits all subnodes.
   */
  def visit(f: PartialFunction[Node, Unit]) {
    Visitor.visit(this)(f)
  }

  /**
   * Applies the function `f1` to the AST node, then visits all subnodes,
   * and finally calls `f2` to the AST node.
   */
  def visit(n: Node, f1: PartialFunction[Node, Unit], f2: PartialFunction[Node, Unit]) {
    Visitor.visit(this, f1, f2)
  }

  /**
   * Applies the function `f` to the AST node, then visits all subnodes if `f`
   * returned true.
   */
  def visitOpt(n: Node)(f: Node => Boolean) {
    Visitor.visitOpt(this)(f)
  }

  /**
   * Applies the function `f1` to the AST node, then visits all subnodes if `f1`
   * returned true, and finally calls `f2` to the AST node.
   */
  def visitOpt(n: Node, f1: Node => Boolean, f2: Node => Unit) {
    Visitor.visitOpt(this, f1, f2)
  }

  /**
   * Performs substitution on the AST
    *
    * @param original The node to match against (and replace)
   * @param replacement The node to replace all occurrences with
   * @return The result of the substitution
   */
  def replace(original: Node, replacement: Node): this.type =
    this.transform({case `original` => replacement})()

  /**
    * This extra level of indirection (not calling transform directly), appears to affect the type-checking. We need to look into this.
    * The usage of this.type is also "suspect", since we are really casting in a way that can't be caught out at runtime..
    *
    * See Silver issue
    */
  def transform(pre: PartialFunction[Node, Node] = PartialFunction.empty)
               (recursive: Node => Boolean = !pre.isDefinedAt(_),
                post: PartialFunction[Node, Node] = PartialFunction.empty)
  : this.type =
    Transformer.transform[this.type](this, pre)(recursive, post)

  override def toString = PrettyPrinter.pretty(this)
}

/**
 * A local variable declaration.  Note that this is not a statement, as local variables do not
 * have to be declared (but if a where clause is needed, then
 * [[viper.carbon.boogie.LocalVarWhereDecl]] can be used.
 */
case class LocalVarDecl(name: Identifier, typ: Type, where: Option[Exp] = None) extends Node {
  def l = LocalVar(name, typ)
}

/**
 * An identifier of a Boogie program.  Creators of identifiers must make sure that
 * names from the same category are unique in any given program (otherwise, the two
 * identifiers refer to the same thing), but the pretty-printer then tries to use
 * the name `preferredName` if possible.
 */
trait Identifier {
  def name: String
  def namespace: Namespace
  def preferredName = name
  override def equals(o: Any) = {
    o match {
      case Identifier(n, ns) => n == name && ns == namespace
      case _ => false
    }
  }
  override def hashCode = List(name, namespace).hashCode
}
case object Identifier {
  def apply(n: String)(implicit ns: Namespace): Identifier =
    new Identifier {
      val name = n
      val namespace = ns
    }
  def unapply(i: Identifier) = Some(i.name, i.namespace)
}
/**
 * A namespace to make it easier to avoid duplicated entities in the Boogie output.
  *
  * @param name The name of the namespace; only used for debugging purposes.
 * @param id The ID of this namespace; used to identify the namespace.
 */
case class Namespace(name: String, id: Int)


// --- Types

sealed trait Type extends Node {
  def freeTypeVars: Seq[TypeVar] = Nil
}
sealed trait BuiltInType extends Type
case object Int extends BuiltInType
case object Bool extends BuiltInType
case object Real extends BuiltInType
case class TypeVar(name: String) extends Type {
  override def freeTypeVars: Seq[TypeVar] = Seq(this)
}
case class NamedType(name: String, typVars: Seq[Type] = Nil) extends Type {
  override def freeTypeVars: Seq[TypeVar] = typVars flatMap (_.freeTypeVars)
}
case class MapType(domains: Seq[Type], range: Type, typVars: Seq[TypeVar] = Nil) extends BuiltInType {
  override def freeTypeVars: Seq[TypeVar] = typVars
}

// --- Expressions

sealed trait Exp extends Node with PrettyExpression {
  def ===(other: Exp) = BinExp(this, EqCmp, other)
  def !==(other: Exp) = BinExp(this, NeCmp, other)
  def :=(rhs: Exp) = Assign(this, rhs)
  def +=(rhs: Exp) = Assign(this, this + rhs)
  def -=(rhs: Exp) = Assign(this, this - rhs)
  def +(other: Exp) = BinExp(this, Add, other)
  def -(other: Exp) = BinExp(this, Sub, other)
  def *(other: Exp) = BinExp(this, Mul, other)
  def /(other: Exp) = BinExp(this, Div, other)
  def div(other: Exp) = BinExp(this, IntDiv, other)
  def %(other: Exp) = BinExp(this, Mod, other)
  def <(other: Exp) = BinExp(this, LtCmp, other)
  def >(other: Exp) = BinExp(this, GtCmp, other)
  def <=(other: Exp) = BinExp(this, LeCmp, other)
  def >=(other: Exp) = BinExp(this, GeCmp, other)
  def neg = UnExp(Minus, this)
  def &&(other: Exp) = BinExp(this, And, other)
  def ||(other: Exp) = BinExp(this, Or, other)
  def ==>(other: Exp) = BinExp(this, Implies, other)
  def <==>(other: Exp) = BinExp(this, Equiv, other)
  def forall(vars: Seq[LocalVarDecl], triggers: Seq[Trigger]) =
    Forall(vars, triggers, this)
  def exists(vars: Seq[LocalVarDecl]) =
    Exists(vars, this)
  def not = UnExp(Not, this)
  def thn(thn: Exp) = PartialCondExp(this, thn)
  def transform(f: PartialFunction[Exp, Option[Exp]]) = Nodes.transform(this, f)
}

object All {
  def apply(exps: Seq[Exp]): Exp = exps match {
    case Nil => TrueLit()
    case x +: Nil => x
    case x +: xs => BinExp(x, And, All(xs))
  }
}

case class PartialCondExp(cond: Exp, thn: Exp) {
  def els(els: Exp) = CondExp(cond, thn, els)
}

case class IntLit(i: BigInt) extends Exp
case class RealLit(d: Double) extends Exp
case class TrueLit() extends BoolLit(true)
case class FalseLit() extends BoolLit(false)
sealed abstract class BoolLit(val b: Boolean) extends Exp
object BoolLit {
  def unapply(b: BoolLit) = Some(b.b)
  def apply(b: Boolean) = if (b) TrueLit() else FalseLit()
}
case class RealConv(e: Exp) extends Exp

case class BinExp(left: Exp, binop: BinOp, right: Exp) extends Exp with PrettyBinaryExpression {
  lazy val op = binop.name
  lazy val priority = binop.priority
  lazy val fixity = binop.fixity
}

case class UnExp(unop: UnOp, exp: Exp) extends Exp with PrettyUnaryExpression {
  lazy val op = unop.name
  lazy val priority = unop.priority
  lazy val fixity = unop.fixity
}

sealed abstract class BinOp(val name: String, val priority: Int, val fixity: Fixity)
sealed abstract class SumOp(override val name: String) extends BinOp(name, 16, Infix(LeftAssociative))
sealed abstract class RelOp(override val name: String) extends BinOp(name, 14, Infix(NonAssociative))
sealed abstract class ProdOp(override val name: String) extends BinOp(name, 18, Infix(LeftAssociative))

case object Add extends SumOp("+")
case object Sub extends SumOp("-")
case object Mul extends ProdOp("*")
case object IntDiv extends ProdOp("div")
case object Div extends ProdOp("/")
case object Mod extends ProdOp("mod")
case object LtCmp extends RelOp("<")
//case object LeCmp extends RelOp("?" or "<=") // removed non ASCII character alternative (can't display/edit)
case object LeCmp extends RelOp("<=") 
case object GtCmp extends RelOp(">")
case object GeCmp extends RelOp(">=")// removed non ASCII character alternative (can't display/edit)
case object EqCmp extends RelOp("==")
case object NeCmp extends RelOp("!=")// removed non ASCII character alternative (can't display/edit)

// Note: Boogie uses the same priority for 'and' and 'or'.
case object Or extends BinOp("||", 6, Infix(NonAssociative))// removed non ASCII character alternative (can't display/edit)
case object And extends BinOp("&&", 6, Infix(NonAssociative))// removed non ASCII character alternative (can't display/edit)
case object Implies extends BinOp("==>", 4, Infix(RightAssociative))// removed non ASCII character alternative (can't display/edit)
case object Equiv extends BinOp("<==>", 2, Infix(NonAssociative))// removed non ASCII character alternative (can't display/edit)

sealed abstract class UnOp(val name: String, val priority: Int, val fixity: Fixity)
case object Not extends UnOp("¬" or "!", 20, Prefix)
case object Minus extends UnOp("-", 20, Prefix)

sealed trait QuantifiedExp extends Exp {
  def vars: Seq[LocalVarDecl]
  def exp: Exp
}
case class Forall(vars: Seq[LocalVarDecl], triggers: Seq[Trigger], exp: Exp, typeVars: Seq[TypeVar] = Nil) extends QuantifiedExp
object MaybeForall {
  def apply(vars: Seq[LocalVarDecl], triggers: Seq[Trigger], exp: Exp) = {
    if (vars.isEmpty) exp
    else Forall(vars, triggers, exp)
  }
}
case class Exists(vars: Seq[LocalVarDecl], exp: Exp) extends QuantifiedExp
case class Trigger(exps: Seq[Exp]) extends Node

case class CondExp(cond: Exp, thn: Exp, els: Exp) extends Exp
case class Old(exp: Exp) extends Exp

//sealed abstract class Var(val name: Identifier, val typ: Type) extends Exp

sealed trait Var extends Exp {
  def name : Identifier
  def typ : Type
}

case class LocalVar(name: Identifier, typ: Type) extends Var
case class GlobalVar(name: Identifier, typ: Type) extends Var
case class Const(name: Identifier) extends Exp
// typ indicates the return type (needed to compute the free type variables)
// AS: We should refactor "name" here to be "id" or similar. Otherwise "fa.name" is confusingly similar to the (usually intended) "fa.name.name"
case class FuncApp(name: Identifier, args: Seq[Exp], typ: Type) extends Exp {
  var showReturnType = false // indicates that the return type should be explicitly pretty-printed (e.g. Seq#Empty() : Seq T)
}

case class MapSelect(map: Exp, idxs: Seq[Exp]) extends Exp

// --- Statements

sealed trait Stmt extends Node {
  /**
   * Returns a list of all actual statements contained in this statement.  That
   * is, all statements except `Seqn`, including statements in the body of loops, etc.
   */
  def children = Statements.children(this)

  /**
   * Returns a list of all undeclared local variables contained in this statement and
   * throws an exception if the same variable is used with different types.
   */
  def undeclLocalVars = Statements.undeclLocalVars(this)
}
case class Lbl(name: Identifier)
case class Goto(dests: Seq[Lbl]) extends Stmt
case class Label(lbl: Lbl) extends Stmt
case class Assume(exp: Exp) extends Stmt
case class AssertImpl(exp: Exp, error: VerificationError) extends Stmt {
  var id = AssertIds.next // Used for mapping errors in the output back to VerificationErrors
}
object Assert {
  def apply(exp: Exp, error: VerificationError) = {
    if (error == null) Statements.EmptyStmt
    else AssertImpl(exp, error)
  }
  def unapply(a: AssertImpl) = Some((a.exp, a.error))
}
object AssertIds {
  var id = 0
  def next = {
    id += 1
    id - 1
  }
}
case class Assign(lhs: Exp, rhs: Exp) extends Stmt
case class HavocImpl(vars: Seq[Var]) extends Stmt
object Havoc {
  def apply(vars: Seq[Var]) = {
    if (vars.isEmpty) Statements.EmptyStmt
    else HavocImpl(vars)
  }
}
case class If(cond: Exp, thn: Stmt, els: Stmt) extends Stmt
case class Seqn(stmts: Seq[Stmt]) extends Stmt
/** A non-deterministic if statement. */
case class NondetIf(thn: Stmt, els: Stmt = Statements.EmptyStmt) extends Stmt
/**
 * Something like a 'declaration' of a local variable that allows to specify a where
 * clause.  However, local variables do not need to be declared if no where clause
 * is needed, and 'declarations' might be omitted if the variable is not used.
 */
case class LocalVarWhereDecl(name: Identifier, where: Exp) extends Stmt
/** A single-line comment (s should not contain new-lines) */
case class Comment(s: String) extends Stmt
object MaybeComment {
  def apply(s: String, stmt: Stmt) = {
    if (stmt.optimize.children.isEmpty) Statements.EmptyStmt
    else Seqn(Comment(s) :: stmt.optimize :: Nil)
  }
}
/**
 * A comment block can be used to group together a sequence of statements that
 * belong together, as described by a comment.
 */
case class CommentBlock(s: String, stmt: Stmt) extends Stmt
object MaybeCommentBlock {
  def apply(s: String, stmt: Stmt) = {
    if (stmt.optimize.children.isEmpty) Statements.EmptyStmt
    else CommentBlock(s, stmt.optimize)
  }
}

/**
 * Only add a statement if something else is non-empty.
 */
object MaybeStmt {
  def apply(isEmpty: Stmt, maybe: Stmt): Stmt = {
    if (isEmpty.optimize.children.isEmpty) Statements.EmptyStmt
    else Seqn(Seq(isEmpty, maybe))
  }
}

// --- Declarations

case class Program(header: Seq[String], decls: Seq[Decl]) extends Node
sealed trait Decl extends Node
case class ConstDecl(name: Identifier, typ: Type, unique: Boolean = false) extends Decl
case class TypeDecl(t: NamedType) extends Decl
case class TypeAlias(name: NamedType, definition: Type) extends Decl
case class Func(name: Identifier, args: Seq[LocalVarDecl], typ: Type) extends Decl
case class Axiom(exp: Exp) extends Decl
case class GlobalVarDecl(name: Identifier, typ: Type) extends Decl
case class Procedure(name: Identifier, ins: Seq[LocalVarDecl], outs: Seq[LocalVarDecl], body: Stmt) extends Decl
/**
 * nLines determines the number of lines between declarations (1 being only a single new-line, i.e. no space).
 *
 * size = 1 means a normal comment
 * size = 2 means a normal comment surrounded by "// ------------" (above and below)
 * size = 3 means a normal comment surrounded by "// ============" (above and below)
 */
case class CommentedDecl(s: String, d: Seq[Decl], size: Int = 3, nLines: Int = 1) extends Decl
object MaybeCommentedDecl {
  def apply(s: String, d: Seq[Decl], size: Int = 3, nLines: Int = 1) = {
    if (d.isEmpty) Nil
    else CommentedDecl(s, d, size, nLines) :: Nil
  }
}
case class DeclComment(s: String) extends Decl
case class LiteralDecl(boogieString: String) extends Decl
