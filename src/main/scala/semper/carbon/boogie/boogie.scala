
package semper.carbon.boogie

import org.kiama.output._
import UnicodeString.string2unicodestring
import semper.sil.verifier.VerificationError

/** The root of the Boogie AST. */
sealed trait Node {
  /**
   * Returns a list of all direct sub-nodes of this node.
   */
  def subnodes = Nodes.subnodes(this)

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
  def visit(f: Node => Unit) {
    Visitor.visit(this)(f)
  }

  /**
   * Applies the function `f1` to the AST node, then visits all subnodes,
   * and finally calls `f2` to the AST node.
   */
  def visit(n: Node, f1: Node => Unit, f2: Node => Unit) {
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

  override def toString = PrettyPrinter.pretty(this)
}

/**
 * A local variable declaration.  Note that this is not a statement, as local variables do not
 * have to be declared.
 */
case class LocalVarDecl(name: Identifier, typ: Type, where: Option[Exp] = None) extends Node

/**
 * An identifier of a Boogie program.  Creators of identifiers must make sure that
 * names from the same category are unique in any given program (otherwise, the two
 * identifiers refer to the same thing), but the pretty-printer then tries to use
 * the name `preferredName` if possible.
 */
case class Identifier(name: String, namespace: Namespace) {
  def preferredName = name
}
case object Identifier {
  def apply(name: String)(implicit namespace: Namespace): Identifier = Identifier(name, namespace)
}
/**
 * A namespace to make it easier to avoid duplicated entities in the Boogie output.
 * @param name The name of the namespace; only used for debugging purposes.
 * @param id The ID of this namespace; used to identify the namespace.
 * @param typ Which of the different categories for Boogie identifiers does
 *            this namespace fall into.
 */
case class Namespace(name: String, id: Int, typ: NamespaceType.Value = NamespaceType.Variables)
/**
 * Type of a namespace (see Boogie manual on identifiers).
 */
object NamespaceType extends Enumeration {
  type NamespaceType = Value
  val Variables, Procedures, Types, Functions, Attributes = Value
}


// --- Types

sealed trait Type extends Node
sealed trait BuiltInType extends Type
case object Int extends BuiltInType
case object Bool extends BuiltInType
case object Real extends BuiltInType
case class TypeVar(name: String) extends Type
case class NamedType(name: String, typVars: Seq[Type] = Nil) extends Type
case class MapType(domains: Seq[Type], range: Type, typVars: Seq[TypeVar] = Nil) extends BuiltInType

// --- Expressions

sealed trait Exp extends Node with PrettyExpression {
  def ===(other: Exp) = BinExp(this, EqCmp, other)
  def !==(other: Exp) = BinExp(this, NeCmp, other)
  def :=(rhs: Exp) = Assign(this, rhs)
  def +(other: Exp) = BinExp(this, Add, other)
  def -(other: Exp) = BinExp(this, Sub, other)
  def *(other: Exp) = BinExp(this, Mul, other)
  def /(other: Exp) = BinExp(this, Div, other)
  def %(other: Exp) = BinExp(this, Mod, other)
  def <(other: Exp) = BinExp(this, LtCmp, other)
  def >(other: Exp) = BinExp(this, GtCmp, other)
  def <=(other: Exp) = BinExp(this, LeCmp, other)
  def >=(other: Exp) = BinExp(this, GeCmp, other)
  def neg = UnExp(Neg, this)
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
sealed abstract class SumOp(override val name: String) extends BinOp(name, 12, Infix(LeftAssoc))
sealed abstract class RelOp(override val name: String) extends BinOp(name, 11, Infix(LeftAssoc))
sealed abstract class ProdOp(override val name: String) extends BinOp(name, 13, Infix(LeftAssoc))

case object Add extends SumOp("+")
case object Sub extends SumOp("-")
case object Mul extends ProdOp("*")
case object Div extends ProdOp("/")
case object Mod extends ProdOp("%")
case object LtCmp extends RelOp("<")
case object LeCmp extends RelOp("≤" or "<=")
case object GtCmp extends RelOp(">")
case object GeCmp extends RelOp("≥" or ">=")
case object EqCmp extends RelOp("==")
case object NeCmp extends RelOp("≠" or "!=")

case object Or extends BinOp("∨" or "||", 3, Infix(LeftAssoc))
case object And extends BinOp("∧" or "&&", 3, Infix(LeftAssoc))
// Note: Boogie uses the same priority for 'and' and 'or'.
case object Implies extends BinOp("⇒" or "==>", 4, Infix(RightAssoc))
case object Equiv extends BinOp("⇔" or "<==>", 5, Infix(NonAssoc))

sealed abstract class UnOp(val name: String, val priority: Int, val fixity: Fixity)
case object Not extends UnOp("¬" or "!", 1, Prefix)
case object Neg extends UnOp("-", 1, Prefix)

sealed trait QuantifiedExp extends Exp {
  def vars: Seq[LocalVarDecl]
  def exp: Exp
}
case class Forall(vars: Seq[LocalVarDecl], triggers: Seq[Trigger], exp: Exp) extends QuantifiedExp
case class Exists(vars: Seq[LocalVarDecl], exp: Exp) extends QuantifiedExp
case class Trigger(exps: Seq[Exp]) extends Node

case class CondExp(cond: Exp, thn: Exp, els: Exp) extends Exp
case class Old(exp: Exp) extends Exp

case class LocalVar(name: Identifier, typ: Type) extends Exp
case class FuncApp(name: Identifier, args: Seq[Exp]) extends Exp
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
case class Assert(exp: Exp, error: VerificationError) extends Stmt {
  var id = AssertIds.next // Used for mapping errors in the output back to VerificationErrors
}
object AssertIds {
  var id = 0
  def next = {
    id += 1
    id - 1
  }
}
case class Assign(lhs: Exp, rhs: Exp) extends Stmt
case class Havoc(vars: Seq[LocalVar]) extends Stmt
case class If(cond: Exp, thn: Stmt, els: Stmt) extends Stmt
case class Seqn(stmts: Seq[Stmt]) extends Stmt
case class NondetIf(thn: Stmt, els: Stmt) extends Stmt
/** A single-line comment (s should not contain new-lines) */
case class Comment(s: String) extends Stmt
/**
 * A comment block can be used to group together a sequence of statements that
 * belong together, as described by a comment.
 */
case class CommentBlock(s: String, stmt: Stmt) extends Stmt

// --- Declarations

case class Program(header: Seq[String], decls: Seq[Decl]) extends Node
sealed trait Decl extends Node
case class Const(name: Identifier, typ: Type) extends Decl
case class TypeDecl(t: NamedType) extends Decl
case class TypeAlias(name: NamedType, definition: Type) extends Decl
case class Func(name: Identifier, args: Seq[LocalVarDecl], typ: Type) extends Decl
case class Axiom(exp: Exp) extends Decl
case class GlobalVarDecl(name: Identifier, typ: Type) extends Decl
case class Procedure(name: Identifier, ins: Seq[LocalVarDecl], outs: Seq[LocalVarDecl], body: Stmt) extends Decl
case class CommentedDecl(s: String, d: Seq[Decl]) extends Decl
