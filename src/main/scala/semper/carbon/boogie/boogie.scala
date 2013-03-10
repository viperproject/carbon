
package semper.carbon.boogie

import org.kiama.output._
import UnicodeString.string2unicodestring
import language.implicitConversions

object Implicits {
  implicit def lift[A](x: A): Seq[A] = Seq(x)
}

/** The root of the Boogie AST. */
sealed trait Node {
  override def toString = PrettyPrinter.pretty(this)
}

/** A local variable declaration.  Note that this is not a statement, as local variables do not have to be declared. */
case class LocalVarDecl(name: String, typ: Type, where: Option[MaybeBool] = None) extends Node

// --- Types

sealed trait Type extends Node
sealed trait BuiltInType extends Type
case object Int extends BuiltInType
case object Bool extends BuiltInType
case object Real extends BuiltInType
case class TypeVar(name: String) extends Type
case class MapType(domains: Seq[Type], range: Type, typVars: Seq[TypeVar] = Nil) extends BuiltInType

// --- Expressions

sealed trait Exp extends Node with PrettyExpression {
  def ===(other: Exp) = BinExp(this, EqCmp, other)
  def !==(other: Exp) = BinExp(this, NeCmp, other)
}

/** A common trait for expressions that one can assign a new value to. */
sealed trait Lhs extends Exp {
  def :=(rhs: Exp) = Assign(this, rhs)
}

/** A trait for expressions that might be of type int. */
sealed trait MaybeNum extends Exp {
  def +(other: MaybeNum) = BinExp(this, Add, other)
  def -(other: MaybeNum) = BinExp(this, Sub, other)
  def *(other: MaybeNum) = BinExp(this, Mul, other)
  def /(other: MaybeNum) = BinExp(this, Div, other)
  def %(other: MaybeNum) = BinExp(this, Mod, other)
  def <(other: MaybeNum) = BinExp(this, LtCmp, other)
  def >(other: MaybeNum) = BinExp(this, GtCmp, other)
  def <=(other: MaybeNum) = BinExp(this, LeCmp, other)
  def >=(other: MaybeNum) = BinExp(this, GeCmp, other)
  def neg = UnExp(Neg, this)
}

/** A trait for expressions that might be of type bool. */
sealed trait MaybeBool extends Exp {
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

case class IntLit(i: BigInt) extends MaybeNum
case class RealLit(d: Double) extends MaybeNum
case class TrueLit() extends BoolLit(true)
case class FalseLit() extends BoolLit(false)
sealed abstract class BoolLit(val b: Boolean) extends Exp with MaybeBool
object BoolLit {
  def unapply(b: BoolLit) = Some(b.b)
  def apply(b: Boolean) = if (b) TrueLit() else FalseLit()
}

case class BinExp(left: Exp, binop: BinOp, right: Exp) extends Exp with PrettyBinaryExpression with MaybeNum with MaybeBool {
  lazy val op = binop.name
  lazy val priority = binop.priority
  lazy val fixity = binop.fixity
}

case class UnExp(unop: UnOp, exp: Exp) extends Exp with PrettyUnaryExpression with MaybeNum with MaybeBool {
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

sealed trait QuantifiedExp extends Exp with MaybeBool {
  def vars: Seq[LocalVarDecl]
  def exp: Exp
}
case class Forall(vars: Seq[LocalVarDecl], triggers: Seq[Trigger], exp: MaybeBool) extends QuantifiedExp
case class Exists(vars: Seq[LocalVarDecl], exp: Exp) extends QuantifiedExp
case class Trigger(exps: Seq[Exp]) extends Node

case class CondExp(cond: Exp, thn: Exp, els: Exp) extends MaybeBool
case class Old(exp: Exp) extends MaybeNum with MaybeBool

case class LocalVar(name: String, typ: Type) extends Lhs with MaybeNum with MaybeBool
case class FuncApp(name: String, args: Seq[Exp]) extends MaybeNum with MaybeBool
case class MapSelect(map: Exp, idxs: Seq[Exp]) extends Lhs with MaybeNum with MaybeBool

// --- Statements

sealed trait Stmt extends Node {
  /**
   * Returns a list of all actual statements contained in this statement.  That
   * is, all statements except `Seqn`, including statements in both branches of
   * conditionals.
   */
  def children: Seq[Stmt] = this match {
    case If(_, thn, els) => Seq(this, thn, els)
    case NondetIf(thn, els) => Seq(this, thn, els)
    case _ => Seq(this)
  }
}
case class Lbl(name: String)
case class Goto(dests: Seq[Lbl]) extends Stmt
case class Label(lbl: Lbl) extends Stmt
case class Assume(exp: Exp) extends Stmt
case class Assert(exp: Exp) extends Stmt
case class Assign(lhs: Lhs, rhs: Exp) extends Stmt
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

case class Program(decls: Seq[Decl]) extends Node
sealed trait Decl extends Node
case class Const(name: String, typ: Type) extends Decl
case class Func(name: String, args: Seq[LocalVarDecl], typ: Type) extends Decl
case class Axiom(exp: Exp) extends Decl
case class GlobalVarDecl(name: String, typ: Type) extends Decl
case class Procedure(name: String, ins: Seq[LocalVarDecl], outs: Seq[LocalVarDecl], body: Stmt) extends Decl
