
package semper.carbon.boogie

import org.kiama.output._
import UnicodeString.lift
import language.implicitConversions

object Implicits {
  implicit def lift[A](x: A): Seq[A] = Seq(x)
}

/** The root of the Boogie AST. */
sealed trait Node {
  override def toString = PrettyPrinter.pretty(this)
}

/** A local variable declaration.  Note that this is not a statement, as local variables do not have to be declared. */
case class LocalVarDecl(name: String, typ: Type, where: Option[Exp] = None) extends Node


// --- Types

sealed trait Type extends Node
sealed trait BuiltInType extends Type
case object Int extends BuiltInType
case object Bool extends BuiltInType
case object Real extends BuiltInType
case class TypeVar(name: String) extends Type
case class Map(domains: Seq[Type], range: Type, typArgs: Seq[TypeVar]) extends BuiltInType
case class NamedType(name: String, typArgs: Seq[TypeVar]) extends Type

// --- Expressions

sealed trait Exp extends Node with PrettyExpression {
  def ===(other: MaybeInt) = BinExp(this, EqCmp, other)
  def !==(other: MaybeInt) = BinExp(this, NeCmp, other)
}

/** A common trait for expressions that one can assign a new value to. */
sealed trait Lhs extends Exp {
  def :=(rhs: Exp) = Assign(this, rhs)
}

/** A trait for expressions that might be of type int. */
sealed trait MaybeInt extends Exp {
  def +(other: MaybeInt) = BinExp(this, Add, other)
  def -(other: MaybeInt) = BinExp(this, Sub, other)
  def *(other: MaybeInt) = BinExp(this, Mul, other)
  def /(other: MaybeInt) = BinExp(this, Div, other)
  def %(other: MaybeInt) = BinExp(this, Mod, other)
  def <(other: MaybeInt) = BinExp(this, LtCmp, other)
  def >(other: MaybeInt) = BinExp(this, GtCmp, other)
  def <=(other: MaybeInt) = BinExp(this, LeCmp, other)
  def >=(other: MaybeInt) = BinExp(this, GeCmp, other)
}

/** A trait for expressions that might be of type bool. */
sealed trait MaybeBool extends Exp {
  def &&(other: MaybeInt) = BinExp(this, And, other)
  def ||(other: MaybeInt) = BinExp(this, Or, other)
  def ==>(other: MaybeInt) = BinExp(this, Implies, other)
  def <==>(other: MaybeInt) = BinExp(this, Equiv, other)
  def forall(vars: Seq[LocalVarDecl], triggers: Seq[Trigger]) =
    Forall(vars, triggers, this)
  def exists(vars: Seq[LocalVarDecl]) =
    Exists(vars, this)
}

case class IntLit(i: BigInt) extends Exp with MaybeInt
case class RealLit(d: Double) extends Exp
case class TrueLit() extends BoolLit(true)
case class FalseLit() extends BoolLit(false)
sealed abstract class BoolLit(val b: Boolean) extends Exp with MaybeBool
object BoolLit {
  def unapply(b: BoolLit) = Some(b.b)
}

case class BinExp(left: Exp, binop: BinOp, right: Exp) extends Exp with PrettyBinaryExpression with MaybeInt with MaybeBool {
  lazy val op = binop.name
  lazy val priority = binop.priority
  lazy val fixity = binop.fixity
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
case object And extends BinOp("∧" or "&&", 3, Infix(LeftAssoc)) // Note: Boogie uses the same priority for 'and' and 'or'.
case object Implies extends BinOp("⇒" or "==>", 4, Infix(RightAssoc))
case object Equiv extends BinOp("⇔" or "<==>", 5, Infix(NonAssoc))

sealed abstract class UnOp(val name: String, val priority: Int, val fixity: Fixity)
case object Not extends UnOp("¬" or "!", 1, Prefix)
case object Neg extends UnOp("-", 1, Prefix)

sealed trait QuantifiedExp extends Exp with MaybeBool {
  def vars: Seq[LocalVarDecl]
  def exp: Exp
}
case class Forall(vars: Seq[LocalVarDecl], triggers: Seq[Trigger], exp: Exp) extends QuantifiedExp
case class Exists(vars: Seq[LocalVarDecl], exp: Exp) extends QuantifiedExp
case class Trigger(exps: Seq[Exp]) extends Node

case class LocalVar(name: String, typ: Type) extends Exp with Lhs with MaybeInt with MaybeBool
case class FuncApp(name: String, args: Seq[Exp]) extends Exp with MaybeInt with MaybeBool
case class MapSelect(map: Exp, idxs: Seq[Exp]) extends Exp with Lhs with MaybeInt with MaybeBool

// --- Statements

sealed trait Stmt extends Node
case class Assume(exp: Exp) extends Stmt
case class Assert(exp: Exp) extends Stmt
case class Assign(lhs: Lhs, rhs: Exp) extends Stmt

// --- Declarations

case class Program(decls: Seq[Decl]) extends Node
sealed trait Decl extends Node
case class TypeDecl(name: String) extends Decl
case class Const(name: String, typ: Type) extends Decl
case class Func(name: String, args: Seq[LocalVarDecl], typ: Type, typArgs: Seq[TypeVar]) extends Decl
case class Axiom(exp: Exp) extends Decl
case class GlobalVarDecl(name: String, typ: Type) extends Decl
case class Procedure(name: String, ins: Seq[LocalVarDecl], outs: Seq[LocalVarDecl], modifies: Seq[String], pres: Seq[Exp], posts: Seq[Exp], body: Stmt) extends Decl
