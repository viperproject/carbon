
package semper.carbon.boogie

import org.kiama.output._
import UnicodeString.lift

/** The root of the Boogie AST. */
sealed trait Node {
  override def toString = PrettyPrinter.pretty(this)
}
case class LocalVarDecl(name: String, typ: Type) extends Node

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

sealed trait Exp extends Node with PrettyExpression

case class IntLit(i: BigInt) extends Exp
case class RealLit(d: Double) extends Exp
case class TrueLit() extends BoolLit(true)
case class FalseLit() extends BoolLit(false)
sealed abstract class BoolLit(val b: Boolean) extends Exp
object BoolLit {
  def unapply(b: BoolLit) = Some(b.b)
}

case class BinExp(left: Exp, binop: BinOp, right: Exp) extends Exp with PrettyBinaryExpression {
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

sealed trait QuantifiedExp extends Exp {
  def vars: Seq[LocalVarDecl]
  def exp: Exp
  def triggers: Seq[Trigger]
}
case class Forall(vars: Seq[LocalVarDecl], triggers: Seq[Trigger], exp: Exp) extends QuantifiedExp
case class Exists(vars: Seq[LocalVarDecl], triggers: Seq[Trigger], exp: Exp) extends QuantifiedExp
case class Trigger(exps: Seq[Exp]) extends Node

case class LocalVar(name: String, typ: Type) extends Exp

// --- Statements

sealed trait Stmt extends Node


// --- Declarations

case class Program(decls: Seq[Decl]) extends Node
sealed trait Decl extends Node
case class TypeDecl(name: String) extends Decl
case class Const(name: String, typ: Type) extends Decl
case class Func(name: String, args: Seq[LocalVarDecl], typ: Type, typArgs: Seq[TypeVar]) extends Decl
case class Axiom(exp: Exp) extends Decl
case class GlobalVarDecl(name: String, typ: Type) extends Decl
case class Procedure(name: String, ins: Seq[LocalVarDecl], outs: Seq[LocalVarDecl], modifies: Seq[String], pres: Seq[Exp], posts: Seq[Exp], body: Stmt) extends Decl
