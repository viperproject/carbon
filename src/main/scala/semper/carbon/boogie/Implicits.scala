package semper.carbon.boogie

import language.implicitConversions

/**
 * A collection of implicits for working with the Boogie AST.
 *
 * @author Stefan Heule
 */
object Implicits {
  implicit def lift[T](t: T): Seq[T] = Seq(t)
  implicit def liftStmt(ss: Seq[Stmt])= Seqn(ss)
}
