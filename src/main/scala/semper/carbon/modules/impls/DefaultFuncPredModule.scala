package semper.carbon.modules.impls

import semper.carbon.modules._
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.{Environment, Verifier}
import semper.carbon.boogie.Implicits._
import semper.sil.ast.utility._

/**
 * The default implementation of a [[semper.carbon.modules.FuncPredModule]].
 *
 * @author Stefan Heule
 */
class DefaultFuncPredModule(val verifier: Verifier) extends FuncPredModule {
  def name = "Function and predicate module"

  import verifier._
  import typeModule._
  import mainModule._
  import stateModule._
  import expModule._

  implicit val fpNamespace = verifier.freshNamespace("funcpred")

  lazy val heights = Functions.heights(verifier.program)
  private val assumeFunctionsAboveName = Identifier("AssumeFunctionsAbove")

  override def preamble = {
    val m = heights.values.max
    DeclComment("Function heights (higher height means its body is available earlier):") ++
      (for (i <- m to 0 by -1) yield {
        val fs = heights.toSeq filter (p => p._2 == i) map (_._1.name)
        DeclComment(s"- height $i: ${fs.mkString(", ")}")
      }) ++
    Func(assumeFunctionsAboveName, LocalVarDecl(Identifier("h"), Int), Bool)
  }

  override def translateFunction(f: sil.Function): Seq[Decl] = {
    env = Environment(verifier, f)
    val func = Func(Identifier(f.name), Nil, translateType(f.typ))
    val limitedFunc = Func(Identifier(f.name + "#limited"), Nil, translateType(f.typ))
    val res = CommentedDecl(s"Translation of function ${f.name}",
      func ++
        limitedFunc ++
        definitionalAxiom(f)
    )
    env = null
    res
  }

  override def translateFuncApp(fa: sil.FuncApp) = {
    translateFuncApp(fa.func, fa.args map translateExp, fa.typ)
  }
  def translateFuncApp(f: sil.Function, args: Seq[Exp], typ: sil.Type) = {
    FuncApp(Identifier(f.name), args, translateType(typ))
  }

  private def assumeFunctionsAbove(i: Int) =
    FuncApp(assumeFunctionsAboveName, IntLit(i), Bool)

  private def definitionalAxiom(f: sil.Function): Seq[Decl] = {
    val height = heights(f)
    val args = f.formalArgs map translateLocalVarDecl
    val fapp = translateFuncApp(f, args map (_.l), f.typ)
    Axiom(Forall(
      stateContributions ++ args,
      Trigger(Seq(staticGoodState, fapp)),
      (staticGoodState && assumeFunctionsAbove(height)) ==>
        (fapp === translateExp(f.exp))
    ))
  }

  override def translatePredicate(p: sil.Predicate): Seq[Decl] = {
    Seq()
  }
}
