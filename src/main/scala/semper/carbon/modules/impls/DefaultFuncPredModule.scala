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
  private val assumeFunctionsAbove: Const = Const(assumeFunctionsAboveName)

  override def preamble = {
    if (verifier.program.functions.isEmpty) Nil
    else {
      val m = heights.values.max
      DeclComment("Function heights (higher height means its body is available earlier):") ++
        (for (i <- m to 0 by -1) yield {
          val fs = heights.toSeq filter (p => p._2 == i) map (_._1.name)
          DeclComment(s"- height $i: ${fs.mkString(", ")}")
        }) ++
        ConstDecl(assumeFunctionsAboveName, Int)
    }
  }

  override def translateFunction(f: sil.Function): Seq[Decl] = {
    env = Environment(verifier, f)
    val args = heapModule.stateContributions ++ (f.formalArgs map translateLocalVarDecl)
    val typ = translateType(f.typ)
    val func = Func(Identifier(f.name), args, typ)
    val limitedFunc = Func(Identifier(f.name + "#limited"), args, typ)
    val res = CommentedDecl(s"Translation of function ${f.name}",
      CommentedDecl("Uninterpreted function definitions", func ++ limitedFunc, size = 1) ++
        CommentedDecl("Definitional axiom", definitionalAxiom(f), size = 1)
    , nLines = 2)
    env = null
    res
  }

  override def translateFuncApp(fa: sil.FuncApp) = {
    translateFuncApp(fa.func, heapModule.currentStateContributions ++ (fa.args map translateExp), fa.typ)
  }
  def translateFuncApp(f: sil.Function, args: Seq[Exp], typ: sil.Type) = {
    FuncApp(Identifier(f.name), args, translateType(typ))
  }

  private def assumeFunctionsAbove(i: Int): Exp =
    assumeFunctionsAbove > IntLit(i)

  def assumeAllFunctionDefinitions: Stmt = {
    if (verifier.program.functions.isEmpty) Nil
    else Assume(assumeFunctionsAbove(((heights map (_._2)).max) + 1))
  }

  private def definitionalAxiom(f: sil.Function): Seq[Decl] = {
    val height = heights(f)
    val heap = heapModule.stateContributions
    val args = f.formalArgs map translateLocalVarDecl
    val fapp = translateFuncApp(f, (heap ++ args) map (_.l), f.typ)
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
