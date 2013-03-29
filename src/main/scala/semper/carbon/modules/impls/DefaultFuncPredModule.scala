package semper.carbon.modules.impls

import semper.carbon.modules._
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.Verifier
import semper.carbon.boogie.Implicits._

/**
 * The default implementation of a [[semper.carbon.modules.FuncPredModule]].
 *
 * @author Stefan Heule
 */
class DefaultFuncPredModule(val verifier: Verifier) extends FuncPredModule {
  def name = "Function and predicate module"

  import verifier._
  import typeModule._

  implicit val fpNamespace = verifier.freshNamespace("funcpred")

  override def translateFunction(f: sil.Function): Seq[Decl] = {
    val func = Func(Identifier(f.name), Nil, translateType(f.typ))
    val limitedFunc = Func(Identifier(f.name + "#limited"), Nil, translateType(f.typ))
    CommentedDecl(s"Translation of function ${f.name}",
      func ::
        limitedFunc ::
        Nil
    )
  }

  override def translatePredicate(p: sil.Predicate): Seq[Decl] = {
    Seq()
  }
}
