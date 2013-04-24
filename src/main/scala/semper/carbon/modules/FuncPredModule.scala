package semper.carbon.modules

import semper.sil.{ast => sil}
import semper.carbon.boogie.{Stmt, Decl, Exp}

/**
 * A module for translating functions and predicates.
 *
 * @author Stefan Heule
 */
trait FuncPredModule extends Module {
  def translateFunction(f: sil.Function): Seq[Decl]
  def translateFuncApp(fa: sil.FuncApp): Exp
  def translatePredicate(p: sil.Predicate): Seq[Decl]
  def assumeAllFunctionDefinitions: Stmt
}
