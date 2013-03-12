package semper.carbon.verifier

import semper.sil.{ast => sil}
import semper.carbon.boogie.{Type, LocalVar}
import semper.sil.utility.NameGenerator

/**
 * An environment that defines mapping of variables during the translation.
 *
 * @author Stefan Heule
 */
case class Environment(verifier: Verifier, member: sil.Member) {

  private val names = NameGenerator()

  // register 'this'
  define(sil.ThisLit()())

  // register types from member
  member match {
    case l: sil.Location =>
      // none
    case sil.Method(name, args, returns, pres, posts, locals, body) =>
      for (v <- args ++ returns ++ locals) {
        define(v.localVar)
      }
    case f@sil.Function(name, args, pres, posts, exp) =>
      define(f.result)
      for (v <- args) {
        define(v.localVar)
      }
    case sil.Domain(name, functions, axioms, typVars) =>
  }

  /** The current mapping of variables. */
  private val currentMapping = collection.mutable.HashMap[sil.AbstractLocalVar, LocalVar]()

  /**
   * Returns the Boogie variable for a given SIL variable (it has to be defined first,
   * otherwise an error is thrown).
   */
  def get(variable: sil.LocalVar): LocalVar = {
    currentMapping.get(variable) match {
      case Some(t) => t
      case None => sys.error(s"Internal Error: variable $variable is not defined.")
    }
  }

  /**
   * Defines a local variable in this environment for a given (Boogie) type.
   */
  def define(variable: sil.AbstractLocalVar) {
    currentMapping.get(variable) match {
      case Some(t) =>
        sys.error(s"Internal Error: variable $variable is already defined.")
      case None =>
        val name = uniqueName(variable.name)
        // check for conflicts with any of the modules
        val conflict = verifier.allModules exists (_.definesGlobalVar(name))
        if (!conflict) {
          val bvar = LocalVar(name, verifier.typeModule.translateType(variable.typ))
          currentMapping.put(variable, bvar)
        } else {
          // try another name (the uniqueName method will use another one next time)
          define(variable)
        }
    }
  }

  /**
   * Takes a string and tries to produce a similar string that is not already used.
   */
  private def uniqueName(s: String): String = {
    names.createUniqueIdentifier(s)
  }
}
