package semper.carbon.verifier

import semper.sil.{ast => sil}
import semper.carbon.boogie.{BoogieNameGenerator, Identifier, LocalVar}
import semper.sil.utility.NameGenerator

/**
 * An environment that assigns unique names to SIL variables;  in SIL, loops can have
 * local variables and thus a method might have two declarations of a local variable
 * with the same name (in different loops).  In Boogie on the other hand, all variables
 * need to be unique.
 *
 * @author Stefan Heule
 */
case class Environment(verifier: Verifier, member: sil.Node) {

  private val names = new BoogieNameGenerator()

  /** The current mapping of variables. */
  private val currentMapping = collection.mutable.HashMap[sil.LocalVar, LocalVar]()

  // register types from member
  member match {
    case sil.Method(name, args, returns, pres, posts, locals, body) =>
      for (v <- args ++ returns ++ locals) {
        define(v.localVar)
      } 
    case f@sil.Function(name, args, typ, pres, posts, exp) =>
      for (v <- args) {
        define(v.localVar)
      }
    case sil.Predicate(name, args, body) =>
      for (v <- args) {
        define(v.localVar)
      }
    case f@sil.DomainFunc(name, args, typ, unique) =>
      for (v <- args) {
        define(v.localVar)
      }
    case _ =>
  }

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
   * Defines a local variable in this environment for a given SIL variable, and returns the corresponding
   * Boogie variable.
   */
  def define(variable: sil.LocalVar): LocalVar = {
    currentMapping.get(variable) match {
      case Some(t) =>
        sys.error(s"Internal Error: variable $variable is already defined.")
      case None =>
        val name = uniqueName(variable.name)
        val bvar = LocalVar(Identifier(name)(verifier.mainModule.silVarNamespace), verifier.typeModule.translateType(variable.typ))
        currentMapping.put(variable, bvar)
        bvar
    }
  }

  def undefine(variable: sil.LocalVar) {
    require(currentMapping.contains(variable))
    currentMapping.remove(variable)
  }

  /**
   * Takes a string and tries to produce a similar string that is not already used.
   */
  private def uniqueName(s: String): String = {
    names.createUniqueIdentifier(s)
  }
}
