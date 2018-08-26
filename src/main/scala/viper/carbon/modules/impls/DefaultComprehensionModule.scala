package viper.carbon.modules.impls

import viper.carbon.boogie.{Exp, FuncApp, Identifier}
import viper.carbon.modules._
import viper.carbon.verifier.Verifier
import viper.silver.{ast => sil}

class DefaultComprehensionModule(verifier: Verifier) extends ComprehensionModule {

  import verifier._
  import expModule._
  import mainModule._
  import typeModule._

  override def name: String = "Comprehension Module"

  override def translateComp(e: sil.Exp): Exp = {
    e match {
      case c@sil.Comp(vars, filter, body, binary, unit) =>
        // retrieve the comprehension object for the comprehension call
        val comp: Comprehension = detectComp(c) match {
          case None =>
            // create a new comprehension instance
            val name = "comp_" + binary + "_" + comprehensions.size
            val localVars = vars map translateLocalVarDecl
            val out = new Comprehension(name, localVars, translateExp(body), binary, translateExp(unit),
              translateType(unit.typ))
            // add the instance to the occurred ones
            comprehensions :+ out
            out
          case Some(c) =>
            c
        }
        FuncApp(Identifier(comp.name), Seq(translateFilter(filter)), comp.typ)
    }
  }

  override def detectComp(c: sil.Comp): Option[Comprehension] = {
    var comp: Option[Comprehension] = None
    val
    comprehensions foreach { c =>  }
    comp
  }

  override def translateFilter(f: sil.Filter): Exp = ???
}
