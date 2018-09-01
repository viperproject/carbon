package viper.carbon.modules.impls

import viper.carbon.boogie._
import viper.carbon.modules._
import viper.carbon.verifier.Verifier
import viper.silver.{ast => sil}

import scala.util.parsing.combinator.token.StdTokens

class DefaultComprehensionModule(val verifier: Verifier) extends ComprehensionModule {

  import verifier._
  import expModule._
  import mainModule._
  import typeModule._
  import heapModule._

  implicit val compNamespace: Namespace = verifier.freshNamespace("comp")

  override def name: String = "Comprehension Module"

  /**
    * A case class for describing a comprehension instance.
    * It holds the name of the comprehension, the original Ast, which was responsible for generating this instance,
    * the boogie local variable declarations describing the arguments of the comprehension,
    * the body of the comprehension, i.e. a expression of the form e.v, describing what the comprehension ranges over,
    * the name of the binary operator, the boogie unit expression and the type of the comprehension.
    */
  case class Comprehension(name: String, originalExp: sil.Comp, varDecls: Seq[LocalVarDecl], body: Exp, binary: String, unit: Exp, typ: Type) {
    /**
      * The boogie function declaration of the filtering function of this comprehension.
      * It has the following signature: filtering_compName(a, f)
      * where a denotes the comprehension argument(s) and f denotes the filter
      */
    val filtering = Func(Identifier("filtering_"+name), varDecls :+ LocalVarDecl(Identifier("f"), filterType), Bool)
    /**
      * A list of local variables emerging from the local variable declarations of this comprehension.
      */
    val localVars = varDecls map {v => v.l}
    /**
      * Applies the filtering function for the specified filter and [[localVars]].
      * This means that this method is a shortcut for application of the comprehension specific filtering function,
      * in a way that the comprehension specific arguments don't need to be specified, but only the filter.
      */
    def applyFiltering(filter: Exp) = filtering.apply(localVars :+ filter)
  }

  /**
    * A class for describing a filter instance.
    * It holds the name of the filter, the original Ast, describing the filter,
    * the filtering condition as a boogie expression,
    * the global variable declaration defining the boogie instances of the filter and the comprehension, this filter
    * belongs to.
    */
  case class Filter(name: String, originalExp: sil.Filter, exp: Exp, varDecl: GlobalVarDecl, comp: Comprehension)

  /**
    * All comprehensions occurring in the program
    */
  private val comprehensions: Seq[Comprehension] = Seq()

  /**
    * All filters occurring in the program
    */
  private val filters: Seq[Filter] = Seq()

  /**
    * All the filters translated in this statement so far.
    */
  private var newFilters: Seq[Filter] = Seq()

  /**
    * Indicates whether the module is ready for translation, i.e. the [[startNextStatement]] method was called.
    */
  private var readyForTranslation = false

  /**
    * The boogie filter type
    */
  val filterType = NamedType("Filter")

  /**
    * The function declaration of the userCreated function
    */
  val userCreated = Func(Identifier("userCreated"), Seq(LocalVarDecl(Identifier("f"), filterType)), Bool)

  override def translateComp(e: sil.Exp): Exp = {
    if (!readyForTranslation) {
      throw new UnexpectedCompExprException()
    }
    e match {
      case c@sil.Comp(vars, filter, body, binary, unit) =>
        // retrieve the comprehension object for the comprehension call
        val comp: Comprehension = detectComp(c) match {
          case None =>
            // create a new comprehension instance
            val name = "comp_" + binary + "_" + comprehensions.size
            // translate and sort local var declarations according to their name for comparison
            val localVars = vars map translateLocalVarDecl
            val out = Comprehension(name, c, localVars, translateExp(body), binary, translateExp(unit),
              translateType(unit.typ))
            // add the instance to the occurred ones
            comprehensions :+ out
            out
          case Some(obj) =>
            obj
        }
        FuncApp(Identifier(comp.name), Seq(translateFilter(filter, comp)), comp.typ)
    }
  }

  /**
    * Detects which comprehension of the currently available comprehensions (in [[comprehensions]]) is called by the
    * expression.
    *
    * @param exp The call to a comprehension
    * @return The comprehension used in the call, wrapped inside Some, or None, if there is no instance of the called
    *         comprehension yet (a new instance has to be created).
    */
  def detectComp(exp: sil.Comp): Option[Comprehension] = {
    // the output of the function, default is none
    var out: Option[Comprehension] = None
    // sort the variable list of exp
    val varList = exp.variables sortBy {v => v.name}
    comprehensions foreach { compare =>
      // compare for syntactic equivalence of the original expressions, but without comparing the filter
      // this means, look, whether the expression references the already known comprehension compObj

      // sort the val list of the current comprehension object for comparison
      val compareVarList = compare.originalExp.variables sortBy {v => v.name}
      if (varList == compareVarList &&
        exp.body == compare.originalExp.body &&
        exp.unit == compare.originalExp.unit &&
        exp.binary == compare.originalExp.binary) {
        out = Some(compare)
      }
    }
    out
  }

  /**
    * Translates a filter, i.e. generate a new filter instance and enlist it in [[filters]], as well as in [[newFilters]],
    * then return a variable representing the filter
    */
  def translateFilter(f: sil.Filter, c: Comprehension): Exp = {
    val name = "filter_" + filters.size
    val varDecl = GlobalVarDecl(Identifier(name), filterType)
    val obj = Filter(name, f, translateExp(f.exp), varDecl, c)
    filters :+ obj
    varDecl.g
  }

  override def startNextStatement() = {
    if (!readyForTranslation) {
      throw new UnexpectedStmtStartException()
    }
    readyForTranslation = true
    newFilters = Seq()
  }

  override def canTranslateComprehension = readyForTranslation

  override def filterPreamble() = {
    readyForTranslation = false
    // create the axiomatizations for every filter
    newFilters map { f =>
      val filtering = f.comp.filtering
      val filteringArgs: Seq[Exp] = filtering.args map {a => a.l}
      val filteringApp = FuncApp(filtering.name, filteringArgs, filtering.typ)
      val trigger = Trigger(Seq(filteringApp))
      // the axiomatization of the filter in terms of its filtering condition
      Forall(f.comp.filtering.args, Seq(trigger), filteringApp <==> f.exp) &&
      // the assumption of the userCreated function for the filter
      FuncApp(userCreated.name, Seq(f.varDecl.g), userCreated.typ)
    }
  }

  override def filterPreambleIdentifiers(): Seq[Identifier] = {
    newFilters map { f =>
      f.varDecl.name
    }
  }

  override def preamble: Seq[Decl] = {
    val out: Seq[Decl] = Seq()

    // generate comprehension independent axioms and declarations

    // filter type declaration
    val filterTypeDecl = TypeDecl(filterType)

    // generate filter generating function declarations
    val minus = Func(
      Identifier("minus"),
      Seq(LocalVarDecl(Identifier("f1"), filterType), LocalVarDecl(Identifier("f2"), filterType)),
      filterType
    )
    val intersect = Func(
      Identifier("intersect"),
      Seq(LocalVarDecl(Identifier("f1"), filterType), LocalVarDecl(Identifier("f2"), filterType)),
      filterType
    )
    val union = Func(
      Identifier("union"),
      Seq(LocalVarDecl(Identifier("f1"), filterType), LocalVarDecl(Identifier("f2"), filterType)),
      filterType
    )
    val narrow = Func(
      Identifier("narrow"),
      Seq(LocalVarDecl(Identifier("f"), filterType), LocalVarDecl(Identifier("r"), refType)),
      filterType
    )
    val filterGeneratingFunDecl = CommentedDecl("Declaration of filter generating functions", Seq(minus, intersect, union, narrow), 1)

    // generate filter property function declarations
    val empty = Func(
      Identifier("empty"),
      Seq(LocalVarDecl(Identifier("f"), filterType)),
      Bool
    )
    val subfilter = Func(
      Identifier("subfilter"),
      Seq(LocalVarDecl(Identifier("f1"), filterType), LocalVarDecl(Identifier("f2"), filterType)),
      Bool
    )
    val equivalent = Func(
      Identifier("equivalent"),
      Seq(LocalVarDecl(Identifier("f1"), filterType), LocalVarDecl(Identifier("f2"), filterType)),
      Bool
    )
    val filterPropertyFunDecl = CommentedDecl("Declaration of filter property functions", Seq(empty, subfilter, equivalent), 1)

    out :+ CommentedDecl("Comprehension independent declarations", Seq(filterTypeDecl, filterGeneratingFunDecl, filterPropertyFunDecl), 2)


    // generate the axiomatizations of the different comprehensions
    comprehensions foreach { c =>
      // practical constants for avoiding boilerplate code
      val fId = Identifier("f")
      val f1Id = Identifier("f1")
      val f2Id = Identifier("f2")
      val rId = Identifier("r")
      val fDecl = LocalVarDecl(fId, filterType)
      val f1Decl = LocalVarDecl(f1Id, filterType)
      val f2Decl = LocalVarDecl(f2Id, filterType)
      val rDecl = LocalVarDecl(rId, refType)
      val f = fDecl.l
      val f1 = f1Decl.l
      val f2 = f2Decl.l
      val r = rDecl.l
      // generate filtering axioms
      val filtering = c.filtering
      val minusAxiom = c.applyFiltering(minus.apply(Seq(f1, f2))) <==>
        (c.applyFiltering(f1) &&  c.applyFiltering(f2).not) forall (
        Seq(f1Decl, f2Decl) ++ c.varDecls,
        Seq(Trigger(Seq(c.applyFiltering(minus.apply(Seq(f1, f2))))))
      )
      val intersectAxiom = c.applyFiltering(intersect.apply(Seq(f1, f2))) <==>
        (c.applyFiltering(f1) &&  c.applyFiltering(f2)) forall (
        Seq(f1Decl, f2Decl) ++ c.varDecls,
        Seq(Trigger(Seq(c.applyFiltering(intersect.apply(Seq(f1, f2))))))
      )
      val unionAxiom = c.applyFiltering(union.apply(Seq(f1, f2))) <==>
        (c.applyFiltering(f1) ||  c.applyFiltering(f2)) forall (
        Seq(f1Decl, f2Decl) ++ c.varDecls,
        Seq(Trigger(Seq(c.applyFiltering(union.apply(Seq(f1, f2))))))
      )
      val narrowAxiom = c.applyFiltering(narrow.apply(Seq(f, r))) <==>
        (c.applyFiltering(f) && (c.body !== )


      val axioms = Seq(
        CommentedDecl("Declaration and axiomatization of filtering function", filterAxioms, 1)
      )
      out :+ CommentedDecl("Axiomatization of comprehension " + c.name, axioms, 2)
    }
    // generate the filter variables
    val filterDeclarations = filters map { f =>
      f.varDecl
    }
    out :+ CommentedDecl("Translation of filter declarations", filterDeclarations, 2)
    out
  }
}
