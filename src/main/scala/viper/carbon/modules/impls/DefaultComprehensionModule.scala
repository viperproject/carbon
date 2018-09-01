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
    * A class for describing a comprehension instance.
    */
  class Comprehension(val ast: sil.Comp) {
    /**
      * The name of the comprehension
      */
    val name = "comp_"+ast.binary+"_"+comprehensions.size
    /**
      * The boogie translated local variable declarations
      */
    val varDecls = {
      ast.variables map translateLocalVarDecl
    }
    /**
      * The boogie translated body of the comprehension
      */
    val body = translateExp(ast.body)
    /**
      * The boogie translated receiver of the body
      */
    val receiver = translateExp(ast.body.rcv)
    /**
      * The identifier for the binary operator
      */
    val binaryId = Identifier(ast.binary)
    /**
      * The boogie translated unit
      */
    val unit = translateExp(ast.unit)
    /**
      * The boogie type of the comprehension
      */
    val typ = translateType(ast.unit.typ)

    /**
      * Returns a boogie function application of the binary opertor
      */
    def binary(lhs: Exp, rhs: Exp) = FuncApp(binaryId, Seq(lhs, rhs), typ)

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
    */
  class Filter(val ast: sil.Filter, val comp: Comprehension) {
    /**
      * The name of the filter
      */
    val name = "filter_"+filters.size
    /**
      * The boogie translated filtering condition
      */
    val cond = translateExp(ast.exp)
    /**
      * The global variable declaration for this filter
      */
    val varDecl = GlobalVarDecl(Identifier(name), filterType)
  }

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
      case c@sil.Comp(_, filter, _, _, _) =>
        // retrieve the comprehension object for the comprehension call
        val comp: Comprehension = detectComp(c) match {
          case None =>
            // TODO: Alpha renaming
            val out = new Comprehension(c)
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
    // TODO: variable naming independent matching
    // the output of the function, default is none
    var out: Option[Comprehension] = None
    // sort the variable list of exp
    val varList = exp.variables sortBy {v => v.name}
    comprehensions foreach { compare =>
      // compare for syntactic equivalence of the original expressions, but without comparing the filter
      // this means, look, whether the expression references the already known comprehension compObj

      // sort the val list of the current comprehension object for comparison
      val compareVarList = compare.ast.variables sortBy {v => v.name}
      if (varList == compareVarList &&
        exp.body == compare.ast.body &&
        exp.unit == compare.ast.unit &&
        exp.binary == compare.ast.binary) {
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
    val filter = new Filter(f, c)
    filters :+ filter
    filter.varDecl.g
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
      Forall(f.comp.filtering.args, Seq(trigger), filteringApp <==> f.cond) &&
      // the assumption of the userCreated function for the filter
      FuncApp(userCreated.name, Seq(f.varDecl.g), userCreated.typ)
    }
  }

  override def filterPreambleIdentifiers(): Seq[Identifier] = {
    newFilters map { f =>
      f.varDecl.name
    }
  }

  /**
    * Just to make the code cleaner
    */
  implicit def singletonSequence[A](a: A): Seq[A] = Seq(a)

  override def preamble: Seq[Decl] = {
    val out: Seq[Decl] = Seq()

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

    // generate comprehension independent axioms and declarations

    // filter type declaration
    val filterTypeDecl = TypeDecl(filterType)

    // generate filter generating function declarations
    val minus = Func(Identifier("minus"), Seq(f1Decl, f2Decl), filterType)
    val intersect = Func(Identifier("intersect"), Seq(f1Decl, f2Decl), filterType)
    val union = Func(Identifier("union"), Seq(f1Decl, f2Decl), filterType)
    val narrow = Func(Identifier("narrow"), Seq(fDecl, rDecl), filterType)
    val filterGeneratingFunDecl = CommentedDecl("Declaration of filter generating functions", Seq(minus, intersect, union, narrow), 1)

    // generate filter property function declarations
    val empty = Func(Identifier("empty"), fDecl, Bool)
    val subfilter = Func(Identifier("subfilter"), Seq(f1Decl, f2Decl), Bool)
    val equivalent = Func(Identifier("equivalent"), Seq(f1Decl, f2Decl), Bool)
    val filterPropertyFunDecl = CommentedDecl("Declaration of filter property functions", Seq(empty, subfilter, equivalent), 1)

    out :+ CommentedDecl("Comprehension independent declarations", Seq(filterTypeDecl, filterGeneratingFunDecl, filterPropertyFunDecl), 2)

    // generate filter property function axiomatizations
    val subfilterAxiom = Axiom(
      subfilter.apply(Seq(f1, f2)) <==> empty.apply(minus.apply(Seq(f1, f2))) forall (
        Seq(f1Decl, f2Decl),
        Trigger(subfilter.apply(Seq(f1, f2)))
      )
    )
    val equivalentAxiom = Axiom(
      equivalent.apply(Seq(f1, f2)) <==> (subfilter.apply(Seq(f1, f2)) && subfilter.apply(Seq(f2, f1))) forall (
        Seq(f1Decl, f2Decl),
        Trigger(equivalent.apply(Seq(f1, f2)))
      )
    )
    val filterPopertyFunAx = CommentedDecl("Comprehension independent axiomatization of filter property functions", Seq(subfilterAxiom, equivalentAxiom), 1)

    out :+ CommentedDecl("Comprehension independent axioms", Seq(filterPopertyFunAx), 2)


    // generate the axiomatizations of the different comprehensions
    comprehensions foreach { c =>

      // generate filtering axioms
      // filtering function declaration
      val filtering = c.filtering
      // filter generating function axiomatizations
      val minusAxiom = Axiom(
        c.applyFiltering(minus.apply(Seq(f1, f2))) <==> (c.applyFiltering(f1) &&  c.applyFiltering(f2).not) forall (
          Seq(f1Decl, f2Decl) ++ c.varDecls,
          Trigger(c.applyFiltering(minus.apply(Seq(f1, f2))))
        )
      )
      val intersectAxiom = Axiom(
        c.applyFiltering(intersect.apply(Seq(f1, f2))) <==> (c.applyFiltering(f1) &&  c.applyFiltering(f2)) forall (
          Seq(f1Decl, f2Decl) ++ c.varDecls,
          Trigger(c.applyFiltering(intersect.apply(Seq(f1, f2))))
        )
      )
      val unionAxiom = Axiom(
        c.applyFiltering(union.apply(Seq(f1, f2))) <==> (c.applyFiltering(f1) ||  c.applyFiltering(f2)) forall (
          Seq(f1Decl, f2Decl) ++ c.varDecls,
          Trigger(c.applyFiltering(union.apply(Seq(f1, f2))))
        )
      )
      val narrowAxiom = Axiom(
        c.applyFiltering(narrow.apply(Seq(f, r))) <==> (c.applyFiltering(f) && (c.receiver !== r)) forall (
          Seq(f1Decl, rDecl) ++ c.varDecls,
          Trigger(c.applyFiltering(narrow.apply(Seq(f, r))))
        )
      )
      // filter property function axiomatizations
      val emptyAxiom = Axiom(
        empty.apply(f) <==> (c.applyFiltering(f).not forall (c.varDecls, Trigger(c.applyFiltering(f)))) forall (
          fDecl,
          Trigger(empty.apply(f))
        )
      )
      val filterAxioms: Seq[Decl] = Seq(filtering, minusAxiom, intersectAxiom, unionAxiom, narrowAxiom, emptyAxiom, subfilterAxiom, equivalentAxiom)


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
