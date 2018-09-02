package viper.carbon.modules.impls

import viper.carbon.boogie._
import viper.carbon.modules._
import viper.carbon.verifier.Verifier
import viper.silver.{ast => sil}
import viper.carbon.boogie.Implicits._

class DefaultComprehensionModule(val verifier: Verifier) extends ComprehensionModule {

  import verifier._
  import expModule._
  import mainModule._
  import typeModule._
  import heapModule._

  implicit val compNamespace: Namespace = verifier.freshNamespace("comp")

  override def name: String = "Comprehension Module"

  /** A class for describing a comprehension instance. */
  class Comprehension(val ast: sil.Comp) {
    /** The name of the comprehension */
    val name = "comp"+comprehensions.size
    /** The boogie translated local variable declarations */
    val varDecls = {
      ast.variables map translateLocalVarDecl
    }
    /** The boogie translated body of the comprehension */
    val body = translateExp(ast.body)
    /** The boogie translated receiver of the body */
    val receiver = translateExp(ast.body.rcv)
    /** The identifier for the binary operator */
    val binaryId = Identifier(ast.binary)
    /** The boogie translated unit */
    val unit = translateExp(ast.unit)
    /** The boogie type of the comprehension */
    val typ = translateType(ast.unit.typ)

    val decl = Func(Identifier(name), hDecl ++ fDecl, typ)

    /** Returns a boogie function application of the binary opertor */
    def binary(lhs: Exp, rhs: Exp) = FuncApp(binaryId, lhs ++ rhs, typ)

    /**
      * The boogie function declaration of the filtering function of this comprehension.
      * It has the following signature: filtering_compName(a, f)
      * where a denotes the comprehension argument(s) and f denotes the filter
      */
    val filtering = Func(Identifier(name + "#filtering"), varDecls :+ LocalVarDecl(Identifier("f"), filterType), Bool)
    /** A list of local variables emerging from the local variable declarations of this comprehension. */
    val localVars = varDecls map {v => v.l}
    /**
      * Applies the filtering function for the specified filter and [[localVars]].
      * This means that this method is a shortcut for application of the comprehension specific filtering function,
      * in a way that the comprehension specific arguments don't need to be specified, but only the filter.
      */
    def applyFiltering(filter: Exp) = filtering.apply(localVars :+ filter)
  }

  /** A class for describing a filter instance.*/
  class Filter(val ast: sil.Filter, val comp: Comprehension) {
    /** The name of the filter */
    val name = "filter"+filters.size
    /** The boogie translated filtering condition */
    val cond = translateExp(ast.exp)
    /** The global variable declaration for this filter */
    val varDecl = GlobalVarDecl(Identifier(name), filterType)
  }

  /** All comprehensions occurring in the program */
  private val comprehensions: Seq[Comprehension] = Seq()

  /** All filters occurring in the program */
  private val filters: Seq[Filter] = Seq()

  /** All the filters translated in this statement so far. */
  private var newFilters: Seq[Filter] = Seq()

  /** Indicates whether the module is ready for translation, i.e. the [[startNextStatement]] method was called. */
  private var readyForTranslation = false

  /** The boogie filter type */
  val filterType = NamedType("Filter")

  /** The function declaration of the userCreated function */
  val userCreated = Func(Identifier("userCreated"), Seq(LocalVarDecl(Identifier("f"), filterType)), Bool)

  // practical constants for common variables for avoiding boilerplate code
  private val fId = Identifier("f")
  private val f1Id = Identifier("f1")
  private val f2Id = Identifier("f2")
  private val rId = Identifier("r")
  private val fDecl = LocalVarDecl(fId, filterType)
  private val f1Decl = LocalVarDecl(f1Id, filterType)
  private val f2Decl = LocalVarDecl(f2Id, filterType)
  private val rDecl = LocalVarDecl(rId, refType)
  private val hDecl = staticStateContributions(withHeap = true, withPermissions = true).head // this is the variable declaration of the viper heap
  private val f = fDecl.l
  private val f1 = f1Decl.l
  private val f2 = f2Decl.l
  private val r = rDecl.l
  private val h = hDecl.l

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
        FuncApp(Identifier(comp.name), translateFilter(filter, comp), comp.typ)
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
      val trigger = Trigger(filteringApp)
      // the axiomatization of the filter in terms of its filtering condition
      Forall(f.comp.filtering.args, trigger, filteringApp <==> f.cond) &&
      // the assumption of the userCreated function for the filter
      FuncApp(userCreated.name, f.varDecl.g, userCreated.typ)
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
    val minus = Func(Identifier("minus"), f1Decl ++ f2Decl, filterType)
    val intersect = Func(Identifier("intersect"), f1Decl ++ f2Decl, filterType)
    val union = Func(Identifier("union"), f1Decl ++ f2Decl, filterType)
    val narrow = Func(Identifier("narrow"), f1Decl ++ f2Decl, filterType)
    val filterGeneratingFunDecl = CommentedDecl("Declaration of filter generating functions", minus ++ intersect ++ union ++ narrow, 1)

    // generate filter property function declarations
    val empty = Func(Identifier("empty"), fDecl, Bool)
    val subfilter = Func(Identifier("subfilter"), f1Decl ++ f2Decl, Bool)
    val equivalent = Func(Identifier("equivalent"), f1Decl ++ f2Decl, Bool)
    val filterPropertyFunDecl = CommentedDecl("Declaration of filter property functions", empty ++ subfilter ++ equivalent, 1)

    // generate comprehension independent dummy functioons
    val userCreated = Func(Identifier("userCreated"), fDecl, Bool)
    val userMentioned = Func(Identifier("userMentioned"), rDecl, Bool)
    val dummyFunDecl = CommentedDecl("Declaration of dummy functions", userCreated ++ userMentioned, 1)

    out :+ CommentedDecl("Comprehension independent declarations", filterTypeDecl ++ filterGeneratingFunDecl ++ filterPropertyFunDecl ++ dummyFunDecl, 2)

    // generate filter property function axiomatizations
    val subfilterAxiom = Axiom(
      subfilter.apply(f1++f2) <==> empty.apply(minus.apply(f1++f2)) forall (
        f1Decl ++ f2Decl,
        Trigger(subfilter.apply(f1++f2))
      )
    )
    val equivalentAxiom = Axiom(
      equivalent.apply(f1++f2) <==> (subfilter.apply(f1++f2) && subfilter.apply(f2++f1)) forall (
        f1Decl ++ f2Decl,
        Trigger(equivalent.apply(f1++f2))
      )
    )
    val filterPopertyFunAx = CommentedDecl("Comprehension independent axiomatization of filter property functions", subfilterAxiom ++ equivalentAxiom, 1)

    out :+ CommentedDecl("Comprehension independent axioms", filterPopertyFunAx, 2)


    // generate the axiomatizations of the different comprehensions
    comprehensions foreach { c =>

      // generate inverse function declaration and axiomatization
      /** The inverse function declarations of all comprehension arguments along with the respective argument declaration */
      val inv: Seq[(Func, LocalVarDecl)] = c.varDecls map { vDecl => (Func(Identifier(c.name + "#inv_"+vDecl.name.name), rDecl, vDecl.typ), vDecl)}
      // inv(e(a)) == a
      val invAxioms1 = inv map { tuple =>
        Axiom(tuple._1.apply(c.receiver) === tuple._2.l forall (tuple._2, Trigger(c.receiver)))
      }
      // e(inv(r)) == r
      val invAxioms2 = inv map { tuple =>
        Axiom(c.receiver.replace(tuple._2.l, tuple._1.apply(r)) === r forall(rDecl, Trigger(tuple._1.apply(r))))
      }


      // generate filtering axioms
      // filtering function declaration
      val filtering = c.filtering
      // filter generating function axiomatizations
      val minusAxiom = Axiom(
        c.applyFiltering(minus.apply(f1++f2)) <==> (c.applyFiltering(f1) &&  c.applyFiltering(f2).not) forall (
          f1Decl ++ f2Decl ++ c.varDecls,
          Trigger(c.applyFiltering(minus.apply(f1++f2)))
        )
      )
      val intersectAxiom = Axiom(
        c.applyFiltering(intersect.apply(f1++f2)) <==> (c.applyFiltering(f1) &&  c.applyFiltering(f2)) forall (
          f1Decl ++ f2Decl ++ c.varDecls,
          Trigger(c.applyFiltering(intersect.apply(f1++f2)))
        )
      )
      val unionAxiom = Axiom(
        c.applyFiltering(union.apply(f1++f2)) <==> (c.applyFiltering(f1) ||  c.applyFiltering(f2)) forall (
          f1Decl ++ f2Decl ++ c.varDecls,
          Trigger(c.applyFiltering(union.apply(f1++f2)))
        )
      )
      val narrowAxiom = Axiom(
        c.applyFiltering(narrow.apply(f++r)) <==> (c.applyFiltering(f) && (c.receiver !== r)) forall (
          fDecl ++ rDecl ++ c.varDecls,
          Trigger(c.applyFiltering(narrow.apply(f++r)))
        )
      )
      // filter property function axiomatizations
      val emptyFilterAxiom = Axiom(
        empty.apply(f) <==> (c.applyFiltering(f).not forall (c.varDecls, Trigger(c.applyFiltering(f)))) forall (
          fDecl,
          Trigger(empty.apply(f))
        )
      )
      val filterAxioms = filtering ++ minusAxiom ++ intersectAxiom ++ unionAxiom ++ narrowAxiom ++ emptyFilterAxiom ++ subfilterAxiom ++ equivalentAxiom

      // generate dummy function
      val dummy = Func(Identifier(c.name+"#dummy"), fDecl, Bool)

      // generate comprehension axioms
      val dummyAxiom = Axiom(dummy.apply(f) forall (hDecl ++ fDecl, Trigger(c.decl.apply(h ++ f))))
      val emptyAxiom = Axiom(empty.apply(f) ==> (c.decl.apply(h ++ f) === c.unit) forall (hDecl ++ fDecl, Trigger(c.decl.apply(h ++ f))))
      val singletonAxiom = Axiom(
        filtering.apply((inv map {tuple => tuple._1.apply(r)}) ++ f) ==>
          c.binary(c.decl.apply(h ++ f) === c.decl.apply(h ++ narrow.apply(f ++ r)), c.body) forall (
          hDecl ++ fDecl ++ rDecl,
          Trigger(dummy.apply(f) ++ c.body ++ userMentioned.apply(r))
        )
      )
      val generalAxiom = Axiom(
        (empty.apply(f).not && empty.apply(f1).not && subfilter.apply(f1++f) && equivalent.apply(f1++f).not) ==>
          (c.decl.apply(h++f) === c.binary(c.decl.apply(h ++ minus.apply(f++f1)), c.decl.apply(h++f1))) forall (
          hDecl ++ fDecl ++ f1Decl,
          Trigger(dummy.apply(f) ++ c.decl.apply(h++f1) ++ userCreated.apply(f1))
        )
      )
      val comprehensionAxioms = dummyAxiom ++ emptyAxiom ++ singletonAxiom ++ generalAxiom

      //additional axioms
      val equalAxiom = Axiom(equivalent.apply(f1++f2) ==> f1 === f2 forall (f1Decl++f2Decl, Trigger(dummy.apply(f1)++dummy.apply(f2))))
      val filterUniteAxiom = Axiom(
        (empty.apply(intersect.apply(f++f1)).not && empty.apply(intersect.apply(f++f2)).not && empty.apply(intersect.apply(f1++f2))) ==>
          (dummy.apply(union.apply(f1++f2)) && userCreated.apply(union.apply(f1++f2))) forall (
          fDecl++f1Decl++f2Decl,
          Trigger(dummy.apply(f)++dummy.apply(f1)++dummy.apply(f2)++userCreated.apply(f1)++userCreated.apply(f2))
        )
      )
      val additionalAxioms = equalAxiom ++ filterUniteAxiom

      //definedness check


      val axioms = CommentedDecl("Declaration and axiomatization of filtering function", filterAxioms, 1) ++
        CommentedDecl("Declaration of comprehension dependent dummy functions", dummy, 1) ++
        CommentedDecl("Comprehension axioms", comprehensionAxioms, 1) ++
        CommentedDecl("Additional axioms", additionalAxioms, 1)
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
