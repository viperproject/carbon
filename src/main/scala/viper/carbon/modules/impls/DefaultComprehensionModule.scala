package viper.carbon.modules.impls

import viper.carbon.boogie._
import viper.carbon.modules._
import viper.carbon.verifier.Verifier
import viper.silver.{ast => sil}
import viper.carbon.boogie.Implicits._
import viper.silver.verifier.{errors, reasons}

class DefaultComprehensionModule(val verifier: Verifier) extends ComprehensionModule {

  import verifier._
  import expModule._
  import mainModule._
  import typeModule._
  import heapModule._

  implicit val compNamespace: Namespace = verifier.freshNamespace("comp")

  override def name: String = "Comprehension Module"

  override def start() = {}

  override def stop() = {}

  override def reset() = {
    comprehensions = Seq()
    filters = Seq()
  }

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
    /** The boogie translated value field of the body */
    val value = translateLocation(ast.body)
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
    /**
      * A list of variables which are defined outside the context of the comprehension of this filter,
      * but which are mentioned in the filter condition
      */
    val outerVarDecls = cond reduce {(n: Node, varLists: Seq[Seq[LocalVar]]) =>
      n match {
        case l: LocalVar =>
          val unit: Seq[LocalVar] = Seq()
          val out = (varLists :\ unit)(_ ++ _)
          if (!comp.localVars.contains(l) && !out.contains(l))
            out :+ l
          else
            out
      }
    } map {l => LocalVarDecl(l.name, l.typ)}
    /**
      * The declaration of this filter,
      * which is a global variable declaration, if the filter is context free (i.e. [[outerVarDecls]] is empty),
      * or a function declaration if it depends on the context
      */
    val decl = if(outerVarDecls.isEmpty)
      GlobalVarDecl(Identifier(name), filterType) else
      Func(Identifier(name), outerVarDecls, filterType)
    /** The boogie expression representing this filter */
    val exp = decl match {
      case f@Func(_, vars, _) => f.apply(vars map {_.l})
      case g: GlobalVarDecl => g.g
    }
  }

  /** All comprehensions occurring in the program */
  private var comprehensions: Seq[Comprehension] = Seq()

  /** All filters occurring in the program */
  private var filters: Seq[Filter] = Seq()

  /** The boogie filter type */
  val filterType = NamedType("Filter")

  /** The function declaration of the userCreated function */
  val userCreated = Func(Identifier("userCreated"), Seq(LocalVarDecl(Identifier("f"), filterType)), Bool)

  // practical constants for common variables for avoiding boilerplate code
  private val fDecl = LocalVarDecl(Identifier("f"), filterType)
  private val f1Decl = LocalVarDecl(Identifier("f1"), filterType)
  private val f2Decl = LocalVarDecl(Identifier("f2"), filterType)
  private val rDecl = LocalVarDecl(Identifier("r"), refType)
  private val hDecl = staticStateContributions(withHeap = true, withPermissions = true).head // this is the variable declaration of the viper heap
  private val f = fDecl.l
  private val f1 = f1Decl.l
  private val f2 = f2Decl.l
  private val r = rDecl.l
  private val h = hDecl.l

  override def translateComp(e: sil.Exp): Exp = {
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
    * Translates a filter, i.e. generate a new filter instance and enlist it in [[filters]],
    * then return a variable (or function call) representing the filter
    */
  private def translateFilter(f: sil.Filter, c: Comprehension): Exp = {
    val filter = new Filter(f, c)
    filters :+ filter
    filter.exp
  }

  override def preamble: Seq[Decl] = {
    var out: Seq[Decl] = Seq()

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

    out = out :+ CommentedDecl("Comprehension independent declarations", filterTypeDecl ++ filterGeneratingFunDecl ++ filterPropertyFunDecl ++ dummyFunDecl, 2)

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

    out = out :+ CommentedDecl("Comprehension independent axioms", filterPopertyFunAx, 2)


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
      val inverseAxioms = (inv map {tuple=>tuple._1}) ++ invAxioms1 ++ invAxioms2


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
          Trigger(dummy.apply(f) ++ MapSelect(h, r++c.value) ++ userMentioned.apply(r))
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
      val error = errors.ComprehensionNotWellformed(c.ast)
      // receiver injectivity check
      /** second version of argument declarations for comparison */
      val argDecl2 = c.varDecls map {vDec => LocalVarDecl(Identifier(vDec.name.name), vDec.typ)}
      /** a sequence of tuples with the standard and second versions of the argument declarations */
      val argZip = c.varDecls zip argDecl2
      /** conjunction of the form: a1 != a1_1 && a2 != a2_1 && ... */
      val notEqualConj = ((argZip map {tuple => tuple._1.l !== tuple._2.l}) :\ BoolLit(true).asInstanceOf[Exp])(_ && _)
      /** the second version of the receiver */
      var recv2 = (argZip :\ c.receiver)((tuple, rec) => rec.replace(tuple._1.l, tuple._2.l))
      val injectiveCheck = Assert(
        notEqualConj ==> (c.receiver !== recv2) forall (c.varDecls++argDecl2, Trigger(c.receiver) ++ Trigger(recv2)),
        error.dueTo(reasons.ReceiverNotInjective(c.ast.body))
      )
      // unit check
      val xDecl = LocalVarDecl(Identifier("x"), c.typ)
      val x = xDecl.l
      val unitCheck = Assert(
        c.binary(x, c.unit) === x forall (xDecl, Trigger(c.binary(x, c.unit))),
        error.dueTo(reasons.CompUnitNotUnit(c.ast.unit))
      )
      // binary commutative check
      val yDecl = LocalVarDecl(Identifier("y"), c.typ)
      val y = yDecl.l
      val binaryCommCheck = Assert(
        c.binary(x, y) === c.binary(y, x) forall (xDecl++yDecl, Trigger(c.binary(x, y))),
        error.dueTo(reasons.CompBinaryNotCommutative(c.ast))
      )
      // binary associative check
      val zDecl = LocalVarDecl(Identifier("z"), c.typ)
      val z = zDecl.l
      val binaryAssocCheck = Assert(
        c.binary(x, c.binary(y, z)) === c.binary(c.binary(x, y), z) forall (xDecl++yDecl++zDecl, Trigger(c.binary(x, c.binary(y, z)))),
        error.dueTo(reasons.CompBinaryNotAssociative(c.ast))
      )
      val definednessCheck: Stmt =
        CommentBlock("Check for receiver injectivity", injectiveCheck) ++
        CommentBlock("Check for unit", unitCheck) ++
        CommentBlock("Check for commutativity of binary operator", binaryCommCheck) ++
        CommentBlock("Check for associativity of binary operator", binaryAssocCheck)
      val definednessProc = Procedure(Identifier(c.name+"#definedness"), Seq(), Seq(), definednessCheck)


      val axioms =
        CommentedDecl("Declaration of comprehension", c.decl, 1) ++
        CommentedDecl("Declaration and axiomatization of inverse functions", inverseAxioms, 1) ++
        CommentedDecl("Declaration and axiomatization of filtering function", filterAxioms, 1) ++
        CommentedDecl("Declaration of comprehension dependent dummy functions", dummy, 1) ++
        CommentedDecl("Comprehension axioms", comprehensionAxioms, 1) ++
        CommentedDecl("Additional axioms", additionalAxioms, 1) ++
        CommentedDecl("Definedness check", definednessProc, 1)
      out = out :+ CommentedDecl("Axiomatization of comprehension " + c.name, axioms, 2)
    }

    // generate the filter variables
    val filterDeclarations = filters map { f =>
      f.decl
    }
    // axiomatize the filters
    val filterAxioms = filters map { f =>
      val filtering = f.comp.filtering
      val filteringArgs: Seq[Exp] = filtering.args map {a => a.l}
      val filteringApp = filtering.apply(filteringArgs)
      val trigger = Trigger(filteringApp)
      val axiom =
        // the axiomatization of the filter in terms of its filtering condition
        Forall(filtering.args, trigger, filteringApp <==> f.cond) &&
          // the assumption of the userCreated function for the filter
          FuncApp(userCreated.name, f.exp, userCreated.typ)
      f.decl match {
          // for function declarations, need to wrap in a outer quantifier, to quantify over the "outer variables"
        case Func(_, args, _) => Axiom(axiom forall (args, Trigger(f.exp)))
        case _: GlobalVarDecl => Axiom(axiom)
      }
    }
    out = out :+ CommentedDecl("Translation of filter declarations", filterDeclarations, 2)
    out
  }
}
