package viper.carbon.modules.impls

import viper.carbon.boogie._
import viper.carbon.modules._
import viper.carbon.verifier.Verifier
import viper.silver.{ast => sil}
import viper.carbon.boogie.Implicits._
import viper.carbon.modules.components.DefinednessComponent
import viper.silver.ast.utility.Expressions
import viper.silver.verifier.{PartialVerificationError, errors, reasons}

import scala.collection.mutable

/*
This module is the default module for translating comprehensions.
The translation of a comprehension generates a simple function call to a new function, expressing the value of the comprehension.
Such a function has a heap and a filter as arguments.
Multiple comprehension expressions are gathered to one comprehension, if the body, the unit and the binary operator are syntactically equivalent,
ignoring variable naming, which means, that the naming of the variable declarations of the comprehension has no influence on detecting equivalence
of comprehensions. This detection is done in the method `detectComp`.
With every comprehension expression however, a new filter instance is generated from the filter expression, if the full comprehension expression
is not completely syntactically equivalent to a different comprehension call (in which case the translation buffer `buffer` translates it to the same,
already translated expression). There is an optimization, which could be implemented,
that syntactically equivalent filters, when ignoring comprehension variable names, are detected.
TODO: Optimization: naming independent filter equivalence detection
Filters are translated to a constant, if they do not depend on variables outside of the comprehension expression,
and to a function with the relevant outer variables as arguments, if it depends on such variables.

Except for the direct translation of a comprehension expression into a simple function call, the module only outputs two further parts:
The preamble and a userMentioned assumption for every viper reference in the program.
The preamble declares and axiomatizes the comprehensions and filters, gathered throughout the program.
The details for this are available in the thesis for comprehension support in Viper.
 */

class DefaultComprehensionModule(val verifier: Verifier) extends ComprehensionModule with DefinednessComponent {

  import verifier._
  import expModule._
  import mainModule._
  import typeModule._
  import heapModule._
  import funcPredModule._


  // =======================================
  // module specific properties and methods
  // =======================================

  implicit val compNamespace: Namespace = verifier.freshNamespace("comp")

  override def name: String = "Comprehension Module"

  override def start() = {
    expModule.register(this)
  }

  override def stop() = {}

  override def reset() = {
    buffer = new mutable.HashMap()
    comprehensions = Seq()
    filters = Seq()
  }


  // =======================================
  // classes for describing comprehension and filter
  // =======================================

  /** A class for describing a comprehension instance. */
  class Comprehension(val ast: sil.Comp) {

    // translations of the different components
    /** The name of the comprehension */
    val name = "comp"+comprehensions.size
    /** The boogie translated local variable declarations */
    val varDecls = {
      ast.variables map translateLocalVarDecl
    }
    /** A list of local variables emerging from the local variable declarations of this comprehension. */
    val localVars = varDecls map {v => v.l}
    /** A map from Ast local variables to their translations */
    val localVarTranslation: Map[sil.LocalVar, LocalVar] = ((ast.variables zip varDecls) map {tuple => tuple._1.localVar -> tuple._2.l}).toMap
    /** The boogie translated body of the comprehension */
    val body = translateExp(ast.body)
    /** The boogie translated receiver of the body */
    val receiver = translateExp(ast.body.rcv)
    /** The boogie translated value field of the body */
    val value = translateLocation(ast.body)
    /** The boogie translated unit */
    val unit = translateExp(ast.unit)
    /** The boogie type of the comprehension */
    val typ = translateType(ast.unit.typ)
    /** The boogie translated binary application example */
    private val binaryApp = translateExp(ast.binaryApp).asInstanceOf[FuncApp]

    /** The function declaration of the comprehension */
    val decl = Func(Identifier(name), hDecl ++ fDecl, typ)

    // methods and properties for binary operator application
    /** Whether the binary function is heap dependent, i.e. it is not a domain function */
    val isBinaryHeapDep = binaryApp.args.size == 3
    /** Returns a boogie function application of the binary opertor */
    def binary(lhs: Exp, rhs: Exp) = binaryApp.replace(body, lhs).replace(unit, rhs)

    // declaration and application of the filtering function
    /** The boogie function declaration of the filtering function of this comprehension. */
    val filtering = Func(Identifier(name + "#filtering"), varDecls :+ LocalVarDecl(Identifier("f"), filterType), Bool)
    /**
      * Applies the filtering function for the specified filter and [[localVars]].
      * This means that this method is a shortcut for application of the comprehension specific filtering function,
      * in a way that the comprehension specific arguments don't need to be specified, but only the filter.
      */
    def applyFiltering(filter: Exp) = filtering.apply(localVars :+ filter)

    // receiver inverse function declaration
    /** Indicates, whether the receiver is a simple variable (of type ref) */
    val recvIsVar = receiver.isInstanceOf[LocalVar]
    /** The inverse function declarations of all comprehension arguments along with the respective argument declaration.
      * Note, that this should not be used, when [[recvIsVar]]*/
    val inv: Seq[(Func, LocalVarDecl)] = varDecls map { vDecl => (Func(Identifier(name + "#inv_"+vDecl.name.name), rDecl, vDecl.typ), vDecl)}
    /** Applies the inverse functions to the given arguments (and respecting the [[recvIsVar]] case).*/
    def invApply(args: Seq[Exp]): Seq[Exp] = {
      require(args.size == inv.size)
      if (recvIsVar) args else inv.indices map {i => inv(i)._1.apply(args(i))}
    }

    // dummy function
    /** The dummy function of this comprehension */
    val dummy = Func(Identifier(name+"#dummy"), fDecl, Bool)
  }


  /** A class for describing a filter instance.*/
  class Filter(ast: sil.Filter, val comp: Comprehension)(val cond: Exp = translateExp(ast.exp)) {

    /** The name of the filter */
    val name = "filter"+filters.size

    /**
      * A list of variables which are defined outside the context of the comprehension of this filter,
      * but which are mentioned in the filter condition
      */
    val outerVarDecls = cond reduce {(n: Node, varLists: Seq[Seq[LocalVar]]) =>
      val unit: Seq[LocalVar] = Seq()
      val out = (varLists :\ unit)((l, r) => (l ++ r).distinct)
      n match {
        case l: LocalVar =>
          if (!comp.localVars.contains(l) && !out.contains(l)) {
            out :+ l
          }else
            out
        case _ => out
      }
    } map {l => LocalVarDecl(l.name, l.typ)}

    /**
      * The declaration of this filter,
      * which is a constant declaration, if the filter is context free (i.e. [[outerVarDecls]] is empty),
      * or a function declaration if it depends on the context
      */
    val decl = if(outerVarDecls.isEmpty)
      ConstDecl(Identifier(name), filterType) else
      Func(Identifier(name), outerVarDecls, filterType)

    /** The boogie expression representing this filter */
    val exp = decl match {
      case f@Func(_, vars, _) => f.apply(vars map {_.l})
      case c: ConstDecl => Const(c.name)
      case _ => sys.error("unexpected filter declaration")
    }
  }


  // =======================================
  // properties and methods for comprehension translation
  // =======================================

  /** All comprehensions occurring in the program */
  private var comprehensions: Seq[Comprehension] = Seq()

  /** All filters occurring in the program */
  private var filters: Seq[Filter] = Seq()

  /** The boogie filter type */
  val filterType = NamedType("Filter")

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

  private var buffer: mutable.HashMap[sil.Exp, Exp] = new mutable.HashMap()

  override def translateComp(e: sil.Exp): Exp = {
    // first check whether it was already translated
    buffer.get(e) match {
      case Some(x) => x
      case None =>
        val out = e match {
          case c@sil.Comp (vars, filter, body, binary, unit) =>
            // retrieve the comprehension object for the comprehension call
            detectComp (c) match {
              case (None, _, _) =>
                // alpha renaming
                val fresh = vars map { v => env.makeUniquelyNamed (v)}
                fresh map { v => env.define (v.localVar)}
                def renaming[E <: sil.Exp] = (e: E) => Expressions.renameVariables (e, vars map { v => v.localVar}, fresh map { v => v.localVar})
                val (freshFilter, freshBody) = (sil.Filter(renaming(filter.exp))(filter.pos, filter.info, filter.errT), renaming(body) )
                // created instance
                val comp = new Comprehension (sil.Comp (fresh, freshFilter, freshBody, binary, unit) (c.typ, c.pos, c.info, c.errT) )
                // translate filter
                val filterInstance = new Filter(freshFilter, comp)()
                filters = filters :+ filterInstance
                val translatedFilter = filterInstance.exp
                // add comprehension to list
                comprehensions = comprehensions :+ comp
                fresh map {v=>env.undefine(v.localVar)}
                comp.decl.apply(currentStateVars ++ translatedFilter)

              case (Some(comp), old, fresh) =>
                // define the fresh variables (the ast variables of the detected comprehension)
                fresh map { v => env.define(v)}
                // translate filter
                // replace all variables in the ast to their corresponding ast variables of the comprehension
                val freshFilter = sil.Filter(Expressions.renameVariables(filter.exp, old, fresh))(filter.pos, filter.info, filter.errT)
                // create a temporary filter instance for translating the filtering condition
                val tempInstance = new Filter(freshFilter, comp)()
                // Replace the variables in the condition with the translated variables of the comprehension.
                // Since the variables were newly defined in the environment, they won't be translated automatically to the
                // corresponding ones of the comprehension.
                val cond = (fresh :\ tempInstance.cond)((v, exp) => exp.replace(env.get(v), comp.localVarTranslation(v)))
                // undefine the variables
                fresh map {v=>env.undefine(v)}
                // create a new intance with the correct condition
                val filterInstance = new Filter(filter, comp)(cond)
                filters = filters :+ filterInstance
                comp.decl.apply(currentStateVars ++ filterInstance.exp)
            }
          case _ => sys.error("unexpected expression when translating comprehension")
        }
        // enlist in buffer
        buffer.put(e, out)
        out
    }
  }

  /**
    * Detects which comprehension of the currently available comprehensions (in [[comprehensions]]) is called by the
    * expression.
    *
    * @param exp The call to a comprehension
    * @return The comprehension used in the call, wrapped inside Some, or None, if there is no instance of the called
    *         comprehension yet (a new instance has to be created), together with a list of the old variables and
    *         a list of the corresponding new variables, i.e. the variables of the comprehension instance in the
    *         order, in which they should be replaced.
    */
  private def detectComp(exp: sil.Comp): (Option[Comprehension], Seq[sil.LocalVar], Seq[sil.LocalVar]) = {
    /** The current variables of the body expression, in the order as they appear in the traversal */
    val oldVars = sil.utility.Expressions.collectVars(exp.body)

    /** The recursive function to detect the comprehension */
    def detect(comps: Seq[Comprehension]): (Option[Comprehension], Seq[sil.LocalVar], Seq[sil.LocalVar]) = {
      comps match {
        case Seq() => (None, Nil, Nil)
        case s: Seq[Comprehension] =>
          val comp = s.head
          // unit and binary are static, so we can compare them directly
          if (exp.binaryApp.funcname == comp.ast.binaryApp.funcname && exp.unit == comp.ast.unit) {
            // Compare the bodies.
            // Since the order of traversal is always the same, we expect for equal bodies,
            // that the collected variables during the traversal for two bodies are the same.
            // For naming independence of the variables, we therefore get a equivalence mapping
            // when collecting the variables for the two bodies.
            // So if we substitute the variables of one body with the equivalent variables of the other body,
            // the two bodies should be the same.
            val fresh = sil.utility.Expressions.collectVars(comp.ast.body)
            if (fresh.size == oldVars.size && Expressions.renameVariables(exp.body, oldVars, fresh) == comp.ast.body) {
              return (Some(comp), oldVars, fresh)
            }
          }
          detect(s.tail)
      }
    }

    detect(comprehensions)
  }


  // =======================================
  // comprehension independent declarations for the preamble
  // =======================================

  // filter type declaration
  private val filterTypeDecl = TypeDecl(filterType)

  // generate filter generating function declarations
  private val minus = Func(Identifier("minus"), f1Decl ++ f2Decl, filterType)
  private val intersect = Func(Identifier("intersect"), f1Decl ++ f2Decl, filterType)
  private val union = Func(Identifier("union"), f1Decl ++ f2Decl, filterType)
  private val narrow = Func(Identifier("narrow"), fDecl ++ rDecl, filterType)

  // filter property function declarations
  private val empty = Func(Identifier("empty"), fDecl, Bool)
  private val subfilter = Func(Identifier("subfilter"), f1Decl ++ f2Decl, Bool)
  private val equivalent = Func(Identifier("equivalent"), f1Decl ++ f2Decl, Bool)

  // dummy function declarations
  private val userCreated = Func(Identifier("userCreated"), fDecl, Bool)
  private val userMentioned = Func(Identifier("userMentioned"), rDecl, Bool)


  // =======================================
  // preamble
  // =======================================

  override def preamble: Seq[Decl] = {
    var out: Seq[Decl] = Seq()

    // generate comprehension independent axioms and declarations

    val filterGeneratingFunDecl = CommentedDecl("Declaration of filter generating functions", minus ++ intersect ++ union ++ narrow, 1)
    val filterPropertyFunDecl = CommentedDecl("Declaration of filter property functions", empty ++ subfilter ++ equivalent, 1)
    val dummyFunDecl = CommentedDecl("Declaration of dummy functions", userCreated ++ userMentioned, 1)

    out = out :+ CommentedDecl("Comprehension independent declarations",
      filterTypeDecl ++
        filterGeneratingFunDecl ++
        filterPropertyFunDecl ++
        dummyFunDecl,
      2, nLines = 2)

    out = out :+ CommentedDecl("Comprehension independent axioms", comprehensionIndependentFilterAxioms(), 2, nLines = 2)

    // generate the axiomatizations of the different comprehensions
    comprehensions foreach { c =>
      val axioms =
        CommentedDecl("Declaration of comprehension", c.decl, 1) ++
        MaybeCommentedDecl("Declaration and axiomatization of inverse functions", inverseAxioms(c), 1) ++
        CommentedDecl("Declaration and axiomatization of filtering function", comprehensionDependentFilterAxioms(c), 1) ++
        CommentedDecl("Declaration of dummy function", c.dummy, 1) ++
        CommentedDecl("Comprehension axioms", comprehensionAxioms(c), 1) ++
        CommentedDecl("Framing axiom", framingAxiom(c), 1) ++
        CommentedDecl("Additional axioms", additionalAxioms(c), 1) ++
        CommentedDecl("Definedness check", definednessCheck(c), 1)

      out = out :+ CommentedDecl("Axiomatization of comprehension " + c.name, axioms, 2, nLines = 2)
    }

    // generate the filter variables
    val filterDeclarations = filters map { f => f.decl }
    // axiomatize the filters
    val filterAxioms = filters map { f => filterAxiomatization(f) }
    out = out ++ MaybeCommentedDecl("Translation of filter declarations", filterDeclarations, 2, nLines = 2)
    out = out ++ MaybeCommentedDecl("Translation of filter axioms", filterAxioms, 2, nLines = 2)

    out
  }


  private def comprehensionIndependentFilterAxioms(): Seq[Decl] = {
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
    CommentedDecl("Comprehension independent axiomatization of filter property functions", subfilterAxiom ++ equivalentAxiom, 1)
  }


  private def comprehensionDependentFilterAxioms(c: Comprehension): Seq[Decl] = {
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

    filtering ++ minusAxiom ++ intersectAxiom ++ unionAxiom ++ narrowAxiom ++ emptyFilterAxiom
  }


  private def inverseAxioms(c: Comprehension): Seq[Decl] = {
    // If the receiver is a plain variable, the inverse is simply the variable itself,
    // hence no function declaration necessary.
    // Therefore only output the axioms if the receiver is not a variable
    if(!c.recvIsVar) {
      // inv(e(a)) == a
      val lhsConjunct = c.inv map {tuple => tuple._1.apply(c.receiver) === tuple._2.l}
      val invAxioms1 = Axiom(lhsConjunct.tail.foldLeft(lhsConjunct.head){_ && _} forall(c.varDecls, Trigger(c.receiver)))
      // e(inv(r)) == r
      val inverseApplications = c.invApply(Seq.fill(c.varDecls.size)(r))
      val receiver = ((c.localVars zip inverseApplications) :\ c.receiver)((tuple, rcv) => rcv.replace(tuple._1, tuple._2))
      val invAxioms2 = Axiom(receiver === r forall (rDecl, c.inv map { tuple =>Trigger(tuple._1.apply(r)) }))
      (c.inv map { tuple => tuple._1 }) ++ invAxioms1 ++ invAxioms2
    } else
      Seq()
  }


  private def comprehensionAxioms(c: Comprehension): Seq[Decl] = {
    val dummyAxiom = Axiom(c.dummy.apply(f) forall (hDecl ++ fDecl, Trigger(c.decl.apply(h ++ f))))
    val emptyAxiom = Axiom(empty.apply(f) ==> (c.decl.apply(h ++ f) === c.unit) forall (hDecl ++ fDecl, Trigger(c.decl.apply(h ++ f))))
    val locationAccess = c.body.replace(c.receiver, r)
    val inverseVal: Seq[Exp] = if(!c.recvIsVar) c.invApply(Seq.fill(c.localVars.size)(r)) else r
    val singletonAxiom = Axiom(
      c.filtering.apply(inverseVal ++ f) ==>
        (c.decl.apply(h ++ f) === c.binary(c.decl.apply(h ++ narrow.apply(f ++ r)), locationAccess)) forall (
        hDecl ++ fDecl ++ rDecl,
        Trigger(c.dummy.apply(f) ++ MapSelect(h, r++c.value) ++ userMentioned.apply(r))
      )
    )
    val generalAxiom = Axiom(
      (empty.apply(f).not && empty.apply(f1).not && subfilter.apply(f1++f) && equivalent.apply(f1++f).not) ==>
        (c.decl.apply(h++f) === c.binary(c.decl.apply(h ++ minus.apply(f++f1)), c.decl.apply(h++f1))) forall (
        hDecl ++ fDecl ++ f1Decl,
        Trigger(c.dummy.apply(f) ++ c.decl.apply(h++f1) ++ userCreated.apply(f1))
      )
    )

    dummyAxiom ++ emptyAxiom ++ singletonAxiom ++ generalAxiom
  }


  private def framingAxiom(c: Comprehension): Seq[Decl] = {
    val h = currentStateVars.head
    val (_, curState) = stateModule.freshTempState("Heap1")
    val h1 = currentStateContributions.head
    val h1Var = h1.l
    val access1 = c.body.replace(c.receiver, r).replace(h, h1Var)
    stateModule.freshTempState("Heap2")
    val h2 = currentStateContributions.head
    val h2Var = h2.l
    val access2 = c.body.replace(c.receiver, r).replace(h, h2Var)
    val out = Axiom(
      (c.filtering.apply(c.invApply(Seq.fill(c.inv.size)(r)) ++ f) ==> (access1 === access2) forall (
        rDecl,
        Trigger(access1 ++ access2)
      )) ==> (c.decl.apply(h1Var ++ f) === c.decl.apply(h2Var ++ f)) forall (
        fDecl++h1++h2,
        Trigger(c.decl.apply(h1Var++f) ++ c.decl.apply(h2Var++f))
      )
    )
    stateModule.replaceState(curState)
    out
  }


  private def additionalAxioms(c: Comprehension): Seq[Decl] = {
    val equalAxiom = Axiom(equivalent.apply(f1++f2) ==> (f1 === f2) forall (f1Decl++f2Decl, Trigger(c.dummy.apply(f1)++c.dummy.apply(f2))))
    val filterUniteAxiom = Axiom(
      (empty.apply(intersect.apply(f++f1)).not && empty.apply(intersect.apply(f++f2)).not && empty.apply(intersect.apply(f1++f2))) ==>
        (c.dummy.apply(union.apply(f1++f2)) && userCreated.apply(union.apply(f1++f2))) forall (
        fDecl++f1Decl++f2Decl,
        Trigger(c.dummy.apply(f)++c.dummy.apply(f1)++c.dummy.apply(f2)++userCreated.apply(f1)++userCreated.apply(f2))
      )
    )
    equalAxiom ++ filterUniteAxiom
  }


  private def definednessCheck(c: Comprehension): Seq[Decl] = {
    // preamble of procedure: definition of heap and necessary assumptions if binary is heap dependent
    val preamble: Seqn = if (c.isBinaryHeapDep){
      Assume(stateModule.staticGoodState) ++
        assumeAllFunctionDefinitions
    } else Seq()
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
    val injectiveCheck: Seq[Stmt] = if(c.recvIsVar) Seq() else Assert( // if receiver is a variable, it is trivially injective
      notEqualConj ==> (c.receiver !== recv2) forall (c.varDecls++argDecl2, Trigger(c.receiver ++ recv2)),
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
      MaybeCommentBlock("Assumptions for heap dependent function", preamble) ++
        MaybeCommentBlock("Check for receiver injectivity", injectiveCheck) ++
        CommentBlock("Check for unit", unitCheck) ++
        CommentBlock("Check for commutativity of binary operator", binaryCommCheck) ++
        CommentBlock("Check for associativity of binary operator", binaryAssocCheck)

    val arg: Seq[LocalVarDecl] = if(c.isBinaryHeapDep) staticStateContributions(withHeap = true, withPermissions = true) else Seq()
    Procedure(Identifier(c.name+"#definedness"), arg, Seq(), definednessCheck)
  }


  private def filterAxiomatization(f: Filter): Decl = {
    val filtering = f.comp.filtering
    val filteringArgs: Seq[Exp] = f.comp.localVars ++ f.exp
    val filteringApp = filtering.apply(filteringArgs)
    val trigger = Trigger(filteringApp)
    val axiom =
    // the axiomatization of the filter in terms of its filtering condition
      Forall(f.comp.varDecls, trigger, filteringApp <==> f.cond) &&
        // the assumption of the userCreated function for the filter
        FuncApp(userCreated.name, f.exp, userCreated.typ)
    f.decl match {
      // for function declarations, need to wrap in a quantifier, to quantify over the "outer variables"
      case Func(_, args, _) => Axiom(axiom forall (args, Trigger(f.exp)))
      case _: ConstDecl => Axiom(axiom)
      case _ => sys.error("unexpected filter declaration")
    }
  }


  // =======================================
  // userMentioned assumption
  // =======================================

  override def validValue(typ: sil.Type, variable: LocalVar, isParameter: Boolean) = {
    // assume userMentioned for all reference variables in the silver code
    typ match {
      case sil.Ref => Some(userMentioned.apply(variable))
      case _ => None
    }
  }

  /** This variable is used for the userMentioned assumption generation to avoid userMentioned assumptions for
    * expressions in quantifiers. It indicates, how many quantifiers surround the current expression.
    */
  private var quantifierLevel = 0

  /** This method is 'misused' to output the userMentioned assumption for every reference-typed expression outside of a quantifier */
  override def partialCheckDefinedness(e: sil.Exp, error: PartialVerificationError, makeChecks: Boolean): (() => Stmt, () => Stmt) = {
    // avoid user mentioned assumptions for expressions in quantifiers (and comprehensions)
    if(e.isInstanceOf[sil.QuantifiedExp] || e.isInstanceOf[sil.Comp]) {
      (() => {quantifierLevel += 1; Statements.EmptyStmt}, () => {quantifierLevel -= 1; Statements.EmptyStmt})
    } else if (e.typ == sil.Ref && quantifierLevel == 0) // assume user mentioned for reference-typed expressions
        (() => Statements.EmptyStmt, () => Assume(userMentioned.apply(translateExp(e))))
    else
      (() => Statements.EmptyStmt, () => Statements.EmptyStmt)
  }
}
