package viper.carbon.boogie

import viper.carbon.verifier.FailureContextImpl
import viper.silver.verifier.{AbstractError, ApplicationEntry, CompleteCounterexample, ConstantEntry, Counterexample, ExtractedHeap, ExtractedModel, ExtractedModelEntry, FailureContext, FieldHeapEntry, HeapEntry, LitBoolEntry, LitIntEntry, LitPermEntry, MapEntry, Model, ModelEntry, NullRefEntry, PredHeapEntry, Rational, RefEntry, SimpleCounterexample, ValueEntry, VarEntry, VerificationError}
import viper.silver.{ast => sil}

import scala.collection.mutable

/**
  * Transforms a counterexample returned by Boogie back to a Viper counterexample.
  */
object BoogieModelTransformer {

  /**
    * Adds a counterexample to the given error if one is available.
    */
  def transformCounterexample(e: AbstractError, names: Map[String, Map[sil.LocalVarDecl, String]], program: sil.Program) : Unit = {
    if (e.isInstanceOf[VerificationError] && ErrorMemberMapping.mapping.contains(e.asInstanceOf[VerificationError])){
      val ve = e.asInstanceOf[VerificationError]
      val methodName = ErrorMemberMapping.mapping.get(ve).get.name
      val namesInMember = names.get(methodName).get.map(e => e._2 -> e._1)
      val model = ve.failureContexts(0).counterExample.get.model

      val store = transformModelEntries(model, namesInMember.toMap)

      // get primary heap and mask
      val primaryMask = getNewestVersion("Mask", model)
      val primaryHeap = getNewestVersion("Heap", model)
      val primaryExtractedHeap = extractHeap(primaryMask, primaryHeap, model, program)

      // get old heap and mask
      val oldMask = getOldVersion("Mask", model)
      val oldHeap = getOldVersion("Heap", model)
      val oldExtractedHeap = (oldMask, oldHeap) match {
        case (Some(msk), Some(hp)) => Some(extractHeap(msk, hp, model, program))
        case _ => None
      }

      // get label heaps and masks
      val labelStates = getOldStates(model)
      val labelExtractedHeaps = labelStates.map{
        case (name, (msk, hp)) => name -> extractHeap(msk, hp, model, program)
      }.toMap

      val exModel = ExtractedModel(store, primaryExtractedHeap, oldExtractedHeap, labelExtractedHeaps)

      ve.failureContexts = Seq(FailureContextImpl(Some(CompleteCounterexample(model, exModel))))
    }
  }

  def translateValue(entry: ValueEntry, typ: sil.Type, model: Model) : ExtractedModelEntry = {
    typ match {
      case sil.Int => {
        entry match {
          case ConstantEntry(value) => LitIntEntry(value.toInt)
        }
      }
      case sil.Bool =>
        entry match {
          case ConstantEntry("true") => LitBoolEntry(true)
          case ConstantEntry("false") => LitBoolEntry(false)
        }
      case sil.Ref => {
        val nullEntry = model.entries.get("null")
        entry match {
          case ce@ConstantEntry(value) if nullEntry == Some(ce) => NullRefEntry(value)
          case ConstantEntry(value) => RefEntry(value)
        }
      }
      case sil.Perm => {
        LitPermEntry(convertPermission(entry))
      }
    }
  }

  def getOldStates(model: Model): Map[String, (ConstantEntry, ConstantEntry)] = {
    val nameOptions = model.entries.keys.filter(n => n.startsWith("Label") && n.endsWith("Mask")).map(n => n.substring(5, n.length - 4))
    val result = nameOptions.collect{
      case n if model.entries.contains(s"Label${n}Heap") => n -> (model.entries.get(s"Label${n}Mask").get.asInstanceOf[ConstantEntry],
                                                                  model.entries.get(s"Label${n}Heap").get.asInstanceOf[ConstantEntry])
    }.toMap
    result
  }

  def getOldVersion(varName: String, model: Model): Option[ConstantEntry] = {
    model.entries.find(_._1.startsWith(varName + "@@")).flatMap{case e => Some(e._2.asInstanceOf[ConstantEntry])}
  }

  def getNewestVersion(varName: String, model: Model): ConstantEntry = {
    var highestIndex = -1
    var result: ConstantEntry = null
    model.entries.foreach({
      case (name, entry) if name.startsWith(varName + "@") && name.indexOf("@@") == -1  => {
        val currentIndex = Integer.parseInt(name.substring(name.indexOf("@") + 1))
        if (currentIndex > highestIndex) {
          result = entry.asInstanceOf[ConstantEntry]
          highestIndex = currentIndex
        }
      }
      case _ =>
    })
    result
  }

  def extractHeap(mask: ConstantEntry, heap: ConstantEntry, model: Model, program: sil.Program): ExtractedHeap = {
    val maskEntries = getMapEntries(mask,  model)
    val realConversion = model.entries("U_2_real").asInstanceOf[MapEntry]
    val maskEntriesWithPerms: Map[(ValueEntry, ValueEntry), ValueEntry] = maskEntries.map({
      case (k, v) => k -> realConversion.options.get(Seq(v)).get
    })
    val nonZeroMaskEntries = maskEntriesWithPerms.filter(_._2 != ConstantEntry("0.0"))

    val heapEntries = getMapEntries(heap,  model)

    // get all field and predicate refs
    val fields = new mutable.HashMap[ConstantEntry, sil.Field]()

    val possiblePredicateEntries: Map[MapEntry, sil.Predicate] = model.entries.flatMap{
      case (name, entry) if PrettyPrinter.backMap.contains(name) => {
        val possibleName = PrettyPrinter.backMap.get(name).get
        val possiblePred = program.predicates.find(p => p.name == possibleName)
        if (possiblePred.isDefined) {
          Some(entry.asInstanceOf[MapEntry] -> possiblePred.get)
        }else{
          None
        }
      }
      case _ => None
    }

    val predicates = new mutable.HashMap[ConstantEntry, (sil.Predicate, Seq[ModelEntry])]()

    model.entries.get("IsPredicateField").get.asInstanceOf[MapEntry].options.foreach({
      case (Seq(valEntry), ConstantEntry("false")) => {
        val fieldEntry = model.entries.find({
          case (name, entry) => entry == valEntry && PrettyPrinter.backMap.contains(name)
        })
        val origName = PrettyPrinter.backMap.get(fieldEntry.get._1).get
        val field = program.fields.find(_.name == origName).get
        fields.update(fieldEntry.get._2.asInstanceOf[ConstantEntry], field)
      }
      case (Seq(valEntry), ConstantEntry("true")) => {
        for ((entry, pred) <- possiblePredicateEntries) {
          val possibleEntry = entry.options.find(_._2 == valEntry)
          if (possibleEntry.isDefined) {
            predicates.update(valEntry.asInstanceOf[ConstantEntry], (pred, possibleEntry.get._1))
          }
        }
      }
    })

    val entries: Seq[HeapEntry] = nonZeroMaskEntries.flatMap{
      case ((receiverEntry, fieldEntry), permEntry) => {
        if (fields.contains(fieldEntry.asInstanceOf[ConstantEntry])) {
          val field = fields.get(fieldEntry.asInstanceOf[ConstantEntry]).get
          val perm = convertPermission(permEntry)
          val value = if (heapEntries.contains((receiverEntry, fieldEntry))) {
            translateValue(heapEntries.get((receiverEntry, fieldEntry)).get, field.typ, model)
          } else {
            VarEntry("?")
          }
          Some(FieldHeapEntry(VarEntry(receiverEntry.asInstanceOf[ConstantEntry].value), field.name, perm, value))
        }else{
          val possiblePred = predicates.get(fieldEntry.asInstanceOf[ConstantEntry])
          if (possiblePred.isDefined){
            val pred = possiblePred.get._1
            val args = possiblePred.get._2
            val translatedArgs = (pred.formalArgs zip args).map({
              case (fArg, arg) => translateValue(arg.asInstanceOf[ValueEntry], fArg.typ, model)
            })
            Some(PredHeapEntry(pred.name, translatedArgs, convertPermission(permEntry)))
          }else{
            None
          }
        }
      }
    }.toSeq

    ExtractedHeap(entries)
  }

  def convertPermission(value: ValueEntry): Rational = {
    value match {
      case ConstantEntry("1.0") => Rational(1, 1)
      case ConstantEntry("0.0") => Rational(0, 1)
      case ApplicationEntry("/", Seq(ConstantEntry(num), ConstantEntry(dem))) => {
        Rational(num.toDouble.toInt, dem.toDouble.toInt)
      }
    }
  }

  def getMapEntries(mapVal: ConstantEntry, model: Model) : Map[(ValueEntry, ValueEntry), ValueEntry] = {
    val lookupEntries = model.entries.get("[3]").get.asInstanceOf[MapEntry]
    val updateEntries = model.entries.get("[4:=]").get.asInstanceOf[MapEntry]
    val result = new mutable.HashMap[(ValueEntry, ValueEntry), ValueEntry]()
    for ((keys, vl) <- lookupEntries.options) {
      if (keys(0) == mapVal) {
        result.update((keys(1), keys(2)), vl)
      }
    }

    // check if we can recover information from previous versions
    val updateEntry = updateEntries.options.find(_._2 == mapVal)
    if (updateEntry.isDefined) {
      val previousMap = updateEntry.get._1(0).asInstanceOf[ConstantEntry]
      val previousMapEntries = getMapEntries(previousMap, model)
      for ((key, vl) <- previousMapEntries) {
        if (!(key._1 == updateEntry.get._1(1) && key._2 == updateEntry.get._1(2))) {
          result.update(key, vl)
        }
      }
    }
    result.toMap
  }

  /**
    *
    * @param originalEntries Entries of the counterexample produced by Boogie
    * @param namesInMember Mapping from Boogie names to Viper names for the Viper member belonging to this error.
    * @return
    */
  def transformModelEntries(model: Model, namesInMember: Map[String, sil.LocalVarDecl]) : Map[String, ExtractedModelEntry] = {
    val originalEntries = model.entries
    val result = mutable.HashMap[String, ExtractedModelEntry]()
    val currentEntryForName = mutable.HashMap[String, String]()
    for ((vname, e) <- originalEntries) {
      var originalName = vname
      if (originalName.startsWith("q@")){
        originalName = originalName.substring(2)
      } else if (originalName.indexOf("@@") != -1){
        originalName = originalName.substring(0, originalName.indexOf("@@"))
      } else if (originalName.indexOf("@") != -1){
        originalName = originalName.substring(0, originalName.indexOf("@"))
      }
      if (PrettyPrinter.backMap.contains(originalName)){
        originalName = PrettyPrinter.backMap.get(originalName).get
        if (namesInMember.contains(originalName)){
          val viperVar = namesInMember.get(originalName).get
          val viperName = viperVar.name
          if (!currentEntryForName.contains(viperName) ||
            isLaterVersion(vname, originalName, currentEntryForName.get(viperName).get)){
            result.update(viperName, translateValue(e.asInstanceOf[ValueEntry], viperVar.typ, model))
            currentEntryForName.update(viperName, vname)
          }
        }
      }
    }
    result.toMap
  }

  /**
    * Heuristically (based on Boogie's naming practices) checks if, of the two Boogie versions of the given
    * original Viper variable name, the first denotes a "later" version (as in, occurring later in the program,
    * therefore containing a more recent value).
    */
  def isLaterVersion(firstName: String, originalName: String, secondName: String) : Boolean = {
    if (secondName == originalName || secondName == "q@" + originalName || secondName.indexOf("@@") != -1){
      true
    } else if (secondName.indexOf("@") != -1 && firstName.indexOf("@@") == -1 && firstName.indexOf("@") != -1) {
      val firstIndex = Integer.parseInt(firstName.substring(firstName.indexOf("@") + 1))
      val secondIndex = Integer.parseInt(secondName.substring(secondName.indexOf("@") + 1))
      firstIndex > secondIndex
    } else {
      false
    }
  }
}
