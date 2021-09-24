package viper.carbon.boogie

import viper.carbon.verifier.FailureContextImpl
import viper.silver.verifier.{AbstractError, Counterexample, FailureContext, Model, ModelEntry, SimpleCounterexample, VerificationError}

import scala.collection.mutable

/**
  * Transforms a counterexample returned by Boogie back to a Viper counterexample.
  */
object BoogieModelTransformer {

  /**
    * Adds a counterexample to the given error if one is available.
    */
  def transformCounterexample(e: AbstractError, names: Map[String, Map[String, String]]) : Unit = {
    if (e.isInstanceOf[VerificationError] && ErrorMemberMapping.mapping.contains(e.asInstanceOf[VerificationError])){
      val ve = e.asInstanceOf[VerificationError]
      val methodName = ErrorMemberMapping.mapping.get(ve).get.name
      val namesInMember = names.get(methodName).get.map(e => e._2 -> e._1)
      val originalEntries = ve.failureContexts(0).counterExample.get.model.entries

      val model = transformModelEntries(originalEntries, namesInMember)
      ve.failureContexts = Seq(FailureContextImpl(Some(SimpleCounterexample(model))))
    }
  }

  /**
    *
    * @param originalEntries Entries of the counterexample produced by Boogie
    * @param namesInMember Mapping from Boogie names to Viper names for the Viper member belonging to this error.
    * @return
    */
  def transformModelEntries(originalEntries: Map[String, ModelEntry], namesInMember: Map[String, String]) : Model = {
    val newEntries = mutable.HashMap[String, ModelEntry]()
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
          val viperName = namesInMember.get(originalName).get
          if (!currentEntryForName.contains(viperName) ||
            isLaterVersion(vname, originalName, currentEntryForName.get(viperName).get)){
            newEntries.update(viperName, e)
            currentEntryForName.update(viperName, vname)
          }
        }
      }
    }
    Model(newEntries.toMap)
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
