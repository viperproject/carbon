package viper.carbon.modules.impls

import viper.carbon.modules.StateModule

object LabelHelper {

  /**
    * Would prefer to use a method that takes a state module as input, but since it would have a dependent return type
    * (stateModule.StateSnapshot) IntelliJ can report false errors for callers.
    * @param labelName
    * @param freshTempStateNoSideEffect provide a fresh state without any side effects
    * @param getSnapshot obtain a stored snapshot
    * @param storeSnapshot store a snapshot
    * @tparam T: state snapshot representation
    * @return state snapshot associated with input label
    */
  def getLabelState[T](labelName: String,
                       freshTempStateNoSideEffect: String => T,
                       getSnapshot: String => Option[T],
                       storeSnapshot: (String, T) => Unit): T = {
    getSnapshot(labelName) match {
      case Some(labelState) => labelState
      case None => {
        val s = freshTempStateNoSideEffect("Label"+labelName)
        storeSnapshot(labelName,s)
        s
      }
    }
  }

}
