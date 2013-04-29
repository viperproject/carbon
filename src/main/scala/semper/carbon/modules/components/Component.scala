package semper.carbon.modules.components

/**
 * Common trait for components.
 *
 * @author Stefan Heule
 */
trait Component {
  /** The list of other components which need to come after this component. */
  var comesBefore: Seq[Any] = Nil
  /** The list of other components after which this component will be used. */
  var comesAfter: Seq[Any] = Nil
}
