package viper.carbon.utility

sealed trait LoopGenKind {

}

case class BeforeEnterLoop(loopId: Int) extends LoopGenKind

case class ExitLoops(loopIds: Seq[Int]) extends LoopGenKind

case class Backedge(loopId: Int) extends LoopGenKind
