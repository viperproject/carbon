package viper.carbon

import org.scalatest.concurrent.{Signaler, TimeLimitedTests}
import org.scalatest.time.{Minutes, Span}

class TimeoutPortableCarbonTests extends PortableCarbonTests with TimeLimitedTests {
  override def timeLimit: Span = Span(5*repetitions, Minutes)

  override val defaultTestSignaler: Signaler = Signaler(t => t.interrupt())
}
