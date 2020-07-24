package viper.carbon

import viper.silver.testing.SMTTypeTest
import viper.silver.verifier.Verifier

class CarbonSMTTypeTest extends SMTTypeTest {
  override val verifier: Verifier = CarbonVerifier()
}
