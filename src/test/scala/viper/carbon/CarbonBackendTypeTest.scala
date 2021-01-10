package viper.carbon

import viper.silver.testing.BackendTypeTest
import viper.silver.verifier.Verifier

class CarbonBackendTypeTest extends BackendTypeTest {
  override val verifier: Verifier = CarbonVerifier()
}
