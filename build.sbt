// Import general settings from Silver
lazy val silver = project in file("silver")

// Carbon specific project settings
lazy val carbon = (project in file("."))
    .dependsOn(silver % "compile->compile;test->test")
    .settings(
        // General settings
        name := "Carbon",
        organization := "viper",
        version := "1.0-SNAPSHOT",

        // Assembly settings
        assembly / assemblyJarName := "carbon.jar",             // JAR filename
        assembly / mainClass := Some("viper.carbon.Carbon"),    // Define JAR's entry point
        assembly / test := {},                                  // Prevent testing before packaging
        // Make all implementations of SilSuite discoverable by the SBT testing framework
        testOptions in Test += Tests.Argument(TestFrameworks.ScalaTest, "-oD"),
    )
