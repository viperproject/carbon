// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

// Import general settings from Silver
lazy val silver = project in file("silver")

// Carbon specific project settings
lazy val carbon = (project in file("."))
    .dependsOn(silver % "compile->compile;test->test")
    .disablePlugins(plugins.JUnitXmlReportPlugin)
    .settings(
        // General settings
        name := "Carbon",
        organization := "viper",
        version := "1.0-SNAPSHOT",

        // Fork test to a different JVM than SBT's, avoiding SBT's classpath interfering with
        // classpath used by Scala's reflection.
        Test / fork := true,
        Test / testOptions += Tests.Argument(TestFrameworks.ScalaTest, "-u", "target/test-reports", "-oD"),

		Compile / fork := true,

        // Assembly settings
        assembly / assemblyJarName := "carbon.jar",             // JAR filename
        assembly / mainClass := Some("viper.carbon.Carbon"),    // Define JAR's entry point
        assembly / test := {},                                  // Prevent testing before packaging
    )
