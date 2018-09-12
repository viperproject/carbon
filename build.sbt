// Import general settings from Silver
lazy val silver = project in file("silver")

// Carbon specific project settings
lazy val carbon = (project in file("."))
    .dependsOn(silver % "compile->compile;test->test")
    .settings(
        // General settings
        name := "Carbon",
        organization := "viper",                     //? Should those come from Silver?
        version := "1.0-SNAPSHOT",                   //? Should come from Silver?

        // Assembly settings
        assembly / assemblyJarName := "carbon.jar",             // JAR filename
        assembly / mainClass := Some("viper.carbon.Carbon"),    // Define JAR's entry point
        assembly / test := {},                                  // Prevent testing before packaging
    )



//  lazy val baseSettings = Seq(
//      scalacOptions in Compile ++= Seq("-deprecation", "-unchecked", "-feature"),
//   )
//
//  lazy val carbon = {
//    var p = Project(
//      settings = (
//           baseSettings
//        ++ Seq(
//              testOptions in Test += Tests.Argument(TestFrameworks.ScalaTest, "-oD"),
//              traceLevel := 20,
//              maxErrors := 6,
//              classDirectory in Test <<= classDirectory in Compile,
//              libraryDependencies ++= externalDep,
//              fork in run := true
//              //fork in Test := true
//           ))
//    )
//    for (dep <- internalDep) {
//      p = p.dependsOn(dep)
//    }
//    p.enablePlugins(JavaAppPackaging)
//  }
//
//  // On the build-server, we cannot have all project in the same directory, and thus we use the publish-local mechanism for dependencies.
//  def isBuildServer = sys.env.contains("BUILD_TAG") // should only be defined on the build server
//  def internalDep = if (isBuildServer) Nil else Seq(dependencies.silSrc % "compile->compile;test->test")
//  def externalDep = if (isBuildServer) Seq(dependencies.sil) else Nil
