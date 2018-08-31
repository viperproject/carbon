//addCommandAlias("tt", "test-only * -- -n ")

ThisBuild / scalaVersion := "2.11.8" //? Not needed

// Import Silver specific project settings
//lazy val silver = project in file("src/main/scala/silver") //? Also works
lazy val silver = project in file("silver")

// Carbon subproject settings
lazy val carbon = (project in file("."))
    .dependsOn(silver % "compile->compile;test->test")
    .settings(
        // General settings
        name := "Carbon",
        organization := "viper",                     //? Should those come from Silver?
        version := "1.0-SNAPSHOT",                   //? Should come from Silver?

        // Testing
        //? Test / classDirectory := (Compile / classDirectory).value,
        //? Test / testOptions += Tests.Argument(TestFrameworks.ScalaTest, "-oD"),

        // Assembly configuration
        assembly / assemblyJarName := "carbon.jar",
        assembly / mainClass := Some("viper.carbon.Carbon"),
        assembly / test := {},  //? Check if necessary
//        assembly / assemblyMergeStrategy := {       //? Should not be necessary, but there's no way if silver, carbon and silicon aren't neasted
//            case "viper/silver/ast/FuncLikeApp.class" => MergeStrategy.last
//            case x => (assembly / assemblyMergeStrategy).value(x)
//        }
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
//
//  object dependencies {
//    lazy val sil = "viper" %% "silver" %  "0.1-SNAPSHOT" % "compile->compile;test->test"
//  }
//}
