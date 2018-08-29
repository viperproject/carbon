//addCommandAlias("tt", "test-only * -- -n ")

ThisBuild / scalaVersion := "2.11.8" //? Not needed

// Import Silver specific project settings
lazy val silver = project in file("src/main/scala/silver")

// Carbon specific project settings
lazy val carbon = (project in file("."))
    .dependsOn(silver % "compile->compile;test->test")
    .settings(
        name := "Carbon",
        organization := "viper",    //? Should those come from Silver?
        version := "1.0-SNAPSHOT",  //? Should come from Silver?
    )




//import sbtassembly.AssemblyPlugin.autoImport._
//import com.typesafe.sbt.packager.archetypes.JavaAppPackaging
//
//object CarbonBuild extends Build {
//  lazy val baseSettings = Seq(
//      scalacOptions in Compile ++= Seq("-deprecation", "-unchecked", "-feature"),
//   )
//
//  lazy val carbon = {
//    var p = Project(
//      id = "carbon",
//      base = file("."),
//      settings = (
//           baseSettings
//        ++ Seq(
//              assemblyJarName in assembly := "carbon.jar",
//              test in assembly := {},
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
