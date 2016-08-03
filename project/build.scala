import sbt._
import Keys._
import sbtassembly.Plugin._
import AssemblyKeys._

object CarbonBuild extends Build {
  lazy val baseSettings = (
       Defaults.defaultSettings
    ++ Seq(
          organization := "viper",
          version := "1.0-SNAPSHOT",
          scalaVersion := "2.11.7",
          scalacOptions in Compile ++= Seq("-deprecation", "-unchecked", "-feature"),
          libraryDependencies += "org.rogach" %% "scallop" % "0.9.5",
          libraryDependencies += "org.jgrapht" % "jgrapht-core" % "0.9.0"
//          libraryDependencies += "com.googlecode.kiama" % "kiama_2.11" % "1.8.0"

       )
  )

  lazy val carbon = {
    var p = Project(
      id = "carbon",
      base = file("."),
      settings = (
           baseSettings
        ++ assemblySettings
        ++ Seq(
              name := "Carbon",
              jarName in assembly := "carbon.jar",
              test in assembly := {},
              javaOptions in Test += "-Xss128m",
              testOptions in Test += Tests.Argument(TestFrameworks.ScalaTest, "-oD"),
              traceLevel := 20,
              maxErrors := 6,
              classDirectory in Test <<= classDirectory in Compile,
              libraryDependencies ++= externalDep
              //fork in Test := true
           ))
    )
    for (dep <- internalDep) {
      p = p.dependsOn(dep)
    }
    p
  }

  // On the build-server, we cannot have all project in the same directory, and thus we use the publish-local mechanism for dependencies.
  def isBuildServer = sys.env.contains("BUILD_TAG") // should only be defined on the build server
  def internalDep = if (isBuildServer) Nil else Seq(dependencies.silSrc % "compile->compile;test->test")
  def externalDep = if (isBuildServer) Seq(dependencies.sil) else Nil

  object dependencies {
    lazy val sil = "viper" %% "silver" %  "0.1-SNAPSHOT" % "compile->compile;test->test"
    lazy val silSrc = RootProject(new java.io.File("../silver"))
  }
}
