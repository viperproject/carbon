import sbt._
import Keys._
import sbtassembly.Plugin._
import AssemblyKeys._

object CarbonBuild extends Build {
  lazy val baseSettings = (
       Defaults.defaultSettings
    ++ Seq(
          organization := "semper",
          version := "1.0-SNAPSHOT",
          scalaVersion := "2.10.1",
          scalacOptions in Compile ++= Seq("-deprecation", "-unchecked", "-feature"),
          libraryDependencies += "org.rogach" %% "scallop" % "0.8.1",
          libraryDependencies += "org.jgrapht" % "jgrapht-jdk1.5" % "0.7.3"
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
              testOptions in Test += Tests.Argument(TestFrameworks.ScalaTest, "-oD"),
              traceLevel := 20,
              maxErrors := 6,
              classDirectory in Test <<= classDirectory in Compile,
              libraryDependencies ++= externalDep))
    )
    for (dep <- internalDep) {
      p = p.dependsOn(dep)
    }
    p
  }

  // On the build-server, we cannot have all project in the same directory, and thus we use the publish-local mechanism for dependencies.
  def isBuildServer = sys.env.contains("BUILD_TAG") // should only be defined on the build server
  def internalDep = if (isBuildServer) Nil else Seq(dependencies.silSrc % "compile->compile;test->test")
  def externalDep = {
    (if (isBuildServer) Seq(dependencies.sil) else Nil)
  }

  object dependencies {
    lazy val sil = "viper" %% "silver" %  "0.1-SNAPSHOT" % "compile->compile;test->test"
    lazy val silSrc = RootProject(new java.io.File("../silver"))
  }
}
