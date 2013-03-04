import sbt._
import Keys._

object CarbonBuild extends Build {
  lazy val baseSettings = (
       Defaults.defaultSettings
    ++ Seq(
          organization := "semper",
          version := "1.0-SNAPSHOT",
          scalaVersion := "2.10.0",
          scalacOptions in Compile ++= Seq("-deprecation", "-unchecked", "-feature"),
          libraryDependencies += "org.rogach" %% "scallop" % "0.8.1"
       )
  )

  lazy val carbon = {
    Project(
      id = "carbon",
      base = file("."),
      settings = (
           baseSettings
        ++ Seq(
              name := "Carbon",
              testOptions in Test += Tests.Argument(TestFrameworks.ScalaTest, "-oD"),
              traceLevel := 10,
              maxErrors := 6,
              classDirectory in Test <<= classDirectory in Compile,
              libraryDependencies ++= Seq()))
    ).dependsOn(RootProject(new java.io.File("../sil")))
  }
}
