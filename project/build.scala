import sbt._
import Keys._
import sbtassembly.AssemblyPlugin.autoImport._
import com.typesafe.sbt.packager.archetypes.JavaAppPackaging

object CarbonBuild extends Build {
  lazy val baseSettings = Seq(
      organization := "viper",
      version := "1.0-SNAPSHOT",
      scalaVersion := "2.11.8",
      scalacOptions in Compile ++= Seq("-deprecation", "-unchecked", "-feature"),
      excludeFilter in unmanagedResources := {
        new SimpleFileFilter(_.getCanonicalPath endsWith "logback.xml")
      },
      libraryDependencies += "org.rogach" %% "scallop" % "2.0.7",
      libraryDependencies += "org.jgrapht" % "jgrapht-core" % "0.9.1"
   )

  lazy val carbon = {
    var p = Project(
      id = "carbon",
      base = file("."),
      settings = (
           baseSettings
        ++ Seq(
              name := "Carbon",
              jarName in assembly := "carbon.jar",
              test in assembly := {},
              testOptions in Test += Tests.Argument(TestFrameworks.ScalaTest, "-oD"),
              traceLevel := 20,
              maxErrors := 6,
              classDirectory in Test <<= classDirectory in Compile,
              libraryDependencies ++= externalDep//,
              //fork in Test := true
           ))
    )
    for (dep <- internalDep) {
      p = p.dependsOn(dep)
    }
    p.enablePlugins(JavaAppPackaging)
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
