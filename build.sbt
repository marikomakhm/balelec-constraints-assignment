scalaVersion := "2.11.5"

scalacOptions ++= Seq(
  "-deprecation",
  "-unchecked",
  "-optimise",
  "-Yinline-warnings"
)

fork := true

javaOptions += "-Xmx2G"

parallelExecution in Test := false

libraryDependencies ++= Seq(
  "org.scalatest" %% "scalatest" % "3.0.1" % "test,grading"
)

lazy val Grading = config("grading").extend(Test)

lazy val root = Project("root", file("."))
  .configs( Grading )
  .settings( inConfig(Grading)(Defaults.testSettings) : _*)

sourceDirectory in Grading := baseDirectory.value / ".." / ".." / "solution" / "src" / "test"
