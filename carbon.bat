@echo off
SetLocal EnableDelayedExpansion

set ROOT_DIR=%~dp0
set JAVA_EXE=java

if "%IVY_HOME%"=="" (
	REM Environment variable IVY_HOME not pre-defined; checks on classpath below will catch a false definition here
	set IVY_HOME=%USERPROFILE%\.ivy2
)
set SBT_HOME=%USERPROFILE%\.sbt

set SCALA_VERSION=2.10.0
set SCALA_VRS=2.10

set __CP.SCALA_LIB="%SBT_HOME%\boot\scala-%SCALA_VERSION%\lib\scala-library.jar"
set __CP.SCALA_LIB2="%SBT_HOME%\boot\scala-%SCALA_VERSION%\lib\scala-reflect.jar"
set __CP.KIAMA_LIB="%IVY_HOME%\cache\com.googlecode.kiama\kiama_%SCALA_VRS%\jars\kiama_%SCALA_VRS%-1.5.1.jar"
set __CP.SCALOP_LIB="%IVY_HOME%\cache\org.rogach\scallop_%SCALA_VRS%\jars\scallop_%SCALA_VRS%-0.9.4.jar"
set __CP.JGRAPH_LIB="%IVY_HOME%\cache\org.jgrapht\jgrapht-jdk1.5\jars\jgrapht-jdk1.5-0.7.3.jar"
set __CP.CARBON="%ROOT_DIR%target\scala-%SCALA_VRS%\classes"
set __CP.SIL="%ROOT_DIR%..\sil\target\scala-%SCALA_VRS%\classes"

set CP=
for /f "tokens=2* delims=.=" %%A in ('set __CP.') do (
	if not exist %%B (
		echo %%B does not exist.
		goto :exit_with_error
	) else (
		set CP=!CP!;%%B
	)
)

set CARBON_MAIN=semper.carbon.Carbon

set CARBON_OPTS=%CARBON_OPTS% %*

::-Xss16M 
set CMD=%JAVA_EXE% -Xss30M -cp %CP% %CARBON_MAIN% %CARBON_OPTS%

call %CMD%

exit /B 0

:exit_with_error
exit /B 1
