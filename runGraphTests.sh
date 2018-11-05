#!/bin/bash

BOOGIE_EXE="${BOOGIE_EXE:-$BOOGIE_HOME/Boogie.exe}"
Z3_EXE="${Z3_EXE:-$BOOGIE_HOME/z3.exe}"

export Z3_EXE
export BOOGIE_EXE

sbt "test:runMain org.scalatest.tools.Runner -o -s viper.carbon.GraphTests"
