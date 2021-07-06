#!/bin/bash

BOOGIE_EXE=/usr/local/Viper/boogie/Binaries/Boogie
Z3_EXE=/usr/local/Viper/z3/bin/z3

export Z3_EXE
export BOOGIE_EXE

sbt "test:runMain org.scalatest.tools.Runner -o -s viper.carbon.GraphTests"
