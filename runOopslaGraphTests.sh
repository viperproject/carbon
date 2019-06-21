#!/bin/bash

unameOut="$(uname -s)"
case "${unameOut}" in
    Linux*)     machine=Linux;;
    Darwin*)    machine=Mac;;
    CYGWIN*)    machine=Cygwin;;
    MINGW*)     machine=MinGw;;
    *)          machine="UNKNOWN:${unameOut}"
esac

if [ "$machine" = "Mac" ]; then 
    BOOGIE_EXE=/usr/local/Viper/boogie/Binaries/Boogie
else 
    BOOGIE_EXE=/usr/local/Viper/boogie/Binaries/Boogie.exe
fi

Z3_EXE=/usr/local/Viper/z3/bin/z3

export Z3_EXE
export BOOGIE_EXE

sbt "test:runMain org.scalatest.tools.Runner -o -s viper.carbon.GraphOopslaTests"
