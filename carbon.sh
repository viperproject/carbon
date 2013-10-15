#!/bin/bash

# To verify a SIL file 'test.sil', run './carbon.sh test.sil'.
#
# The script expects the environment variable $BOOGIE_HOME to be set, e.g.
# export BOOGIE_HOME=/home/severinh/Software/boogie
# Consider adding such a line to your ~/.profile.
#
# Ensure that the file 'Boogie.exe' in the Boogie folder is executable.
# Note that the 'z3.exe' file must be located inside the Boogie folder.

export BOOGIE_EXE=$BOOGIE_HOME/Boogie.exe
export Z3_EXE=$BOOGIE_HOME/z3.exe

sbt "run-main semper.carbon.Carbon $@"