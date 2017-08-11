#!/bin/bash

# To verify a SIL file 'test.sil', run './carbon.sh test.sil'.
#
# The script expects the environment variable $BOOGIE_HOME to be set, e.g.
# export BOOGIE_HOME=/home/severinh/Software/boogie
# Consider adding such a line to your ~/.profile.
#
# Ensure that the file 'Boogie.exe' in the Boogie folder is executable.
# Note that the 'z3.exe' file must be located inside the Boogie folder.
#
# Alternatively you could also just set the BOOGIE_EXE and Z3_EXE to point o
# the executable files

set -e

BOOGIE_EXE="${BOOGIE_EXE:-$BOOGIE_HOME/Boogie.exe}"
Z3_EXE="${Z3_EXE:-$BOOGIE_HOME/z3.exe}"

export Z3_EXE
export BOOGIE_EXE

BASEDIR="$(realpath `dirname $0`)"

CP_FILE="$BASEDIR/carbon_classpath.txt"

if [ ! -f $CP_FILE ]; then
    (cd $BASEDIR; sbt "export runtime:dependencyClasspath" | tail -n1 > $CP_FILE)
fi

java -Xss30M -cp "`cat $CP_FILE`" viper.carbon.Carbon $@
