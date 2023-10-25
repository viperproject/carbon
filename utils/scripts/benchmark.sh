#!/bin/bash

PROGRAM_NAME=${0##*/} # https://stackoverflow.com/a/3588939

PAUSE="false"
CARBONTESTS_REPETITIONS=10
CARBONTESTS_TIMEOUT="180" # in seconds
CARBONTESTS_RANDOMIZE_Z3="false"
CARBONTESTS_CSV="benchmark_$(date +%Y-%m-%d_%H-%M).csv"
CARBONTESTS_WARMUP=
CARBONTESTS_INCL_FILE=
CARBONTESTS_TARGET=

function usage() {
  echo "Usage:"
  echo "  $PROGRAM_NAME [options] <path/to/target/files/>";
  echo
  echo "Options:"
  echo "  -h, --help"
  echo "  -p, --pause [true|false] (default: $PAUSE, if empty: true)"
  echo "  -w, --warmup-directory <path/to/warmup/files/> (optional)"
  echo "  -i, --includes <path/to/file.txt> (optional)"
  echo "  -r, --repetitions <n> (default: $CARBONTESTS_REPETITIONS)"
  echo "  -c, --csv-file <path/to/file.csv> (default: $CARBONTESTS_CSV)"
  echo "  -t, --timeout <seconds> (default: $CARBONTESTS_TIMEOUT)"
  echo "  -z, --randomize-z3 [true|false] (default: $CARBONTESTS_RANDOMIZE_Z3, if empty: true)"
}

function die() {
  EXIT_CODE=$1
  shift
  echo $@ >&2
  exit $EXIT_CODE
}

function quit_or_continue() {
  read -p "Press Q to abort, any other key to continue ..." -n 1 -s KEY
  echo
  if [[ ${KEY^^} == "Q" ]]; then exit; fi # https://stackoverflow.com/a/32210715
}

function set_boolean_flag() {
  local -n REFVAR=$1 # https://stackoverflow.com/a/50281697

  if [[ $3 == "" ]]; then
    REFVAR="true"
  else
    [[ $3 == "true" ]] || [[ $3 == "false" ]] || die 2 "Option '$2' takes arguments 'true' or 'false', but got '$3'"
    REFVAR=$3
  fi  
}

# Declare valid arguments and parse provided ones
TEMP=$(getopt \
-n $PROGRAM_NAME \
-o hp::r:w:i:c:t:z:: \
--long \
pause::,\
repetitions:,\
warmup-directory:,\
csv-file:,\
timeout:,\
randomize-z3:,\
includes:,\
help \
-- "$@")
# --quiet \  ## suppress getopt errors

# if [ $? -ne 0 ]; then
#   echo "Error parsing arguments. Try $PROGRAM_NAME --help" >&2
#   exit 2
# fi
[ $? -eq 0 ] || { echo; usage; exit 2; }

eval set -- "$TEMP"
while true; do
  case $1 in
    -h|--help) usage; exit 0 ;;
    -p|--pause)
      set_boolean_flag PAUSE $1 $2
      shift ;;    
    -r|--repetitions) CARBONTESTS_REPETITIONS=$2; shift ;;
    -w|--warmup-directory) CARBONTESTS_WARMUP=$2; shift ;;
    -i|--includes) CARBONTESTS_INCL_FILE=$2; shift ;;
    -c|--csv-file) CARBONTESTS_CSV=$2; shift ;;
    -t|--timeout) CARBONTESTS_TIMEOUT=$2; shift ;;
    -z|--randomize-z3)
      set_boolean_flag CARBONTESTS_RANDOMIZE_Z3 $1 $2
      shift ;;
    --) shift; break ;; # no more arguments to parse                                
    *) die 2 "Unhandled option '$1'" ;;
  esac
  shift
done

# echo "Trailing arguments \$@: '$@'"

CARBONTESTS_TARGET=$@

([[ $CARBONTESTS_TARGET != "" ]] && [[ -d $CARBONTESTS_TARGET ]]) || die 1 "Target '$CARBONTESTS_TARGET' is not a directory"

# http://mywiki.wooledge.org/BashFAQ/050
SBT_ARGS="
  test:runMain 
  -DCARBONTESTS_TARGET=$CARBONTESTS_TARGET
  -DCARBONTESTS_WARMUP=$CARBONTESTS_WARMUP 
  -DCARBONTESTS_REPETITIONS=$CARBONTESTS_REPETITIONS 
  -DCARBONTESTS_CSV=$CARBONTESTS_CSV 
  -DCARBONTESTS_INCL_FILE=$CARBONTESTS_INCL_FILE 
  -DCARBONTESTS_TIMEOUT=$CARBONTESTS_TIMEOUT   
  -DCARBONTESTS_RANDOMIZE_Z3=$CARBONTESTS_RANDOMIZE_Z3   
  org.scalatest.tools.Runner 
  -o -s 
  viper.carbon.PortableCarbonTests"

if [[ $PAUSE == "true" ]]; then
  echo "About to execute sbt with the following arguments: $SBT_ARGS"
  echo
  quit_or_continue
fi

sbt "$SBT_ARGS"
