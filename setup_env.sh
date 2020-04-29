#!/bin/sh

#SCRIPT=$(readlink -f "$0")
SCRIPT=$(readlink -f -- "$0")
SCRIPTPATH=$(dirname "$SCRIPT")

export AFLPLUSPLUSSMART=$SCRIPTPATH
export PATH=$PATH:$AFLPLUSPLUSSMART:$AFLPLUSPLUSSMART/peach-3.0.202-source/output/linux_x86_64_debug/bin
export AFL_PATH=$AFLPLUSPLUSSMART
export LD_LIBRARY_PATH=/usr/local/lib
