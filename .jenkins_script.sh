#!/bin/bash

set -xe

# This is specific to our testing setup at IU:
if [ -f "$ENVSCRIPT" ]; then source "$ENVSCRIPT"; fi
if [ "$STACK" == ""  ]; then STACK=stack; fi
which -a $STACK
$STACK --version

time $STACK setup
time $STACK test

# Then we run some standalone tests:
RUN="stack exec ghostbust --"

if [ `uname` == "Darwin" ]; then
    OS=osx
else
    OS=linux
fi

# Peek at where stack has put it:
find -name ghostbust
# Test run:
$RUN -h

# Hack, for now assume Stack has installed GHC:
GHC=~/.stack/programs/x86_64-${OS}/ghc-7.10.2/bin/ghc

# First, run one example by hand.

$RUN Remover2/examples/MiniFeldspar.hs Remover2/examples/output/MiniFeldspar_Busted.hs
$GHC Remover2/examples/output/MiniFeldspar_Busted.hs

# Second, run in fuzz test mode:

rm -rf Remover2/examples/output/
for file in `ls Remover2/examples/*.hs`; do
    $RUN --fuzz $file
done

