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

# Hack, for now assume Stack has installed GHC:
GHC=~/.stack/programs/x86_64-linux/ghc-7.10.2/bin/ghc

$RUN Remover2/examples/MiniFeldspar.hs Remover2/examples/MiniFeldspar_busted.hs

$GHC Remover2/examples/MiniFeldspar_busted.hs
