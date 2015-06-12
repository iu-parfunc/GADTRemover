#!/bin/bash

set -xe

# This is specific to our testing setup at IU:
ENVSCRIPT=$HOME/rn_jenkins_scripts/acquire_ghc.sh
if [ -f "$ENVSCRIPT" ]; then source "$ENVSCRIPT"; fi
if [ "$CABAL" == ""  ]; then CABAL=cabal; fi

which -a $CABAL
$CABAL --version

$CABAL sandbox init

OPTS=" -j --ghc-options=-j3 --run-tests "

# For now just make sure everything installs:
$CABAL install ./GADTRemover ./GADT_CastChallenge $OPTS

cd ./GADT_CastChallenge/
$CABAL sandbox init --sandbox=../.cabal-sandbox/
$CABAL test
