#!/bin/bash

# This is specific to our testing setup at IU:
ENVSCRIPT=$HOME/rn_jenkins_scripts/acquire_ghc.sh
if [ -f "$ENVSCRIPT" ]; then source "$ENVSCRIPT"; fi
if [ "$CABAL" == ""  ]; then CABAL=cabal; fi

$CABAL sandbox init

OPTS=" -j --ghc-options=-j3 --run-tests "

# For now just make sure everything installs:
$CABAL install ./GADTRemover ./GADT_CastChallenge $OPTS
