#!/bin/bash

set -xe

# This is specific to our testing setup at IU:
if [ "$JENKINS_GHC" == ""  ]; then JENKINS_GHC=7.8.4; fi
ENVSCRIPT=$HOME/rn_jenkins_scripts/acquire_ghc.sh
if [ -f "$ENVSCRIPT" ]; then source "$ENVSCRIPT"; fi
if [ "$CABAL" == ""  ]; then CABAL=cabal; fi

which -a $CABAL
$CABAL --version

$CABAL sandbox init

OPTS=" -j --ghc-options=-j3 --enable-tests --only-dependencies "

PKGS="./GADTRemover ./CastChallenge ./Remover2"

# Install and run-tests in one step:
$CABAL install $PKGS $OPTS

top=`pwd`
for pkg in $PKGS; do
    cd "$pkg"
    $CABAL sandbox init --sandbox=../.cabal-sandbox/
    $CABAL configure --enable-tests
    $CABAL test --show-details=always
    cd "$top";
done
