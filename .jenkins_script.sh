#!/bin/bash

set -xe

# This is specific to our testing setup at IU:
if [ -f "$ENVSCRIPT" ]; then source "$ENVSCRIPT"; fi
if [ "$STACK" == ""  ]; then STACK=stack; fi
which -a $STACK
$STACK --version

$STACK setup
$STACK test
