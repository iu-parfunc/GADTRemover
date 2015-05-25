This repository contains a couple of related experiments:

#### Build status:

 * Jenkins: [![Build Status](http://tester-lin.soic.indiana.edu:8080/buildStatus/icon?job=ghostbuster_gadts)](http://tester-lin.soic.indiana.edu:8080/job/ghostbuster_gadts/)

# GADTRemover and GADTCreator

The GADTRemover is a tool for transforming Haskell code that makes use
of GADTs into one that does not.  Conversely, the GADTCreator takes a
type system and create the corresponding GADT definition.


# GADT_CastChallenge

A minutarized, handwritten version of the challenge found in the
Accelerate AST.  That is, given a type-levele DeBruijn (GADT) AST, how
can you write a downcast to a Haskell98 AST followed by an upcast?
This represents a minature but complete version of the code we would
like to ultimately generate, using all the corresponding Haskell type
system features / extensions.
