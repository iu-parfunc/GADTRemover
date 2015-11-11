
SurveyScripts
=============

This directory contains scripts for running a survey of datatypes in
Haskell packages.

It manages data in the `./data` subdirectory, which should generally
be a symlink to some big, local. storage.  Here's a cheat sheet for
what the different steps of processing are:

 * `./data/0_all_hackage_tarballs`
 * `./data/1_only_newest_versions`

The Makefile drives the different stages of the processing pipeline.
