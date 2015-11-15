

.PHONY: step1 step2 step3 step4 CompileBusted clean distclean


default: scripts
all: scripts step1 step2 step3 step4

# Backpedaling and building scripts as executables:
scripts:
	stack install

# These steps are really per-package and could be broken up that way
# ------------------------------------------------------------------
step1:
	./GrabNewestPerPackage.hs

step2:
	./UntarFiles.hs

## All that you should need to do is feed it the location of the files here:
#
# Gathers DDefs from each discovered haskell file.
# Organize output in per-package directories.
step3:
	cd data/2_untarred && ../../bin/ConnectedDDefs.exe . ../3_ddef_clusters/

# Attempt to compile generated DDefs
step4: CompileBusted
	./bin/CompileBusted.exe data/3_ddef_clusters/ghostbust_data.csv data/4_compiled_ddefs +RTS -N

# ------------------------------------------------------------------

clean:
	stack clean
	rm -rf data/1_only_newest_versions
	rm -rf data/2_untarred
	rm -rf data/3_ddef_clusters
	rm -rf data/4_compiled_ddefs
	rm -rf dist
	rm -f  bin/*

distclean:
