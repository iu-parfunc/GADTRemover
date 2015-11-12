

all: step1 step2

# These steps are really per-package and could be broken up that way
# ------------------------------------------------------------------
step1:
	./GrabNewestPerPackage.hs

step2:
	./UntarFiles.hs

## All that you should need to do is feed it the location of the files here:
step3:
	cd data/2_untarred/
	../../ConnectedDDefs.hs . ../3_ddef_clusters/
# Gather DDefs from each discovered haskell file.
# Organize output in per-package directories.


# ------------------------------------------------------------------

clean:
	rm -rf data/1_only_newest_versions data/2_untarred/ data/3_ddef_clusters/

distclean:
