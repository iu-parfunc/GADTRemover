#!/bin/bash

# Script launched by Jenkins to do the full survey.
set -xe

# Just in case we are run in a dirty directory:
make clean

# First, set up directories:
# --------------------------------------------------------------------------------

localstorage=/home.local/$USER/
# localstorage=$HOME/local/

if ! [ -d $localstorage ]; then
    echo "Local storage not found."
    exit 1
fi

inputdir=$localstorage/hackage_all_tarballs/
scratch=$localstorage/GhostbusterSurvey/

mkdir -p ./data/
mkdir -p $scratch

ln -s -f $inputdir ./data/0_hackage_all_tarballs

intermediates="1_only_newest_versions 2_untarred 3_ddef_clusters 4_compiled_ddefs"

for dir in $intermediates; do
    mkdir -p $scratch/$dir
    ln -s -f $scratch/$dir ./data/$dir
done

outdir=`pwd`/collected_output_stats_`date +"%s"`/

mkdir -p "$outdir"
uname -a > "$outdir/uname.txt"

function collect() {
    find ./data/ -name "*.csv" | xargs -i cp {} $outdir/
}

# Next, run the whole pipeline:
# --------------------------------------------------------------------------------

time make all

# We *could* do this in between steps...
collect
