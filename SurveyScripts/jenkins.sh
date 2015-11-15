#!/bin/bash

# Script launched by Jenkins to do the full survey.
set -xe

# Just in case we are run in a dirty directory:
make clean

# First, set up directories:
# --------------------------------------------------------------------------------

# Try two places:
localstorage=/home.local/$USER/
if ! [ -d $localstorage ]; then
    localstorage=$HOME/local/
fi

if ! [ -d $localstorage ]; then
    echo "Local storage not found."
    exit 1
fi

# input
# ------------------------------

origdir=$localstorage/hackage_all_tarballs/
mkdir -p ./data/

inputdir=./data/0_hackage_all_tarballs

if [ "$SKIPTO" == "" ]; then
    # Run the WHOLE data set.
    ln -s -f $origdir $inputdir
else
    echo "Running on a SUBRANGE of input packages.  "
    ls $origdir/ | sort > full_file_list.txt
    echo "The FULL data set discovered has this many tarballs:"`wc -l full_file_list.txt`

    # Annoyingly, tail is zero-based
    onebased=$((SKIPTO + 1))
    tail -n+${onebased} full_file_list.txt > all_following.txt
    if [ "$RUNONLY" == "" ]; then
        cp all_following.txt my_chunk.txt
    else
        head -n${RUNONLY} all_following.txt > my_chunk.txt
    fi

    rm -rf $inputdir
    mkdir -p $inputdir
    echo "Here's the size of my_chunk.txt: "`wc -l my_chunk.txt`
    for file in `cat my_chunk.txt`; do
        echo "Linking: $file"
        ln -s "$origdir/$file" "$inputdir/$file"
    done
fi

# intermediates
# ------------------------------

scratch=$localstorage/GhostbusterSurvey/
mkdir -p $scratch

intermediates="1_only_newest_versions 2_untarred 3_ddef_clusters 4_compiled_ddefs"
for dir in $intermediates; do
    mkdir -p $scratch/$dir
    ln -s -f $scratch/$dir ./data/$dir
done

# final output location
# ------------------------------

outdir=`pwd`/collected_output_stats_`date +"%s"`/

mkdir -p "$outdir"
uname -a | tee "$outdir/uname.txt"

# Next, run the pipeline:
# --------------------------------------------------------------------------------

time make all

# We *could* do this collection in between steps...
for csvfile in `find ./data/ -name "*.csv"`; do
    cp "$csvfile" "$outdir/"
done
