#!/bin/sh
#
# Re-generate JSON state graphs for specs that are used for "oracle tests" i.e.
# testing equivalence between TLC output and Javascript TLA interpreter output.
#

tlc="java -cp ../../tla2tools-checkall.jar tlc2.TLC"
for spec in `ls *.tla`; do
    $tlc -deadlock -metadir "states/$spec" -dump json $spec.json -noGenerateSpecTE $spec
done
