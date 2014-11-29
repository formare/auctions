#!/bin/sh -eux
# Auction Theory Toolbox (http://formare.github.io/auctions/)

# Author: Marco B. Caminati http://caminati.co.nr

# Dually licenced under
# * Creative Commons Attribution (CC-BY) 3.0
# * ISC License (1-clause BSD License)
# See LICENSE file for details
# (Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
# Isabelle build script

i=/home/staff/caminamb/apps/Isabelle2014

rm -f ./ROOT
rm -rf ./document ./output

$i/bin/isabelle mkroot -d -n Vcg
sed -i -e "/theories *$/ a CombinatorialAuction" ROOT
sed -i -r -e 's/^ *\\author *\{.*\} *$/\\author\{M. B. Caminati, C. Lange, M. Kerber, C. Rowat\}/' document/root.tex
$i/bin/isabelle build -c -v -j 5 -D . 

