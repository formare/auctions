# $Id$
# 
# Auction Theory Toolbox
# 
# Authors:
# * Manfred Kerber <m.kerber@cs.bham.ac.uk>
# * Christoph Lange <math.semantic.web@gmail.com>
# * Colin Rowat <c.rowat@bham.ac.uk>
# 
# Licenced under
# * ISC License (1-clause BSD License)
# See LICENSE file for details

# TODO CL: convert to sbt: http://www.scala-sbt.org/

CombinatorialVickreyAuctionCATS.class: \
  CombinatorialVickreyAuctionCATS.scala \
  CombinatorialVickreyAuction/nVCG_CaseChecker.class
	scalac $<

# need to compile all sources at once to avoid missing dependencies
CombinatorialVickreyAuction/nVCG_CaseChecker.class: CombinatorialVickreyAuction.scala nVCG_CaseChecker.scala
	scalac $$(perl -lne 'print "$$1.scala" if /^object ([^ ]+) {/' $<)

nVCG_CaseChecker.scala: CombinatorialVickreyAuction.scala
	./split-scala-modules.pl < $<

CombinatorialVickreyAuctionCATS.jar: CombinatorialVickreyAuctionCATS.class
	jar cf $@ CombinatorialVickreyAuction/ CombinatorialVickreyAuctionCATS*.class

# TODO CL: automate locating scala-library.jar
CombinatorialVickreyAuctionCATS.zip: CombinatorialVickreyAuctionCATS.jar example.cats README
	zip -j $@ /opt/scala-2.10.1/lib/scala-library.jar $^
