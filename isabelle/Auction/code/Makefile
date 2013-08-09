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

# TODO CL: consider using sbt (http://www.scala-sbt.org/) instead of make

PACKAGE = CombinatorialVickreyAuction
EXECUTABLES = $(PACKAGE)CATS.class \
$(PACKAGE)HardCoded.class

all: $(EXECUTABLES)

# getting dependencies of executable classes right
$(EXECUTABLES): %.class: \
  %.scala \
  $(PACKAGE)/nVCG_CaseChecker.class \
  $(PACKAGE)/SetWrapper.class \
  $(PACKAGE)/NatSetWrapper.class \
  $(PACKAGE)/IsabelleLibraryWrapper.class \
  $(PACKAGE)/TieBreaker.class
	scalac $<

# implicit rule (pattern rule) for compiling Scala classes
$(PACKAGE)/%.class: %.scala
	scalac $<

# need to compile all sources at once to avoid missing dependencies
$(PACKAGE)/nVCG_CaseChecker.class: generated/$(PACKAGE).scala nVCG_CaseChecker.scala
	scalac $$(perl -lne 'print "$$1.scala" if /^object ([^ ]+) {/' $<)

nVCG_CaseChecker.scala: generated/$(PACKAGE).scala
	./split-scala-modules.pl < $<

$(PACKAGE)CATS.jar: $(PACKAGE)CATS.class
	jar cf $@ $(PACKAGE)/ $(PACKAGE)CATS*.class

# locating scala-library.jar: http://stackoverflow.com/a/7582803/2397768
$(PACKAGE)CATS.zip: $(PACKAGE)CATS.jar example.cats README
	zip -j $@ \
		$$(scala -e 'val so = classOf[ScalaObject].getResource("ScalaObject.class").toString; println(so.substring(so.lastIndexOf(":") + 1, so.lastIndexOf("!")))') \
		$^

clean:
	find . -name '*.class' -o \
	       -name '*.jar' -o \
	       -name '*.zip' \
	| xargs rm -f

.PHONY: all clean
