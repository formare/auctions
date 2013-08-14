PREFIX = ..
include $(PREFIX)/Makefile.vars

BROWSER_INFO = $(shell isabelle getenv -b ISABELLE_BROWSER_INFO)

SUBDIRS = \
	Auction/code

all: sync subdirs

include $(PREFIX)/Makefile.in

# TODO run code generator with something like
# isabelle codegen ~/.isabelle/Isabelle2013/heaps/polyml-5.5.0_x86-linux/HOL CombinatorialVickreyAuction 'winning_allocations_comp_CL payments_comp_workaround in Scala file "code/generated/CombinatorialVickreyAuction.scala"'
# Note that we still need the wrapper CombinatorialVickreyAuction, because of the code_include declaration.
#
# $(BROWSER_INFO)/HOL/Auction/session.graph: Auction
# 	isabelle build -o browser_info -v -D $<
# 
# graph.pdf: $(BROWSER_INFO)/HOL/Auction/session.graph
# 	isabelle browser -o $@ $<
# 
# Auction/output/document.pdf: Auction
# 	isabelle build -D Auction
