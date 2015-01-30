PREFIX = ..
include $(PREFIX)/Makefile.vars

BROWSER_INFO = $(shell isabelle getenv -b ISABELLE_BROWSER_INFO)

SUBDIRS = \
	Auction/code

all: sync subdirs

include $(PREFIX)/Makefile.in

# TODO CL: add this rule to find stuff not yet documented
# for i in *.thy; do fgrep -q $i ../index.php || echo $i; done

# $(BROWSER_INFO)/HOL/Auction/session.graph: Auction
# 	isabelle build -o browser_info -v -D $<
# 
# graph.pdf: $(BROWSER_INFO)/HOL/Auction/session.graph
# 	isabelle browser -o $@ $<
# 
# Auction/output/document.pdf: Auction
# 	isabelle build -D Auction
