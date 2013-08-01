PREFIX = ..
include $(PREFIX)/Makefile.vars

BROWSER_INFO = $(shell isabelle getenv -b ISABELLE_BROWSER_INFO)

all: sync

include $(PREFIX)/Makefile.in

# $(BROWSER_INFO)/HOL/Auction/session.graph: Auction
# 	isabelle build -o browser_info -v -D $<
# 
# graph.pdf: $(BROWSER_INFO)/HOL/Auction/session.graph
# 	isabelle browser -o $@ $<
# 
# Auction/output/document.pdf: Auction
# 	isabelle build -D Auction
