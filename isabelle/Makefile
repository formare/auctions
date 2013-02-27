PREFIX = ..
include $(PREFIX)/Makefile.vars

SYNC_FILES = \
	Auction/Maximum.thy \
	Auction/MaximumTest.thy \
	Auction/SecondPriceAuction.thy \
	Auction/SingleGoodAuction.thy \
	Auction/SingleGoodAuctionProperties.thy \
	Auction/SingleGoodAuctionTest.thy \
	Auction/Vectors.thy \
	Auction/Vickrey.thy \
	Auction/Vickrey_Short.thy \
	index.php \
	sidebar.php \
	graph.pdf \
	Auction/output/document.pdf
BROWSER_INFO = $(shell isabelle getenv -b ISABELLE_BROWSER_INFO)

all: sync

include $(PREFIX)/Makefile.in

$(BROWSER_INFO)/HOL/Auction/session.graph: Auction
	isabelle build -o browser_info -v -D $<

graph.pdf: $(BROWSER_INFO)/HOL/Auction/session.graph
	isabelle browser -o $@ $<
