include ../Makefile.vars

SYNC_FILES = \
	Auction/Maximum.thy \
	Auction/MaximumTest.thy \
	Auction/SecondPriceAuction.thy \
	Auction/SingleGoodAuction.thy \
	Auction/SingleGoodAuctionProperties.thy \
	Auction/SingleGoodAuctionTest.thy \
	Auction/Vectors.thy \
	Auction/Vickrey.thy \
	README.isabelle.html

all: sync

include ../Makefile.in

graph.pdf: Auction
	isabelle browser -o $@ ~/.isabelle/Isabelle2012/browser_info/HOL/Auction/*.graph
