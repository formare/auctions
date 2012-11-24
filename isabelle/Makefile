SYNC_FILES = \
	Auction/Maximum.thy \
	Auction/MaximumTest.thy \
	Auction/SecondPriceAuction.thy \
	Auction/SingleGoodAuction.thy \
	Auction/SingleGoodAuctionProperties.thy \
	Auction/SingleGoodAuctionTest.thy \
	Auction/Vectors.thy \
	Auction/Vickrey.thy \
	LICENSE LICENSE-CC-BY LICENSE-ISC \
	README

all: sync

graph.pdf: Auction
	isabelle browser -o $@ ~/.isabelle/Isabelle2012/browser_info/HOL/Auction/*.graph
sync:
	rsync -avzc --delete $(SYNC_FILES) \
	gromit:/bham/htdocs/website/research/projects/formare/code/auction-theory
