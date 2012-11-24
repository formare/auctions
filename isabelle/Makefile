SYNC_FILES = SingleGoodAuctionTest.thy SingleGoodAuction.thy Vectors.thy Vickrey.thy LICENSE LICENSE-CC-BY LICENSE-ISC README

all: sync

sync:
	rsync -avzc --delete $(SYNC_FILES) \
	gromit:/bham/htdocs/website/research/projects/formare/code/auction-theory
