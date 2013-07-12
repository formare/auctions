# TODO CL: convert to sbt: http://www.scala-sbt.org/

CombinatorialVickreyAuctionCATS.class: \
  CombinatorialVickreyAuctionCATS.scala \
  CombinatorialVickreyAuction/nVCG_CaseChecker.class
	scalac $<

# TODO CL: rename once we have refactored nVCG_CaseChecker.thy into separate theories
CombinatorialVickreyAuction/nVCG_CaseChecker.class: CombinatorialVickreyAuction.scala
	scalac $<

CombinatorialVickreyAuctionCATS.jar: CombinatorialVickreyAuctionCATS.class
	jar cf $@ CombinatorialVickreyAuction/ CombinatorialVickreyAuctionCATS*.class

# TODO CL: automate locating scala-library.jar
CombinatorialVickreyAuctionCATS.zip: CombinatorialVickreyAuctionCATS.jar example.cats README
	zip -j $@ /opt/scala-2.10.1/lib/scala-library.jar $^
