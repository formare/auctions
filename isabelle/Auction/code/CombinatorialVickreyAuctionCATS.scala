/*
 * Auction Theory Toolbox (http://formare.github.io/auctions/)
 * 
 * Authors:
 * * Manfred Kerber <mnfrd.krbr@gmail.com>
 * * Christoph Lange <math.semantic.web@gmail.com>
 * * Colin Rowat <c.rowat@bham.ac.uk>
 * 
 * Licenced under
 * * ISC License (1-clause BSD License)
 * See LICENSE file for details
 *
 */

/* modules of the generated code (including Isabelle library) */
import CombinatorialVickreyAuction.Finite_Set._
import CombinatorialVickreyAuction.Int._
import CombinatorialVickreyAuction.Nat._
import CombinatorialVickreyAuction.Rat._
import CombinatorialVickreyAuction.Real._
import CombinatorialVickreyAuction.Set._
import CombinatorialVickreyAuction.CombinatorialVickreyAuction._

/* our wrappers around the Isabelle library */
import CombinatorialVickreyAuction.SetWrapper._
import CombinatorialVickreyAuction.NatSetWrapper._
import CombinatorialVickreyAuction.IsabelleLibraryWrapper._

/* our utility libraries */
import CombinatorialVickreyAuction.TieBreaker._

/** Runs a combinatorial auction on CATS-generated input
 * (see <a href="http://www.cs.ubc.ca/~kevinlb/CATS/CATS-readme.html#4.%20%20File Formats">CATS README, section “File Formats”</a>) */
object CombinatorialVickreyAuctionCATS {
  /** runs a combinatorial Vickrey auction, processing CATS-formatted data from standard input */
  def main(args: Array[String]) {
    // http://www.cs.ubc.ca/~kevinlb/CATS/CATS-readme.html#4.%20%20File%20Formats

    // Each program in this suite outputs a file with the following format:
    
    // % comments
    
    // ...
    
    // goods <NUMBER OF GOODS>
    // bids <NUMBER OF BIDS>
    // 0   <content of bid 0>
    // 1   <content of bid 1>
    // ...
    // <NUMBER OF BIDS-2>  <content of bid NUMBER OF BIDS - 2>
    // <NUMBER OF BIDS-1>  <content of bid NUMBER OF BIDS - 1>
    
    // where <content of bid i> (i between 0 and NUMBER OF BIDS-1, inclusive) represents:
    
    // <real number representing price>  <good i requested>  <good j requested>  ... <good k requested>  #
    
    // where each good number is between 0 and NUMBER OF GOODS-1
    
    // Informally, the file format is: any number of comment lines beginning with percent sign, the word "goods" followed by the total number of goods, on the next line, the word "bids" followed by the total number of bids.  Then each following line is the bid number, followed by the price, followed by each good-number requested, all terminated by a pound sign.  Each line that represents a bid is tab-delimited.

    /* TODO CL: reimplement parsing as per https://github.com/formare/auctions/issues/11,
     * https://github.com/formare/auctions/issues/8,
     * https://github.com/formare/auctions/issues/9,
     * https://github.com/formare/auctions/issues/10
     */
    val nGoodsRE = """goods\s+([0-9]+)""".r
    val nGoodsRE(nGoodsStr) = Console.readLine
    val nGoods = nGoodsStr.toInt
    val nBidsRE = """bids\s+([0-9]+)""".r
    val nBidsRE(nBidsStr) = Console.readLine
    val nBids = nBidsStr.toInt
    val bidRE = """([0-9]+)\s+([0-9]+)\s+((?:[0-9]+\s+)*)#""".r
    
    val bidsLines = (for (expectedBidID <- 0 to nBids) yield
      Console.readLine match {
        case bidRE(bidID, price, bidContent) =>
          if (bidID.toInt == expectedBidID) Some((
            Nata(BigInt(bidID.toInt)),
            Ratreal(Frct((Int_of_integer(price.toInt), Int_of_integer(1)))),
            intListToNatSet(bidContent.split("""\s+""").map(_.toInt).to[List])
          )) else None
        case _ => None
      }).flatten
    println("processed CATS input: " + prettyPrint(bidsLines))

    // CONVERT TO THE DATA STRUCTURES THE GENERATED CODE NEEDS
    val participantSet : set[nat] = Seta((0 to nBids - 1).map(x => Nata(BigInt(x))).to[List])
    println("Participants: " + prettyPrint(participantSet))
    val goodsSet : set[nat] = Seta((0 to nGoods - 1).map(x => Nata(BigInt(x))).to[List])
    println("Goods: " + prettyPrint(goodsSet))
    val bidFunction : nat => set[nat] => real = (bidder: nat) => (goods: set[nat]) => {
      val bid = bidsLines.find((elem: (nat, Ratreal, set[nat])) =>
        elem._1 == bidder
        && setEquals(goods, elem._3))
      bid match {
        case Some(b) => b._2
        case None => Ratreal(zero_rat)
      }
    }

    val tieBreaker = trivialTieBreaker[set[(set[nat], nat)]] _

    val winningAllocations = winning_allocations_alg_CL(goodsSet, participantSet, bidFunction)
    println("Winning allocations: " + prettyPrint(winningAllocations))
    println("Winner after tie-breaking: " + prettyPrint(tieBreaker(winningAllocations)))

    val payments = for (participant <- 0 to nBids - 1) yield
      // for the following occurrence of tieBreaker, we need the explicit type.  Above, trivialTieBreaker[Any] would also have worked.
      (participant, payments_alg(goodsSet, participantSet, tieBreaker)(bidFunction)(Nata(participant)))
    println("Payments per participant: " + prettyPrint(payments))
  }
}
