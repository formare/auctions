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
import CombinatorialVickreyAuction.Nat._
import CombinatorialVickreyAuction.Rat._
import CombinatorialVickreyAuction.Real._
import CombinatorialVickreyAuction.Set._
import CombinatorialVickreyAuction.CombinatorialVickreyAuction._

/* our wrappers around the Isabelle library */
import CombinatorialVickreyAuction.RatWrapper._
import CombinatorialVickreyAuction.SetWrapper._
import CombinatorialVickreyAuction.NatSetWrapper._
import CombinatorialVickreyAuction.IsabelleLibraryWrapper._

/* our utility libraries */
import CombinatorialVickreyAuction.TieBreaker._

/** Runs a combinatorial auction on a CATS-like input format with bidder IDs
 * (see <a href="http://www.cs.ubc.ca/~kevinlb/CATS/CATS-readme.html#4.%20%20File Formats">CATS README, section “File Formats”</a> and local file <code>example.cab</code> */
object CombinatorialVickreyAuctionCAB {
  /** runs a combinatorial Vickrey auction, processing CATS-formatted data from standard input */
  def main(args: Array[String]) {
    // % comments
    
    // goods <NUMBER OF GOODS>
    // bidders <NUMBER OF BIDDERS>
    // <BIDDER-ID> <real number representing price>  <good i requested>  <good j requested>  ... <good k requested>  #
    // where each bidder ID is between 0 and NUMBER OF BIDDERS-1
    // and each good number is between 0 and NUMBER OF GOODS-1
    
    // Informally, the file format is: any number of comment lines beginning with percent sign, the word "goods" followed by the total number of goods, on the next line, the word "bids" followed by the total number of bids.  Then each following line is the bid number, followed by the price, followed by each good-number requested, all terminated by a pound sign.  Each line that represents a bid is tab-delimited.

    /* TODO CL: reimplement parsing as per https://github.com/formare/auctions/issues/8,
     * https://github.com/formare/auctions/issues/9,
     * https://github.com/formare/auctions/issues/10
     */

    // regular expressions that match input lines
    val nGoodsRE = """goods\s+(\d+)""".r
    val nBiddersRE = """bidders\s+(\d+)""".r
    val bidRE = """(\d+)\s+(\d+)(?:\.(\d+))?\s+((?:\d+\s+)*)#""".r // (?: ... ) is a non-capturing group

    // iterator over all non-comment lines from standard input
    val contentLines = scala.io.Source.stdin.getLines().filter(_(0) != '%')

    val nGoods = contentLines.next match {
      case nGoodsRE(nGoodsStr) => nGoodsStr.toInt
      case instead => {
        Console.err.printf("Expected \"goods <number>\"; found \"%s\"\n", instead)
        System.exit(1)
        0 // fallback return value; never needed
      }
    }
    
    val nBidders = contentLines.next match {
      case nBiddersRE(nBidsStr) => nBidsStr.toInt
      case instead => {
        Console.err.printf("Expected \"bids <number>\"; found \"%s\"\n", instead)
        System.exit(2)
        0
      }
    }

    val bidsLines = (contentLines collect {
      case bidRE(bidderID, priceWhole, priceMaybeFrac, bidContent) => {
        // turn a decimal number into a fraction
        val power = if (priceMaybeFrac != null) priceMaybeFrac.length else 0
        val frac = if (priceMaybeFrac != null) priceMaybeFrac.toInt else 0
        val commonDen = math.pow(10, power).toInt
        (Nata(BigInt(bidderID.toInt)),
         Ratreal(decToFrct(priceWhole, Option(priceMaybeFrac))),
         intListToNatSet(bidContent.split("""\s+""").map(_.toInt).to[List]))
      }
      case instead => {
        Console.err.printf("Expected \"<bidderID> <price> <good> ... <good> #\"; found \"%s\"\n", instead)
        System.exit(3)
        (null, null, null) // TODO CL: find better fallback value
      }
    }).toList
    println("processed CAB input: " + prettyPrint(bidsLines))

    // CONVERT TO THE DATA STRUCTURES THE GENERATED CODE NEEDS
    val participantSet : set[nat] = Seta((0 to nBidders - 1).map(x => Nata(BigInt(x))).to[List])
                    // ^ seems we need this explicit type information; otherwise we get type mismatch errors
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

    val payments = for (participant <- 0 to nBidders - 1) yield
      // for the following occurrence of tieBreaker, we need the explicit type.  Above, trivialTieBreaker[Any] would also have worked.
      (participant, payments_alg(goodsSet, participantSet, tieBreaker)(bidFunction)(Nata(BigInt(participant))))
    println("Payments per participant: " + prettyPrint(payments))
  }
}
