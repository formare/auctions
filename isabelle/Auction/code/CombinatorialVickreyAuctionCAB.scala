/*
 * $Id: CombinatorialVickreyAuctionCATS.scala 1453 2013-08-08 21:55:52Z langec $
 * 
 * Auction Theory Toolbox
 * 
 * Authors:
 * * Manfred Kerber <m.kerber@cs.bham.ac.uk>
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
import CombinatorialVickreyAuction.Nat
import CombinatorialVickreyAuction.Nata._
import CombinatorialVickreyAuction.Rat._
import CombinatorialVickreyAuction.RealDef._
import CombinatorialVickreyAuction.Set._
import CombinatorialVickreyAuction.nVCG_CaseChecker._

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

    // regular expressions that match input lines
    // TODO change to parser combinators
    val nGoodsRE = """goods\s+(\d+)""".r
    val nBiddersRE = """bidders\s+(\d+)""".r
    val bidRE = """(\d+)\s+(\d+)(?:\.(\d+))?\s+((?:\d+\s+)*)#""".r // (?: ... ) is a non-capturing group

    // iterator over all non-comment lines from standard input
    val contentLines = scala.io.Source.stdin.getLines().filter(_(0) != '%')

    val nGoods = contentLines.next match {
      case nGoodsRE(nGoodsStr) => nGoodsStr.toInt
      case instead => {
        // TODO output input line number
        Console.err.printf("Expected \"goods <number>\"; found \"%s\"\n", instead)
        System.exit(1)
        0 // fallback return value; never needed
      }
    }
    
    val nBidders = contentLines.next match {
      case nBiddersRE(nBidsStr) => nBidsStr.toInt
      case instead => {
        Console.err.println("Expected \"bids <number>\"; found \"%s\"\n", instead)
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
        // TODO check whether values are in range
        (Nat(bidderID.toInt),
         Ratreal(decToFrct(priceWhole, Option(priceMaybeFrac))),
         intListToNatSet(bidContent.split("""\s+""").map(_.toInt).to[List]))
      }
      case instead => {
        Console.err.printf("Expected \"<bidderID> <price> <good> ... <good> #\"; found \"%s\"\n", instead)
        System.exit(3)
        (null, null, null) // TODO find better fallback value
      }
    }).toList
    println("processed CAB input: " + prettyPrint(bidsLines))

    // CONVERT TO THE DATA STRUCTURES THE GENERATED CODE NEEDS
    val participantSet = Seta((0 to nBidders - 1).map(Nat(_)).to[List])
    println("Participants: ", prettyPrint(participantSet))
    val goodsSet = Seta((0 to nGoods - 1).map(Nat(_)).to[List])
    println("Goods: ", prettyPrint(goodsSet))
    val bidFunction = (bidder: Nat) => (goods: set[Nat]) => {
      val bid = bidsLines.find((elem: (Nat, Ratreal, set[Nat])) =>
        elem._1 == bidder
        && setEquals(goods, elem._3))
      bid match {
        case Some(b) => b._2
        case None => Ratreal(zero_rat)
      }
    }

    val tieBreaker = trivialTieBreaker[set[(set[Nat], Nat)]] _

    val winningAllocations = winning_allocations_comp_CL(goodsSet, participantSet, bidFunction)
    println("Winning allocations: ", prettyPrint(winningAllocations))
    println("Winner after tie-breaking: ", prettyPrint(tieBreaker(winningAllocations)))

    val payments = for (participant <- 0 to nBidders - 1) yield
      // for the following occurrence of tieBreaker, we need the explicit type.  Above, trivialTieBreaker[Any] would also have worked.
      (participant, payments_comp_workaround(goodsSet, participantSet, tieBreaker, bidFunction, Nat(participant)))
    println("Payments per participant: ", prettyPrint(payments))
  }
}
