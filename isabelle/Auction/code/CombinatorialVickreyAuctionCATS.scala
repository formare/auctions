/*
 * $Id$
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
import CombinatorialVickreyAuction.SetWrapper._
import CombinatorialVickreyAuction.NatSetWrapper._
import CombinatorialVickreyAuction.IsabelleLibraryWrapper._

/* our utility libraries */
import CombinatorialVickreyAuction.TieBreaker._

/** Runs a combinatorial auction on CATS-generated input
 * (see <a href="http://www.cs.ubc.ca/~kevinlb/CATS/CATS-readme.html#4.%20%20File Formats">CATS README, section “File Formats”</a> */
// TODO CL: roll out wrappers that only depend on the Isabelle library once https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2013-July/msg00028.html has been answered
object CombinatorialVickreyAuctionCATS {
  /** the paper example */
  def paperExampleParticipants = intListToNatSet(List(1, 2, 3))
  def paperExampleGoods = intListToNatSet(List(11, 12))
  def paperExampleBids = (bidder: Nat) => (goods: set[Nat]) =>
    if (bidder == Nat(1) && setEquals(goods, paperExampleGoods /* i.e. the whole set */)
        || (bidder == Nat(2) || bidder == Nat(3)) && card(goods) == Nat(1))
      // As it happens, code from Set.card was exported.
      // TODO CL: Depending on the implementation of the functions from which we actually _want_ to generate code, we can't rely on this.  What's a good practice for making sure code for certain library functions is always generated?
      Ratreal(Frct(2, 1))
    else Ratreal(zero_rat)

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

    // TODO exception handling
    val nGoodsRE = """goods\s+([0-9]+)""".r
    val nGoodsRE(nGoodsStr) = Console.readLine
    val nGoods = nGoodsStr.toInt // TODO simplify this "matching regexp to Int"
    val nBidsRE = """bids\s+([0-9]+)""".r
    val nBidsRE(nBidsStr) = Console.readLine
    val nBids = nBidsStr.toInt // TODO simplify this "matching regexp to Int"
    val bidRE = """([0-9]+)\s+([0-9]+)\s+((?:[0-9]+\s+)*)#""".r // TODO allow decimal price in addition to integer
    
    val bidsLines = (for (expectedBidID <- 0 to nBids) yield
      Console.readLine match {
        case bidRE(bidID, price, bidContent) =>
          if (bidID.toInt == expectedBidID) Some(
            Nat(bidID.toInt),
            Ratreal(Frct(price.toInt, 1)),
            intListToNatSet(bidContent.split("""\s+""").map(_.toInt).to[List])
          ) else None /* TODO actually throw exception */
        case _ => None
      }).flatten
    println("processed CATS input: " + prettyPrint(bidsLines))

    // CONVERT TO THE DATA STRUCTURES THE GENERATED CODE NEEDS
    // val participantSet = paperExampleParticipants
    // val goodsSet = paperExampleGoods
    // val bidFunction = paperExampleBids
    val participantSet = Seta((0 to nBids - 1).map(Nat(_)).to[List])
    println("Participants: " + prettyPrint(participantSet))
    val goodsSet = Seta((0 to nGoods - 1).map(Nat(_)).to[List])
    println("Goods: " + prettyPrint(goodsSet))
    val bidFunction = (bidder: Nat) => (goods: set[Nat]) => {
      val bid = bidsLines.find((elem: (Nat, real, set[Nat])) =>
        elem._1 == bidder
        && setEquals(goods, elem._3))
      bid match {
        case Some(b) => b._2
        case None => Ratreal(zero_rat)
      }
    }

    val tieBreaker = trivialTieBreaker[set[(set[Nat], Nat)]] _

    val winningAllocations = winning_allocations_comp_CL(goodsSet, participantSet, bidFunction)
    println("Winning allocations: " + prettyPrint(winningAllocations))
    println("Winner after tie-breaking: " + prettyPrint(tieBreaker(winningAllocations)))

    val payments = for (participant <- 0 to nBids - 1) yield
      // for the following occurrence of tieBreaker, we need the explicit type.  Above, trivialTieBreaker[Any] would also have worked.
      (participant, payments_comp_workaround(goodsSet, participantSet, tieBreaker, bidFunction, Nat(participant)))
    println("Payments per participant: " + prettyPrint(payments))
  }
}
