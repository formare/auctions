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
import CombinatorialVickreyAuction.Code_Numeral._
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

object CombinatorialVickreyAuctionHardCoded {
  /** the paper example from http://arxiv.org/abs/1308.1779 */
  def paperExampleParticipants = intListToNatSet(List(1, 2, 3))
  def paperExampleGoods = intListToNatSet(List(11, 12))
  def paperExampleBids = (bidder: nat) => (goods: set[nat]) =>
    if (bidder == Nata(BigInt(1)) && setEquals(goods, paperExampleGoods /* i.e. the whole set */)
        || (bidder == Nata(BigInt(2)) || bidder == Nata(BigInt(3))) && card(goods) == Nata(BigInt(1)))
      // As it happens, code from Set.card was exported (TODO CL: ensure this; see https://github.com/formare/auctions/issues/12)
      Ratreal(Frct((Int_of_integer(2), Int_of_integer(1))))
    else Ratreal(zero_rat)

  /** runs a combinatorial Vickrey auction on hard-coded input*/
  def main(args: Array[String]) {
    val participantSet = paperExampleParticipants
    val goodsSet = paperExampleGoods
    val bidFunction = paperExampleBids

    val tieBreaker = trivialTieBreaker[set[(set[nat], nat)]] _

    val winningAllocations = winning_allocations_alg_CL(goodsSet, participantSet, bidFunction)
    println("Winning allocations: " + prettyPrint(winningAllocations))
    println("Winner after tie-breaking: " + prettyPrint(tieBreaker(winningAllocations)))

    val payments = for (participant <- 0 to integer_of_nat(card(participantSet)).toInt - 1) yield
      // for the following occurrence of tieBreaker, we need the explicit type.  Above, trivialTieBreaker[Any] would also have worked.
      (participant, payments_alg(goodsSet, participantSet, tieBreaker)(bidFunction)(Nata(BigInt(participant))))
    println("Payments per participant: " + prettyPrint(payments))
  }
}
