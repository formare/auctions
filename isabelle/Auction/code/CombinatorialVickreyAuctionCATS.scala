import CombinatorialVickreyAuction.Nat
import CombinatorialVickreyAuction.CombinatorialVickreyAuction._

object CombinatorialVickreyAuctionCATS {
  /** converts a Scala list to an Isabelle set */
  def intListToNatSet(l: List[Int]): set[Nat] = Set(l.map(Nat(_)))
  
  /** a trivial tie breaker that takes the head of a List */
  def trivialTieBreaker[T](l: List[T]) = l.head

  /** equality for Isabelle sets */
  def setEquals[T](s1: set[T], s2: set[T]) = (s1, s2) match {
    case (Set(l1), Set(l2)) => l1 == l2
    case _ => false
  }

  /** runs a combinatorial Vickrey auction, processing CATS-formatted data from standard input */
  def main(args: Array[String]) {
    // START WITH SOME CONSTANT INPUT DATA
    val participants = List(1, 2, 3)
    val goods = List(11, 12)

    // CONVERT TO THE DATA STRUCTURES THE GENERATED CODE NEEDS
    val participantSet = intListToNatSet(participants)
    val goodsSet = intListToNatSet(goods)
    println("goods as set: " + goodsSet)
    println("goods =? {11,12}: " + (setEquals[Nat](goodsSet, intListToNatSet(List(11, 12)))))
    println("goods =? {12,11}: " + (setEquals[Nat](goodsSet, intListToNatSet(List(12, 11)))))
    
    // TODO use bid from paper example
    //       if (bidder = 1 ∧ goods = {11,12}
    //     ∨ (bidder = 2 ∨ bidder = 3) ∧ card goods = 1)
    // then 2
    // else 0)"
    val bidFunction = (bidder: Nat) => (goods: set[Nat]) =>
      if (bidder == 1) Ratreal(zero_rat) else Ratreal(zero_rat)
    val tieBreaker = trivialTieBreaker[Any] _

    val winningAllocations = winning_allocations_comp_CL(goodsSet, participantSet, bidFunction)
    println("Winner: " + tieBreaker(winningAllocations))
  }
}
