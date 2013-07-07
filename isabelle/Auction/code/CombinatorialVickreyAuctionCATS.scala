import CombinatorialVickreyAuction.Nat
import CombinatorialVickreyAuction.CombinatorialVickreyAuction._

/** Runs a combinatorial auction on CATS-generated input
 * (see <a href="http://www.cs.ubc.ca/~kevinlb/CATS/CATS-readme.html#4.%20%20File Formats">CATS README, section “File Formats”</a> */
object CombinatorialVickreyAuctionCATS {
  /** converts a Scala list to an Isabelle set.
   * Note that converting Int (hardware words) to Nat is OK, as it doesn't lose information, but converting vice versa is problematic when the Nat values are very large; then one should better convert to BigInt. */
  // TODO move to "SetCompanion" module
  def intListToNatSet(l: List[Int]): set[Nat] = Set(l.map(Nat(_)))

  /** equality for Isabelle sets (ignoring the order of the underlying List) */
  // TODO move to "SetCompanion" module
  def setEquals[T](s1: set[T], s2: set[T]) = (s1, s2) match {
    case (Set(l1), Set(l2)) => l1.toSet == l2.toSet
    case _ => false
  }

  /** a trivial tie breaker that takes the head of a List */
  def trivialTieBreaker[T](l: List[T]) = l.head

  /** runs a combinatorial Vickrey auction, processing CATS-formatted data from standard input */
  def main(args: Array[String]) {
    // START WITH SOME CONSTANT INPUT DATA
    val theParticipants = List(1, 2, 3)
    val theGoods = List(11, 12)

    // CONVERT TO THE DATA STRUCTURES THE GENERATED CODE NEEDS
    val participantSet = intListToNatSet(theParticipants)
    val goodsSet = intListToNatSet(theGoods)
    
    // TODO use bid from paper example
    //       if (bidder = 1 ∧ goods = {11,12}
    //     ∨ (bidder = 2 ∨ bidder = 3) ∧ card goods = 1)
    // then 2
    // else 0)"
    val bidFunction = (bidder: Nat) => (goods: set[Nat]) =>
      if (bidder == Nat(1) && setEquals(goods, goodsSet /* i.e. the whole set */)
        || (bidder == Nat(2) || bidder == Nat(3)) && card(goods) == Nat(1))
        // As it happens, code from Set.card was exported.
        // TODO CL: Depending on the implementation of the functions from which we actually _want_ to generate code, we can't rely on this.  What's a good practice for making sure code for certain library functions is always generated?
        Ratreal(Frct(2, 0))
      else Ratreal(zero_rat)
    val tieBreaker = trivialTieBreaker[Any] _

    val winningAllocations = winning_allocations_comp_CL(goodsSet, participantSet, bidFunction)
    println("Winner: " + tieBreaker(winningAllocations))
  }
}
