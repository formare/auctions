import CombinatorialVickreyAuction.Finite_Set._
import CombinatorialVickreyAuction.Nat
import CombinatorialVickreyAuction.Nata._
import CombinatorialVickreyAuction.Rat._
import CombinatorialVickreyAuction.RealDef._
import CombinatorialVickreyAuction.Set._
import CombinatorialVickreyAuction.nVCG_CaseChecker._

/** Runs a combinatorial auction on CATS-generated input
 * (see <a href="http://www.cs.ubc.ca/~kevinlb/CATS/CATS-readme.html#4.%20%20File Formats">CATS README, section “File Formats”</a> */
// TODO CL: roll out wrappers that only depend on the Isabelle library once https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2013-July/msg00028.html has been answered
object CombinatorialVickreyAuctionCATS {
  /** converts a Scala list to an Isabelle set.
   * Note that converting Int (hardware words) to Nat is OK, as it doesn't lose information, but converting vice versa is problematic when the Nat values are very large; then one should better convert to BigInt. */
  // TODO move to "SetCompanion" module
  def intListToNatSet(l: List[Int]): set[Nat] = Seta(l.map(Nat(_)))

  /** equality for Isabelle sets (ignoring the order of the underlying List) */
  // TODO move to "SetCompanion" module
  def setEquals[T](s1: set[T], s2: set[T]) = (s1, s2) match {
    case (Seta(l1), Seta(l2)) => l1.toSet == l2.toSet
    case _ => false
  }
  
  /** pretty-prints several Isabelle types for display to the user */
  // TODO CL: factor out to a module such as "IsabelleLibraryCompanion"
  def prettyPrint[A](x: A): String = x match {
    /* tuples */
    case (fst, snd) => "(%s, %s)".format(prettyPrint(fst), prettyPrint(snd))
    /* Isabelle sets */
    case Seta(l) => "{%s}".format(l.map(prettyPrint(_)).mkString(", "))
    /* Isabelle's reals-from-rationals */
    // matching Frct(num, den) doesn't work, as actually (num, den) is a tuple
    case Ratreal(Frct((num, den))) => (num.toDouble / den.toDouble).toString /* note that this loses precision! */
    /* anything else */
    case _ => x.toString
  }

  /** a trivial tie breaker that takes the head of a List */
  def trivialTieBreaker[T](l: List[T]) = l.head

  /** the paper example */
  def paperExampleParticipants = intListToNatSet(List(1, 2, 3))
  def paperExampleGoods = intListToNatSet(List(11, 12))
  def paperExampleBids = (bidder: Nat) => (goods: set[Nat]) =>
    if (bidder == Nat(1) && setEquals(goods, paperExampleGoods /* i.e. the whole set */)
        || (bidder == Nat(2) || bidder == Nat(3)) && card(goods) == Nat(1))
      // As it happens, code from Set.card was exported.
      // TODO CL: Depending on the implementation of the functions from which we actually _want_ to generate code, we can't rely on this.  What's a good practice for making sure code for certain library functions is always generated?
      Ratreal(Frct(2, 0))
    else Ratreal(zero_rat)

  /** runs a combinatorial Vickrey auction, processing CATS-formatted data from standard input */
  def main(args: Array[String]) {
    // CONVERT TO THE DATA STRUCTURES THE GENERATED CODE NEEDS
    val participantSet = paperExampleParticipants
    val goodsSet = paperExampleGoods
    val bidFunction = paperExampleBids

    val tieBreaker = trivialTieBreaker[Any] _

    val winningAllocations = winning_allocations_comp_CL(goodsSet, participantSet, bidFunction)
    println("Winner: " + prettyPrint(tieBreaker(winningAllocations)))
  }
}
