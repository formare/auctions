import code.Nat
import code.Vickrey._

object VickreyTest {
  def curry[A,B,C](g: (A,B) => C) = (x:A) => (y:B) => g(x,y)

  // this would in some cases allow us to write an Int where Nat is expected
  implicit def intToNat(x:Int) = Nat(x)

  def main(args: Array[String]) {
    println("Enter the numeric IDs of the participants; terminate input with an empty line:")
    val participants = 
      Iterator.continually(Console.readLine).
      takeWhile(_ != "").
      toList.map(_.toInt) // TODO error handling when input line doesn't parse as an Int
    println("Participants: " + participants)
    // thanks to [Nat] type argument we can take advantage of the intToNat implicit type conversion

    println("Enter the participants' bids as fractions, e.g. 2/3.")
    val bids = Map(participants.map(i => {
        print("Bid for participant " + i + ": ")
        val (num, den) = Console.readf2("{0,number,integer}/{1,number,integer}")
        i -> Ratreal(Frct(num.asInstanceOf[Long].intValue, den.asInstanceOf[Long].intValue))
      }): _*)
    println("Bids: " + bids)

    val tie_breaker = curry {(x:Nat, y:Nat) => y < x}
    println("Tie breaker: <")

    println(fs_spa_winner(Set(participants.map(Nat(_))),
                          (x: Nat) => bids.getOrElse(x.as_Int, Ratreal(zero_rat)),
                          // the way we defined participants, the "OrElse" part won't be needed here, so we can put anything in its place.
                          tie_breaker))
  }
}
