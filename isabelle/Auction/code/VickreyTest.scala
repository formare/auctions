import code.Nat
import code.Vickrey._

/** run with "scala VickreyTest", or with "java -cp .:/usr/share/scala/lib/scala-library.jar VickreyTest" */
object VickreyTest {
  def curry[A,B,C](g: (A,B) => C) = (x:A) => (y:B) => g(x,y)

  /* something like this might in some cases allow us to write an Int where Nat is expected
  implicit def intToNat(x:Int) = Nat(x)
  */
  
  def prettyPrint[A](x: A) = x match {
    // matching Frct(num, den) doesn't work, as actually (num, den) is a tuple
    case Ratreal(Frct((num, den))) => num.toDouble / den.toDouble
    case _ => x
  }
  
  def vecToMap[A](v: (Nat => A), n: set[Nat]) =
    n match {
      case Set(xs) => Map(xs.map(i => i -> prettyPrint(v(i))): _*) }

  /** reads a decimal number, e.g. "3.14", from standard input */
  def readDecimal(): real = {
    val Decimal = """(\d+)(?:\.(\d+))?""".r
    val Decimal(whole, maybeFrac) = Iterator.continually(Console.readLine).dropWhile(!Decimal.unapplySeq(_).isDefined).next
    val power = if (maybeFrac != null) maybeFrac.length else 0
    val frac = if (maybeFrac != null) maybeFrac.toInt else 0
    val commonDen = math.pow(10, power).toInt
    Ratreal(Frct(commonDen * whole.toInt + frac, commonDen))
  } 

  /** runs a second price auction */
  def main(args: Array[String]) {
    // READ INPUTS
    println("Enter the numeric IDs of the participants; terminate input with an empty line:")
    val participants = 
      Iterator.continually(Console.readLine).
      takeWhile(_ != "").
      toList.map(_.toInt) // TODO error handling when input line doesn't parse as an Int
    println("Participants: " + participants)

    println("Enter the participants' bids as decimal numbers, e.g. 27 or 3.14.")
    val bids = Map(participants.map(i => {
        print("Bid for participant " + i + ": ")
        i -> readDecimal()
      }): _*)
    println("Bids: " + bids)
    // for hard-coded constants use functions like { case foo => bar case baz => ... }

    println("Enter the tie breaker as '>'-separated list of participant IDs:")
    val tmpList = Console.readLine.split(" *> *").toList.map(_.toInt)
    val tbList = if
      (tmpList.toSet == participants.toSet)
      tmpList
    else {
      print("Invalid or incomplete list entered; falling back to random order: ")
      val randomized = util.Random.shuffle(participants).reverse
      println(randomized.mkString(" > "))
      randomized
    }
    
    // CONVERT TO THE DATA STRUCTURES THE GENERATED CODE NEEDS
    val participantSet = Set(participants.map(Nat(_)))
    val bidVector = (x: Nat) => bids.getOrElse(x.as_Int, Ratreal(zero_rat)) // the way we defined participants, the "OrElse" part won't be needed here, so we can put anything in its place.
    val tieBreaker = curry {
      (x:Nat, y:Nat) => tbList.indexOf(x.as_Int) < tbList.indexOf(y.as_Int)
    }

    println("Winner: " +
            fs_spa_winner(participantSet,
                          bidVector,
                          tieBreaker))
    val alloc = fs_spa_allocation(participantSet,
                                  bidVector,
                                  tieBreaker) 
    println("Allocation: " +
            vecToMap(alloc, participantSet))
    val pay = fs_spa_payments(participantSet,
                              bidVector,
                              tieBreaker) 
    println("Payments: " +
            vecToMap(pay, participantSet))
  }
}
