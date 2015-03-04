// HANDWRITTEN NON-VERIFIED CODE FROM HERE

// print a number plus a trailing whitespace
def printWithSpace(args: BigInt): Unit = {
  print(args + " ");
}

// a single bid is represented as a pair (bidder, (listOfGoods, bid)).
// printBidder prints the first component, i.e., bidder
def printBidder(args: (BigInt, (List[BigInt], BigInt))): Unit = {
    println(" Bidder: " + args._1);
}

// recursively print a list separated by commas
def printListOfGoods(args: List[BigInt]): Unit = {
  args match {
       case Nil => print("");
       case head::Nil => print(head);
       case head::tail => print(head + ", "); printListOfGoods(tail);
     }
}

// a single bid is represented as a pair (bidder, (listOfGoods, bid)).
// printGoods prints the first component of the second, i.e., listOfGoods
def printGoods(args: (BigInt, (List[BigInt], BigInt))): Unit = {
    print(" Goods:  {");
    printListOfGoods(args._2._1);
    println("}");
}

// a single bid is represented as a pair (bidder, (listOfGoods, bid)).
// printBid prints the second component of the second, i.e., bid
def printBid(args: (BigInt, (List[BigInt], BigInt))): Unit = {
    println(" Bid:    " + args._2._2);
}

// prints a single bid as bidder + goods + bid
def printSingleBid(args: (BigInt, (List[BigInt], BigInt))): Unit = {
    printBidder(args);
    printGoods(args);
    printBid(args);
    println();
}

// prints each of the bids in a list one by one
def printAllBids(args: List[(BigInt, (List[BigInt], BigInt))]): Unit = {
    args.foreach(printSingleBid)
  }

// selects the first element from a set represented as a list
// (i.e., the only element in case of a singleton, else the first element of the list.)
// fails for empty set.
def choice[A](x0: set[A]): A = x0 match {
  case seta(List(x)) => x
  case seta(x :: _) => x
}

// print the payment that a particular participant has to pay
def printPrice(b: List[(BigInt, (List[BigInt], BigInt))], r: BigInt, participant: BigInt) {
    println((payments(b, r).apply(participant)));
}

// The Isabelle generated code will compute an allocation in form of list of pairs (participant, listOfWonItems).
// printAllocationAndPayment prints the allocation and the price to be paid for a single pair of this kind.
def printAllocationAndPayment(args: (BigInt, List[BigInt]), b: List[(BigInt, (List[BigInt], BigInt))], r: BigInt):
    Unit = args match {
               case (hd, tl) => print(" X_" + hd + " = {" ); 
                                printListOfGoods(tl);
                                print("}    payment:");
                                printPrice(b, r, hd);
  }


// The Isabelle generated code will compute an allocation in form of list of pairs (participant, listOfWonItems).
// printAllocationAndPayments prints the allocation and the price to be paid for each such pair one by one.
def printAllocationsAndPayments(args: set[List[(BigInt, List[BigInt])]], b: List[(BigInt, (List[BigInt], BigInt))], r: BigInt):
   Unit = { choice(args).foreach(arg => printAllocationAndPayment(arg, b, r));
  }

/* In order to run an example the bids and the random number can be arguments to runExample in the form
 *
 * val r1: BigInt = 0 // 0, 1, 2, ... 23
 *
 * val b1: List[(BigInt, (List[BigInt], BigInt))] =
 *   List((1, (List(11, 12), 2)),
 *        (2, (List(11), 2)),
 *        (2, (List(12), 2)),
 *        (3, (List(11), 2)),
 *        (3, (List(12), 2)))
 *         
 * runExample(b1, r1);         
 */
def runExample(b: List[(BigInt, (List[BigInt], BigInt))], r: BigInt):
   Unit = {
      println("************************************************************************************************");
      println("input bid vector:"); printAllBids(b);
      print("Random number for tie breaking: "); println(r);
      println;

      println("Winning allocation and payments:"); 
      printAllocationsAndPayments(allocation(b, r), b, r);
      println("************************************************************************************************");
}

// END OF HANDWRITTEN NON-VERIFIED CODE

// START OF EXAMPLE e1 with bids b1 and random number r1
// select random number in range 0, 1, ..., 2^card(goods) * factorial(numberOfParticipants) - 1
val r1: BigInt = 0 // 0, 1, 2, ... 23

val b1: List[(BigInt, (List[BigInt], BigInt))] =
    List((1, (List(11, 12), 2)),
         (2, (List(11), 2)),
         (2, (List(12), 2)),
         (3, (List(11), 2)),
         (3, (List(12), 2)))
// END OF EXAMPLE e1

// START OF EXAMPLE e2 with bids b2 and random number r2
// select random number in range 0, 1, ..., 2^card(goods) * factorial(numberOfParticipants) - 1
val r2: BigInt = 1 // 0, 1, 2, ... 23

val b2: List[(BigInt, (List[BigInt], BigInt))] =
    List((1, (List(11, 12), 5)),
         (2, (List(11), 3)),
         (2, (List(12), 3)),
         (3, (List(11), 2)),
         (3, (List(12), 4)))
// END OF EXAMPLE e2

// START OF EXAMPLE e3 with bids b3 and random number r3
// select random number in range 0, 1, ..., 2^card(goods) * factorial(numberOfParticipants) - 1
val r3: BigInt = 0 // 0, 1, 2, ... 47

val b3: List[(BigInt, (List[BigInt], BigInt))] =
    List((1, (List(11, 12, 13), 20)),
         (1, (List(11, 12), 18)),
         (2, (List(11), 10)),
         (2, (List(12), 15)),
         (2, (List(13), 15)),
         (2, (List(12,13), 18)),
         (3, (List(11), 2)),
         (3, (List(11,12), 12)),
         (3, (List(11,13), 17)),
         (3, (List(12,13), 18)),
         (3, (List(11,12,13), 19)))
// END OF EXAMPLE e3

// START OF main

def main(args: Array[String]) {

//for (i <- 0 to 23) {
//runExample(b1, i);
//}

runExample(b1, r1);
runExample(b2, r2);
runExample(b3, r3);

// END OF main
}
