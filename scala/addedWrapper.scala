// HANDWRITTEN NON-VERIFIED CODE FROM HERE
def printWithSpace(args: BigInt): Unit = {
  print(args + " ");
}

def printListOfGoods(args: List[BigInt]): Unit = {
  args match {
       case Nil => print("");
       case head::Nil => print(head);
       case head::tail => print(head + ", "); printListOfGoods(tail);
     }
}

def printBidder(args: List[List[BigInt]]): Unit = {
    println(" Bidder: " + args.head.head);
}

def printGoods(args: List[List[BigInt]]): Unit = {
    print(" Goods:  {");
    printListOfGoods(args.tail.head);
    println("}");
}

def printBid(args: List[List[BigInt]]): Unit = {
    println(" Bid:    " + args.tail.tail.head.head);
}

def printSingleBid(args: List[List[BigInt]]): Unit = {
    printBidder(args);
    printGoods(args);
    printBid(args);
    println();
}

def printAllBids(args: List[List[List[BigInt]]]): Unit = {
    args.foreach(printSingleBid)
  }

/*def the_elem[A](x0: set[A]): A = x0 match {
  case seta(List(x)) => x
}
*/

def choice[A](x0: set[A]): A = x0 match {
  case seta(List(x)) => x
  case seta(x :: _) => x
}

def printAllocatedGoods(args: List[BigInt]): Unit = {
    printListOfGoods(args);
}

def printPrice(b: List[List[List[BigInt]]], r: BigInt, args: BigInt) {
    println((payments(b, r).apply(args)));
}

def printAllocationAndPayment(args: (BigInt, List[BigInt]), b:  List[List[List[BigInt]]], r: BigInt): Unit =
args match {
    case (hd, tl) => print(" X_" + hd + " = {" ); 
                     printAllocatedGoods(tl);
                     print("}    payment:");
                     printPrice(b, r, hd);
//    println(args);
  }


def printAllocationsAndPayments(args: set[List[(BigInt, List[BigInt])]], b: List[List[List[BigInt]]], r: BigInt):
   Unit = { choice(args).foreach(arg => printAllocationAndPayment(arg, b, r));
  }

          
def main(args: Array[String]) {
println("input bid vector:"); printAllBids(b1);
println;

println("Winning allocation and payments:"); 
printAllocationsAndPayments(allocation(b1, r1), b1, r1);
}
// END OF HANDWRITTEN NON-VERIFIED CODE
