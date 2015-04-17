/*

This is the Scala wrapper for dynamic auctions that terminate when no
further valid bids are made.  The wrapper has to be manually added
before the last line with the final closing "}" to the Isabelle
extracted code which is found in dynamicAuctionTerminating.scala

In order to run the code (after possibly first installing Scala)
you have first to compile the adapted file with e.g.,

         scalac -nowarn dynamicAuctionTerminating.scala

and then run it with

         scala dynamicAuctionTerminating

from a shell.

*/

def input[A](n:(Boolean, List[dynamicAuctionTerminating.nat])) :
                    (BigInt, (Boolean, List[dynamicAuctionTerminating.nat])) = {
	val x = readInt; 
	return (x,n);
}

def output[A](x: (String, A)) : A = {
	println(fst (x));
	return (snd (x));
}

def main(args: Array[String]) {
	val x = dynamicAuctionTerminatingExported(input, output);
}
