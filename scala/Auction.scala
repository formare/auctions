object Auction {
    type Bidvector = Array[Int];
    type Bidmatrix = Array[Bidvector];
    var n: Int = 3; // bidders
    var t: Int = 10; // rounds = running time


    //var bidmatrix = new scala.collection.mutable.ArrayBuffer[Array[Int]]()

    var bidmatrix = Array.ofDim[Int](n,t);
    
    def localToInt(s: String):Int = {
        // from http://alvinalexander.com/scala/how-cast-string-to-int-in-scala-string-int-conversion
        try {
            s.toInt
        } catch {
        case e:Exception => 0
        }
    }

    def validBid(bid:Int,i:Int,j:Int) : Boolean = {
        bid > bidmatrix{i}{j-1}
    }

    def roundOfBidding(j: Int) = {
    for(i <- 0 to n-1) {
        val x = readLine;
        val newBid = localToInt(x);
        if (validBid(newBid,i,j)) {
            bidmatrix{i}{j} = newBid;
        } else {
            bidmatrix{i}{j} = bidmatrix{i}{j-1};
        }
    }
    for(i <- 0 to n-1) {
        for (k <- 0 to j) {
            print(bidmatrix{i}{k})
                }
        println();
    }
}


//    var bidmatrix = Array(1,2,3)
//        bidmatrix = bidmatrix map(_*3)

//    var j: Int = 1;
    def main(args: Array[String]) {
        var j: Int = 0;
        while (life(bidmatrix, j)) {
                j = j+1;
                roundOfBidding(j);
            }
    }

    def life(bidmatrix : Bidmatrix, j : Int) : Boolean = {
    var result: Boolean = true;
        if (j != 0) {
            result = false;
            var i : Int = 0
            while (!result && i < n) {
                if (bidmatrix{i}{j} > bidmatrix{i}{j-1}) {
                    result = true;
                } else {
                    i = i+1;
                }
            }
        }
        result}
}




//val ys = xs filter (x => x % 2 == 0)