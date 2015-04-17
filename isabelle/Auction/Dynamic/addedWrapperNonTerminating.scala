def untrusted(n:BigInt) : String = {
	val x=readLine;
	return x;
}

def main(args: Array[String]) {
	val x=trusted(untrusted);
}








def untrustedInput(n:BigInt) : String = {
	val x=readLine;
	return x;
}

def untrustedOutput(message:String) : String = {
	println(message);
	return message;
}

def main(args: Array[String]) {
	val x=trusted(untrustedInput, untrustedOutput);
}













def untrustedInput(n:BigInt) : String = {
	val x=scala.io.StdIn.readLine;
	return x;
}

def untrustedOutput(message:String) : String = {
	println(message);
	return message;
}

def main(args: Array[String]) {
	val x=trusted(untrustedOutput, untrustedInput);
}












def untrustedInput(n:BigInt) : String = {
	val x=readLine;
	return x;
}

def untrustedOutput(message:String) : String = {
	println(message);
	return message;
}

def main(args: Array[String]) {
	val x=prova(untrustedInput, untrustedOutput);
}

















def untrustedInput(n:List[String]) : List[String] = {
	val x=readLine;
	return (x::n);
}

def untrustedOutput(x: (List[String], String)) : List[String] = {
	println(snd (x));
	return (fst (x));
}

def main(args: Array[String]) {
	val x=evaluateMe(untrustedInput, untrustedOutput);
}

















def untrustedInput(n:List[BigInt]) : List[BigInt] = {
	val x=readInt; //NB: We rely on the user typing an integer, here! This is a naive but simple approach.
	return (x::n);
}

def untrustedOutput(x: (List[BigInt], String)) : List[BigInt] = {
	println(snd (x));
	return (fst (x));
}

def main(args: Array[String]) {
	val x=evaluateMe(untrustedInput, untrustedOutput);
}

















def unverifiedInput(n:List[BigInt]) : List[BigInt] = {
	val x=readInt; //NB: We rely on the user typing an integer, here! This is a naive but simple approach.
	return (x::n);
}

def unverifiedOutput(x: (String, List[BigInt])) : List[BigInt] = {
	println(fst (x));
	return (snd (x));
}

def main(args: Array[String]) {
	val x=evaluateMe(unverifiedInput, unverifiedOutput);
}






















def unverifiedInput[A](n:A) : (BigInt, A) = {
	val x=readInt; 
	return (x,n);
}

def unverifiedOutput[A](x: (String, A)) : A = {
	println(fst (x));
	return (snd (x));
}

def main(args: Array[String]) {
	val x=dynamicAuctionTerminatingExported(unverifiedInput, unverifiedOutput);
}

















def input(n:List[BigInt]) : List[BigInt] = {
	val x=readInt;
	return (x::n);
}

def output(x: (String, List[BigInt])) : List[BigInt] = {
	println(fst (x));
	return (snd (x));
}

def main(args: Array[String]) {
	val x=evaluateMe(input, output);
}
















def input[A](n:(Boolean, List[a.nat])) : (BigInt, (Boolean, List[a.nat])) = {
	val x=readInt; 
	return (x,n);
}

def output[A](x: (String, A)) : A = {
	println(fst (x));
	return (snd (x));
}

def main(args: Array[String]) {
	val x=dynamicAuctionTerminatingExported(input, output);
}



