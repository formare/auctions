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
	println("debug");
	val x=readLine;
	return x;
}

def untrustedOutput(message:String) : String = {
	println(message);
	return message;
}

def main(args: Array[String]) {
	val x=prova(untrustedInput);
}

