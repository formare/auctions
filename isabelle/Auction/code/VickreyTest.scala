import code.Nat
import code.Vickrey

object VickreyTest {
def main(args: Array[String]) {
println(Vickrey.arg_max_l_tb(List(Nat(1),Nat(2)), 
                     (x: Nat) => (y: Nat) => y < x, 
                     (x: Nat) => if (x == Nat(1)) 
		                       Vickrey.Ratreal(Vickrey.Frct(6,4))
                                 else  Vickrey.Ratreal(Vickrey.Frct(6,4))
			   ))
}}
