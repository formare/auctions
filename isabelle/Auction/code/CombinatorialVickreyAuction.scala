package CombinatorialVickreyAuction


object Fun {

def id[A]: A => A = (x: A) => x

def comp[A, B, C](f: A => B, g: C => A): C => B = (x: C) => f(g(x))

} /* object Fun */

object HOL {

trait equal[A] {
  val `HOL.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`HOL.equal`(a, b)

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

} /* object HOL */

object Product_Type {

def fst[A, B](x0: (A, B)): A = x0 match {
  case (a, b) => a
}

def snd[A, B](x0: (A, B)): B = x0 match {
  case (a, b) => b
}

def apsnd[A, B, C](f: A => B, x1: (C, A)): (C, B) = (f, x1) match {
  case (f, (x, y)) => (x, f(y))
}

def equal_proda[A : HOL.equal, B : HOL.equal](x0: (A, B), x1: (A, B)): Boolean =
  (x0, x1) match {
  case ((aa, ba), (a, b)) => HOL.eq[A](aa, a) && HOL.eq[B](ba, b)
}

implicit def equal_prod[A : HOL.equal, B : HOL.equal]: HOL.equal[(A, B)] = new
  HOL.equal[(A, B)] {
  val `HOL.equal` = (a: (A, B), b: (A, B)) => equal_proda[A, B](a, b)
}

} /* object Product_Type */

object Power {

trait power[A] extends Groups.one[A] with Groups.times[A] {
}

} /* object Power */

object Groups {

trait one[A] {
  val `Groups.one`: A
}
def one[A](implicit A: one[A]): A = A.`Groups.one`

trait plus[A] {
  val `Groups.plus`: (A, A) => A
}
def plus[A](a: A, b: A)(implicit A: plus[A]): A = A.`Groups.plus`(a, b)

trait zero[A] {
  val `Groups.zero`: A
}
def zero[A](implicit A: zero[A]): A = A.`Groups.zero`

trait times[A] {
  val `Groups.times`: (A, A) => A
}
def times[A](a: A, b: A)(implicit A: times[A]): A = A.`Groups.times`(a, b)

trait semigroup_add[A] extends plus[A] {
}

trait monoid_add[A] extends semigroup_add[A] with zero[A] {
}

trait semigroup_mult[A] extends times[A] {
}

trait monoid_mult[A] extends semigroup_mult[A] with Power.power[A] {
}

trait ab_semigroup_add[A] extends semigroup_add[A] {
}

trait comm_monoid_add[A] extends ab_semigroup_add[A] with monoid_add[A] {
}

} /* object Groups */

object Orderings {

trait ord[A] {
  val `Orderings.less_eq`: (A, A) => Boolean
  val `Orderings.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean =
  A.`Orderings.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`Orderings.less`(a, b)

trait preorder[A] extends ord[A] {
}

trait order[A] extends preorder[A] {
}

trait linorder[A] extends order[A] {
}

} /* object Orderings */

object Nat {

abstract sealed class nat
final case class Zero_nat() extends nat
final case class Suc(a: nat) extends nat

def of_nat_aux[A : Rings.semiring_1](inc: A => A, x1: nat, i: A): A =
  (inc, x1, i) match {
  case (inc, Zero_nat(), i) => i
  case (inc, Suc(n), i) => of_nat_aux[A](inc, n, inc(i))
}

def of_nat[A : Rings.semiring_1](n: nat): A =
  of_nat_aux[A]((i: A) => Groups.plus[A](i, Groups.one[A]), n, Groups.zero[A])

def less_nat(m: nat, x1: nat): Boolean = (m, x1) match {
  case (m, Suc(n)) => less_eq_nat(m, n)
  case (n, Zero_nat()) => false
}

def less_eq_nat(x0: nat, n: nat): Boolean = (x0, n) match {
  case (Suc(m), n) => less_nat(m, n)
  case (Zero_nat(), n) => true
}

implicit def ord_nat: Orderings.ord[nat] = new Orderings.ord[nat] {
  val `Orderings.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `Orderings.less` = (a: nat, b: nat) => less_nat(a, b)
}

def one_nat: nat = Suc(Zero_nat())

def equal_nata(x0: nat, x1: nat): Boolean = (x0, x1) match {
  case (Suc(nat), Zero_nat()) => false
  case (Zero_nat(), Suc(nat)) => false
  case (Suc(nata), Suc(nat)) => equal_nata(nata, nat)
  case (Zero_nat(), Zero_nat()) => true
}

implicit def equal_nat: HOL.equal[nat] = new HOL.equal[nat] {
  val `HOL.equal` = (a: nat, b: nat) => equal_nata(a, b)
}

implicit def preorder_nat: Orderings.preorder[nat] = new Orderings.preorder[nat]
  {
  val `Orderings.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `Orderings.less` = (a: nat, b: nat) => less_nat(a, b)
}

implicit def order_nat: Orderings.order[nat] = new Orderings.order[nat] {
  val `Orderings.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `Orderings.less` = (a: nat, b: nat) => less_nat(a, b)
}

def plus_nat(x0: nat, n: nat): nat = (x0, n) match {
  case (Suc(m), n) => plus_nat(m, Suc(n))
  case (Zero_nat(), n) => n
}

implicit def linorder_nat: Orderings.linorder[nat] = new Orderings.linorder[nat]
  {
  val `Orderings.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `Orderings.less` = (a: nat, b: nat) => less_nat(a, b)
}

} /* object Nat */

object Rings {

trait semiring[A]
  extends Groups.ab_semigroup_add[A] with Groups.semigroup_mult[A] {
}

trait mult_zero[A] extends Groups.times[A] with Groups.zero[A] {
}

trait semiring_0[A]
  extends Groups.comm_monoid_add[A] with mult_zero[A] with semiring[A] {
}

trait zero_neq_one[A] extends Groups.one[A] with Groups.zero[A] {
}

trait semiring_1[A]
  extends Num.semiring_numeral[A] with semiring_0[A] with zero_neq_one[A] {
}

} /* object Rings */

object Num {

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

def bitM(x0: num): num = x0 match {
  case One() => One()
  case Bit0(n) => Bit1(bitM(n))
  case Bit1(n) => Bit1(Bit0(n))
}

trait numeral[A] extends Groups.one[A] with Groups.semigroup_add[A] {
}

def less_eq_num(x0: num, n: num): Boolean = (x0, n) match {
  case (Bit1(m), Bit0(n)) => less_num(m, n)
  case (Bit1(m), Bit1(n)) => less_eq_num(m, n)
  case (Bit0(m), Bit1(n)) => less_eq_num(m, n)
  case (Bit0(m), Bit0(n)) => less_eq_num(m, n)
  case (Bit1(m), One()) => false
  case (Bit0(m), One()) => false
  case (One(), n) => true
}

def less_num(m: num, x1: num): Boolean = (m, x1) match {
  case (Bit1(m), Bit0(n)) => less_num(m, n)
  case (Bit1(m), Bit1(n)) => less_num(m, n)
  case (Bit0(m), Bit1(n)) => less_eq_num(m, n)
  case (Bit0(m), Bit0(n)) => less_num(m, n)
  case (One(), Bit1(n)) => true
  case (One(), Bit0(n)) => true
  case (m, One()) => false
}

def plus_num(x0: num, x1: num): num = (x0, x1) match {
  case (Bit1(m), Bit1(n)) => Bit0(plus_num(plus_num(m, n), One()))
  case (Bit1(m), Bit0(n)) => Bit1(plus_num(m, n))
  case (Bit1(m), One()) => Bit0(plus_num(m, One()))
  case (Bit0(m), Bit1(n)) => Bit1(plus_num(m, n))
  case (Bit0(m), Bit0(n)) => Bit0(plus_num(m, n))
  case (Bit0(m), One()) => Bit1(m)
  case (One(), Bit1(n)) => Bit0(plus_num(n, One()))
  case (One(), Bit0(n)) => Bit1(n)
  case (One(), One()) => Bit0(One())
}

def equal_num(x0: num, x1: num): Boolean = (x0, x1) match {
  case (Bit1(numa), Bit0(num)) => false
  case (Bit0(numa), Bit1(num)) => false
  case (Bit1(num), One()) => false
  case (One(), Bit1(num)) => false
  case (Bit0(num), One()) => false
  case (One(), Bit0(num)) => false
  case (Bit1(numa), Bit1(num)) => equal_num(numa, num)
  case (Bit0(numa), Bit0(num)) => equal_num(numa, num)
  case (One(), One()) => true
}

def times_num(m: num, n: num): num = (m, n) match {
  case (Bit1(m), Bit1(n)) =>
    Bit1(plus_num(plus_num(m, n), Bit0(times_num(m, n))))
  case (Bit1(m), Bit0(n)) => Bit0(times_num(Bit1(m), n))
  case (Bit0(m), Bit1(n)) => Bit0(times_num(m, Bit1(n)))
  case (Bit0(m), Bit0(n)) => Bit0(Bit0(times_num(m, n)))
  case (One(), n) => n
  case (m, One()) => m
}

def nat_of_num(x0: num): Nat.nat = x0 match {
  case One() => Nat.Suc(Nat.Zero_nat())
  case Bit0(x) => Nat.plus_nat(nat_of_num(x), nat_of_num(x))
  case Bit1(x) => Nat.Suc(Nat.plus_nat(nat_of_num(x), nat_of_num(x)))
}

trait semiring_numeral[A]
  extends Groups.monoid_mult[A] with numeral[A] with Rings.semiring[A] {
}

} /* object Num */

object Int {

abstract sealed class int
final case class Zero_int() extends int
final case class Pos(a: Num.num) extends int
final case class Neg(a: Num.num) extends int

def dup(x0: int): int = x0 match {
  case Neg(n) => Neg(Num.Bit0(n))
  case Pos(n) => Pos(Num.Bit0(n))
  case Zero_int() => Zero_int()
}

def nat(x0: int): Nat.nat = x0 match {
  case Pos(k) => Num.nat_of_num(k)
  case Zero_int() => Nat.Zero_nat()
  case Neg(k) => Nat.Zero_nat()
}

def uminus_int(x0: int): int = x0 match {
  case Neg(m) => Pos(m)
  case Pos(m) => Neg(m)
  case Zero_int() => Zero_int()
}

def minus_int(k: int, l: int): int = (k, l) match {
  case (Neg(m), Neg(n)) => sub(n, m)
  case (Neg(m), Pos(n)) => Neg(Num.plus_num(m, n))
  case (Pos(m), Neg(n)) => Pos(Num.plus_num(m, n))
  case (Pos(m), Pos(n)) => sub(m, n)
  case (Zero_int(), l) => uminus_int(l)
  case (k, Zero_int()) => k
}

def plus_inta(k: int, l: int): int = (k, l) match {
  case (Neg(m), Neg(n)) => Neg(Num.plus_num(m, n))
  case (Neg(m), Pos(n)) => sub(n, m)
  case (Pos(m), Neg(n)) => sub(m, n)
  case (Pos(m), Pos(n)) => Pos(Num.plus_num(m, n))
  case (Zero_int(), l) => l
  case (k, Zero_int()) => k
}

def sub(x0: Num.num, x1: Num.num): int = (x0, x1) match {
  case (Num.Bit0(m), Num.Bit1(n)) => minus_int(dup(sub(m, n)), Pos(Num.One()))
  case (Num.Bit1(m), Num.Bit0(n)) => plus_inta(dup(sub(m, n)), Pos(Num.One()))
  case (Num.Bit1(m), Num.Bit1(n)) => dup(sub(m, n))
  case (Num.Bit0(m), Num.Bit0(n)) => dup(sub(m, n))
  case (Num.One(), Num.Bit1(n)) => Neg(Num.Bit0(n))
  case (Num.One(), Num.Bit0(n)) => Neg(Num.bitM(n))
  case (Num.Bit1(m), Num.One()) => Pos(Num.Bit0(m))
  case (Num.Bit0(m), Num.One()) => Pos(Num.bitM(m))
  case (Num.One(), Num.One()) => Zero_int()
}

def one_inta: int = Pos(Num.One())

implicit def one_int: Groups.one[int] = new Groups.one[int] {
  val `Groups.one` = one_inta
}

def less_int(x0: int, x1: int): Boolean = (x0, x1) match {
  case (Neg(k), Neg(l)) => Num.less_num(l, k)
  case (Neg(k), Pos(l)) => true
  case (Neg(k), Zero_int()) => true
  case (Pos(k), Neg(l)) => false
  case (Pos(k), Pos(l)) => Num.less_num(k, l)
  case (Pos(k), Zero_int()) => false
  case (Zero_int(), Neg(l)) => false
  case (Zero_int(), Pos(l)) => true
  case (Zero_int(), Zero_int()) => false
}

def abs_int(i: int): int = (if (less_int(i, Zero_int())) uminus_int(i) else i)

implicit def plus_int: Groups.plus[int] = new Groups.plus[int] {
  val `Groups.plus` = (a: int, b: int) => plus_inta(a, b)
}

def equal_inta(x0: int, x1: int): Boolean = (x0, x1) match {
  case (Neg(k), Neg(l)) => Num.equal_num(k, l)
  case (Neg(k), Pos(l)) => false
  case (Neg(k), Zero_int()) => false
  case (Pos(k), Neg(l)) => false
  case (Pos(k), Pos(l)) => Num.equal_num(k, l)
  case (Pos(k), Zero_int()) => false
  case (Zero_int(), Neg(l)) => false
  case (Zero_int(), Pos(l)) => false
  case (Zero_int(), Zero_int()) => true
}

def sgn_int(i: int): int =
  (if (equal_inta(i, Zero_int())) Zero_int()
    else (if (less_int(Zero_int(), i)) Pos(Num.One())
           else uminus_int(Pos(Num.One()))))

implicit def zero_int: Groups.zero[int] = new Groups.zero[int] {
  val `Groups.zero` = Zero_int()
}

implicit def equal_int: HOL.equal[int] = new HOL.equal[int] {
  val `HOL.equal` = (a: int, b: int) => equal_inta(a, b)
}

def times_inta(k: int, l: int): int = (k, l) match {
  case (Neg(m), Neg(n)) => Pos(Num.times_num(m, n))
  case (Neg(m), Pos(n)) => Neg(Num.times_num(m, n))
  case (Pos(m), Neg(n)) => Neg(Num.times_num(m, n))
  case (Pos(m), Pos(n)) => Pos(Num.times_num(m, n))
  case (Zero_int(), l) => Zero_int()
  case (k, Zero_int()) => Zero_int()
}

implicit def times_int: Groups.times[int] = new Groups.times[int] {
  val `Groups.times` = (a: int, b: int) => times_inta(a, b)
}

implicit def power_int: Power.power[int] = new Power.power[int] {
  val `Groups.times` = (a: int, b: int) => times_inta(a, b)
  val `Groups.one` = one_inta
}

implicit def semigroup_add_int: Groups.semigroup_add[int] = new
  Groups.semigroup_add[int] {
  val `Groups.plus` = (a: int, b: int) => plus_inta(a, b)
}

implicit def numeral_int: Num.numeral[int] = new Num.numeral[int] {
  val `Groups.plus` = (a: int, b: int) => plus_inta(a, b)
  val `Groups.one` = one_inta
}

def less_eq_int(x0: int, x1: int): Boolean = (x0, x1) match {
  case (Neg(k), Neg(l)) => Num.less_eq_num(l, k)
  case (Neg(k), Pos(l)) => true
  case (Neg(k), Zero_int()) => true
  case (Pos(k), Neg(l)) => false
  case (Pos(k), Pos(l)) => Num.less_eq_num(k, l)
  case (Pos(k), Zero_int()) => false
  case (Zero_int(), Neg(l)) => false
  case (Zero_int(), Pos(l)) => true
  case (Zero_int(), Zero_int()) => true
}

implicit def ab_semigroup_add_int: Groups.ab_semigroup_add[int] = new
  Groups.ab_semigroup_add[int] {
  val `Groups.plus` = (a: int, b: int) => plus_inta(a, b)
}

implicit def semigroup_mult_int: Groups.semigroup_mult[int] = new
  Groups.semigroup_mult[int] {
  val `Groups.times` = (a: int, b: int) => times_inta(a, b)
}

implicit def semiring_int: Rings.semiring[int] = new Rings.semiring[int] {
  val `Groups.times` = (a: int, b: int) => times_inta(a, b)
  val `Groups.plus` = (a: int, b: int) => plus_inta(a, b)
}

implicit def mult_zero_int: Rings.mult_zero[int] = new Rings.mult_zero[int] {
  val `Groups.zero` = Zero_int()
  val `Groups.times` = (a: int, b: int) => times_inta(a, b)
}

implicit def monoid_add_int: Groups.monoid_add[int] = new Groups.monoid_add[int]
  {
  val `Groups.zero` = Zero_int()
  val `Groups.plus` = (a: int, b: int) => plus_inta(a, b)
}

implicit def comm_monoid_add_int: Groups.comm_monoid_add[int] = new
  Groups.comm_monoid_add[int] {
  val `Groups.zero` = Zero_int()
  val `Groups.plus` = (a: int, b: int) => plus_inta(a, b)
}

implicit def semiring_0_int: Rings.semiring_0[int] = new Rings.semiring_0[int] {
  val `Groups.times` = (a: int, b: int) => times_inta(a, b)
  val `Groups.zero` = Zero_int()
  val `Groups.plus` = (a: int, b: int) => plus_inta(a, b)
}

implicit def monoid_mult_int: Groups.monoid_mult[int] = new
  Groups.monoid_mult[int] {
  val `Groups.one` = one_inta
  val `Groups.times` = (a: int, b: int) => times_inta(a, b)
}

implicit def semiring_numeral_int: Num.semiring_numeral[int] = new
  Num.semiring_numeral[int] {
  val `Groups.plus` = (a: int, b: int) => plus_inta(a, b)
  val `Groups.one` = one_inta
  val `Groups.times` = (a: int, b: int) => times_inta(a, b)
}

implicit def zero_neq_one_int: Rings.zero_neq_one[int] = new
  Rings.zero_neq_one[int] {
  val `Groups.zero` = Zero_int()
  val `Groups.one` = one_inta
}

implicit def semiring_1_int: Rings.semiring_1[int] = new Rings.semiring_1[int] {
  val `Groups.zero` = Zero_int()
  val `Groups.one` = one_inta
  val `Groups.times` = (a: int, b: int) => times_inta(a, b)
  val `Groups.plus` = (a: int, b: int) => plus_inta(a, b)
}

} /* object Int */

object Divides {

def adjust(b: Int.int): ((Int.int, Int.int)) => (Int.int, Int.int) =
  (a: (Int.int, Int.int)) =>
    {
      val (q, r): (Int.int, Int.int) = a;
      (if (Int.less_eq_int(Int.Zero_int(), Int.minus_int(r, b)))
        (Int.plus_inta(Int.times_inta(Int.Pos(Num.Bit0(Num.One())), q),
                        Int.Pos(Num.One())),
          Int.minus_int(r, b))
        else (Int.times_inta(Int.Pos(Num.Bit0(Num.One())), q), r))
    }

def posDivAlg(a: Int.int, b: Int.int): (Int.int, Int.int) =
  (if (Int.less_int(a, b) || Int.less_eq_int(b, Int.Zero_int()))
    (Int.Zero_int(), a)
    else (adjust(b)).apply(posDivAlg(a, Int.times_inta(Int.Pos(Num.Bit0(Num.One())),
                b))))

def pdivmod(k: Int.int, l: Int.int): (Int.int, Int.int) =
  (if (Int.equal_inta(l, Int.Zero_int())) (Int.Zero_int(), Int.abs_int(k))
    else posDivAlg(Int.abs_int(k), Int.abs_int(l)))

def divmod_int(k: Int.int, l: Int.int): (Int.int, Int.int) =
  (if (Int.equal_inta(k, Int.Zero_int())) (Int.Zero_int(), Int.Zero_int())
    else (if (Int.equal_inta(l, Int.Zero_int())) (Int.Zero_int(), k)
           else Product_Type.apsnd[Int.int, Int.int,
                                    Int.int]((a: Int.int) =>
       Int.times_inta(Int.sgn_int(l), a),
      (if (Int.equal_inta(Int.sgn_int(k), Int.sgn_int(l))) pdivmod(k, l)
        else {
               val (r, s): (Int.int, Int.int) = pdivmod(k, l);
               (if (Int.equal_inta(s, Int.Zero_int()))
                 (Int.uminus_int(r), Int.Zero_int())
                 else (Int.minus_int(Int.uminus_int(r), Int.Pos(Num.One())),
                        Int.minus_int(Int.abs_int(l), s)))
             }))))

def div_int(a: Int.int, b: Int.int): Int.int =
  Product_Type.fst[Int.int, Int.int](divmod_int(a, b))

def mod_int(a: Int.int, b: Int.int): Int.int =
  Product_Type.snd[Int.int, Int.int](divmod_int(a, b))

} /* object Divides */

object GCD {

def gcd_int(k: Int.int, l: Int.int): Int.int =
  Int.abs_int((if (Int.equal_inta(l, Int.Zero_int())) k
                else gcd_int(l, Divides.mod_int(Int.abs_int(k),
         Int.abs_int(l)))))

} /* object GCD */

object Rat {

import /*implicits*/ Int.equal_int

abstract sealed class rat
final case class Frct(a: (Int.int, Int.int)) extends rat

def quotient_of(x0: rat): (Int.int, Int.int) = x0 match {
  case Frct(x) => x
}

def less_rat(p: rat, q: rat): Boolean =
  {
    val (a, c): (Int.int, Int.int) = quotient_of(p)
    val (b, d): (Int.int, Int.int) = quotient_of(q);
    Int.less_int(Int.times_inta(a, d), Int.times_inta(c, b))
  }

def normalize(p: (Int.int, Int.int)): (Int.int, Int.int) =
  (if (Int.less_int(Int.Zero_int(), Product_Type.snd[Int.int, Int.int](p)))
    {
      val a: Int.int =
        GCD.gcd_int(Product_Type.fst[Int.int, Int.int](p),
                     Product_Type.snd[Int.int, Int.int](p));
      (Divides.div_int(Product_Type.fst[Int.int, Int.int](p), a),
        Divides.div_int(Product_Type.snd[Int.int, Int.int](p), a))
    }
    else (if (Int.equal_inta(Product_Type.snd[Int.int, Int.int](p),
                              Int.Zero_int()))
           (Int.Zero_int(), Int.Pos(Num.One()))
           else {
                  val a: Int.int =
                    Int.uminus_int(GCD.gcd_int(Product_Type.fst[Int.int,
                         Int.int](p),
        Product_Type.snd[Int.int, Int.int](p)));
                  (Divides.div_int(Product_Type.fst[Int.int, Int.int](p), a),
                    Divides.div_int(Product_Type.snd[Int.int, Int.int](p), a))
                }))

def plus_rat(p: rat, q: rat): rat =
  Frct({
         val (a, c): (Int.int, Int.int) = quotient_of(p)
         val (b, d): (Int.int, Int.int) = quotient_of(q);
         normalize((Int.plus_inta(Int.times_inta(a, d), Int.times_inta(b, c)),
                     Int.times_inta(c, d)))
       })

def zero_rat: rat = Frct((Int.Zero_int(), Int.Pos(Num.One())))

def equal_rat(a: rat, b: rat): Boolean =
  Product_Type.equal_proda[Int.int, Int.int](quotient_of(a), quotient_of(b))

def minus_rat(p: rat, q: rat): rat =
  Frct({
         val (a, c): (Int.int, Int.int) = quotient_of(p)
         val (b, d): (Int.int, Int.int) = quotient_of(q);
         normalize((Int.minus_int(Int.times_inta(a, d), Int.times_inta(b, c)),
                     Int.times_inta(c, d)))
       })

def less_eq_rat(p: rat, q: rat): Boolean =
  {
    val (a, c): (Int.int, Int.int) = quotient_of(p)
    val (b, d): (Int.int, Int.int) = quotient_of(q);
    Int.less_eq_int(Int.times_inta(a, d), Int.times_inta(c, b))
  }

} /* object Rat */

object Lista {

def hd[A](x0: List[A]): A = x0 match {
  case x :: xs => x
}

def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) :: map[A, B](f, xs)
}

def nth[A](x0: List[A], x1: Nat.nat): A = (x0, x1) match {
  case (x :: xs, Nat.Suc(n)) => nth[A](xs, n)
  case (x :: xs, Nat.Zero_nat()) => x
}

def fold[A, B](f: A => B => B, x1: List[A], s: B): B = (f, x1, s) match {
  case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
  case (f, Nil, s) => s
}

def maps[A, B](f: A => List[B], x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) ++ maps[A, B](f, xs)
}

def upto(i: Int.int, j: Int.int): List[Int.int] =
  (if (Int.less_eq_int(i, j)) i :: upto(Int.plus_inta(i, Int.Pos(Num.One())), j)
    else Nil)

def foldr[A, B](f: A => B => B, x1: List[A]): B => B = (f, x1) match {
  case (f, Nil) => Fun.id[B]
  case (f, x :: xs) => Fun.comp[B, B, B](f(x), foldr[A, B](f, xs))
}

def filter[A](p: A => Boolean, x1: List[A]): List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x :: xs) => (if (p(x)) x :: filter[A](p, xs) else filter[A](p, xs))
}

def member[A : HOL.equal](x0: List[A], y: A): Boolean = (x0, y) match {
  case (Nil, y) => false
  case (x :: xs, y) => HOL.eq[A](x, y) || member[A](xs, y)
}

def insert[A : HOL.equal](x: A, xs: List[A]): List[A] =
  (if (member[A](xs, x)) xs else x :: xs)

def listsum[A : Groups.monoid_add](xs: List[A]): A =
  (foldr[A, A]((a: A) => (b: A) => Groups.plus[A](a, b),
                xs)).apply(Groups.zero[A])

def remdups[A : HOL.equal](x0: List[A]): List[A] = x0 match {
  case Nil => Nil
  case x :: xs =>
    (if (member[A](xs, x)) remdups[A](xs) else x :: remdups[A](xs))
}

def list_all[A](p: A => Boolean, x1: List[A]): Boolean = (p, x1) match {
  case (p, Nil) => true
  case (p, x :: xs) => p(x) && list_all[A](p, xs)
}

def insort_key[A, B : Orderings.linorder](f: A => B, x: A, xa2: List[A]):
      List[A] =
  (f, x, xa2) match {
  case (f, x, Nil) => List(x)
  case (f, x, y :: ys) =>
    (if (Orderings.less_eq[B](f(x), f(y))) x :: y :: ys
      else y :: insort_key[A, B](f, x, ys))
}

def sort_key[A, B : Orderings.linorder](f: A => B, xs: List[A]): List[A] =
  (foldr[A, List[A]]((a: A) => (b: List[A]) => insort_key[A, B](f, a, b),
                      xs)).apply(Nil)

def removeAll[A : HOL.equal](x: A, xa1: List[A]): List[A] = (x, xa1) match {
  case (x, Nil) => Nil
  case (x, y :: xs) =>
    (if (HOL.eq[A](x, y)) removeAll[A](x, xs) else y :: removeAll[A](x, xs))
}

def gen_length[A](n: Nat.nat, x1: List[A]): Nat.nat = (n, x1) match {
  case (n, x :: xs) => gen_length[A](Nat.Suc(n), xs)
  case (n, Nil) => n
}

def size_list[A]: (List[A]) => Nat.nat =
  (a: List[A]) => gen_length[A](Nat.Zero_nat(), a)

def map_filter[A, B](f: A => Option[B], x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) =>
    (f(x) match {
       case None => map_filter[A, B](f, xs)
       case Some(y) => y :: map_filter[A, B](f, xs)
     })
}

def list_update[A](x0: List[A], i: Nat.nat, y: A): List[A] = (x0, i, y) match {
  case (x :: xs, Nat.Suc(i), y) => x :: list_update[A](xs, i, y)
  case (x :: xs, Nat.Zero_nat(), y) => y :: xs
  case (Nil, i, y) => Nil
}

def map_project[A, B](f: A => Option[B], x1: Set.set[A]): Set.set[B] = (f, x1)
  match {
  case (f, Set.Seta(xs)) => Set.Seta[B](map_filter[A, B](f, xs))
}

def sorted_list_of_set[A : HOL.equal : Orderings.linorder](x0: Set.set[A]):
      List[A] =
  x0 match {
  case Set.Seta(xs) => sort_key[A, A]((x: A) => x, remdups[A](xs))
}

} /* object Lista */

object Set {

abstract sealed class set[A]
final case class Seta[A](a: List[A]) extends set[A]
final case class Coset[A](a: List[A]) extends set[A]

def image[A, B](f: A => B, x1: set[A]): set[B] = (f, x1) match {
  case (f, Seta(xs)) => Seta[B](Lista.map[A, B](f, xs))
}

def insert[A : HOL.equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, Coset(xs)) => Coset[A](Lista.removeAll[A](x, xs))
  case (x, Seta(xs)) => Seta[A](Lista.insert[A](x, xs))
}

def member[A : HOL.equal](x: A, xa1: set[A]): Boolean = (x, xa1) match {
  case (x, Coset(xs)) => ! (Lista.member[A](xs, x))
  case (x, Seta(xs)) => Lista.member[A](xs, x)
}

def remove[A : HOL.equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, Coset(xs)) => Coset[A](Lista.insert[A](x, xs))
  case (x, Seta(xs)) => Seta[A](Lista.removeAll[A](x, xs))
}

def bot_set[A]: set[A] = Seta[A](Nil)

def sup_set[A : HOL.equal](x0: set[A], a: set[A]): set[A] = (x0, a) match {
  case (Coset(xs), a) =>
    Coset[A](Lista.filter[A]((x: A) => ! (member[A](x, a)), xs))
  case (Seta(xs), a) =>
    Lista.fold[A, set[A]]((aa: A) => (b: set[A]) => insert[A](aa, b), xs, a)
}

def less_eq_set[A : HOL.equal](a: set[A], b: set[A]): Boolean = (a, b) match {
  case (Coset(Nil), Seta(Nil)) => false
  case (a, Coset(ys)) => Lista.list_all[A]((y: A) => ! (member[A](y, a)), ys)
  case (Seta(xs), b) => Lista.list_all[A]((x: A) => member[A](x, b), xs)
}

def equal_seta[A : HOL.equal](a: set[A], b: set[A]): Boolean =
  less_eq_set[A](a, b) && less_eq_set[A](b, a)

implicit def equal_set[A : HOL.equal]: HOL.equal[set[A]] = new HOL.equal[set[A]]
  {
  val `HOL.equal` = (a: set[A], b: set[A]) => equal_seta[A](a, b)
}

def the_elem[A](x0: set[A]): A = x0 match {
  case Seta(List(x)) => x
}

def minus_set[A : HOL.equal](a: set[A], x1: set[A]): set[A] = (a, x1) match {
  case (a, Coset(xs)) => Seta[A](Lista.filter[A]((x: A) => member[A](x, a), xs))
  case (a, Seta(xs)) =>
    Lista.fold[A, set[A]]((aa: A) => (b: set[A]) => remove[A](aa, b), xs, a)
}

} /* object Set */

object Maximum {

def arg_max_comp_list[A, B : HOL.equal : Orderings.linorder](x0: List[A],
                      f: A => B):
      List[A] =
  (x0, f) match {
  case (Nil, f) => Nil
  case (List(x), f) => List(x)
  case (x :: v :: va, f) =>
    {
      val arg_max_xs: List[A] = arg_max_comp_list[A, B](v :: va, f)
      val prev_max: B = f(Lista.hd[A](arg_max_xs));
      (if (Orderings.less[B](prev_max, f(x))) List(x)
        else (if (HOL.eq[B](f(x), prev_max)) x :: arg_max_xs else arg_max_xs))
    }
}

def maximum_comp_list[A, B : Orderings.linorder](x0: List[A], b: A => B): B =
  (x0, b) match {
  case (Nil, b) => sys.error("undefined")
  case (List(x), b) => b(x)
  case (x :: v :: va, b) =>
    {
      val max_xs: B = maximum_comp_list[A, B](v :: va, b);
      (if (Orderings.less[B](max_xs, b(x))) b(x) else max_xs)
    }
}

} /* object Maximum */

object RealDef {

abstract sealed class real
final case class Ratreal(a: Rat.rat) extends real

def less_eq_real(x0: real, x1: real): Boolean = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Rat.less_eq_rat(x, y)
}

def less_real(x0: real, x1: real): Boolean = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Rat.less_rat(x, y)
}

implicit def ord_real: Orderings.ord[real] = new Orderings.ord[real] {
  val `Orderings.less_eq` = (a: real, b: real) => less_eq_real(a, b)
  val `Orderings.less` = (a: real, b: real) => less_real(a, b)
}

def plus_reala(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(Rat.plus_rat(x, y))
}

implicit def plus_real: Groups.plus[real] = new Groups.plus[real] {
  val `Groups.plus` = (a: real, b: real) => plus_reala(a, b)
}

def zero_reala: real = Ratreal(Rat.zero_rat)

implicit def zero_real: Groups.zero[real] = new Groups.zero[real] {
  val `Groups.zero` = zero_reala
}

def equal_reala(x0: real, x1: real): Boolean = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Rat.equal_rat(x, y)
}

implicit def equal_real: HOL.equal[real] = new HOL.equal[real] {
  val `HOL.equal` = (a: real, b: real) => equal_reala(a, b)
}

implicit def preorder_real: Orderings.preorder[real] = new
  Orderings.preorder[real] {
  val `Orderings.less_eq` = (a: real, b: real) => less_eq_real(a, b)
  val `Orderings.less` = (a: real, b: real) => less_real(a, b)
}

implicit def order_real: Orderings.order[real] = new Orderings.order[real] {
  val `Orderings.less_eq` = (a: real, b: real) => less_eq_real(a, b)
  val `Orderings.less` = (a: real, b: real) => less_real(a, b)
}

def minus_real(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(Rat.minus_rat(x, y))
}

implicit def linorder_real: Orderings.linorder[real] = new
  Orderings.linorder[real] {
  val `Orderings.less_eq` = (a: real, b: real) => less_eq_real(a, b)
  val `Orderings.less` = (a: real, b: real) => less_real(a, b)
}

implicit def semigroup_add_real: Groups.semigroup_add[real] = new
  Groups.semigroup_add[real] {
  val `Groups.plus` = (a: real, b: real) => plus_reala(a, b)
}

implicit def monoid_add_real: Groups.monoid_add[real] = new
  Groups.monoid_add[real] {
  val `Groups.zero` = zero_reala
  val `Groups.plus` = (a: real, b: real) => plus_reala(a, b)
}

implicit def ab_semigroup_add_real: Groups.ab_semigroup_add[real] = new
  Groups.ab_semigroup_add[real] {
  val `Groups.plus` = (a: real, b: real) => plus_reala(a, b)
}

implicit def comm_monoid_add_real: Groups.comm_monoid_add[real] = new
  Groups.comm_monoid_add[real] {
  val `Groups.zero` = zero_reala
  val `Groups.plus` = (a: real, b: real) => plus_reala(a, b)
}

} /* object RealDef */

object Relation {

def image[A : HOL.equal, B](r: Set.set[(A, B)], s: Set.set[A]): Set.set[B] =
  Lista.map_project[(A, B),
                     B]((a: (A, B)) =>
                          {
                            val (x, y): (A, B) = a;
                            (if (Set.member[A](x, s)) Some[B](y) else None)
                          },
                         r)

def range[A, B](r: Set.set[(A, B)]): Set.set[B] =
  Set.image[(A, B), B]((a: (A, B)) => Product_Type.snd[A, B](a), r)

def domain[A, B](r: Set.set[(A, B)]): Set.set[A] =
  Set.image[(A, B), A]((a: (A, B)) => Product_Type.fst[A, B](a), r)

} /* object Relation */

object Finite_Set {

def card[A : HOL.equal](x0: Set.set[A]): Nat.nat = x0 match {
  case Set.Seta(xs) => Lista.size_list[A].apply(Lista.remdups[A](xs))
}

} /* object Finite_Set */

object Partitions {

import /*implicits*/ Int.semiring_1_int

def all_partitions_fun_list[A : HOL.equal](x0: List[A]):
      List[List[Set.set[A]]] =
  x0 match {
  case Nil => Nil
  case List(x) => List(List(Set.insert[A](x, Set.bot_set[A])))
  case x :: v :: va =>
    {
      val xs_partitions: List[List[Set.set[A]]] =
        all_partitions_fun_list[A](v :: va);
      Lista.maps[List[Set.set[A]],
                  List[Set.set[A]]]((p: List[Set.set[A]]) =>
                                      Lista.map[Nat.nat,
         List[Set.set[A]]]((i: Nat.nat) =>
                             Lista.list_update[Set.set[A]](p, i,
                    Set.sup_set[A](Set.insert[A](x, Set.bot_set[A]),
                                    Lista.nth[Set.set[A]](p, i))),
                            Lista.map[Int.int,
                                       Nat.nat]((a: Int.int) => Int.nat(a),
         Lista.upto(Int.Zero_int(),
                     Int.minus_int(Nat.of_nat[Int.int](Lista.size_list[Set.set[A]].apply(p)),
                                    Int.Pos(Num.One()))))),
                                     xs_partitions) ++
        Lista.map[List[Set.set[A]],
                   List[Set.set[A]]]((a: List[Set.set[A]]) =>
                                       Set.insert[A](x, Set.bot_set[A]) :: a,
                                      xs_partitions)
    }
}

} /* object Partitions */

object Big_Operators {

def setsum[A : HOL.equal,
            B : Groups.comm_monoid_add](f: A => B, x1: Set.set[A]):
      B =
  (f, x1) match {
  case (f, Set.Seta(xs)) =>
    Lista.listsum[B](Lista.map[A, B](f, Lista.remdups[A](xs)))
}

} /* object Big_Operators */

object RelationProperties {

import /*implicits*/ Product_Type.equal_prod

def inverse[A, B](r: Set.set[(A, B)]): Set.set[(B, A)] =
  Set.image[(A, B),
             (B, A)]((a: (A, B)) => {
                                      val (x, y): (A, B) = a;
                                      (y, x)
                                    },
                      r)

def eval_rel[A : HOL.equal, B](r: Set.set[(A, B)], a: A): B =
  Set.the_elem[B](Relation.image[A, B](r, Set.insert[A](a, Set.bot_set[A])))

def eval_rel_or[A : HOL.equal, B : HOL.equal](r: Set.set[(A, B)], a: A, z: B):
      B =
  {
    val im: Set.set[B] =
      Relation.image[A, B](r, Set.insert[A](a, Set.bot_set[A]));
    (if (Nat.equal_nata(Finite_Set.card[B](im), Nat.one_nat))
      Set.the_elem[B](im) else z)
  }

def injective_functions_list[A : HOL.equal,
                              B : HOL.equal : Orderings.linorder](x0: List[A],
                           ys: List[B]):
      List[Set.set[(A, B)]] =
  (x0, ys) match {
  case (Nil, ys) => List(Set.bot_set[(A, B)])
  case (x :: xs, ys) =>
    Lista.maps[Set.set[(A, B)],
                Set.set[(A, B)]]((f: Set.set[(A, B)]) =>
                                   Lista.map[B,
      Set.set[(A, B)]]((free_in_range: B) =>
                         Set.sup_set[(A, B)](f,
      Set.insert[(A, B)]((x, free_in_range), Set.bot_set[(A, B)])),
                        Lista.sorted_list_of_set[B](Set.minus_set[B](Set.Seta[B](ys),
                              Relation.range[A, B](f)))),
                                  injective_functions_list[A, B](xs, ys))
}

} /* object RelationProperties */

object nVCG_CaseChecker {

import /*implicits*/ RealDef.equal_real, Nat.linorder_nat,
  RealDef.linorder_real, RealDef.comm_monoid_add_real, Set.equal_set,
  Nat.equal_nat

def revenue_rel(b: Nat.nat => (Set.set[Nat.nat]) => RealDef.real,
                 buyer: Set.set[(Set.set[Nat.nat], Nat.nat)]):
      RealDef.real =
  Big_Operators.setsum[Set.set[Nat.nat],
                        RealDef.real]((y: Set.set[Nat.nat]) =>
(b(RelationProperties.eval_rel[Set.set[Nat.nat], Nat.nat](buyer, y)))(y),
                                       Relation.domain[Set.set[Nat.nat],
                Nat.nat](buyer))

def possible_allocations_comp(g: Set.set[Nat.nat], n: Set.set[Nat.nat]):
      List[Set.set[(Set.set[Nat.nat], Nat.nat)]] =
  Lista.maps[List[Set.set[Nat.nat]],
              Set.set[(Set.set[Nat.nat],
                        Nat.nat)]]((y: List[Set.set[Nat.nat]]) =>
                                     Lista.map[Set.set[(Set.set[Nat.nat],
                 Nat.nat)],
        Set.set[(Set.set[Nat.nat],
                  Nat.nat)]]((potential_buyer:
                                Set.set[(Set.set[Nat.nat], Nat.nat)])
                               => potential_buyer,
                              RelationProperties.injective_functions_list[Set.set[Nat.nat],
                                   Nat.nat](y,
     Lista.sorted_list_of_set[Nat.nat](n))),
                                    Partitions.all_partitions_fun_list[Nat.nat](Lista.sorted_list_of_set[Nat.nat](g)))

def max_revenue_comp(g: Set.set[Nat.nat], n: Set.set[Nat.nat],
                      b: Nat.nat => (Set.set[Nat.nat]) => RealDef.real):
      RealDef.real =
  Maximum.maximum_comp_list[Set.set[(Set.set[Nat.nat], Nat.nat)],
                             RealDef.real](possible_allocations_comp(g, n),
    (a: Set.set[(Set.set[Nat.nat], Nat.nat)]) => revenue_rel(b, a))

def winning_allocations_comp_CL(g: Set.set[Nat.nat], n: Set.set[Nat.nat],
                                 b: Nat.nat =>
                                      (Set.set[Nat.nat]) => RealDef.real):
      List[Set.set[(Set.set[Nat.nat], Nat.nat)]] =
  Maximum.arg_max_comp_list[Set.set[(Set.set[Nat.nat], Nat.nat)],
                             RealDef.real](possible_allocations_comp(g, n),
    (a: Set.set[(Set.set[Nat.nat], Nat.nat)]) => revenue_rel(b, a))

def payments_comp_workaround(g: Set.set[Nat.nat], na: Set.set[Nat.nat],
                              t: (List[Set.set[(Set.set[Nat.nat], Nat.nat)]]) =>
                                   Set.set[(Set.set[Nat.nat], Nat.nat)],
                              b: Nat.nat => (Set.set[Nat.nat]) => RealDef.real,
                              n: Nat.nat):
      RealDef.real =
  RealDef.minus_real(max_revenue_comp(g, Set.remove[Nat.nat](n, na), b),
                      Big_Operators.setsum[Nat.nat,
    RealDef.real]((m: Nat.nat) =>
                    (b(m))(RelationProperties.eval_rel_or[Nat.nat,
                   Set.set[Nat.nat]](RelationProperties.inverse[Set.set[Nat.nat],
                         Nat.nat](t(winning_allocations_comp_CL(g, na, b))),
                                      m, Set.bot_set[Nat.nat])),
                   Set.remove[Nat.nat](n, na)))

} /* object nVCG_CaseChecker */
