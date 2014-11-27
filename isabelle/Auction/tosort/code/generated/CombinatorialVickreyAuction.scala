package CombinatorialVickreyAuction

object Fun {

def id[A]: A => A = (x: A) => x

def comp[A, B, C](f: A => B, g: C => A): C => B = (x: C) => f(g(x))

} /* object Fun */

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

object Groups {

trait plus[A] {
  val `Groups.plus`: (A, A) => A
}
def plus[A](a: A, b: A)(implicit A: plus[A]): A = A.`Groups.plus`(a, b)

trait zero[A] {
  val `Groups.zero`: A
}
def zero[A](implicit A: zero[A]): A = A.`Groups.zero`

trait minus[A] {
  val `Groups.minus`: (A, A) => A
}
def minus[A](a: A, b: A)(implicit A: minus[A]): A = A.`Groups.minus`(a, b)

trait semigroup_add[A] extends plus[A] {
}

trait monoid_add[A] extends semigroup_add[A] with zero[A] {
}

trait ab_semigroup_add[A] extends semigroup_add[A] {
}

trait comm_monoid_add[A] extends ab_semigroup_add[A] with monoid_add[A] {
}

} /* object Groups */

object HOL {

trait equal[A] {
  val `HOL.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`HOL.equal`(a, b)

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

} /* object HOL */

object Num {

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

} /* object Num */

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

def product[A, B](x0: Set.set[A], x1: Set.set[B]): Set.set[(A, B)] = (x0, x1)
  match {
  case (Set.Seta(xs), Set.Seta(ys)) =>
    Set.Seta[(A, B)](Lista.maps[A, (A, B)]((x: A) =>
     Lista.map[B, (A, B)]((a: B) => (x, a), ys),
    xs))
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

object Lista {

def hd[A](x0: List[A]): A = x0 match {
  case x :: xs => x
}

def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) :: map[A, B](f, xs)
}

def fold[A, B](f: A => B => B, x1: List[A], s: B): B = (f, x1, s) match {
  case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
  case (f, Nil, s) => s
}

def maps[A, B](f: A => List[B], x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) ++ maps[A, B](f, xs)
}

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

def remove1[A : HOL.equal](x: A, xa1: List[A]): List[A] = (x, xa1) match {
  case (x, Nil) => Nil
  case (x, y :: xs) => (if (HOL.eq[A](x, y)) xs else y :: remove1[A](x, xs))
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
  case (n, x :: xs) => gen_length[A](Nat.suc(n), xs)
  case (n, Nil) => n
}

def size_list[A]: (List[A]) => Nat.nat =
  (a: List[A]) => gen_length[A](Nat.zero_nat, a)

def map_filter[A, B](f: A => Option[B], x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) =>
    (f(x) match {
       case None => map_filter[A, B](f, xs)
       case Some(y) => y :: map_filter[A, B](f, xs)
     })
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

object Nat {

abstract sealed class nat
final case class Nata(a: BigInt) extends nat

def plus_nat(m: nat, n: nat): nat =
  Nata(Code_Numeral.integer_of_nat(m) + Code_Numeral.integer_of_nat(n))

def one_nat: nat = Nata(BigInt(1))

def suc(n: nat): nat = plus_nat(n, one_nat)

def less_eq_nat(m: nat, n: nat): Boolean =
  Code_Numeral.integer_of_nat(m) <= Code_Numeral.integer_of_nat(n)

def less_nat(m: nat, n: nat): Boolean =
  Code_Numeral.integer_of_nat(m) < Code_Numeral.integer_of_nat(n)

implicit def ord_nat: Orderings.ord[nat] = new Orderings.ord[nat] {
  val `Orderings.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `Orderings.less` = (a: nat, b: nat) => less_nat(a, b)
}

def equal_nata(m: nat, n: nat): Boolean =
  Code_Numeral.integer_of_nat(m) == Code_Numeral.integer_of_nat(n)

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

def zero_nat: nat = Nata(BigInt(0))

implicit def linorder_nat: Orderings.linorder[nat] = new Orderings.linorder[nat]
  {
  val `Orderings.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `Orderings.less` = (a: nat, b: nat) => less_nat(a, b)
}

} /* object Nat */

object Int {

abstract sealed class int
final case class Int_of_integer(a: BigInt) extends int

def uminus_int(k: int): int =
  Int_of_integer((- (Code_Numeral.integer_of_int(k))))

def zero_int: int = Int_of_integer(BigInt(0))

def less_int(k: int, l: int): Boolean =
  Code_Numeral.integer_of_int(k) < Code_Numeral.integer_of_int(l)

def abs_int(i: int): int = (if (less_int(i, zero_int)) uminus_int(i) else i)

def equal_inta(k: int, l: int): Boolean =
  Code_Numeral.integer_of_int(k) == Code_Numeral.integer_of_int(l)

implicit def equal_int: HOL.equal[int] = new HOL.equal[int] {
  val `HOL.equal` = (a: int, b: int) => equal_inta(a, b)
}

def plus_int(k: int, l: int): int =
  Int_of_integer(Code_Numeral.integer_of_int(k) +
                   Code_Numeral.integer_of_int(l))

def minus_int(k: int, l: int): int =
  Int_of_integer(Code_Numeral.integer_of_int(k) -
                   Code_Numeral.integer_of_int(l))

def times_int(k: int, l: int): int =
  Int_of_integer(Code_Numeral.integer_of_int(k) *
                   Code_Numeral.integer_of_int(l))

def less_eq_int(k: int, l: int): Boolean =
  Code_Numeral.integer_of_int(k) <= Code_Numeral.integer_of_int(l)

} /* object Int */

object Code_Numeral {

def abs_integer(k: BigInt): BigInt = (if (k < BigInt(0)) (- k) else k)

def sgn_integer(k: BigInt): BigInt =
  (if (k == BigInt(0)) BigInt(0)
    else (if (k < BigInt(0)) (- BigInt(1)) else BigInt(1)))

def divmod_integer(k: BigInt, l: BigInt): (BigInt, BigInt) =
  (if (k == BigInt(0)) (BigInt(0), BigInt(0))
    else (if (l == BigInt(0)) (BigInt(0), k)
           else (Fun.comp[BigInt, ((BigInt, BigInt)) => (BigInt, BigInt),
                           BigInt](Fun.comp[BigInt => BigInt,
     ((BigInt, BigInt)) => (BigInt, BigInt),
     BigInt]((a: BigInt => BigInt) =>
               (b: (BigInt, BigInt)) =>
                 Product_Type.apsnd[BigInt, BigInt, BigInt](a, b),
              (a: BigInt) => (b: BigInt) => a * b),
                                    (a: BigInt) =>
                                      sgn_integer(a))).apply(l).apply((if (sgn_integer(k) ==
                                     sgn_integer(l))
                                ((k: BigInt) => (l: BigInt) => if (l == 0)
                                  (BigInt(0), k) else
                                  (k.abs /% l.abs)).apply(k).apply(l)
                                else {
                                       val (r, s): (BigInt, BigInt) =
 ((k: BigInt) => (l: BigInt) => if (l == 0) (BigInt(0), k) else
   (k.abs /% l.abs)).apply(k).apply(l);
                                       (if (s == BigInt(0)) ((- r), BigInt(0))
 else ((- r) - BigInt(1), abs_integer(l) - s))
                                     }))))

def div_integer(k: BigInt, l: BigInt): BigInt =
  Product_Type.fst[BigInt, BigInt](divmod_integer(k, l))

def mod_integer(k: BigInt, l: BigInt): BigInt =
  Product_Type.snd[BigInt, BigInt](divmod_integer(k, l))

def integer_of_int(x0: Int.int): BigInt = x0 match {
  case Int.Int_of_integer(k) => k
}

def integer_of_nat(x0: Nat.nat): BigInt = x0 match {
  case Nat.Nata(x) => x
}

} /* object Code_Numeral */

object Divides {

def div_int(k: Int.int, l: Int.int): Int.int =
  Int.Int_of_integer(Code_Numeral.div_integer(Code_Numeral.integer_of_int(k),
       Code_Numeral.integer_of_int(l)))

def mod_int(k: Int.int, l: Int.int): Int.int =
  Int.Int_of_integer(Code_Numeral.mod_integer(Code_Numeral.integer_of_int(k),
       Code_Numeral.integer_of_int(l)))

} /* object Divides */

object GCD {

def gcd_int(k: Int.int, l: Int.int): Int.int =
  Int.abs_int((if (Int.equal_inta(l, Int.zero_int)) k
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
    Int.less_int(Int.times_int(a, d), Int.times_int(c, b))
  }

def normalize(p: (Int.int, Int.int)): (Int.int, Int.int) =
  (if (Int.less_int(Int.zero_int, Product_Type.snd[Int.int, Int.int](p)))
    {
      val a: Int.int =
        GCD.gcd_int(Product_Type.fst[Int.int, Int.int](p),
                     Product_Type.snd[Int.int, Int.int](p));
      (Divides.div_int(Product_Type.fst[Int.int, Int.int](p), a),
        Divides.div_int(Product_Type.snd[Int.int, Int.int](p), a))
    }
    else (if (Int.equal_inta(Product_Type.snd[Int.int, Int.int](p),
                              Int.zero_int))
           (Int.zero_int, Int.Int_of_integer(BigInt(1)))
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
         normalize((Int.plus_int(Int.times_int(a, d), Int.times_int(b, c)),
                     Int.times_int(c, d)))
       })

def zero_rat: rat = Frct((Int.zero_int, Int.Int_of_integer(BigInt(1))))

def equal_rat(a: rat, b: rat): Boolean =
  Product_Type.equal_proda[Int.int, Int.int](quotient_of(a), quotient_of(b))

def minus_rat(p: rat, q: rat): rat =
  Frct({
         val (a, c): (Int.int, Int.int) = quotient_of(p)
         val (b, d): (Int.int, Int.int) = quotient_of(q);
         normalize((Int.minus_int(Int.times_int(a, d), Int.times_int(b, c)),
                     Int.times_int(c, d)))
       })

def less_eq_rat(p: rat, q: rat): Boolean =
  {
    val (a, c): (Int.int, Int.int) = quotient_of(p)
    val (b, d): (Int.int, Int.int) = quotient_of(q);
    Int.less_eq_int(Int.times_int(a, d), Int.times_int(c, b))
  }

} /* object Rat */

object Real {

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

def minus_reala(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(Rat.minus_rat(x, y))
}

implicit def minus_real: Groups.minus[real] = new Groups.minus[real] {
  val `Groups.minus` = (a: real, b: real) => minus_reala(a, b)
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

} /* object Real */

object Maximum {

def arg_max_alg_list[A, B : HOL.equal : Orderings.linorder](x0: List[A],
                     f: A => B):
      List[A] =
  (x0, f) match {
  case (Nil, f) => Nil
  case (List(x), f) => List(x)
  case (x :: v :: va, f) =>
    {
      val arg_max_xs: List[A] = arg_max_alg_list[A, B](v :: va, f)
      val prev_max: B = f(Lista.hd[A](arg_max_xs));
      (if (Orderings.less[B](prev_max, f(x))) List(x)
        else (if (HOL.eq[B](f(x), prev_max)) x :: arg_max_xs else arg_max_xs))
    }
}

def maximum_alg_list[A, B : Orderings.linorder](x0: List[A], b: A => B): B =
  (x0, b) match {
  case (Nil, b) => sys.error("undefined")
  case (List(x), b) => b(x)
  case (x :: v :: va, b) =>
    {
      val max_xs: B = maximum_alg_list[A, B](v :: va, b);
      (if (Orderings.less[B](max_xs, b(x))) b(x) else max_xs)
    }
}

} /* object Maximum */

object Lattices {

def minus_funa[A, B : Groups.minus](a: A => B, b: A => B, x: A): B =
  Groups.minus[B](a(x), b(x))

implicit def minus_fun[A, B : Groups.minus]: Groups.minus[A => B] = new
  Groups.minus[A => B] {
  val `Groups.minus` = (a: A => B, b: A => B) => (c: A) =>
    minus_funa[A, B](a, b, c)
}

} /* object Lattices */

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

def converse[A, B](r: Set.set[(A, B)]): Set.set[(B, A)] =
  Set.image[(A, B),
             (B, A)]((a: (A, B)) => {
                                      val (x, y): (A, B) = a;
                                      (y, x)
                                    },
                      r)

} /* object Relation */

object Finite_Set {

def card[A : HOL.equal](x0: Set.set[A]): Nat.nat = x0 match {
  case Set.Seta(xs) => Lista.size_list[A].apply(Lista.remdups[A](xs))
}

} /* object Finite_Set */

object Partitions {

import /*implicits*/ Set.equal_set

def insert_into_member_list[A : HOL.equal](new_el: A, sets: List[Set.set[A]],
    s: Set.set[A]):
      List[Set.set[A]] =
  Set.sup_set[A](s, Set.insert[A](new_el, Set.bot_set[A])) ::
    Lista.remove1[Set.set[A]](s, sets)

def coarser_partitions_with_list[A : HOL.equal](new_el: A, p: List[Set.set[A]]):
      List[List[Set.set[A]]] =
  (Set.insert[A](new_el, Set.bot_set[A]) :: p) ::
    Lista.map[Set.set[A],
               List[Set.set[A]]]((a: Set.set[A]) =>
                                   insert_into_member_list[A](new_el, p, a),
                                  p)

def all_coarser_partitions_with_list[A : HOL.equal](elem: A,
             ps: List[List[Set.set[A]]]):
      List[List[Set.set[A]]] =
  Lista.maps[List[Set.set[A]],
              List[Set.set[A]]]((a: List[Set.set[A]]) =>
                                  coarser_partitions_with_list[A](elem, a),
                                 ps)

def all_partitions_list[A : HOL.equal](x0: List[A]): List[List[Set.set[A]]] = x0
  match {
  case Nil => List(Nil)
  case e :: x =>
    all_coarser_partitions_with_list[A](e, all_partitions_list[A](x))
}

def all_partitions_alg[A : HOL.equal : Orderings.linorder](x: Set.set[A]):
      List[List[Set.set[A]]] =
  all_partitions_list[A](Lista.sorted_list_of_set[A](x))

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

object RelationOperators {

import /*implicits*/ Product_Type.equal_prod

def outside[A : HOL.equal, B : HOL.equal](r: Set.set[(A, B)], x: Set.set[A]):
      Set.set[(A, B)] =
  Set.minus_set[(A, B)](r, Product_Type.product[A,
         B](x, Relation.range[A, B](r)))

def paste[A : HOL.equal, B : HOL.equal](p: Set.set[(A, B)], q: Set.set[(A, B)]):
      Set.set[(A, B)] =
  Set.sup_set[(A, B)](outside[A, B](p, Relation.domain[A, B](q)), q)

def eval_rel[A : HOL.equal, B](r: Set.set[(A, B)], a: A): B =
  Set.the_elem[B](Relation.image[A, B](r, Set.insert[A](a, Set.bot_set[A])))

} /* object RelationOperators */

object RelationProperties {

import /*implicits*/ Product_Type.equal_prod

def eval_rel_or[A : HOL.equal, B : HOL.equal](r: Set.set[(A, B)], a: A, z: B):
      B =
  {
    val im: Set.set[B] =
      Relation.image[A, B](r, Set.insert[A](a, Set.bot_set[A]));
    (if (Nat.equal_nata(Finite_Set.card[B](im), Nat.one_nat))
      Set.the_elem[B](im) else z)
  }

def sup_rels_from_alg[A : HOL.equal,
                       B : HOL.equal : Orderings.linorder](r: Set.set[(A, B)],
                    x: A, y: Set.set[B]):
      List[Set.set[(A, B)]] =
  Lista.map[B, Set.set[(A, B)]]((ya: B) =>
                                  RelationOperators.paste[A,
                   B](r, Set.insert[(A, B)]((x, ya), Set.bot_set[(A, B)])),
                                 Lista.sorted_list_of_set[B](Set.minus_set[B](y,
                                       Relation.range[A, B](r))))

def injections_alg[A : HOL.equal,
                    B : HOL.equal : Orderings.linorder](x0: List[A],
                 y: Set.set[B]):
      List[Set.set[(A, B)]] =
  (x0, y) match {
  case (Nil, y) => List(Set.bot_set[(A, B)])
  case (x :: xs, y) =>
    Lista.maps[Set.set[(A, B)],
                Set.set[(A, B)]]((r: Set.set[(A, B)]) =>
                                   sup_rels_from_alg[A, B](r, x, y),
                                  injections_alg[A, B](xs, y))
}

} /* object RelationProperties */

object CombinatorialAuction {

import /*implicits*/ Nat.linorder_nat, Real.comm_monoid_add_real, Set.equal_set,
  Nat.equal_nat

def value_rel(b: Nat.nat => (Set.set[Nat.nat]) => Real.real,
               buyer: Set.set[(Set.set[Nat.nat], Nat.nat)]):
      Real.real =
  Big_Operators.setsum[Set.set[Nat.nat],
                        Real.real]((y: Set.set[Nat.nat]) =>
                                     (b(RelationOperators.eval_rel[Set.set[Nat.nat],
                            Nat.nat](buyer, y)))(y),
                                    Relation.domain[Set.set[Nat.nat],
             Nat.nat](buyer))

def possible_allocations_alg(g: Set.set[Nat.nat], n: Set.set[Nat.nat]):
      List[Set.set[(Set.set[Nat.nat], Nat.nat)]] =
  Lista.maps[List[Set.set[Nat.nat]],
              Set.set[(Set.set[Nat.nat],
                        Nat.nat)]]((y: List[Set.set[Nat.nat]]) =>
                                     RelationProperties.injections_alg[Set.set[Nat.nat],
                                Nat.nat](y, n),
                                    Partitions.all_partitions_alg[Nat.nat](g))

} /* object CombinatorialAuction */

object CombinatorialVickreyAuction {

import /*implicits*/ Real.equal_real, Real.comm_monoid_add_real, Set.equal_set,
  Lattices.minus_fun, Real.minus_real, Real.linorder_real, Nat.equal_nat

def alpha_alg(g: Set.set[Nat.nat], na: Set.set[Nat.nat],
               b: Nat.nat => (Set.set[Nat.nat]) => Real.real, n: Nat.nat):
      Real.real =
  Maximum.maximum_alg_list[Set.set[(Set.set[Nat.nat], Nat.nat)],
                            Real.real](CombinatorialAuction.possible_allocations_alg(g,
      Set.remove[Nat.nat](n, na)),
(a: Set.set[(Set.set[Nat.nat], Nat.nat)]) =>
  CombinatorialAuction.value_rel(b, a))

def winning_allocations_alg_CL(g: Set.set[Nat.nat], n: Set.set[Nat.nat],
                                b: Nat.nat => (Set.set[Nat.nat]) => Real.real):
      List[Set.set[(Set.set[Nat.nat], Nat.nat)]] =
  Maximum.arg_max_alg_list[Set.set[(Set.set[Nat.nat], Nat.nat)],
                            Real.real](CombinatorialAuction.possible_allocations_alg(g,
      n),
(a: Set.set[(Set.set[Nat.nat], Nat.nat)]) =>
  CombinatorialAuction.value_rel(b, a))

def winning_allocation_alg_CL(g: Set.set[Nat.nat], n: Set.set[Nat.nat],
                               t: (List[Set.set[(Set.set[Nat.nat],
          Nat.nat)]]) =>
                                    Set.set[(Set.set[Nat.nat], Nat.nat)],
                               b: Nat.nat => (Set.set[Nat.nat]) => Real.real):
      Set.set[(Set.set[Nat.nat], Nat.nat)] =
  t(winning_allocations_alg_CL(g, n, b))

def remaining_value_alg(g: Set.set[Nat.nat], na: Set.set[Nat.nat],
                         t: (List[Set.set[(Set.set[Nat.nat], Nat.nat)]]) =>
                              Set.set[(Set.set[Nat.nat], Nat.nat)],
                         b: Nat.nat => (Set.set[Nat.nat]) => Real.real,
                         n: Nat.nat):
      Real.real =
  Big_Operators.setsum[Nat.nat,
                        Real.real]((m: Nat.nat) =>
                                     (b(m))(RelationProperties.eval_rel_or[Nat.nat,
                                    Set.set[Nat.nat]](Relation.converse[Set.set[Nat.nat],
                                 Nat.nat](winning_allocation_alg_CL(g, na, t,
                             b)),
               m, Set.bot_set[Nat.nat])),
                                    Set.remove[Nat.nat](n, na))

def payments_alg(g: Set.set[Nat.nat], n: Set.set[Nat.nat],
                  t: (List[Set.set[(Set.set[Nat.nat], Nat.nat)]]) =>
                       Set.set[(Set.set[Nat.nat], Nat.nat)]):
      (Nat.nat => (Set.set[Nat.nat]) => Real.real) => Nat.nat => Real.real =
  (a: Nat.nat => (Set.set[Nat.nat]) => Real.real) =>
    Lattices.minus_funa[Nat.nat => (Set.set[Nat.nat]) => Real.real,
                         Nat.nat =>
                           Real.real]((aa:
 Nat.nat => (Set.set[Nat.nat]) => Real.real)
=> (b: Nat.nat) => alpha_alg(g, n, aa, b),
                                       (aa:
  Nat.nat => (Set.set[Nat.nat]) => Real.real)
 => (b: Nat.nat) => remaining_value_alg(g, n, t, aa, b),
                                       a)

} /* object CombinatorialVickreyAuction */
