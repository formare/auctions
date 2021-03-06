package code

object Vickrey {

def id[A]: A => A = (x: A) => x

trait equal[A] {
  val `Vickrey.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean =
  A.`Vickrey.equal`(a, b)

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

abstract sealed class int
final case class Int_of_integer(a: BigInt) extends int

abstract sealed class nat
final case class Nat(a: BigInt) extends nat

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

abstract sealed class rat
final case class Frct(a: (int, int)) extends rat

abstract sealed class set[A]
final case class Set[A](a: List[A]) extends set[A]
final case class Coset[A](a: List[A]) extends set[A]

def comp[A, B, C](f: A => B, g: C => A): C => B = (x: C) => f(g(x))

def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) :: map[A, B](f, xs)
}

abstract sealed class real
final case class Ratreal(a: rat) extends real

def fold[A, B](f: A => B => B, x1: List[A], s: B): B = (f, x1, s) match {
  case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
  case (f, Nil, s) => s
}

def image[A, B](f: A => B, x1: set[A]): set[B] = (f, x1) match {
  case (f, Set(xs)) => Set[B](map[A, B](f, xs))
}

def foldr[A, B](f: A => B => B, x1: List[A]): B => B = (f, x1) match {
  case (f, Nil) => id[B]
  case (f, x :: xs) => comp[B, B, B](f(x), foldr[A, B](f, xs))
}

trait ord[A] {
  val `Vickrey.less_eq`: (A, A) => Boolean
  val `Vickrey.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean =
  A.`Vickrey.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`Vickrey.less`(a, b)

def integer_of_nat(x0: nat): BigInt = x0 match {
  case Nat(x) => x
}

def less_eq_nat(m: nat, n: nat): Boolean =
  integer_of_nat(m) <= integer_of_nat(n)

def less_nat(m: nat, n: nat): Boolean = integer_of_nat(m) < integer_of_nat(n)

implicit def ord_nat: ord[nat] = new ord[nat] {
  val `Vickrey.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `Vickrey.less` = (a: nat, b: nat) => less_nat(a, b)
}

def removeAll[A : equal](x: A, xa1: List[A]): List[A] = (x, xa1) match {
  case (x, Nil) => Nil
  case (x, y :: xs) =>
    (if (eq[A](x, y)) removeAll[A](x, xs) else y :: removeAll[A](x, xs))
}

def member[A : equal](x0: List[A], y: A): Boolean = (x0, y) match {
  case (Nil, y) => false
  case (x :: xs, y) => eq[A](x, y) || member[A](xs, y)
}

def insert[A : equal](x: A, xs: List[A]): List[A] =
  (if (member[A](xs, x)) xs else x :: xs)

def remove[A : equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, Coset(xs)) => Coset[A](insert[A](x, xs))
  case (x, Set(xs)) => Set[A](removeAll[A](x, xs))
}

def one_rat: rat = Frct((Int_of_integer(BigInt(1)), Int_of_integer(BigInt(1))))

def integer_of_int(x0: int): BigInt = x0 match {
  case Int_of_integer(k) => k
}

def equal_inta(k: int, l: int): Boolean = integer_of_int(k) == integer_of_int(l)

implicit def equal_int: equal[int] = new equal[int] {
  val `Vickrey.equal` = (a: int, b: int) => equal_inta(a, b)
}

def less_int(k: int, l: int): Boolean = integer_of_int(k) < integer_of_int(l)

def zero_int: int = Int_of_integer(BigInt(0))

def remdups[A : equal](x0: List[A]): List[A] = x0 match {
  case Nil => Nil
  case x :: xs =>
    (if (member[A](xs, x)) remdups[A](xs) else x :: remdups[A](xs))
}

def equal_nata(m: nat, n: nat): Boolean = integer_of_nat(m) == integer_of_nat(n)

implicit def equal_nat: equal[nat] = new equal[nat] {
  val `Vickrey.equal` = (a: nat, b: nat) => equal_nata(a, b)
}

trait preorder[A] extends ord[A] {
}

trait order[A] extends preorder[A] {
}

implicit def preorder_nat: preorder[nat] = new preorder[nat] {
  val `Vickrey.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `Vickrey.less` = (a: nat, b: nat) => less_nat(a, b)
}

implicit def order_nat: order[nat] = new order[nat] {
  val `Vickrey.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `Vickrey.less` = (a: nat, b: nat) => less_nat(a, b)
}

def zero_nat: nat = Nat(BigInt(0))

def quotient_of(x0: rat): (int, int) = x0 match {
  case Frct(x) => x
}

def times_int(k: int, l: int): int =
  Int_of_integer(integer_of_int(k) * integer_of_int(l))

def less_rat(p: rat, q: rat): Boolean =
  {
    val (a, c): (int, int) = quotient_of(p)
    val (b, d): (int, int) = quotient_of(q);
    less_int(times_int(a, d), times_int(c, b))
  }

def zero_rat: rat = Frct((zero_int, Int_of_integer(BigInt(1))))

def less_eq_int(k: int, l: int): Boolean =
  integer_of_int(k) <= integer_of_int(l)

def less_eq_rat(p: rat, q: rat): Boolean =
  {
    val (a, c): (int, int) = quotient_of(p)
    val (b, d): (int, int) = quotient_of(q);
    less_eq_int(times_int(a, d), times_int(c, b))
  }

def less_eq_real(x0: real, x1: real): Boolean = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => less_eq_rat(x, y)
}

def less_real(x0: real, x1: real): Boolean = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => less_rat(x, y)
}

implicit def ord_real: ord[real] = new ord[real] {
  val `Vickrey.less_eq` = (a: real, b: real) => less_eq_real(a, b)
  val `Vickrey.less` = (a: real, b: real) => less_real(a, b)
}

trait linorder[A] extends order[A] {
}

def insort_key[A, B : linorder](f: A => B, x: A, xa2: List[A]): List[A] =
  (f, x, xa2) match {
  case (f, x, Nil) => List(x)
  case (f, x, y :: ys) =>
    (if (less_eq[B](f(x), f(y))) x :: y :: ys
      else y :: insort_key[A, B](f, x, ys))
}

def sort_key[A, B : linorder](f: A => B, xs: List[A]): List[A] =
  (foldr[A, List[A]]((a: A) => (b: List[A]) => insort_key[A, B](f, a, b),
                      xs)).apply(Nil)

def max[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) b else a)

def equal_prod[A : equal, B : equal](x0: (A, B), x1: (A, B)): Boolean = (x0, x1)
  match {
  case ((aa, ba), (a, b)) => eq[A](aa, a) && eq[B](ba, b)
}

def equal_rat(a: rat, b: rat): Boolean =
  equal_prod[int, int](quotient_of(a), quotient_of(b))

implicit def preorder_real: preorder[real] = new preorder[real] {
  val `Vickrey.less_eq` = (a: real, b: real) => less_eq_real(a, b)
  val `Vickrey.less` = (a: real, b: real) => less_real(a, b)
}

implicit def order_real: order[real] = new order[real] {
  val `Vickrey.less_eq` = (a: real, b: real) => less_eq_real(a, b)
  val `Vickrey.less` = (a: real, b: real) => less_real(a, b)
}

def maxa[A : linorder](x0: set[A]): A = x0 match {
  case Set(x :: xs) => fold[A, A]((a: A) => (b: A) => max[A](a, b), xs, x)
}

def maximum[A, B : linorder](n: set[A], y: A => B): B =
  maxa[B](image[A, B](y, n))

implicit def linorder_nat: linorder[nat] = new linorder[nat] {
  val `Vickrey.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `Vickrey.less` = (a: nat, b: nat) => less_nat(a, b)
}

def equal_real(x0: real, x1: real): Boolean = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => equal_rat(x, y)
}

implicit def linorder_real: linorder[real] = new linorder[real] {
  val `Vickrey.less_eq` = (a: real, b: real) => less_eq_real(a, b)
  val `Vickrey.less` = (a: real, b: real) => less_real(a, b)
}

def sorted_list_of_set[A : equal : linorder](x0: set[A]): List[A] = x0 match {
  case Set(xs) => sort_key[A, A]((x: A) => x, remdups[A](xs))
}

def arg_max_l_tb(x0: List[nat], t: nat => nat => Boolean, b: nat => real): nat =
  (x0, t, b) match {
  case (Nil, t, b) => zero_nat
  case (List(x), t, b) => x
  case (x :: v :: va, t, b) =>
    {
      val y: nat = arg_max_l_tb(v :: va, t, b);
      (if (less_real(b(y), b(x))) x
        else (if (equal_real(b(x), b(y)) && (t(x))(y)) x else y))
    }
}

def arg_max_tb(n: set[nat], t: nat => nat => Boolean, b: nat => real): nat =
  arg_max_l_tb(sorted_list_of_set[nat](n), t, b)

def fs_spa_winner(n: set[nat], b: nat => real, t: nat => nat => Boolean): nat =
  arg_max_tb(n, t, b)

def fs_spa_payments(n: set[nat], b: nat => real, t: nat => nat => Boolean):
      nat => real =
  {
    val winner: nat = fs_spa_winner(n, b, t);
    (i: nat) =>
      (if (equal_nata(i, winner)) maximum[nat, real](remove[nat](i, n), b)
        else Ratreal(zero_rat))
  }

def fs_spa_allocation(n: set[nat], b: nat => real, t: nat => nat => Boolean):
      nat => real =
  {
    val winner: nat = fs_spa_winner(n, b, t);
    (i: nat) =>
      (if (equal_nata(i, winner)) Ratreal(one_rat) else Ratreal(zero_rat))
  }

} /* object Vickrey */
