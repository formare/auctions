object Vickrey {

trait equal[A] {
  val `Vickrey.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean =
  A.`Vickrey.equal`(a, b)

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

abstract sealed class int
final case class Zero_int() extends int
final case class Pos(a: num) extends int
final case class Neg(a: num) extends int

abstract sealed class nat
final case class Zero_nat() extends nat
final case class Suc(a: nat) extends nat

abstract sealed class rat
final case class Frct(a: (int, int)) extends rat

abstract sealed class set[A]
final case class Set[A](a: List[A]) extends set[A]
final case class Coset[A](a: List[A]) extends set[A]

def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) :: map[A, B](f, xs)
}

def fold[A, B](f: A => B => B, x1: List[A], s: B): B = (f, x1, s) match {
  case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
  case (f, Nil, s) => s
}

def image[A, B](f: A => B, x1: set[A]): set[B] = (f, x1) match {
  case (f, Set(xs)) => Set[B](map[A, B](f, xs))
}

def filtera[A](p: A => Boolean, x1: List[A]): List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x :: xs) => (if (p(x)) x :: filtera[A](p, xs) else filtera[A](p, xs))
}

def filter[A](p: A => Boolean, x1: set[A]): set[A] = (p, x1) match {
  case (p, Set(xs)) => Set[A](filtera[A](p, xs))
}

abstract sealed class real
final case class Ratreal(a: rat) extends real

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

def equal_inta(x0: int, x1: int): Boolean = (x0, x1) match {
  case (Neg(k), Neg(l)) => equal_num(k, l)
  case (Neg(k), Pos(l)) => false
  case (Neg(k), Zero_int()) => false
  case (Pos(k), Neg(l)) => false
  case (Pos(k), Pos(l)) => equal_num(k, l)
  case (Pos(k), Zero_int()) => false
  case (Zero_int(), Neg(l)) => false
  case (Zero_int(), Pos(l)) => false
  case (Zero_int(), Zero_int()) => true
}

implicit def equal_int: equal[int] = new equal[int] {
  val `Vickrey.equal` = (a: int, b: int) => equal_inta(a, b)
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

def less_int(x0: int, x1: int): Boolean = (x0, x1) match {
  case (Neg(k), Neg(l)) => less_num(l, k)
  case (Neg(k), Pos(l)) => true
  case (Neg(k), Zero_int()) => true
  case (Pos(k), Neg(l)) => false
  case (Pos(k), Pos(l)) => less_num(k, l)
  case (Pos(k), Zero_int()) => false
  case (Zero_int(), Neg(l)) => false
  case (Zero_int(), Pos(l)) => true
  case (Zero_int(), Zero_int()) => false
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

def quotient_of(x0: rat): (int, int) = x0 match {
  case Frct(x) => x
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

def times_int(k: int, l: int): int = (k, l) match {
  case (Neg(m), Neg(n)) => Pos(times_num(m, n))
  case (Neg(m), Pos(n)) => Neg(times_num(m, n))
  case (Pos(m), Neg(n)) => Neg(times_num(m, n))
  case (Pos(m), Pos(n)) => Pos(times_num(m, n))
  case (Zero_int(), l) => Zero_int()
  case (k, Zero_int()) => Zero_int()
}

def less_rat(p: rat, q: rat): Boolean =
  {
    val (a, c): (int, int) = quotient_of(p)
    val (b, d): (int, int) = quotient_of(q);
    less_int(times_int(a, d), times_int(c, b))
  }

trait ord[A] {
  val `Vickrey.less_eq`: (A, A) => Boolean
  val `Vickrey.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean =
  A.`Vickrey.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`Vickrey.less`(a, b)

def max[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) b else a)

def equal_prod[A : equal, B : equal](x0: (A, B), x1: (A, B)): Boolean = (x0, x1)
  match {
  case ((aa, ba), (a, b)) => eq[A](aa, a) && eq[B](ba, b)
}

def equal_rat(a: rat, b: rat): Boolean =
  equal_prod[int, int](quotient_of(a), quotient_of(b))

def less_eq_int(x0: int, x1: int): Boolean = (x0, x1) match {
  case (Neg(k), Neg(l)) => less_eq_num(l, k)
  case (Neg(k), Pos(l)) => true
  case (Neg(k), Zero_int()) => true
  case (Pos(k), Neg(l)) => false
  case (Pos(k), Pos(l)) => less_eq_num(k, l)
  case (Pos(k), Zero_int()) => false
  case (Zero_int(), Neg(l)) => false
  case (Zero_int(), Pos(l)) => true
  case (Zero_int(), Zero_int()) => true
}

trait preorder[A] extends ord[A] {
}

trait order[A] extends preorder[A] {
}

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

def maxa[A : linorder](x0: set[A]): A = x0 match {
  case Set(x :: xs) => fold[A, A]((a: A) => (b: A) => max[A](a, b), xs, x)
}

implicit def preorder_real: preorder[real] = new preorder[real] {
  val `Vickrey.less_eq` = (a: real, b: real) => less_eq_real(a, b)
  val `Vickrey.less` = (a: real, b: real) => less_real(a, b)
}

implicit def order_real: order[real] = new order[real] {
  val `Vickrey.less_eq` = (a: real, b: real) => less_eq_real(a, b)
  val `Vickrey.less` = (a: real, b: real) => less_real(a, b)
}

def equal_real(x0: real, x1: real): Boolean = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => equal_rat(x, y)
}

implicit def linorder_real: linorder[real] = new linorder[real] {
  val `Vickrey.less_eq` = (a: real, b: real) => less_eq_real(a, b)
  val `Vickrey.less` = (a: real, b: real) => less_real(a, b)
}

def maximum(n: set[nat], y: nat => real): real =
  maxa[real](image[nat, real](y, n))

def arg_max_set(n: set[nat], b: nat => real): set[nat] =
  filter[nat]((i: nat) => equal_real(maximum(n, b), b(i)), n)

def arg_max_l_tb(x0: List[nat], t: nat => nat => Boolean, b: nat => real): nat =
  (x0, t, b) match {
  case (Nil, t, b) => Zero_nat()
  case (List(x), t, b) => x
  case (x :: v :: va, t, b) =>
    {
      val y: nat = arg_max_l_tb(v :: va, t, b);
      (if (less_real(b(y), b(x))) x
        else (if (equal_real(b(x), b(y)) && (t(x))(y)) x else y))
    }
}

} /* object Vickrey */
