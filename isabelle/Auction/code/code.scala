package code


object Nat {

  def apply(numeral: BigInt): Nat = new Nat(numeral max 0)
  def apply(numeral: Int): Nat = Nat(BigInt(numeral))
  def apply(numeral: String): Nat = Nat(BigInt(numeral))

}

class Nat private(private val value: BigInt) {

  override def hashCode(): Int = this.value.hashCode()

  override def equals(that: Any): Boolean = that match {
    case that: Nat => this equals that
    case _ => false
  }

  override def toString(): String = this.value.toString

  def equals(that: Nat): Boolean = this.value == that.value

  def as_BigInt: BigInt = this.value
  def as_Int: Int = if (this.value >= scala.Int.MinValue && this.value <= scala.Int.MaxValue)
      this.value.intValue
    else error("Int value out of range: " + this.value.toString)

  def +(that: Nat): Nat = new Nat(this.value + that.value)
  def -(that: Nat): Nat = Nat(this.value - that.value)
  def *(that: Nat): Nat = new Nat(this.value * that.value)

  def /%(that: Nat): (Nat, Nat) = if (that.value == 0) (new Nat(0), this)
    else {
      val (k, l) = this.value /% that.value
      (new Nat(k), new Nat(l))
    }

  def <=(that: Nat): Boolean = this.value <= that.value

  def <(that: Nat): Boolean = this.value < that.value

}


object Natural {

  def apply(numeral: BigInt): Natural = new Natural(numeral max 0)
  def apply(numeral: Int): Natural = Natural(BigInt(numeral))
  def apply(numeral: String): Natural = Natural(BigInt(numeral))

}

class Natural private(private val value: BigInt) {

  override def hashCode(): Int = this.value.hashCode()

  override def equals(that: Any): Boolean = that match {
    case that: Natural => this equals that
    case _ => false
  }

  override def toString(): String = this.value.toString

  def equals(that: Natural): Boolean = this.value == that.value

  def as_BigInt: BigInt = this.value
  def as_Int: Int = if (this.value >= scala.Int.MinValue && this.value <= scala.Int.MaxValue)
      this.value.intValue
    else error("Int value out of range: " + this.value.toString)

  def +(that: Natural): Natural = new Natural(this.value + that.value)
  def -(that: Natural): Natural = Natural(this.value - that.value)
  def *(that: Natural): Natural = new Natural(this.value * that.value)

  def /%(that: Natural): (Natural, Natural) = if (that.value == 0) (new Natural(0), this)
    else {
      val (k, l) = this.value /% that.value
      (new Natural(k), new Natural(l))
    }

  def <=(that: Natural): Boolean = this.value <= that.value

  def <(that: Natural): Boolean = this.value < that.value

}


object Vickrey {

trait equal[A] {
  val `Vickrey.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean =
  A.`Vickrey.equal`(a, b)

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

abstract sealed class rat
final case class Frct(a: (BigInt, BigInt)) extends rat

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

implicit def equal_int: equal[BigInt] = new equal[BigInt] {
  val `Vickrey.equal` = (a: BigInt, b: BigInt) => a == b
}

def quotient_of(x0: rat): (BigInt, BigInt) = x0 match {
  case Frct(x) => x
}

def less_rat(p: rat, q: rat): Boolean =
  {
    val (a, c): (BigInt, BigInt) = quotient_of(p)
    val (b, d): (BigInt, BigInt) = quotient_of(q);
    a * d < c * b
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
  equal_prod[BigInt, BigInt](quotient_of(a), quotient_of(b))

trait preorder[A] extends ord[A] {
}

trait order[A] extends preorder[A] {
}

def less_eq_rat(p: rat, q: rat): Boolean =
  {
    val (a, c): (BigInt, BigInt) = quotient_of(p)
    val (b, d): (BigInt, BigInt) = quotient_of(q);
    a * d <= c * b
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

def maximum(n: set[Nat], y: Nat => real): real =
  maxa[real](image[Nat, real](y, n))

def arg_max_set(n: set[Nat], b: Nat => real): set[Nat] =
  filter[Nat]((i: Nat) => equal_real(maximum(n, b), b(i)), n)

def arg_max_l_tb(x0: List[Nat], t: Nat => Nat => Boolean, b: Nat => real): Nat =
  (x0, t, b) match {
  case (Nil, t, b) => Nat(0)
  case (List(x), t, b) => x
  case (x :: v :: va, t, b) =>
    {
      val y: Nat = arg_max_l_tb(v :: va, t, b);
      (if (less_real(b(y), b(x))) x
        else (if (equal_real(b(x), b(y)) && (t(x))(y)) x else y))
    }
}

} /* object Vickrey */
