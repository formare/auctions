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

def id[A]: A => A = (x: A) => x

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

def comp[A, B, C](f: A => B, g: C => A): C => B = (x: C) => f(g(x))

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

implicit def ord_nat: ord[Nat] = new ord[Nat] {
  val `Vickrey.less_eq` = (a: Nat, b: Nat) => a <= b
  val `Vickrey.less` = (a: Nat, b: Nat) => a < b
}

def member[A : equal](x0: List[A], y: A): Boolean = (x0, y) match {
  case (Nil, y) => false
  case (x :: xs, y) => eq[A](x, y) || member[A](xs, y)
}

abstract sealed class real
final case class Ratreal(a: rat) extends real

implicit def equal_int: equal[BigInt] = new equal[BigInt] {
  val `Vickrey.equal` = (a: BigInt, b: BigInt) => a == b
}

def remdups[A : equal](x0: List[A]): List[A] = x0 match {
  case Nil => Nil
  case x :: xs =>
    (if (member[A](xs, x)) remdups[A](xs) else x :: remdups[A](xs))
}

implicit def equal_nat: equal[Nat] = new equal[Nat] {
  val `Vickrey.equal` = (a: Nat, b: Nat) => a == b
}

trait preorder[A] extends ord[A] {
}

trait order[A] extends preorder[A] {
}

implicit def preorder_nat: preorder[Nat] = new preorder[Nat] {
  val `Vickrey.less_eq` = (a: Nat, b: Nat) => a <= b
  val `Vickrey.less` = (a: Nat, b: Nat) => a < b
}

implicit def order_nat: order[Nat] = new order[Nat] {
  val `Vickrey.less_eq` = (a: Nat, b: Nat) => a <= b
  val `Vickrey.less` = (a: Nat, b: Nat) => a < b
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

def equal_prod[A : equal, B : equal](x0: (A, B), x1: (A, B)): Boolean = (x0, x1)
  match {
  case ((aa, ba), (a, b)) => eq[A](aa, a) && eq[B](ba, b)
}

def equal_rat(a: rat, b: rat): Boolean =
  equal_prod[BigInt, BigInt](quotient_of(a), quotient_of(b))

implicit def linorder_nat: linorder[Nat] = new linorder[Nat] {
  val `Vickrey.less_eq` = (a: Nat, b: Nat) => a <= b
  val `Vickrey.less` = (a: Nat, b: Nat) => a < b
}

def less_real(x0: real, x1: real): Boolean = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => less_rat(x, y)
}

def equal_real(x0: real, x1: real): Boolean = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => equal_rat(x, y)
}

def sorted_list_of_set[A : equal : linorder](x0: set[A]): List[A] = x0 match {
  case Set(xs) => sort_key[A, A]((x: A) => x, remdups[A](xs))
}

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

def arg_max_tb(n: set[Nat], t: Nat => Nat => Boolean, b: Nat => real): Nat =
  arg_max_l_tb(sorted_list_of_set[Nat](n), t, b)

} /* object Vickrey */
