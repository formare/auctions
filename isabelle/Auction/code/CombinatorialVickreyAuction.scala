package CombinatorialVickreyAuction


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


object CombinatorialVickreyAuction {

def id[A]: A => A = (x: A) => x

trait equal[A] {
  val `CombinatorialVickreyAuction.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean =
  A.`CombinatorialVickreyAuction.equal`(a, b)

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

abstract sealed class rat
final case class Frct(a: (BigInt, BigInt)) extends rat

abstract sealed class set[A]
final case class Set[A](a: List[A]) extends set[A]
final case class Coset[A](a: List[A]) extends set[A]

def hd[A](x0: List[A]): A = x0 match {
  case x :: xs => x
}

def suc(n: Nat): Nat = n + Nat(1)

def comp[A, B, C](f: A => B, g: C => A): C => B = (x: C) => f(g(x))

def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) :: map[A, B](f, xs)
}

def nth[A](x0: List[A], n: Nat): A = (x0, n) match {
  case (x :: xs, n) => (if (n == Nat(0)) x else nth[A](xs, n - Nat(1)))
}

def fold[A, B](f: A => B => B, x1: List[A], s: B): B = (f, x1, s) match {
  case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
  case (f, Nil, s) => s
}

def maps[A, B](f: A => List[B], x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) ++ maps[A, B](f, xs)
}

def upto(i: BigInt, j: BigInt): List[BigInt] =
  (if (i <= j) i :: upto(i + BigInt(1), j) else Nil)

def image[A, B](f: A => B, x1: set[A]): set[B] = (f, x1) match {
  case (f, Set(xs)) => Set[B](map[A, B](f, xs))
}

def foldr[A, B](f: A => B => B, x1: List[A]): B => B = (f, x1) match {
  case (f, Nil) => id[B]
  case (f, x :: xs) => comp[B, B, B](f(x), foldr[A, B](f, xs))
}

trait ord[A] {
  val `CombinatorialVickreyAuction.less_eq`: (A, A) => Boolean
  val `CombinatorialVickreyAuction.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean =
  A.`CombinatorialVickreyAuction.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean =
  A.`CombinatorialVickreyAuction.less`(a, b)

implicit def ord_nat: ord[Nat] = new ord[Nat] {
  val `CombinatorialVickreyAuction.less_eq` = (a: Nat, b: Nat) => a <= b
  val `CombinatorialVickreyAuction.less` = (a: Nat, b: Nat) => a < b
}

def removeAll[A : equal](x: A, xa1: List[A]): List[A] = (x, xa1) match {
  case (x, Nil) => Nil
  case (x, y :: xs) =>
    (if (eq[A](x, y)) removeAll[A](x, xs) else y :: removeAll[A](x, xs))
}

def membera[A : equal](x0: List[A], y: A): Boolean = (x0, y) match {
  case (Nil, y) => false
  case (x :: xs, y) => eq[A](x, y) || membera[A](xs, y)
}

def inserta[A : equal](x: A, xs: List[A]): List[A] =
  (if (membera[A](xs, x)) xs else x :: xs)

def insert[A : equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, Coset(xs)) => Coset[A](removeAll[A](x, xs))
  case (x, Set(xs)) => Set[A](inserta[A](x, xs))
}

def member[A : equal](x: A, xa1: set[A]): Boolean = (x, xa1) match {
  case (x, Coset(xs)) => ! (membera[A](xs, x))
  case (x, Set(xs)) => membera[A](xs, x)
}

def remove[A : equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, Coset(xs)) => Coset[A](inserta[A](x, xs))
  case (x, Set(xs)) => Set[A](removeAll[A](x, xs))
}

def apsnd[A, B, C](f: A => B, x1: (C, A)): (C, B) = (f, x1) match {
  case (f, (x, y)) => (x, f(y))
}

def sgn_int(i: BigInt): BigInt =
  (if (i == BigInt(0)) BigInt(0)
    else (if (BigInt(0) < i) BigInt(1) else (- BigInt(1))))

def abs_int(i: BigInt): BigInt = (if (i < BigInt(0)) (- i) else i)

def divmod_int(k: BigInt, l: BigInt): (BigInt, BigInt) =
  (if (k == BigInt(0)) (BigInt(0), BigInt(0))
    else (if (l == BigInt(0)) (BigInt(0), k)
           else apsnd[BigInt, BigInt,
                       BigInt]((a: BigInt) => sgn_int(l) * a,
                                (if (sgn_int(k) == sgn_int(l))
                                  ((k: BigInt) => (l: BigInt) => if (l == 0)
                                    (BigInt(0), k) else
                                    (k.abs /% l.abs)).apply(k).apply(l)
                                  else {
 val (r, s): (BigInt, BigInt) =
   ((k: BigInt) => (l: BigInt) => if (l == 0) (BigInt(0), k) else
     (k.abs /% l.abs)).apply(k).apply(l);
 (if (s == BigInt(0)) ((- r), BigInt(0))
   else ((- r) - BigInt(1), abs_int(l) - s))
                                       }))))

def snd[A, B](x0: (A, B)): B = x0 match {
  case (a, b) => b
}

def mod_int(a: BigInt, b: BigInt): BigInt =
  snd[BigInt, BigInt](divmod_int(a, b))

def gcd_int(k: BigInt, l: BigInt): BigInt =
  abs_int((if (l == BigInt(0)) k
            else gcd_int(l, mod_int(abs_int(k), abs_int(l)))))

trait plus[A] {
  val `CombinatorialVickreyAuction.plus`: (A, A) => A
}
def plus[A](a: A, b: A)(implicit A: plus[A]): A =
  A.`CombinatorialVickreyAuction.plus`(a, b)

trait zero[A] {
  val `CombinatorialVickreyAuction.zero`: A
}
def zero[A](implicit A: zero[A]): A = A.`CombinatorialVickreyAuction.zero`

def filter[A](p: A => Boolean, x1: List[A]): List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x :: xs) => (if (p(x)) x :: filter[A](p, xs) else filter[A](p, xs))
}

abstract sealed class real
final case class Ratreal(a: rat) extends real

def bot_set[A]: set[A] = Set[A](Nil)

def sup_set[A : equal](x0: set[A], a: set[A]): set[A] = (x0, a) match {
  case (Coset(xs), a) => Coset[A](filter[A]((x: A) => ! (member[A](x, a)), xs))
  case (Set(xs), a) =>
    fold[A, set[A]]((aa: A) => (b: set[A]) => insert[A](aa, b), xs, a)
}

trait minus[A] {
  val `CombinatorialVickreyAuction.minus`: (A, A) => A
}
def minus[A](a: A, b: A)(implicit A: minus[A]): A =
  A.`CombinatorialVickreyAuction.minus`(a, b)

implicit def equal_int: equal[BigInt] = new equal[BigInt] {
  val `CombinatorialVickreyAuction.equal` = (a: BigInt, b: BigInt) => a == b
}

trait semigroup_add[A] extends plus[A] {
}

trait monoid_add[A] extends semigroup_add[A] with zero[A] {
}

def listsum[A : monoid_add](xs: List[A]): A =
  (foldr[A, A]((a: A) => (b: A) => plus[A](a, b), xs)).apply(zero[A])

def remdups[A : equal](x0: List[A]): List[A] = x0 match {
  case Nil => Nil
  case x :: xs =>
    (if (membera[A](xs, x)) remdups[A](xs) else x :: remdups[A](xs))
}

implicit def equal_nat: equal[Nat] = new equal[Nat] {
  val `CombinatorialVickreyAuction.equal` = (a: Nat, b: Nat) => a == b
}

trait preorder[A] extends ord[A] {
}

trait order[A] extends preorder[A] {
}

implicit def preorder_nat: preorder[Nat] = new preorder[Nat] {
  val `CombinatorialVickreyAuction.less_eq` = (a: Nat, b: Nat) => a <= b
  val `CombinatorialVickreyAuction.less` = (a: Nat, b: Nat) => a < b
}

implicit def order_nat: order[Nat] = new order[Nat] {
  val `CombinatorialVickreyAuction.less_eq` = (a: Nat, b: Nat) => a <= b
  val `CombinatorialVickreyAuction.less` = (a: Nat, b: Nat) => a < b
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

def fst[A, B](x0: (A, B)): A = x0 match {
  case (a, b) => a
}

def div_int(a: BigInt, b: BigInt): BigInt =
  fst[BigInt, BigInt](divmod_int(a, b))

def normalize(p: (BigInt, BigInt)): (BigInt, BigInt) =
  (if (BigInt(0) < snd[BigInt, BigInt](p))
    {
      val a: BigInt = gcd_int(fst[BigInt, BigInt](p), snd[BigInt, BigInt](p));
      (div_int(fst[BigInt, BigInt](p), a), div_int(snd[BigInt, BigInt](p), a))
    }
    else (if (snd[BigInt, BigInt](p) == BigInt(0)) (BigInt(0), BigInt(1))
           else {
                  val a: BigInt =
                    (- (gcd_int(fst[BigInt, BigInt](p),
                                 snd[BigInt, BigInt](p))));
                  (div_int(fst[BigInt, BigInt](p), a),
                    div_int(snd[BigInt, BigInt](p), a))
                }))

def plus_rat(p: rat, q: rat): rat =
  Frct({
         val (a, c): (BigInt, BigInt) = quotient_of(p)
         val (b, d): (BigInt, BigInt) = quotient_of(q);
         normalize((a * d + b * c, c * d))
       })

def zero_rat: rat = Frct((BigInt(0), BigInt(1)))

def list_all[A](p: A => Boolean, x1: List[A]): Boolean = (p, x1) match {
  case (p, Nil) => true
  case (p, x :: xs) => p(x) && list_all[A](p, xs)
}

def less_eq_set[A : equal](a: set[A], b: set[A]): Boolean = (a, b) match {
  case (Coset(Nil), Set(Nil)) => false
  case (a, Coset(ys)) => list_all[A]((y: A) => ! (member[A](y, a)), ys)
  case (Set(xs), b) => list_all[A]((x: A) => member[A](x, b), xs)
}

def equal_seta[A : equal](a: set[A], b: set[A]): Boolean =
  less_eq_set[A](a, b) && less_eq_set[A](b, a)

implicit def equal_set[A : equal]: equal[set[A]] = new equal[set[A]] {
  val `CombinatorialVickreyAuction.equal` = (a: set[A], b: set[A]) =>
    equal_seta[A](a, b)
}

def the_elem[A](x0: set[A]): A = x0 match {
  case Set(List(x)) => x
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

def equal_proda[A : equal, B : equal](x0: (A, B), x1: (A, B)): Boolean =
  (x0, x1) match {
  case ((aa, ba), (a, b)) => eq[A](aa, a) && eq[B](ba, b)
}

def equal_rat(a: rat, b: rat): Boolean =
  equal_proda[BigInt, BigInt](quotient_of(a), quotient_of(b))

def minus_rat(p: rat, q: rat): rat =
  Frct({
         val (a, c): (BigInt, BigInt) = quotient_of(p)
         val (b, d): (BigInt, BigInt) = quotient_of(q);
         normalize((a * d - b * c, c * d))
       })

def minus_set[A : equal](a: set[A], x1: set[A]): set[A] = (a, x1) match {
  case (a, Coset(xs)) => Set[A](filter[A]((x: A) => member[A](x, a), xs))
  case (a, Set(xs)) =>
    fold[A, set[A]]((aa: A) => (b: set[A]) => remove[A](aa, b), xs, a)
}

def gen_length[A](n: Nat, x1: List[A]): Nat = (n, x1) match {
  case (n, x :: xs) => gen_length[A](suc(n), xs)
  case (n, Nil) => n
}

def size_list[A]: (List[A]) => Nat = (a: List[A]) => gen_length[A](Nat(0), a)

def map_filter[A, B](f: A => Option[B], x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) =>
    (f(x) match {
       case None => map_filter[A, B](f, xs)
       case Some(y) => y :: map_filter[A, B](f, xs)
     })
}

def map_project[A, B](f: A => Option[B], x1: set[A]): set[B] = (f, x1) match {
  case (f, Set(xs)) => Set[B](map_filter[A, B](f, xs))
}

def imagea[A : equal, B](r: set[(A, B)], s: set[A]): set[B] =
  map_project[(A, B),
               B]((a: (A, B)) =>
                    {
                      val (x, y): (A, B) = a;
                      (if (member[A](x, s)) Some[B](y) else None)
                    },
                   r)

def range[A, B](r: set[(A, B)]): set[B] =
  image[(A, B), B]((a: (A, B)) => snd[A, B](a), r)

def card[A : equal](x0: set[A]): Nat = x0 match {
  case Set(xs) => size_list[A].apply(remdups[A](xs))
}

implicit def linorder_nat: linorder[Nat] = new linorder[Nat] {
  val `CombinatorialVickreyAuction.less_eq` = (a: Nat, b: Nat) => a <= b
  val `CombinatorialVickreyAuction.less` = (a: Nat, b: Nat) => a < b
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
  val `CombinatorialVickreyAuction.less_eq` = (a: real, b: real) =>
    less_eq_real(a, b)
  val `CombinatorialVickreyAuction.less` = (a: real, b: real) => less_real(a, b)
}

def domain[A, B](r: set[(A, B)]): set[A] =
  image[(A, B), A]((a: (A, B)) => fst[A, B](a), r)

def list_update[A](x0: List[A], i: Nat, y: A): List[A] = (x0, i, y) match {
  case (Nil, i, y) => Nil
  case (x :: xs, i, y) =>
    (if (i == Nat(0)) y :: xs else x :: list_update[A](xs, i - Nat(1), y))
}

def plus_reala(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(plus_rat(x, y))
}

implicit def plus_real: plus[real] = new plus[real] {
  val `CombinatorialVickreyAuction.plus` = (a: real, b: real) =>
    plus_reala(a, b)
}

def zero_reala: real = Ratreal(zero_rat)

implicit def zero_real: zero[real] = new zero[real] {
  val `CombinatorialVickreyAuction.zero` = zero_reala
}

def minus_funa[A, B : minus](a: A => B, b: A => B, x: A): B =
  minus[B](a(x), b(x))

implicit def minus_fun[A, B : minus]: minus[A => B] = new minus[A => B] {
  val `CombinatorialVickreyAuction.minus` = (a: A => B, b: A => B, c: A) =>
    minus_funa[A, B](a, b, c)
}

def equal_reala(x0: real, x1: real): Boolean = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => equal_rat(x, y)
}

implicit def equal_real: equal[real] = new equal[real] {
  val `CombinatorialVickreyAuction.equal` = (a: real, b: real) =>
    equal_reala(a, b)
}

def minus_reala(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(minus_rat(x, y))
}

implicit def minus_real: minus[real] = new minus[real] {
  val `CombinatorialVickreyAuction.minus` = (a: real, b: real) =>
    minus_reala(a, b)
}

implicit def preorder_real: preorder[real] = new preorder[real] {
  val `CombinatorialVickreyAuction.less_eq` = (a: real, b: real) =>
    less_eq_real(a, b)
  val `CombinatorialVickreyAuction.less` = (a: real, b: real) => less_real(a, b)
}

implicit def order_real: order[real] = new order[real] {
  val `CombinatorialVickreyAuction.less_eq` = (a: real, b: real) =>
    less_eq_real(a, b)
  val `CombinatorialVickreyAuction.less` = (a: real, b: real) => less_real(a, b)
}

trait ab_semigroup_add[A] extends semigroup_add[A] {
}

trait comm_monoid_add[A] extends ab_semigroup_add[A] with monoid_add[A] {
}

def setsum[A : equal, B : comm_monoid_add](f: A => B, x1: set[A]): B = (f, x1)
  match {
  case (f, Set(xs)) => listsum[B](map[A, B](f, remdups[A](xs)))
}

implicit def linorder_real: linorder[real] = new linorder[real] {
  val `CombinatorialVickreyAuction.less_eq` = (a: real, b: real) =>
    less_eq_real(a, b)
  val `CombinatorialVickreyAuction.less` = (a: real, b: real) => less_real(a, b)
}

implicit def equal_prod[A : equal, B : equal]: equal[(A, B)] = new equal[(A, B)]
  {
  val `CombinatorialVickreyAuction.equal` = (a: (A, B), b: (A, B)) =>
    equal_proda[A, B](a, b)
}

implicit def semigroup_add_real: semigroup_add[real] = new semigroup_add[real] {
  val `CombinatorialVickreyAuction.plus` = (a: real, b: real) =>
    plus_reala(a, b)
}

implicit def monoid_add_real: monoid_add[real] = new monoid_add[real] {
  val `CombinatorialVickreyAuction.zero` = zero_reala
  val `CombinatorialVickreyAuction.plus` = (a: real, b: real) =>
    plus_reala(a, b)
}

def sorted_list_of_set[A : equal : linorder](x0: set[A]): List[A] = x0 match {
  case Set(xs) => sort_key[A, A]((x: A) => x, remdups[A](xs))
}

def arg_max_comp_list[A, B : equal : linorder](x0: List[A], f: A => B):
      List[A] =
  (x0, f) match {
  case (Nil, f) => Nil
  case (List(x), f) => List(x)
  case (x :: v :: va, f) =>
    {
      val arg_max_xs: List[A] = arg_max_comp_list[A, B](v :: va, f)
      val prev_max: B = f(hd[A](arg_max_xs));
      (if (less[B](prev_max, f(x))) List(x)
        else (if (eq[B](f(x), prev_max)) x :: arg_max_xs else arg_max_xs))
    }
}

def maximum_comp_list[A, B : linorder](x0: List[A], b: A => B): B = (x0, b)
  match {
  case (Nil, b) => sys.error("undefined")
  case (List(x), b) => b(x)
  case (x :: v :: va, b) =>
    {
      val max_xs: B = maximum_comp_list[A, B](v :: va, b);
      (if (less[B](max_xs, b(x))) b(x) else max_xs)
    }
}

def inverse[A, B](r: set[(A, B)]): set[(B, A)] =
  image[(A, B), (B, A)]((a: (A, B)) => {
 val (x, y): (A, B) = a;
 (y, x)
                                       },
                         r)

implicit def ab_semigroup_add_real: ab_semigroup_add[real] = new
  ab_semigroup_add[real] {
  val `CombinatorialVickreyAuction.plus` = (a: real, b: real) =>
    plus_reala(a, b)
}

implicit def comm_monoid_add_real: comm_monoid_add[real] = new
  comm_monoid_add[real] {
  val `CombinatorialVickreyAuction.zero` = zero_reala
  val `CombinatorialVickreyAuction.plus` = (a: real, b: real) =>
    plus_reala(a, b)
}

def eval_rel[A : equal, B](r: set[(A, B)], a: A): B =
  the_elem[B](imagea[A, B](r, insert[A](a, bot_set[A])))

def injective_functions_list[A : equal,
                              B : equal : linorder](x0: List[A], ys: List[B]):
      List[set[(A, B)]] =
  (x0, ys) match {
  case (Nil, ys) => List(bot_set[(A, B)])
  case (x :: xs, ys) =>
    maps[set[(A, B)],
          set[(A, B)]]((f: set[(A, B)]) =>
                         map[B, set[(A, B)]]((free_in_range: B) =>
       sup_set[(A, B)](f, insert[(A, B)]((x, free_in_range), bot_set[(A, B)])),
      sorted_list_of_set[B](minus_set[B](Set[B](ys), range[A, B](f)))),
                        injective_functions_list[A, B](xs, ys))
}

def all_partitions_fun_list[A : equal](x0: List[A]): List[List[set[A]]] = x0
  match {
  case Nil => Nil
  case List(x) => List(List(insert[A](x, bot_set[A])))
  case x :: v :: va =>
    {
      val xs_partitions: List[List[set[A]]] =
        all_partitions_fun_list[A](v :: va);
      maps[List[set[A]],
            List[set[A]]]((p: List[set[A]]) =>
                            map[Nat, List[set[A]]]((i: Nat) =>
             list_update[set[A]](p, i,
                                  sup_set[A](insert[A](x, bot_set[A]),
      nth[set[A]](p, i))),
            map[BigInt,
                 Nat]((a: BigInt) => Nat(a),
                       upto(BigInt(0),
                             size_list[set[A]].apply(p).as_BigInt -
                               BigInt(1)))),
                           xs_partitions) ++
        map[List[set[A]],
             List[set[A]]]((a: List[set[A]]) => insert[A](x, bot_set[A]) :: a,
                            xs_partitions)
    }
}

def possible_allocations_comp(g: set[Nat], n: set[Nat]):
      List[set[(set[Nat], Nat)]] =
  maps[List[set[Nat]],
        set[(set[Nat],
              Nat)]]((y: List[set[Nat]]) =>
                       map[set[(set[Nat], Nat)],
                            set[(set[Nat],
                                  Nat)]]((potential_buyer: set[(set[Nat], Nat)])
   => potential_buyer,
  injective_functions_list[set[Nat], Nat](y, sorted_list_of_set[Nat](n))),
                      all_partitions_fun_list[Nat](sorted_list_of_set[Nat](g)))

def revenue_rel(b: Nat => (set[Nat]) => real, buyer: set[(set[Nat], Nat)]):
      real =
  setsum[set[Nat],
          real]((y: set[Nat]) => (b(eval_rel[set[Nat], Nat](buyer, y)))(y),
                 domain[set[Nat], Nat](buyer))

def max_revenue_comp(g: set[Nat], n: set[Nat], b: Nat => (set[Nat]) => real):
      real =
  maximum_comp_list[set[(set[Nat], Nat)],
                     real](possible_allocations_comp(g, n),
                            (a: set[(set[Nat], Nat)]) => revenue_rel(b, a))

def alpha_comp(g: set[Nat], na: set[Nat], b: Nat => (set[Nat]) => real, n: Nat):
      real =
  max_revenue_comp(g, remove[Nat](n, na), b)

def eval_rel_or[A : equal, B : equal](r: set[(A, B)], a: A, z: B): B =
  {
    val im: set[B] = imagea[A, B](r, insert[A](a, bot_set[A]));
    (if (card[B](im) == Nat(1)) the_elem[B](im) else z)
  }

def winning_allocations_comp_CL(g: set[Nat], n: set[Nat],
                                 b: Nat => (set[Nat]) => real):
      List[set[(set[Nat], Nat)]] =
  arg_max_comp_list[set[(set[Nat], Nat)],
                     real](possible_allocations_comp(g, n),
                            (a: set[(set[Nat], Nat)]) => revenue_rel(b, a))

def remaining_value_comp(g: set[Nat], na: set[Nat],
                          t: (List[set[(set[Nat], Nat)]]) =>
                               set[(set[Nat], Nat)],
                          b: Nat => (set[Nat]) => real, n: Nat):
      real =
  setsum[Nat, real]((m: Nat) =>
                      (b(m))(eval_rel_or[Nat,
  set[Nat]](inverse[set[Nat], Nat](t(winning_allocations_comp_CL(g, na, b))), m,
             bot_set[Nat])),
                     remove[Nat](n, na))

def payments_comp(g: set[Nat], n: set[Nat],
                   t: (List[set[(set[Nat], Nat)]]) => set[(set[Nat], Nat)]):
      (Nat => (set[Nat]) => real) => Nat => real =
  (a: Nat => (set[Nat]) => real) =>
    minus_funa[Nat => (set[Nat]) => real,
                Nat =>
                  real]((aa: Nat => (set[Nat]) => real) =>
                          (b: Nat) => alpha_comp(g, n, aa, b),
                         (aa: Nat => (set[Nat]) => real) =>
                           (b: Nat) => remaining_value_comp(g, n, t, aa, b),
                         a)

} /* object CombinatorialVickreyAuction */
