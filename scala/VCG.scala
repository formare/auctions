object VCG {

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

def equal_num(x0: num, x1: num): Boolean = (x0, x1) match {
  case (Bit0(numa), Bit1(num)) => false
  case (Bit1(numa), Bit0(num)) => false
  case (One(), Bit1(num)) => false
  case (Bit1(num), One()) => false
  case (One(), Bit0(num)) => false
  case (Bit0(num), One()) => false
  case (Bit1(numa), Bit1(num)) => equal_num(numa, num)
  case (Bit0(numa), Bit0(num)) => equal_num(numa, num)
  case (One(), One()) => true
}

abstract sealed class int
final case class zero_int() extends int
final case class Pos(a: num) extends int
final case class Neg(a: num) extends int

def equal_inta(x0: int, x1: int): Boolean = (x0, x1) match {
  case (Neg(k), Neg(l)) => equal_num(k, l)
  case (Neg(k), Pos(l)) => false
  case (Neg(k), zero_int()) => false
  case (Pos(k), Neg(l)) => false
  case (Pos(k), Pos(l)) => equal_num(k, l)
  case (Pos(k), zero_int()) => false
  case (zero_int(), Neg(l)) => false
  case (zero_int(), Pos(l)) => false
  case (zero_int(), zero_int()) => true
}

trait equal[A] {
  val `VCG.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`VCG.equal`(a, b)

implicit def equal_int: equal[int] = new equal[int] {
  val `VCG.equal` = (a: int, b: int) => equal_inta(a, b)
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

def less_eq_num(x0: num, n: num): Boolean = (x0, n) match {
  case (Bit1(m), Bit0(n)) => less_num(m, n)
  case (Bit1(m), Bit1(n)) => less_eq_num(m, n)
  case (Bit0(m), Bit1(n)) => less_eq_num(m, n)
  case (Bit0(m), Bit0(n)) => less_eq_num(m, n)
  case (Bit1(m), One()) => false
  case (Bit0(m), One()) => false
  case (One(), n) => true
}

def less_eq_int(x0: int, x1: int): Boolean = (x0, x1) match {
  case (Neg(k), Neg(l)) => less_eq_num(l, k)
  case (Neg(k), Pos(l)) => true
  case (Neg(k), zero_int()) => true
  case (Pos(k), Neg(l)) => false
  case (Pos(k), Pos(l)) => less_eq_num(k, l)
  case (Pos(k), zero_int()) => false
  case (zero_int(), Neg(l)) => false
  case (zero_int(), Pos(l)) => true
  case (zero_int(), zero_int()) => true
}

trait ord[A] {
  val `VCG.less_eq`: (A, A) => Boolean
  val `VCG.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`VCG.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`VCG.less`(a, b)

def less_int(x0: int, x1: int): Boolean = (x0, x1) match {
  case (Neg(k), Neg(l)) => less_num(l, k)
  case (Neg(k), Pos(l)) => true
  case (Neg(k), zero_int()) => true
  case (Pos(k), Neg(l)) => false
  case (Pos(k), Pos(l)) => less_num(k, l)
  case (Pos(k), zero_int()) => false
  case (zero_int(), Neg(l)) => false
  case (zero_int(), Pos(l)) => true
  case (zero_int(), zero_int()) => false
}

implicit def ord_int: ord[int] = new ord[int] {
  val `VCG.less_eq` = (a: int, b: int) => less_eq_int(a, b)
  val `VCG.less` = (a: int, b: int) => less_int(a, b)
}

trait preorder[A] extends ord[A] {
}

trait order[A] extends preorder[A] {
}

implicit def preorder_int: preorder[int] = new preorder[int] {
  val `VCG.less_eq` = (a: int, b: int) => less_eq_int(a, b)
  val `VCG.less` = (a: int, b: int) => less_int(a, b)
}

implicit def order_int: order[int] = new order[int] {
  val `VCG.less_eq` = (a: int, b: int) => less_eq_int(a, b)
  val `VCG.less` = (a: int, b: int) => less_int(a, b)
}

trait linorder[A] extends order[A] {
}

implicit def linorder_int: linorder[int] = new linorder[int] {
  val `VCG.less_eq` = (a: int, b: int) => less_eq_int(a, b)
  val `VCG.less` = (a: int, b: int) => less_int(a, b)
}

abstract sealed class nat
final case class Nat(a: BigInt) extends nat

def integer_of_nat(x0: nat): BigInt = x0 match {
  case Nat(x) => x
}

def equal_nata(m: nat, n: nat): Boolean = integer_of_nat(m) == integer_of_nat(n)

implicit def equal_nat: equal[nat] = new equal[nat] {
  val `VCG.equal` = (a: nat, b: nat) => equal_nata(a, b)
}

def plus_nata(m: nat, n: nat): nat = Nat(integer_of_nat(m) + integer_of_nat(n))

trait plus[A] {
  val `VCG.plus`: (A, A) => A
}
def plus[A](a: A, b: A)(implicit A: plus[A]): A = A.`VCG.plus`(a, b)

implicit def plus_nat: plus[nat] = new plus[nat] {
  val `VCG.plus` = (a: nat, b: nat) => plus_nata(a, b)
}

def zero_nata: nat = Nat(BigInt(0))

trait zero[A] {
  val `VCG.zero`: A
}
def zero[A](implicit A: zero[A]): A = A.`VCG.zero`

implicit def zero_nat: zero[nat] = new zero[nat] {
  val `VCG.zero` = zero_nata
}

def less_eq_nat(m: nat, n: nat): Boolean =
  integer_of_nat(m) <= integer_of_nat(n)

def less_nat(m: nat, n: nat): Boolean = integer_of_nat(m) < integer_of_nat(n)

implicit def ord_nat: ord[nat] = new ord[nat] {
  val `VCG.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `VCG.less` = (a: nat, b: nat) => less_nat(a, b)
}

implicit def preorder_nat: preorder[nat] = new preorder[nat] {
  val `VCG.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `VCG.less` = (a: nat, b: nat) => less_nat(a, b)
}

implicit def order_nat: order[nat] = new order[nat] {
  val `VCG.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `VCG.less` = (a: nat, b: nat) => less_nat(a, b)
}

trait semigroup_add[A] extends plus[A] {
}

trait monoid_add[A] extends semigroup_add[A] with zero[A] {
}

implicit def semigroup_add_nat: semigroup_add[nat] = new semigroup_add[nat] {
  val `VCG.plus` = (a: nat, b: nat) => plus_nata(a, b)
}

implicit def monoid_add_nat: monoid_add[nat] = new monoid_add[nat] {
  val `VCG.zero` = zero_nata
  val `VCG.plus` = (a: nat, b: nat) => plus_nata(a, b)
}

implicit def linorder_nat: linorder[nat] = new linorder[nat] {
  val `VCG.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `VCG.less` = (a: nat, b: nat) => less_nat(a, b)
}

trait ab_semigroup_add[A] extends semigroup_add[A] {
}

trait comm_monoid_add[A] extends ab_semigroup_add[A] with monoid_add[A] {
}

implicit def ab_semigroup_add_nat: ab_semigroup_add[nat] = new
  ab_semigroup_add[nat] {
  val `VCG.plus` = (a: nat, b: nat) => plus_nata(a, b)
}

implicit def comm_monoid_add_nat: comm_monoid_add[nat] = new
  comm_monoid_add[nat] {
  val `VCG.zero` = zero_nata
  val `VCG.plus` = (a: nat, b: nat) => plus_nata(a, b)
}

def pred_list[A](p: A => Boolean, x1: List[A]): Boolean = (p, x1) match {
  case (p, Nil) => true
  case (p, x :: xs) => p(x) && pred_list[A](p, xs)
}

abstract sealed class set[A]
final case class seta[A](a: List[A]) extends set[A]
final case class coset[A](a: List[A]) extends set[A]

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

def membera[A : equal](x0: List[A], y: A): Boolean = (x0, y) match {
  case (Nil, y) => false
  case (x :: xs, y) => eq[A](x, y) || membera[A](xs, y)
}

def member[A : equal](x: A, xa1: set[A]): Boolean = (x, xa1) match {
  case (x, coset(xs)) => ! (membera[A](xs, x))
  case (x, seta(xs)) => membera[A](xs, x)
}

def less_eq_set[A : equal](a: set[A], b: set[A]): Boolean = (a, b) match {
  case (coset(Nil), seta(Nil)) => false
  case (a, coset(ys)) => pred_list[A]((y: A) => ! (member[A](y, a)), ys)
  case (seta(xs), b) => pred_list[A]((x: A) => member[A](x, b), xs)
}

def equal_seta[A : equal](a: set[A], b: set[A]): Boolean =
  less_eq_set[A](a, b) && less_eq_set[A](b, a)

implicit def equal_set[A : equal]: equal[set[A]] = new equal[set[A]] {
  val `VCG.equal` = (a: set[A], b: set[A]) => equal_seta[A](a, b)
}

def equal_proda[A : equal, B : equal](x0: (A, B), x1: (A, B)): Boolean =
  (x0, x1) match {
  case ((x1, x2), (y1, y2)) => eq[A](x1, y1) && eq[B](x2, y2)
}

implicit def equal_prod[A : equal, B : equal]: equal[(A, B)] = new equal[(A, B)]
  {
  val `VCG.equal` = (a: (A, B), b: (A, B)) => equal_proda[A, B](a, b)
}

implicit def ord_integer: ord[BigInt] = new ord[BigInt] {
  val `VCG.less_eq` = (a: BigInt, b: BigInt) => a <= b
  val `VCG.less` = (a: BigInt, b: BigInt) => a < b
}

trait minus[A] {
  val `VCG.minus`: (A, A) => A
}
def minus[A](a: A, b: A)(implicit A: minus[A]): A = A.`VCG.minus`(a, b)

def id[A]: A => A = (x: A) => x

def one_nat: nat = Nat(BigInt(1))

def Suc(n: nat): nat = plus_nata(n, one_nat)

def filtera[A](p: A => Boolean, x1: List[A]): List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x :: xs) => (if (p(x)) x :: filtera[A](p, xs) else filtera[A](p, xs))
}

def removeAll[A : equal](x: A, xa1: List[A]): List[A] = (x, xa1) match {
  case (x, Nil) => Nil
  case (x, y :: xs) =>
    (if (eq[A](x, y)) removeAll[A](x, xs) else y :: removeAll[A](x, xs))
}

def inserta[A : equal](x: A, xs: List[A]): List[A] =
  (if (membera[A](xs, x)) xs else x :: xs)

def insert[A : equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, coset(xs)) => coset[A](removeAll[A](x, xs))
  case (x, seta(xs)) => seta[A](inserta[A](x, xs))
}

def fold[A, B](f: A => B => B, x1: List[A], s: B): B = (f, x1, s) match {
  case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
  case (f, Nil, s) => s
}

def sup_set[A : equal](x0: set[A], a: set[A]): set[A] = (x0, a) match {
  case (coset(xs), a) => coset[A](filtera[A]((x: A) => ! (member[A](x, a)), xs))
  case (seta(xs), a) =>
    fold[A, set[A]]((aa: A) => (b: set[A]) => insert[A](aa, b), xs, a)
}

def bot_set[A]: set[A] = seta[A](Nil)

def map[A, B](fi: A => B, x1: List[A]): List[B] = (fi, x1) match {
  case (fi, Nil) => Nil
  case (fi, x21a :: x22) => fi(x21a) :: map[A, B](fi, x22)
}

def image[A, B](f: A => B, x1: set[A]): set[B] = (f, x1) match {
  case (f, seta(xs)) => seta[B](map[A, B](f, xs))
}

def Pow[A : equal](x0: set[A]): set[set[A]] = x0 match {
  case seta(x :: xs) =>
    {
      val a: set[set[A]] = Pow[A](seta[A](xs));
      sup_set[set[A]](a, image[set[A],
                                set[A]]((aa: set[A]) => insert[A](x, aa), a))
    }
  case seta(Nil) => insert[set[A]](bot_set[A], bot_set[set[A]])
}

def comp[A, B, C](f: A => B, g: C => A): C => B = (x: C) => f(g(x))

def max[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) b else a)

def minus_nat(m: nat, n: nat): nat =
  Nat(max[BigInt](BigInt(0), integer_of_nat(m) - integer_of_nat(n)))

def nth[A](x0: List[A], n: nat): A = (x0, n) match {
  case (x :: xs, n) =>
    (if (equal_nata(n, zero_nata)) x else nth[A](xs, minus_nat(n, one_nat)))
}

def upt(i: nat, j: nat): List[nat] =
  (if (less_nat(i, j)) i :: upt(Suc(i), j) else Nil)

def maps[A, B](f: A => List[B], x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) ++ maps[A, B](f, xs)
}

def foldr[A, B](f: A => B => B, x1: List[A]): B => B = (f, x1) match {
  case (f, Nil) => id[B]
  case (f, x :: xs) => comp[B, B, B](f(x), foldr[A, B](f, xs))
}

def funpow[A](n: nat, f: A => A): A => A =
  (if (equal_nata(n, zero_nata)) id[A]
    else comp[A, A, A](f, funpow[A](minus_nat(n, one_nat), f)))

def filter[A](p: A => Boolean, x1: set[A]): set[A] = (p, x1) match {
  case (p, seta(xs)) => seta[A](filtera[A](p, xs))
}

def remove[A : equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, coset(xs)) => coset[A](inserta[A](x, xs))
  case (x, seta(xs)) => seta[A](removeAll[A](x, xs))
}

def rotate1[A](x0: List[A]): List[A] = x0 match {
  case Nil => Nil
  case x :: xs => xs ++ List(x)
}

def rotate[A](n: nat): (List[A]) => List[A] =
  funpow[List[A]](n, (a: List[A]) => rotate1[A](a))

def hd[A](x0: List[A]): A = x0 match {
  case x21 :: x22 => x21
}

def remdups[A : equal](x0: List[A]): List[A] = x0 match {
  case Nil => Nil
  case x :: xs =>
    (if (membera[A](xs, x)) remdups[A](xs) else x :: remdups[A](xs))
}

def remove1[A : equal](x: A, xa1: List[A]): List[A] = (x, xa1) match {
  case (x, Nil) => Nil
  case (x, y :: xs) => (if (eq[A](x, y)) xs else y :: remove1[A](x, xs))
}

def the_elem[A](x0: set[A]): A = x0 match {
  case seta(List(x)) => x
}

def Max[A : linorder](x0: set[A]): A = x0 match {
  case seta(x :: xs) => fold[A, A]((a: A) => (b: A) => max[A](a, b), xs, x)
}

def argmax[A, B : equal : linorder](f: A => B, a: set[A]): set[A] =
  filter[A]((x: A) => eq[B](f(x), Max[B](image[A, B](f, a))), a)

def map_filter[A, B](f: A => Option[B], x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) =>
    (f(x) match {
       case None => map_filter[A, B](f, xs)
       case Some(y) => y :: map_filter[A, B](f, xs)
     })
}

def map_project[A, B](f: A => Option[B], x1: set[A]): set[B] = (f, x1) match {
  case (f, seta(xs)) => seta[B](map_filter[A, B](f, xs))
}

def Image[A : equal, B](r: set[(A, B)], s: set[A]): set[B] =
  map_project[(A, B),
               B]((a: (A, B)) =>
                    {
                      val (x, y): (A, B) = a;
                      (if (member[A](x, s)) Some[B](y) else None)
                    },
                   r)

def snd[A, B](x0: (A, B)): B = x0 match {
  case (x1, x2) => x2
}

def Range[A, B](r: set[(A, B)]): set[B] =
  image[(A, B), B]((a: (A, B)) => snd[A, B](a), r)

def gen_length[A](n: nat, x1: List[A]): nat = (n, x1) match {
  case (n, x :: xs) => gen_length[A](Suc(n), xs)
  case (n, Nil) => n
}

def size_list[A]: (List[A]) => nat = (a: List[A]) => gen_length[A](zero_nata, a)

def sgn_integer(k: BigInt): BigInt =
  (if (k == BigInt(0)) BigInt(0)
    else (if (k < BigInt(0)) BigInt(- 1) else BigInt(1)))

def abs_integer(k: BigInt): BigInt = (if (k < BigInt(0)) (- k) else k)

def apsnd[A, B, C](f: A => B, x1: (C, A)): (C, B) = (f, x1) match {
  case (f, (x, y)) => (x, f(y))
}

def divmod_integer(k: BigInt, l: BigInt): (BigInt, BigInt) =
  (if (k == BigInt(0)) (BigInt(0), BigInt(0))
    else (if (l == BigInt(0)) (BigInt(0), k)
           else (comp[BigInt, ((BigInt, BigInt)) => (BigInt, BigInt),
                       BigInt](comp[BigInt => BigInt,
                                     ((BigInt, BigInt)) => (BigInt, BigInt),
                                     BigInt]((a: BigInt => BigInt) =>
       (b: (BigInt, BigInt)) => apsnd[BigInt, BigInt, BigInt](a, b),
      (a: BigInt) => (b: BigInt) => a * b),
                                (a: BigInt) =>
                                  sgn_integer(a))).apply(l).apply((if (sgn_integer(k) ==
                                 sgn_integer(l))
                            ((k: BigInt) => (l: BigInt) => if (l == 0)
                              (BigInt(0), k) else
                              (k.abs /% l.abs)).apply(k).apply(l)
                            else {
                                   val (r, s): (BigInt, BigInt) =
                                     ((k: BigInt) => (l: BigInt) => if (l == 0)
                                       (BigInt(0), k) else
                                       (k.abs /% l.abs)).apply(k).apply(l);
                                   (if (s == BigInt(0)) ((- r), BigInt(0))
                                     else ((- r) - BigInt(1),
    abs_integer(l) - s))
                                 }))))

def mod_integer(k: BigInt, l: BigInt): BigInt =
  snd[BigInt, BigInt](divmod_integer(k, l))

def mod_nat(m: nat, n: nat): nat =
  Nat(mod_integer(integer_of_nat(m), integer_of_nat(n)))

def fst[A, B](x0: (A, B)): A = x0 match {
  case (x1, x2) => x1
}

def div_integer(k: BigInt, l: BigInt): BigInt =
  fst[BigInt, BigInt](divmod_integer(k, l))

def div_nat(m: nat, n: nat): nat =
  Nat(div_integer(integer_of_nat(m), integer_of_nat(n)))

def perm2[A](x0: List[A]): nat => List[A] = x0 match {
  case Nil => (_: nat) => Nil
  case x :: l =>
    (n: nat) =>
      (rotate[A](minus_nat(size_list[A].apply(x ::
        (rotate[A](mod_nat(n, plus_nata(one_nat,
 size_list[A].apply(l))))).apply((perm2[A](l)).apply(div_nat(n,
                      plus_nata(one_nat, size_list[A].apply(l)))))),
                            mod_nat(mod_nat(n,
     plus_nata(one_nat, size_list[A].apply(l))),
                                     size_list[A].apply(x ::
                  (rotate[A](mod_nat(n, plus_nata(one_nat,
           size_list[A].apply(l))))).apply((perm2[A](l)).apply(div_nat(n,
                                plus_nata(one_nat,
   size_list[A].apply(l)))))))))).apply(x ::
  (rotate[A](mod_nat(n, plus_nata(one_nat,
                                   size_list[A].apply(l))))).apply((perm2[A](l)).apply(div_nat(n,
                plus_nata(one_nat, size_list[A].apply(l))))))
}

def Domain[A, B](r: set[(A, B)]): set[A] =
  image[(A, B), A]((a: (A, B)) => fst[A, B](a), r)

def converse[A, B](r: set[(A, B)]): set[(B, A)] =
  image[(A, B), (B, A)]((a: (A, B)) => {
 val (x, y): (A, B) = a;
 (y, x)
                                       },
                         r)

def finestpart[A : equal](x: set[A]): set[set[A]] =
  image[A, set[A]]((xa: A) => insert[A](xa, bot_set[A]), x)

def product[A, B](x0: set[A], x1: set[B]): set[(A, B)] = (x0, x1) match {
  case (seta(xs), seta(ys)) =>
    seta[(A, B)](maps[A, (A, B)]((x: A) => map[B, (A, B)]((a: B) => (x, a), ys),
                                  xs))
}

def filterpositions2[A](p: A => Boolean, l: List[A]): List[nat] =
  maps[nat, nat]((n: nat) => (if (p(nth[A](l, n))) List(n) else Nil),
                  upt(zero_nata, size_list[A].apply(l)))

def minus_set[A : equal](a: set[A], x1: set[A]): set[A] = (a, x1) match {
  case (a, coset(xs)) => seta[A](filtera[A]((x: A) => member[A](x, a), xs))
  case (a, seta(xs)) =>
    fold[A, set[A]]((aa: A) => (b: set[A]) => remove[A](aa, b), xs, a)
}

def Outside[A : equal, B : equal](r: set[(A, B)], x: set[A]): set[(A, B)] =
  minus_set[(A, B)](r, product[A, B](x, Range[A, B](r)))

def paste[A : equal, B : equal](p: set[(A, B)], q: set[(A, B)]): set[(A, B)] =
  sup_set[(A, B)](Outside[A, B](p, Domain[A, B](q)), q)

def listsum[A : monoid_add](xs: List[A]): A =
  (foldr[A, A]((a: A) => (b: A) => plus[A](a, b), xs)).apply(zero[A])

def setsum[A : equal, B : comm_monoid_add](f: A => B, x1: set[A]): B = (f, x1)
  match {
  case (f, seta(xs)) => listsum[B](map[A, B](f, remdups[A](xs)))
}

def Sup_set[A : equal](x0: set[set[A]]): set[A] = x0 match {
  case seta(xs) =>
    fold[set[A],
          set[A]]((a: set[A]) => (b: set[A]) => sup_set[A](a, b), xs,
                   bot_set[A])
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

def sorted_list_of_set[A : equal : linorder](x0: set[A]): List[A] = x0 match {
  case seta(xs) => sort_key[A, A]((x: A) => x, remdups[A](xs))
}

def injections_alg[A : equal, B : equal : linorder](x0: List[A], y: set[B]):
      List[set[(A, B)]]
  =
  (x0, y) match {
  case (Nil, y) => List(bot_set[(A, B)])
  case (x :: xs, y) =>
    maps[set[(A, B)],
          set[(A, B)]]((r: set[(A, B)]) =>
                         map[B, set[(A, B)]]((ya: B) =>
       paste[A, B](r, insert[(A, B)]((x, ya), bot_set[(A, B)])),
      sorted_list_of_set[B](minus_set[B](y, Range[A, B](r)))),
                        injections_alg[A, B](xs, y))
}

def insert_into_member_list[A : equal](new_el: A, sets: List[set[A]],
s: set[A]):
      List[set[A]]
  =
  sup_set[A](s, insert[A](new_el, bot_set[A])) :: remove1[set[A]](s, sets)

def coarser_partitions_with_list[A : equal](new_el: A, p: List[set[A]]):
      List[List[set[A]]]
  =
  (insert[A](new_el, bot_set[A]) :: p) ::
    map[set[A],
         List[set[A]]]((a: set[A]) => insert_into_member_list[A](new_el, p, a),
                        p)

def all_coarser_partitions_with_list[A : equal](elem: A,
         ps: List[List[set[A]]]):
      List[List[set[A]]]
  =
  maps[List[set[A]],
        List[set[A]]]((a: List[set[A]]) =>
                        coarser_partitions_with_list[A](elem, a),
                       ps)

def all_partitions_list[A : equal](x0: List[A]): List[List[set[A]]] = x0 match {
  case Nil => List(Nil)
  case e :: x =>
    all_coarser_partitions_with_list[A](e, all_partitions_list[A](x))
}

def eval_rel[A : equal, B](r: set[(A, B)], a: A): B =
  the_elem[B](Image[A, B](r, insert[A](a, bot_set[A])))

def vcga[A : equal,
          B : comm_monoid_add : equal : linorder](n: set[int], g: List[A],
           b: ((int, set[A])) => B, r: nat):
      set[(int, set[A])]
  =
  Outside[int, set[A]](the_elem[set[(int, set[A])]](argmax[set[(int, set[A])],
                    nat]((a: set[(int, set[A])]) =>
                           setsum[(int, set[A]),
                                   nat]((x: (int, set[A])) =>
  (if (member[(int, set[A])](x, Domain[(int, set[A]),
nat](image[(int, set[A]),
            ((int, set[A]),
              nat)]((pair: (int, set[A])) =>
                      (pair,
                        setsum[set[A],
                                nat]((ga: set[A]) =>
                                       (if (member[(int,
             set[A])]((fst[int, set[A]](pair), ga),
                       Domain[(int, set[A]),
                               nat](paste[(int, set[A]),
   nat](product[(int, set[A]),
                 nat](product[int, set[A]](sup_set[int](n,
                 insert[int](zero_int(), bot_set[int])),
    finestpart[A](seta[A](g))),
                       insert[nat](zero_nata, bot_set[nat])),
         product[(int, set[A]),
                  nat](Sup_set[(int, set[A])](image[(int, set[A]),
             set[(int, set[A])]]((paira: (int, set[A])) =>
                                   product[int,
    set[A]](insert[int](fst[int, set[A]](paira), bot_set[int]),
             finestpart[A](snd[int, set[A]](paira))),
                                  hd[set[(int,
   set[A])]]((perm2[set[(int, set[A])]](map[nat,
     set[(int, set[A])]]((aa: nat) =>
                           nth[set[(int, set[A])]](map[set[(set[A], int)],
                set[(int, set[A])]]((ab: set[(set[A], int)]) =>
                                      converse[set[A], int](ab),
                                     maps[List[set[A]],
   set[(set[A],
         int)]]((l: List[set[A]]) =>
                  injections_alg[set[A],
                                  int](l,
sup_set[int](n, insert[int](zero_int(), bot_set[int]))),
                 all_partitions_list[A](g))),
            aa),
                          filterpositions2[set[(int,
         set[A])]]((xa: set[(int, set[A])]) =>
                     member[set[(int, set[A])]](xa,
         (comp[(set[(int, set[A])]) => B,
                (set[set[(int, set[A])]]) => set[set[(int, set[A])]],
                ((int, set[A])) =>
                  B]((aa: (set[(int, set[A])]) => B) =>
                       (ba: set[set[(int, set[A])]]) =>
                         argmax[set[(int, set[A])], B](aa, ba),
                      (aa: ((int, set[A])) => B) =>
                        (ba: set[(int, set[A])]) =>
                          setsum[(int, set[A]),
                                  B](aa, ba))).apply(b).apply(seta[set[(int,
                                 set[A])]](map[set[(set[A], int)],
        set[(int, set[A])]]((aa: set[(set[A], int)]) =>
                              converse[set[A], int](aa),
                             maps[List[set[A]],
                                   set[(set[A],
 int)]]((l: List[set[A]]) =>
          injections_alg[set[A],
                          int](l, sup_set[int](n,
        insert[int](zero_int(), bot_set[int]))),
         all_partitions_list[A](g)))))),
                    map[set[(set[A], int)],
                         set[(int, set[A])]]((aa: set[(set[A], int)]) =>
       converse[set[A], int](aa),
      maps[List[set[A]],
            set[(set[A],
                  int)]]((l: List[set[A]]) =>
                           injections_alg[set[A],
   int](l, sup_set[int](n, insert[int](zero_int(), bot_set[int]))),
                          all_partitions_list[A](g))))))).apply(r)))),
                        insert[nat](one_nat, bot_set[nat]))))))
 eval_rel[(int, set[A]),
           nat](paste[(int, set[A]),
                       nat](product[(int, set[A]),
                                     nat](product[int,
           set[A]](sup_set[int](n, insert[int](zero_int(), bot_set[int])),
                    finestpart[A](seta[A](g))),
   insert[nat](zero_nata, bot_set[nat])),
                             product[(int, set[A]),
                                      nat](Sup_set[(int,
             set[A])](image[(int, set[A]),
                             set[(int, set[A])]]((paira: (int, set[A])) =>
           product[int, set[A]](insert[int](fst[int, set[A]](paira),
     bot_set[int]),
                                 finestpart[A](snd[int, set[A]](paira))),
          hd[set[(int, set[A])]]((perm2[set[(int,
      set[A])]](map[nat, set[(int, set[A])]]((aa: nat) =>
       nth[set[(int, set[A])]](map[set[(set[A], int)],
                                    set[(int,
  set[A])]]((ab: set[(set[A], int)]) => converse[set[A], int](ab),
             maps[List[set[A]],
                   set[(set[A],
                         int)]]((l: List[set[A]]) =>
                                  injections_alg[set[A],
          int](l, sup_set[int](n, insert[int](zero_int(), bot_set[int]))),
                                 all_partitions_list[A](g))),
                                aa),
      filterpositions2[set[(int, set[A])]]((xa: set[(int, set[A])]) =>
     member[set[(int, set[A])]](xa, (comp[(set[(int, set[A])]) => B,
   (set[set[(int, set[A])]]) => set[set[(int, set[A])]],
   ((int, set[A])) =>
     B]((aa: (set[(int, set[A])]) => B) =>
          (ba: set[set[(int, set[A])]]) =>
            argmax[set[(int, set[A])], B](aa, ba),
         (aa: ((int, set[A])) => B) =>
           (ba: set[(int, set[A])]) =>
             setsum[(int, set[A]),
                     B](aa, ba))).apply(b).apply(seta[set[(int,
                    set[A])]](map[set[(set[A], int)],
                                   set[(int,
 set[A])]]((aa: set[(set[A], int)]) => converse[set[A], int](aa),
            maps[List[set[A]],
                  set[(set[A],
                        int)]]((l: List[set[A]]) =>
                                 injections_alg[set[A],
         int](l, sup_set[int](n, insert[int](zero_int(), bot_set[int]))),
                                all_partitions_list[A](g)))))),
    map[set[(set[A], int)],
         set[(int, set[A])]]((aa: set[(set[A], int)]) =>
                               converse[set[A], int](aa),
                              maps[List[set[A]],
                                    set[(set[A],
  int)]]((l: List[set[A]]) =>
           injections_alg[set[A],
                           int](l, sup_set[int](n,
         insert[int](zero_int(), bot_set[int]))),
          all_partitions_list[A](g))))))).apply(r)))),
    insert[nat](one_nat, bot_set[nat]))),
                 (fst[int, set[A]](pair), ga))
 else zero_nata),
                                      finestpart[A](snd[int, set[A]](pair)))),
                     product[int, set[A]](sup_set[int](n,
                insert[int](zero_int(), bot_set[int])),
   remove[set[A]](bot_set[A], Pow[A](seta[A](g))))))))
    eval_rel[(int, set[A]),
              nat](image[(int, set[A]),
                          ((int, set[A]),
                            nat)]((pair: (int, set[A])) =>
                                    (pair,
                                      setsum[set[A],
      nat]((ga: set[A]) =>
             (if (member[(int, set[A])]((fst[int, set[A]](pair), ga),
 Domain[(int, set[A]),
         nat](paste[(int, set[A]),
                     nat](product[(int, set[A]),
                                   nat](product[int,
         set[A]](sup_set[int](n, insert[int](zero_int(), bot_set[int])),
                  finestpart[A](seta[A](g))),
 insert[nat](zero_nata, bot_set[nat])),
                           product[(int, set[A]),
                                    nat](Sup_set[(int,
           set[A])](image[(int, set[A]),
                           set[(int, set[A])]]((paira: (int, set[A])) =>
         product[int, set[A]](insert[int](fst[int, set[A]](paira),
   bot_set[int]),
                               finestpart[A](snd[int, set[A]](paira))),
        hd[set[(int, set[A])]]((perm2[set[(int,
    set[A])]](map[nat, set[(int, set[A])]]((aa: nat) =>
     nth[set[(int, set[A])]](map[set[(set[A], int)],
                                  set[(int,
set[A])]]((ab: set[(set[A], int)]) => converse[set[A], int](ab),
           maps[List[set[A]],
                 set[(set[A],
                       int)]]((l: List[set[A]]) =>
                                injections_alg[set[A],
        int](l, sup_set[int](n, insert[int](zero_int(), bot_set[int]))),
                               all_partitions_list[A](g))),
                              aa),
    filterpositions2[set[(int, set[A])]]((xa: set[(int, set[A])]) =>
   member[set[(int, set[A])]](xa, (comp[(set[(int, set[A])]) => B,
 (set[set[(int, set[A])]]) => set[set[(int, set[A])]],
 ((int, set[A])) =>
   B]((aa: (set[(int, set[A])]) => B) =>
        (ba: set[set[(int, set[A])]]) => argmax[set[(int, set[A])], B](aa, ba),
       (aa: ((int, set[A])) => B) =>
         (ba: set[(int, set[A])]) =>
           setsum[(int, set[A]),
                   B](aa, ba))).apply(b).apply(seta[set[(int,
                  set[A])]](map[set[(set[A], int)],
                                 set[(int, set[A])]]((aa: set[(set[A], int)]) =>
               converse[set[A], int](aa),
              maps[List[set[A]],
                    set[(set[A],
                          int)]]((l: List[set[A]]) =>
                                   injections_alg[set[A],
           int](l, sup_set[int](n, insert[int](zero_int(), bot_set[int]))),
                                  all_partitions_list[A](g)))))),
  map[set[(set[A], int)],
       set[(int, set[A])]]((aa: set[(set[A], int)]) =>
                             converse[set[A], int](aa),
                            maps[List[set[A]],
                                  set[(set[A],
int)]]((l: List[set[A]]) =>
         injections_alg[set[A],
                         int](l, sup_set[int](n,
       insert[int](zero_int(), bot_set[int]))),
        all_partitions_list[A](g))))))).apply(r)))),
  insert[nat](one_nat, bot_set[nat]))))))
               eval_rel[(int, set[A]),
                         nat](paste[(int, set[A]),
                                     nat](product[(int, set[A]),
           nat](product[int, set[A]](sup_set[int](n,
           insert[int](zero_int(), bot_set[int])),
                                      finestpart[A](seta[A](g))),
                 insert[nat](zero_nata, bot_set[nat])),
   product[(int, set[A]),
            nat](Sup_set[(int, set[A])](image[(int, set[A]),
       set[(int, set[A])]]((paira: (int, set[A])) =>
                             product[int, set[A]](insert[int](fst[int,
                           set[A]](paira),
                       bot_set[int]),
           finestpart[A](snd[int, set[A]](paira))),
                            hd[set[(int, set[A])]]((perm2[set[(int,
                        set[A])]](map[nat, set[(int,
         set[A])]]((aa: nat) =>
                     nth[set[(int, set[A])]](map[set[(set[A], int)],
          set[(int, set[A])]]((ab: set[(set[A], int)]) =>
                                converse[set[A], int](ab),
                               maps[List[set[A]],
                                     set[(set[A],
   int)]]((l: List[set[A]]) =>
            injections_alg[set[A],
                            int](l, sup_set[int](n,
          insert[int](zero_int(), bot_set[int]))),
           all_partitions_list[A](g))),
      aa),
                    filterpositions2[set[(int,
   set[A])]]((xa: set[(int, set[A])]) =>
               member[set[(int, set[A])]](xa,
   (comp[(set[(int, set[A])]) => B,
          (set[set[(int, set[A])]]) => set[set[(int, set[A])]],
          ((int, set[A])) =>
            B]((aa: (set[(int, set[A])]) => B) =>
                 (ba: set[set[(int, set[A])]]) =>
                   argmax[set[(int, set[A])], B](aa, ba),
                (aa: ((int, set[A])) => B) =>
                  (ba: set[(int, set[A])]) =>
                    setsum[(int, set[A]),
                            B](aa, ba))).apply(b).apply(seta[set[(int,
                           set[A])]](map[set[(set[A], int)],
  set[(int, set[A])]]((aa: set[(set[A], int)]) => converse[set[A], int](aa),
                       maps[List[set[A]],
                             set[(set[A],
                                   int)]]((l: List[set[A]]) =>
    injections_alg[set[A],
                    int](l, sup_set[int](n,
  insert[int](zero_int(), bot_set[int]))),
   all_partitions_list[A](g)))))),
              map[set[(set[A], int)],
                   set[(int, set[A])]]((aa: set[(set[A], int)]) =>
 converse[set[A], int](aa),
maps[List[set[A]],
      set[(set[A],
            int)]]((l: List[set[A]]) =>
                     injections_alg[set[A],
                                     int](l,
   sup_set[int](n, insert[int](zero_int(), bot_set[int]))),
                    all_partitions_list[A](g))))))).apply(r)))),
                  insert[nat](one_nat, bot_set[nat]))),
                               (fst[int, set[A]](pair), ga))
               else zero_nata),
            finestpart[A](snd[int, set[A]](pair)))),
                                   product[int,
    set[A]](sup_set[int](n, insert[int](zero_int(), bot_set[int])),
             remove[set[A]](bot_set[A], Pow[A](seta[A](g))))),
                    x)
    else zero_nata),
 a),
                          argmax[set[(int, set[A])],
                                  B]((a: set[(int, set[A])]) =>
                                       setsum[(int, set[A]), B](b, a),
                                      seta[set[(int,
         set[A])]](map[set[(set[A], int)],
                        set[(int, set[A])]]((a: set[(set[A], int)]) =>
      converse[set[A], int](a),
     maps[List[set[A]],
           set[(set[A],
                 int)]]((l: List[set[A]]) =>
                          injections_alg[set[A],
  int](l, sup_set[int](insert[int](zero_int(), bot_set[int]), n)),
                         all_partitions_list[A](g))))))),
                        insert[int](zero_int(), bot_set[int]))

def vcgpComp[A : equal,
              B : comm_monoid_add : minus : equal : linorder](na: set[int],
                       g: List[A], b: ((int, set[A])) => B, r: nat, n: int):
      B
  =
  minus[B](Max[B](image[set[(int, set[A])],
                         B]((a: set[(int, set[A])]) =>
                              setsum[(int, set[A]), B](b, a),
                             image[set[(int, set[A])],
                                    set[(int,
  set[A])]]((f: set[(int, set[A])]) =>
              Outside[int, set[A]](f, insert[int](zero_int(), bot_set[int])),
             seta[set[(int, set[A])]](map[set[(set[A], int)],
   set[(int, set[A])]]((a: set[(set[A], int)]) => converse[set[A], int](a),
                        maps[List[set[A]],
                              set[(set[A],
                                    int)]]((l: List[set[A]]) =>
     injections_alg[set[A],
                     int](l, sup_set[int](remove[int](n, na),
   insert[int](zero_int(), bot_set[int]))),
    all_partitions_list[A](g))))))),
            setsum[(int, set[A]),
                    B](b, Outside[int, set[A]](vcga[A, B](na, g, b, r),
        insert[int](n, bot_set[int]))))

} /* object VCG */
