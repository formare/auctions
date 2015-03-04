object VCG {

abstract sealed class nat
final case class Nat(a: BigInt) extends nat

def integer_of_nat(x0: nat): BigInt = x0 match {
  case Nat(x) => x
}

def equal_nata(m: nat, n: nat): Boolean = integer_of_nat(m) == integer_of_nat(n)

trait equal[A] {
  val `VCG.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`VCG.equal`(a, b)

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

trait ord[A] {
  val `VCG.less_eq`: (A, A) => Boolean
  val `VCG.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`VCG.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`VCG.less`(a, b)

def less_nat(m: nat, n: nat): Boolean = integer_of_nat(m) < integer_of_nat(n)

implicit def ord_nat: ord[nat] = new ord[nat] {
  val `VCG.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `VCG.less` = (a: nat, b: nat) => less_nat(a, b)
}

trait preorder[A] extends ord[A] {
}

trait order[A] extends preorder[A] {
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

trait linorder[A] extends order[A] {
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

def equal_lista[A : equal](x0: List[A], x1: List[A]): Boolean = (x0, x1) match {
  case (Nil, x21 :: x22) => false
  case (x21 :: x22, Nil) => false
  case (x21 :: x22, y21 :: y22) => eq[A](x21, y21) && equal_lista[A](x22, y22)
  case (Nil, Nil) => true
}

implicit def equal_list[A : equal]: equal[List[A]] = new equal[List[A]] {
  val `VCG.equal` = (a: List[A], b: List[A]) => equal_lista[A](a, b)
}

def equal_proda[A : equal, B : equal](x0: (A, B), x1: (A, B)): Boolean =
  (x0, x1) match {
  case ((x1, x2), (y1, y2)) => eq[A](x1, y1) && eq[B](x2, y2)
}

implicit def equal_prod[A : equal, B : equal]: equal[(A, B)] = new equal[(A, B)]
  {
  val `VCG.equal` = (a: (A, B), b: (A, B)) => equal_proda[A, B](a, b)
}

implicit def equal_integer: equal[BigInt] = new equal[BigInt] {
  val `VCG.equal` = (a: BigInt, b: BigInt) => a == b
}

implicit def plus_integer: plus[BigInt] = new plus[BigInt] {
  val `VCG.plus` = (a: BigInt, b: BigInt) => a + b
}

implicit def zero_integer: zero[BigInt] = new zero[BigInt] {
  val `VCG.zero` = BigInt(0)
}

trait minus[A] {
  val `VCG.minus`: (A, A) => A
}
def minus[A](a: A, b: A)(implicit A: minus[A]): A = A.`VCG.minus`(a, b)

implicit def minus_integer: minus[BigInt] = new minus[BigInt] {
  val `VCG.minus` = (a: BigInt, b: BigInt) => a - b
}

implicit def ord_integer: ord[BigInt] = new ord[BigInt] {
  val `VCG.less_eq` = (a: BigInt, b: BigInt) => a <= b
  val `VCG.less` = (a: BigInt, b: BigInt) => a < b
}

implicit def preorder_integer: preorder[BigInt] = new preorder[BigInt] {
  val `VCG.less_eq` = (a: BigInt, b: BigInt) => a <= b
  val `VCG.less` = (a: BigInt, b: BigInt) => a < b
}

implicit def order_integer: order[BigInt] = new order[BigInt] {
  val `VCG.less_eq` = (a: BigInt, b: BigInt) => a <= b
  val `VCG.less` = (a: BigInt, b: BigInt) => a < b
}

implicit def semigroup_add_integer: semigroup_add[BigInt] = new
  semigroup_add[BigInt] {
  val `VCG.plus` = (a: BigInt, b: BigInt) => a + b
}

implicit def monoid_add_integer: monoid_add[BigInt] = new monoid_add[BigInt] {
  val `VCG.zero` = BigInt(0)
  val `VCG.plus` = (a: BigInt, b: BigInt) => a + b
}

implicit def linorder_integer: linorder[BigInt] = new linorder[BigInt] {
  val `VCG.less_eq` = (a: BigInt, b: BigInt) => a <= b
  val `VCG.less` = (a: BigInt, b: BigInt) => a < b
}

implicit def ab_semigroup_add_integer: ab_semigroup_add[BigInt] = new
  ab_semigroup_add[BigInt] {
  val `VCG.plus` = (a: BigInt, b: BigInt) => a + b
}

implicit def comm_monoid_add_integer: comm_monoid_add[BigInt] = new
  comm_monoid_add[BigInt] {
  val `VCG.zero` = BigInt(0)
  val `VCG.plus` = (a: BigInt, b: BigInt) => a + b
}

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

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

def concat[A](xss: List[List[A]]): List[A] =
  (foldr[List[A],
          List[A]]((a: List[A]) => (b: List[A]) => a ++ b, xss)).apply(Nil)

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

def b1: List[List[List[BigInt]]] =
  List(List(List(BigInt(1)), List(BigInt(11), BigInt(12)), List(BigInt(2))),
        List(List(BigInt(2)), List(BigInt(11)), List(BigInt(2))),
        List(List(BigInt(2)), List(BigInt(12)), List(BigInt(2))),
        List(List(BigInt(3)), List(BigInt(11)), List(BigInt(2))),
        List(List(BigInt(3)), List(BigInt(12)), List(BigInt(2))))

def r1: BigInt = BigInt(1)

def minus_set[A : equal](a: set[A], x1: set[A]): set[A] = (a, x1) match {
  case (a, coset(xs)) => seta[A](filtera[A]((x: A) => member[A](x, a), xs))
  case (a, seta(xs)) =>
    fold[A, set[A]]((aa: A) => (b: set[A]) => remove[A](aa, b), xs, a)
}

def Outside[A : equal, B : equal](r: set[(A, B)], x: set[A]): set[(A, B)] =
  minus_set[(A, B)](r, product[A, B](x, Range[A, B](r)))

def paste[A : equal, B : equal](p: set[(A, B)], q: set[(A, B)]): set[(A, B)] =
  sup_set[(A, B)](Outside[A, B](p, Domain[A, B](q)), q)

def eval_rel[A : equal, B](r: set[(A, B)], a: A): B =
  the_elem[B](Image[A, B](r, insert[A](a, bot_set[A])))

def nat_of_integer(k: BigInt): nat = Nat(max[BigInt](BigInt(0), k))

def helper[A](list: List[List[A]]): ((A, set[A]), A) =
  (((comp[List[A], A,
           List[List[A]]]((a: List[A]) => hd[A](a),
                           (a: List[List[A]]) => hd[List[A]](a))).apply(list),
     seta[A](nth[List[A]](list, one_nat))),
    hd[A](nth[List[A]](list, nat_of_integer(BigInt(2)))))

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

def vcgaAlgWithoutLosers[A : equal,
                          B : comm_monoid_add : equal : linorder](n:
                            set[BigInt],
                           g: List[A], b: ((BigInt, set[A])) => B, r: BigInt):
      set[(BigInt, set[A])]
  =
  Outside[BigInt,
           set[A]](the_elem[set[(BigInt,
                                  set[A])]](argmax[set[(BigInt, set[A])],
            nat]((a: set[(BigInt, set[A])]) =>
                   setsum[(BigInt, set[A]),
                           nat]((x: (BigInt, set[A])) =>
                                  (if (member[(BigInt,
        set[A])](x, Domain[(BigInt, set[A]),
                            nat](image[(BigInt, set[A]),
((BigInt, set[A]),
  nat)]((pair: (BigInt, set[A])) =>
          (pair,
            setsum[set[A],
                    nat]((ga: set[A]) =>
                           (if (member[(BigInt,
 set[A])]((fst[BigInt, set[A]](pair), ga),
           Domain[(BigInt, set[A]),
                   nat](paste[(BigInt, set[A]),
                               nat](product[(BigInt, set[A]),
     nat](product[BigInt,
                   set[A]](sup_set[BigInt](n,
    insert[BigInt](BigInt(0), bot_set[BigInt])),
                            finestpart[A](seta[A](g))),
           insert[nat](zero_nata, bot_set[nat])),
                                     product[(BigInt, set[A]),
      nat](Sup_set[(BigInt,
                     set[A])](image[(BigInt, set[A]),
                                     set[(BigInt,
   set[A])]]((paira: (BigInt, set[A])) =>
               product[BigInt,
                        set[A]](insert[BigInt](fst[BigInt, set[A]](paira),
        bot_set[BigInt]),
                                 finestpart[A](snd[BigInt, set[A]](paira))),
              hd[set[(BigInt,
                       set[A])]]((perm2[set[(BigInt,
      set[A])]](map[nat, set[(BigInt,
                               set[A])]]((aa: nat) =>
   nth[set[(BigInt,
             set[A])]](map[set[(set[A], BigInt)],
                            set[(BigInt,
                                  set[A])]]((ab: set[(set[A], BigInt)]) =>
      converse[set[A], BigInt](ab),
     maps[List[set[A]],
           set[(set[A],
                 BigInt)]]((l: List[set[A]]) =>
                             injections_alg[set[A],
     BigInt](l, sup_set[BigInt](n, insert[BigInt](BigInt(0), bot_set[BigInt]))),
                            all_partitions_list[A](g))),
                        aa),
  filterpositions2[set[(BigInt,
                         set[A])]]((xa: set[(BigInt, set[A])]) =>
                                     member[set[(BigInt,
          set[A])]](xa, (comp[(set[(BigInt, set[A])]) => B,
                               (set[set[(BigInt, set[A])]]) =>
                                 set[set[(BigInt, set[A])]],
                               ((BigInt, set[A])) =>
                                 B]((aa: (set[(BigInt, set[A])]) => B) =>
                                      (ba: set[set[(BigInt, set[A])]]) =>
argmax[set[(BigInt, set[A])], B](aa, ba),
                                     (aa: ((BigInt, set[A])) => B) =>
                                       (ba: set[(BigInt, set[A])]) =>
 setsum[(BigInt, set[A]),
         B](aa, ba))).apply(b).apply(seta[set[(BigInt,
        set[A])]](map[set[(set[A], BigInt)],
                       set[(BigInt,
                             set[A])]]((aa: set[(set[A], BigInt)]) =>
 converse[set[A], BigInt](aa),
maps[List[set[A]],
      set[(set[A],
            BigInt)]]((l: List[set[A]]) =>
                        injections_alg[set[A],
BigInt](l, sup_set[BigInt](n, insert[BigInt](BigInt(0), bot_set[BigInt]))),
                       all_partitions_list[A](g)))))),
                                    map[set[(set[A], BigInt)],
 set[(BigInt,
       set[A])]]((aa: set[(set[A], BigInt)]) => converse[set[A], BigInt](aa),
                  maps[List[set[A]],
                        set[(set[A],
                              BigInt)]]((l: List[set[A]]) =>
  injections_alg[set[A],
                  BigInt](l, sup_set[BigInt](n,
      insert[BigInt](BigInt(0), bot_set[BigInt]))),
 all_partitions_list[A](g))))))).apply(nat_of_integer(r))))),
            insert[nat](one_nat, bot_set[nat]))))))
                             eval_rel[(BigInt, set[A]),
                                       nat](paste[(BigInt, set[A]),
           nat](product[(BigInt, set[A]),
                         nat](product[BigInt,
                                       set[A]](sup_set[BigInt](n,
                        insert[BigInt](BigInt(0), bot_set[BigInt])),
        finestpart[A](seta[A](g))),
                               insert[nat](zero_nata, bot_set[nat])),
                 product[(BigInt, set[A]),
                          nat](Sup_set[(BigInt,
 set[A])](image[(BigInt, set[A]),
                 set[(BigInt,
                       set[A])]]((paira: (BigInt, set[A])) =>
                                   product[BigInt,
    set[A]](insert[BigInt](fst[BigInt, set[A]](paira), bot_set[BigInt]),
             finestpart[A](snd[BigInt, set[A]](paira))),
                                  hd[set[(BigInt,
   set[A])]]((perm2[set[(BigInt,
                          set[A])]](map[nat,
 set[(BigInt,
       set[A])]]((aa: nat) =>
                   nth[set[(BigInt,
                             set[A])]](map[set[(set[A], BigInt)],
    set[(BigInt,
          set[A])]]((ab: set[(set[A], BigInt)]) => converse[set[A], BigInt](ab),
                     maps[List[set[A]],
                           set[(set[A],
                                 BigInt)]]((l: List[set[A]]) =>
     injections_alg[set[A],
                     BigInt](l, sup_set[BigInt](n,
         insert[BigInt](BigInt(0), bot_set[BigInt]))),
    all_partitions_list[A](g))),
aa),
                  filterpositions2[set[(BigInt,
 set[A])]]((xa: set[(BigInt, set[A])]) =>
             member[set[(BigInt,
                          set[A])]](xa, (comp[(set[(BigInt, set[A])]) => B,
       (set[set[(BigInt, set[A])]]) => set[set[(BigInt, set[A])]],
       ((BigInt, set[A])) =>
         B]((aa: (set[(BigInt, set[A])]) => B) =>
              (ba: set[set[(BigInt, set[A])]]) =>
                argmax[set[(BigInt, set[A])], B](aa, ba),
             (aa: ((BigInt, set[A])) => B) =>
               (ba: set[(BigInt, set[A])]) =>
                 setsum[(BigInt, set[A]),
                         B](aa, ba))).apply(b).apply(seta[set[(BigInt,
                        set[A])]](map[set[(set[A], BigInt)],
                                       set[(BigInt,
     set[A])]]((aa: set[(set[A], BigInt)]) => converse[set[A], BigInt](aa),
                maps[List[set[A]],
                      set[(set[A],
                            BigInt)]]((l: List[set[A]]) =>
injections_alg[set[A],
                BigInt](l, sup_set[BigInt](n,
    insert[BigInt](BigInt(0), bot_set[BigInt]))),
                                       all_partitions_list[A](g)))))),
            map[set[(set[A], BigInt)],
                 set[(BigInt,
                       set[A])]]((aa: set[(set[A], BigInt)]) =>
                                   converse[set[A], BigInt](aa),
                                  maps[List[set[A]],
set[(set[A],
      BigInt)]]((l: List[set[A]]) =>
                  injections_alg[set[A],
                                  BigInt](l,
   sup_set[BigInt](n, insert[BigInt](BigInt(0), bot_set[BigInt]))),
                 all_partitions_list[A](g))))))).apply(nat_of_integer(r))))),
                                insert[nat](one_nat, bot_set[nat]))),
     (fst[BigInt, set[A]](pair), ga))
                             else zero_nata),
                          finestpart[A](snd[BigInt, set[A]](pair)))),
         product[BigInt,
                  set[A]](sup_set[BigInt](n,
   insert[BigInt](BigInt(0), bot_set[BigInt])),
                           remove[set[A]](bot_set[A], Pow[A](seta[A](g))))))))
                                    eval_rel[(BigInt, set[A]),
      nat](image[(BigInt, set[A]),
                  ((BigInt, set[A]),
                    nat)]((pair: (BigInt, set[A])) =>
                            (pair,
                              setsum[set[A],
                                      nat]((ga: set[A]) =>
     (if (member[(BigInt,
                   set[A])]((fst[BigInt, set[A]](pair), ga),
                             Domain[(BigInt, set[A]),
                                     nat](paste[(BigInt, set[A]),
         nat](product[(BigInt, set[A]),
                       nat](product[BigInt,
                                     set[A]](sup_set[BigInt](n,
                      insert[BigInt](BigInt(0), bot_set[BigInt])),
      finestpart[A](seta[A](g))),
                             insert[nat](zero_nata, bot_set[nat])),
               product[(BigInt, set[A]),
                        nat](Sup_set[(BigInt,
                                       set[A])](image[(BigInt, set[A]),
               set[(BigInt,
                     set[A])]]((paira: (BigInt, set[A])) =>
                                 product[BigInt,
  set[A]](insert[BigInt](fst[BigInt, set[A]](paira), bot_set[BigInt]),
           finestpart[A](snd[BigInt, set[A]](paira))),
                                hd[set[(BigInt,
 set[A])]]((perm2[set[(BigInt,
                        set[A])]](map[nat, set[(BigInt,
         set[A])]]((aa: nat) =>
                     nth[set[(BigInt,
                               set[A])]](map[set[(set[A], BigInt)],
      set[(BigInt,
            set[A])]]((ab: set[(set[A], BigInt)]) =>
                        converse[set[A], BigInt](ab),
                       maps[List[set[A]],
                             set[(set[A],
                                   BigInt)]]((l: List[set[A]]) =>
       injections_alg[set[A],
                       BigInt](l, sup_set[BigInt](n,
           insert[BigInt](BigInt(0), bot_set[BigInt]))),
      all_partitions_list[A](g))),
  aa),
                    filterpositions2[set[(BigInt,
   set[A])]]((xa: set[(BigInt, set[A])]) =>
               member[set[(BigInt,
                            set[A])]](xa, (comp[(set[(BigInt, set[A])]) => B,
         (set[set[(BigInt, set[A])]]) => set[set[(BigInt, set[A])]],
         ((BigInt, set[A])) =>
           B]((aa: (set[(BigInt, set[A])]) => B) =>
                (ba: set[set[(BigInt, set[A])]]) =>
                  argmax[set[(BigInt, set[A])], B](aa, ba),
               (aa: ((BigInt, set[A])) => B) =>
                 (ba: set[(BigInt, set[A])]) =>
                   setsum[(BigInt, set[A]),
                           B](aa, ba))).apply(b).apply(seta[set[(BigInt,
                          set[A])]](map[set[(set[A], BigInt)],
 set[(BigInt,
       set[A])]]((aa: set[(set[A], BigInt)]) => converse[set[A], BigInt](aa),
                  maps[List[set[A]],
                        set[(set[A],
                              BigInt)]]((l: List[set[A]]) =>
  injections_alg[set[A],
                  BigInt](l, sup_set[BigInt](n,
      insert[BigInt](BigInt(0), bot_set[BigInt]))),
 all_partitions_list[A](g)))))),
              map[set[(set[A], BigInt)],
                   set[(BigInt,
                         set[A])]]((aa: set[(set[A], BigInt)]) =>
                                     converse[set[A], BigInt](aa),
                                    maps[List[set[A]],
  set[(set[A],
        BigInt)]]((l: List[set[A]]) =>
                    injections_alg[set[A],
                                    BigInt](l,
     sup_set[BigInt](n, insert[BigInt](BigInt(0), bot_set[BigInt]))),
                   all_partitions_list[A](g))))))).apply(nat_of_integer(r))))),
                              insert[nat](one_nat, bot_set[nat]))))))
       eval_rel[(BigInt, set[A]),
                 nat](paste[(BigInt, set[A]),
                             nat](product[(BigInt, set[A]),
   nat](product[BigInt,
                 set[A]](sup_set[BigInt](n,
  insert[BigInt](BigInt(0), bot_set[BigInt])),
                          finestpart[A](seta[A](g))),
         insert[nat](zero_nata, bot_set[nat])),
                                   product[(BigInt, set[A]),
    nat](Sup_set[(BigInt,
                   set[A])](image[(BigInt, set[A]),
                                   set[(BigInt,
 set[A])]]((paira: (BigInt, set[A])) =>
             product[BigInt,
                      set[A]](insert[BigInt](fst[BigInt, set[A]](paira),
      bot_set[BigInt]),
                               finestpart[A](snd[BigInt, set[A]](paira))),
            hd[set[(BigInt,
                     set[A])]]((perm2[set[(BigInt,
    set[A])]](map[nat, set[(BigInt,
                             set[A])]]((aa: nat) =>
 nth[set[(BigInt,
           set[A])]](map[set[(set[A], BigInt)],
                          set[(BigInt,
                                set[A])]]((ab: set[(set[A], BigInt)]) =>
    converse[set[A], BigInt](ab),
   maps[List[set[A]],
         set[(set[A],
               BigInt)]]((l: List[set[A]]) =>
                           injections_alg[set[A],
   BigInt](l, sup_set[BigInt](n, insert[BigInt](BigInt(0), bot_set[BigInt]))),
                          all_partitions_list[A](g))),
                      aa),
filterpositions2[set[(BigInt,
                       set[A])]]((xa: set[(BigInt, set[A])]) =>
                                   member[set[(BigInt,
        set[A])]](xa, (comp[(set[(BigInt, set[A])]) => B,
                             (set[set[(BigInt, set[A])]]) =>
                               set[set[(BigInt, set[A])]],
                             ((BigInt, set[A])) =>
                               B]((aa: (set[(BigInt, set[A])]) => B) =>
                                    (ba: set[set[(BigInt, set[A])]]) =>
                                      argmax[set[(BigInt, set[A])], B](aa, ba),
                                   (aa: ((BigInt, set[A])) => B) =>
                                     (ba: set[(BigInt, set[A])]) =>
                                       setsum[(BigInt, set[A]),
       B](aa, ba))).apply(b).apply(seta[set[(BigInt,
      set[A])]](map[set[(set[A], BigInt)],
                     set[(BigInt,
                           set[A])]]((aa: set[(set[A], BigInt)]) =>
                                       converse[set[A], BigInt](aa),
                                      maps[List[set[A]],
    set[(set[A],
          BigInt)]]((l: List[set[A]]) =>
                      injections_alg[set[A],
                                      BigInt](l,
       sup_set[BigInt](n, insert[BigInt](BigInt(0), bot_set[BigInt]))),
                     all_partitions_list[A](g)))))),
                                  map[set[(set[A], BigInt)],
                                       set[(BigInt,
     set[A])]]((aa: set[(set[A], BigInt)]) => converse[set[A], BigInt](aa),
                maps[List[set[A]],
                      set[(set[A],
                            BigInt)]]((l: List[set[A]]) =>
injections_alg[set[A],
                BigInt](l, sup_set[BigInt](n,
    insert[BigInt](BigInt(0), bot_set[BigInt]))),
                                       all_partitions_list[A](g))))))).apply(nat_of_integer(r))))),
          insert[nat](one_nat, bot_set[nat]))),
                       (fst[BigInt, set[A]](pair), ga))
       else zero_nata),
    finestpart[A](snd[BigInt, set[A]](pair)))),
                           product[BigInt,
                                    set[A]](sup_set[BigInt](n,
                     insert[BigInt](BigInt(0), bot_set[BigInt])),
     remove[set[A]](bot_set[A], Pow[A](seta[A](g))))),
            x)
                                    else zero_nata),
                                 a),
                  argmax[set[(BigInt, set[A])],
                          B]((a: set[(BigInt, set[A])]) =>
                               setsum[(BigInt, set[A]), B](b, a),
                              seta[set[(BigInt,
 set[A])]](map[set[(set[A], BigInt)],
                set[(BigInt,
                      set[A])]]((a: set[(set[A], BigInt)]) =>
                                  converse[set[A], BigInt](a),
                                 maps[List[set[A]],
                                       set[(set[A],
     BigInt)]]((l: List[set[A]]) =>
                 injections_alg[set[A],
                                 BigInt](l,
  sup_set[BigInt](insert[BigInt](BigInt(0), bot_set[BigInt]), n)),
                all_partitions_list[A](g))))))),
                    insert[BigInt](BigInt(0), bot_set[BigInt]))

def vcgaAlg[A : equal,
             B : comm_monoid_add : equal : linorder](n: set[BigInt], g: List[A],
              b: ((BigInt, set[A])) => B, r: BigInt):
      set[(BigInt, set[A])]
  =
  paste[BigInt,
         set[A]](product[BigInt,
                          set[A]](n, insert[set[A]](bot_set[A],
             bot_set[set[A]])),
                  vcgaAlgWithoutLosers[A, B](n, g, b, r))

def vcgpAlg[A : equal,
             B : comm_monoid_add : minus : equal : linorder](na: set[BigInt],
                      g: List[A], b: ((BigInt, set[A])) => B, r: BigInt,
                      n: BigInt):
      B
  =
  minus[B](Max[B](image[set[(BigInt, set[A])],
                         B]((a: set[(BigInt, set[A])]) =>
                              setsum[(BigInt, set[A]), B](b, a),
                             image[set[(BigInt, set[A])],
                                    set[(BigInt,
  set[A])]]((f: set[(BigInt, set[A])]) =>
              Outside[BigInt,
                       set[A]](f, insert[BigInt](BigInt(0), bot_set[BigInt])),
             seta[set[(BigInt,
                        set[A])]](map[set[(set[A], BigInt)],
                                       set[(BigInt,
     set[A])]]((a: set[(set[A], BigInt)]) => converse[set[A], BigInt](a),
                maps[List[set[A]],
                      set[(set[A],
                            BigInt)]]((l: List[set[A]]) =>
injections_alg[set[A],
                BigInt](l, sup_set[BigInt](remove[BigInt](n, na),
    insert[BigInt](BigInt(0), bot_set[BigInt]))),
                                       all_partitions_list[A](g))))))),
            setsum[(BigInt, set[A]),
                    B](b, Outside[BigInt,
                                   set[A]](vcgaAlgWithoutLosers[A,
                         B](na, g, b, r),
    insert[BigInt](n, bot_set[BigInt]))))

def listBid2funcBid(listBid: List[List[List[BigInt]]]):
      ((BigInt, set[BigInt])) => BigInt
  =
  (x: (BigInt, set[BigInt])) =>
    (if (member[(BigInt,
                  set[BigInt])](x, Domain[(BigInt, set[BigInt]),
   BigInt](image[List[List[BigInt]],
                  ((BigInt, set[BigInt]),
                    BigInt)]((a: List[List[BigInt]]) => helper[BigInt](a),
                              seta[List[List[BigInt]]](listBid)))))
      eval_rel[(BigInt, set[BigInt]),
                BigInt](image[List[List[BigInt]],
                               ((BigInt, set[BigInt]),
                                 BigInt)]((a: List[List[BigInt]]) =>
    helper[BigInt](a),
   seta[List[List[BigInt]]](listBid)),
                         x)
      else BigInt(0))

def payments(b: List[List[List[BigInt]]], r: BigInt): BigInt => BigInt =
  (a: BigInt) =>
    vcgpAlg[BigInt,
             BigInt](seta[BigInt]((comp[List[BigInt], List[BigInt],
 List[List[List[BigInt]]]]((aa: List[BigInt]) => remdups[BigInt](aa),
                            (aa: List[List[List[BigInt]]]) =>
                              map[List[List[BigInt]],
                                   BigInt](comp[List[BigInt], BigInt,
         List[List[BigInt]]]((ab: List[BigInt]) => hd[BigInt](ab),
                              (ab: List[List[BigInt]]) => hd[List[BigInt]](ab)),
    aa))).apply(b)),
                      (comp[List[List[BigInt]], List[BigInt],
                             List[List[List[BigInt]]]](comp[List[BigInt],
                     List[BigInt],
                     List[List[BigInt]]]((aa: List[BigInt]) =>
   remdups[BigInt](aa),
  (aa: List[List[BigInt]]) => concat[BigInt](aa)),
                (aa: List[List[List[BigInt]]]) =>
                  map[List[List[BigInt]],
                       List[BigInt]]((l: List[List[BigInt]]) =>
                                       nth[List[BigInt]](l, one_nat),
                                      aa))).apply(b),
                      listBid2funcBid(b), r, a)

def allocation(b: List[List[List[BigInt]]], r: BigInt):
      set[List[(BigInt, List[BigInt])]]
  =
  insert[List[(BigInt,
                List[BigInt])]](map[BigInt,
                                     (BigInt,
                                       List[BigInt])]((x: BigInt) =>
                (x, sorted_list_of_set[BigInt](eval_rel[BigInt,
                 set[BigInt]](vcgaAlg[BigInt,
                                       BigInt](seta[BigInt]((comp[List[BigInt],
                           List[BigInt],
                           List[List[List[BigInt]]]]((a: List[BigInt]) =>
               remdups[BigInt](a),
              (a: List[List[List[BigInt]]]) =>
                map[List[List[BigInt]],
                     BigInt](comp[List[BigInt], BigInt,
                                   List[List[BigInt]]]((aa: List[BigInt]) =>
                 hd[BigInt](aa),
                (aa: List[List[BigInt]]) => hd[List[BigInt]](aa)),
                              a))).apply(b)),
        (comp[List[List[BigInt]], List[BigInt],
               List[List[List[BigInt]]]](comp[List[BigInt], List[BigInt],
       List[List[BigInt]]]((a: List[BigInt]) => remdups[BigInt](a),
                            (a: List[List[BigInt]]) => concat[BigInt](a)),
  (a: List[List[List[BigInt]]]) =>
    map[List[List[BigInt]],
         List[BigInt]]((l: List[List[BigInt]]) => nth[List[BigInt]](l, one_nat),
                        a))).apply(b),
        listBid2funcBid(b), r),
                               x))),
               (comp[set[BigInt], List[BigInt],
                      set[(BigInt,
                            set[BigInt])]]((a: set[BigInt]) =>
     sorted_list_of_set[BigInt](a),
    (a: set[(BigInt, set[BigInt])]) =>
      Domain[BigInt,
              set[BigInt]](a))).apply(vcgaAlg[BigInt,
       BigInt](seta[BigInt]((comp[List[BigInt], List[BigInt],
                                   List[List[List[BigInt]]]]((a: List[BigInt])
                       => remdups[BigInt](a),
                      (a: List[List[List[BigInt]]]) =>
                        map[List[List[BigInt]],
                             BigInt](comp[List[BigInt], BigInt,
   List[List[BigInt]]]((aa: List[BigInt]) => hd[BigInt](aa),
                        (aa: List[List[BigInt]]) => hd[List[BigInt]](aa)),
                                      a))).apply(b)),
                (comp[List[List[BigInt]], List[BigInt],
                       List[List[List[BigInt]]]](comp[List[BigInt],
               List[BigInt],
               List[List[BigInt]]]((a: List[BigInt]) => remdups[BigInt](a),
                                    (a: List[List[BigInt]]) =>
                                      concat[BigInt](a)),
          (a: List[List[List[BigInt]]]) =>
            map[List[List[BigInt]],
                 List[BigInt]]((l: List[List[BigInt]]) =>
                                 nth[List[BigInt]](l, one_nat),
                                a))).apply(b),
                listBid2funcBid(b), r))),
                                 bot_set[List[(BigInt, List[BigInt])]])

} /* object VCG */
