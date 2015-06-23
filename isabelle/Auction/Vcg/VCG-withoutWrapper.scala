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

def filter[A](p: A => Boolean, x1: set[A]): set[A] = (p, x1) match {
  case (p, seta(xs)) => seta[A](filtera[A](p, xs))
}

def remove[A : equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, coset(xs)) => coset[A](inserta[A](x, xs))
  case (x, seta(xs)) => seta[A](removeAll[A](x, xs))
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

def fst[A, B](x0: (A, B)): A = x0 match {
  case (x1, x2) => x1
}

def Domain[A, B](r: set[(A, B)]): set[A] =
  image[(A, B), A]((a: (A, B)) => fst[A, B](a), r)

def converse[A, B](r: set[(A, B)]): set[(B, A)] =
  image[(A, B), (B, A)]((a: (A, B)) => {
 val (x, y): (A, B) = a;
 (y, x)
                                       },
                         r)

def apsnd[A, B, C](f: A => B, x1: (C, A)): (C, B) = (f, x1) match {
  case (f, (x, y)) => (x, f(y))
}

def finestpart[A : equal](x: set[A]): set[set[A]] =
  image[A, set[A]]((xa: A) => insert[A](xa, bot_set[A]), x)

def product[A, B](x0: set[A], x1: set[B]): set[(A, B)] = (x0, x1) match {
  case (seta(xs), seta(ys)) =>
    seta[(A, B)](maps[A, (A, B)]((x: A) => map[B, (A, B)]((a: B) => (x, a), ys),
                                  xs))
}

def size_list[A]: (List[A]) => nat = (a: List[A]) => gen_length[A](zero_nata, a)

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

def eval_rel[A : equal, B](r: set[(A, B)], a: A): B =
  the_elem[B](Image[A, B](r, insert[A](a, bot_set[A])))

def sgn_integer(k: BigInt): BigInt =
  (if (k == BigInt(0)) BigInt(0)
    else (if (k < BigInt(0)) BigInt(- 1) else BigInt(1)))

def abs_integer(k: BigInt): BigInt = (if (k < BigInt(0)) (- k) else k)

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

def nat_of_integer(k: BigInt): nat = Nat(max[BigInt](BigInt(0), k))

def mod_integer(k: BigInt, l: BigInt): BigInt =
  snd[BigInt, BigInt](divmod_integer(k, l))

def mod_nat(m: nat, n: nat): nat =
  Nat(mod_integer(integer_of_nat(m), integer_of_nat(n)))

def randomEl[A](list: List[A], random: BigInt): A =
  nth[A](list, mod_nat(nat_of_integer(random), size_list[A].apply(list)))

def listsum[A : monoid_add](xs: List[A]): A =
  (foldr[A, A]((a: A) => (b: A) => plus[A](a, b), xs)).apply(zero[A])

def setsum[A : equal, B : comm_monoid_add](f: A => B, x1: set[A]): B = (f, x1)
  match {
  case (f, seta(xs)) => listsum[B](map[A, B](f, remdups[A](xs)))
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

def chosenAllocationAlg[A : equal : linorder, B : equal,
                         C : comm_monoid_add : equal : linorder](n: set[A],
                          omega: List[B], b: ((A, set[B])) => C, r: BigInt):
      set[(A, set[B])]
  =
  randomEl[set[(A, set[B])]](map[nat, set[(A,
    set[B])]]((a: nat) =>
                nth[set[(A, set[B])]](map[set[(set[B], A)],
   set[(A, set[B])]]((aa: set[(set[B], A)]) => converse[set[B], A](aa),
                      maps[List[set[B]],
                            set[(set[B],
                                  A)]]((l: List[set[B]]) =>
 injections_alg[set[B], A](l, n),
all_partitions_list[B](omega))),
                                       a),
               filterpositions2[set[(A, set[B])]]((x: set[(A, set[B])]) =>
            member[set[(A, set[B])]](x, (comp[(set[(A, set[B])]) => C,
       (set[set[(A, set[B])]]) => set[set[(A, set[B])]],
       ((A, set[B])) =>
         C]((a: (set[(A, set[B])]) => C) =>
              (ba: set[set[(A, set[B])]]) => argmax[set[(A, set[B])], C](a, ba),
             (a: ((A, set[B])) => C) =>
               (ba: set[(A, set[B])]) =>
                 setsum[(A, set[B]),
                         C](a, ba))).apply(b).apply(seta[set[(A,
                       set[B])]](map[set[(set[B], A)],
                                      set[(A,
    set[B])]]((a: set[(set[B], A)]) => converse[set[B], A](a),
               maps[List[set[B]],
                     set[(set[B],
                           A)]]((l: List[set[B]]) =>
                                  injections_alg[set[B], A](l, n),
                                 all_partitions_list[B](omega)))))),
           map[set[(set[B], A)],
                set[(A, set[B])]]((a: set[(set[B], A)]) =>
                                    converse[set[B], A](a),
                                   maps[List[set[B]],
 set[(set[B],
       A)]]((l: List[set[B]]) => injections_alg[set[B], A](l, n),
             all_partitions_list[B](omega))))),
                              r)

def toFunctionWithFallbackAlg[A : equal, B](r: set[(A, B)], fallback: B): A => B
  =
  (x: A) =>
    (if (member[A](x, Domain[A, B](r))) eval_rel[A, B](r, x) else fallback)

def summedBidVectorAlg[A : equal, B : equal,
                        C : comm_monoid_add](bids: ((A, set[B])) => C,
      n: set[A], omega: set[B]):
      ((A, set[B])) => C
  =
  toFunctionWithFallbackAlg[(A, set[B]),
                             C](image[(A, set[B]),
                                       ((A, set[B]),
 C)]((pair: (A, set[B])) =>
       (pair,
         setsum[set[B],
                 C]((g: set[B]) => bids((fst[A, set[B]](pair), g)),
                     finestpart[B](snd[A, set[B]](pair)))),
      product[A, set[B]](n, remove[set[B]](bot_set[B], Pow[B](omega)))),
                                 zero[C])

def Sup_set[A : equal](x0: set[set[A]]): set[A] = x0 match {
  case seta(xs) =>
    fold[set[A],
          set[A]]((a: set[A]) => (b: set[A]) => sup_set[A](a, b), xs,
                   bot_set[A])
}

def pseudoAllocation[A : equal, B : equal](allocation: set[(A, set[B])]):
      set[(A, set[B])]
  =
  Sup_set[(A, set[B])](image[(A, set[B]),
                              set[(A, set[B])]]((pair: (A, set[B])) =>
          product[A, set[B]](insert[A](fst[A, set[B]](pair), bot_set[A]),
                              finestpart[B](snd[A, set[B]](pair))),
         allocation))

def maxbidAlg[A : equal,
               B : equal](a: set[(A, set[B])], n: set[A], omega: set[B]):
      ((A, set[B])) => nat
  =
  toFunctionWithFallbackAlg[(A, set[B]),
                             nat](paste[(A, set[B]),
 nat](product[(A, set[B]),
               nat](product[A, set[B]](n, finestpart[B](omega)),
                     insert[nat](zero_nata, bot_set[nat])),
       product[(A, set[B]),
                nat](pseudoAllocation[A, B](a),
                      insert[nat](one_nat, bot_set[nat]))),
                                   zero_nata)

def tiebidsAlg[A : equal,
                B : equal](a: set[(A, set[B])], n: set[A], omega: set[B]):
      ((A, set[B])) => nat
  =
  summedBidVectorAlg[A, B, nat](maxbidAlg[A, B](a, n, omega), n, omega)

def resolvingBidAlg[A : equal : linorder, B : equal,
                     C : comm_monoid_add : equal : linorder](n: set[A],
                      omega: List[B], bids: ((A, set[B])) => C, random: BigInt):
      ((A, set[B])) => nat
  =
  tiebidsAlg[A, B](chosenAllocationAlg[A, B, C](n, omega, bids, random), n,
                    seta[B](omega))

def randomBidsAlg[A : equal,
                   B : comm_monoid_add : equal : linorder](n: set[BigInt],
                    omega: List[A], b: ((BigInt, set[A])) => B, random: BigInt):
      ((BigInt, set[A])) => nat
  =
  resolvingBidAlg[BigInt, A,
                   B](sup_set[BigInt](n, insert[BigInt](BigInt(0),
                 bot_set[BigInt])),
                       omega, b, random)

def vcgaAlgWithoutLosers[A : equal,
                          B : comm_monoid_add : equal : linorder](n:
                            set[BigInt],
                           omega: List[A], b: ((BigInt, set[A])) => B,
                           r: BigInt):
      set[(BigInt, set[A])]
  =
  Outside[BigInt,
           set[A]](the_elem[set[(BigInt,
                                  set[A])]](argmax[set[(BigInt, set[A])],
            nat]((a: set[(BigInt, set[A])]) =>
                   setsum[(BigInt, set[A]),
                           nat](randomBidsAlg[A, B](n, omega, b, r), a),
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
                all_partitions_list[A](omega))))))),
                    insert[BigInt](BigInt(0), bot_set[BigInt]))

def vcgaAlg[A : equal,
             B : comm_monoid_add : equal : linorder](n: set[BigInt],
              omega: List[A], b: ((BigInt, set[A])) => B, r: BigInt):
      set[(BigInt, set[A])]
  =
  paste[BigInt,
         set[A]](product[BigInt,
                          set[A]](n, insert[set[A]](bot_set[A],
             bot_set[set[A]])),
                  vcgaAlgWithoutLosers[A, B](n, omega, b, r))

def vcgpAlg[A : comm_monoid_add : minus : linorder,
             B](na: set[BigInt], omega: List[BigInt],
                 b: ((BigInt, set[BigInt])) => A, r: B, n: BigInt,
                 winningAllocation: set[(BigInt, set[BigInt])]):
      A
  =
  minus[A](Max[A](image[set[(BigInt, set[BigInt])],
                         A]((a: set[(BigInt, set[BigInt])]) =>
                              setsum[(BigInt, set[BigInt]), A](b, a),
                             image[set[(BigInt, set[BigInt])],
                                    set[(BigInt,
  set[BigInt])]]((f: set[(BigInt, set[BigInt])]) =>
                   Outside[BigInt,
                            set[BigInt]](f,
  insert[BigInt](BigInt(0), bot_set[BigInt])),
                  seta[set[(BigInt,
                             set[BigInt])]](map[set[(set[BigInt], BigInt)],
         set[(BigInt,
               set[BigInt])]]((a: set[(set[BigInt], BigInt)]) =>
                                converse[set[BigInt], BigInt](a),
                               maps[List[set[BigInt]],
                                     set[(set[BigInt],
   BigInt)]]((l: List[set[BigInt]]) =>
               injections_alg[set[BigInt],
                               BigInt](l,
sup_set[BigInt](remove[BigInt](n, na),
                 insert[BigInt](BigInt(0), bot_set[BigInt]))),
              all_partitions_list[BigInt](omega))))))),
            setsum[(BigInt, set[BigInt]),
                    A](b, Outside[BigInt,
                                   set[BigInt]](winningAllocation,
         insert[BigInt](n, bot_set[BigInt]))))

def participantsSet[A, B](b: List[(A, B)]): set[A] =
  image[(A, B), A]((a: (A, B)) => fst[A, B](a), seta[(A, B)](b))

def Bid2funcBid[A : equal, B : equal](b: List[(A, (List[B], BigInt))]):
      ((A, set[B])) => BigInt
  =
  toFunctionWithFallbackAlg[(A, set[B]),
                             BigInt](seta[((A, set[B]),
    BigInt)](map[(A, (List[B], BigInt)),
                  ((A, set[B]),
                    BigInt)]((x: (A, (List[B], BigInt))) =>
                               ((fst[A, (List[B], BigInt)](x),
                                  seta[B]((comp[(List[B], BigInt), List[B],
         (A, (List[B],
               BigInt))]((a: (List[B], BigInt)) => fst[List[B], BigInt](a),
                          (a: (A, (List[B], BigInt))) =>
                            snd[A, (List[B], BigInt)](a))).apply(x))),
                                 (comp[(List[B], BigInt), BigInt,
(A, (List[B],
      BigInt))]((a: (List[B], BigInt)) => snd[List[B], BigInt](a),
                 (a: (A, (List[B], BigInt))) =>
                   snd[A, (List[B], BigInt)](a))).apply(x)),
                              b)),
                                      BigInt(0))

def goodsList[A, B : equal : linorder, C](b: List[(A, (List[B], C))]): List[B] =
  sorted_list_of_set[B](Sup_set[B](image[(A, (List[B], C)),
  set[B]](comp[(List[B], C), set[B],
                (A, (List[B],
                      C))](comp[List[B], set[B],
                                 (List[B],
                                   C)]((a: List[B]) => seta[B](a),
(a: (List[B], C)) => fst[List[B], C](a)),
                            (a: (A, (List[B], C))) => snd[A, (List[B], C)](a)),
           seta[(A, (List[B], C))](b))))

def payments[A](b: List[(BigInt, (List[BigInt], BigInt))], r: A, n: BigInt,
                 a: set[(BigInt, set[BigInt])]):
      BigInt
  =
  vcgpAlg[BigInt,
           A](participantsSet[BigInt, (List[BigInt], BigInt)](b),
               goodsList[BigInt, BigInt, BigInt](b),
               Bid2funcBid[BigInt, BigInt](b), r, n, a)

def allocationPrettyPrint[A : equal : linorder,
                           B : equal : linorder](a: set[(A, set[B])]):
      set[List[(A, List[B])]]
  =
  insert[List[(A, List[B])]](map[A, (A, List[B])]((x: A) =>
            (x, sorted_list_of_set[B](eval_rel[A, set[B]](a, x))),
           (comp[set[A], List[A],
                  set[(A, set[B])]]((aa: set[A]) => sorted_list_of_set[A](aa),
                                     (aa: set[(A, set[B])]) =>
                                       Domain[A, set[B]](aa))).apply(a)),
                              bot_set[List[(A, List[B])]])

} /* object VCG */
