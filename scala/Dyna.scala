object Dyna {

trait equal[A] {
  val `Dyna.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`Dyna.equal`(a, b)

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

abstract sealed class nat
final case class Nat(a: BigInt) extends nat

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

abstract sealed class set[A]
final case class Set[A](a: List[A]) extends set[A]
final case class Coset[A](a: List[A]) extends set[A]

def hd[A](x0: List[A]): A = x0 match {
  case x :: xs => x
}

def integer_of_nat(x0: nat): BigInt = x0 match {
  case Nat(x) => x
}

def plus_nata(m: nat, n: nat): nat = Nat(integer_of_nat(m) + integer_of_nat(n))

def one_nata: nat = Nat(BigInt(1))

def suc(n: nat): nat = plus_nata(n, one_nata)

def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) :: map[A, B](f, xs)
}

trait ord[A] {
  val `Dyna.less_eq`: (A, A) => Boolean
  val `Dyna.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`Dyna.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`Dyna.less`(a, b)

implicit def ord_integer: ord[BigInt] = new ord[BigInt] {
  val `Dyna.less_eq` = (a: BigInt, b: BigInt) => a <= b
  val `Dyna.less` = (a: BigInt, b: BigInt) => a < b
}

def max[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) b else a)

def minus_nat(m: nat, n: nat): nat =
  Nat(max[BigInt](BigInt(0), integer_of_nat(m) - integer_of_nat(n)))

def equal_nata(m: nat, n: nat): Boolean = integer_of_nat(m) == integer_of_nat(n)

def zero_nat: nat = Nat(BigInt(0))

def nth[A](x0: List[A], n: nat): A = (x0, n) match {
  case (x :: xs, n) =>
    (if (equal_nata(n, zero_nat)) x else nth[A](xs, minus_nat(n, one_nata)))
}

def fold[A, B](f: A => B => B, x1: List[A], s: B): B = (f, x1, s) match {
  case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
  case (f, Nil, s) => s
}

def rev[A](xs: List[A]): List[A] =
  fold[A, List[A]]((a: A) => (b: List[A]) => a :: b, xs, Nil)

def less_nat(m: nat, n: nat): Boolean = integer_of_nat(m) < integer_of_nat(n)

def upt(i: nat, j: nat): List[nat] =
  (if (less_nat(i, j)) i :: upt(suc(i), j) else Nil)

def zip[A, B](xs: List[A], ys: List[B]): List[(A, B)] = (xs, ys) match {
  case (x :: xs, y :: ys) => (x, y) :: zip[A, B](xs, ys)
  case (xs, Nil) => Nil
  case (Nil, ys) => Nil
}

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

def membera[A : equal](x0: List[A], y: A): Boolean = (x0, y) match {
  case (Nil, y) => false
  case (x :: xs, y) => eq[A](x, y) || membera[A](xs, y)
}

def member[A : equal](x: A, xa1: set[A]): Boolean = (x, xa1) match {
  case (x, Coset(xs)) => ! (membera[A](xs, x))
  case (x, Set(xs)) => membera[A](xs, x)
}

def imagea[A : equal, B](r: set[(A, B)], s: set[A]): set[B] =
  map_project[(A, B),
               B]((a: (A, B)) =>
                    {
                      val (x, y): (A, B) = a;
                      (if (member[A](x, s)) Some[B](y) else None)
                    },
                   r)

def the_elem[A](x0: set[A]): A = x0 match {
  case Set(List(x)) => x
}

def bot_set[A]: set[A] = Set[A](Nil)

def removeAll[A : equal](x: A, xa1: List[A]): List[A] = (x, xa1) match {
  case (x, Nil) => Nil
  case (x, y :: xs) =>
    (if (eq[A](x, y)) removeAll[A](x, xs) else y :: removeAll[A](x, xs))
}

def inserta[A : equal](x: A, xs: List[A]): List[A] =
  (if (membera[A](xs, x)) xs else x :: xs)

def insert[A : equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, Coset(xs)) => Coset[A](removeAll[A](x, xs))
  case (x, Set(xs)) => Set[A](inserta[A](x, xs))
}

def eval_rel[A : equal, B](r: set[(A, B)], a: A): B =
  the_elem[B](imagea[A, B](r, insert[A](a, bot_set[A])))

def top_set[A]: set[A] = Coset[A](Nil)

def filtera[A](p: A => Boolean, x1: List[A]): List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x :: xs) => (if (p(x)) x :: filtera[A](p, xs) else filtera[A](p, xs))
}

def remove[A : equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, Coset(xs)) => Coset[A](inserta[A](x, xs))
  case (x, Set(xs)) => Set[A](removeAll[A](x, xs))
}

def inf_set[A : equal](a: set[A], x1: set[A]): set[A] = (a, x1) match {
  case (a, Coset(xs)) =>
    fold[A, set[A]]((aa: A) => (b: set[A]) => remove[A](aa, b), xs, a)
  case (a, Set(xs)) => Set[A](filtera[A]((x: A) => member[A](x, a), xs))
}

def inf_seta[A : equal](x0: set[set[A]]): set[A] = x0 match {
  case Set(xs) =>
    fold[set[A],
          set[A]]((a: set[A]) => (b: set[A]) => inf_set[A](a, b), xs,
                   top_set[A])
}

trait preorder[A] extends ord[A] {
}

trait order[A] extends preorder[A] {
}

trait linorder[A] extends order[A] {
}

def min[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) a else b)

def mina[A : linorder](x0: set[A]): A = x0 match {
  case Set(x :: xs) => fold[A, A]((a: A) => (b: A) => min[A](a, b), xs, x)
}

def snd[A, B](x0: (A, B)): B = x0 match {
  case (a, b) => b
}

def gen_length[A](n: nat, x1: List[A]): nat = (n, x1) match {
  case (n, x :: xs) => gen_length[A](suc(n), xs)
  case (n, Nil) => n
}

def size_list[A]: (List[A]) => nat = (a: List[A]) => gen_length[A](zero_nat, a)

def maps[A, B](f: A => List[B], x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) ++ maps[A, B](f, xs)
}

def filterpositions2[A](p: A => Boolean, l: List[A]): List[nat] =
  maps[nat, nat]((n: nat) => (if (p(nth[A](l, n))) List(n) else Nil),
                  upt(zero_nat, size_list[A].apply(l)))

def equal_boola(p: Boolean, pa: Boolean): Boolean = (p, pa) match {
  case (p, true) => p
  case (p, false) => ! p
  case (true, p) => p
  case (false, p) => ! p
}

def fst[A, B](x0: (A, B)): A = x0 match {
  case (a, b) => a
}

trait plus[A] {
  val `Dyna.plus`: (A, A) => A
}
def plus[A](a: A, b: A)(implicit A: plus[A]): A = A.`Dyna.plus`(a, b)

trait one[A] {
  val `Dyna.one`: A
}
def one[A](implicit A: one[A]): A = A.`Dyna.one`

def sametomyleft[A : one : plus : equal](l: List[A]): List[Boolean] =
  map[(A, A),
       Boolean]((x: (A, A)) => eq[A](fst[A, A](x), snd[A, A](x)),
                 zip[A, A](l, plus[A](hd[A](l), one[A]) :: l))

def stopauctionat[A : one : plus : equal](l: List[A]): List[nat] =
  filterpositions2[Boolean]((x: Boolean) => equal_boola(x, true),
                             sametomyleft[A](l))

def image[A, B](f: A => B, x1: set[A]): set[B] = (f, x1) match {
  case (f, Set(xs)) => Set[B](map[A, B](f, xs))
}

def domain[A, B](r: set[(A, B)]): set[A] =
  image[(A, B), A]((a: (A, B)) => fst[A, B](a), r)

def less_eq_nat(m: nat, n: nat): Boolean =
  integer_of_nat(m) <= integer_of_nat(n)

implicit def ord_nat: ord[nat] = new ord[nat] {
  val `Dyna.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `Dyna.less` = (a: nat, b: nat) => less_nat(a, b)
}

implicit def preorder_nat: preorder[nat] = new preorder[nat] {
  val `Dyna.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `Dyna.less` = (a: nat, b: nat) => less_nat(a, b)
}

implicit def order_nat: order[nat] = new order[nat] {
  val `Dyna.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `Dyna.less` = (a: nat, b: nat) => less_nat(a, b)
}

implicit def linorder_nat: linorder[nat] = new linorder[nat] {
  val `Dyna.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `Dyna.less` = (a: nat, b: nat) => less_nat(a, b)
}

implicit def equal_nat: equal[nat] = new equal[nat] {
  val `Dyna.equal` = (a: nat, b: nat) => equal_nata(a, b)
}

def stopat[A : equal, B, C : one : plus : equal](b: set[(A, List[(B, C)])]):
      nat =
  mina[nat](inf_seta[nat](image[A, set[nat]]((i: A) =>
       Set[nat](stopauctionat[C](map[(B, C),
                                      C]((a: (B, C)) => snd[B, C](a),
  eval_rel[A, List[(B, C)]](b, i)))),
      domain[A, List[(B, C)]](b))))

def toFunction[A : equal, B](r: set[(A, B)]): A => B =
  (a: A) => eval_rel[A, B](r, a)

def graph[A, B](x: set[A], f: A => B): set[(A, B)] =
  image[A, (A, B)]((xa: A) => (xa, f(xa)), x)

def equal_proda[A : equal, B : equal](x0: (A, B), x1: (A, B)): Boolean =
  (x0, x1) match {
  case ((aa, ba), (a, b)) => eq[A](aa, a) && eq[B](ba, b)
}

implicit def equal_prod[A : equal, B : equal]: equal[(A, B)] = new equal[(A, B)]
  {
  val `Dyna.equal` = (a: (A, B), b: (A, B)) => equal_proda[A, B](a, b)
}

implicit def equal_bool: equal[Boolean] = new equal[Boolean] {
  val `Dyna.equal` = (a: Boolean, b: Boolean) => equal_boola(a, b)
}

def liveliness[A, B : ord](prev: (A, B), cur: (Boolean, B)): Boolean =
  (if (less[B](snd[Boolean, B](cur), snd[A, B](prev)) ||
         ! (fst[Boolean, B](cur)))
    false else true)

def lastvalidbid[A, B : ord](prev: (A, B), cur: (Boolean, B)): B =
  (if (liveliness[A, B](prev, cur)) snd[Boolean, B](cur) else snd[A, B](prev))

def amendedbidlist(x0: List[(Boolean, nat)]): List[(Boolean, nat)] = x0 match {
  case Nil => List((true, zero_nat))
  case x :: b =>
    (liveliness[Boolean,
                 nat](nth[(Boolean, nat)](amendedbidlist(b), zero_nat), x),
      lastvalidbid[Boolean,
                    nat](nth[(Boolean, nat)](amendedbidlist(b), zero_nat),
                          x)) ::
      amendedbidlist(b)
}

def relcomp[A, B : equal, C](x0: set[(A, B)], x1: set[(B, C)]): set[(A, C)] =
  (x0, x1) match {
  case (Set(xys), Set(yzs)) =>
    Set[(A, C)](maps[(A, B),
                      (A, C)]((xy: (A, B)) =>
                                maps[(B, C),
                                      (A,
C)]((yz: (B, C)) =>
      (if (eq[B](snd[A, B](xy), fst[B, C](yz)))
        List((fst[A, B](xy), snd[B, C](yz))) else Nil),
     yzs),
                               xys))
}

def maxa[A : linorder](x0: set[A]): A = x0 match {
  case Set(x :: xs) => fold[A, A]((a: A) => (b: A) => max[A](a, b), xs, x)
}

def filter[A](p: A => Boolean, x1: set[A]): set[A] = (p, x1) match {
  case (p, Set(xs)) => Set[A](filtera[A](p, xs))
}

def arg_max[A, B : equal : linorder](f: A => B, a: set[A]): set[A] =
  filter[A]((x: A) => eq[B](f(x), maxa[B](image[A, B](f, a))), a)

def range[A, B](r: set[(A, B)]): set[B] =
  image[(A, B), B]((a: (A, B)) => snd[A, B](a), r)

def equal_lista[A : equal](x0: List[A], x1: List[A]): Boolean = (x0, x1) match {
  case (a :: list, Nil) => false
  case (Nil, a :: list) => false
  case (aa :: lista, a :: list) => eq[A](aa, a) && equal_lista[A](lista, list)
  case (Nil, Nil) => true
}

implicit def equal_list[A : equal]: equal[List[A]] = new equal[List[A]] {
  val `Dyna.equal` = (a: List[A], b: List[A]) => equal_lista[A](a, b)
}

implicit def plus_nat: plus[nat] = new plus[nat] {
  val `Dyna.plus` = (a: nat, b: nat) => plus_nata(a, b)
}

implicit def one_nat: one[nat] = new one[nat] {
  val `Dyna.one` = one_nata
}

def winner(b: set[(nat, List[(Boolean, nat)])]): set[nat] =
  arg_max[nat, nat](toFunction[nat, nat](relcomp[nat, List[(Boolean, nat)],
          nat](relcomp[nat, List[(Boolean, nat)],
                        List[(Boolean,
                               nat)]](b, graph[List[(Boolean, nat)],
        List[(Boolean,
               nat)]](range[nat, List[(Boolean, nat)]](b),
                       (ba: List[(Boolean, nat)]) =>
                         rev[(Boolean,
                               nat)](amendedbidlist(rev[(Boolean, nat)](ba))))),
                graph[List[(Boolean, nat)],
                       nat](range[nat, List[(Boolean,
      nat)]](relcomp[nat, List[(Boolean, nat)],
                      List[(Boolean,
                             nat)]](b, graph[List[(Boolean, nat)],
      List[(Boolean,
             nat)]](range[nat, List[(Boolean, nat)]](b),
                     (ba: List[(Boolean, nat)]) =>
                       rev[(Boolean,
                             nat)](amendedbidlist(rev[(Boolean, nat)](ba)))))),
                             (x: List[(Boolean, nat)]) =>
                               snd[Boolean,
                                    nat](nth[(Boolean,
       nat)](x, stopat[nat, Boolean,
                        nat](relcomp[nat, List[(Boolean, nat)],
                                      List[(Boolean,
     nat)]](b, graph[List[(Boolean, nat)],
                      List[(Boolean,
                             nat)]](range[nat, List[(Boolean, nat)]](b),
                                     (ba: List[(Boolean, nat)]) =>
                                       rev[(Boolean,
     nat)](amendedbidlist(rev[(Boolean, nat)](ba))))))))))),
                     domain[nat, nat](relcomp[nat, List[(Boolean, nat)],
       nat](relcomp[nat, List[(Boolean, nat)],
                     List[(Boolean,
                            nat)]](b, graph[List[(Boolean, nat)],
     List[(Boolean,
            nat)]](range[nat, List[(Boolean, nat)]](b),
                    (ba: List[(Boolean, nat)]) =>
                      rev[(Boolean,
                            nat)](amendedbidlist(rev[(Boolean, nat)](ba))))),
             graph[List[(Boolean, nat)],
                    nat](range[nat, List[(Boolean,
   nat)]](relcomp[nat, List[(Boolean, nat)],
                   List[(Boolean,
                          nat)]](b, graph[List[(Boolean, nat)],
   List[(Boolean,
          nat)]](range[nat, List[(Boolean, nat)]](b),
                  (ba: List[(Boolean, nat)]) =>
                    rev[(Boolean,
                          nat)](amendedbidlist(rev[(Boolean, nat)](ba)))))),
                          (x: List[(Boolean, nat)]) =>
                            snd[Boolean,
                                 nat](nth[(Boolean,
    nat)](x, stopat[nat, Boolean,
                     nat](relcomp[nat, List[(Boolean, nat)],
                                   List[(Boolean,
  nat)]](b, graph[List[(Boolean, nat)],
                   List[(Boolean,
                          nat)]](range[nat, List[(Boolean, nat)]](b),
                                  (ba: List[(Boolean, nat)]) =>
                                    rev[(Boolean,
  nat)](amendedbidlist(rev[(Boolean, nat)](ba))))))))))))

def nat_of_integer(k: BigInt): nat = Nat(max[BigInt](BigInt(0), k))

def replicate[A](n: nat, x: A): List[A] =
  (if (equal_nata(n, zero_nat)) Nil
    else x :: replicate[A](minus_nat(n, one_nata), x))

def example: set[(nat, List[(Boolean, nat)])] =
  insert[(nat, List[(Boolean,
                      nat)])]((nat_of_integer(BigInt(10)),
                                zip[Boolean,
                                     nat](replicate[Boolean](nat_of_integer(BigInt(10)),
                      true),
   List(one_nata, nat_of_integer(BigInt(4)), nat_of_integer(BigInt(4)),
         nat_of_integer(BigInt(5)), nat_of_integer(BigInt(6)),
         nat_of_integer(BigInt(6)), nat_of_integer(BigInt(6)),
         nat_of_integer(BigInt(6)), nat_of_integer(BigInt(6)),
         nat_of_integer(BigInt(6))))),
                               insert[(nat,
List[(Boolean,
       nat)])]((nat_of_integer(BigInt(20)),
                 zip[Boolean,
                      nat](replicate[Boolean](nat_of_integer(BigInt(10)), true),
                            List(nat_of_integer(BigInt(5)),
                                  nat_of_integer(BigInt(4)),
                                  nat_of_integer(BigInt(7)),
                                  nat_of_integer(BigInt(7)),
                                  nat_of_integer(BigInt(9)),
                                  nat_of_integer(BigInt(9)),
                                  nat_of_integer(BigInt(9)),
                                  nat_of_integer(BigInt(9)),
                                  nat_of_integer(BigInt(9)),
                                  nat_of_integer(BigInt(9))))),
                bot_set[(nat, List[(Boolean, nat)])]))

} /* object Dyna */
