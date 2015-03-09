object a {

abstract sealed class nat
final case class Nat(a: BigInt) extends nat

def integer_of_nat(x0: nat): BigInt = x0 match {
  case Nat(x) => x
}

def equal_nata(m: nat, n: nat): Boolean = integer_of_nat(m) == integer_of_nat(n)

trait equal[A] {
  val `a.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`a.equal`(a, b)

implicit def equal_nat: equal[nat] = new equal[nat] {
  val `a.equal` = (a: nat, b: nat) => equal_nata(a, b)
}

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

def sgn_integer(k: BigInt): BigInt =
  (if (k == BigInt(0)) BigInt(0)
    else (if (k < BigInt(0)) BigInt(- 1) else BigInt(1)))

def abs_integer(k: BigInt): BigInt = (if (k < BigInt(0)) (- k) else k)

def apsnd[A, B, C](f: A => B, x1: (C, A)): (C, B) = (f, x1) match {
  case (f, (x, y)) => (x, f(y))
}

def comp[A, B, C](f: A => B, g: C => A): C => B = (x: C) => f(g(x))

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

def snd[A, B](x0: (A, B)): B = x0 match {
  case (x1, x2) => x2
}

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

trait ord[A] {
  val `a.less_eq`: (A, A) => Boolean
  val `a.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`a.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`a.less`(a, b)

def max[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) b else a)

implicit def ord_integer: ord[BigInt] = new ord[BigInt] {
  val `a.less_eq` = (a: BigInt, b: BigInt) => a <= b
  val `a.less` = (a: BigInt, b: BigInt) => a < b
}

def nat_of_integer(k: BigInt): nat = Nat(max[BigInt](BigInt(0), k))

def zero_nata: nat = Nat(BigInt(0))

def one_nat: nat = Nat(BigInt(1))

abstract sealed class nibble
final case class Nibble0() extends nibble
final case class Nibble1() extends nibble
final case class Nibble2() extends nibble
final case class Nibble3() extends nibble
final case class Nibble4() extends nibble
final case class Nibble5() extends nibble
final case class Nibble6() extends nibble
final case class Nibble7() extends nibble
final case class Nibble8() extends nibble
final case class Nibble9() extends nibble
final case class NibbleA() extends nibble
final case class NibbleB() extends nibble
final case class NibbleC() extends nibble
final case class NibbleD() extends nibble
final case class NibbleE() extends nibble
final case class NibbleF() extends nibble

def digit2string(n: nat): List[Char] =
  (if (equal_nata(n, zero_nata)) List('0')
    else (if (equal_nata(n, one_nat)) List('1')
           else (if (equal_nata(n, nat_of_integer(BigInt(2)))) List('2')
                  else (if (equal_nata(n, nat_of_integer(BigInt(3)))) List('3')
                         else (if (equal_nata(n, nat_of_integer(BigInt(4))))
                                List('4')
                                else (if (equal_nata(n,
              nat_of_integer(BigInt(5))))
                                       List('5')
                                       else (if (equal_nata(n,
                     nat_of_integer(BigInt(6))))
      List('6')
      else (if (equal_nata(n, nat_of_integer(BigInt(7)))) List('7')
             else (if (equal_nata(n, nat_of_integer(BigInt(8)))) List('8')
                    else List('9'))))))))))

def less_nat(m: nat, n: nat): Boolean = integer_of_nat(m) < integer_of_nat(n)

def shows_string: (List[Char]) => (List[Char]) => List[Char] =
  (a: List[Char]) => (b: List[Char]) => a ++ b

def shows_nat(n: nat): (List[Char]) => List[Char] =
  (if (less_nat(n, nat_of_integer(BigInt(10))))
    shows_string.apply(digit2string(n))
    else comp[List[Char], List[Char],
               List[Char]](shows_nat(div_nat(n, nat_of_integer(BigInt(10)))),
                            shows_string.apply(digit2string(mod_nat(n,
                             nat_of_integer(BigInt(10)))))))

def shows_prec_nat(d: nat, n: nat): (List[Char]) => List[Char] = shows_nat(n)

def shows_between(l: (List[Char]) => List[Char], p: (List[Char]) => List[Char],
                   r: (List[Char]) => List[Char]):
      (List[Char]) => List[Char]
  =
  comp[List[Char], List[Char],
        List[Char]](l, comp[List[Char], List[Char], List[Char]](p, r))

def shows_sep[A](s: A => (List[Char]) => List[Char],
                  sep: (List[Char]) => List[Char], x2: List[A]):
      (List[Char]) => List[Char]
  =
  (s, sep, x2) match {
  case (s, sep, Nil) => shows_string.apply(Nil)
  case (s, sep, List(x)) => s(x)
  case (s, sep, x :: v :: va) =>
    comp[List[Char], List[Char],
          List[Char]](s(x),
                       comp[List[Char], List[Char],
                             List[Char]](sep, shows_sep[A](s, sep, v :: va)))
}

def nulla[A](x0: List[A]): Boolean = x0 match {
  case Nil => true
  case x :: xs => false
}

def shows_list_gen[A](elt: A => (List[Char]) => List[Char], e: List[Char],
                       l: List[Char], s: List[Char], r: List[Char],
                       xs: List[A]):
      (List[Char]) => List[Char]
  =
  (if (nulla[A](xs)) shows_string.apply(e)
    else shows_between(shows_string.apply(l),
                        shows_sep[A](elt, shows_string.apply(s), xs),
                        shows_string.apply(r)))

def shows_list_aux[A](s: A => (List[Char]) => List[Char], xs: List[A]):
      (List[Char]) => List[Char]
  =
  shows_list_gen[A](s, List('[', ']'), List('['), List(',', ' '), List(']'), xs)

def shows_list_nat: (List[nat]) => (List[Char]) => List[Char] =
  (a: List[nat]) =>
    shows_list_aux[nat]((aa: nat) => shows_prec_nat(zero_nata, aa), a)

trait show[A] {
  val `a.shows_prec`: (nat, A, List[Char]) => List[Char]
  val `a.shows_list`: (List[A], List[Char]) => List[Char]
}
def shows_prec[A](a: nat, b: A, c: List[Char])(implicit A: show[A]): List[Char]
  = A.`a.shows_prec`(a, b, c)
def shows_list[A](a: List[A], b: List[Char])(implicit A: show[A]): List[Char] =
  A.`a.shows_list`(a, b)

implicit def show_nat: show[nat] = new show[nat] {
  val `a.shows_prec` = (a: nat, b: nat, c: List[Char]) =>
    (shows_prec_nat(a, b)).apply(c)
  val `a.shows_list` = (a: List[nat], b: List[Char]) =>
    shows_list_nat.apply(a).apply(b)
}

trait zero[A] {
  val `a.zero`: A
}
def zero[A](implicit A: zero[A]): A = A.`a.zero`

implicit def zero_nat: zero[nat] = new zero[nat] {
  val `a.zero` = zero_nata
}

def less_eq_nat(m: nat, n: nat): Boolean =
  integer_of_nat(m) <= integer_of_nat(n)

implicit def ord_nat: ord[nat] = new ord[nat] {
  val `a.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `a.less` = (a: nat, b: nat) => less_nat(a, b)
}

trait preorder[A] extends ord[A] {
}

trait order[A] extends preorder[A] {
}

implicit def preorder_nat: preorder[nat] = new preorder[nat] {
  val `a.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `a.less` = (a: nat, b: nat) => less_nat(a, b)
}

implicit def order_nat: order[nat] = new order[nat] {
  val `a.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `a.less` = (a: nat, b: nat) => less_nat(a, b)
}

trait linorder[A] extends order[A] {
}

implicit def linorder_nat: linorder[nat] = new linorder[nat] {
  val `a.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `a.less` = (a: nat, b: nat) => less_nat(a, b)
}

def rec_bool[A](f1: A, f2: A, x2: Boolean): A = (f1, f2, x2) match {
  case (f1, f2, true) => f1
  case (f1, f2, false) => f2
}

def shows_prec_bool: nat => Boolean => (List[Char]) => List[Char] =
  (_: nat) =>
    (a: Boolean) =>
      rec_bool[(List[Char]) =>
                 List[Char]]((aa: List[Char]) => List('T', 'r', 'u', 'e') ++ aa,
                              (aa: List[Char]) =>
                                List('F', 'a', 'l', 's', 'e') ++ aa,
                              a)

def shows_list_bool: (List[Boolean]) => (List[Char]) => List[Char] =
  (a: List[Boolean]) =>
    shows_list_aux[Boolean](shows_prec_bool.apply(zero_nata), a)

implicit def show_bool: show[Boolean] = new show[Boolean] {
  val `a.shows_prec` = (a: nat, b: Boolean, c: List[Char]) =>
    shows_prec_bool.apply(a).apply(b).apply(c)
  val `a.shows_list` = (a: List[Boolean], b: List[Char]) =>
    shows_list_bool.apply(a).apply(b)
}

abstract sealed class set[A]
final case class seta[A](a: List[A]) extends set[A]
final case class coset[A](a: List[A]) extends set[A]

abstract sealed class llist[A]
final case class LNil[A]() extends llist[A]
final case class LCons[A](a: A, b: llist[A]) extends llist[A]

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

def plus_nat(m: nat, n: nat): nat = Nat(integer_of_nat(m) + integer_of_nat(n))

def Suc(n: nat): nat = plus_nat(n, one_nat)

def top_set[A]: set[A] = coset[A](Nil)

def filter[A](p: A => Boolean, x1: List[A]): List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x :: xs) => (if (p(x)) x :: filter[A](p, xs) else filter[A](p, xs))
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

def remove[A : equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, coset(xs)) => coset[A](inserta[A](x, xs))
  case (x, seta(xs)) => seta[A](removeAll[A](x, xs))
}

def member[A : equal](x: A, xa1: set[A]): Boolean = (x, xa1) match {
  case (x, coset(xs)) => ! (membera[A](xs, x))
  case (x, seta(xs)) => membera[A](xs, x)
}

def fold[A, B](f: A => B => B, x1: List[A], s: B): B = (f, x1, s) match {
  case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
  case (f, Nil, s) => s
}

def inf_set[A : equal](a: set[A], x1: set[A]): set[A] = (a, x1) match {
  case (a, coset(xs)) =>
    fold[A, set[A]]((aa: A) => (b: set[A]) => remove[A](aa, b), xs, a)
  case (a, seta(xs)) => seta[A](filter[A]((x: A) => member[A](x, a), xs))
}

def Inf_set[A : equal](x0: set[set[A]]): set[A] = x0 match {
  case seta(xs) =>
    fold[set[A],
          set[A]]((a: set[A]) => (b: set[A]) => inf_set[A](a, b), xs,
                   top_set[A])
}

def bot_set[A]: set[A] = seta[A](Nil)

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

def the_elem[A](x0: set[A]): A = x0 match {
  case seta(List(x)) => x
}

def insert[A : equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, coset(xs)) => coset[A](removeAll[A](x, xs))
  case (x, seta(xs)) => seta[A](inserta[A](x, xs))
}

def eval_rel[A : equal, B](r: set[(A, B)], a: A): B =
  the_elem[B](Image[A, B](r, insert[A](a, bot_set[A])))

def equal_bool(p: Boolean, pa: Boolean): Boolean = (p, pa) match {
  case (p, true) => p
  case (p, false) => ! p
  case (true, p) => p
  case (false, p) => ! p
}

def gen_length[A](n: nat, x1: List[A]): nat = (n, x1) match {
  case (n, x :: xs) => gen_length[A](Suc(n), xs)
  case (n, Nil) => n
}

def size_list[A]: (List[A]) => nat = (a: List[A]) => gen_length[A](zero_nata, a)

def maps[A, B](f: A => List[B], x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) ++ maps[A, B](f, xs)
}

def upt(i: nat, j: nat): List[nat] =
  (if (less_nat(i, j)) i :: upt(Suc(i), j) else Nil)

def minus_nat(m: nat, n: nat): nat =
  Nat(max[BigInt](BigInt(0), integer_of_nat(m) - integer_of_nat(n)))

def nth[A](x0: List[A], n: nat): A = (x0, n) match {
  case (x :: xs, n) =>
    (if (equal_nata(n, zero_nata)) x else nth[A](xs, minus_nat(n, one_nat)))
}

def filterpositions2[A](p: A => Boolean, l: List[A]): List[nat] =
  maps[nat, nat]((n: nat) => (if (p(nth[A](l, n))) List(n) else Nil),
                  upt(zero_nata, size_list[A].apply(l)))

def map[A, B](fi: A => B, x1: List[A]): List[B] = (fi, x1) match {
  case (fi, Nil) => Nil
  case (fi, x21a :: x22) => fi(x21a) :: map[A, B](fi, x22)
}

def take[A](n: nat, x1: List[A]): List[A] = (n, x1) match {
  case (n, Nil) => Nil
  case (n, x :: xs) =>
    (if (equal_nata(n, zero_nata)) Nil
      else x :: take[A](minus_nat(n, one_nat), xs))
}

def drop[A](n: nat, x1: List[A]): List[A] = (n, x1) match {
  case (n, Nil) => Nil
  case (n, x :: xs) =>
    (if (equal_nata(n, zero_nata)) x :: xs
      else drop[A](minus_nat(n, one_nat), xs))
}

def zip[A, B](xs: List[A], ys: List[B]): List[(A, B)] = (xs, ys) match {
  case (x :: xs, y :: ys) => (x, y) :: zip[A, B](xs, ys)
  case (xs, Nil) => Nil
  case (Nil, ys) => Nil
}

def sametomyleft[A : zero : equal](l: List[A]): List[Boolean] =
  take[Boolean](size_list[A].apply(l),
                 false ::
                   map[(A, A),
                        Boolean]((x: (A, A)) =>
                                   eq[A](fst[A, A](x), snd[A, A](x)),
                                  drop[(A,
 A)](one_nat, zip[A, A](l, zero[A] :: l))))

def stopauctionat[A : zero : equal](l: List[A]): List[nat] =
  filterpositions2[Boolean]((x: Boolean) => equal_bool(x, true),
                             sametomyleft[A](l))

def image[A, B](f: A => B, x1: set[A]): set[B] = (f, x1) match {
  case (f, seta(xs)) => seta[B](map[A, B](f, xs))
}

def Domain[A, B](r: set[(A, B)]): set[A] =
  image[(A, B), A]((a: (A, B)) => fst[A, B](a), r)

def stops[A : equal, B, C : zero : equal](b: set[(A, List[(B, C)])]): set[nat] =
  Inf_set[nat](image[A, set[nat]]((i: A) =>
                                    seta[nat](stopauctionat[C](map[(B, C),
                            C]((a: (B, C)) => snd[B, C](a),
                                eval_rel[A, List[(B, C)]](b, i)))),
                                   Domain[A, List[(B, C)]](b)))

def hd[A](x0: List[A]): A = x0 match {
  case x21 :: x22 => x21
}

def tl[A](x0: List[A]): List[A] = x0 match {
  case Nil => Nil
  case x21 :: x22 => x22
}

def sublist[A](xs: List[A], a: set[nat]): List[A] =
  map_filter[(A, nat),
              A]((x: (A, nat)) =>
                   (if (member[nat](snd[A, nat](x), a)) Some[A](fst[A, nat](x))
                     else None),
                  zip[A, nat](xs, upt(zero_nata, size_list[A].apply(xs))))

def shows_prec_list[A : show](d: nat, l: List[A]): (List[Char]) => List[Char] =
  (a: List[Char]) => shows_list[A](l, a)

def times_nat(m: nat, n: nat): nat = Nat(integer_of_nat(m) * integer_of_nat(n))

def Max[A : linorder](x0: set[A]): A = x0 match {
  case seta(x :: xs) => fold[A, A]((a: A) => (b: A) => max[A](a, b), xs, x)
}

def maxpositions[A : linorder](l: List[A]): List[nat] =
  filterpositions2[A]((a: A) => less_eq[A](Max[A](seta[A](l)), a), l)

def override_on[A : equal, B](f: A => B, g: A => B, a: set[A]): A => B =
  (aa: A) => (if (member[A](aa, a)) g(aa) else f(aa))

def Range[A, B](r: set[(A, B)]): set[B] =
  image[(A, B), B]((a: (A, B)) => snd[A, B](a), r)

def replicate[A](n: nat, x: A): List[A] =
  (if (equal_nata(n, zero_nata)) Nil
    else x :: replicate[A](minus_nat(n, one_nat), x))

def livelinessList[A : equal, B, C : zero : equal](b: set[(A, List[(B, C)])]):
      List[Boolean]
  =
  true ::
    map[nat, Boolean](override_on[nat, Boolean]((a: nat) =>
          nth[Boolean](replicate[Boolean](Max[nat](image[List[(B, C)],
                  nat](size_list[(B, C)], Range[A, List[(B, C)]](b))),
   true),
                        a),
         (_: nat) => false, stops[A, B, C](b)),
                       upt(zero_nata,
                            size_list[Boolean].apply(replicate[Boolean](Max[nat](image[List[(B,
              C)],
        nat](size_list[(B, C)], Range[A, List[(B, C)]](b))),
                                 true))))

def graph[A, B](x: set[A], f: A => B): set[(A, B)] =
  image[A, (A, B)]((xa: A) => (xa, f(xa)), x)

def message(l: List[nat]): List[Char] =
  List('C', 'u', 'r', 'r', 'e', 'n', 't', ' ', 'w', 'i', 'n', 'n', 'e', 'r',
        ':', ' ') ++
    ((shows_prec_list[nat](zero_nata,
                            maxpositions[nat](sublist[nat](l,
                    seta[nat](upt(Suc(times_nat(div_nat(minus_nat(size_list[nat].apply(l),
                           nat_of_integer(BigInt(2))),
                 nth[nat](l, zero_nata)),
         nth[nat](l, zero_nata))),
                                   Suc(times_nat(Suc(div_nat(minus_nat(size_list[nat].apply(l),
                                nat_of_integer(BigInt(2))),
                      nth[nat](l, zero_nata))),
          nth[nat](l, zero_nata))))))))).apply(Nil) ++
      (List('L', 'i', 'v', 'e', 'l', 'i', 'n', 'e', 's', 's', ':', ' ') ++
        ((shows_prec_list[Boolean](zero_nata,
                                    livelinessList[nat, Boolean,
            nat](graph[nat, List[(Boolean,
                                   nat)]](seta[nat](upt(zero_nata,
                 size_list[List[(Boolean,
                                  nat)]].apply(map[nat,
            List[(Boolean,
                   nat)]]((i: nat) =>
                            zip[Boolean,
                                 nat](replicate[Boolean](plus_nat(div_nat(minus_nat(size_list[nat].apply(l),
     nat_of_integer(BigInt(2))),
                                   nth[nat](l, zero_nata)),
                           one_nat),
                  true),
                                       sublist[nat](l,
             image[nat, nat]((a: nat) => plus_nat(Suc(i), a),
                              image[nat, nat]((a: nat) =>
        times_nat(nth[nat](l, zero_nata), a),
       seta[nat](upt(zero_nata,
                      Suc(div_nat(minus_nat(size_list[nat].apply(l),
     nat_of_integer(BigInt(2))),
                                   nth[nat](l, zero_nata))))))))),
                           upt(zero_nata, nth[nat](l, zero_nata)))))),
   (a: nat) =>
     nth[List[(Boolean,
                nat)]](map[nat, List[(Boolean,
                                       nat)]]((i: nat) =>
        zip[Boolean,
             nat](replicate[Boolean](plus_nat(div_nat(minus_nat(size_list[nat].apply(l),
                         nat_of_integer(BigInt(2))),
               nth[nat](l, zero_nata)),
       one_nat),
                                      true),
                   sublist[nat](l, image[nat,
  nat]((aa: nat) => plus_nat(Suc(i), aa),
        image[nat, nat]((aa: nat) => times_nat(nth[nat](l, zero_nata), aa),
                         seta[nat](upt(zero_nata,
Suc(div_nat(minus_nat(size_list[nat].apply(l), nat_of_integer(BigInt(2))),
             nth[nat](l, zero_nata))))))))),
       upt(zero_nata, nth[nat](l, zero_nata))),
                        a))))).apply(Nil) ++
          (List('\12') ++
            (List('N', 'e', 'x', 't', ',', ' ', 'i', 'n', 'p', 'u', 't', ' ',
                   'b', 'i', 'd', ' ', 'f', 'o', 'r', ' ', 'r', 'o', 'u', 'n',
                   'd', ' ') ++
              ((shows_prec_nat(zero_nata,
                                div_nat(minus_nat(size_list[nat].apply(l),
           one_nat),
 nth[nat](l, zero_nata)))).apply(Nil) ++
                (List(',', ' ', 'p', 'a', 'r', 't', 'i', 'c', 'i', 'p', 'a',
                       'n', 't', ' ') ++
                  (shows_prec_nat(zero_nata,
                                   mod_nat(minus_nat(size_list[nat].apply(l),
              one_nat),
    nth[nat](l, zero_nata)))).apply(Nil))))))))

def iterates[A](f: A => A, x: A): llist[A] = LCons[A](x, iterates[A](f, f(x)))

def evaluateMe(input: (List[BigInt]) => List[BigInt],
                output: ((List[BigInt], String)) => List[BigInt]):
      (List[BigInt], llist[List[BigInt]])
  =
  (output((Nil, ("" ++
                  List('S', 't', 'a', 'r', 't', 'i', 'n', 'g', '\12', 'I', 'n',
                        'p', 'u', 't', ' ', 't', 'h', 'e', ' ', 'n', 'u', 'm',
                        'b', 'e', 'r', ' ', 'o', 'f', ' ', 'b', 'i', 'd', 'd',
                        'e', 'r', 's', ':')))),
    iterates[List[BigInt]](comp[List[BigInt], List[BigInt],
                                 List[BigInt]](comp[List[BigInt], List[BigInt],
             List[BigInt]](comp[(List[BigInt], String), List[BigInt],
                                 List[BigInt]](output,
        (x: List[BigInt]) =>
          (x, ("" ++
                (message(map[BigInt,
                              nat]((a: BigInt) => nat_of_integer(a), x)))))),
                            (l: List[BigInt]) =>
                              tl[BigInt](l) ++ List(hd[BigInt](l))),
        input),
                            Nil))

                            
                            
def untrustedInput(n:List[BigInt]) : List[BigInt] = {
	val x=readInt; //NB: We rely on the user typing an integer, here! This is a naive but simple approach.
	return (x::n);
}

def untrustedOutput(x: (List[BigInt], String)) : List[BigInt] = {
	println(snd (x));
	return (fst (x));
}

def main(args: Array[String]) {
	val x=evaluateMe(untrustedInput, untrustedOutput);
}

def printWithSpace(args: BigInt): Unit = {
  print(args + " ");
}

def printListOfGoods(args: List[BigInt]): Unit = {
  args match {
       case Nil => print("");
       case head::Nil => print(head);
       case head::tail => print(head + ", "); printListOfGoods(tail);
     }
}

def printBidder(args: List[List[BigInt]]): Unit = {
    println(" Bidder: " + args.head.head);
}

def printGoods(args: List[List[BigInt]]): Unit = {
    print(" Goods:  {");
    printListOfGoods(args.tail.head);
    println("}");
}

def printBid(args: List[List[BigInt]]): Unit = {
    println(" Bid:    " + args.tail.tail.head.head);
}

def printSingleBid(args: List[List[BigInt]]): Unit = {
    printBidder(args);
    printGoods(args);
    printBid(args);
    println();
}

def printAllBids(args: List[List[List[BigInt]]]): Unit = {
    args.foreach(printSingleBid)
  }

/*def the_elem[A](x0: set[A]): A = x0 match {
  case seta(List(x)) => x
}
*/

def choice[A](x0: set[A]): A = x0 match {
  case seta(List(x)) => x
  case seta(x :: _) => x
}

def printAllocatedGoods(args: List[BigInt]): Unit = {
    printListOfGoods(args);
}

def printPrice(args: BigInt) {
}

def printAllocationAndPayment(args: (BigInt, List[BigInt])): Unit = args match {
    case (hd, tl) => print(" X_" + hd + " = {" ); 
                     printAllocatedGoods(tl);
                     print("}    payment:");
  //                   printPrice(hd);
//    println(args);
  }


def printAllocationsAndPayments(args: set[List[(BigInt, List[BigInt])]]):
   Unit = { choice(args).foreach(printAllocationAndPayment);
  }

          
def main(args: Array[String]) {
println("input bid vector:"); printAllBids(b1);
println;

println("Winning allocation and payments:"); 
printAllocationsAndPayments(example);
};


} /* object a */
