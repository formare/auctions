object Dyna {

trait equal[A] {
  val `Dyna.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`Dyna.equal`(a, b)

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

def equal_proda[A : equal, B : equal](x0: (A, B), x1: (A, B)): Boolean =
  (x0, x1) match {
  case ((aa, ba), (a, b)) => eq[A](aa, a) && eq[B](ba, b)
}

implicit def equal_prod[A : equal, B : equal]: equal[(A, B)] = new equal[(A, B)]
  {
  val `Dyna.equal` = (a: (A, B), b: (A, B)) => equal_proda[A, B](a, b)
}

def equal_boola(p: Boolean, pa: Boolean): Boolean = (p, pa) match {
  case (p, true) => p
  case (p, false) => ! p
  case (true, p) => p
  case (false, p) => ! p
}

implicit def equal_bool: equal[Boolean] = new equal[Boolean] {
  val `Dyna.equal` = (a: Boolean, b: Boolean) => equal_boola(a, b)
}

abstract sealed class nat
final case class Nat(a: BigInt) extends nat

def integer_of_nat(x0: nat): BigInt = x0 match {
  case Nat(x) => x
}

def plus_nata(m: nat, n: nat): nat = Nat(integer_of_nat(m) + integer_of_nat(n))

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

def one_nata: nat = Nat(BigInt(1))

def suc(n: nat): nat = plus_nata(n, one_nata)

def gen_length[A](n: nat, x1: List[A]): nat = (n, x1) match {
  case (n, x :: xs) => gen_length[A](suc(n), xs)
  case (n, Nil) => n
}

def zero_nat: nat = Nat(BigInt(0))

def size_list[A]: (List[A]) => nat = (a: List[A]) => gen_length[A](zero_nat, a)

def membera[A : equal](x0: List[A], y: A): Boolean = (x0, y) match {
  case (Nil, y) => false
  case (x :: xs, y) => eq[A](x, y) || membera[A](xs, y)
}

def remdups[A : equal](x0: List[A]): List[A] = x0 match {
  case Nil => Nil
  case x :: xs =>
    (if (membera[A](xs, x)) remdups[A](xs) else x :: remdups[A](xs))
}

abstract sealed class set[A]
final case class Set[A](a: List[A]) extends set[A]
final case class Coset[A](a: List[A]) extends set[A]

def card[A : equal](x0: set[A]): nat = x0 match {
  case Set(xs) => size_list[A].apply(remdups[A](xs))
}

def equal_lista[A : equal](x0: List[A], x1: List[A]): Boolean = (x0, x1) match {
  case (a :: list, Nil) => false
  case (Nil, a :: list) => false
  case (aa :: lista, a :: list) => eq[A](aa, a) && equal_lista[A](lista, list)
  case (Nil, Nil) => true
}

implicit def equal_list[A : equal]: equal[List[A]] = new equal[List[A]] {
  val `Dyna.equal` = (a: List[A], b: List[A]) => equal_lista[A](a, b)
}

def equal_nata(m: nat, n: nat): Boolean = integer_of_nat(m) == integer_of_nat(n)

implicit def equal_nat: equal[nat] = new equal[nat] {
  val `Dyna.equal` = (a: nat, b: nat) => equal_nata(a, b)
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

def bidMatrix: set[(nat, List[(Boolean, nat)])] =
  insert[(nat, List[(Boolean,
                      nat)])]((zero_nat, Nil),
                               insert[(nat,
List[(Boolean, nat)])]((one_nata, Nil), bot_set[(nat, List[(Boolean, nat)])]))

def n: nat = card[(nat, List[(Boolean, nat)])](bidMatrix)

trait ord[A] {
  val `Dyna.less_eq`: (A, A) => Boolean
  val `Dyna.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`Dyna.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`Dyna.less`(a, b)

trait preorder[A] extends ord[A] {
}

trait order[A] extends preorder[A] {
}

trait linorder[A] extends order[A] {
}

def max[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) b else a)

def fold[A, B](f: A => B => B, x1: List[A], s: B): B = (f, x1, s) match {
  case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
  case (f, Nil, s) => s
}

def maxa[A : linorder](x0: set[A]): A = x0 match {
  case Set(x :: xs) => fold[A, A]((a: A) => (b: A) => max[A](a, b), xs, x)
}

implicit def ord_integer: ord[BigInt] = new ord[BigInt] {
  val `Dyna.less_eq` = (a: BigInt, b: BigInt) => a <= b
  val `Dyna.less` = (a: BigInt, b: BigInt) => a < b
}

def minus_nat(m: nat, n: nat): nat =
  Nat(max[BigInt](BigInt(0), integer_of_nat(m) - integer_of_nat(n)))

def list_update[A](x0: List[A], i: nat, y: A): List[A] = (x0, i, y) match {
  case (Nil, i, y) => Nil
  case (x :: xs, i, y) =>
    (if (equal_nata(i, zero_nat)) y :: xs
      else x :: list_update[A](xs, minus_nat(i, one_nata), y))
}

def less_eq_nat(m: nat, n: nat): Boolean =
  integer_of_nat(m) <= integer_of_nat(n)

def less_nat(m: nat, n: nat): Boolean = integer_of_nat(m) < integer_of_nat(n)

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

def snd[A, B](x0: (A, B)): B = x0 match {
  case (a, b) => b
}

def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) :: map[A, B](f, xs)
}

def image[A, B](f: A => B, x1: set[A]): set[B] = (f, x1) match {
  case (f, Set(xs)) => Set[B](map[A, B](f, xs))
}

def range[A, B](r: set[(A, B)]): set[B] =
  image[(A, B), B]((a: (A, B)) => snd[A, B](a), r)

def replicate[A](n: nat, x: A): List[A] =
  (if (equal_nata(n, zero_nat)) Nil
    else x :: replicate[A](minus_nat(n, one_nata), x))

trait plus[A] {
  val `Dyna.plus`: (A, A) => A
}
def plus[A](a: A, b: A)(implicit A: plus[A]): A = A.`Dyna.plus`(a, b)

implicit def plus_nat: plus[nat] = new plus[nat] {
  val `Dyna.plus` = (a: nat, b: nat) => plus_nata(a, b)
}

trait one[A] {
  val `Dyna.one`: A
}
def one[A](implicit A: one[A]): A = A.`Dyna.one`

implicit def one_nat: one[nat] = new one[nat] {
  val `Dyna.one` = one_nata
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

def eval_rel[A : equal, B](r: set[(A, B)], a: A): B =
  the_elem[B](imagea[A, B](r, insert[A](a, bot_set[A])))

def top_set[A]: set[A] = Coset[A](Nil)

def filter[A](p: A => Boolean, x1: List[A]): List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x :: xs) => (if (p(x)) x :: filter[A](p, xs) else filter[A](p, xs))
}

def remove[A : equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, Coset(xs)) => Coset[A](inserta[A](x, xs))
  case (x, Set(xs)) => Set[A](removeAll[A](x, xs))
}

def inf_set[A : equal](a: set[A], x1: set[A]): set[A] = (a, x1) match {
  case (a, Coset(xs)) =>
    fold[A, set[A]]((aa: A) => (b: set[A]) => remove[A](aa, b), xs, a)
  case (a, Set(xs)) => Set[A](filter[A]((x: A) => member[A](x, a), xs))
}

def inf_seta[A : equal](x0: set[set[A]]): set[A] = x0 match {
  case Set(xs) =>
    fold[set[A],
          set[A]]((a: set[A]) => (b: set[A]) => inf_set[A](a, b), xs,
                   top_set[A])
}

def min[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) a else b)

def mina[A : linorder](x0: set[A]): A = x0 match {
  case Set(x :: xs) => fold[A, A]((a: A) => (b: A) => min[A](a, b), xs, x)
}

def maps[A, B](f: A => List[B], x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) ++ maps[A, B](f, xs)
}

def upt(i: nat, j: nat): List[nat] =
  (if (less_nat(i, j)) i :: upt(suc(i), j) else Nil)

def nth[A](x0: List[A], n: nat): A = (x0, n) match {
  case (x :: xs, n) =>
    (if (equal_nata(n, zero_nat)) x else nth[A](xs, minus_nat(n, one_nata)))
}

def filterpositions2[A](p: A => Boolean, l: List[A]): List[nat] =
  maps[nat, nat]((n: nat) => (if (p(nth[A](l, n))) List(n) else Nil),
                  upt(zero_nat, size_list[A].apply(l)))

def fst[A, B](x0: (A, B)): A = x0 match {
  case (a, b) => a
}

def zip[A, B](xs: List[A], ys: List[B]): List[(A, B)] = (xs, ys) match {
  case (x :: xs, y :: ys) => (x, y) :: zip[A, B](xs, ys)
  case (xs, Nil) => Nil
  case (Nil, ys) => Nil
}

def hd[A](x0: List[A]): A = x0 match {
  case x :: xs => x
}

def sametomyleft[A : one : plus : equal](l: List[A]): List[Boolean] =
  map[(A, A),
       Boolean]((x: (A, A)) => eq[A](fst[A, A](x), snd[A, A](x)),
                 zip[A, A](l, plus[A](hd[A](l), one[A]) :: l))

def stopauctionat[A : one : plus : equal](l: List[A]): List[nat] =
  filterpositions2[Boolean]((x: Boolean) => equal_boola(x, true),
                             sametomyleft[A](l))

def domain[A, B](r: set[(A, B)]): set[A] =
  image[(A, B), A]((a: (A, B)) => fst[A, B](a), r)

def stopat[A : equal, B, C : one : plus : equal](b: set[(A, List[(B, C)])]):
      nat =
  mina[nat](inf_seta[nat](image[A, set[nat]]((i: A) =>
       Set[nat](stopauctionat[C](map[(B, C),
                                      C]((a: (B, C)) => snd[B, C](a),
  eval_rel[A, List[(B, C)]](b, i)))),
      domain[A, List[(B, C)]](b))))

def life(b: set[(nat, List[(Boolean, nat)])]): nat => Boolean =
  (a: nat) =>
    nth[Boolean](true ::
                   list_update[Boolean](replicate[Boolean](maxa[nat](image[List[(Boolean,
  nat)],
                                    nat](size_list[(Boolean, nat)],
  range[nat, List[(Boolean, nat)]](b))),
                    true),
 stopat[nat, Boolean, nat](b), false),
                  a)

def example: Boolean = (life(bidMatrix)).apply(zero_nat)

def sup_set[A : equal](x0: set[A], a: set[A]): set[A] = (x0, a) match {
  case (Coset(xs), a) => Coset[A](filter[A]((x: A) => ! (member[A](x, a)), xs))
  case (Set(xs), a) =>
    fold[A, set[A]]((aa: A) => (b: set[A]) => insert[A](aa, b), xs, a)
}

def nat_of_integer(k: BigInt): nat = Nat(max[BigInt](BigInt(0), k))

def product[A, B](x0: set[A], x1: set[B]): set[(A, B)] = (x0, x1) match {
  case (Set(xs), Set(ys)) =>
    Set[(A, B)](maps[A, (A, B)]((x: A) => map[B, (A, B)]((a: B) => (x, a), ys),
                                 xs))
}

def minus_set[A : equal](a: set[A], x1: set[A]): set[A] = (a, x1) match {
  case (a, Coset(xs)) => Set[A](filter[A]((x: A) => member[A](x, a), xs))
  case (a, Set(xs)) =>
    fold[A, set[A]]((aa: A) => (b: set[A]) => remove[A](aa, b), xs, a)
}

def outside[A : equal, B : equal](r: set[(A, B)], x: set[A]): set[(A, B)] =
  minus_set[(A, B)](r, product[A, B](x, range[A, B](r)))

def paste[A : equal, B : equal](p: set[(A, B)], q: set[(A, B)]): set[(A, B)] =
  sup_set[(A, B)](outside[A, B](p, domain[A, B](q)), q)

def addSingleBid(ba: set[(nat, List[(Boolean, nat)])], part: nat, b: nat):
      set[(nat, List[(Boolean, nat)])] =
  paste[nat, List[(Boolean,
                    nat)]](ba, insert[(nat,
List[(Boolean,
       nat)])]((fst[nat, List[(Boolean,
                                nat)]]((part,
 eval_rel[nat, List[(Boolean, nat)]](ba, part) ++ List((true, b)))),
                 snd[nat, List[(Boolean,
                                 nat)]]((part,
  eval_rel[nat, List[(Boolean, nat)]](ba, part) ++ List((true, b))))),
                bot_set[(nat, List[(Boolean, nat)])]))

def example02: set[(nat, List[(Boolean, nat)])] =
  addSingleBid(bidMatrix, zero_nat, nat_of_integer(BigInt(4)))


    def localToInt(s: String):Int = {
        // from http://alvinalexander.com/scala/how-cast-string-to-int-in-scala-string-int-conversion
        try {
            s.toInt
        } catch {
        case e:Exception => 0
        }
    }

    def main(args: Array[String]) {
        var M=bidMatrix;
        var j: BigInt = 0;
        var i: BigInt=0;
        while ( life(bidMatrix).apply(Nat(j)) ) {
          j = j+1;
          while (i < integer_of_nat(n)) { // Can't use for loop with BigInt
            print("Input the bid for bidder " + (i+1) + " in round " + j +".\n")
            val x = readLine; val newBid = localToInt(x);
            M = addSingleBid (M, Nat (i+1), Nat(newBid)); 
            i=i+1
          }
        }
    }


} /* object Dyna */
