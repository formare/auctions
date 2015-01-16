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

def plus_nat(m: nat, n: nat): nat = Nat(integer_of_nat(m) + integer_of_nat(n))

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

def one_nat: nat = Nat(BigInt(1))

def suc(n: nat): nat = plus_nat(n, one_nat)

def gen_length[A](n: nat, x1: List[A]): nat = (n, x1) match {
  case (n, x :: xs) => gen_length[A](suc(n), xs)
  case (n, Nil) => n
}

def zero_nata: nat = Nat(BigInt(0))

def size_list[A]: (List[A]) => nat = (a: List[A]) => gen_length[A](zero_nata, a)

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
                      nat)])]((zero_nata, Nil),
                               insert[(nat,
List[(Boolean, nat)])]((one_nat, Nil), bot_set[(nat, List[(Boolean, nat)])]))

def n: nat = card[(nat, List[(Boolean, nat)])](bidMatrix)

def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) :: map[A, B](f, xs)
}

def image[A, B](f: A => B, x1: set[A]): set[B] = (f, x1) match {
  case (f, Set(xs)) => Set[B](map[A, B](f, xs))
}

def graph[A, B](x: set[A], f: A => B): set[(A, B)] =
  image[A, (A, B)]((xa: A) => (xa, f(xa)), x)

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

def converse[A, B](r: set[(A, B)]): set[(B, A)] =
  image[(A, B), (B, A)]((a: (A, B)) => {
 val (x, y): (A, B) = a;
 (y, x)
                                       },
                         r)

def max[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) b else a)

def fold[A, B](f: A => B => B, x1: List[A], s: B): B = (f, x1, s) match {
  case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
  case (f, Nil, s) => s
}

def maxa[A : linorder](x0: set[A]): A = x0 match {
  case Set(x :: xs) => fold[A, A]((a: A) => (b: A) => max[A](a, b), xs, x)
}

def snd[A, B](x0: (A, B)): B = x0 match {
  case (a, b) => b
}

def fst[A, B](x0: (A, B)): A = x0 match {
  case (a, b) => a
}

def maps[A, B](f: A => List[B], x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) ++ maps[A, B](f, xs)
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

def range[A, B](r: set[(A, B)]): set[B] =
  image[(A, B), B]((a: (A, B)) => snd[A, B](a), r)

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

implicit def ord_integer: ord[BigInt] = new ord[BigInt] {
  val `Dyna.less_eq` = (a: BigInt, b: BigInt) => a <= b
  val `Dyna.less` = (a: BigInt, b: BigInt) => a < b
}

def minus_nat(m: nat, n: nat): nat =
  Nat(max[BigInt](BigInt(0), integer_of_nat(m) - integer_of_nat(n)))

def nth[A](x0: List[A], n: nat): A = (x0, n) match {
  case (x :: xs, n) =>
    (if (equal_nata(n, zero_nata)) x else nth[A](xs, minus_nat(n, one_nat)))
}

def wdp[A : linorder](matrix: set[(A, List[(Boolean, nat)])]): A =
  maxa[A](imagea[nat, A](converse[A, nat](relcomp[A, List[(Boolean, nat)],
           nat](matrix,
                 graph[List[(Boolean, nat)],
                        nat](range[A, List[(Boolean, nat)]](matrix),
                              (x: List[(Boolean, nat)]) =>
                                snd[Boolean,
                                     nat](nth[(Boolean,
        nat)](x, minus_nat(maxa[nat](image[List[(Boolean, nat)],
    nat](size_list[(Boolean, nat)],
          image[(A, List[(Boolean, nat)]),
                 List[(Boolean,
                        nat)]]((a: (A, List[(Boolean, nat)])) =>
                                 snd[A, List[(Boolean, nat)]](a),
                                matrix))),
                            one_nat)))))),
                          insert[nat](maxa[nat](range[A,
               nat](relcomp[A, List[(Boolean, nat)],
                             nat](matrix,
                                   graph[List[(Boolean, nat)],
  nat](range[A, List[(Boolean, nat)]](matrix),
        (x: List[(Boolean, nat)]) =>
          snd[Boolean,
               nat](nth[(Boolean,
                          nat)](x, minus_nat(maxa[nat](image[List[(Boolean,
                            nat)],
                      nat](size_list[(Boolean, nat)],
                            image[(A, List[(Boolean, nat)]),
                                   List[(Boolean,
  nat)]]((a: (A, List[(Boolean, nat)])) => snd[A, List[(Boolean, nat)]](a),
          matrix))),
      one_nat))))))),
                                       bot_set[nat])))

def override_on[A : equal, B](f: A => B, g: A => B, a: set[A]): A => B =
  (aa: A) => (if (member[A](aa, a)) g(aa) else f(aa))

def replicate[A](n: nat, x: A): List[A] =
  (if (equal_nata(n, zero_nata)) Nil
    else x :: replicate[A](minus_nat(n, one_nat), x))

trait zero[A] {
  val `Dyna.zero`: A
}
def zero[A](implicit A: zero[A]): A = A.`Dyna.zero`

def upt(i: nat, j: nat): List[nat] =
  (if (less_nat(i, j)) i :: upt(suc(i), j) else Nil)

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

def filterpositions2[A](p: A => Boolean, l: List[A]): List[nat] =
  maps[nat, nat]((n: nat) => (if (p(nth[A](l, n))) List(n) else Nil),
                  upt(zero_nata, size_list[A].apply(l)))

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
  filterpositions2[Boolean]((x: Boolean) => equal_boola(x, true),
                             sametomyleft[A](l))

def domain[A, B](r: set[(A, B)]): set[A] =
  image[(A, B), A]((a: (A, B)) => fst[A, B](a), r)

def stops[A : equal, B, C : zero : equal](b: set[(A, List[(B, C)])]): set[nat] =
  inf_seta[nat](image[A, set[nat]]((i: A) =>
                                     Set[nat](stopauctionat[C](map[(B, C),
                            C]((a: (B, C)) => snd[B, C](a),
                                eval_rel[A, List[(B, C)]](b, i)))),
                                    domain[A, List[(B, C)]](b)))

def livelinessList[A : equal, B, C : zero : equal](b: set[(A, List[(B, C)])]):
      List[Boolean] =
  true ::
    map[nat, Boolean](override_on[nat, Boolean]((a: nat) =>
          nth[Boolean](replicate[Boolean](maxa[nat](image[List[(B, C)],
                   nat](size_list[(B, C)], range[A, List[(B, C)]](b))),
   true),
                        a),
         (_: nat) => false, stops[A, B, C](b)),
                       upt(zero_nata,
                            size_list[Boolean].apply(replicate[Boolean](maxa[nat](image[List[(B,
               C)],
         nat](size_list[(B, C)], range[A, List[(B, C)]](b))),
                                 true))))

implicit def zero_nat: zero[nat] = new zero[nat] {
  val `Dyna.zero` = zero_nata
}

def alive(b: set[(nat, List[(Boolean, nat)])]): nat => Boolean =
  (a: nat) => nth[Boolean](livelinessList[nat, Boolean, nat](b), a)

def price[A : equal : linorder](matrix: set[(A, List[(Boolean, nat)])]): nat =
  eval_rel[A, nat](relcomp[A, List[(Boolean, nat)],
                            nat](matrix,
                                  graph[List[(Boolean, nat)],
 nat](range[A, List[(Boolean, nat)]](matrix),
       (x: List[(Boolean, nat)]) =>
         snd[Boolean,
              nat](nth[(Boolean,
                         nat)](x, minus_nat(maxa[nat](image[List[(Boolean,
                           nat)],
                     nat](size_list[(Boolean, nat)],
                           image[(A, List[(Boolean, nat)]),
                                  List[(Boolean,
 nat)]]((a: (A, List[(Boolean, nat)])) => snd[A, List[(Boolean, nat)]](a),
         matrix))),
     one_nat))))),
                    maxa[A](imagea[nat, A](converse[A,
             nat](relcomp[A, List[(Boolean, nat)],
                           nat](matrix,
                                 graph[List[(Boolean, nat)],
nat](range[A, List[(Boolean, nat)]](matrix),
      (x: List[(Boolean, nat)]) =>
        snd[Boolean,
             nat](nth[(Boolean,
                        nat)](x, minus_nat(maxa[nat](image[List[(Boolean, nat)],
                    nat](size_list[(Boolean, nat)],
                          image[(A, List[(Boolean, nat)]),
                                 List[(Boolean,
nat)]]((a: (A, List[(Boolean, nat)])) => snd[A, List[(Boolean, nat)]](a),
        matrix))),
    one_nat)))))),
    insert[nat](maxa[nat](range[A, nat](relcomp[A, List[(Boolean, nat)],
         nat](matrix,
               graph[List[(Boolean, nat)],
                      nat](range[A, List[(Boolean, nat)]](matrix),
                            (x: List[(Boolean, nat)]) =>
                              snd[Boolean,
                                   nat](nth[(Boolean,
      nat)](x, minus_nat(maxa[nat](image[List[(Boolean, nat)],
  nat](size_list[(Boolean, nat)],
        image[(A, List[(Boolean, nat)]),
               List[(Boolean,
                      nat)]]((a: (A, List[(Boolean, nat)])) =>
                               snd[A, List[(Boolean, nat)]](a),
                              matrix))),
                          one_nat))))))),
                 bot_set[nat]))))

def example: Boolean = (alive(bidMatrix)).apply(n)

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
  addSingleBid(bidMatrix, zero_nata, nat_of_integer(BigInt(4)))

  

    def localToInt(s: String):Int = {
        // from http://alvinalexander.com/scala/how-cast-string-to-int-in-scala-string-int-conversion
        try {
            s.toInt
        } catch {
        case e:Exception => 0
        }
    }

    def main(args: Array[String]) {
        var M=bidMatrix; var j: BigInt = 0;
        while ( alive(M).apply(Nat(j)) ) {
          j = j+1; var i: BigInt=0;
          while (i < integer_of_nat(n)) { // Can't use for loop with BigInt
            print("Input the bid for bidder " + i + " in round " + j +".\n")
            val x = readLine; val newBid = localToInt(x);
            println("debug0 " + i);
            M = addSingleBid (M, Nat (i), Nat(newBid)); 
            i=i+1
            print("debug1 " + livelinessList(M));
          }
//          println ("debug2");
//          println ("debug3");
        }
        println("Outcome:");
        println (wdp(M));
        println (price(M));
    }  
  
  
} /* object Dyna */
