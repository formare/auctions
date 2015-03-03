//Title of this code
//'Rextester' class is the entry point for your code.
//Don't declare a package.
//scala 2.9.2

object auctionWrapper extends App {

def pred_list[A](p: A => Boolean, x1: List[A]): Boolean = (p, x1) match {
  case (p, Nil) => true
  case (p, x :: xs) => p(x) && pred_list[A](p, xs)
}

abstract sealed class set[A]
final case class seta[A](a: List[A]) extends set[A]
final case class coset[A](a: List[A]) extends set[A]

trait equal[A] {
  val `a.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`a.equal`(a, b)

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
  val `a.equal` = (a: set[A], b: set[A]) => equal_seta[A](a, b)
}

def equal_proda[A : equal, B : equal](x0: (A, B), x1: (A, B)): Boolean =
  (x0, x1) match {
  case ((x1, x2), (y1, y2)) => eq[A](x1, y1) && eq[B](x2, y2)
}

implicit def equal_prod[A : equal, B : equal]: equal[(A, B)] = new equal[(A, B)]
  {
  val `a.equal` = (a: (A, B), b: (A, B)) => equal_proda[A, B](a, b)
}

implicit def equal_integer: equal[BigInt] = new equal[BigInt] {
  val `a.equal` = (a: BigInt, b: BigInt) => a == b
}

trait plus[A] {
  val `a.plus`: (A, A) => A
}
def plus[A](a: A, b: A)(implicit A: plus[A]): A = A.`a.plus`(a, b)

implicit def plus_integer: plus[BigInt] = new plus[BigInt] {
  val `a.plus` = (a: BigInt, b: BigInt) => a + b
}

trait zero[A] {
  val `a.zero`: A
}
def zero[A](implicit A: zero[A]): A = A.`a.zero`

implicit def zero_integer: zero[BigInt] = new zero[BigInt] {
  val `a.zero` = BigInt(0)
}

trait ord[A] {
  val `a.less_eq`: (A, A) => Boolean
  val `a.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`a.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`a.less`(a, b)

implicit def ord_integer: ord[BigInt] = new ord[BigInt] {
  val `a.less_eq` = (a: BigInt, b: BigInt) => a <= b
  val `a.less` = (a: BigInt, b: BigInt) => a < b
}

trait preorder[A] extends ord[A] {
}

trait order[A] extends preorder[A] {
}

implicit def preorder_integer: preorder[BigInt] = new preorder[BigInt] {
  val `a.less_eq` = (a: BigInt, b: BigInt) => a <= b
  val `a.less` = (a: BigInt, b: BigInt) => a < b
}

implicit def order_integer: order[BigInt] = new order[BigInt] {
  val `a.less_eq` = (a: BigInt, b: BigInt) => a <= b
  val `a.less` = (a: BigInt, b: BigInt) => a < b
}

trait semigroup_add[A] extends plus[A] {
}

trait monoid_add[A] extends semigroup_add[A] with zero[A] {
}

implicit def semigroup_add_integer: semigroup_add[BigInt] = new
  semigroup_add[BigInt] {
  val `a.plus` = (a: BigInt, b: BigInt) => a + b
}

implicit def monoid_add_integer: monoid_add[BigInt] = new monoid_add[BigInt] {
  val `a.zero` = BigInt(0)
  val `a.plus` = (a: BigInt, b: BigInt) => a + b
}

trait linorder[A] extends order[A] {
}

implicit def linorder_integer: linorder[BigInt] = new linorder[BigInt] {
  val `a.less_eq` = (a: BigInt, b: BigInt) => a <= b
  val `a.less` = (a: BigInt, b: BigInt) => a < b
}

trait ab_semigroup_add[A] extends semigroup_add[A] {
}

trait comm_monoid_add[A] extends ab_semigroup_add[A] with monoid_add[A] {
}

implicit def ab_semigroup_add_integer: ab_semigroup_add[BigInt] = new
  ab_semigroup_add[BigInt] {
  val `a.plus` = (a: BigInt, b: BigInt) => a + b
}

implicit def comm_monoid_add_integer: comm_monoid_add[BigInt] = new
  comm_monoid_add[BigInt] {
  val `a.zero` = BigInt(0)
  val `a.plus` = (a: BigInt, b: BigInt) => a + b
}

abstract sealed class nat
final case class Nat(a: BigInt) extends nat

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

def id[A]: A => A = (x: A) => x

def comp[A, B, C](f: A => B, g: C => A): C => B = (x: C) => f(g(x))

def integer_of_nat(x0: nat): BigInt = x0 match {
  case Nat(x) => x
}

def max[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) b else a)

def minus_nat(m: nat, n: nat): nat =
  Nat(max[BigInt](BigInt(0), integer_of_nat(m) - integer_of_nat(n)))

def equal_nat(m: nat, n: nat): Boolean = integer_of_nat(m) == integer_of_nat(n)

def zero_nat: nat = Nat(BigInt(0))

def one_nat: nat = Nat(BigInt(1))

def nth[A](x0: List[A], n: nat): A = (x0, n) match {
  case (x :: xs, n) =>
    (if (equal_nat(n, zero_nat)) x else nth[A](xs, minus_nat(n, one_nat)))
}

def fold[A, B](f: A => B => B, x1: List[A], s: B): B = (f, x1, s) match {
  case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
  case (f, Nil, s) => s
}

def maps[A, B](f: A => List[B], x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) ++ maps[A, B](f, xs)
}

def map[A, B](fi: A => B, x1: List[A]): List[B] = (fi, x1) match {
  case (fi, Nil) => Nil
  case (fi, x21a :: x22) => fi(x21a) :: map[A, B](fi, x22)
}

def image[A, B](f: A => B, x1: set[A]): set[B] = (f, x1) match {
  case (f, seta(xs)) => seta[B](map[A, B](f, xs))
}

def b1: List[List[List[BigInt]]] =
  List(List(List(BigInt(1)), 
                 List(BigInt(11), BigInt(12), BigInt(13)), List(BigInt(3))),
        List(List(BigInt(2)), List(BigInt(11), BigInt(13)), List(BigInt(22))))

def foldr[A, B](f: A => B => B, x1: List[A]): B => B = (f, x1) match {
  case (f, Nil) => id[B]
  case (f, x :: xs) => comp[B, B, B](f(x), foldr[A, B](f, xs))
}

def filtera[A](p: A => Boolean, x1: List[A]): List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x :: xs) => (if (p(x)) x :: filtera[A](p, xs) else filtera[A](p, xs))
}

def filter[A](p: A => Boolean, x1: set[A]): set[A] = (p, x1) match {
  case (p, seta(xs)) => seta[A](filtera[A](p, xs))
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

def remove[A : equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, coset(xs)) => coset[A](inserta[A](x, xs))
  case (x, seta(xs)) => seta[A](removeAll[A](x, xs))
}

def concat[A](xss: List[List[A]]): List[A] =
  (foldr[List[A],
          List[A]]((a: List[A]) => (b: List[A]) => a ++ b, xss)).apply(Nil)

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

def nat_of_integer(k: BigInt): nat = Nat(max[BigInt](BigInt(0), k))

def helper[A](list: List[List[A]]): ((A, set[A]), A) =
  (((comp[List[A], A,
           List[List[A]]]((a: List[A]) => hd[A](a),
                           (a: List[List[A]]) => hd[List[A]](a))).apply(list),
     seta[A](nth[List[A]](list, one_nat))),
    hd[A](nth[List[A]](list, nat_of_integer(BigInt(2)))))

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

def minus_set[A : equal](a: set[A], x1: set[A]): set[A] = (a, x1) match {
  case (a, coset(xs)) => seta[A](filtera[A]((x: A) => member[A](x, a), xs))
  case (a, seta(xs)) =>
    fold[A, set[A]]((aa: A) => (b: set[A]) => remove[A](aa, b), xs, a)
}

def bot_set[A]: set[A] = seta[A](Nil)

def product[A, B](x0: set[A], x1: set[B]): set[(A, B)] = (x0, x1) match {
  case (seta(xs), seta(ys)) =>
    seta[(A, B)](maps[A, (A, B)]((x: A) => map[B, (A, B)]((a: B) => (x, a), ys),
                                  xs))
}

def Outside[A : equal, B : equal](r: set[(A, B)], x: set[A]): set[(A, B)] =
  minus_set[(A, B)](r, product[A, B](x, Range[A, B](r)))

def sup_set[A : equal](x0: set[A], a: set[A]): set[A] = (x0, a) match {
  case (coset(xs), a) => coset[A](filtera[A]((x: A) => ! (member[A](x, a)), xs))
  case (seta(xs), a) =>
    fold[A, set[A]]((aa: A) => (b: set[A]) => insert[A](aa, b), xs, a)
}

def fst[A, B](x0: (A, B)): A = x0 match {
  case (x1, x2) => x1
}

def Domain[A, B](r: set[(A, B)]): set[A] =
  image[(A, B), A]((a: (A, B)) => fst[A, B](a), r)

def paste[A : equal, B : equal](p: set[(A, B)], q: set[(A, B)]): set[(A, B)] =
  sup_set[(A, B)](Outside[A, B](p, Domain[A, B](q)), q)

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

def converse[A, B](r: set[(A, B)]): set[(B, A)] =
  image[(A, B), (B, A)]((a: (A, B)) => {
 val (x, y): (A, B) = a;
 (y, x)
                                       },
                         r)

def example: set[List[(BigInt, List[BigInt])]] =
  image[set[(BigInt, set[BigInt])],
         List[(BigInt,
                List[BigInt])]]((a: set[(BigInt, set[BigInt])]) =>
                                  map[BigInt,
                                       (BigInt,
 List[BigInt])]((x: BigInt) =>
                  (x, sorted_list_of_set[BigInt](eval_rel[BigInt,
                   set[BigInt]](a, x))),
                 (comp[set[BigInt], List[BigInt],
                        set[(BigInt,
                              set[BigInt])]]((aa: set[BigInt]) =>
       sorted_list_of_set[BigInt](aa),
      (aa: set[(BigInt, set[BigInt])]) =>
        Domain[BigInt, set[BigInt]](aa))).apply(a)),
                                 argmax[set[(BigInt, set[BigInt])],
 BigInt]((a: set[(BigInt, set[BigInt])]) =>
           setsum[(BigInt, set[BigInt]), BigInt](listBid2funcBid(b1), a),
          seta[set[(BigInt,
                     set[BigInt])]](map[set[(set[BigInt], BigInt)],
 set[(BigInt,
       set[BigInt])]]((a: set[(set[BigInt], BigInt)]) =>
                        converse[set[BigInt], BigInt](a),
                       maps[List[set[BigInt]],
                             set[(set[BigInt],
                                   BigInt)]]((l: List[set[BigInt]]) =>
       injections_alg[set[BigInt],
                       BigInt](l, sup_set[BigInt](insert[BigInt](BigInt(0),
                          bot_set[BigInt]),
           seta[BigInt](map[List[List[BigInt]],
                             BigInt](comp[List[BigInt], BigInt,
   List[List[BigInt]]]((a: List[BigInt]) => hd[BigInt](a),
                        (a: List[List[BigInt]]) => hd[List[BigInt]](a)),
                                      b1)))),
      all_partitions_list[BigInt]((comp[List[List[BigInt]], List[BigInt],
 List[List[List[BigInt]]]](comp[List[BigInt], List[BigInt],
                                 List[List[BigInt]]]((a: List[BigInt]) =>
               remdups[BigInt](a),
              (a: List[List[BigInt]]) => concat[BigInt](a)),
                            (a: List[List[List[BigInt]]]) =>
                              map[List[List[BigInt]],
                                   List[BigInt]]((l: List[List[BigInt]]) =>
           nth[List[BigInt]](l, one_nat),
          a))).apply(b1)))))))
          
// Anything after the line "object Rextester extends App {" and to this line has been generated by Isabelle. 
//Go to line 199 to modify input
//http://stackoverflow.com/questions/6639377/how-do-i-print-a-list-of-anything-in-scala

// The rest of the file are handwritten functions to print some output.

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
    println(payments(args));
}

def printAllocationAndPayment(args: (BigInt, List[BigInt])): Unit = args match {
    case (hd, tl) => print(" X_" + hd + " = {" ); 
                     printAllocatedGoods(tl);
                     print("}    payment:");
                     printPrice(hd);
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

}
