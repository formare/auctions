/*
 * Auction Theory Toolbox (http://formare.github.io/auctions/)
 * 
 * Authors:
 * * Manfred Kerber <mnfrd.krbr@gmail.com>
 * * Christoph Lange <math.semantic.web@gmail.com>
 * * Colin Rowat <c.rowat@bham.ac.uk>
 * 
 * Licenced under
 * * ISC License (1-clause BSD License)
 * See LICENSE file for details
 *
 */

package CombinatorialVickreyAuction

import Rat._
import RealDef._
import Set._

object IsabelleLibraryWrapper {
  def seqToPrettyString(s: Seq[Any]): String =
    s.map(prettyPrint(_)).mkString(", ") 

  /** pretty-prints several Isabelle types for display to the user */
  def prettyPrint[A](x: A): String = x match {
    /* Isabelle sets */
    case Seta(l) => "{%s}".format(seqToPrettyString(l))
    /* Isabelle's reals-from-rationals */
    // matching Frct(num, den) doesn't work, as actually (num, den) is a tuple
    case Ratreal(Frct((num, den))) => (num.toDouble / den.toDouble).toString /* note that this loses precision! */
    /* some Scala structures */
    case s: Seq[Any] => "[%s]".format(seqToPrettyString(s)) /* matches, e.g., List and Vector */
    case p: Product => "(%s)".format(p.productIterator.toList.map(prettyPrint(_)).mkString(", "))
    /* anything else */
    case _ => x.toString
  }
}
