/*
 * Auction Theory Toolbox (http://formare.github.io/auctions/)
 * 
 * Authors:
 * * Manfred Kerber <m.kerber@cs.bham.ac.uk>
 * * Christoph Lange <math.semantic.web@gmail.com>
 * * Colin Rowat <c.rowat@bham.ac.uk>
 * 
 * Licenced under
 * * ISC License (1-clause BSD License)
 * See LICENSE file for details
 *
 */

package CombinatorialVickreyAuction

object TieBreaker {
  /** a trivial tie breaker that takes the head of a List */
  def trivialTieBreaker[T](l: List[T]) = l.head
}
