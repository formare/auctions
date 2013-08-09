/*
 * $Id$
 * 
 * Auction Theory Toolbox
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

import Set._

object SetWrapper {

  /** equality for Isabelle sets (ignoring the order of the underlying List) */
  def setEquals[T](s1: set[T], s2: set[T]) = (s1, s2) match {
    case (Seta(l1), Seta(l2)) => l1.toSet == l2.toSet
    case _ => false
  }
}
