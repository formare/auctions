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

import Nat._
import Set._

object NatSetWrapper {
  /** converts a Scala list to an Isabelle set.
   * Note that converting Int (hardware words) to Nat is OK, as it doesn't lose information, but converting vice versa is problematic when the Nat values are very large; then one should better convert to BigInt. */
  def intListToNatSet(l: List[Int]): set[nat] = Seta(l.map(x => Nat.Nata(BigInt(x))))
}
