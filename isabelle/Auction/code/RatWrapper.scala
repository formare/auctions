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

object RatWrapper {
  /**
    * converts decimal numbers (whole.fraction, given as strings)
    * to rational numbers (numerator/denominator) */
  def decToFrct(whole: String, maybeFrac: Option[String]): rat = {
    val power = maybeFrac match {
      case Some(f) => f.length
      case None => 0
    }
    val frac = maybeFrac match {
      case Some(f) => f.toInt
      case None => 0
    }
    val commonDen = math.pow(10, power).toInt
    Frct((commonDen * whole.toInt + frac, commonDen))
  }
}
