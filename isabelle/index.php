<?php
require_once($_SERVER['DOCUMENT_ROOT'] . '/sys/includes/wwwlib.php'); 

$title = 'Auction Theory Toolbox – Isabelle';

SetHeaderTitle($title);
SetPageTitle($title);
SetMaintainer('Christoph Lange', 'c.lange@cs.bham.ac.uk');
AddStylesheet('../../../formare.css');

HTMLHeader();
PageStart();
?>
<h2>Files relevant to the Isabelle formalisation</h2>
<ul>
  <li>*.thy: Isabelle formalisation:<ul>
      <li><a href="Vectors.thy">Vectors.thy</a>: vectors, implemented as functions</li>
      <li><a href="Maximum.thy">Maximum.thy</a>: maximum components of vectors, and their properties</li>
      <li><a href="MaximumTest.thy">MaximumTest.thy</a>: some examples for testing Maximum</li>
      <li><a href="SingleGoodAuction.thy">SingleGoodAuction.thy</a>: single good auctions</li>
      <li><a href="SingleGoodAuctionTest.thy">SingleGoodAuctionTest.thy</a>: some examples for testing SingleGoodAuction</li>
      <li><a href="SingleGoodAuctionProperties.thy">SingleGoodAuctionProperties.thy</a>: some properties that single good auctions can have</li>
      <li><a href="SecondPriceAuction.thy">SecondPriceAuction.thy</a>: second price single good auctions and some of their properties</li>
      <li><a href="Vickrey.thy">Vickrey.thy</a>: Vickrey's Theorem: second price auctions are efficient, and truthful bidding is a weakly dominant strategy.</li></ul>
      <li><a href="Vickrey_Short.thy">Vickrey_Short.thy</a>: a more recent all-in-one version</li></ul>
  </li>
  <li>*.pdf: exported files:<ul>
      <li><a href="document.pdf">document.pdf</a>: human-readable LaTeX paper</li>
      <li><a href="graph.pdf">graph.pdf</a>: theory graph</li></ul></li>
</ul>
<h2>How to run</h2>
<ol>
  <li>Obtain <a href="https://isabelle.in.tum.de/">Isabelle</a>.  Our code is known to work with Isabelle2013.</li>
  <li>Interactive mode: run <code>isabelle jedit Auction/Vickrey.thy</code> and agree to loading all of its dependencies.</li>
  <li>Batch mode: run <code>isabelle build -D Auction</code> and open the generated <code>Auction/output/document.pdf</code></li>
</ol>
<?php
PageEnd();
HTMLFooter();
?>
<?php /*
Local Variables:
mode: html 
End:
*/ ?>
