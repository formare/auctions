<?php
require_once($_SERVER['DOCUMENT_ROOT'] . '/sys/includes/wwwlib.php'); 
$formare_root = '../../../';
require_once($formare_root . 'macros.php');

$title = 'Auction Theory Toolbox – Isabelle';

SetHeaderTitle($title);
SetPageTitle($title);
SetMaintainer('Christoph Lange', 'c.lange@cs.bham.ac.uk');
AddStylesheet($formare_root . 'formare.css');

HTMLHeader();
PageStart();
?>
<h2>Files relevant to the Isabelle formalisation</h2>
<ul>
  <li><a href="https://codex.cs.bham.ac.uk/svn/langec/formare/code/auction/isabelle">Source repository (Subversion)</a>.  You can browse the repository as user <code>guest</code> with password <code>guest</code>.</li>
  <li><a href="isabelle.zip">all-in-one ZIP archive for download</a></li>
  <li>*.thy: Isabelle formalisation:<ul>
      <li>General foundations of static single good auctions, and Vickrey's theorem:
        <ul>
          <li><a href="Auction/All.thy">All.thy</a>: loads all theories whose formalisation is stable, for convenience</li>
          <li><a href="Auction/Vectors.thy">Vectors.thy</a>: vectors, implemented as functions</li>
          <li><a href="Auction/Maximum.thy">Maximum.thy</a>: maximum components of vectors, and their properties</li>
          <li><a href="Auction/MaximumTest.thy">MaximumTest.thy</a>: some examples for testing Maximum</li>
          <li><a href="Auction/SingleGoodAuction.thy">SingleGoodAuction.thy</a>: single good auctions</li>
          <li><a href="Auction/SingleGoodAuctionTest.thy">SingleGoodAuctionTest.thy</a>: some examples for testing SingleGoodAuction</li>
          <li><a href="Auction/SingleGoodAuctionProperties.thy">SingleGoodAuctionProperties.thy</a>: some properties that single good auctions can have</li>
          <li><a href="Auction/SecondPriceAuction.thy">SecondPriceAuction.thy</a>: second price single good auctions (underspecified; without tie-breaking) and some of their properties</li>
          <li><a href="Auction/Vickrey.thy">Vickrey.thy</a>: Vickrey's Theorem: second price auctions are efficient, and truthful bidding is a weakly dominant strategy.</li></ul>
      </li>
      <li>Soundness checks for static single good auctions:
        <ul>
          <li><a href="Auction/SecondPriceAuctionCaseCheck.thy">SecondPriceAuction.thy</a>: soundness proof of the underspecified second price single good auctions without tie-breaking</li>
          <li><a href="Auction/UniqueMaximum.thy">UniqueMaximum.thy</a>: determining a unique maximum components of vectors, subject to tie-breaking</li>
          <li><a href="Auction/SingleGoodAuctionTieBreaker.thy">SingleGoodAuctionTieBreaker.thy</a>: tie-breaking rules for single good auctions</li>
          <li><a href="Auction/FullySpecifiedSingleGoodAuction.thy">FullySpecifiedSingleGoodAuction.thy</a>: fully specified single good auctions, with tie-breaking rules</li>
          <li><a href="Auction/FullySpecifiedSecondPriceAuction.thy">FullySpecifiedSecondPriceAuction.thy</a>: fully specified variant of the second price single good auction</li>
          <li><a href="Auction/FullySpecifiedSecondPriceAuctionCaseCheck.thy">FullySpecifiedSecondPriceAuctionCaseCheck.thy</a>: soundness proof of the fully specified variant of the second price single good auction</li>
      </ul></li>
      <li>Static combinatorial auctions, from foundations to soundness checks:
        <ul>
          <li><a href="Auction/RelationProperties.thy">RelationProperties.thy</a>: further helpful properties of relations, beyond Relations.thy from the library</li>
          <li><a href="Auction/Partitions.thy">Partitions.thy</a>: partitions of sets</li>
          <li><a href="Auction/nVCG_CaseChecker.thy">nVCG_CaseChecker.thy</a>: soundness proof (in progress) of the fully specified combinatorial Vickrey auction</li>
          <li><a href="Auction/CombinatorialVickreyAuction.thy">CombinatorialVickreyAuction.thy</a>: wrapper to generate verified code to execute the combinatorial Vickrey auction</li>
        </ul>
      </li>
  </li>
  <li>*.pdf: exported files (for an old version of Vickrey's theorem at the time of this writing):<ul>
      <li><a href="Auction/output/document/root.pdf">human-readable LaTeX paper</a></li>
      <li><a href="graph.pdf">theory graph</a></li></ul></li>
  <li><a href="Auction/code/">code</a>: executable Scala code generated from the fully specified auctions (in progress)</li>
  <li><a href="Makefile">Makefile</a> contains rules to regenerate some of the files mentioned above.</li>
</ul>
<h2>How to run</h2>
<ol>
  <li>Obtain <a href="https://isabelle.in.tum.de/">Isabelle</a>.  Our code is known to work with Isabelle2013.</li>
  <li>Interactive mode: run <code>isabelle jedit Auction/Vickrey.thy</code>, and agree to loading all of its dependencies.</li>
  <li>Batch mode: run <code>isabelle build -D Auction</code> and open the generated <code>Auction/output/document/root.pdf</code></li>
</ol>
<p style="text-align:right; font-style:italic"><? echo $timestamp ?></p>
<?php
PageEnd();
HTMLFooter();
?>
<?php /*
Local Variables:
mode: html 
End:
*/ ?>
