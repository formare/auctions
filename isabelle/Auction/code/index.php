<?php
require_once($_SERVER['DOCUMENT_ROOT'] . '/sys/includes/wwwlib.php'); 
$formare_root = '../../../../../';
require_once($formare_root . 'macros.php');

$title = 'Auction Theory Toolbox – Isabelle (generated Scala code)';

SetHeaderTitle($title);
SetPageTitle($title);
SetMaintainer('Christoph Lange', 'math.semantic.web@gmail.com');
AddStylesheet($formare_root . 'formare.css');

HTMLHeader();
PageStart();
?>
<h2>Verified code generated from the <a href="../..">Isabelle formalisation</a></h2>
<ul>
  <li><a href="https://github.com/formare/auctions/tree/master/isabelle/Auction/code">Source repository (on GitHub)</a>.</li>
  <li><a href="code.zip">all-in-one ZIP archive for download</a></li>
  <li>Self-contained demos:
    <ul>
      <li>Hard-coded input: <a href="CombinatorialVickreyAuctionHardCoded.jar">executable code</a>, <a href="CombinatorialVickreyAuctionHardCoded.scala">source</a></li>
      <li>Using the bid format of <a href="http://www.cs.ubc.ca/~kevinlb/CATS/">CATS</a>: <a href="CombinatorialVickreyAuctionCATS.jar">executable code</a>, <a href="CombinatorialVickreyAuctionCATS.scala">source</a>, <a href="example.cats">sample bid input</a></li>
      <li>Using a variant of the CATS format with bidder IDs (“CAB”): <a href="CombinatorialVickreyAuctionCAB.jar">executable code</a>, <a href="CombinatorialVickreyAuctionCAB.scala">source</a>, <a href="example.cab">sample bid input</a></li>
    </ul>
  </li>
  <li>Other shared code modules:
    <ul>
      <li><a href="TieBreaker.scala">TieBreaker.scala</a>: tie-breaking functions</li>
    </ul>
  </li>
  <li>Wrappers around various types of the Isabelle library to make them Scala-friendly:
    <ul>
      <li><a href="NatSetWrapper.scala">NatSetWrapper.scala</a>: <code>nat set</code></li>
      <li><a href="RatWrapper.scala">RatWrapper.scala</a>: rational numbers</li>
      <li><a href="SetWrapper.scala">SetWrapper.scala</a>: <code>set</code></li>
      <li><a href="IsabelleLibraryWrapper.scala">IsabelleLibraryWrapper.scala</a>: general functions</li>
    </ul>
  </li>
  <li>Utilities:
    <ul>
      <li><a href="split-scala-modules.pl">split-scala-modules.pl</a>: splits Isabelle-generated Scala code into one Scala source file per module (i.e. per <code>object</code>/<code>class</code>)</li>
      <li><a href="Makefile">Makefile</a> contains rules to regenerate some of the files mentioned above.</li>
    </ul>
  </li>
</ul>
<h2>How to run</h2>
<ol>
  <li>For just executing the generated code, obtain Scala (see <a href="#isabelle-scala">below</a>), or use <a href="http://java.com">Java</a> with a recent version of <a href="https://oss.sonatype.org/content/groups/scala-tools/org/scala-lang/scala-library/">scala-library.jar</a>, e.g. <a href="https://oss.sonatype.org/content/groups/scala-tools/org/scala-lang/scala-library/2.10.2/scala-library-2.10.2.jar">scala-library-2.10.2</a>.  Then follow the instructions in <a href="README">README</a>.</li>
  <li id="isabelle-scala">For building the code, obtain <a href="https://isabelle.in.tum.de/">Isabelle</a> and <a href="http://www.scala-lang.org">Scala</a>.  Our formalisation is known to work with Isabelle2013; the generated code is known to work with Scala 2.10.</li>
  <li>You currently need to manually load and run any of the Isabelle theories that generate code (check the <a href="../..">overview</a> for “code”), e.g. in jEdit.</li>
  <li>The <a href="Makefile">Makefile</a> has several relevant targets; e.g., you can build and run the CAB example as follows:
    <ol>
      <li><code>make CombinatorialVickreyAuctionCAB.class</code></li>
      <li><code>scala CombinatorialVickreyAuctionCAB &lt; example.cab</code></li>
  </ol></li>
  <li>For executing <a href="split-scala-modules.pl">split-scala-modules.pl</a> (required by the Makefile), you need Perl ≥5.10 with the <code>File::Spec</code> module.</li>
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
