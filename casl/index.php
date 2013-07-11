<?php
require_once($_SERVER['DOCUMENT_ROOT'] . '/sys/includes/wwwlib.php'); 
$formare_root = '../../../';
require_once($formare_root . 'macros.php');

$title = 'Auction Theory Toolbox (ATT) – CASL';

SetHeaderTitle($title);
SetPageTitle($title);
SetMaintainer('Christoph Lange', 'c.lange@cs.bham.ac.uk');
AddStylesheet($formare_root . 'formare.css');

HTMLHeader();
PageStart();
?>
<h2>Files relevant to the CASL formalisation</h2>
<ul>
  <li><a href="casl.zip">all-in-one ZIP archive for download</a></li>
  <li>*.casl: <a href="http://www.cofi.info">CASL</a> formalisation:<ul>
      <li><a href="Vickrey.casl">Vickrey.casl</a>: Vickrey's Theorem and all of its prerequisites</a></li>
  </ul></li>
  <li>*.hpf: proof scripts for Hets, whenever a lemma/theorem requires a multi-step proof:
    <ul>
      <li>general: <a href="Vickrey-consistency.hpf">consistency of all specs</a>
      <li><a href="Vickrey1.hpf">SingleGoodAuction.allocation_unique</a></li>
      <li><a href="Vickrey2.hpf">Maximum.only_one_maximum</a></li>
      <li>…</li>
    </ul>
  </li>
  <li>further relevant <a href="Makefile">Makefile</a> targets:
    <ul>
      <li>Use, e.g., <code>make Vickrey_Maximum.tptp</code> to export a <a href="http://www.cs.miami.edu/~tptp/">TPTP</a> <a href="http://www.cs.miami.edu/~tptp/TPTP/TR/TPTPTR.shtml">FOF</a> representation of the Maximum specification in Vickrey.casl.  This is suitable for feeding into <a href="http://www.cs.miami.edu/~tptp/cgi-bin/SystemOnTPTP">System on TPTP</a>.<br/>
        Even more useful are TPTP exports of individual goals, but these you can only export interactively from the Hets GUI, by pretending to invoke a TPTP-based prover such as E for them (see below), and then saving the input file that Hets generated for sending to the prover.  With <a href="Vickrey_SecondPriceAuction_only_max_bidder_wins.tptp">Vickrey_SecondPriceAuction_only_max_bidder_wins.tptp</a> we provide one such file for your convenience.  This is known to work with E.</li>
    </ul>
  </li>
</ul>
<h2>How to run</h2>
<ol>
  <li>Obtain <a href="http://www.dfki.de/cps/hets">Hets (Heterogeneous Tool Set)</a>.  Our code is known to work with Hets 0.98.  Hets runs on Linux and Mac OS; an image for virtual machines is available as well.</li>
  <li>Make sure that some additional tools required by Hets are installed (either via the Hets installer or by other means) and accessible in your <code>PATH</code>:
    <ul>
      <li>some automated FOL theorem provers: We recommend <a href="http://www.spass-prover.org/">SPASS</a> and <a href="http://www4.informatik.tu-muenchen.de/~schulz/E/">E</a>.</li>
      <li><a href="http://www.informatik.uni-bremen.de/uDrawGraph/">uDraw(Graph)</a></li>
  </ul></li>
  <li>Download the <a href="http://www.cofi.info/Libraries">CASL libraries</a> and set <code>HETS_LIB</code> to the directory where you downloaded them.</li>
  <li>Running <code>hets -g Vickrey.casl</code> displays the development graph GUI.  In this graph, you can right-click on any theory node with open proof goals (displayed in red) and try to prove them.</li>
  <li>Some theorems cannot be proved in one step.  For proving them, we provide scripts, one per theorem.  You can run them with <code>hets -I &lt; script.hpf</code>.</li>
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
