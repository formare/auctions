<?php
require_once($_SERVER['DOCUMENT_ROOT'] . '/sys/includes/wwwlib.php'); 

$title = 'Auction Theory Toolbox – CASL';

SetHeaderTitle($title);
SetPageTitle($title);
SetMaintainer('Christoph Lange', 'c.lange@cs.bham.ac.uk');
AddStylesheet('../../../formare.css');

HTMLHeader();
PageStart();
?>
<h2>Files relevant to the CASL formalisation</h2>
<ul>
  <li>*.casl: <a href="http://www.cofi.info">CASL</a> formalisation:<ul>
      <li><a href="Vickrey.casl">Vickrey.casl</a>: Vickrey's Theorem and all of its prerequisites</a></li>
  </ul></li>
  <li>further relevant <a href="Makefile">Makefile</a> targets:
    <ul>
      <li>use, e.g., <code>make Vickrey_Maximum.tptp</code> to export a <a href="http://www.cs.miami.edu/~tptp/">TPTP</a> <a href="http://www.cs.miami.edu/~tptp/TPTP/TR/TPTPTR.shtml">FOF</a> representation of the Maximum specification in Vickrey.casl.  This is suitable for feeding into <a href="http://www.cs.miami.edu/~tptp/cgi-bin/SystemOnTPTP">System on TPTP</a>.</li>
    </ul>
  </li>
</ul>
<h2>How to run</h2>
<ol>
  <li>Obtain <a href="http://www.dfki.de/cps/hets">Hets (Heterogeneous Tool Set)</a>.  Hets runs on Linux and Mac OS; an image for virtual machines is available as well.</li>
  <li>Make sure that some additional tools required by Hets are installed (either via the Hets installer or by other means) and accessible in your <code>PATH</code>:
    <ul>
      <li>some automated FOL theorem provers: We recommend <a href="http://www.spass-prover.org/">SPASS</a> and <a href="http://www4.informatik.tu-muenchen.de/~schulz/E/">E</a>.</li>
      <li><a href="http://www.informatik.uni-bremen.de/uDrawGraph/">uDraw(Graph)</a></li>
  </ul></li>
  <li>Download the <a href="http://www.cofi.info/Libraries">CASL libraries</a> and set <code>HETS_LIB</code> to the directory where you downloaded them.</li>
  <li>Running <code>hets -g Vickrey.casl</code> displays a development graph.  In this graph, you can right-click on any theory node with open proof goals (displayed in red) and try to prove them.</li>
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
