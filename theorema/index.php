<?php
require_once($_SERVER['DOCUMENT_ROOT'] . '/sys/includes/wwwlib.php'); 
$formare_root = '../../../';
require_once($formare_root . 'macros.php');

$title = 'Auction Theory Toolbox (ATT) – Theorema';

SetHeaderTitle($title);
SetPageTitle($title);
SetMaintainer('Christoph Lange', 'c.lange@cs.bham.ac.uk');
AddStylesheet($formare_root . 'formare.css');

HTMLHeader();
PageStart();
?>
<h2>Files relevant to the Theorema formalisation</h2>
<ul>
  <li><a href="https://github.com/formare/auctions/tree/master/theorema">Source repository on GitHub</a>.</li>
  <li><a href="theorema.zip">all-in-one ZIP archive for download</a></li>
  <li><a href="Vickrey.nb">Theorema formalisation</a></li>
  <li><a href="Vickrey.pdf">PDF export</a></li>
</ul>
<h2>How to run</h2>
<ol>
  <li>Get a licence of <a href="http://www.wolfram.com/mathematica/">Mathematica 8</a>.</li>
  <li>For now, please contact <a href="http://www.risc.jku.at/people/wwindste/">Wolfgang Windsteiger</a> for a copy of Theorema and for installation instructions.</li>
  <li>Open the Theorema formalisation in Mathematica.</li>
  <li>Evaluate the cell that reads <code>Needs["Theorema`"]</code> by placing the cursor there and pressing Shift+Return, or evaluate all initialization cells via <em>Evaluation→Evaluate Initialization Cells</em>.</li>
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
