<?php
require_once($_SERVER['DOCUMENT_ROOT'] . '/sys/includes/wwwlib.php'); 

$title = 'Auction Theory Toolbox (ATT) – Mizar';

SetHeaderTitle($title);
SetPageTitle($title);
SetMaintainer('Christoph Lange', 'c.lange@cs.bham.ac.uk');
AddStylesheet('../../../formare.css');

HTMLHeader();
PageStart();
?>
<h2>Files relevant to the Mizar formalisation</h2>
<ul>
  <li><a href="mizar.zip">all-in-one ZIP archive for download</a></li>
  <li>Mizar formalisation:<ul>
      <li><a href="dict/vickrey.voc">Vocabulary</a> (names of defined objects)</li>
      <li><a href="text/vickrey.miz">Formalisation</a> (<a href="text/vickrey-proofless.miz">version stripped of proofs</a>)</li>
  </ul></li>
  <li>Utility scripts:<ul>
      <li><a href="tools/proofcut.sh">proofcut</a> strips proofs for presentation</li>
      <li><a href="tools/onlycode.sh">onlycode</a> removes all non-code for statistical analysis (e.g. the <a href="http://www.cs.ru.nl/~freek/factor/">de Bruijn factor</a>)</li></ul></li>
</ul>
<h2>How to run</h2>
<ol>
  <li>Obtain the <a href="http://mizar.org/system/">Mizar system</a>.  Our code is known to work with Mizar 8.1.01.</li>
  <li>…</li>
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
