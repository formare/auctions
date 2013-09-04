<?php
require_once($_SERVER['DOCUMENT_ROOT'] . '/sys/includes/wwwlib.php'); 
$formare_root = '../../../';
require_once($formare_root . 'macros.php');

$title = 'Auction Theory Toolbox (ATT) – Mizar';

SetHeaderTitle($title);
SetPageTitle($title);
SetMaintainer('Christoph Lange', 'c.lange@cs.bham.ac.uk');
AddStylesheet($formare_root . 'formare.css');

HTMLHeader();
PageStart();
?>
<h2>Files relevant to the Mizar formalisation</h2>
<ul>
  <li><a href="https://github.com/formare/auctions/tree/master/mizar">Source repository on GitHub</a>.</li>
  <li><a href="mizar.zip">all-in-one ZIP archive for download</a></li>
  <li>Mizar formalisation:<ul>
      <li><a href="dict/vickrey.voc">Vocabulary</a> (names of defined objects)</li>
      <li><a href="text/vickrey.miz">Formalisation</a> (<a href="text/vickrey-proofless.miz">version stripped of proofs</a>: for instructive purposes, not verifiable with Mizar)</li>
  </ul></li>
  <li>Utility scripts:<ul>
      <li><a href="tools/proofcut.sh">proofcut</a> strips proofs for presentation</li>
      <li><a href="tools/onlycode.sh">onlycode</a> removes all non-code for statistical analysis (e.g. computing the <a href="http://www.cs.ru.nl/~freek/factor/">de Bruijn factor</a>)</li></ul></li>
</ul>
<h2>How to run</h2>
<ol>
  <li>Obtain and install the <a href="http://mizar.org/system/#download">Mizar system</a>.  Our code was tested on version 8.1.01 (see comments in <a href="text/vickrey.miz">vickrey.miz</a>'s header for details).  Note that the latest releases are available only in the <a href="ftp://mizar.uwb.edu.pl/pub/system/">architecture-specific directories</a>.</li>
  <li>Create a directory, change into it, and extract <a href="mizar.zip">the ZIP archive</a>.</li>
  <li>Run <code>mizf ./text/vickrey</code> and expect no errors :-)</li>
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
