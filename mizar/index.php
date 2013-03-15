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
      <li><a href="dict/vickrey.voc">Vocabulary</a></li>
      <li><a href="text/vickrey.miz">Formalisation</a></li>
  </ul></li>
  <li><a href="vickrey-proofless.miz">Formalisation without proof</a></li>
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
