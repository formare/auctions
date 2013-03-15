<?php
require_once($_SERVER['DOCUMENT_ROOT'] . '/sys/includes/wwwlib.php'); 

$title = 'Auction Theory Toolbox (ATT) – Theorema';

SetHeaderTitle($title);
SetPageTitle($title);
SetMaintainer('Christoph Lange', 'c.lange@cs.bham.ac.uk');
AddStylesheet('../../../formare.css');

HTMLHeader();
PageStart();
?>
<h2>Files relevant to the Theorema formalisation</h2>
<ul>
  <li><a href="theorema.zip">all-in-one ZIP archive for download</a></li>
  <li><a href="Vickrey.nb">Theorema formalisation</a></li>
  <li><a href="Vickrey.pdf">PDF export</a></li>
</ul>
<h2>How to run</h2>
<ol>
  <li>Get a licence of <a href="http://www.wolfram.com/mathematica/">Mathematica 8</a>.</li>
  <li>For now, please contact <a href="http://www.risc.jku.at/people/wwindste/">Wolfgang Windsteiger</a> for a copy of Theorema.</li>
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
