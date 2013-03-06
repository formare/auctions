<?php
require_once($_SERVER['DOCUMENT_ROOT'] . '/sys/includes/wwwlib.php'); 

$title = 'Auction Theory Toolbox';

SetHeaderTitle($title);
SetPageTitle($title);
SetMaintainer('Christoph Lange', 'c.lange@cs.bham.ac.uk');
AddStylesheet('../../formare.css');

HTMLHeader();
PageStart();
?>
<p>This is an output of the <a href="../..">ForMaRE</a> research project.  For the research background, please see our 2013 paper “<a href="../../events/aisb2013/stage1.php#s6">Developing an Auction Theory Toolbox</a> (in: Enabling Domain Experts to use Formalised Reasoning. Do-Form, symposium at the AISB Annual Convention, 2013).  In particular, our formalisation is guided by Eric Maskin's 2004 review article “<a href="http://scholar.harvard.edu/maskin/publications/unity-auction-theory">The unity of auction theory: Milgrom's master class</a>” (Journal of Economic Literature 42.4, p.&nbsp;1102–1115).  As this article makes rather high-level statements, we have elaborated them to more detail on paper.</p>
<p>We have used different languages for the formalisation.  The table below lists the current state of formalising the propositions given in Maskin's review article.  Further contributions are highly welcome; this includes both formalisations of propositions not yet covered, as well as re-formalisations in new languages.  If you are interested, please contact us via <a href="mailto:formare-discuss@cs.bham.ac.uk?Auction%20Theory%20Toolbox">formare-discuss@cs.bham.ac.uk</a>.  (You need to <a href="https://mailman.cs.bham.ac.uk/mailman/listinfo/formare-discuss">subscribe</a> first.)</p>
<p>This table shows the following information:</p>
<ul>
  <li><strong>Proposition</strong>: the number of the respective Proposition in Maskin's review article and the original authors of the theorem</li>
  <li><strong>Elaboration</strong>: a link to the elaborated paper version</li>
  <li>For each <strong>formalisation</strong>: its authors.  The formalisations of all theorems can be accessed via the column header showing the name of the respective language.</li>
</ul>
<table style="width: 100%">
  <thead>
    <tr>
      <th style="width: 16%">Proposition</th>
      <th style="width: 16%">Elaboration</th>
      <th style="width: 17%"><a href="casl">CASL</a></th>
      <th style="width: 17%"><a href="isabelle">Isabelle</a></th>
      <th style="width: 17%">Mizar</th>
      <th style="width: 17%">Theorema</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <td>1 (Vickrey)</td>
      <td><a href="source/1.pdf">elaboration</a><!-- this paper is not physically in this svn, but uploaded via https://codex.cs.bham.ac.uk/svn/mmk/KLR/auction-theory/Makefile -->
        (<a href="http://www.socscistaff.bham.ac.uk/rowat/">Rowat</a>/<a href="http://www.cs.bham.ac.uk/~mmk/">Kerber</a>/<a href="http://www.cs.bham.ac.uk/~langec/">Lange</a>)</td>
      <td>Lange/<a href="http://www.informatik.uni-bremen.de/~till/">Mossakowski</a></td>
      <td>Lange/<a href="http://www.lri.fr/~wenzel/">Wenzel</a>/Kerber</td>
      <td><a href="http://uniroma1.academia.edu/MarcoCaminati">Caminati</a></td>
      <td><a href="http://www.risc.jku.at/people/wwindste/">Windsteiger</a></td>
    </tr>
    <tr><td>2 (Green/Laffont/Holmstr&ouml;m/Maskin)</td><td></td><td></td><td></td><td></td><td></td></tr>
    <tr><td>3 (Green/Laffont/Maskin)</td><td></td><td></td><td></td><td></td><td></td></tr>
    <tr><td>4 (d'Aspremont/G&eacute;rard-Varet)</td><td></td><td></td><td></td><td></td><td></td></tr>
    <tr><td>5 (Laffont/Maskin/Myerson/Satterthwaite)</td><td></td><td></td><td></td><td></td><td></td></tr>
    <tr><td>6 (Vickrey/Myerson/Riley/Samuelson)</td><td></td><td></td><td></td><td></td><td></td></tr>
    <tr><td>7 (Myerson/Riley/Samuelson)</td><td></td><td></td><td></td><td></td><td></td></tr>
    <tr><td>8 (Vickrey)</td><td></td><td></td><td></td><td></td><td></td></tr>
    <tr><td>9 (Vickrey/Riley/Samuelson/Myerson)</td><td></td><td></td><td></td><td></td><td></td></tr>
    <tr><td>10 (Riley/Samuelson/Myerson)</td><td></td><td></td><td></td><td></td><td></td></tr>
    <tr><td>11 (Holt/Maskin/Riley/Matthews)</td><td></td><td></td><td></td><td></td><td></td></tr>
    <tr><td>12 (Maskin/Jehiel/Moldovanu)</td><td></td><td></td><td></td><td></td><td></td></tr>
    <tr><td>13 (Milgrom/Weber)</td><td></td><td></td><td></td><td></td><td></td></tr>
  </tbody>
</table>
<p>Unless otherwise stated, the sources of the Auction Theory Toolbox are dually licenced under the <a href="LICENSE-ISC">ISC License</a> and the <a href="http://creativecommons.org/licenses/by/3.0/">Creative Commons Attribution 3.0 License</a>.  With a dual licence for source code and creative works, we follow the model of the Mizar Mathematical Library, as suggested by <a href="http://arxiv.org/abs/1107.3212">Alama, Kohlhase, Naumowicz, Rudnicki, Urban and Mamane</a>.</p>
<?php
PageEnd();
HTMLFooter();
?>
<?php /*
Local Variables:
mode: html 
End:
*/ ?>
