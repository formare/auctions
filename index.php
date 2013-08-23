<?php
require_once($_SERVER['DOCUMENT_ROOT'] . '/sys/includes/wwwlib.php'); 
$formare_root = '../../';
require_once($formare_root . 'macros.php');

$title = 'Auction Theory Toolbox (ATT)';

SetHeaderTitle($title);
SetPageTitle($title);
SetMaintainer('Christoph Lange', 'math.semantic.web@gmail.com');
AddStylesheet($formare_root . 'formare.css');

HTMLHeader();
PageStart();
?>
<p>This is an output of the <a href="../..">ForMaRE</a> research project.  For the research background and first results, please see our paper “<a href="../../publications.php#cicm2013-comparison">A Qualitative Comparison of the Suitability of Four Theorem Provers for Basic Auction Theory</a>” (in: Conference on Intelligent Computer Mathematics, 2013).  We particularly focus on</p>
<ul>
  <li><a href="#maskin">proving theorems about static single-good auctions</a></li>
  <li><a href="#sound-verif">checking the soundness of more complex auctions and generating verified software.</a></li>
</ul>
<p>Both will be detailed below.</p>
<h2 id="maskin">Proving theorems about static single-good auctions</h2>
<p>Our formalisation is guided by Eric Maskin's 2004 review article “<a href="http://scholar.harvard.edu/maskin/publications/unity-auction-theory">The unity of auction theory: Milgrom's master class</a>” (Journal of Economic Literature 42.4, p.&nbsp;1102–1115).  As this article makes rather high-level statements, we have elaborated them to more detail on paper.</p>
<p>We have used different languages for the formalisation.  The table below lists the current state of formalising the propositions given in Maskin's review article.  Further contributions are highly welcome; this includes</p>
<ul>
  <li>formalisations of propositions not yet covered</li>
  <li>re-formalisations in new languages</li>
  <li>improvements to existing formalisations</li>
</ul>
<p>For any questions, please contact us via <a href="mailto:formare-discuss@cs.bham.ac.uk?subject=Auction%20Theory%20Toolbox">formare-discuss@cs.bham.ac.uk</a>.  (You need to <a href="https://mailman.cs.bham.ac.uk/mailman/listinfo/formare-discuss">subscribe</a> first.)</p>
<p>Downloadable files are linked below.  If you would like to contribute to the latest developments, please have a look at our <a href="https://github.com/formare/auctions">Github repository</a>.</p>
<p>The table below shows the following information:</p>
<ul>
  <li><strong>Proposition</strong>: the number of the respective Proposition in Maskin's review article and the original authors of the theorem</li>
  <li><strong>Elaboration</strong>: a link to the elaborated paper version</li>
  <li>For each <strong>formalisation</strong>: its authors.  The formalisations of all theorems can be accessed via the column header showing the name of the respective language.</li>
</ul>
<table style="width:100%; table-layout:fixed; word-wrap:break-word">
  <colgroup>
    <col style="width:16%"/>
    <col style="width:16%"/>
    <col style="width:17%"/>
    <col style="width:17%"/>
    <col style="width:17%"/>
    <col style="width:17%"/>
  </colgroup> 
  <thead>
    <tr>
      <th>Proposition (<a href="http://scholar.harvard.edu/maskin/publications/unity-auction-theory">Maskin</a>)</th>
      <th>Elaboration</th>
      <th><a href="casl">CASL</a></th>
      <th><a href="isabelle">Isabelle</a></th>
      <th><a href="mizar">Mizar</a></th>
      <th><a href="theorema">Theorema</a></th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <td>1 (Vickrey)</td>
      <td><a href="paper/maskin/1.pdf">elaboration</a>
        (<a href="http://www.socscistaff.bham.ac.uk/rowat/">Rowat</a>/<a href="http://www.cs.bham.ac.uk/~mmk/">Kerber</a>/<a href="http://www.cs.bham.ac.uk/~langec/">Lange</a>)</td>
      <td>Lange/<wbr/><a href="http://www.informatik.uni-bremen.de/~till/">Mossakowski</a></td>
      <td>Lange/<wbr/><a href="http://www.lri.fr/~wenzel/">Wenzel</a>/<wbr/>Kerber</td>
      <td><a href="http://uniroma1.academia.edu/MarcoCaminati">Caminati</a></td>
      <td><a href="http://www.risc.jku.at/people/wwindste/">Windsteiger</a></td>
    </tr>
    <tr><td>2 (Green/<wbr/>Laffont/<wbr/>Holmstr&ouml;m/<wbr/>Maskin)</td><td></td><td></td><td></td><td></td><td></td></tr>
    <tr><td>3 (Green/<wbr/>Laffont/<wbr/>Maskin)</td><td></td><td></td><td></td><td></td><td></td></tr>
    <tr><td>4 (d'Aspremont/<wbr/>G&eacute;rard-Varet)</td><td></td><td></td><td></td><td></td><td></td></tr>
    <tr><td>5 (Laffont/<wbr/>Maskin/<wbr/>Myerson/<wbr/>Satterthwaite)</td><td></td><td></td><td></td><td></td><td></td></tr>
    <tr><td>6 (Vickrey/<wbr/>Myerson/<wbr/>Riley/<wbr/>Samuelson)</td><td></td><td></td><td></td><td></td><td></td></tr>
    <tr><td>7 (Myerson/<wbr/>Riley/<wbr/>Samuelson)</td><td></td><td></td><td></td><td></td><td></td></tr>
    <tr><td>8 (Vickrey)</td><td></td><td></td><td></td><td></td><td></td></tr>
    <tr><td>9 (Vickrey/<wbr/>Riley/<wbr/>Samuelson/<wbr/>Myerson)</td><td></td><td></td><td></td><td></td><td></td></tr>
    <tr><td>10 (Riley/<wbr/>Samuelson/<wbr/>Myerson)</td><td></td><td></td><td></td><td></td><td></td></tr>
    <tr><td>11 (Holt/<wbr/>Maskin/<wbr/>Riley/<wbr/>Matthews)</td><td></td><td></td><td></td><td></td><td></td></tr>
    <tr><td>12 (Maskin/<wbr/>Jehiel/<wbr/>Moldovanu)</td><td></td><td></td><td></td><td></td><td></td></tr>
    <tr><td>13 (Milgrom/<wbr/>Weber)</td><td></td><td></td><td></td><td></td><td></td></tr>
  </tbody>
</table>
<h2 id="sound-verif">Soundness of complex auctions; verified auction software</h2>
<p>In this effort, we prove that auctions are soundly specified, i.e. assign a unique, well-defined outcome to each well-formed bid input.  This is easier to prove than certain other properties of auctions studied <a href="#maskin">above</a>, but we deal with more complex auctions, at the moment with static combinatorial auctions.  Once the soundness of an auction has been proved, we generate verified software code from the formalisation.  Our work is guided by some of the chapters of the following book: Peter Cramton, Yoav Shoham, and Richard Steinberg (2006). <a href="http://mitpress.mit.edu/books/combinatorial-auctions">Combinatorial Auctions</a>. MIT Press. ISBN 0-262-03342-9.  Here, we focus on <a href="isabelle">Isabelle</a> as a formalisation tool.</p>
<table style="width:100%; table-layout:fixed; word-wrap:break-word">
  <colgroup>
    <col style="width:34"/>
    <col style="width:33"/>
    <col style="width:33"/>
  </colgroup> 
  <thead>
    <tr>
      <th>Topic (Chapter)</th>
      <th>Elaboration</th>
      <th><a href="isabelle">Isabelle</a></th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <td>Vickrey auction (1)</td>
      <td><a href="http://arxiv.org/abs/1308.1779">see section 4</a>
        (<a href="http://www.socscistaff.bham.ac.uk/rowat/">Rowat</a>/<a href="http://www.cs.bham.ac.uk/~mmk/">Kerber</a>/<a href="http://www.cs.bham.ac.uk/~langec/">Lange</a>)</td>
      <td>Lange/<wbr/><a href="http://uniroma1.academia.edu/MarcoCaminati">Caminati</a> (in progress)</td>
    </tr>
  </tbody>
</table>
<p>Unless otherwise stated, the sources of the Auction Theory Toolbox are dually licenced under the <a href="LICENSE-ISC">ISC License</a> and the <a href="http://creativecommons.org/licenses/by/3.0/">Creative Commons Attribution 3.0 License</a>.  With a dual licence for source code and creative works, we follow the model of the <a href="http://mizar.org/library/">Mizar Mathematical Library</a>, as suggested by <a href="http://arxiv.org/abs/1107.3212">Alama, Kohlhase, Naumowicz, Rudnicki, Urban and Mamane</a>.</p>
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
