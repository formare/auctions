%--------------------------------------------------------------------------
% File     : <For TPTP use only> 
% Domain   : Arithmetic
% Problem  : If the converse of P is a function, then the setsum over P of (F o snd) equals the setsum over P of F. o means functional composition here.  
% Version  : 
% English  : 

% Refs     : [CKLR:SASI-EC15], Email to G. Sutcliffe
% Source   : [ATT]
% Names    : setsumPairsInverse

% Status   : Unsolved
% Rating   : 
% Syntax   : 
% SPC      : 

% Comments : Problem extracted from the Auction Theory Toolbox: http://afp.sourceforge.net/browser_info/current/AFP/Vickrey_Clarke_Groves/MiscTools.html
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include partition axioms
include('Axioms/SET006+2.ax').
%----Include new axioms
include('./fof.ax').
%--------------------------------------------------------------------------

fof(setsumPairsInverse, conjecture, (
	! [F, P] : (
	( (isfunction(F)) & (isrelation(P)) & (isruniq(converse(P))) & (isfinite(P)) & (subset(range(F),omega)) & 
	(subset(range(P), domain(F)))) =>
	(fsetsum(relcomp(snd(P), F), P) = fsetsum(F, range(P)))
	)
)).

%--------------------------------------------------------------------------

