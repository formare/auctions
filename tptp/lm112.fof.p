%--------------------------------------------------------------------------
% File     : <For TPTP use only> 
% Domain   : Arithmetic
% Problem  : The setsum, over a set Z, of the characteristic function of a set X, equals the cardinality of Z /\ X.
% Version  : 
% English  : 

% Refs     : [CKLR:SASI-EC15], Email to G. Sutcliffe
% Source   : [ATT]
% Names    : lm112

% Status   : Unsolved
% Rating   : 
% Syntax   : 
% SPC      : 

% Comments : lm112 links the concept of cardinality to the sum over a set: it is somehow a bridge between set theory and economics (where we use fsetsum to calculate revenues). Problem extracted from the Auction Theory Toolbox: http://afp.sourceforge.net/browser_info/current/AFP/Vickrey_Clarke_Groves/MiscTools.html
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include partition axioms
include('Axioms/SET006+2.ax').
%----Include new axioms
include('./fof.ax').
%--------------------------------------------------------------------------

fof(lm112, conjecture, (
	! [X,Y,Z] : ( 
  ((subset(Z,union(X,Y))) & (isfinite(Z))) => 
  (fsetsum(chi(X,Y), Z) = card (intersection(Z,X)))
  )
)).

%--------------------------------------------------------------------------

