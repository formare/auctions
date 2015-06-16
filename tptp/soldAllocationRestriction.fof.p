%--------------------------------------------------------------------------
% File     : <For TPTP use only> 
% Domain   : Social Choice Theory
% Problem  : An allocation A is invariant to subtracting a single bidder X.
% Version  : 
% English  : 

% Refs     : [CKLR:SASI-EC15], Email to G. Sutcliffe
% Source   : [ATT]
% Names    : soldAllocationRestriction

% Status   : Unsolved
% Rating   : 
% Syntax   : 
% SPC      : 

% Comments : Problem extracted from the Auction Theory Toolbox: http://afp.sourceforge.net/browser_info/current/AFP/Vickrey_Clarke_Groves/CombinatorialAuction.html 
% This is a fundamental step to prove the non-negativity of price in VCG.
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include partition axioms
include('Axioms/SET006+2.ax').
%----Include new axioms
include('./fof.ax').
%--------------------------------------------------------------------------

fof(soldAllocationRestriction, conjecture,
	( ! [N,G,A,X,S] : (
	(member(A, soldallocations(S,N,G))) => (member(outside(A,singleton(X)), 
	soldallocations(S,difference(N, singleton(X)), G)
	)) 
	))
).

%--------------------------------------------------------------------------

