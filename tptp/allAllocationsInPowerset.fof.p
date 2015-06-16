%--------------------------------------------------------------------------
% File     : <For TPTP use only> 
% Domain   : Social Choice Theory
% Problem  : Given a set N of participants and G of goods, the set of all allocations is a subset of the cartesian product of N with the powerset of G, excluding {}. 
% Version  : 
% English  : 

% Refs     : [CKLR:SASI-EC15], Email to G. Sutcliffe
% Source   : [ATT]
% Names    : allAllocationsInPowerset 

% Status   : Unsolved
% Rating   : 
% Syntax   : 
% SPC      : 

% Comments : Problem extracted from the Auction Theory Toolbox: http://afp.sourceforge.net/browser_info/current/AFP/Vickrey_Clarke_Groves/CombinatorialAuction.html

%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include partition axioms
include('Axioms/SET006+2.ax').
%----Include new axioms
include('./fof.ax').
%--------------------------------------------------------------------------

fof(allAllocationsInPowerset, conjecture,
	(
		subset(allallocations(N,G),
			power_set(cartprod(N, difference(power_set(G), singleton(empty_set))))
		)
	)
).

%--------------------------------------------------------------------------

