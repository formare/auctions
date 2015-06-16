%--------------------------------------------------------------------------
% File     : <For TPTP use only> 
% Domain   : Social Choice Theory
% Problem  : The possible allocations of a set of goods G among a set of participants N are finite, if so are N and G.  
% Version  : 
% English  : 

% Refs     : [CKLR:SASI-EC15], Email to G. Sutcliffe
% Source   : [ATT]
% Names    : soldAllocationsFinite

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

fof(soldAllocationsFinite, conjecture, (! [S, N, G] : ( 
	((isfinite(N)) & (isfinite(G))) => (isfinite(soldallocations(S,N,G)))	
))).

%--------------------------------------------------------------------------

