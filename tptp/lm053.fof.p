%--------------------------------------------------------------------------
% File     : <For TPTP use only> 
% Domain   : Social Choice Theory
% Problem  : Reassignment of goods preserve the property of being an allocation.
% Version  : 
% English  : Given an allocation A, all the goods allocated to the participants of a set X are reassigned to a participant I not in X. We show that the outcome is still an allocation (relative to the original set of participants with X removed).

% Refs     : [CKLR:SASI-EC15], Email to G. Sutcliffe
% Source   : [ATT]
% Names    : lm053

% Status   : Unsolved
% Rating   : 
% Syntax   : 
% SPC      : 

% Comments : Problem extracted from the Auction Theory Toolbox: http://afp.sourceforge.net/browser_info/current/AFP/Vickrey_Clarke_Groves/Universes.html
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include partition axioms
include('Axioms/SET006+2.ax').
%----Include new axioms
include('./fof.ax').
%--------------------------------------------------------------------------

fof(lm053, conjecture, (
	![A,N,G,I,X] : (
		(
		 (member(A,allallocations(N,G))) & 
		 (member(I, difference(N,X))) &
		 (~(intersection(domain(A), X) = empty_set))
		)
		=> 
		(       
			member(
			union(outside(A ,union(X, singleton(I))), 
			      cartprod(singleton(I), singleton(sum(image(A, union(X,singleton(I))))))), 
			allallocations (difference(N,X), sum(range(A))))
		)
        )
)).

%--------------------------------------------------------------------------

