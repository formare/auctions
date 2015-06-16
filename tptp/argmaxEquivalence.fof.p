%--------------------------------------------------------------------------
% File     : <For TPTP use only> 
% Domain   : Arithmetic
% Problem  : The argmax of two functions (F and G) over a set A is the same if F and G coincide on A.
% Version  : 
% English  : 

% Refs     : [CKLR:SASI-EC15], Email to G. Sutcliffe
% Source   : [ATT]
% Names    : argmaxEquivalence

% Status   : Unsolved
% Rating   : 
% Syntax   : 
% SPC      : 

% Comments : Problem extracted from the Auction Theory Toolbox: http://afp.sourceforge.net/browser_info/current/AFP/Vickrey_Clarke_Groves/Argmax.html
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include partition axioms
include('Axioms/SET006+2.ax').
%----Include new axioms
include('./fof.ax').
%--------------------------------------------------------------------------

fof(argmaxEquivalence, conjecture, (
( ! [F,G,A] :
	(
	( 	(isfunction(F)) & (isfunction(G)) & (subset(A,intersection(domain(F),domain(G)))) & 
		(subset(union(range(F),range(G)),omega)) &
		(finite(A)) &
		( ! [X] : ((member(X,A)) => (relapply(F,X)=relapply(G,X))))
	) 
	=> 
	(argmax(F,A) = argmax(G,A))
	)
)
)).

%--------------------------------------------------------------------------

