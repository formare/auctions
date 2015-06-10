%--------------------------------------------------------------------------
% File     : <For TPTP use only> 
% Domain   : Set Theory
% Problem  : The family that results from removing one element from a set in a non-overlapping family is not a member of the original family. 
% Version  : 
% English  : E.g., With P = {{1,2},{3,4,5}}, when removing 3 from {3,4,5} the resulting set {4,5} is not in P.

% Refs     : [CKLR:SASI-EC15], Email to G. Sutcliffe
% Source   : [ATT]
% Names    : remove_from_eq_class_preserves_disjoint

% Status   : Unsolved
% Rating   : 
% Syntax   : 
% SPC      : 

% Comments : Problem extracted from the Auction Theory Toolbox
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include partition axioms
include('Axioms/SET006+2.ax').
%----Include new axioms
include('./fof.ax').
%--------------------------------------------------------------------------

fof(remove_from_eq_class_preserves_disjoint, conjecture,
(! [E, X, P] : 
            ( (non_overlapping(P) & member(X,P) & member(E,X)) => 
              ~(member(difference(X,singleton(E)), P))
              )
)              
).

%--------------------------------------------------------------------------

