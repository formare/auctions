%--------------------------------------------------------------------------
% File     : <For TPTP use only> 
% Domain   : Set Theory
% Problem  : The family that results from removing one element from an equivalence class of a non-overlapping family is not otherwise a member of the family. 
% Version  : 
% English  : 

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

