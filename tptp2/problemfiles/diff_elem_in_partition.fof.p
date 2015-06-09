%--------------------------------------------------------------------------
% File     : <For TPTP use only> 
% Domain   : Set Theory
% Problem  : Every element of the difference of a set A and another set B ends up in 
  an element of a partition of A, but not in an element of the partition of B. 
% Version  : 
% English  : 

% Refs     : [CKLR:SASI-EC15], Email to G. Sutcliffe
% Source   : [ATT]
% Names    : diff_elem_in_partition

% Status   : Unsolved
% Rating   : 
% Syntax   : 
% SPC      : 

% Comments : Problem extracted from the Auction Theory Toolbox. This theorem was not used in the end, but it looks like it could be a good problem for TPTP.
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include partition axioms
include('Axioms/SET006+2.ax').
%----Include new axioms
include('./fof.ax').
%--------------------------------------------------------------------------

fof(diff_elem_in_partition, conjecture,
(! [X, A, B, P] :
(
                ((member(X,difference(A,B)) & partition(P,A)) => 
                    (? [S] : member(S,difference(P,singleton(B))) & member(X,S)))
                    )
)).

%--------------------------------------------------------------------------

