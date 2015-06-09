%--------------------------------------------------------------------------
% File     : <For TPTP use only> 
% Domain   : Set Theory
% Problem  : an alternative characterization of the set partitioned by a partition obtained by 
  inserting an element into an equivalence class of a given partition (if C is a partition) 
% Version  : 
% English  : 

% Refs     : [CKLR:SASI-EC15], Email to G. Sutcliffe
% Source   : [ATT]
% Names    : insert_into_member_partition1

% Status   : Unsolved
% Rating   : 
% Syntax   : 
% SPC      : 

% Comments : Problem extracted from the Auction Theory Toolbox.
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include partition axioms
include('Axioms/SET006+2.ax').
%----Include new axioms
include('./fof.ax').
%--------------------------------------------------------------------------

fof(insert_into_member_partition1, conjecture, 
(! [A, B, C] : (
                sum(insertIntoMember(A,B,C)) = 
                sum(union(singleton(union(singleton(A), B)), difference(C, singleton(B)))
))
)).

%--------------------------------------------------------------------------

