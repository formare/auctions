%--------------------------------------------------------------------------
% File     : <For TPTP use only> 
% Domain   : Set Theory
% Problem  : an alternative characterization of the set partitioned by a partition obtained by 
  inserting an element into an equivalence class of a given partition (if P is a partition) 
% Version  : 
% English  : Assume P = {{1,2},{3,4,5}} and B = {1,2} and A = 6,
%            then insertIntoMember(A,B,P) = {{1,2,6},{3,4,5}}. The theorem says that the big union of this (i.e.
%            {1,2,3,4,5,6}) is the same as the big union of {{6} u {1,2}} u P\{{1,2}}, i.e. big union of {{1,2,6},{3,4,5}}.

% Refs     : [CKLR:SASI-EC15], Email to G. Sutcliffe
% Source   : [ATT]
% Names    : insert_into_member_partition1

% Status   : Unsolved
% Rating   : 
% Syntax   : 
% SPC      : 

% Comments : Problem extracted from the Auction Theory Toolbox: http://afp.sourceforge.net/browser_info/current/AFP/Vickrey_Clarke_Groves/Partitions.html
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include partition axioms
include('Axioms/SET006+2.ax').
%----Include new axioms
include('./fof.ax').
%--------------------------------------------------------------------------

fof(insert_into_member_partition1, conjecture, 
(! [A, B, P] : (
                sum(insertIntoMember(A,B,P)) = 
                sum(union(singleton(union(singleton(A), B)), difference(P, singleton(B)))
))
)).

%--------------------------------------------------------------------------

