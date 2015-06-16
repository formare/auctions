%--------------------------------------------------------------------------
% File     : <For TPTP use only> 
% Domain   : Set Theory
% Problem  : {E} is a partition of E for any non-empty set E; 
% Version  : 
% English  : A non-empty set ``is'' a partition of itself.

% Refs     : [CKLR:SASI-EC15], Email to G. Sutcliffe
% Source   : [ATT]
% Names    : set_partitions_itself

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

fof(set_partitions_itself,conjecture,
    ( ! [E] : 
    	    (~ (E = empty_set)) => (partition(singleton(E),E))
    )
   ).

%--------------------------------------------------------------------------

