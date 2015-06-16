%--------------------------------------------------------------------------
% File     : <For TPTP use only> 
% Domain   : Set Theory
% Problem  : A subfamily of a non-overlapping family is also a non-overlapping family 
% Version  : 
% English  : If Q is a family of non-overlapping sets and P is a subfamily then it is non-overlapping as well. 

% Refs     : [CKLR:SASI-EC15], Email to G. Sutcliffe
% Source   : [ATT]
% Names    : subset_is_non_overlapping

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

fof(subset_is_non_overlapping, conjecture,
    ( ! [P,Q] : 
    	    ((subset(P,Q) & non_overlapping(Q)) => non_overlapping(P))
    )
   ).

%--------------------------------------------------------------------------

