%--------------------------------------------------------------------------
% File     : <For TPTP use only> 
% Domain   : Set Theory (Relations)
% Problem  : {(x,X)}-{(x,Y)} coincides with the cartesian product of {x} and {X}-{Y}.  
% Version  : 
% English  : 

% Refs     : [CKLR:SASI-EC15], Email to G. Sutcliffe
% Source   : [ATT]
% Names    : pairDifference

% Status   : Unsolved
% Rating   : 
% Syntax   : 
% SPC      : 

% Comments : Problem extracted from the Auction Theory Toolbox: http://afp.sourceforge.net/browser_info/current/AFP/Vickrey_Clarke_Groves/MiscTools.html
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include partition axioms
include('Axioms/SET006+2.ax').
%----Include new axioms
include('./fof.ax').
%--------------------------------------------------------------------------

fof(pairDifference, conjecture, ( ! [A, B, C]: (
	difference(singleton( pair(A,B) ), singleton( pair(A,C) )) = cartprod(singleton(A), difference(singleton(B), singleton(C)))
	))
).

%--------------------------------------------------------------------------

