%--------------------------------------------------------------------------
% File     : <For TPTP use only> 
% Domain   : Arithmetic
% Problem  : The maximum of the image of A through F is not smaller than any value F assumes over A.
% Version  : 
% English  : 

% Refs     : [CKLR:SASI-EC15], Email to G. Sutcliffe
% Source   : [ATT]
% Names    : maxLemma

% Status   : Unsolved
% Rating   : 
% Syntax   : 
% SPC      : 

% Comments : Here, sum means max, member means <, and member(X,suc(Y)) means X<=Y. Problem extracted from the Auction Theory Toolbox: 
http://afp.sourceforge.net/browser_info/current/AFP/Vickrey_Clarke_Groves/Argmax.html
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include partition axioms
include('Axioms/SET006+2.ax').
%----Include new axioms
include('./fof.ax').
%--------------------------------------------------------------------------

fof(maxLemma, conjecture, ( ! [A, B, F]: (
	((member(A,B)) & (isfinite(B)) & (isfunction(F)) & (subset(range(F),omega)) & (subset(B,domain(F)))) => (member(relapply(F,A),suc(sum(image(F,B)))))
))).

%--------------------------------------------------------------------------

