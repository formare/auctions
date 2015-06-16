%--------------------------------------------------------------------------
% File     : <For TPTP use only> 
% Domain   : Arithmetic
% Problem  : argmax F is the counterimage, through F, of {max(F[A])}, where F[A] is the image of the set A through F. 
% Version  : 
% English  : 

% Refs     : [CKLR:SASI-EC15], Email to G. Sutcliffe
% Source   : [ATT]
% Names    : lm01

% Status   : Unsolved
% Rating   : 
% Syntax   : 
% SPC      : 

% Comments : max is set-theoretically rendered via sum. Problem extracted from the Auction Theory Toolbox: http://afp.sourceforge.net/browser_info/current/AFP/Vickrey_Clarke_Groves/Argmax.html
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include partition axioms
include('Axioms/SET006+2.ax').
%----Include new axioms
include('./fof.ax').
%--------------------------------------------------------------------------

fof(lm01, conjecture, (
	((isfunction(F)) & (finite(F)) & (subset(range(F),omega))) => 
	(argmax(F,A) = intersection(A,image(converse(F),singleton(sum(image(F,A))))))
)).

%--------------------------------------------------------------------------

