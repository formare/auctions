theory Questions
imports Main
begin

(* TODO CL: ask whether there a way of writing the alternative as b_hat, as it looks in the paper version? *)
(* makarius: Isabelle is text based, and Isabelle/jEdit is a plain text editor, but there are
   many tricks that can be played with "visual tuning" of formal documents; most of this works
   for the generated LaTeX.  Here is just a cheap one:

  We re-use an existing letter symbol from the Isabelle repertoire.  Its LaTeX interpretation
  is re-defined in document/root.tex like this:

   \renewcommand{\isasymbb}{\isamath{\hat b}}

  You can also try to find alternative Unicode mapping for $ISABELLE_HOME_USER/etc/symbols
  but it rarely works out so well in practice.
 *)

definition "\<bb> = 0"


(* TODO CL: report jEdit bug that suggested completions for nat (\<nat>) and bool (\<bool>) cause syntax errors *)
(* makarius: completion still lacks context (Isabelle2013), so it can propose things that don't make sense *)

(* TODO CL: report Isabelle/jEdit bug: no auto-indentation *)
(* makarius: not a bug, but lack of feature (when it eventually arrives, people will complain
   about being forced into Isar standard indentation) *)

(* TODO CL: report Isabelle/jEdit bug: can't copy goal in output pane to clipboard *)
(* makarius: this should work in Isabelle2012 already, using plain CONTROL-C, not menus;
   in Isabelle2013 it is even more robust, since the Output panel uses the same technology as
   jEdit editor buffers (still no menu operation, though) *)

(* TODO CL: report Isabelle/jEdit bug: when I set long lines to wrap at window boundary, wrapped part behaves badly: not editable *)
(* makarius: soft-wrap is rarely used; in Isabelle2012 its rendering was indeed broken;
   should work in Isabelle2013 *)

(* TODO CL: ask whether jEdit's Isabelle mode disables word wrapping *)
(* makarius: depending what word wrapping means exactly, it might be a conflict of tokens of jEdit
   vs. tokens of Isabelle; note that Isabelle/jEdit installs its own token marker for approximative
   syntax highlighting; *)

end
