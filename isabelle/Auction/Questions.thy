theory Questions
imports Main
begin

(* This file includes some questions, mainly related to usability, that had occurred during the formalisation, and their answers. *)

(*** Soft-wrapping long lines ***)

(* Christoph: when setting long lines to wrap at the window boundary in Isabelle/jEdit 2012, the wrapped part behaved badly and wasn't even editable. *)

    (* Makarius: soft-wrap is rarely used; in Isabelle2012 its rendering was indeed broken; should work in Isabelle2013 *)

        (* Christoph: We've had this discussion before on the isabelle-users mailing list.  I still disagree to some extent.  In the interest of comprehensibility I preferred long, descriptive symbol names here, which inevitably make lines long.  In the wide-screen age, you wouldn't want to hard-wrap all of them to, say, 80 columns.  But we might agree on something like 120. *)

(* Christoph: Does jEdit's Isabelle mode disable word wrapping? *)

    (* Makarius: depending what word wrapping means exactly, it might be a conflict of tokens of jEdit
    vs. tokens of Isabelle; note that Isabelle/jEdit installs its own token marker for approximative
    syntax highlighting; *)

        (* Christoph: I had actually been referring to soft line wrapping here. *)

(*** Hat accents on top of mathematical symbol names ***)

(* Christoph: Is there a way of writing the alternative bid as \hat{b}, as it is done in the LaTeX paper? *)

    (* Makarius: Isabelle is text based, and Isabelle/jEdit is a plain text editor, but there are many tricks that can be played with "visual tuning" of formal documents; most of this works for the generated LaTeX.  Here is just a cheap one:

    We re-use an existing letter symbol from the Isabelle repertoire.  Its LaTeX interpretation
    is re-defined in document/root.tex like this:

    \renewcommand{\isasymbb}{\isamath{\hat b}}

    You can also try to find alternative Unicode mapping for $ISABELLE_HOME_USER/etc/symbols
    but it rarely works out so well in practice. *)

definition "\<bb> = 0"

(*** Some auto-completions cause syntax errors. ***)

(* Christoph: jEdit's suggested completions for nat (\<nat>) and bool (\<bool>) cause Isabelle syntax errors. *)

    (* Makarius: completion still lacks context (Isabelle2013), so it can propose things that don't make sense *)

(*** No auto-indentation ***)

(* Christoph: Isabelle/jEdit does not support auto-indentation. *)

    (* Makarius: This is not a bug, but a lack of feature (when it eventually arrives, people will complain about being forced into Isar standard indentation) *) 

(*** Can't copy goal in output pane to clipboard ***)

(* Christoph: probably a bug in Isabelle2012 *)

    (* Makarius: this should work in Isabelle2012 already, using plain CONTROL-C, not menus;
    in Isabelle2013 it is even more robust, since the Output panel uses the same technology as
    jEdit editor buffers (still no menu operation, though) *)

        (* Christoph: I never use menus for this, but I wouldn't want to install Isabelle2012 again just to verify _that_ ;-) *)

end
