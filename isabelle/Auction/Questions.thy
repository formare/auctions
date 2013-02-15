theory Questions
imports Main
begin

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
