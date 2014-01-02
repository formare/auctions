(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Manfred Kerber <mnfrd.krbr@gmail.com>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>
* Makarius Wenzel <wenzel@lri.fr>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* Some properties that single good auctions can have *}

theory SingleGoodAuctionProperties
imports
  SingleGoodAuction
  Maximum

begin

section {* Soundness *}

subsection {* Well-defined outcome *}

text{* In the general case, by ``well-defined outcome'' we mean that the good gets properly 
  allocated w.r.t.\ the definition of an @{text allocation}.  We are not constraining the payments
  at this point. *}
definition sga_outcome_allocates :: "participant set \<Rightarrow> bids \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool"
  where
    "sga_outcome_allocates N b x p \<longleftrightarrow> allocation N x"

type_synonym outcome_well_definedness = "participant set \<Rightarrow> bids \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool"

(* TODO CL: maybe add the premise that the input should be admissible; in the combinatorial case
   we needed this. *)
definition sga_well_defined_outcome :: "single_good_auction \<Rightarrow> outcome_well_definedness \<Rightarrow> bool"
  where
    "sga_well_defined_outcome A well_defined_outcome_pred \<longleftrightarrow>
      (\<forall> ((N::participant set, b::bids), (x::allocation, p::payments)) \<in> A .
        well_defined_outcome_pred N b x p)"

subsection {* Left-totality *}

text{* Convenience wrapper for left-totality of a single good auction in relational form:
  for each admissible input (determined by an admissibility predicate),
  there exists some outcome (not necessarily unique nor well-defined). *}
definition sga_left_total :: "single_good_auction \<Rightarrow> input_admissibility \<Rightarrow> bool"
  where "sga_left_total A admissible \<longleftrightarrow>
    { (N, b) . admissible N b } \<subseteq> Domain A"

text{* introduction rule for @{const sga_left_total}, to facilitate left-totality proofs *}
lemma sga_left_totalI:
  assumes "\<And> N b . admissible N b \<Longrightarrow> (\<exists> x p . ((N, b), (x, p)) \<in> A)"
  shows "sga_left_total A admissible"
using assms unfolding sga_left_total_def by fast

subsection {* Right-uniqueness *}

(* CL: the way we define "right-uniqueness up to some equivalence relation", and equality of vectors,
   we can't reuse RelationProperties.runiq as our right-uniqueness notion.  At least not now, but:
   TODO CL: maybe introduce "right-uniqueness up to some equivalence relation" as a concept of its own,
   not defined in terms of "trivial (= empty or singleton) image", but as "image is at most one 
   equivalence class". *)

type_synonym outcome_equivalence = "participant set \<Rightarrow> bids \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool"

text{* Right-uniqueness of a single good auction defined as a relation: for each admissible bid vector,
  if there is an outcome, it is unique.  We define this once for underspecified auctions, i.e.
  where tie-breaking is not specified, \<dots> *}
definition sga_right_unique :: "single_good_auction \<Rightarrow> input_admissibility \<Rightarrow> outcome_equivalence \<Rightarrow> bool"
  where "sga_right_unique A admissible equivalent \<longleftrightarrow>
    (\<forall> (N :: participant set) (b :: bids) . admissible N b \<longrightarrow>
      (\<forall> (x :: allocation) (x' :: allocation) (p :: payments) (p' :: payments) .
        ((N, b), (x, p)) \<in> A \<and> ((N, b), (x', p')) \<in> A \<longrightarrow> equivalent N b x p x' p'))"

text{* introduction rule for @{term sga_right_unique} *}
lemma sga_right_uniqueI:
  assumes "\<And> N b x x' p p' . admissible N b \<Longrightarrow> ((N, b), (x, p)) \<in> A \<Longrightarrow> ((N, b), (x', p')) \<in> A \<Longrightarrow> equivalent N b x p x' p'"
  shows "sga_right_unique A admissible equivalent"
using assms unfolding sga_right_unique_def by force

text{* \<dots> and once for fully specified (“fs”) single good auctions with tie-breaking, where outcome equivalence
  is defined by equality: *}
definition fs_sga_right_unique :: "single_good_auction \<Rightarrow> input_admissibility \<Rightarrow> bool"
  where "fs_sga_right_unique A admissible \<longleftrightarrow>
    sga_right_unique A admissible
      (* equivalence by equality: *)
      (\<lambda> N b x p x' p' . eq N x x' \<and> eq N p p')"

subsection {* Soundness combined *}

definition sga_case_check :: "single_good_auction \<Rightarrow> input_admissibility \<Rightarrow> outcome_equivalence \<Rightarrow> outcome_well_definedness \<Rightarrow> bool"
  where "sga_case_check A admissible equivalent well_defined \<longleftrightarrow>
    sga_left_total A admissible \<and>
    sga_right_unique A admissible equivalent \<and>
    sga_well_defined_outcome A well_defined"

definition fs_sga_case_check :: "single_good_auction \<Rightarrow> input_admissibility \<Rightarrow> outcome_well_definedness \<Rightarrow> bool"
  where "fs_sga_case_check A admissible well_defined \<longleftrightarrow>
    sga_left_total A admissible \<and>
    fs_sga_right_unique A admissible \<and>
    sga_well_defined_outcome A well_defined"

subsection {* Efficiency *}

text{* A single good auction (this is the one we are talking about here) is efficient, if the winner is among the participants who have the
highest valuation of the good. *}
definition efficient :: "participant set \<Rightarrow> valuations \<Rightarrow> bids \<Rightarrow> single_good_auction \<Rightarrow> bool"
  where
    "efficient N v b A \<longleftrightarrow>
      valuations N v \<and> bids N b \<and> single_good_auction A \<and>
      (\<forall> x p . ((N, b), (x, p)) \<in> A
        (* TODO CL: Is there a way of not naming p, as we don't need it? *)
        \<longrightarrow>
        (\<forall>i \<in> N. x i = 1 \<longrightarrow> i \<in> arg_max N v))"

subsection {* Equilibrium in weakly dominant strategies *}

text{* Given some single good auction, a strategy profile supports an equilibrium in weakly dominant strategies
  if each participant maximises its payoff by playing its component in that profile,
    whatever the other participants do. *}
definition equilibrium_weakly_dominant_strategy ::
  "participant set \<Rightarrow> valuations \<Rightarrow> bids \<Rightarrow> single_good_auction \<Rightarrow> bool" where
  "equilibrium_weakly_dominant_strategy N v b A \<longleftrightarrow>
    valuations N v \<and> bids N b \<and> single_good_auction A \<and>
    (\<forall>i \<in> N.
      (\<forall>whatever_bid . bids N whatever_bid \<longrightarrow>
        (let b' = whatever_bid(i := b i)
         in 
         (\<forall> x p x' p' . ((N, whatever_bid), (x, p)) \<in> A \<and> ((N, b'), (x', p')) \<in> A
          \<longrightarrow>
          payoff (v i) (x' i) (p' i) \<ge> payoff (v i) (x i) (p i)))))"

(* TODO CL: consider defining dominance as per https://github.com/formare/auctions/issues/23 *)

end
