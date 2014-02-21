(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Manfred Kerber <mnfrd.krbr@gmail.com>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>
* Marco B. Caminati <marco.caminati@gmail.com>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* Combinatorial Auctions *}

theory CombinatorialAuction
imports Complex_Main
  Vectors
  Partitions
  RelationProperties

begin

section {* Types *}

type_synonym participant = index
type_synonym goods = "nat set" (* CL: actually we'd prefer "'a set", as we really don't care about the type *)
type_synonym price = real

(*
CL: Keeping old initial vector-based bid implementation (suitable for multiple items per good and
  fractions of items) for reference.
		
(* one participant's bid on a set of goods *)
definition b :: "participant \<Rightarrow> goods \<Rightarrow> nat" where "b i y = (\<Sum> x \<in> y . x)"

text{* convenience type synonyms for most of the basic concepts we are dealing with *}
type_synonym endowment = "nat vector" (* conceptually: good \<Rightarrow> quantity *)
type_synonym endowment_subset = "nat vector" (* conceptually the same, but \<le> endowment *)

(* A single participant ascribes real values to subsets of the endowment. *)
type_synonym valuation = "endowment_subset \<Rightarrow> real"
type_synonym valuations = "valuation vector"
type_synonym bid = "endowment_subset \<Rightarrow> real"

(* A well-formed bid is non-negative for each “subset” of the endowment, i.e. each vector s
   that is component-wise 0 \<le> s \<le> x0. *)
definition bid :: "bid \<Rightarrow> goods \<Rightarrow> endowment \<Rightarrow> bool"
  where "bid b K x0 \<longleftrightarrow> (\<forall> s . non_negative_real_vector K s \<and> vector_le K s x0 \<longrightarrow> b s \<ge> 0)"

type_synonym allocation = "participant \<Rightarrow> endowment_subset"

type_synonym payments = "real vector"
*)

type_synonym bids = "participant \<Rightarrow> goods \<Rightarrow> price"
type_synonym allocation_rel = "(goods \<times> participant) set"
(* CL: providing a separate "goods set", as for allocation_fun below, is not necessary,
   as the function-as-relation-as-set representation already includes the domain
   on which we intend the function to work :-)  When representing the allocation as a function,
   we do need the set on which we intend to use the function, as Isabelle's functions are
   always total. *)

type_synonym payments = "participant \<Rightarrow> price"

(* CL: probably not needed, neither for close-to-paper nor for computable version
type_synonym allocation_fun = "(goods set) \<times> (goods \<rightharpoonup> participant)"
*)

type_synonym combinatorial_auction_pred = "goods \<Rightarrow> participant set \<Rightarrow> bids \<Rightarrow> allocation_rel \<Rightarrow> payments \<Rightarrow> bool"
type_synonym combinatorial_auction_tup = "(goods \<times> participant set \<times> bids) \<times> (allocation_rel \<times> payments)"
type_synonym combinatorial_auction_rel = "combinatorial_auction_tup set"

section {* Valid input *}

type_synonym input_validity = "goods \<Rightarrow> participant set \<Rightarrow> bids \<Rightarrow> bool"

text {* Valid input (i.e.\ valid bids w.r.t.\ the goods and participants).  As we represent
  @{typ bids} as functions, which are always total in Isabelle/HOL, we can't simply test, e.g., whether
  their domain is @{term "G \<times> N"} for the given goods @{term G} and participants @{term N}.  All we 
  can enforce are non-empty finite sets of goods and participants, and that the bids are monotonic
  w.r.t. (sub)sets of goods, and non-negative, with bids on an empty set of goods being zero.

  We need the monotonicity as we do not  *}
(* CL: Once we realise general/special auctions using locales, we need a valid_input axiom. *)
definition valid_input :: "goods \<Rightarrow> participant set \<Rightarrow> bids \<Rightarrow> bool"
where "valid_input G N b \<longleftrightarrow>
  card G > 0 \<and> card N > 0 \<and>
  (\<forall> n H H' . n \<in> N \<and> H \<subseteq> H' \<longrightarrow> b n H \<le> b n H') (* monotonicity *) \<and>
  (\<forall> n H . n \<in> N \<and> H \<subseteq> G \<longrightarrow> b n H \<ge> 0) (* non-negativity *) \<and>
  (\<forall> n \<in> N . b n {} = 0) (* zero on empty set *)"

section {* Allocations *}

text {* the value (according to the bids submitted) of a certain allocation *}
fun value_rel :: "bids \<Rightarrow> allocation_rel \<Rightarrow> price"
where "value_rel b x = (\<Sum> (y::goods) \<in> Domain x . b (x ,, y) y
  (* CL@CR: This implicitly assumes a value of 0 for goods not sold.  OK?
            Goods not sold don't occur in the allocation relation x and 
            therefore won't be summands of this sum. *)
)"

(* CL: probably not needed, neither for close-to-paper nor for computable version
definition value_fun :: "bids \<Rightarrow> allocation_fun \<Rightarrow> price"
where "value_fun b Yp  = (let Y = fst Yp; x = snd Yp in
  \<Sum> y \<in> Y . (let n = x y in 
    case n of None \<Rightarrow> 0 (* CL@CR: OK to assume a value of 0 for goods not sold? *)
            | Some n \<Rightarrow> b n y))"
*)

text {* all possible allocations of a set of goods to a set of participants: 
  injective functions that map sets of goods to their potential buyers, i.e.\ participants.
  Here, we assume that everything gets allocated, i.e. that there is no free disposal.
  This assumption facilitates the paper\<leftrightarrow>algorithm equivalence proof for injective functions. *}
fun possible_allocations_rel :: "goods \<Rightarrow> participant set \<Rightarrow> allocation_rel set"
where "possible_allocations_rel G N = \<Union> { injections Y N | Y . Y \<in> all_partitions G }" 

notepad
begin
  fix Rs::"('a \<times> 'b) set set"
  fix Sss::"'a set set"
  fix P::"'a set \<Rightarrow> ('a \<times> 'b) set set"
  (* TODO CL: an example (to be mentioned in the paper) for how hard set theory is for Isabelle:
     takes several minutes to find (2013), 104 ms to prove *)
  have "{ R . \<exists> Y \<in> Sss . R \<in> P Y } = \<Union> { P Y | Y . Y \<in> Sss }" by (smt Collect_cong Union_eq mem_Collect_eq)
end

text {* algorithmic version of @{const possible_allocations_rel} *}
fun possible_allocations_alg :: "goods \<Rightarrow> participant set \<Rightarrow> allocation_rel list"
where "possible_allocations_alg G N = concat [ injections_alg Y N . Y \<leftarrow> all_partitions_alg G ]"

(* example (uncomment to run): possibilities to allocate goods {1,2,3} to participants {100,200} *)
(*
value "possible_allocations_alg {1,2,3::nat} {100,200::nat}"
*)

(* CL: probably not needed, neither for close-to-paper nor for computable version
definition possible_allocations_fun :: "goods \<Rightarrow> participant set \<Rightarrow> allocation_fun set"
where "possible_allocations_fun G N = { (Y,x) .
  Y \<in> all_partitions G
  \<and> (\<forall> y \<in> Y . (\<exists> n \<in> N . x y = Some n) \<or> x y = None)
  \<and> inj_on x Y
 }"
*)

section {* Relational vs. predicate form*}

text {* A general combinatorial auction in predicate form.
  To give the auction designer flexibility (including the possibility to introduce mistakes),
  we only constrain the left hand side of the relation, as to cover valid inputs.
  This definition makes sure that whenever we speak of a combinatorial auction, there is a
  valid input on the left hand side.  In other words, this predicate returns false for relations having left
  hand side entries that are known not to be valid inputs.
  For this and other reasons (including Isabelle's difficulties to handle complex set comprehensions)
  it is more convenient to treat the auction as a predicate over all of
  its arguments, instead of a left-hand-side/right-hand-side relation.*}
definition pred :: "goods \<Rightarrow> participant set \<Rightarrow> bids \<Rightarrow> allocation_rel \<Rightarrow> payments \<Rightarrow> bool"
where "pred G N b x p \<longleftrightarrow> valid_input G N b"

text {* Given an auction in predicate form @{const pred}, construct a predicate that takes all 
  arguments of @{const pred} as one @{term "(input, outcome)"} pair, and checks whether its
  components satisfy @{const pred}.  This is useful for modelling the auction in relational form. *}
definition pred_tup :: "combinatorial_auction_pred \<Rightarrow> combinatorial_auction_tup \<Rightarrow> bool"
where "pred_tup P T \<longleftrightarrow> (\<exists> G N b x p . T = ((G, N, b), (x, p)) \<and> P G N b x p)"

text {* We construct the relational form of an auction from the predicate form @{const pred}: given a 
  predicate that defines an auction by telling us for all possible arguments whether they 
  form an @{term "(input, outcome)"} pair according to the auction's definition, we construct a predicate
  that tells us whether all @{term "(input, outcome)"} pairs in a given relation satisfy that predicate,
  i.e.\ whether the given relation is an auction of the desired type. *}
definition rel_sat_pred :: "combinatorial_auction_pred \<Rightarrow> combinatorial_auction_rel \<Rightarrow> bool"
where "rel_sat_pred P A \<longleftrightarrow> (\<forall> T \<in> A . pred_tup P T)"

(* TODO CL: Now that we have rel_all, check whether this is still needed.  rel_sat_pred could also
   now be defined as "A \<subseteq> (rel_all P)" *)
text {* A variant of @{const rel_sat_pred}: We construct a predicate that tells us whether the
  given relation comprises \emph{all} @{term "(input, outcome)"} pairs that satisfy the given auction predicate, 
  i.e.\ whether the given relation comprises all possible auctions of the desired type.  *}
definition rel_all_pred :: "combinatorial_auction_pred \<Rightarrow> combinatorial_auction_rel \<Rightarrow> bool"
where "rel_all_pred P A \<longleftrightarrow> (\<forall> T . T \<in> A \<longleftrightarrow> pred_tup P T)"

(* TODO CL: document *)
definition rel_all :: "combinatorial_auction_pred \<Rightarrow> combinatorial_auction_rel"
where "rel_all P = { T . pred_tup P T }"

(* TODO CL: document *)
lemma pred_imp_rel_all: "P G N b x p \<Longrightarrow> ((G, N, b), (x, p)) \<in> rel_all P"
unfolding rel_all_def
using pred_tup_def mem_Collect_eq
by force

end

