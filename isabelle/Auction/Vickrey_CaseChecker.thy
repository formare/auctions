(*
$Id$

Auction Theory Toolbox

Authors:
* Manfred Kerber <m.kerber@cs.bham.ac.uk>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>
* Makarius Wenzel <wenzel@lri.fr>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)


header {* Vickrey's Theorem: second price auctions are
  efficient, and truthful bidding is a weakly dominant strategy --
  copy to experiment with ``case checking'' *}

theory Vickrey_CaseChecker
imports Complex_Main "~~/src/HOL/Library/Order_Relation"
        "~~/src/HOL/Library/Efficient_Nat"

begin

section {* Single good auctions *}

subsection {* Preliminaries *}

type_synonym participant = nat
type_synonym participants = "nat set"

type_synonym 'a vector = "participant \<Rightarrow> 'a"

definition non_negative_real_vector :: "participants \<Rightarrow> real vector \<Rightarrow> bool"
  where "non_negative_real_vector N v \<longleftrightarrow> (\<forall>i \<in> N. v i \<ge> 0)"

definition positive_real_vector :: "participants \<Rightarrow> real vector \<Rightarrow> bool"
  where "positive_real_vector N v \<longleftrightarrow> (\<forall>i \<in> N. v i > 0)"

text{* equality of vectors is defined component-wise up to the vectors' length *}
definition vectors_equal :: "participants \<Rightarrow> 'a vector \<Rightarrow> 'a vector \<Rightarrow> bool"
  where "vectors_equal N v w \<longleftrightarrow> (\<forall>i \<in> N . v i = w i)"

text{* convenience type synonyms for most of the basic concepts we are dealing with *}
type_synonym valuations = "real vector"
type_synonym bids = "real vector"
type_synonym allocation = "real vector"
type_synonym payments = "real vector"

text{* Helps to determine whether one participant should be preferred over another one in the case of a draw.
  t x y = True should result in x being (strictly) preferred. *}
type_synonym tie_breaker = "participant \<Rightarrow> participant \<Rightarrow> bool"

text{* Is a tie-breaker well-behaved on a given set of participants?  I.e. does it assign a 
  unique value to each participant? *}
definition wf_tie_breaker_on :: "tie_breaker \<Rightarrow> participants \<Rightarrow> bool"
  where "wf_tie_breaker_on tie_breaker participants \<longleftrightarrow>
    strict_linear_order_on participants
      {(a::participant, b::participant) . {a, b} \<subseteq> participants \<and> tie_breaker a b}"
(* old version for tie_breaker = "participant \<Rightarrow> real", to be used with <
   "card (tie_breaker ` participants) = card participants" *)

(* CL: code provided by Le_J (http://stackoverflow.com/a/16690357/2397768) –
   how to prove strict linear order in a concrete case: *)
(*
lemma "strict_linear_order_on {1::nat, 2} {(a::nat, b) . {a, b} \<subseteq> {1::nat, 2} \<and> a < b}"
  unfolding strict_linear_order_on_def partial_order_on_def preorder_on_def
    irrefl_def total_on_def trans_def antisym_def
  by auto
*)

(* TODO CL: link to "function" theorems from this text *)
text{* Initially we'd like to formalise any single good auction as a relation of bids and outcome.
  Proving the well-definedness of an auction is then a separate step in the auction design process.
  It involves:
  \begin{enumerate}
  \item checking that the allocation and payments vectors actually meet our expectation of an allocation or payment,
    as defined by the @{term allocation_def} and @{term vickrey_payment} predicates below
  \item checking that the relation actually is a function, i.e. that it is
    \begin{enumerate}
    \item left-total: ``for any admissible bids \dots''
    \item right-unique: ``\dots there is a unique outcome.''
    \end{enumerate}
  \end{enumerate}
*}
type_synonym single_good_auction = "((participants \<times> bids) \<times> (allocation \<times> payments)) set"

subsection {* Valuation *}

definition valuations :: "participants \<Rightarrow> valuations \<Rightarrow> bool"
  where "valuations N v \<longleftrightarrow> positive_real_vector N v"

subsection {* Strategy (bids) *}

definition bids :: "participants \<Rightarrow> bids \<Rightarrow> bool"
  where "bids N b \<longleftrightarrow> non_negative_real_vector N b"

lemma valuation_is_bid: "valuations N v \<Longrightarrow> bids N v"
  by (auto simp add: valuations_def positive_real_vector_def bids_def non_negative_real_vector_def)

subsection {* Allocation *}

(* CL: changed for case checker: From now on, we merely assume that an allocation is a vector 
       of reals that sum up to 1, i.e. this allows for a divisible good,
       and we no longer assume that it is a function of the bids.
       This will make it easier for us to ``overlook'' cases in the definitions of concrete auctions ;-)
   CL@CR: I see that in your paper formalisation you had already defined the allocation as 
          a vector of {0,1} with exactly one 1.  *)
text{* We employ the general definition of an allocation for a divisible single good.
  This is to allow for more possibilities of an auction to be not well-defined.
  Also, it is no longer the allocation that we model as a function of the bid, but instead we model
  the \emph{auction} as a relation of bids to a @{text "(allocation \<times> payments)"} outcome. *}
(* text_raw{*\snip{allocation_def}{1}{2}{%*} *)
definition allocation :: "participants \<Rightarrow> allocation \<Rightarrow> bool"
  where "allocation N x \<longleftrightarrow> non_negative_real_vector N x \<and> (\<Sum> i \<in> N . x i) = 1"
(* text_raw{*}%endsnip*} *)

subsection {* Payment *}

text{* Same as with the @{text allocation} we now model this as a plain vector. *}
definition vickrey_payment :: "participants \<Rightarrow> payments \<Rightarrow> bool"
  where "vickrey_payment N p \<longleftrightarrow> (\<forall>i \<in> N . p i \<ge> 0)"

subsection {* Payoff *}

definition payoff :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  where "payoff v x p = v * x - p"

text{* To give the auction designer flexibility (including the possibility to introduce mistakes),
  we only constrain the left hand side of the relation, as to cover admissible @{text bids}.
  This definition makes sure that whenever we speak of a single good auction, there is a bid vector
  on the left hand side.  In other words, this predicate returns false for relations having left
  hand side entries that are known not to be bid vectors.
  For this and other purposes it is more convenient to treat the auction as a predicate over all of
  its arguments, instead of a left-hand-side/right-hand-side relation.*}
definition sga_pred :: "participants \<Rightarrow> bids \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool"
  where
    "sga_pred N b x p \<longleftrightarrow> bids N b"

text{* We construct the relational version of an auction from the predicate version: given a 
  predicate that defines an auction by telling us for all possible arguments whether they 
  form an (input, outcome) pair according to the auction's definition, we construct a predicate
  that tells us whether all (input, outcome) pairs in a given relation satisfy that predicate,
  i.e. whether the given relation is an auction of the desired type. *}
definition rel_sat_sga_pred ::
  "(participants \<Rightarrow> bids \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool) \<Rightarrow> single_good_auction \<Rightarrow> bool"
  where "rel_sat_sga_pred pred A \<longleftrightarrow> (\<forall> ((N, b), (x, p)) \<in> A . pred N b x p)"

text{* A variant of @{text rel_sat_sga_pred}: We construct a predicate that tells us whether the
  given relation comprises all (input, outcome) pairs that satisfy the given auction predicate, 
  i.e. whether the given relation comprises all possible auctions of the desired type.  *}
definition rel_all_sga_pred ::
  "(participants \<Rightarrow> bids \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool) \<Rightarrow> single_good_auction \<Rightarrow> bool"
  where "rel_all_sga_pred pred A \<longleftrightarrow> (\<forall> N b x p . ((N, b), (x, p)) \<in> A \<longleftrightarrow> pred N b x p)"

text{* Now for the relational version of the single good auction: *}
definition single_good_auction :: "single_good_auction \<Rightarrow> bool"
  where "single_good_auction A = rel_sat_sga_pred sga_pred A"

text{* In the general case, by ``well-defined outcome'' we mean that the good gets properly 
  allocated w.r.t. the definition of an @{text allocation}.  We are not constraining the payments
  at this point. *}
definition sga_well_defined_outcome_pred :: "participants \<Rightarrow> bids \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool"
  where
    "sga_well_defined_outcome_pred N b x p \<longleftrightarrow> allocation N x"

definition sga_well_defined_outcome :: "single_good_auction \<Rightarrow> bool"
  where
    "sga_well_defined_outcome A \<longleftrightarrow>
      (\<forall> ((N::participants, b::bids), (x::allocation, p::payments)) \<in> A .
        sga_well_defined_outcome_pred N b x p)"

type_synonym input_admissibility = "participants \<Rightarrow> bids \<Rightarrow> bool"

text{* Left-totality of an auction defined as a relation: for each admissible bid vector
  there exists some outcome (not necessarily unique). *}
definition sga_left_total :: "single_good_auction \<Rightarrow> input_admissibility \<Rightarrow> bool"
  where "sga_left_total A admissible \<longleftrightarrow>
    (\<forall> (N :: participants) (b :: bids) . admissible N b \<longrightarrow>
      (\<exists> (x :: allocation) (p :: payments) . ((N, b), (x, p)) \<in> A))"

text{* If one relation is left-total on a given set, its superrelations are left-total on that set too. *}
lemma left_total_suprel:
  fixes A :: single_good_auction
    and B :: single_good_auction
    and admissible :: input_admissibility
  assumes left_total_subrel: "sga_left_total A admissible"
      and suprel: "A \<subseteq> B"
  shows "sga_left_total B admissible"
using assms sga_left_total_def
by (metis set_mp)

type_synonym outcome_equivalence = "participants \<Rightarrow> bids \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool"

text{* Right-uniqueness of an auction defined as a relation: for each admissible bid vector,
  if there is an outcome, it is unique.  We define this once for underspecified auctions, i.e.
  where tie-breaking is not specified, \<dots> *}
definition sga_right_unique :: "single_good_auction \<Rightarrow> input_admissibility \<Rightarrow> outcome_equivalence \<Rightarrow> bool"
  where "sga_right_unique A admissible equivalent \<longleftrightarrow>
    (\<forall> (N :: participants) (b :: bids) . admissible N b \<longrightarrow>
      (\<forall> (x :: allocation) (x' :: allocation) (p :: payments) (p' :: payments) .
        ((N, b), (x, p)) \<in> A \<and> ((N, b), (x', p')) \<in> A \<longrightarrow> equivalent N b x p x' p'))"

text{* \<dots> and once for fully specified (“fs”) auctions with tie-breaking, where outcome equivalence
  is defined by equality: *}
definition fs_sga_right_unique :: "single_good_auction \<Rightarrow> input_admissibility \<Rightarrow> bool"
  where "fs_sga_right_unique A admissible \<longleftrightarrow>
    sga_right_unique A admissible
      (* equivalence by equality: *)
      (\<lambda> N b x p x' p' . vectors_equal N x x' \<and> vectors_equal N p p')"

definition sga_function :: "single_good_auction \<Rightarrow> input_admissibility \<Rightarrow> outcome_equivalence \<Rightarrow> bool"
  where "sga_function A admissible equivalent \<longleftrightarrow>
    sga_left_total A admissible \<and> sga_right_unique A admissible equivalent"

subsection {* Maximum *}
text{* This subsection uses Isabelle's set maximum functions, wrapping them for our use. *}

definition maximum_defined :: "participants \<Rightarrow> bool"
  where "maximum_defined N \<longleftrightarrow> card N > 0"

lemma maximum_except_defined:
  fixes N i
  assumes "i \<in> N" "card N > 1"
  shows "maximum_defined (N - {i})"
  using assms maximum_defined_def
  by (smt card.remove card_infinite)

definition maximum :: "participants \<Rightarrow> real vector \<Rightarrow> real"
  where "maximum N y = Max (y ` N)"

lemma maximum_equal:
  fixes N :: participants and y :: "real vector" and z :: "real vector"
  assumes "\<forall>i \<in> N. y i = z i"
  shows "maximum N y = maximum N z"
proof -
  have "y ` N = z ` N" by (rule image_cong) (auto simp add: assms)
  then show ?thesis unfolding maximum_def by simp
qed

lemma maximum_is_greater_or_equal:
  fixes N :: participants and y :: "real vector" and i :: participant
  assumes "maximum_defined N"
    and "i \<in> N"
  shows "maximum N y \<ge> y i"
  using assms unfolding maximum_defined_def maximum_def by (simp add: card_gt_0_iff)

lemma maximum_is_component:
  fixes N :: participants and y :: "real vector"
  assumes defined: "maximum_defined N"
  shows "\<exists>i \<in> N. maximum N y = y i"
proof -
  let ?A = "y ` N"
  from defined have "finite ?A" and "?A \<noteq> {}"
    unfolding maximum_defined_def by (simp_all add: card_gt_0_iff)
  then have "Max ?A \<in> ?A" by (rule Max_in)
  then obtain i where "i \<in> N" and "Max ?A = y i" by blast
  with maximum_def show ?thesis by auto
qed

lemma maximum_sufficient:
  fixes N :: participants and y :: "real vector" and m :: real
  assumes defined: "maximum_defined N"
    and greater_or_equal: "\<forall>i \<in> N. m \<ge> y i"
    and is_component: "\<exists>i \<in> N. m = y i"
  shows "maximum N y = m"
  unfolding maximum_def
proof -
  let ?A = "y ` N"
  show "Max ?A = m"
  proof (rule Max_eqI)
    from defined show "finite ?A"
      unfolding maximum_defined_def by (simp add: card_gt_0_iff)
    show "m \<in> ?A" using is_component by blast
    fix a assume "a \<in> ?A"
    then show "a \<le> m" using greater_or_equal by blast
  qed
qed

text{* the set of all indices of maximum components of a vector *}
definition arg_max_set :: "participants \<Rightarrow> real vector \<Rightarrow> participants"
  where "arg_max_set N b = {i \<in> N . maximum N b = b i}"

text{* the index of the single maximum component *}
fun arg_max_l_tb :: "(participant list) \<Rightarrow> tie_breaker \<Rightarrow> bids \<Rightarrow> participant"
where "arg_max_l_tb [] t b = 0" (* in practice we will only call the function with lists of at least one element *)
    | "arg_max_l_tb [x] t b = x"
    | "arg_max_l_tb (x # xs) t b =
      (let y = arg_max_l_tb xs t b in
        if (b x > b y) then x (* TODO CL: Once this works, make 'highest bid' just a special case of tie-breaking,
          and allow for custom chains of tie-breaking functions to be defined. *)
        else if (b x = b y \<and> t x y) then x
        else y)"

(* TODO CL: once proving properties of the list-based implementation of this function
   starts to hurt, follow Lars Noschinski's advice to use the list-based implementation for
   code generation only, and otherwise use an equivalent set-based definition.
   http://stackoverflow.com/questions/16702866/defining-an-arg-max-like-function-over-finite-sets-and-proving-some-of-its-pr#comment24451608_16707012 *)
fun arg_max_tb :: "participants \<Rightarrow> tie_breaker \<Rightarrow> bids \<Rightarrow> participant"
where "arg_max_tb N t b = arg_max_l_tb (sorted_list_of_set N) t b"

(* uncomment for testing:
value "arg_max_tb {2::nat, 4, 6} (* the participant indices *)
  op> (* the tie breaking function *)
  (\<lambda> i . nth [27::real, 42, 42] (i div 2 - 1::nat))"
*)

(* code provided by Lars Noschinski on the Isabelle mailing list, 2013-05-22 *)
lemma sorted_list_of_set_remove': (* TODO CL: sorted_list_of_set_not_empty (for which this is needed) should be in the library in 2014; remove then *)
  assumes "finite A" "x \<in> A"
  shows "sorted_list_of_set A = insort x (sorted_list_of_set (A - {x}))"
proof -
  from assms have "insert x (A - {x}) = A" by blast
  then have "sorted_list_of_set A = sorted_list_of_set (insert x (A - {x}))"
    by simp
  also have "\<dots> = insort x (sorted_list_of_set (A - {x}))"
  using assms by simp
  finally show ?thesis .
qed

(* code provided by Lars Noschinski on the Isabelle mailing list, 2013-05-22 *)
lemma sorted_list_of_set_eq_Nil_iff [simp] : (* TODO CL: should be in the library in 2014; remove then *)
  assumes "finite S"
  shows "sorted_list_of_set S = [] \<longleftrightarrow> S = {}"
using assms by (auto simp: sorted_list_of_set_remove')

text{* The highest bidder, determined by tie-breaking using @{term arg_max_tb},
  is one member of the set of all highest bidders, determined using @{term arg_max_set}. *}
lemma arg_max_tb_imp_arg_max_set :
  fixes N :: participants
    and t :: tie_breaker
    and b :: bids
  assumes defined: "maximum_defined N"
  shows "arg_max_tb N t b \<in> arg_max_set N b"
(* A proof could be indirect by assuming that arg_max_tb N t b is not in the set,
   i.e., that the arg_max_tb offers less or more, and bring this to a contradiction.*)
proof -
  def Nsort \<equiv> "sorted_list_of_set N"
  from defined have finite: "finite N" and ne: "N \<noteq> {}"
    unfolding maximum_defined_def by (simp_all add: card_gt_0_iff)
  (* TODO CL: Isabelle 2014 might be able to do the following step more automatically: *)
  from finite Nsort_def sorted_list_of_set have distinct: "distinct Nsort" by auto
  from finite ne Nsort_def have "Nsort \<noteq> []" by simp
  then have stmt_list: "distinct Nsort \<longrightarrow> arg_max_l_tb Nsort t b \<in> arg_max_set (set Nsort) b"
  proof (induct Nsort rule: list_nonempty_induct)
    case single
    {
      fix x have "arg_max_l_tb [x] t b \<in> arg_max_set (set [x]) b"
        unfolding arg_max_l_tb.simps arg_max_set_def maximum_def Nsort_def by simp
    }
    then show ?case ..
  next
    case cons (* CL: How can I use the cons.*, that I'm getting here, below? *)
    fix x xs
    assume a1: "xs \<noteq> []" and a2: "distinct xs \<longrightarrow> arg_max_l_tb xs t b \<in> arg_max_set (set xs) b"
    from a1 have mdxs: "maximum_defined (set xs)" using maximum_defined_def by (metis List.finite_set card_gt_0_iff set_empty2)
    from a1 have mdxs': "maximum_defined (set (x # xs))" using maximum_defined_def by (metis List.finite_set card_gt_0_iff list.distinct(1) set_empty2)
    show "distinct (x # xs) \<longrightarrow> arg_max_l_tb (x # xs) t b \<in> arg_max_set (set (x # xs)) b"
    proof
      assume distinct': "distinct (x # xs)"
      def i \<equiv> "arg_max_l_tb (x # xs) t b"
      with a1 have "i =
        (let y = arg_max_l_tb xs t b in
          if (b x > b y) then x
          else if (b x = b y \<and> t x y) then x
          else y)" by (metis arg_max_l_tb.simps(2) arg_max_l_tb.simps(3) neq_Nil_conv)
      then have i_unf: "i = (let y = arg_max_l_tb xs t b in
          if (b x > b y \<or> b x = b y \<and> t x y) then x
          else y)" by smt
      show "i \<in> arg_max_set (set (x # xs)) b"
      proof (cases "i = arg_max_l_tb xs t b")
        case True (* the maximum is the same as before *)
        with a2 distinct' have ams: "i \<in> arg_max_set (set xs) b" by simp
        with mdxs have i_in: "i \<in> (set xs)" unfolding arg_max_set_def using maximum_is_component by simp
        then have i_in': "i \<in> (set (x # xs))" by simp
        from i_unf True have "\<not> (b x > b i \<or> b x = b i \<and> t x i)" by (smt distinct' distinct.simps(2) i_in)
        then have 1: "b x \<le> b i" by auto
        from ams have "b i = maximum (set xs) b" unfolding arg_max_set_def by simp
        with maximum_is_greater_or_equal mdxs have "\<forall> j \<in> (set xs) . b i \<ge> b j" by simp
        with 1 have "\<forall> j \<in> (set (x # xs)) . b i \<ge> b j" by simp
        with maximum_sufficient mdxs' i_in' have "b i = maximum (set (x # xs)) b" by metis
        with i_in' show ?thesis unfolding arg_max_set_def by simp
      next
        case False (* the newly inserted element x is the maximum *)
        def y \<equiv> "arg_max_l_tb xs t b"
        with i_unf have yi: "
          i = (if (b x > b y \<or> b x = b y \<and> t x y) then x
          else y)" by auto
        from y_def False have "i \<noteq> y" unfolding i_def by simp
        with yi have bi: "(b x > b y \<or> b x = b y \<and> t x y) \<and> i = x" by smt
        from y_def a2 distinct' have ams: "y \<in> arg_max_set (set xs) b" by simp
        with mdxs have y_in: "y \<in> (set xs)" unfolding arg_max_set_def using maximum_is_component by simp
        then have y_in': "y \<in> (set (x # xs))" by simp
        from ams have "b y = maximum (set xs) b" unfolding arg_max_set_def by simp
        with maximum_is_greater_or_equal mdxs have "\<forall> j \<in> (set xs) . b y \<ge> b j" by simp
        with bi have "\<forall> j \<in> (set xs) . b x \<ge> b j" by auto (* because b x \<ge> b y *)
        then have "\<forall> j \<in> (set (x # xs)) . b x \<ge> b j" by simp
        with maximum_sufficient mdxs' have "b x = maximum (set (x # xs)) b" by (metis distinct' distinct.simps(2) distinct_length_2_or_more)
        with bi show ?thesis unfolding arg_max_set_def by simp
      qed
    qed
  qed
  from Nsort_def `finite N` have "N = set Nsort" by simp
  from Nsort_def have "arg_max_tb N t b = arg_max_l_tb Nsort t b" by simp
  with distinct stmt_list have "arg_max_tb N t b \<in> arg_max_set (set Nsort) b" by simp
  with `N = set Nsort` show ?thesis by simp
qed

lemma maximum_except_is_greater_or_equal:
  fixes N :: participants and y :: "real vector" and j :: participant and i :: participant
  assumes defined: "maximum_defined N"
    and i: "i \<in> N \<and> i \<noteq> j"
  shows "maximum (N - {j}) y \<ge> y i"
proof -
  let ?M = "N - {j}"
  let ?A = "y ` ?M"
  from i have *: "i \<in> ?M" by simp
  with defined have "finite ?A" and "?A \<noteq> {}"
    unfolding maximum_defined_def by (auto simp add: card_gt_0_iff)
  with * have "Max ?A \<ge> y i" by (auto simp add: Max_ge_iff)
  then show ?thesis unfolding maximum_def .
qed

lemma maximum_remaining_maximum:
  fixes N :: participants and y :: "real vector" and j :: participant
  assumes defined': "maximum_defined (N - {j})"
    and j_max: "y j = maximum N y"
  shows "y j \<ge> maximum (N - {j}) y"
proof -
  have "y ` (N - {j}) \<subseteq> y ` N" by blast
  with defined' have "maximum (N - {j}) y \<le> maximum N y"
    unfolding maximum_def maximum_defined_def by (simp add: card_gt_0_iff Max_mono)
  also note j_max [symmetric]
  finally show ?thesis .
qed

lemma remaining_maximum_invariant:
  fixes N :: participants and y :: "real vector" and i :: participant and a :: real
  shows "maximum (N - {i}) (y(i := a)) = maximum (N - {i}) y"
proof -
  let ?M = "N - {i}"
  have "y ` ?M = (y(i := a)) ` ?M" by auto
  then show ?thesis unfolding maximum_def by simp
qed

subsection {* Second price single good auctions and some of their properties *}

definition second_price_auction_winner_outcome ::
    "participants \<Rightarrow> bids \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> participant \<Rightarrow> bool"
  where
    "second_price_auction_winner_outcome N b x p i \<longleftrightarrow>
      x i = 1 \<and> p i = maximum (N - {i}) b"

definition second_price_auction_winner ::
    "participants \<Rightarrow> bids \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> participant \<Rightarrow> bool"
  where
    "second_price_auction_winner N b x p i \<longleftrightarrow>
      i \<in> N \<and> i \<in> arg_max_set N b \<and>
      second_price_auction_winner_outcome N b x p i"

definition second_price_auction_loser ::
    "participants \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> participant \<Rightarrow> bool"
  where "second_price_auction_loser N x p i \<longleftrightarrow> i \<in> N \<and>
     x i = 0 \<and>
     p i = 0"

definition spa_admissible_input :: "participants \<Rightarrow> bids \<Rightarrow> bool"
  where "spa_admissible_input N b \<longleftrightarrow> card N > 1 \<and> bids N b"

definition spa_pred :: "participants \<Rightarrow> bids \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool"
  where
    "spa_pred N b x p \<longleftrightarrow>
      spa_admissible_input N b \<and>
      (\<exists>i \<in> N. second_price_auction_winner N b x p i \<and>
        (\<forall>j \<in> N . j \<noteq> i \<longrightarrow> second_price_auction_loser N x p j))"

definition second_price_auction :: "single_good_auction \<Rightarrow> bool"
  where "second_price_auction A = rel_sat_sga_pred spa_pred A"

text{* definition of a second price auction, projected to the allocation *}
lemma spa_allocation :
  fixes N :: participants and b :: bids
    and x :: allocation and p :: payments
  assumes "spa_pred N b x p"
  shows "\<exists> i \<in> N . x i = 1 \<and> (\<forall> j \<in> N . j \<noteq> i \<longrightarrow> x j = 0)"
  using assms
  unfolding spa_pred_def second_price_auction_def
    second_price_auction_winner_def second_price_auction_winner_outcome_def
    second_price_auction_loser_def
  by auto

(* fs = fully specified *)
definition fs_spa_pred :: "participants \<Rightarrow> bids \<Rightarrow> tie_breaker \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool"
  where
    "fs_spa_pred N b t x p \<longleftrightarrow>
      spa_admissible_input N b \<and>
      (\<exists>i \<in> N . i = arg_max_tb N t b \<and> second_price_auction_winner_outcome N b x p i \<and>
        (\<forall>j \<in> N . j \<noteq> i \<longrightarrow> second_price_auction_loser N x p j))"

text{* convenience function to compute the winner of a fully specified second price auction with tie-breaking *}
fun fs_spa_winner :: "participants \<Rightarrow> bids \<Rightarrow> tie_breaker \<Rightarrow> participant"
  where "fs_spa_winner N b t = arg_max_tb N t b"

text{* convenience function to compute the allocation of a fully specified second price auction with tie-breaking *}
fun fs_spa_allocation :: "participants \<Rightarrow> bids \<Rightarrow> tie_breaker \<Rightarrow> allocation"
  where "fs_spa_allocation N b t = (let winner = fs_spa_winner N b t in
    (\<lambda> i . if (i = winner) then 1 else 0))"

text{* convenience function to compute the payments of a fully specified second price auction with tie-breaking *}
fun fs_spa_payments :: "participants \<Rightarrow> bids \<Rightarrow> tie_breaker \<Rightarrow> payments"
  where "fs_spa_payments N b t = (let winner = fs_spa_winner N b t in
    (\<lambda> i . if (i = winner) then maximum (N - {i}) b else 0))"

text{* The definitions of the computable functions @{text fs_spa_allocation} and @{text fs_spa_payments}
  are consistent with how we defined the outcome of a fully specified second price auction
  with tie-breaking in @{text fs_spa_pred}. *}
lemma fs_spa_pred_allocation_payments:
  fixes N :: participants
    and b :: bids
    and t :: tie_breaker
    and x :: allocation
    and p :: payments
  shows "fs_spa_pred N b t x p \<longleftrightarrow>
    spa_admissible_input N b \<and>
    vectors_equal N x (fs_spa_allocation N b t) \<and>
    vectors_equal N p (fs_spa_payments N b t)"
proof
  assume "fs_spa_pred N b t x p"
  then have "spa_admissible_input N b"
    and outcome: "\<exists>i \<in> N . i = fs_spa_winner N b t \<and>
     x i = 1 \<and> (\<forall>j \<in> N . j \<noteq> i \<longrightarrow> x j = 0) \<and>
     p i = maximum (N - {i}) b \<and> (\<forall>j \<in> N . j \<noteq> i \<longrightarrow> p j = 0)"
    unfolding fs_spa_pred_def
      second_price_auction_winner_outcome_def second_price_auction_loser_def
     using fs_spa_winner.simps by auto
  then show "spa_admissible_input N b \<and>
    vectors_equal N x (fs_spa_allocation N b t) \<and>
    vectors_equal N p (fs_spa_payments N b t)"
    using fs_spa_allocation.simps fs_spa_payments.simps vectors_equal_def by smt
next
  assume "spa_admissible_input N b \<and>
    vectors_equal N x (fs_spa_allocation N b t) \<and>
    vectors_equal N p (fs_spa_payments N b t)"
  then have admissible: "spa_admissible_input N b"
    and outcome: "let winner = fs_spa_winner N b t in
      (\<forall>i \<in> N . x i = (if (i = winner) then 1 else 0)) \<and>
      (\<forall>i \<in> N . p i = (if (i = winner) then maximum (N - {i}) b else 0))"
    unfolding vectors_equal_def
    using fs_spa_allocation.simps fs_spa_payments.simps by simp_all
  from admissible have winner_range: "fs_spa_winner N b t \<in> N"
    using arg_max_set_def arg_max_tb_imp_arg_max_set fs_spa_winner.simps maximum_defined_def mem_Collect_eq spa_admissible_input_def
    by smt
  with outcome have "let winner = fs_spa_winner N b t in
      x winner = 1 \<and> (\<forall>j \<in> N . j \<noteq> winner \<longrightarrow> x j = 0) \<and>
      p winner = maximum (N - {winner}) b \<and> (\<forall>j \<in> N . j \<noteq> winner \<longrightarrow> p j = 0)" by metis
  with admissible winner_range show "fs_spa_pred N b t x p"
     unfolding fs_spa_pred_def second_price_auction_winner_outcome_def second_price_auction_loser_def
     using fs_spa_winner.simps by metis
qed

lemma fs_spa_is_spa :
  fixes N :: participants
    and b :: bids
    and t :: tie_breaker
    and x :: allocation
    and p :: payments
  assumes "fs_spa_pred N b t x p"
  shows "spa_pred N b x p"
proof -
  from assms have card: "card N > 1" and bids: "bids N b" and
    def_unfolded: "(\<exists>i \<in> N . i = arg_max_tb N t b \<and> second_price_auction_winner_outcome N b x p i \<and>
      (\<forall>j \<in> N . j \<noteq> i \<longrightarrow> second_price_auction_loser N x p j))"
    unfolding fs_spa_pred_def spa_admissible_input_def by auto
  then obtain winner
    where fs_spa_winner: "winner \<in> N \<and> winner = arg_max_tb N t b \<and>
        second_price_auction_winner_outcome N b x p winner"
      and spa_loser: "\<forall>j \<in> N . j \<noteq> winner \<longrightarrow> second_price_auction_loser N x p j" by blast
  have spa_winner: "winner \<in> N \<and> second_price_auction_winner N b x p winner"
  proof -
    from fs_spa_winner have range: "winner \<in> N"
      and determination: "winner = arg_max_tb N t b"
      and spa_winner_outcome: "second_price_auction_winner_outcome N b x p winner"
      by auto
    from card have maximum_defined: "maximum_defined N" unfolding maximum_defined_def by simp
    with determination have "winner \<in> arg_max_set N b" using arg_max_tb_imp_arg_max_set by simp
    with range and spa_winner_outcome show ?thesis
      unfolding second_price_auction_winner_def by simp
  qed
  with card bids spa_loser have "card N > 1 \<and> bids N b \<and> (\<exists>i \<in> N. second_price_auction_winner N b x p i \<and>
    (\<forall>j \<in> N . j \<noteq> i \<longrightarrow> second_price_auction_loser N x p j))" by blast
  then show ?thesis unfolding spa_admissible_input_def spa_pred_def by simp
qed

text{* alternative definition for easier currying *}
definition fs_spa_pred' :: "tie_breaker \<Rightarrow> participants \<Rightarrow> bids \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool"
  where "fs_spa_pred' t N b x p = fs_spa_pred N b t x p"

lemma rel_all_fs_spa_is_spa:
  fixes A :: single_good_auction
    and B :: single_good_auction
    and t :: tie_breaker
  assumes A_fs_spa: "rel_all_sga_pred (fs_spa_pred' t) A"
      and B_spa: "rel_all_sga_pred spa_pred B"
  shows "A \<subseteq> B"
proof -
  {
    fix N b x p assume "((N, b), (x, p)) \<in> A"
    with A_fs_spa have "fs_spa_pred N b t x p"
      unfolding rel_all_sga_pred_def fs_spa_pred'_def by simp
    then have "spa_pred N b x p" using fs_spa_is_spa by simp
    with B_spa have "((N, b), (x, p)) \<in> B" unfolding rel_all_sga_pred_def by simp
  }
  then show ?thesis by auto
qed

text{* Our second price auction (@{text spa_pred}) is well-defined in that its outcome is an allocation. *}
lemma spa_allocates :
  fixes N :: participants and b :: bids
    and x :: allocation and p :: payments
  assumes spa: "spa_pred N b x p"
      and finite: "finite N"
  shows "allocation N x"
proof -
  from spa obtain i where i_def: "i \<in> N \<and> x i = 1" using spa_allocation by blast
  (* the losers' allocations are all 0 *)
  with spa have j_def: "\<forall>j \<in> N - {i} . x j = 0" using spa_allocation by (metis member_remove remove_def)
  then have "(\<Sum> k \<in> N . x k) = 1" using finite i_def by (metis comm_monoid_add_class.add.right_neutral setsum.F_neutral' setsum.remove)
  then show ?thesis unfolding allocation_def non_negative_real_vector_def by (smt spa spa_allocation)
qed

lemma spa_well_defined_sga :
  fixes N :: participants and b :: bids
    and x :: allocation and p :: payments
  assumes spa: "spa_pred N b x p"
      and finite: "finite N"
  shows "sga_well_defined_outcome_pred N b x p"
  using assms spa_allocates unfolding allocation_def sga_well_defined_outcome_pred_def by simp

text{* definition of a second price auction, projected to the payments *}
lemma spa_payments :
  fixes N :: participants and b :: bids
    and x :: allocation and p :: payments
  assumes "spa_pred N b x p"
  shows "\<exists> i \<in> N . p i = maximum (N - {i}) b \<and> (\<forall> j \<in> N . j \<noteq> i \<longrightarrow> p j = 0)"
  using assms
  unfolding spa_pred_def second_price_auction_def second_price_auction_winner_def second_price_auction_winner_outcome_def second_price_auction_loser_def
  by auto

(* TODO CL: In the general auction case it may make sense to check that the payments (including the seller's payment)
   sum up to 0.
*)
text{* Our second price auction (@{text spa_pred}) is well-defined in that its outcome specifies non-negative payments for everyone. *}
lemma spa_vickrey_payment :
  fixes N :: participants and b :: bids
    and x :: allocation and p :: payments
  assumes spa: "spa_pred N b x p"
  shows "vickrey_payment N p"
proof -
  from spa have card_N: "card N > 1" unfolding spa_pred_def spa_admissible_input_def by simp
  then have maximum_defined: "maximum_defined N" unfolding spa_pred_def maximum_defined_def by auto
  from spa obtain i where i_range: "i \<in> N"
    and i_pay: "p i = maximum (N - {i}) b"
    and losers_pay: "\<forall> j \<in> N . j \<noteq> i \<longrightarrow> p j = 0"
    using spa_payments by blast
  (* Note that if "card N = 1" were allowed, there would be no such k.  This seems fine for now,
     but in the next step it becomes apparent what we need "card N = 1" and thus this k_def for:
     for obtaining the fact `greater`, which talks about the second-highest bid and assumes 
     that it is defined. *)
  from card_N and i_range obtain k where k_def: "k \<in> N \<and> k \<noteq> i" 
    by (metis all_not_in_conv card.insert card_empty ex_least_nat_le finite.emptyI insertCI le0 monoid_add_class.add.right_neutral nonempty_iff not_less)
  from k_def and maximum_defined have greater: "maximum (N - {i}) b \<ge> b k" using maximum_except_is_greater_or_equal by blast
  also have "\<dots> \<ge> 0" using spa spa_pred_def second_price_auction_def spa_admissible_input_def bids_def non_negative_real_vector_def by (smt greater k_def)
  with i_pay and calculation have "p i \<ge> 0" by simp
  with i_range and losers_pay have "\<forall> k \<in> N . p k \<ge> 0" by auto
  with vickrey_payment_def show ?thesis ..
qed

lemma fs_spa_is_left_total :
  fixes A :: single_good_auction
    and t :: tie_breaker
  assumes fs_spa: "rel_all_sga_pred (fs_spa_pred' t) A"
  shows "sga_left_total A spa_admissible_input"
proof -
  {
    fix N :: participants and b :: bids
    assume admissible: "spa_admissible_input N b"
    (* Note that Isabelle says that "Max {}" exists (but of course can't specify it).
       However we are working with our own wrapped maximum definition anyway. *)
    then obtain winner::participant where winner_def: "winner \<in> N \<and> winner = arg_max_tb N t b"
      using spa_admissible_input_def
        arg_max_set_def arg_max_tb.simps arg_max_tb_imp_arg_max_set
        maximum_def maximum_is_component maximum_defined_def
      by (smt mem_Collect_eq)
    (* Now that we know the winner exists, let's construct a suitable allocation and payments. *)
    def x \<equiv> "\<lambda> i::participant . if i = winner then 1::real else 0"
    def p \<equiv> "\<lambda> i::participant . if i = winner then maximum (N - {i}) b else 0"
    from x_def and p_def and winner_def and admissible
      have "fs_spa_pred N b t x p"
      using spa_admissible_input_def
        second_price_auction_winner_def second_price_auction_winner_outcome_def second_price_auction_loser_def
        fs_spa_pred_def
      by auto
    with fs_spa have "\<exists> (x :: allocation) (p :: payments) . ((N, b), (x, p)) \<in> A"
      using fs_spa_pred'_def spa_pred_def rel_all_sga_pred_def by auto
  }
  then show ?thesis unfolding sga_left_total_def by blast
qed

(* CL: Neither for fs_spa_is_left_total nor here we needed to assume wf_tie_breaker_on_participants,
   so what _do_ we need it for? *)
lemma fs_spa_is_right_unique :
  fixes A :: single_good_auction
    and t :: tie_breaker
  assumes fs_spa: "rel_all_sga_pred (fs_spa_pred' t) A"
  shows "fs_sga_right_unique A spa_admissible_input"
proof -
  {
    fix N :: participants and b :: bids
    assume admissible: "spa_admissible_input N b"
    fix x :: allocation and x' :: allocation and p :: payments and p' :: payments

    assume "((N, b), (x, p)) \<in> A"
    with fs_spa have "fs_spa_pred N b t x p" unfolding rel_all_sga_pred_def fs_spa_pred'_def by blast
    then obtain winner::participant
      where range: "winner \<in> N \<and> winner = arg_max_tb N t b"
        and alloc: "x winner = 1 \<and> (\<forall> j \<in> N . j \<noteq> winner \<longrightarrow> x j = 0)"
        and pay: "p winner = maximum (N - {winner}) b \<and> (\<forall>j \<in> N . j \<noteq> winner \<longrightarrow> p j = 0)"
      unfolding fs_spa_pred_def second_price_auction_def second_price_auction_winner_def second_price_auction_winner_outcome_def second_price_auction_loser_def
      by blast
    
    assume "((N, b), (x', p')) \<in> A"
    with fs_spa have "fs_spa_pred N b t x' p'" unfolding rel_all_sga_pred_def fs_spa_pred'_def by blast
    then obtain winner'::participant
      where range': "winner' \<in> N \<and> winner' = arg_max_tb N t b"
        and alloc': "x' winner' = 1 \<and> (\<forall> j \<in> N . j \<noteq> winner' \<longrightarrow> x' j = 0)"
        and pay': "p' winner' = maximum (N - {winner'}) b \<and> (\<forall>j \<in> N . j \<noteq> winner' \<longrightarrow> p' j = 0)"
      unfolding fs_spa_pred_def second_price_auction_def second_price_auction_winner_def second_price_auction_winner_outcome_def second_price_auction_loser_def
      by blast

    from range alloc pay range' alloc' pay' have "vectors_equal N x x' \<and> vectors_equal N p p'" unfolding vectors_equal_def by metis
  }
  then show ?thesis unfolding sga_right_unique_def fs_sga_right_unique_def by blast
qed

(* TODO CL: This lemma also works when admissibility is defined as "card N > 0" because
   when we compute the second-highest bid for the payments vector, card N = 0 will 
   boil down to the question of whether Max {} exists.  Isabelle says that it exists; to see this try

lemma max_exists : "\<exists>x . x = Max {}" by blast

  This is an inherent trait of Isabelle's HOL implementation: all functions are total in principle, 
  just sometimes underspecified, so that you don't know _what_ "Max {}" is.  To see this try

value "Max {}"

  vs.

value "Max {1::nat, 2}"

  Isabelle supports partial functions.  One can either use explicit undefinedness (using the Option datatype with the None and Some constructors),
  but that would affect and thus bloat large parts of our formalisation.

  In "isabelle doc functions" section 7 there is also something that looks like a more sophisticated support for 
  partial functions.

  For now, spa_is_left_total doesn't catch the case "card N = 1", but spa_vickrey_payment, which is
  part of our checks whether the outcome is well-defined, doesn't work for "case N = 1".  For precise
  details, see the comment in spa_vickrey_payment.

  So, @CR, this is really a good justification for why we need spa_vickrey_payment.  Indeed the whole
  battery of case checks now covers: "for each admissible input there is (that's left-totality) a 
  unique (that's right-uniqueness), well-defined (that's spa_vickrey_payment and spa_allocates) outcome."
*)
text{* Our relational definition of second price auction is left-total. *}
lemma spa_is_left_total :
  fixes A :: single_good_auction
  (* A is the set of all second price auctions.
     Assuming "second_price_auction A" would merely mean that all elements of A are second price auctions,
     which is not enough here. *)
  assumes spa: "rel_all_sga_pred spa_pred A"
  shows "sga_left_total A spa_admissible_input"
proof -
  def t \<equiv> "op>::(participant \<Rightarrow> participant \<Rightarrow> bool)"
  (* Note that it is not necessary to prove that fs_spa_pred' is satisfiable. *)
  def fs_spa_pred'' \<equiv> "\<lambda> tup . (\<exists> N b x p . tup = ((N, b), (x, p)) \<and> (fs_spa_pred' t) N b x p)"
  then have "\<exists> A . (\<forall> tup . tup \<in> A \<longleftrightarrow> fs_spa_pred'' tup)" by (metis mem_Collect_eq)
  with fs_spa_pred''_def have "\<exists> A . (\<forall> a b c d . ((a, b), (c, d)) \<in> A \<longleftrightarrow> (fs_spa_pred' t) a b c d)" by simp
  then have "\<exists> B . rel_all_sga_pred (fs_spa_pred' t) B" unfolding rel_all_sga_pred_def .
  then obtain B where B_fs_spa: "rel_all_sga_pred (fs_spa_pred' t) B" ..
  with spa have sup: "B \<subseteq> A" using rel_all_fs_spa_is_spa by simp
  from B_fs_spa fs_spa_is_left_total have B_left_total: "sga_left_total B spa_admissible_input" by simp
  with sup B_left_total show ?thesis using left_total_suprel by simp
qed

text{* We consider two outcomes of a second price auction equivalent if 
\begin{enumerate}
\item the bids of the participants to which the good is allocated are equal
\item the bids of the participants with positive payments are equal
\end{enumerate}
This should be as weak as possible, as not to accidentally restate the full definition of a second price auction.
 *}
definition spa_equivalent_outcome :: "participants \<Rightarrow> bids \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool"
  where "spa_equivalent_outcome N b x p x' p' \<longleftrightarrow> 
    b ` { i \<in> N . x i = 1 } = b ` { i \<in> N . x' i = 1 } \<and>
    b ` { i \<in> N . p i > 0 } = b ` { i \<in> N . p' i > 0 }"
(* This definition is more general in that it allow for divisible goods. *)

text{* Under certain conditions we can show that 
  the bids of the participants with positive payments are equal
  (one direction of the equality) *}
lemma positive_payment_bids_eq_suff :
  fixes N :: participants
    and winner :: participant
    and b :: bids
    and p :: payments
    and p' :: payments
  assumes admissible: "spa_admissible_input N b"
      and range: "winner \<in> N \<and> winner \<in> arg_max_set N b"
      and pay: "p winner = maximum (N - {winner}) b \<and> (\<forall>j \<in> N . j \<noteq> winner \<longrightarrow> p j = 0)"
      and range': "winner' \<in> N \<and> winner' \<in> arg_max_set N b"
      and pay': "p' winner' = maximum (N - {winner'}) b \<and> (\<forall>j \<in> N . j \<noteq> winner' \<longrightarrow> p' j = 0)"
  shows "b ` { i \<in> N . p i > 0 } \<subseteq> b ` { i \<in> N . p' i > 0 }"
proof (intro subsetI)
  from admissible have bids: "bids N b" and ge2: "card N > 1"
    using spa_admissible_input_def by auto
  fix bid assume premise: "bid \<in> b ` { i \<in> N . p i > 0 }"
  with range pay range' have bw': "bid = b winner'" using arg_max_set_def by auto
  from premise pay have p_positive: "p winner > 0" by auto
  with ge2 range pay have bwpos: "b winner > 0"
    using arg_max_set_def maximum_except_defined maximum_remaining_maximum by (smt mem_Collect_eq)
  from ge2 range' have md: "maximum_defined (N - {winner'})" using maximum_except_defined by blast
  have "maximum (N - {winner'}) b > 0"
  proof (rule ccontr)
    assume assm: "\<not> maximum (N - {winner'}) b > 0"
    {
      fix i assume i_range: "i \<in> (N - {winner'})"
      with bids have bipos: "b i \<ge> 0" unfolding bids_def non_negative_real_vector_def by blast
      from md have "maximum (N - {winner'}) b \<ge> b i" using i_range maximum_is_greater_or_equal by simp
      then have "maximum (N - {winner'}) b = 0" using assm bipos by simp
    }
    with assm range range' pay pay' have foow': "maximum (N - {winner'}) b = 0"
      using maximum_is_component md by metis
    show False
    proof cases
      assume "winner' = winner"
      then show False using p_positive pay foow' by auto
    next
      assume "winner' \<noteq> winner"
      with range have "winner \<in> N - {winner'}" by fast
      then have x: "maximum (N - {winner'}) b \<ge> b winner" using range maximum_is_greater_or_equal md by blast
      with foow' have bwzn: "b winner \<le> 0" by auto
      from range have "maximum N b = b winner" using arg_max_set_def by auto
      with md x maximum_remaining_maximum bwpos bwzn show False by auto
    qed
  qed
  then show "bid \<in> b ` { i \<in> N . p' i > 0 }" using range' pay' bw' by auto
qed

text{* Our relational definition of second price auction is right-unique. *}
lemma spa_is_right_unique :
  fixes A :: single_good_auction
  (* A is the set of all second price auctions.
     Assuming "second_price_auction A" would merely mean that all elements of A are second price auctions,
     which is not enough here. *)
  assumes spa: "rel_all_sga_pred spa_pred A"
  shows "sga_right_unique A spa_admissible_input spa_equivalent_outcome"
proof -
  {
    fix N :: participants and b :: bids
    assume admissible: "spa_admissible_input N b"
    fix x :: allocation and x' :: allocation and p :: payments and p' :: payments

    assume "((N, b), (x, p)) \<in> A"
    with spa have "spa_pred N b x p" unfolding rel_all_sga_pred_def by blast
    then obtain winner::participant
      where range: "winner \<in> N \<and> winner \<in> arg_max_set N b"
        and alloc: "x winner = 1 \<and> (\<forall> j \<in> N . j \<noteq> winner \<longrightarrow> x j = 0)"
        and pay: "p winner = maximum (N - {winner}) b \<and> (\<forall>j \<in> N . j \<noteq> winner \<longrightarrow> p j = 0)"
      unfolding spa_pred_def second_price_auction_def second_price_auction_winner_def second_price_auction_winner_outcome_def second_price_auction_loser_def
      by blast

    assume "((N, b), (x', p')) \<in> A"
    with spa have "spa_pred N b x' p'" unfolding rel_all_sga_pred_def by blast
    then obtain winner'::participant
      where range': "winner' \<in> N \<and> winner' \<in> arg_max_set N b"
        and alloc': "x' winner' = 1 \<and> (\<forall> j \<in> N . j \<noteq> winner' \<longrightarrow> x' j = 0)"
        and pay': "p' winner' = maximum (N - {winner'}) b \<and> (\<forall>j \<in> N . j \<noteq> winner' \<longrightarrow> p' j = 0)"
      unfolding spa_pred_def second_price_auction_def second_price_auction_winner_def second_price_auction_winner_outcome_def second_price_auction_loser_def
      by blast

    have "b ` { i \<in> N . x i = 1 } = b ` { i \<in> N . x' i = 1 }"
    proof (intro equalityI) (* CL: any way to collapse these two cases into one? *)
      from range alloc range' alloc' show "b ` { i \<in> N . x i = 1 } \<subseteq> b ` { i \<in> N . x' i = 1 }"
        using arg_max_set_def by auto
    next
      from range' alloc' range alloc show "b ` { i \<in> N . x' i = 1 } \<subseteq> b ` { i \<in> N . x i = 1 }"
        using arg_max_set_def by auto
    qed
    moreover have "b ` { i \<in> N . p i > 0 } = b ` { i \<in> N . p' i > 0 }"
    proof (intro equalityI) (* CL: any way to collapse these two cases into one? *)
      from admissible range pay range' pay' show "b ` { i \<in> N . p i > 0 } \<subseteq> b ` { i \<in> N . p' i > 0 }"
        using positive_payment_bids_eq_suff by simp
    next
      from admissible range' pay' range pay show "b ` { i \<in> N . p' i > 0 } \<subseteq> b ` { i \<in> N . p i > 0 }"
        using positive_payment_bids_eq_suff by simp
    qed
    ultimately have "spa_equivalent_outcome N b x p x' p'" unfolding spa_equivalent_outcome_def ..
  }
  then show ?thesis unfolding sga_right_unique_def by blast
qed

lemma spa_is_sga_pred :
  fixes N :: participants and b :: bids
    and x :: allocation and p :: payments
  assumes "spa_pred N b x p"
  shows "sga_pred N b x p"
  using assms
  unfolding spa_pred_def spa_admissible_input_def sga_pred_def by simp

lemma spa_is_sga :
  fixes A :: single_good_auction
  assumes spa: "second_price_auction A"
  shows "single_good_auction A"
proof -
  {
    fix N :: participants and b :: bids and x :: allocation and p :: payments
    assume "((N, b), (x, p)) \<in> A"
    with spa have "spa_pred N b x p" unfolding second_price_auction_def rel_sat_sga_pred_def by blast
    then have "sga_pred N b x p" using spa_is_sga_pred by blast
  }
  then show ?thesis unfolding single_good_auction_def rel_sat_sga_pred_def by blast
qed

lemma spa_allocates_binary :
  fixes N :: participants and b :: bids
    and x :: allocation and p :: payments
    and i :: participant
  assumes "spa_pred N b x p"
      and "i \<in> N"
  shows "x i = 0 \<or> x i = 1"
  using assms
  unfolding spa_pred_def second_price_auction_def second_price_auction_winner_def second_price_auction_winner_outcome_def second_price_auction_loser_def
  by fast

lemma allocated_implies_spa_winner:
  fixes N :: participants and b :: bids
     and x :: allocation and p :: payments
     and winner :: participant
  assumes "spa_pred N b x p"
    and "winner \<in> N"
    and "x winner = 1"
  shows "second_price_auction_winner N b x p winner"
  using assms
  unfolding spa_pred_def second_price_auction_def second_price_auction_winner_def second_price_auction_loser_def
    allocation_def
  by (metis zero_neq_one)
    (* CL: With the generalised allocation_def, this proof needed a bit more complexity,
         as "x winner = 1" implies "x i = 0" for all other participants is rather implicit now. *)

lemma not_allocated_implies_spa_loser:
  fixes N :: participants and b :: bids
    and x :: allocation and p :: payments
    and loser :: participant
  assumes spa: "spa_pred N b x p"
    and range: "loser \<in> N"
    and loses: "x loser = 0"
  shows "second_price_auction_loser N x p loser"
proof -
  from loses have "\<not> second_price_auction_winner N b x p loser"
    unfolding second_price_auction_winner_def second_price_auction_winner_outcome_def by simp
  with spa range show ?thesis
      unfolding spa_pred_def second_price_auction_def by fast
qed

lemma only_max_bidder_wins:
  fixes N :: participants and max_bidder :: participant
    and b :: bids and x :: allocation and p :: payments
  assumes defined: "maximum_defined N"
    and spa: "spa_pred N b x p"
    and range: "max_bidder \<in> N"
    and only_max_bidder: "b max_bidder > maximum (N - {max_bidder}) b"
  shows "second_price_auction_winner N b x p max_bidder"
proof -
  from spa have spa_unfolded:
    "spa_admissible_input N b \<and> (\<exists>i. second_price_auction_winner N b x p i \<and>
      (\<forall>j \<in> N. j \<noteq> i \<longrightarrow> second_price_auction_loser N x p j))"
    unfolding spa_pred_def second_price_auction_def by blast
  {
    fix j :: participant
    assume j_not_max: "j \<in> N \<and> j \<noteq> max_bidder"
    have "j \<notin> arg_max_set N b"
    proof
      assume "j \<in> arg_max_set N b"
      then have maximum: "b j = maximum N b" unfolding arg_max_set_def by simp

      from j_not_max range have "b j \<le> maximum (N - {max_bidder}) b"
        using defined maximum_except_is_greater_or_equal by simp
      with only_max_bidder have *: "b j < b max_bidder" by simp

      from defined range maximum have "b j \<ge> b max_bidder"
        by (simp add: maximum_is_greater_or_equal)
      with * show False by simp
    qed
  }
    with spa_unfolded show ?thesis
    by (auto simp add: second_price_auction_winner_def)
qed

lemma second_price_auction_winner_payoff:
  fixes N :: participants and v :: valuations and x :: allocation
    and b :: bids and p :: payments and winner :: participant
  assumes defined: "maximum_defined N"
    and spa: "spa_pred N b x p"
    and i_range: "i \<in> N"
    and wins: "x i = 1"
  shows "payoff (v i) (x i) (p i) = v i - maximum (N - {i}) b"
proof -
  have "payoff (v i) (x i) (p i) = v i - p i"
    using wins unfolding payoff_def by simp
  also have "\<dots> = v i - maximum (N - {i}) b"
    using defined spa i_range wins
      using allocated_implies_spa_winner
    unfolding second_price_auction_winner_def second_price_auction_winner_outcome_def
    by simp
  finally show ?thesis .
qed

lemma second_price_auction_loser_payoff:
  fixes N :: participants and v :: valuations and x :: allocation
    and b :: bids and p :: payments and loser :: participant
  assumes "spa_pred N b x p"
    and "i \<in> N"
    and "x i = 0"
  shows "payoff (v i) (x i) (p i) = 0"
  using assms not_allocated_implies_spa_loser
  unfolding second_price_auction_loser_def payoff_def by simp

lemma winners_payoff_on_deviation_from_valuation:
  fixes N :: participants and v :: valuations and x :: allocation
    and b :: bids and p :: payments and winner :: participant
  assumes "maximum_defined N"
    and "spa_pred N b x p"
    and "i \<in> N"
    and "x i = 1"
  shows "payoff (v i) (x i) (p i) = v i - maximum (N - {i}) (b(i := v i))"
  using assms second_price_auction_winner_payoff remaining_maximum_invariant
  by simp

section {* Some properties that single good auctions can have *}

subsection {* Efficiency *}

definition efficient :: "participants \<Rightarrow> valuations \<Rightarrow> bids \<Rightarrow> single_good_auction \<Rightarrow> bool"
  where
    "efficient N v b A \<longleftrightarrow>
      valuations N v \<and> bids N b \<and> single_good_auction A \<and>
      (\<forall> x p . ((N, b), (x, p)) \<in> A
        (* TODO CL: Is there a way of not naming p, as we don't need it? *)
        \<longrightarrow>
        (\<forall>i \<in> N. x i = 1 \<longrightarrow> i \<in> arg_max_set N v))"

subsection {* Equilibrium in weakly dominant strategies *}

definition equilibrium_weakly_dominant_strategy ::
  "participants \<Rightarrow> valuations \<Rightarrow> bids \<Rightarrow> single_good_auction \<Rightarrow> bool" where
  "equilibrium_weakly_dominant_strategy N v b A \<longleftrightarrow>
    valuations N v \<and> bids N b \<and> single_good_auction A \<and>
    (\<forall>i \<in> N.
      (\<forall>whatever_bid . bids N whatever_bid \<and> whatever_bid i \<noteq> b i \<longrightarrow>
        (let b' = whatever_bid(i := b i)
         in 
         (\<forall> x p x' p' . ((N, whatever_bid), (x, p)) \<in> A \<and> ((N, b'), (x', p')) \<in> A
          \<longrightarrow>
          payoff (v i) (x' i) (p' i) \<ge> payoff (v i) (x i) (p i)))))"

section {* Vickrey's Theorem *}

subsection {* Part 1: A second-price auction supports an equilibrium in weakly dominant
  strategies if all participants bid their valuation. *}

theorem vickreyA:
  fixes N :: participants and v :: valuations and A :: single_good_auction
  assumes val: "valuations N v" 
  defines "b \<equiv> v"
  assumes spa: "second_price_auction A"
      and card_N: "card N > 1"
  shows "equilibrium_weakly_dominant_strategy N v b A"
proof -
  have defined: "maximum_defined N" using card_N
    unfolding maximum_defined_def by (auto simp: card_ge_0_finite)
  then have finite: "finite N" by (metis card_N card_infinite less_nat_zero_code)

  from val have bids: "bids N b"
    unfolding b_def by (rule valuation_is_bid)
  {
    fix i :: participant
    assume i_range: "i \<in> N"

    let ?M = "N - {i}"
    have defined': "maximum_defined ?M"
      using card_N i_range unfolding maximum_defined_def
      by (simp add: card_ge_0_finite card_Diff_singleton)

    fix whatever_bid :: bids
    assume alternative_is_bid: "bids N whatever_bid"
    (* TOOD CL: also assume "whatever_bid i \<noteq> b i"? *)

    let ?b = "whatever_bid(i := b i)"
    
    have is_bid: "bids N ?b"
      using bids alternative_is_bid
      unfolding bids_def non_negative_real_vector_def by simp

    let ?b_max = "maximum N ?b"
    let ?b_max' = "maximum ?M ?b"

    fix x :: allocation and x' :: allocation and p :: payments and p' :: payments
    assume outcome: "((N, whatever_bid), (x, p)) \<in> A"
       and outcome': "((N, ?b), (x', p')) \<in> A"

    from spa outcome have spa_pred: "spa_pred N whatever_bid x p"
      unfolding second_price_auction_def rel_sat_sga_pred_def by blast
    from spa outcome' have spa_pred': "spa_pred N ?b x' p'"
      unfolding second_price_auction_def rel_sat_sga_pred_def by blast

    from spa_pred finite have allocation: "allocation N x" using spa_allocates by blast
    from spa_pred' finite have allocation': "allocation N x'" using spa_allocates by blast
    from spa_pred card_N have pay: "vickrey_payment N p" using spa_vickrey_payment by blast
    from spa_pred' card_N have pay': "vickrey_payment N p'" using spa_vickrey_payment by blast

    have weak_dominance:
      "payoff (v i) (x' i) (p' i) \<ge> payoff (v i) (x i) (p i)"
    proof cases
      assume alloc: "x' i = 1"
      with spa_pred' i_range
      have winner: "second_price_auction_winner N ?b x' p' i"
        by (rule allocated_implies_spa_winner)

      from winner have "?b i = ?b_max"
        unfolding second_price_auction_winner_def arg_max_set_def by simp
      with defined' have "?b i \<ge> ?b_max'"
        by (rule maximum_remaining_maximum)

      from winner have "p' i = ?b_max'"
        unfolding second_price_auction_winner_def second_price_auction_winner_outcome_def
        by simp

      have winner_payoff: "payoff (v i) (x' i) (p' i) = v i - ?b_max'"
        using defined spa_pred' i_range alloc
        by (rule second_price_auction_winner_payoff)

      have non_negative_payoff: "payoff (v i) (x' i) (p' i) \<ge> 0"
      proof -
        from `?b i \<ge> ?b_max'` have "?b i - ?b_max' \<ge> 0" by simp
        with winner_payoff show ?thesis unfolding b_def by simp
      qed

      show ?thesis
      proof cases -- {* case 1a of the short proof *}
        assume "x i = 1"
        with defined spa_pred alternative_is_bid i_range
        have "payoff (v i) (x i) (p i) = v i - ?b_max'"
          using winners_payoff_on_deviation_from_valuation unfolding b_def by simp
        also have "\<dots> = payoff (v i) (x' i) (p' i)" using winner_payoff ..
        finally show ?thesis by (rule eq_refl)
      next -- {* case 1b of the short proof *}
        assume "x i \<noteq> 1"
        (* CL: TODO I'm sure one can use spa_allocates_binary at the top level of the 
               case distinction, to get rid of having to do this step for each case distinction. *)
        with spa_pred alternative_is_bid i_range have "x i = 0"
          using spa_allocates_binary by blast
        with spa_pred i_range
        have "payoff (v i) (x i) (p i) = 0"
          by (rule second_price_auction_loser_payoff)
        also have "\<dots> \<le> payoff (v i) (x' i) (p' i)" using non_negative_payoff .
        finally show ?thesis .
      qed

    next -- {* case 2 of the short proof *}
      assume non_alloc: "x' i \<noteq> 1"
      (* CL: TODO I'm sure one can use spa_allocates_binary at the top level of the 
             case distinction, to get rid of having to do this step for each case distinction. *)
      with spa_pred' i_range have "x' i = 0"
        using spa_allocates_binary by blast
      with spa_pred' i_range
      have loser_payoff: "payoff (v i) (x' i) (p' i) = 0"
        by (rule second_price_auction_loser_payoff)

      have i_bid_at_most_second: "?b i \<le> ?b_max'"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have "?b i > ?b_max'" by simp
        with defined spa_pred' i_range
        have "second_price_auction_winner N ?b x' p' i"
          using only_max_bidder_wins by simp
        with non_alloc show False using second_price_auction_winner_def second_price_auction_winner_outcome_def by simp
      qed

      show ?thesis
      proof cases -- {* case 2a of the short proof *}
        assume "x i = 1"
        with defined spa_pred i_range
        have "payoff (v i) (x i) (p i) = ?b i - ?b_max'"
          using winners_payoff_on_deviation_from_valuation unfolding b_def by simp
        also have "\<dots> \<le> 0" using i_bid_at_most_second by simp
        also have "\<dots> = payoff (v i) (x' i) (p' i)" using loser_payoff ..
        finally show ?thesis .
      next -- {* case 2b of the short proof *}
        assume "x i \<noteq> 1"
        (* CL: TODO I'm sure one can use spa_allocates_binary at the top level of the 
               case distinction, to get rid of having to do this step for each case distinction. *)
        with spa_pred alternative_is_bid i_range have "x i = 0"
          using spa_allocates_binary by blast
        with spa_pred i_range
        have "payoff (v i) (x i) (p i) = 0"
          by (rule second_price_auction_loser_payoff)
        also have "\<dots> = payoff (v i) (x' i) (p' i)" using loser_payoff ..
        finally show ?thesis by (rule eq_refl)
      qed
    qed
  }
  with spa val bids show ?thesis
    using spa_is_sga
    unfolding equilibrium_weakly_dominant_strategy_def
    by auto
qed


subsection {* Part 2: A second-price auction is efficient if all participants bid their valuation. *}

theorem vickreyB:
  fixes N :: participants and v :: valuations and A :: single_good_auction
  assumes val: "valuations N v"
  assumes spa: "second_price_auction A"
  defines "b \<equiv> v"
  shows "efficient N v b A"
proof -
  from val have bids: "bids N v" by (rule valuation_is_bid)
  {
    fix k :: participant and x :: allocation and p :: payments
    (* TODO CL: We actually don't need p; is there a way to do without? *)
    assume range: "k \<in> N" and outcome: "((N, v), (x, p)) \<in> A" and wins: "x k = 1"
    from outcome spa have "spa_pred N v x p"
      unfolding second_price_auction_def rel_sat_sga_pred_def
      by blast
    with range and wins have "k \<in> arg_max_set N v"
      using allocated_implies_spa_winner
      unfolding second_price_auction_winner_def by blast
  }
  with bids spa show ?thesis
    using val unfolding b_def efficient_def using spa_is_sga by blast
qed

code_include Scala ""
{*package code
*}
export_code fs_spa_winner fs_spa_allocation fs_spa_payments in Scala
(* In SML, OCaml and Scala "file" is a file name; in Haskell it's a directory name ending with / *)
module_name Vickrey file "code/code.scala"
(* A trivial example to try interactively with the generated Scala code:

:load code.scala
Vickrey.times_int(Vickrey.Zero_int(), Vickrey.Zero_int())

Notes:
* There are apparently no ready-to-use code-unfold theorems (codegen \<section>2.2) in the library.
*)
print_codeproc
end
