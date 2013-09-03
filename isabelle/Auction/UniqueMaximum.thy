(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

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

header {* Maximum components of vectors (unique thanks to tie-breaking), and their properties *}

theory UniqueMaximum
imports Maximum FullySpecifiedSingleGoodAuction
begin

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

fun arg_max_tb :: "participant set \<Rightarrow> tie_breaker \<Rightarrow> bids \<Rightarrow> participant"
where "arg_max_tb N t b = arg_max_l_tb (sorted_list_of_set N) t b"

(* TODO CL: once proving properties of the list-based implementation of this function
   starts to hurt, follow Lars Noschinski's advice to use the list-based implementation for
   code generation only, and otherwise use an equivalent set-based definition.
   http://stackoverflow.com/questions/16702866/defining-an-arg-max-like-function-over-finite-sets-and-proving-some-of-its-pr#comment24451608_16707012 *)
fun arg_max_tb_req_wb :: "participant set \<Rightarrow> tie_breaker \<Rightarrow> bids \<rightharpoonup> participant"
where "arg_max_tb_req_wb N t b = (if (wb_tie_breaker_on t N)
  then Some (arg_max_tb N t b)
  else None)"

lemma arg_max_tb_wb:
  assumes "wb_tie_breaker_on t N" shows "arg_max_tb N t b = the (arg_max_tb_req_wb N t b)"
  using assms by simp

(* uncomment for testing:
value "arg_max_tb {2::nat, 4, 6} (* the participant indices *)
  op> (* the tie breaking function *)
  (\<lambda> i . nth [27::real, 42, 42] (i div 2 - 1::nat))"
*)

(* original code provided by Lars Noschinski on the Isabelle mailing list, 2013-05-22 *)
lemma sorted_list_of_set_remove': (* TODO CL: sorted_list_of_set_not_empty (for which this is needed) should be in the library in 2014; remove then *)
  assumes "finite A" "x \<in> A"
  shows "sorted_list_of_set A = insort x (sorted_list_of_set (A - {x}))" (is "?lhs = ?rhs")
proof -
  from assms have "insert x (A - {x}) = A" by blast
  then have "?lhs = sorted_list_of_set (insert x (A - {x}))" by simp
  also have "\<dots> = ?rhs" using assms by simp
  finally show ?thesis .
qed

(* code provided by Lars Noschinski on the Isabelle mailing list, 2013-05-22 *)
lemma sorted_list_of_set_eq_Nil_iff [simp] : (* TODO CL: should be in the library in 2014; remove then *)
  assumes "finite S"
  shows "sorted_list_of_set S = [] \<longleftrightarrow> S = {}"
using assms by (auto simp: sorted_list_of_set_remove')

text{* The highest bidder, determined by tie-breaking using @{term arg_max_tb},
  is one member of the set of all highest bidders, determined using @{term arg_max}. *}
lemma arg_max_tb_imp_arg_max :
  fixes N :: "participant set"
    and t :: tie_breaker
    and b :: bids
  assumes defined: "maximum_defined N"
      and wb_tie: "wb_tie_breaker_on t N"
  shows "the (arg_max_tb_req_wb N t b) \<in> arg_max N b"
(* A proof could be indirect by assuming that arg_max_tb N t b is not in the set,
   i.e., that the arg_max_tb offers less or more, and bring this to a contradiction.*)
proof -
  def Nsort \<equiv> "sorted_list_of_set N"
  from defined have finite: "finite N" and ne: "N \<noteq> {}"
    unfolding maximum_defined_def by (simp_all add: card_gt_0_iff)
  (* TODO CL: Isabelle 2014 might be able to do the following step more automatically: *)
  from finite Nsort_def sorted_list_of_set have distinct: "distinct Nsort" by auto
  from finite ne Nsort_def have "Nsort \<noteq> []" by simp
  then have stmt_list: "distinct Nsort \<longrightarrow> arg_max_l_tb Nsort t b \<in> arg_max (set Nsort) b"
  proof (induct Nsort rule: list_nonempty_induct)
    case single
    {
      fix x have "arg_max_l_tb [x] t b \<in> arg_max (set [x]) b"
        unfolding arg_max_def maximum_def Nsort_def by simp
    }
    then show ?case ..
  next
    case cons (* CL: How can I use the cons.*, that I'm getting here, below? *)
    fix x xs
    assume a1: "xs \<noteq> []" and a2: "distinct xs \<longrightarrow> arg_max_l_tb xs t b \<in> arg_max (set xs) b"
    from a1 have mdxs: "maximum_defined (set xs)" unfolding maximum_defined_def by (metis List.finite_set card_gt_0_iff set_empty2)
    from a1 have mdxs': "maximum_defined (set (x # xs))" unfolding maximum_defined_def by (metis List.finite_set card_gt_0_iff list.distinct(1) set_empty)
    show "distinct (x # xs) \<longrightarrow> arg_max_l_tb (x # xs) t b \<in> arg_max (set (x # xs)) b"
    proof
      assume distinct': "distinct (x # xs)"
      def i \<equiv> "arg_max_l_tb (x # xs) t b"
      with a1 have "i =
        (let y = arg_max_l_tb xs t b in
          if (b x > b y) then x
          else if (b x = b y \<and> t x y) then x
          else y)" by (metis arg_max_l_tb.simps(2,3) neq_Nil_conv)
      then have i_unf: "i = (let y = arg_max_l_tb xs t b in
          if (b x > b y \<or> b x = b y \<and> t x y) then x
          else y)" by smt
      show "i \<in> arg_max (set (x # xs)) b"
      proof (cases "i = arg_max_l_tb xs t b")
        case True (* the maximum is the same as before *)
        with a2 distinct' have ams: "i \<in> arg_max (set xs) b" by simp
        with mdxs have i_in: "i \<in> (set xs)" unfolding arg_max_def using maximum_is_component by simp
        then have i_in': "i \<in> (set (x # xs))" by simp
        from i_unf True have "\<not> (b x > b i \<or> b x = b i \<and> t x i)" by (smt distinct' distinct.simps(2) i_in)
        then have 1: "b x \<le> b i" by auto
        from ams have "b i = maximum (set xs) b" unfolding arg_max_def by simp
        with maximum_is_greater_or_equal mdxs have "\<forall> j \<in> (set xs) . b i \<ge> b j" by (metis (full_types))
        with 1 have "\<forall> j \<in> (set (x # xs)) . b i \<ge> b j" by simp
        with maximum_sufficient mdxs' i_in' have "b i = maximum (set (x # xs)) b" by metis
        with i_in' show ?thesis unfolding arg_max_def by simp
      next
        case False (* the newly inserted element x is the maximum *)
        def y \<equiv> "arg_max_l_tb xs t b"
        with i_unf have yi: "
          i = (if (b x > b y \<or> b x = b y \<and> t x y) then x
          else y)" by auto
        from y_def False have "i \<noteq> y" unfolding i_def by simp
        with yi have bi: "(b x > b y \<or> b x = b y \<and> t x y) \<and> i = x" by smt
        from y_def a2 distinct' have ams: "y \<in> arg_max (set xs) b" by simp
        with mdxs have y_in: "y \<in> (set xs)" unfolding arg_max_def using maximum_is_component by simp
        then have y_in': "y \<in> (set (x # xs))" by simp
        from ams have "b y = maximum (set xs) b" unfolding arg_max_def by simp
        with maximum_is_greater_or_equal mdxs have "\<forall> j \<in> (set xs) . b y \<ge> b j" by (metis (full_types))
        with bi have "\<forall> j \<in> (set xs) . b x \<ge> b j" by auto (* because b x \<ge> b y *)
        then have "\<forall> j \<in> (set (x # xs)) . b x \<ge> b j" by simp
        with maximum_sufficient mdxs' have "b x = maximum (set (x # xs)) b" by (metis distinct' distinct.simps(2) distinct_length_2_or_more)
        with bi show ?thesis unfolding arg_max_def by simp
      qed
    qed
  qed
  from Nsort_def `finite N` have "N = set Nsort" by simp
  from Nsort_def wb_tie have "the (arg_max_tb_req_wb N t b) = arg_max_l_tb Nsort t b" by simp
  with distinct stmt_list have "the (arg_max_tb_req_wb N t b) \<in> arg_max (set Nsort) b" by simp
  with `N = set Nsort` show ?thesis by simp
qed

end

