(*
Author: Aadish Kumar
Thank you to Dr Colin Rowat and Dr Marco Caminati for their guidance and support
*)

theory RET
imports 
 "~~/src/HOL/Multivariate_Analysis/Integration"
begin

definition win_prob :: "nat \<Rightarrow> real \<Rightarrow> real"
where "win_prob i = real"

definition payment :: "nat \<Rightarrow> real \<Rightarrow> real"
where "payment i = real"

definition surplus :: "nat \<Rightarrow> real \<Rightarrow> real" 
where "surplus i v = (win_prob i v)*v - (payment i v)"

(*
Formal proof of the Revenue Equivalence Theorem over an open interval V.
*)

theorem RevenueEquivalenceTheorem:
  fixes N::"nat set"
  assumes "i\<in>N"
  and val_int: "V={a<..<b}"
  and win_prob_continuous_within_val: "continuous_on {a<..<b} (win_prob i)"
  and surplus_continuous: "continuous_on {a..b} (surplus i)"
  and truth_constraint: "\<forall>w\<in>V. \<forall>v\<in>V. (win_prob i v)*v - (payment i v) \<ge> (win_prob i w)*v 
  - (payment i w)"

(*
For the assumption win_prob_continuous_within_val, I stated (win_prob i) is continuous_on {a<..<b}
as it is less stricter than continuous_on {a..b} *)

  shows "\<forall>w\<in>V. (payment i w) = (win_prob i w)*w - integral {a .. w} (win_prob i) - (surplus i a)"
proof-
  have first_inequality: "\<forall>w\<in>V. \<forall>h. (w+h \<in> V) \<longrightarrow> h * (win_prob i w) \<le> surplus i (w+h) 
  - surplus i w"
  proof-
    have substitute_1: "\<forall>w\<in>V. \<forall>v\<in>V. surplus i v - surplus i w \<ge> (win_prob i w)*v 
    - w*(win_prob i w)"
    using truth_constraint surplus_def by fastforce
    have factorise_1: "\<forall>w\<in>V. \<forall>v\<in>V. surplus i v - surplus i w \<ge> (v-w)*(win_prob i w)"
    using substitute_1 by (simp add: algebra_simps)
  show ?thesis using factorise_1 by fastforce
  qed
  have second_inequality: "\<forall>w\<in>V. \<forall>h. (w+h)\<in>V \<longrightarrow> surplus i (w+h) - surplus i w \<le> h * 
  win_prob i (w+h)"
  proof-
    have truth_type_w: "\<forall>w\<in>V. \<forall>v\<in>V. (win_prob i w)*w - (payment i w) \<ge> (win_prob i v)*w 
    - (payment i v)"
    using truth_constraint by auto
    have substitute_2: "\<forall>w\<in>V. \<forall>v\<in>V. surplus i w - surplus i v \<ge> (win_prob i v)*w 
    - v*(win_prob i v)"
    using truth_constraint truth_type_w surplus_def by fastforce
    have factorise_2: "\<forall>w\<in>V. \<forall>v\<in>V. surplus i v - surplus i w \<le> (v-w)*(win_prob i v)"
    using substitute_2 by (simp add: algebra_simps)
  show ?thesis using factorise_2 by fastforce
  qed
  have open_val: "open V" using val_int by auto

(* open interval needed to take limits below *)

  have limit_both: "\<forall>w\<in>V. ((\<lambda>h. (surplus i (w+h) - surplus i w) / h) ---> win_prob i w) (at 0)"
  proof-

(* taking limits as h approaches 0 from left and from right *)

    have limit_right: "\<forall>w\<in>V. ((\<lambda>h. (surplus i (w+h) - surplus i w) / h) ---> win_prob i w) 
    (at_right 0)"
    proof-                  
    have first_ev: "\<forall>w\<in>V. eventually (\<lambda>h. win_prob i w \<le> (surplus i (w+h) - surplus i w) / h) 
    (at_right 0)"
      unfolding eventually_at at_right_eq
      using first_inequality open_val always_eventually
      apply (simp add: divide_simps mult_ac)
      by (metis (no_types, hide_lams) add.commute diff_0_right diff_add_cancel 
        diff_minus_eq_add dist_norm open_real_def)
    have second_ev: "\<forall>w\<in>V. eventually (\<lambda>h. (surplus i (w+h) - surplus i w) / h \<le> win_prob i (w+h)) 
    (at_right 0)"
      unfolding eventually_at at_right_eq
      using open_val always_eventually
      apply (simp add: divide_simps mult_ac)
      by (metis (no_types, hide_lams) add.commute second_inequality diff_0_right diff_add_cancel 
        diff_minus_eq_add dist_norm open_real_def)
    have lim_wh: "\<forall>w\<in>V. ((\<lambda>h. win_prob i (w+h)) ---> win_prob i w) (at_right 0)"
      using open_val win_prob_continuous_within_val val_int
      by (metis LIM_offset_zero_iff at_within_open continuous_on_def filterlim_at_split)
    have lim_w: "\<forall>w\<in>V. ((\<lambda>h. win_prob i (w)) ---> win_prob i w) (at_right 0)"

(* lim_wh and lim_w could be proven at filter (at 0) using the same methods, and then used with 
first_ev and second_ev to prove limit_left and limit_right, however I've proved them for (at_left 0)
and (at_right 0) separately to make it easier to follow) *)

      by (auto intro!: tendsto_eq_intros)
  show ?thesis using first_ev second_ev lim_wh lim_w real_tendsto_sandwich by fastforce
  qed
  have limit_left: "\<forall>w\<in>V. ((\<lambda>h. (surplus i (w+h) - surplus i w) / h) ---> win_prob i w) 
  (at_left 0)"
  proof-                  
    have first_ev: "\<forall>w\<in>V. eventually (\<lambda>h. win_prob i w \<ge> (surplus i (w+h) - surplus i w) / h) 
    (at_left 0)"
      unfolding eventually_at at_left_eq
      using open_val always_eventually
      apply (simp add: divide_simps mult_ac)
      by (metis (no_types, hide_lams) add.commute first_inequality diff_0_right diff_add_cancel  
      diff_minus_eq_add dist_norm open_real_def)
    have second_ev: "\<forall>w\<in>V. eventually (\<lambda>h. (surplus i (w+h) - surplus i w) / h \<ge> win_prob i (w+h)) 
    (at_left 0)"
      unfolding eventually_at at_left_eq
      using open_val always_eventually
      apply (simp add: divide_simps mult_ac)
      by (metis (no_types, hide_lams) add.commute second_inequality diff_0_right diff_add_cancel 
        diff_minus_eq_add dist_norm open_real_def)

    have lim_wh: "\<forall>w\<in>V. ((\<lambda>h. win_prob i (w+h)) ---> win_prob i w) (at_left 0)"
      using open_val win_prob_continuous_within_val val_int
      by (metis LIM_offset_zero_iff at_within_open continuous_on_def filterlim_at_split)

    have lim_w: "\<forall>w\<in>V. ((\<lambda>h. win_prob i (w)) ---> win_prob i w) (at_left 0)"
      by (auto intro!: tendsto_eq_intros)
    show ?thesis using first_ev second_ev lim_wh lim_w real_tendsto_sandwich by fast
    qed
  show ?thesis using limit_left limit_right 
    using filterlim_split_at_real by blast
  qed
  have surplus_deriv: "\<forall>w\<in>{a<..<b}. (surplus i has_vector_derivative win_prob i w) (at w)"
  using limit_both val_int DERIV_def has_field_derivative_iff_has_vector_derivative by blast

 have win_prob_integral: "\<forall>w\<in>{a<..<b}. (win_prob i has_integral (surplus i w - surplus i a)) 
    {a..w}"
    proof-
      have continuous_on_val_int: "\<forall>x\<in>{a<..<b}. continuous_on {a..x} (surplus i)" 
      using continuous_on_subset surplus_continuous by fastforce
      have deriv_within_val_int: "\<forall>w\<in>{a<..<b}. \<forall>x\<in>{a<..<w}. (surplus i has_vector_derivative 
      win_prob i x) (at x)" 
      using surplus_deriv by simp
      show ?thesis
        apply safe                          
        apply (rule fundamental_theorem_of_calculus_interior)
        by (auto simp: continuous_on_val_int deriv_within_val_int)
      qed

(* fundamental_theorem_of_calculus_interior necessary as we are working with open intervals *)

    have integral_subj: "\<forall>w\<in>V. integral {a..w} (win_prob i) + surplus i a = surplus i w"
      using win_prob_integral integral_unique val_int by fastforce
    have payment_subj: "\<forall>w\<in>V. (payment i w) = (win_prob i w)*w - surplus i w"
      using surplus_def by simp
  show ?thesis using win_prob_integral payment_subj integral_subj surplus_def by auto
  qed
end
