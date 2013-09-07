theory Chain_Bug_4_fails
imports Main
begin

text {* A trivial set (i.e. singleton or empty), as in Mizar *}
definition trivial where "trivial x = (x \<subseteq> {the_elem x})"

text {* right-uniqueness of a relation (in other words: the relation is a function on its domain) *}
definition runiq :: "('a \<times> 'b) set \<Rightarrow> bool" where
"runiq R = (\<forall> x \<in> Domain R . trivial (R `` {x}))"

text {* the set of all injective functions from @{term X} to @{term Y} *}
definition injections :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set set"
where "injections X Y = {R . Domain R = X \<and> Range R \<subseteq> Y \<and> runiq R \<and> runiq (R\<inverse>)}"

lemma
  fixes Y::"'b set"
  shows "{{}} = injections {} Y"
proof -
  have "{{}} = {R::('a \<times> 'b) set. Domain R = {} \<and> Range R \<subseteq> Y \<and> runiq R \<and> runiq (R\<inverse>)}" (is "?LHS = ?RHS")
  proof
    have "Domain {} = {}" by simp
    moreover have "Range {} \<subseteq> Y" by simp
    moreover have "runiq {}" unfolding runiq_def by fast
    moreover have "runiq ({}\<inverse>)" unfolding runiq_def by fast
    ultimately have "Domain {} = {} \<and> Range {} \<subseteq> Y \<and> runiq {} \<and> runiq ({}\<inverse>)" by blast
    (* CL: Merging the steps before and after this comment considerably increases complexity. *)
    then have "{} \<in> {R . Domain R = {} \<and> Range R \<subseteq> Y \<and> runiq R \<and> runiq (R\<inverse>)}" by (rule CollectI)
    then show "?LHS \<subseteq> ?RHS" by (smt empty_subsetI insert_subset)
  next
    {
      fix R::"('a \<times> 'b) set"
      assume "R \<in> {R . Domain R = {} \<and> Range R \<subseteq> Y \<and> runiq R \<and> runiq (R\<inverse>)}"
      then have "Domain R = {} \<and> Range R \<subseteq> Y \<and> runiq R \<and> runiq (R\<inverse>)" ..
      then have "R = {}" using Domain_empty_iff by metis
      then have "R \<in> {{}}" by simp
    }
    then show "?RHS \<subseteq> ?LHS" by (rule subsetI)
  qed
  also have "{R . Domain R = {} \<and> Range R \<subseteq> Y \<and> runiq R \<and> runiq (R\<inverse>)} = injections {} Y"
    unfolding injections_def ..
  finally show "{{}} = injections {} Y" sorry
qed

end
