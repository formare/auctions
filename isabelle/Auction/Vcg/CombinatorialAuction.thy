(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Marco B. Caminati http://caminati.co.nr
* Manfred Kerber <mnfrd.krbr@gmail.com>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* VCG auction: definitions and theorems *}

theory CombinatorialAuction

imports
UniformTieBreaking

(* The following three theories are needed for the extraction of Scala code *)
"~~/src/HOL/Library/Code_Target_Nat" 
"~~/src/HOL/Library/Code_Target_Int" 
"~~/src/HOL/Library/Code_Numeral"

begin

section {* Definition of a VCG auction scheme, through the pair @{term "(vcga, vcgp)"} *}

(* b is a bid vector and participants is the set of all participants present in b *) 
abbreviation "participants b == Domain (Domain b)"

(* The seller is represented as integer 0, the other particants as integers 1, ..., n *)
abbreviation "seller == (0::integer)"

(* N is the set of participants N = {0, 1, ..., n} and \<Omega> is the set of goods to be auctioned *)
abbreviation "allAllocations N \<Omega> == possibleAllocationsRel N \<Omega>"

(* allAllocations' and allAllocations'' are variants of allAllocations. All three formulations are equivent. *)
abbreviation "allAllocations' N \<Omega> == 
  injectionsUniverse \<inter> {a. Domain a \<subseteq> N & Range a \<in> all_partitions \<Omega>}" 

abbreviation "allAllocations'' N \<Omega> == allocationsUniverse \<inter> {a. Domain a \<subseteq> N & \<Union> Range a = \<Omega>}"

lemma allAllocationsEquivalence: 
  "allAllocations N \<Omega>=allAllocations' N \<Omega> & allAllocations N \<Omega>=allAllocations'' N \<Omega>" 
  using allocationInjectionsUnivervseProperty possibleAllocationsIntersection by metis

lemma allAllocationsVarCharacterization: 
  "(a \<in> allAllocations'' N \<Omega>) = (a \<in> allocationsUniverse& Domain a \<subseteq> N & \<Union> Range a = \<Omega>)" 
  by force

(* remove the seller from the set of all allocations *)
abbreviation "soldAllocations N \<Omega> == (Outside' {seller}) ` (allAllocations (N \<union> {seller}) \<Omega>)"

(* soldAllocations' and soldAllocations'' are variants of soldAllocations reflecting the different
   formulations of allAllocations. soldAllocations''' is yet another variant. These variants are
   used since for different proofs different variants are easier to use. *)
abbreviation "soldAllocations' N \<Omega> == (Outside' {seller}) ` (allAllocations' (N \<union> {seller}) \<Omega>)"
abbreviation "soldAllocations'' N \<Omega> == (Outside' {seller}) ` (allAllocations'' (N \<union> {seller}) \<Omega>)"
abbreviation "soldAllocations''' N \<Omega> == 
  allocationsUniverse \<inter> {aa. Domain aa\<subseteq>N-{seller} & \<Union>Range aa\<subseteq>\<Omega>}"
lemma soldAllocationsEquivalence: 
  "soldAllocations N \<Omega> = soldAllocations' N \<Omega> & 
   soldAllocations' N \<Omega> = soldAllocations'' N \<Omega>"
  using assms allAllocationsEquivalence by metis

corollary soldAllocationsEquivalenceVariant: 
  "soldAllocations = soldAllocations'  & 
   soldAllocations' = soldAllocations'' & 
   soldAllocations = soldAllocations''" 
  using soldAllocationsEquivalence by metis

lemma allocationSellerMonotonicity: 
  "soldAllocations (N-{seller}) \<Omega> \<subseteq> soldAllocations N \<Omega>" 
  using Outside_def by simp

lemma allocationsUniverseCharacterization: 
  "(a \<in> allocationsUniverse) = (a \<in> allAllocations'' (Domain a) (\<Union> Range a))"
  by blast

lemma allocationMonotonicity: 
  assumes "N1 \<subseteq> N2" 
  shows "allAllocations'' N1 \<Omega> \<subseteq> allAllocations'' N2 \<Omega>" 
  using assms by auto

lemma allocationWithOneParticipant: 
  assumes "a \<in> allAllocations'' N \<Omega>" 
  shows "Domain (a -- x) \<subseteq> N-{x}" 
  using assms Outside_def by fastforce

lemma soldAllocationIsAllocation: 
  assumes "a \<in> soldAllocations N \<Omega>" 
  shows "a \<in> allocationsUniverse"
proof -
obtain aa where "a  =aa -- seller & aa \<in> allAllocations (N\<union>{seller}) \<Omega>"
  using assms by blast
then have "a \<subseteq> aa & aa \<in> allocationsUniverse" 
  unfolding Outside_def using possibleAllocationsIntersectionSubset by blast
then show ?thesis using subsetAllocation by blast
qed

lemma soldAllocationIsAllocationVariant: 
  assumes "a \<in> soldAllocations N \<Omega>" 
  shows "a \<in> allAllocations'' (Domain a) (\<Union>Range a)"
proof - 
  show ?thesis using assms soldAllocationIsAllocation by blast 
qed

lemma onlyGoodsAreSold: 
  assumes "a \<in> soldAllocations'' N \<Omega>" 
  shows "\<Union> Range a \<subseteq> \<Omega>" 
  using assms Outside_def by blast

lemma soldAllocationIsRestricted: 
  "a \<in> soldAllocations'' N \<Omega> = 
   (EX aa. aa -- (seller) = a  &  aa \<in> allAllocations'' (N \<union> {seller}) \<Omega>)" 
  by blast

(* Note that +* enlarges the function by one additional pair *)
lemma restrictionConservation:
  "(R +* ({x}\<times>Y)) -- x = R -- x" 
  unfolding Outside_def paste_def by blast

lemma allocatedToBuyerMeansSold: 
  assumes "a \<in> allocationsUniverse" "Domain a \<subseteq> N-{seller}" "\<Union> Range a \<subseteq> \<Omega>" 
  shows "a \<in> soldAllocations'' N \<Omega>"
proof -
  let ?i = "seller" 
  let ?Y = "{\<Omega>-\<Union> Range a}-{{}}" 
  let ?b = "{?i}\<times>?Y" 
  let ?aa = "a\<union>?b"
  let ?aa' = "a +* ?b" 
  have
  1: "a \<in> allocationsUniverse" using assms(1) by fast 
  have "?b \<subseteq> {(?i,\<Omega>-\<Union> Range a)} - {(?i, {})}" by fastforce 
  then have 
  2: "?b \<in> allocationsUniverse" 
    using allocationUniverseProperty subsetAllocation by (metis(no_types))
  have 
  3: "\<Union> Range a \<inter> \<Union> (Range ?b) = {}" by blast 
  have 
  4: "Domain a \<inter> Domain ?b ={}" using assms by fast
  have "?aa \<in> allocationsUniverse" using 1 2 3 4 by (rule allocationUnion)
  then have "?aa \<in> allAllocations'' (Domain ?aa) (\<Union> Range ?aa)" 
    unfolding allocationsUniverseCharacterization by metis 
  then have "?aa \<in> allAllocations'' (N\<union>{?i}) (\<Union> Range ?aa)" 
    using allocationMonotonicity assms paste_def by auto
  moreover have "Range ?aa = Range a \<union> ?Y" by blast 
  then moreover have "\<Union> Range ?aa = \<Omega>" 
    using Un_Diff_cancel Un_Diff_cancel2 Union_Un_distrib Union_empty Union_insert  
    by (metis (lifting, no_types) assms(3) cSup_singleton subset_Un_eq) 
  moreover have "?aa' = ?aa" using 4 by (rule paste_disj_domains)
  ultimately have "?aa' \<in> allAllocations'' (N\<union>{?i}) \<Omega>" by simp
  moreover have "Domain ?b \<subseteq> {?i}" by fast 
  have "?aa' -- ?i = a -- ?i" by (rule restrictionConservation)
  moreover have "... = a" using Outside_def assms(2) by auto 
  ultimately show ?thesis using soldAllocationIsRestricted by auto
qed

lemma allocationCharacterization: 
  "a \<in> allAllocations N \<Omega>  =  
   (a \<in> injectionsUniverse & Domain a \<subseteq> N & Range a \<in> all_partitions \<Omega>)" 
  by (metis (full_types) posssibleAllocationsRelCharacterization)

(* The lemmas lm01, lm02, lm03, and lm04 are used in order to prove
   lemma soldAllocationVariantEquivalence   *)
lemma lm01: 
  assumes "a \<in> soldAllocations'' N \<Omega>" 
  shows "Domain a \<subseteq> N-{seller} & a \<in> allocationsUniverse"  
proof -
  let ?i = "seller" 
  obtain aa where
  0: "a = aa -- ?i & aa \<in> allAllocations'' (N \<union> {?i}) \<Omega>" 
    using assms(1) soldAllocationIsRestricted by blast
  then have "Domain aa \<subseteq> N \<union> {?i}" using allocationCharacterization by blast
  then have "Domain a \<subseteq> N - {?i}" using 0 Outside_def by blast
  moreover have "a \<in> soldAllocations N \<Omega>" using assms soldAllocationsEquivalenceVariant by metis
  then moreover have "a \<in> allocationsUniverse" using soldAllocationIsAllocation by blast
  ultimately show ?thesis by blast
qed

corollary lm02: 
  assumes "a \<in> soldAllocations'' N \<Omega>" 
  shows "a \<in> allocationsUniverse & Domain a \<subseteq> N-{seller} & \<Union> Range a \<subseteq> \<Omega>"
proof -
  have "a \<in> allocationsUniverse" using assms lm01 by blast
  moreover have "Domain a \<subseteq> N-{seller}" using assms lm01 by blast
  moreover have "\<Union> Range a \<subseteq> \<Omega>" using assms onlyGoodsAreSold by blast
  ultimately show ?thesis by blast
qed

corollary lm03:
  "(a \<in> soldAllocations'' N \<Omega>) =
   (a \<in> allocationsUniverse & a \<in> {aa. Domain aa \<subseteq> N-{seller} & \<Union> Range aa \<subseteq> \<Omega>})" 
  (is "?L = ?R") 
proof -
  have "(a\<in>soldAllocations'' N \<Omega>) =
        (a\<in>allocationsUniverse& Domain a \<subseteq> N-{seller} & \<Union> Range a \<subseteq> \<Omega>)" 
  using lm02 allocatedToBuyerMeansSold by (metis (mono_tags))
  then have "?L = (a\<in>allocationsUniverse& Domain a \<subseteq> N-{seller} & \<Union> Range a \<subseteq> \<Omega>)" by fast
  moreover have "... = ?R" using mem_Collect_eq by (metis (lifting, no_types))
  ultimately show ?thesis by auto
qed

corollary lm04: 
  "a \<in> soldAllocations'' N \<Omega> =
   (a\<in> (allocationsUniverse \<inter> {aa. Domain aa \<subseteq> N-{seller} & \<Union> Range aa \<subseteq> \<Omega>}))" 
  using lm03 by (metis (mono_tags) Int_iff)

corollary soldAllocationVariantEquivalence: 
  "soldAllocations'' N \<Omega> = soldAllocations''' N \<Omega>" 
  (is "?L=?R") 
proof - 
  {
   fix a 
   have "a \<in> ?L = (a \<in> ?R)" by (rule lm04)
  } 
  thus ?thesis by blast 
qed

(* We use lm05 in order to show a variant for soldAllocations without ''' *)
lemma lm05: 
  assumes "a \<in> soldAllocations''' N \<Omega>" 
  shows "a -- n \<in> soldAllocations''' (N-{n}) \<Omega>"
proof -
  let ?bb = seller 
  let ?d = Domain 
  let ?r = Range 
  let ?X1 = "{aa. ?d aa \<subseteq> N-{n}-{?bb} & \<Union>?r aa\<subseteq>\<Omega>}" 
  let ?X2 = "{aa. ?d aa \<subseteq> N-{?bb} & \<Union>?r aa \<subseteq> \<Omega>}" 
  have "a\<in>?X2" using assms(1) by fast  
  then have 
  0: "?d a \<subseteq> N-{?bb} & \<Union>?r a \<subseteq> \<Omega>" by blast 
  then have "?d (a--n) \<subseteq> N-{?bb}-{n}" 
    using outside_reduces_domain by (metis Diff_mono subset_refl) 
  moreover have "... = N-{n}-{?bb}" by fastforce 
  ultimately have "?d (a--n) \<subseteq> N-{n}-{?bb}" by blast 
  moreover have "\<Union> ?r (a--n) \<subseteq> \<Omega>" 
    unfolding Outside_def using 0 by blast 
  ultimately have "a -- n \<in> ?X1" by fast 
  moreover have "a--n \<in> allocationsUniverse" 
    using assms(1) Int_iff allocationsUniverseOutside by (metis(lifting,mono_tags)) 
  ultimately show ?thesis by blast
qed

lemma allAllocationsEquivalenceExtended: 
  "soldAllocations =  soldAllocations' & 
   soldAllocations' = soldAllocations'' &
   soldAllocations'' = soldAllocations'''" 
  using soldAllocationVariantEquivalence soldAllocationsEquivalenceVariant by metis

(* The following corollary shows that an allocation is invariant to subtracting a single bidder.   
   This is used a fundamental step to prove the non-negativity of price in VCG. *)
corollary soldAllocationRestriction: 
  assumes "a \<in> soldAllocations N \<Omega>" 
  shows "a -- n \<in> soldAllocations (N-{n}) \<Omega>"
proof - 
  let ?A' = soldAllocations''' 
  have "a \<in> ?A' N \<Omega>" using assms allAllocationsEquivalenceExtended by metis 
  then have "a -- n \<in> ?A' (N-{n}) \<Omega>" by (rule lm05) 
  thus ?thesis using allAllocationsEquivalenceExtended by metis 
qed

corollary allocationGoodsMonotonicity: 
  assumes "\<Omega>1 \<subseteq> \<Omega>2" 
  shows "soldAllocations''' N \<Omega>1 \<subseteq> soldAllocations''' N \<Omega>2"
  using assms by blast

corollary allocationGoodsMonotonicityVariant: 
  assumes "\<Omega>1 \<subseteq> \<Omega>2" 
  shows "soldAllocations'' N \<Omega>1 \<subseteq> soldAllocations'' N \<Omega>2" 
proof -
  have "soldAllocations'' N \<Omega>1 = soldAllocations''' N \<Omega>1" 
    by (rule soldAllocationVariantEquivalence)
  moreover have "... \<subseteq> soldAllocations''' N \<Omega>2" 
    using assms(1) by (rule allocationGoodsMonotonicity)
  moreover have "... = soldAllocations'' N \<Omega>2" using soldAllocationVariantEquivalence by metis
  ultimately show ?thesis by auto
qed

(* maximalStrictAllocationsAlg are the allocations maximizing the revenue. They also include the
   unallocated goods assigned to the seller (bidder 0).*)
abbreviation "maximalStrictAllocations N \<Omega> b == argmax (setsum b) (allAllocations ({seller}\<union>N) \<Omega>)"

(* randomBids builds up a bid vector from a random number so that bidding with this bid vector
   resolves any ties. Details are defined in UniformTieBreaking.thy *)
abbreviation "randomBids N \<Omega> b random == resolvingBid (N\<union>{seller}) \<Omega> b random"

(* vcgas gives the one-element set with the winning allocation after tie breaking.
   (argmax\<circ>setsum) b ... determines the set of all maximal allocations.
   (argmax\<circ>setsum) (randomBids ...) restricts that by tie-breaking to a singleton.
   Outside' {seller} removes the seller from the only allocation in the singleton.   *)
abbreviation "vcgas N \<Omega> b r  == 
  Outside' {seller} `((argmax\<circ>setsum) (randomBids N \<Omega> b r)
                                      ((argmax\<circ>setsum) b (allAllocations (N \<union> {seller}) (set \<Omega>))))"

(* Takes the element out of the one elemnt set (vcgas ...) *)
abbreviation "vcga N \<Omega> b r == the_elem (vcgas N \<Omega> b r)"

(* alternative definition of vcga *)
abbreviation "vcga' N \<Omega> b r == 
  (the_elem (argmax (setsum (randomBids N \<Omega> b r)) 
                    (maximalStrictAllocations N (set \<Omega>) b)))
  -- seller"

(* The following three auxiliary lemmas, lm06, lm07, and lm08 are used to prove lemma
   vcgaEquivalence as well as in the theorem that cardinality of vcgas is one.*)
lemma lm06: 
  assumes "card ((argmax\<circ>setsum) (randomBids N \<Omega> b r) 
                                 ((argmax\<circ>setsum) b (allAllocations (N\<union>{seller}) (set \<Omega>)))) = 1" 
  shows "vcga N \<Omega> b r = 
         (the_elem ((argmax\<circ>setsum) (randomBids N \<Omega> b r) 
                                    ((argmax\<circ>setsum) b (allAllocations ({seller}\<union>N) (set \<Omega>))))) 
          -- seller"
  using assms cardOneTheElem by auto

corollary lm07: 
  assumes "card ((argmax\<circ>setsum) (randomBids N \<Omega> b r) 
                                 ((argmax\<circ>setsum) b (allAllocations (N\<union>{seller}) (set \<Omega>)))) = 1"
  shows "vcga N \<Omega> b r = vcga' N \<Omega> b r" 
  (is "?l = ?r")
proof -
  have "?l = (the_elem ((argmax\<circ>setsum) (randomBids N \<Omega> b r) 
                                        ((argmax\<circ>setsum) b (allAllocations ({seller}\<union>N) (set \<Omega>)))))
              -- seller"
    using assms by (rule lm06) 
  moreover have "... = ?r" by force 
  ultimately show ?thesis by blast
qed

lemma lm08: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "card ((argmax\<circ>setsum) (randomBids N \<Omega> bids random)
                               ((argmax\<circ>setsum) bids (allAllocations (N\<union>{seller}) (set \<Omega>)))) = 1"
  (is "card ?l=_")
proof - 
  let ?N = "N\<union>{seller}" 
  let ?b' = "randomBids N \<Omega> bids random" 
  let ?s = setsum 
  let ?a = argmax 
  let ?f = "?a \<circ> ?s"
  have 
  1: "?N\<noteq>{}" by auto 
  have 
  2: "finite ?N" using assms(3) by simp
  have "?a (?s ?b') (?a (?s bids) (allAllocations ?N (set \<Omega>))) =
        {chosenAllocation' ?N \<Omega> bids random}" (is "?L=?R")
  using 1 assms(1) assms(2) 2 by (rule winningAllocationUniqueness)
  moreover have "?L= ?f ?b' (?f bids (allAllocations ?N (set \<Omega>)))" by auto
  ultimately have "?l = {chosenAllocation' ?N \<Omega> bids random}" by simp
  moreover have "card ...=1" by simp ultimately show ?thesis by simp 
qed

lemma vcgaEquivalence: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "vcga N \<Omega> b r = vcga' N \<Omega> b r"
  using assms lm07 lm08 by blast

(* After showing that the cardinality of vcgas is 1, we know that the_elem to determine vcga
   will return a definite value. *)
theorem vcgaDefiniteness: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "card (vcgas N \<Omega> b r) = 1"
proof -
  have "card ((argmax\<circ>setsum) (randomBids N \<Omega> b r) 
                              ((argmax\<circ>setsum) b (allAllocations (N\<union>{seller}) (set \<Omega>)))) =
        1" 
  (is "card ?X = _") using assms lm08 by blast
  moreover have "(Outside'{seller}) ` ?X = vcgas N \<Omega> b r" by blast
  ultimately show ?thesis using cardOneImageCardOne by blast
qed

(* Since vcga is well-defined the following theorem is trivial. *)
theorem vcgpDefiniteness: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "\<exists>! y. vcgap N \<Omega> b r n = y" 
  using assms vcgaDefiniteness by simp

(* The following lemma is a variant of the vcgaDefiniteness theorem. *)
lemma vcgaDefinitenessVariant: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows  "card (argmax (setsum (randomBids N \<Omega> b r)) 
                       (maximalStrictAllocations N (set \<Omega>) b)) =
          1"
  (is "card ?L=_")
proof -
  let ?n = "{seller}" 
  have 
  1: "(?n \<union> N)\<noteq>{}" by simp 
  have 
  2: "finite (?n\<union>N)" using assms(3) by fast 
  have "terminatingAuctionRel (?n\<union>N) \<Omega> b r = {chosenAllocation' (?n\<union>N) \<Omega> b r}" 
    using 1 assms(1) assms(2) 2 by (rule winningAllocationUniqueness) 
  moreover have "?L = terminatingAuctionRel (?n\<union>N) \<Omega> b r" by auto
  ultimately show ?thesis by auto
qed

theorem winningAllocationIsMaximal:
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "the_elem (argmax (setsum (randomBids N \<Omega> b r)) 
                          (maximalStrictAllocations N (set \<Omega>) b)) \<in>
         (maximalStrictAllocations N (set \<Omega>) b)" 
  (is "the_elem ?X \<in> ?R") 
proof -
  have "card ?X=1" using assms by (rule vcgaDefinitenessVariant) 
  moreover have "?X \<subseteq> ?R" by auto
  ultimately show ?thesis using cardinalityOneTheElem by blast
qed

corollary winningAllocationIsMaximalWithoutSeller: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "vcga' N \<Omega> b r \<in> (Outside' {seller})`(maximalStrictAllocations N (set \<Omega>) b)"
  using assms winningAllocationIsMaximal by blast

lemma maximalAllactionWithoutSeller: 
  "(Outside' {seller})`(maximalStrictAllocations N \<Omega> b) \<subseteq> soldAllocations N \<Omega>"
  using Outside_def by force

lemma onlyGoodsAreAllocatedAuxiliary: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "vcga' N \<Omega> b r \<in> soldAllocations N (set \<Omega>)" 
  (is "?a \<in> ?A") 
proof - 
  have "?a \<in> (Outside' {seller})`(maximalStrictAllocations N (set \<Omega>) b)" 
    using assms by (rule winningAllocationIsMaximalWithoutSeller) 
  thus ?thesis using maximalAllactionWithoutSeller  by fastforce 
qed

theorem onlyGoodsAreAllocated: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "vcga N \<Omega> b r \<in> soldAllocations N (set \<Omega>)" 
  (is "_\<in>?r") 
proof - 
  have "vcga' N \<Omega> b r \<in> ?r" using assms by (rule onlyGoodsAreAllocatedAuxiliary) 
  then show ?thesis using assms vcgaEquivalence by blast 
qed

(* Let b be a bid vector such that the seller's bid for each possible set of goods is 0 then 
   the revenue does not depend on the presence of the seller. *)
corollary neutralSeller: 
  assumes "\<forall>X. X \<in> Range a \<longrightarrow>b (seller, X)=0" "finite a" 
  shows "setsum b a = setsum b (a--seller)"
proof -
  let ?n = seller 
  have "finite (a||{?n})" using assms restrict_def by (metis finite_Int) 
  moreover have "\<forall>z \<in> a||{?n}. b z=0" using assms restrict_def by fastforce
  ultimately have "setsum b (a||{?n}) = 0" using assms by (metis setsum.neutral)
  thus ?thesis using setsumOutside assms(2) by (metis comm_monoid_add_class.add.right_neutral)
qed

corollary neutralSellerVariant: 
  assumes "\<forall>a\<in>A. finite a & (\<forall> X. X\<in>Range a \<longrightarrow> b (seller, X)=0)"
  shows "{setsum b a| a. a\<in>A} = {setsum b (a -- seller)| a. a\<in>A}" 
  using assms neutralSeller by (metis (lifting, no_types))

lemma vcgaIsMaximalAux1: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "EX a. ((a \<in> (maximalStrictAllocations N (set \<Omega>) b))  &  (vcga' N \<Omega> b r = a -- seller)  &
                (a \<in> argmax (setsum b) (allAllocations ({seller}\<union>N) (set \<Omega>))))" 
  using assms winningAllocationIsMaximalWithoutSeller argmax_def by fast

lemma vcgaIsMaximalAux2: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  "\<forall>a \<in> allAllocations ({seller}\<union>N) (set \<Omega>). \<forall> X \<in> Range a. b (seller, X)=0"
  (is "\<forall>a\<in>?X. _") 
  shows "setsum b (vcga' N \<Omega> b r) = Max{setsum b a| a. a \<in> soldAllocations N (set \<Omega>)}"
proof -
  let ?n = seller 
  let ?s = setsum 
  let ?a = "vcga' N \<Omega> b r" 
  obtain a where 
  0: "a \<in> maximalStrictAllocations N (set \<Omega>) b & 
      ?a = a--?n & 
      (a \<in> argmax (setsum b) (allAllocations({seller}\<union>N)(set \<Omega>)))"
  (is "_ & ?a=_ & a\<in>?Z")
    using assms(1,2,3) vcgaIsMaximalAux1 by blast
  have 
  1: "\<forall>a \<in> ?X. finite a & (\<forall> X. X\<in>Range a \<longrightarrow> b (?n, X)=0)" 
    using assms(4) List.finite_set allocationFinite by metis 
  have 
  2: "a \<in> ?X" using 0 by auto have "a \<in> ?Z" using 0 by fast 
  then have "a \<in> ?X\<inter>{x. ?s b x = Max (?s b ` ?X)}" using injectionsUnionCommute by simp
  then have "a \<in> {x. ?s b x = Max (?s b ` ?X)}" using injectionsUnionCommute by simp
  moreover have "?s b ` ?X = {?s b a| a. a\<in>?X}" by blast
  ultimately have "?s b a = Max {?s b a| a. a\<in>?X}" by auto
  moreover have "{?s b a| a. a\<in>?X} = {?s b (a--?n)| a. a\<in>?X}" 
    using 1 by (rule neutralSellerVariant)
  moreover have "... = {?s b a| a. a \<in> Outside' {?n}`?X}" by blast
  moreover have "... = {?s b a| a. a \<in> soldAllocations N (set \<Omega>)}" by simp
  ultimately have "Max {?s b a| a. a \<in> soldAllocations N (set \<Omega>)} = ?s b a" by simp
  moreover have "... = ?s b (a--?n)" using 1 2 neutralSeller by (metis (lifting, no_types))
  ultimately show "?s b ?a=Max{?s b a| a. a \<in> soldAllocations N (set \<Omega>)}" using 0 by simp
qed

text {* Adequacy theorem: The allocation satisfies the standard pen-and-paper specification 
of a VCG auction. See, for example, \cite[\S~1.2]{cramton}. *}
theorem vcgaIsMaximal: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" "\<forall> X. b (seller, X) = 0" 
  shows "setsum b (vcga' N \<Omega> b r) = Max{setsum b a| a. a \<in> soldAllocations N (set \<Omega>)}"
  using assms vcgaIsMaximalAux2 by blast

corollary vcgaIsAllocationAllocatingGoodsOnly: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "vcga' N \<Omega> b r \<in> allocationsUniverse & \<Union> Range (vcga' N \<Omega> b r) \<subseteq> set \<Omega>" 
proof -
  let ?a = "vcga' N \<Omega> b r" 
  let ?n = seller
  obtain a where 
  0: "?a = a -- seller & a \<in> maximalStrictAllocations N (set \<Omega>) b"
    using assms winningAllocationIsMaximalWithoutSeller by blast
  then moreover have 
  1: "a \<in> allAllocations ({?n}\<union>N) (set \<Omega>)" by auto
  moreover have "maximalStrictAllocations N (set \<Omega>) b \<subseteq> allocationsUniverse" 
     by (metis (lifting, mono_tags) winningAllocationPossible 
                                    possibleAllocationsUniverse subset_trans)
  ultimately moreover have "?a = a -- seller  &  a \<in> allocationsUniverse" by blast
  then have "?a \<in> allocationsUniverse" using allocationsUniverseOutside by auto
  moreover have "\<Union> Range a= set \<Omega>" using possibleAllocationsIntersectionSetEquals 1 by metis
  then moreover have "\<Union> Range ?a \<subseteq> set \<Omega>" using Outside_def 0 by fast
  ultimately show ?thesis using allocationsUniverseOutside Outside_def by blast
qed

(***)
lemma "vcga' N \<Omega> b r = the_elem ((argmax \<circ> setsum) (randomBids N \<Omega> b r) 
((argmax \<circ> setsum) b (allAllocations ({seller}\<union>N) (set \<Omega>)))) -- seller" by simp

abbreviation "vcgp N \<Omega> b r n ==
Max (setsum b ` (soldAllocations (N-{n}) (set \<Omega>))) - (setsum b (vcga N \<Omega> b r -- n))"

lemma lm63: assumes "x \<in> X" "finite X" shows "Max (f`X) >= f x" (is "?L >= ?R") using assms 
by (metis (hide_lams, no_types) Max.coboundedI finite_imageI image_eqI)

lemma lm59: assumes "finite N" "finite \<Omega>" shows "finite (soldAllocations N \<Omega>)" using assms possibleAllocationsRelFinite
finite.emptyI finite.insertI finite_UnI finite_imageI by metis

text{* The price paid by any participant is non-negative. *}
theorem NonnegPrices: assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" shows 
"vcgp N \<Omega> b r n >= (0::price)" 
proof - 
let ?a="vcga N \<Omega> b r" let ?A=soldAllocations let ?f="setsum b" 
have "?a \<in> ?A N (set \<Omega>)" using assms by (rule onlyGoodsAreAllocated)
then have "?a -- n \<in> ?A (N-{n}) (set \<Omega>)" by (rule soldAllocationRestriction)
moreover have "finite (?A (N-{n}) (set \<Omega>))" using assms(3) lm59 finite_set finite_Diff by blast
ultimately have "Max (?f`(?A (N-{n}) (set \<Omega>))) \<ge> ?f (?a -- n)" (is "?L >= ?R") by (rule lm63)
then show "?L - ?R >=0" by linarith
qed

lemma lm19b: "allAllocations N \<Omega> = possibleAllocationsRel N \<Omega>" using assms by (metis allocationInjectionsUnivervseProperty)
abbreviation "strictAllocationsUniverse == allocationsUniverse"

abbreviation "Goods bids == \<Union>((snd\<circ>fst)`bids)"

corollary lm45: assumes "a \<in> soldAllocations''' N \<Omega>" shows "Range a \<in> partitionsUniverse" 
using assms by (metis (lifting, mono_tags) Int_iff nonOverlapping mem_Collect_eq)

corollary lm45a: assumes "a \<in> soldAllocations N \<Omega>" shows "Range a \<in> partitionsUniverse"
proof - have "a \<in> soldAllocations''' N \<Omega>" using assms allAllocationsEquivalenceExtended by metis thus ?thesis by (rule lm45) qed

corollary assumes 
"N \<noteq> {}" "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" (*MC: why does this emerge only now? *) 
shows "(Outside' {seller}) ` (terminatingAuctionRel N \<Omega> (bids) random) = 
{chosenAllocation' N \<Omega> bids random -- (seller)}" (is "?L=?R")
proof -
have "?R = Outside' {seller} ` {chosenAllocation' N \<Omega> bids random}" using Outside_def 
by blast 
moreover have "... = (Outside'{seller})`(terminatingAuctionRel N \<Omega> bids random)" using assms winningAllocationUniqueness 
by blast
ultimately show ?thesis by presburger
qed

(* abbreviation "argMax X f == argmax f X" *)
lemma "terminatingAuctionRel N \<Omega> b r = 
((argmax (setsum (resolvingBid N \<Omega> b (r)))) \<circ> (argmax (setsum b)))
(possibleAllocationsRel N (set \<Omega>))" by force
term "(Union \<circ> (argmax (setsum (resolvingBid N \<Omega> b (r)))) \<circ> (argmax (setsum b)))
(possibleAllocationsRel N (set \<Omega>))"

lemma "maximalStrictAllocations N \<Omega> b=winningAllocationsRel ({seller} \<union> N) \<Omega> b" by fast

lemma lm64: assumes "a \<in> allocationsUniverse" 
"n1 \<in> Domain a" "n2 \<in> Domain a"
"n1 \<noteq> n2" 
shows "a,,n1 \<inter> a,,n2={}" using assms is_non_overlapping_def nonOverlapping mem_Collect_eq 
proof - have "Range a \<in> partitionsUniverse" using assms nonOverlapping by blast
moreover have "a \<in> injectionsUniverse & a \<in> partitionValuedUniverse" using assms by (metis (lifting, no_types) IntD1 IntD2)
ultimately moreover have "a,,n1 \<in> Range a" using assms 
by (metis (mono_tags) eval_runiq_in_Range mem_Collect_eq)
ultimately moreover have "a,,n1 \<noteq> a,,n2" using 
assms converse.intros eval_runiq_rel mem_Collect_eq runiq_basic by (metis (lifting, no_types))
ultimately show ?thesis using is_non_overlapping_def by (metis (lifting, no_types) assms(3) eval_runiq_in_Range mem_Collect_eq)
qed

lemma lm64c: assumes "a \<in> allocationsUniverse" 
"n1 \<in> Domain a" "n2 \<in> Domain a"
"n1 \<noteq> n2" 
shows "a,,,n1 \<inter> a,,,n2={}" using assms lm64 imageEquivalence by fastforce 

text{* No good is assigned twice. *}
theorem PairwiseDisjointAllocations:
fixes n1::"participant" fixes \<Omega>::"goods list" fixes N::"participant set"
assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N"  
(* "n1 \<in> Domain (vcga' N \<Omega> b r)" "n2 \<in> Domain (vcga' N \<Omega> b r)" *) 
"n1 \<noteq> n2" 
shows "(vcga' N \<Omega> b r),,,n1 \<inter> (vcga' N \<Omega> b r),,,n2={}"  
proof -
have "vcga' N \<Omega> b r \<in> allocationsUniverse" using vcgaIsAllocationAllocatingGoodsOnly assms by blast
then show ?thesis using lm64c assms by fast
qed

lemma assumes "R,,,x \<noteq> {}" shows "x \<in> Domain R" using assms  
proof - have "\<Union> (R``{x}) \<noteq> {}" using assms(1) by fast
then have "R``{x} \<noteq> {}" by fast thus ?thesis by blast qed

lemma assumes "runiq f" and "x \<in> Domain f" shows "(f ,, x) \<in> Range f" using assms 
by (rule eval_runiq_in_Range)

text {* Nothing outside the set of goods is allocated. *}
theorem OnlyGoodsAllocated: assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" "g \<in> (vcga N \<Omega> b r),,,n" 
shows "g \<in> set \<Omega>"
proof - 
let ?a="vcga' N \<Omega> b r" have "?a \<in> allocationsUniverse" using assms(1,2,3) vcgaIsAllocationAllocatingGoodsOnly by blast
then have "runiq ?a" using assms(1,2,3) by blast
moreover have "n \<in> Domain ?a" using assms eval_rel_def vcgaEquivalence by fast
ultimately moreover have "?a,,n \<in> Range ?a" using eval_runiq_in_Range by fast 
ultimately have "?a,,,n \<in> Range ?a" using imageEquivalence by fastforce
then have "g \<in> \<Union> Range ?a" using assms vcgaEquivalence by blast 
moreover have "\<Union> Range ?a \<subseteq> set \<Omega>" using assms(1,2,3) vcgaIsAllocationAllocatingGoodsOnly by fast
ultimately show ?thesis by blast
qed

definition "allStrictAllocations N \<Omega> == possibleAllocationsAlg N \<Omega>"
abbreviation "maximalStrictAllocationsAlg N \<Omega> b==
argmax (setsum b) (set (allStrictAllocations ({seller}\<union>N) \<Omega>))"

definition "maximalStrictAllocations2 N \<Omega> b=
argmax (setsum b) (set (allStrictAllocations ({seller}\<union>N) \<Omega>))"

definition "chosenAllocation N \<Omega> b (r::integer) == 
hd(perm2 (takeAll (%x. x\<in> (argmax \<circ> setsum) b (set (allStrictAllocations N \<Omega>))) (allStrictAllocations N \<Omega>)) (nat_of_integer r))"

definition "chosenAllocationEff N \<Omega> b (r::integer) == 
(takeAll (%x. x\<in> (argmax \<circ> setsum) b (set (allStrictAllocations N \<Omega>))) (allStrictAllocations N \<Omega>) ! (nat_of_integer r))"


definition "maxbid a N \<Omega> == (bidMaximizedBy a N \<Omega>) Elsee 0"
definition "summedBidVector bids N \<Omega> == (summedBidVectorRel bids N \<Omega>) Elsee 0"
definition "tiebids a N \<Omega> == summedBidVector (maxbid a N \<Omega>) N \<Omega>"
definition "resolvingBidAlg N \<Omega> bids random == tiebids (chosenAllocation N \<Omega> bids random) N (set \<Omega>)"
definition "randomBidsAlg N \<Omega> b random==resolvingBidAlg (N\<union>{seller}) \<Omega> b random"
definition "vcgaAlgWithoutLosers N \<Omega> b r == (the_elem
(argmax (setsum (randomBidsAlg N \<Omega> b r)) (maximalStrictAllocationsAlg N \<Omega> b))) -- seller"
abbreviation "addLosers participantset allo==(participantset \<times> {{}}) +* allo"
definition "vcgaAlg N \<Omega> b r = addLosers N (vcgaAlgWithoutLosers N \<Omega> b r)"
abbreviation "allAllocationsComp N \<Omega> == 
(Outside' {seller}) ` set (allStrictAllocations (N \<union> {seller}) \<Omega>)"
definition "vcgpAlg N \<Omega> b r n =
Max (setsum b ` (allAllocationsComp (N-{n}) \<Omega>)) - (setsum b (vcgaAlgWithoutLosers N \<Omega> b r -- n))"

lemma lm01a: assumes "x \<in> Domain f" shows "toFunction f x = (f Elsee 0) x"
unfolding toFunctionWithFallbackAlg_def
by (metis assms toFunction_def)
lemma lm03a: "Domain (Y \<times> {0::nat}) = Y & Domain (X \<times> {1})=X" by blast
lemma lm04a: "Domain (X <|| Y) = X \<union> Y" using lm03a paste_Domain sup_commute by metis
corollary lm04b: "Domain (bidMaximizedBy a N \<Omega>) = pseudoAllocation a \<union> N \<times> (finestpart \<Omega>)" using lm04a
by metis
lemma lm19: "(pseudoAllocation a) \<subseteq> Domain (bidMaximizedBy a N \<Omega>)" by (metis lm04a Un_upper1)

lemma lm02a: assumes "x \<in> (N \<times> (Pow \<Omega> - {{}}))" shows 
"summedBidVector' b N \<Omega> x=summedBidVector b N \<Omega> x" unfolding summedBidVector_def 
using assms lm01a Domain.simps imageI by (metis(no_types,lifting))
(*lm64*)

(*
lemma assumes "a \<in> possibleAllocationsRel N \<Omega>" shows "pseudoAllocation a \<subseteq> Domain (bidMaximizedBy a N \<Omega>)" 
using assms sorry

corollary lm01b: "\<forall>x. x \<in>(pseudoAllocation aa) \<longrightarrow> ((bidMaximizedBy a N \<Omega>) Elsee 0) x =
(toFunction (bidMaximizedBy a N \<Omega>)) x" using assms lm01 lm19 sorry

corollary assumes 
"pseudoAllocation aa \<subseteq> pseudoAllocation a \<union> (N \<times> (finestpart \<Omega>))" "finite (pseudoAllocation aa)"
shows "setsum ((bidMaximizedBy a N \<Omega>) Elsee 0) (pseudoAllocation a) - 
(setsum ((bidMaximizedBy a N \<Omega>) Elsee 0) (pseudoAllocation aa)) = 
card (pseudoAllocation a) - card (pseudoAllocation aa \<inter> (pseudoAllocation a))" 
(is "?l1 - ?l2 = ?r") using allAllocationsEquivalence assms lm49 lm04 lm05 Un_upper1 UnCI UnI1 
proof -
(* sledgehammer [isar_proofs=true,"try0"=true,smt_proofs=false,provers=z3] *)
have "pseudoAllocation aa \<subseteq> Domain (bidMaximizedBy a N \<Omega>)" using lm04b assms(1) 
by metis
then have "\<forall> x \<in> pseudoAllocation aa. toFunction (bidMaximizedBy a N \<Omega>) x = 
(bidMaximizedBy a N \<Omega> Elsee 0) x" by (metis (erased, lifting) rev_subsetD toFunction_def)
then have "setsum (toFunction (bidMaximizedBy a N \<Omega>)) (pseudoAllocation aa) = ?l2"
using lm20 by fast
moreover have "?l1 = setsum (toFunction (bidMaximizedBy a N \<Omega>)) (pseudoAllocation a)"
using lm01b setsum.cong by fast
ultimately have "?l1 - ?l2 = setsum (toFunction (bidMaximizedBy a N \<Omega>)) (pseudoAllocation a) 
- setsum (toFunction (bidMaximizedBy a N \<Omega>)) (pseudoAllocation aa)" by presburger
moreover have "... = ?r" using assms lm49 allAllocationsEquivalence by fast
ultimately show ?thesis by presburger
qed
*)

corollary lm20: assumes "\<forall>x \<in> X. f x = g x" shows "setsum f X = setsum g X" 
using assms setsum.cong by auto

lemma lm06a: assumes "fst pair \<in> N" "snd pair \<in> Pow \<Omega> - {{}}" shows 
"setsum (%g. (toFunction (bidMaximizedBy a N \<Omega>)) (fst pair, g))
        (finestpart (snd pair)) =
setsum (%g. ((bidMaximizedBy a N \<Omega>) Elsee 0) (fst pair, g)) (finestpart (snd pair))"
using assms lm01a lm05 lm04a Un_upper1 UnCI UnI1 setsum.cong finestpartSubset Diff_iff Pow_iff in_mono
proof -
let ?f1="%g.(toFunction (bidMaximizedBy a N \<Omega>))(fst pair, g)"
let ?f2="%g.((bidMaximizedBy a N \<Omega>) Elsee 0)(fst pair, g)"
{ 
  fix g assume "g \<in> finestpart (snd pair)" then have 
  0: "g \<in> finestpart \<Omega>" using assms finestpartSubset  by (metis Diff_iff Pow_iff in_mono)
  have "?f1 g = ?f2 g" 
  proof -
    have "\<And>x\<^sub>1 x\<^sub>2. (x\<^sub>1, g) \<in> x\<^sub>2 \<times> finestpart \<Omega> \<or> x\<^sub>1 \<notin> x\<^sub>2" by (metis 0 mem_Sigma_iff) 
    then have "(pseudoAllocation a <| (N \<times> finestpart \<Omega>)) (fst pair, g) = maxbid a N \<Omega> (fst pair, g)"
    unfolding toFunctionWithFallbackAlg_def maxbid_def
    by (metis (no_types) lm04a UnCI assms(1) toFunction_def)
    thus ?thesis unfolding maxbid_def by blast
  qed
}
thus ?thesis using setsum.cong by simp
qed

corollary lm07a: assumes "pair \<in> N \<times> (Pow \<Omega> - {{}})" shows 
"summedBid (toFunction (bidMaximizedBy a N \<Omega>)) pair = 
summedBid ((bidMaximizedBy a N \<Omega>) Elsee 0) pair" using assms lm06 
proof - 
have "fst pair \<in> N" using assms by force 
moreover have "snd pair \<in> Pow \<Omega> - {{}}" using assms(1) by force
ultimately show ?thesis using lm06a by blast
qed

lemma lm08a: assumes "\<forall>x \<in> X. f x = g x" shows "f`X=g`X" using assms by (metis image_cong)

corollary lm09a: "\<forall> pair \<in> N \<times> (Pow \<Omega> - {{}}).  
summedBid (toFunction (bidMaximizedBy a N \<Omega>)) pair = 
summedBid ((bidMaximizedBy a N \<Omega>) Elsee 0) pair" using lm07a 
by blast  

corollary lm10: 
"(summedBid (toFunction (bidMaximizedBy a N \<Omega>))) ` (N \<times> (Pow \<Omega> - {{}}))=
(summedBid ((bidMaximizedBy a N \<Omega>) Elsee 0)) ` (N \<times> (Pow \<Omega> - {{}}))" (is "?f1 ` ?Z = ?f2 ` ?Z")
proof - (*MC: no way to automatize this trivial proof??!! *)
have "\<forall> z \<in> ?Z. ?f1 z = ?f2 z" by (rule lm09a) thus ?thesis 
using image_cong by (metis(mono_tags,lifting))
qed

corollary lm11: "summedBidVectorRel (toFunction (bidMaximizedBy a N \<Omega>)) N \<Omega> =
summedBidVectorRel ((bidMaximizedBy a N \<Omega>) Elsee 0) N \<Omega>" using lm10 by metis

corollary lm12: "summedBidVectorRel (maxbid' a N \<Omega>) N \<Omega> = summedBidVectorRel (maxbid a N \<Omega>) N \<Omega>"
unfolding maxbid_def using lm11 by metis

lemma lm13: assumes "x \<in> (N \<times> (Pow \<Omega> - {{}}))" shows 
"summedBidVector' (maxbid' a N \<Omega>) N \<Omega> x = summedBidVector (maxbid a N \<Omega>) N \<Omega> x"
(is "?f1 ?g1 N \<Omega> x = ?f2 ?g2 N \<Omega> x")
using assms lm02 lm12  
proof -
let ?h1="maxbid' a N \<Omega>" let ?h2="maxbid a N \<Omega>" let ?hh1="real \<circ> ?h1" let ?hh2="real \<circ> ?h2"
have "summedBidVectorRel ?h1 N \<Omega> = summedBidVectorRel ?h2 N \<Omega>" using lm12 by metis 
moreover have "summedBidVector ?h2 N \<Omega>=(summedBidVectorRel ?h2 N \<Omega>) Elsee 0"
unfolding summedBidVector_def by fast
ultimately have " summedBidVector ?h2 N \<Omega>=summedBidVectorRel ?h1 N \<Omega> Elsee 0" by presburger
moreover have "... x = (toFunction (summedBidVectorRel ?h1 N \<Omega>)) x" using assms 
lm01a summedBidVectorCharacterization by (metis (mono_tags))
ultimately have "summedBidVector ?h2 N \<Omega> x = (toFunction (summedBidVectorRel ?h1 N \<Omega>)) x" 
by (metis (lifting, no_types))
thus ?thesis by simp
qed

corollary lm70c: assumes "card N > 0" "distinct \<Omega>" shows 
"possibleAllocationsRel N (set \<Omega>) = set (possibleAllocationsAlg N \<Omega>)"  
using assms possibleAllocationsBridgingLemma by metis

lemma lm24: assumes "card A > 0" "card B > 0" shows "card (A \<union> B) > 0" 
using assms card_gt_0_iff finite_Un sup_eq_bot_iff by (metis(no_types))
corollary lm24b: assumes "card A > 0" shows "card ({a} \<union> A) > 0" using assms lm24 
by (metis card_empty card_insert_disjoint empty_iff finite.emptyI lessI)

corollary assumes "card N > 0" "distinct \<Omega>" shows
"maximalStrictAllocations N (set \<Omega>) b = maximalStrictAllocationsAlg N \<Omega> b"
unfolding allStrictAllocations_def
using assms lm70c lm24b by (metis(no_types))

(*
proof - let ?N="{seller}\<union>N" 
have "card ?N > 0" using assms(1) using 
One_nat_def card.insert card_0_eq card_ge_0_finite finite_Un gr0I insert_absorb sup_bot_left sup_eq_bot_iff zero_neq_one
by (metis )
then have "allAllocations ?N (set \<Omega>) = set (allStrictAllocations ?N \<Omega>)"
using assms(2) by (rule lm70c)
then show ?thesis by presburger
qed
*)

corollary lm70d: assumes "card N > 0" "distinct \<Omega>" shows 
"allAllocations N (set \<Omega>) = set (allStrictAllocations N \<Omega>)" 
unfolding allStrictAllocations_def
using assms lm70c by blast 

corollary lm70f: assumes "card N > 0" "distinct \<Omega>" shows 
"winningAllocationsRel N (set \<Omega>) b = 
(argmax \<circ> setsum) b (set (allStrictAllocations N \<Omega>))"
unfolding allStrictAllocations_def
using assms lm70c by (metis comp_apply)

corollary lm70g: assumes "card N > 0" "distinct \<Omega>" shows
"chosenAllocation' N \<Omega> b r = chosenAllocation N \<Omega> b r" 
unfolding chosenAllocation_def using assms lm70f allStrictAllocations_def by (metis(no_types)) 
corollary lm13b: assumes "x \<in> (N \<times> (Pow \<Omega> - {{}}))" shows "tiebids' a N \<Omega> x = tiebids a N \<Omega> x" (is "?L=_") 
proof - 
have "?L = summedBidVector' (maxbid' a N \<Omega>) N \<Omega> x" by fast moreover have "...= 
summedBidVector (maxbid a N \<Omega>) N \<Omega> x" using assms by (rule lm13) ultimately show ?thesis 
unfolding tiebids_def by fast
qed 

lemma lm14: assumes "card N > 0" "distinct \<Omega>" "a \<subseteq> (N \<times> (Pow (set \<Omega>) - {{}}))" shows
"setsum (resolvingBid N \<Omega> b r) a = setsum (resolvingBidAlg N \<Omega> b r) a" (is "?L=?R") 
(* (is "?s ?r' a = ?s ?r a") *)
proof - 
let ?c'="chosenAllocation' N \<Omega> b r" let ?c="chosenAllocation N \<Omega> b r" let ?r'="resolvingBid N \<Omega> b r"
have "?c' = ?c" using assms(1,2) by (rule lm70g) then
have "?r' = tiebids' ?c N (set \<Omega>)" by presburger
moreover have "\<forall>x \<in> a. tiebids' ?c N (set \<Omega>) x = tiebids ?c N (set \<Omega>) x" using assms(3) lm13b by blast
ultimately have "\<forall>x \<in> a. ?r' x = resolvingBidAlg N \<Omega> b r x" unfolding resolvingBidAlg_def by presburger
thus ?thesis using setsum.cong by simp
qed
lemma lm15: "allAllocations N \<Omega> \<subseteq> Pow (N \<times> (Pow \<Omega> - {{}}))" by (metis PowI allocationPowerset subsetI)
corollary lm14b: assumes "card N > 0" "distinct \<Omega>" "a \<in> allAllocations N (set \<Omega>)" 
shows "setsum (resolvingBid N \<Omega> b r) a = setsum (resolvingBidAlg N \<Omega> b r) a"
proof -
have "a \<subseteq> N \<times> (Pow (set \<Omega>) - {{}})" using assms(3) lm15 by blast 
thus ?thesis using assms(1,2) lm14 by blast
qed

corollary lm14c: assumes "finite N" "distinct \<Omega>" "a \<in> maximalStrictAllocations N (set \<Omega>) b" 
shows "setsum (randomBids N \<Omega> b r) a = setsum (randomBidsAlg N \<Omega> b r) a"
proof - 
have "card (N\<union>{seller})>0" using assms(1) sup_eq_bot_iff insert_not_empty
by (metis card_gt_0_iff finite.emptyI finite.insertI finite_UnI)
moreover have "distinct \<Omega>" using assms(2) by simp
moreover have "a \<in> allAllocations (N\<union>{seller}) (set \<Omega>)" using assms(3) by fastforce
ultimately show ?thesis unfolding randomBidsAlg_def by (rule lm14b)
qed

lemma lm16: assumes "\<forall>x\<in>X. f x = g x" shows "argmax f X=argmax g X" 
using assms argmaxLemma Collect_cong image_cong 
by (metis(no_types,lifting))

(*MC: without passing theorem lm02 with "using", e and z3 (through sledgehammer) say this theorem is unprovable *)

corollary lm92e: assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" shows 
"1=card (argmax (setsum (randomBidsAlg N \<Omega> b r)) (maximalStrictAllocations N (set \<Omega>) b))"
using assms vcgaDefinitenessVariant lm14c 
proof -
have "\<forall> a \<in> maximalStrictAllocations N (set \<Omega>) b. 
setsum (randomBids N \<Omega> b r) a = setsum (randomBidsAlg N \<Omega> b r) a" using assms(3,1) lm14c by blast
then have "argmax (setsum (randomBidsAlg N \<Omega> b r)) (maximalStrictAllocations N (set \<Omega>) b) =
argmax (setsum (randomBids N \<Omega> b r)) (maximalStrictAllocations N (set \<Omega>) b)" using lm16 by blast
moreover have "card ... = 1" using assms by (rule vcgaDefinitenessVariant)
ultimately show ?thesis by presburger
qed

corollary lm70e: assumes "finite N" "distinct \<Omega>" shows
"maximalStrictAllocations N (set \<Omega>) b=maximalStrictAllocationsAlg N \<Omega> b" 
proof -
let ?N="{seller} \<union> N" 
have "card ?N>0" using assms(1) by (metis (full_types) card_gt_0_iff finite_insert insert_is_Un insert_not_empty)
thus ?thesis using assms(2) lm70d by metis
qed

corollary assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" shows 
"1=card (argmax (setsum (randomBidsAlg N \<Omega> b r)) (maximalStrictAllocationsAlg N \<Omega> b))"
proof - 
have "1=card (argmax (setsum (randomBidsAlg N \<Omega> b r)) (maximalStrictAllocations N (set \<Omega>) b))"
using assms by (rule lm92e)
moreover have "maximalStrictAllocations N (set \<Omega>) b = maximalStrictAllocationsAlg N \<Omega> b" 
using assms(3,1) by (rule lm70e) ultimately show ?thesis by metis
qed

lemma "maximalStrictAllocations N (set \<Omega>) b \<subseteq> Pow (({seller}\<union>N) \<times> (Pow (set \<Omega>) - {{}}))"
using lm15 winningAllocationPossible subset_trans by (metis (no_types))

lemma lm17: "(image converse) (Union X)=Union ((image converse) ` X)" by auto

lemma "possibleAllocationsRel N \<Omega> =
Union {converse`(injections Y N)| Y. Y \<in> all_partitions \<Omega>}" 
by auto

lemma "allAllocations N \<Omega> = Union{{a^-1|a. a\<in>injections Y N}|Y. Y\<in>all_partitions \<Omega>}" by auto
term "(\<Sum>i\<in>X. f i)"
term "(\<Union>i\<in>X. x i)"
abbreviation "endowment a n == a,,,n"
abbreviation "vcgEndowment N \<Omega> b r n==endowment (vcga N \<Omega> b r) n"

(*abbreviation "f x y == ((x::real)+1)*(y+2)"*)

abbreviation "firstPriceP N \<Omega> b r n ==
b (n, winningAllocationAlg N \<Omega> r b,, n)"

lemma assumes "\<forall> X. b (n, X) \<ge> 0" shows
"firstPriceP N \<Omega> b r n \<ge> 0" using assms by blast

(*
value "injections_alg [0::nat,1] {11::nat, 12}"
thy_deps

theorem counterexample_lm64c: assumes "a \<in> allocationsUniverse" 
"n1\<in> Domain a" "n2 \<in> Domain a"
shows "a,,,n1 \<inter> a,,,n2={}" nitpick
value "vcgaAlg (int`N00) \<Omega>00 (b00 Elsee 0) 1" 
*)


(* MC: test examples, commented out 
definition "N00 = {1,6::nat}"
definition "\<Omega>00 = [11::nat, 12, 13]"
definition "b00 = 
{
((1::nat,{11::nat}),3::nat),
((1,{12}),0),
((1,{11,12}),4),
((2,{11}),2),
((2,{12}),2),
((2,{11,12}),1)
}"
term b00
(* definition "example = vcgaAlg (int`N00) \<Omega>00 (b00 Elsee 0) 1" *)
definition ao where "ao=(%x. (if x=0 then (24::nat) else 11))"

value "randomBidsAlg {1,2,3} [11,12,13] (b01 Elsee 0) 1 (2,{12})" 
definition "N01={1::integer,2,3}"
definition "\<Omega>01=[11::integer,12,13]"
definition "f01=b01 Elsee 0"
definition "evaluateMe01 = vcgaAlg N01 \<Omega>01 f01 1"
definition "evaluateMe02 = maximalStrictAllocationsAlg N01 \<Omega>01 f01"
definition "evaluateMe03 = randomBidsAlg N01 \<Omega>01 f01 1 (2,{12})"
value "chosenAllocation (N01\<union>{seller}) \<Omega>01 f01 1" 
definition "chosenAllocation01={(2, {12}), (3, {13, 11})}"
(* value "graph ((N01\<union>{seller}) \<times> (Pow (set \<Omega>01)-{{}})) (randomBidsAlg N01 \<Omega>01 f01 1)" *) 
abbreviation "graphRandomBids01::((integer \<times> integer set) \<times> nat) set ==
{((3, {12, 13}), 1), ((3, {12}), 0), ((3, {}), 0), ((3, {13}), 1), ((3, {11, 13}), 2), ((3, {11}), 1),
  ((3, {11, 12}), 1), ((3, {11, 12, 13}), 2), ((2, {12, 13}), 1), ((2, {12}), 1), ((2, {}), 0), ((2, {13}), 0),
  ((2, {11, 13}), 0), ((2, {11}), 0), ((2, {11, 12}), 1), ((2, {11, 12, 13}), 1), ((1, {12, 13}), 0),
  ((1, {12}), 0), ((1, {}), 0), ((1, {13}), 0), ((1, {11, 13}), 0), ((1, {11}), 0), ((1, {11, 12}), 0),
  ((1, {11, 12, 13}), 0), ((seller, {12, 13}), 0), ((seller, {12}), 0), ((seller, {}), 0), ((seller, {13}), 0),
  ((seller, {11, 13}), 0), ((seller, {11}), 0), ((seller, {11, 12}), 0), ((seller, {11, 12, 13}), 0)}"
value "graph ((N01\<union>{seller}) \<times> (Pow (set \<Omega>01)-{{}})) (tiebids 
chosenAllocation01 
N01 (set \<Omega>01))"
(* 
MC: A key hint is in the much longer evaluation time of the following, compared to the one above
MC: fixed by changing "abbreviation tiebids ..." into "definition tiebids ..."
*)
value "graph ((N01\<union>{seller}) \<times> (Pow (set \<Omega>01)-{{}})) (tiebids 
(chosenAllocation (N01\<union>{seller}) \<Omega>01 f01 1) N01 (set \<Omega>01))"

value "vcgaAlg N01 \<Omega>01 f01 1"
value "b01 \<union> {}"

*)

abbreviation "goods == sorted_list_of_set o Union o Range o Domain"
(*
abbreviation "b02==b01 \<union> ({1,2,3}\<times>{{14},{15}})\<times>{20}"
abbreviation "N02==participants b02"
abbreviation "\<Omega>02==goods b02"
abbreviation "f02==b02 Elsee 0"

(*value "chosenAllocation (N02\<union>{seller}) \<Omega>02 f02 1"
value "maximalStrictAllocationsAlg (N02\<union>{seller}) \<Omega>02 f02"*)
abbreviation "chosenAllocation02==
{(2, {14}), (3, {15}), (1, {12, 13, 11})}" 
value "graph ((N02\<union>{seller}) \<times> (Pow (set \<Omega>02)-{{}}))
(tiebids chosenAllocation02 (participants b02) (set (goods b02)))"
(*value "graph ((N02\<union>{seller}) \<times> (Pow (set \<Omega>02)-{{}}))
(tiebids (chosenAllocation (N02\<union>{seller}) \<Omega>02 f02 1) (participants b02) (set (goods b02)))"*)
(*value "graph ((N02\<union>{seller}) \<times> (Pow (set \<Omega>02)-{{}}))
(resolvingBidAlg (N02\<union>{seller}) \<Omega>02 f02 1)"*) 
(* value "randomBidsAlg ((fst o fst)`b02) (sorted_list_of_set (Union ((snd o fst)`b02))) (b02 Elsee 0) 1 (1,{11})" *)
*)

(* part to make input/output easier *)
abbreviation "allocationPrettyPrint2 a == map (%x. (x, sorted_list_of_set(a,,x))) ((sorted_list_of_set \<circ> Domain) a)"
definition "helper (list) == (((hd\<circ>hd) list, set (list!1)), hd(list!2))"
definition "listBid2funcBid listBid = (helper`(set listBid)) Elsee (0::integer)"

abbreviation "singleBidConverter x == ((fst x, set ((fst o snd) x)), (snd o snd) x)"
definition "Bid2funcBid b = set (map singleBidConverter b) Elsee (0::integer)"

abbreviation "participantsSet b == fst ` (set b)"
abbreviation "goodsList2 b == sorted_list_of_set (Union ((set o fst o snd) `(set b)))"

definition "allocation b r = {allocationPrettyPrint2 
(vcgaAlg ((participantsSet b)) (goodsList2 b) (Bid2funcBid b) r)
}"

definition "payments b r = vcgpAlg ((participantsSet b)) (goodsList2 b) (Bid2funcBid b) r"
export_code allocation payments chosenAllocationEff in Scala module_name VCG file "/dev/shm/VCG.scala"





abbreviation "b01 == 
{
((1::integer,{11::integer, 12, 13}),20::integer),
((1,{11,12}),18),
((2,{11}),10),
((2,{12}),15),
((2,{12,13}),18),
((3,{11}),2),
((3,{11,12}),12),
((3,{11,13}),17),
((3,{12,13}),18),
((3,{11,12,13}),19),
((4,{11,12,13,14,15,16}),19)
}"
value "participants b01"
(*
MC: Why does this 
value "maximalStrictAllocationsAlg {1,2,3} [11, 12, 13]
 (%x. (0::integer))"
take longer than this?
value "maximalStrictAllocationsAlg {1,2,3} [11, 12, 13]
 (b01 Elsee 0)"
*)
(* value "possibleAllocationsAlg3 {1,2,3,4,5,6,7,8} [11, 12, 13, 14, 15, 16, 17, 18, 19]"*)

end

(* 
{ { echo asdff; tac ../VCG.scala ; } | sed -n -e '1,/\}/ !p'  | tac | cat - ../addedWrapper.scala; echo \}; }| sed -e "s/\(Nat\)\([^a-zA-Z]\)/NNat\2/g; s/\(Sup_set\)\([^a-zA-Z]\)/SSup_set\2/g"
*)

