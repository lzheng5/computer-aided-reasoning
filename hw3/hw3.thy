theory hw3 
imports Main
begin

abbreviation equiv_class :: "'A \<Rightarrow> 'A rel \<Rightarrow> 'A set" ("[_]\<^sub>_" [1000, 999] 999) where 
 "equiv_class x E \<equiv> E `` {x}"

lemma "[x]\<^sub>R = {y. (x, y) \<in> R}"
  by (simp add: Image_def)

(* 3.1 *)
theorem equiv_class_dec :                 
  "equiv A R \<Longrightarrow> \<forall> x y. ([x]\<^sub>R = [y]\<^sub>R) \<or> (disjnt ([x]\<^sub>R) ([y]\<^sub>R))"
  apply clarify
  by (simp add: disjnt_equiv_class equiv_class_eq_iff)

(* 3.2.a *) 
definition sym_part :: "'A rel \<Rightarrow> 'A rel" where 
  "sym_part R = {(x, y) | x y . (x, y) \<in> R \<and> (y, x) \<in> R}"

theorem preorder_induce_equiv : 
  "preorder_on A R \<Longrightarrow> equiv A (sym_part R)"
  unfolding sym_part_def preorder_on_def equiv_def
  apply clarify
  apply (auto; simp add: refl_on_def sym_on_def trans_on_def) 
  by blast

(* 3.2.b *) 
definition quotient_order :: "'A rel \<Rightarrow> ('A set \<times> 'A set) set" where
  "quotient_order R = {(X, Y). \<exists>x y. X = [x]\<^sub>R \<and> Y = [y]\<^sub>R \<and> (x, y) \<in> R}"

theorem quotient_poset : 
  "preorder_on A R \<Longrightarrow> 
   E = (sym_part R) \<Longrightarrow> 
   partial_order_on (A // E) (quotient_order E)"
  unfolding preorder_on_def partial_order_on_def sym_part_def quotient_order_def
  apply clarify
  unfolding quotient_def
  apply auto
    apply (auto simp add: refl_on_def) 
  apply (simp add: trans_on_def, blast) 
  apply (simp add: antisym_on_def) 
  apply clarify
  by (meson transD)

(* 4.1 *) 
(* Have to redefine total_on *) 
definition total_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "total_on A r \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>A. (x, y) \<in> r \<or> (y, x) \<in> r)"

theorem total_union_inverse : 
  "total_on A R \<Longrightarrow> 
   R \<subseteq> A \<times> A \<Longrightarrow> 
   R \<union> R\<inverse> = A \<times> A"
  unfolding total_on_def 
  by auto

(* 4.2 *) 
definition strict_part :: "'A rel \<Rightarrow> 'A rel" where 
  "strict_part R = { (x, y) | x y . (x, y) \<in> R \<and> x \<noteq> y }"

definition strict_partial_order_on :: "'A set \<Rightarrow> 'A rel \<Rightarrow> bool" where 
  "strict_partial_order_on A R = (\<exists> P . partial_order_on A P \<and> R = strict_part P)"

definition "refl_part A R \<equiv> R \<union> (Id_on A)"

lemma refl_part_domain : 
  "R \<subseteq> A \<times> A \<Longrightarrow> (a, b) \<in> refl_part A R \<Longrightarrow> (a \<in> A \<and> b \<in> A)"
  unfolding refl_part_def Id_on_def
  by blast

lemma refl_part_member : 
  "(a, b) \<in> R \<Longrightarrow> (a, b) \<in> refl_part A R"
  unfolding refl_part_def Id_on_def 
  by blast

lemma refl_part_member_inv : 
 "(a, b) \<in> refl_part A R \<Longrightarrow> a \<noteq> b \<Longrightarrow> (a, b) \<in> R"
  unfolding refl_part_def Id_on_def
  by blast

lemma refl_refl_part : 
  "refl_on A (refl_part A R)"
  unfolding refl_part_def Id_on_def refl_on_def
  by auto 

lemma trans_refl_part : 
  "R \<subseteq> A \<times> A \<Longrightarrow> trans_on A R \<Longrightarrow> trans (refl_part A R)"
  unfolding refl_part_def trans_on_def
  by blast 

lemma antisym_refl_part : 
  "R \<subseteq> A \<times> A \<Longrightarrow> irrefl_on A R \<Longrightarrow> trans_on A R \<Longrightarrow> antisym (refl_part A R)"
  unfolding trans_on_def antisym_on_def refl_part_def Id_on_def irrefl_on_def
  apply clarify
  apply (erule UnE, blast)
  by (erule UnE; blast)

theorem strict_partial_order_iff_irrefl_trans : 
  "R \<subseteq> A \<times> A \<Longrightarrow> 
   (strict_partial_order_on A R \<longleftrightarrow> (irrefl_on A R \<and> trans_on A R))"
  unfolding strict_partial_order_on_def strict_part_def partial_order_on_def
  apply auto
    apply (simp add: irrefl_on_def)
   apply (simp add: preorder_on_def trans_on_def refl_on_def antisym_on_def, blast)
  apply (rule_tac x="refl_part A R" in exI) 
  unfolding preorder_on_def 
  apply (auto simp add: refl_part_member
                        refl_part_domain refl_refl_part 
                        trans_refl_part antisym_refl_part)
   apply (simp add: irrefl_on_def, blast)
  by (simp add: refl_part_member_inv)

(* 4.3 *) 
theorem strict_partial_order_induce_partial_order : 
  "strict_partial_order_on A R \<Longrightarrow> 
   partial_order_on A (R \<union> (Id_on A))"
  unfolding strict_partial_order_on_def partial_order_on_def strict_part_def Id_on_def
  apply clarify
  apply auto
    apply (simp add: refl_on_def preorder_on_def trans_on_def, auto)
  by (simp add: preorder_on_def antisym_on_def trans_on_def)

(* 4.4 *) 
lemma preorder_irrefl_trans : 
  "preorder_on A R \<Longrightarrow>
   P = R - R\<inverse> \<Longrightarrow>  
   (irrefl_on A P \<and> trans_on A P)"
  unfolding preorder_on_def trans_on_def irrefl_on_def
  by auto

lemma preorder_subset : 
  "preorder_on A R \<Longrightarrow> 
   R \<subseteq> (A \<times> A)" 
  unfolding preorder_on_def 
  by blast

theorem preorder_induce_strict_partial_order : 
  "preorder_on A R \<Longrightarrow> 
   strict_partial_order_on A (R - R\<inverse>)"
  using preorder_irrefl_trans strict_partial_order_iff_irrefl_trans
  by (smt (verit, best) Diff_subset preorder_subset subset_trans)

(* 4.5 *) 
definition "total_order_on A R \<equiv> partial_order_on A R \<and> total_on A R"

definition strict_total_order_on :: "'A set \<Rightarrow> 'A rel \<Rightarrow> bool" where 
  "strict_total_order_on A R \<longleftrightarrow> (\<exists> P . total_order_on A P \<and> R = strict_part P)"

lemma partial_order_subset : 
  "partial_order_on A R \<Longrightarrow> 
   R \<subseteq> (A \<times> A)" 
  using partial_order_on_def preorder_subset 
  by blast

lemma strict_partial_order_subset : 
  "strict_partial_order_on A R \<Longrightarrow> 
   R \<subseteq> (A \<times> A)" 
  unfolding strict_partial_order_on_def 
  apply clarify 
  by (metis UnCI partial_order_onD(4) refl_part_def refl_part_domain
      strict_partial_order_induce_partial_order
      strict_partial_order_on_def)

lemma strict_total_order_strict_partial_order : 
  "strict_total_order_on A R \<Longrightarrow> strict_partial_order_on A R"
  unfolding strict_total_order_on_def strict_partial_order_on_def total_order_on_def partial_order_on_def
  by auto

lemma strict_total_order_subset : 
  "strict_total_order_on A R \<Longrightarrow> 
   R \<subseteq> (A \<times> A)" 
  by (metis strict_total_order_strict_partial_order strict_partial_order_subset)

definition connected_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "connected_on A r \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>A. (x, y) \<in> r \<or> (y, x) \<in> r \<or> x = y)"

lemma strict_total_order_connected : 
  "strict_total_order_on A R \<Longrightarrow> connected_on A R" 
  unfolding strict_total_order_on_def connected_on_def total_order_on_def total_on_def strict_part_def
  by auto

lemma strict_total_order_irrefl_trans_connected : 
  "strict_total_order_on A R \<Longrightarrow> (irrefl_on A R \<and> trans_on A R \<and> connected_on A R)"
  using strict_total_order_connected strict_total_order_strict_partial_order strict_partial_order_iff_irrefl_trans
  by (metis le_sup_iff partial_order_onD(4)
      strict_partial_order_induce_partial_order) 

lemma total_refl_part : 
  "connected_on A R \<Longrightarrow> hw3.total_on A (refl_part A R)"
  unfolding refl_part_def total_on_def connected_on_def
  by blast

lemma strict_refl_part_member : 
  "R \<subseteq> A \<times> A \<Longrightarrow> (a, b) \<in> R \<Longrightarrow> irrefl_on A R \<Longrightarrow> (a, b) \<in> strict_part (refl_part A R)"
  unfolding refl_part_def strict_part_def Id_on_def irrefl_on_def 
  by blast
  
lemma strict_refl_part_member_inv : 
  "(a, b) \<in> strict_part (refl_part A R) \<Longrightarrow> (a, b) \<in> R"
  unfolding refl_part_def strict_part_def Id_on_def irrefl_on_def 
  by blast
 
lemma irrefl_trans_connected_strict_total_order : 
  "(R \<subseteq> A \<times> A \<and> irrefl_on A R \<and> trans_on A R \<and> connected_on A R) \<Longrightarrow> strict_total_order_on A R"
  unfolding strict_total_order_on_def total_order_on_def 
  apply (rule_tac x="refl_part A R" in exI)
  apply auto 
  unfolding partial_order_on_def preorder_on_def 
     apply (auto simp add: refl_part_member
                           refl_part_domain refl_refl_part 
                           trans_refl_part antisym_refl_part
                           total_refl_part strict_refl_part_member)
  by (simp add: strict_refl_part_member_inv)

theorem strict_total_order_iff_irrefl_trans_connected : 
  "strict_total_order_on A R \<longleftrightarrow> (R \<subseteq> A \<times> A \<and> irrefl_on A R \<and> trans_on A R \<and> connected_on A R)"
  using strict_total_order_subset strict_total_order_irrefl_trans_connected irrefl_trans_connected_strict_total_order
  by metis

(* 4.6 *)
(* Have to redefine [well_order_on] *) 
definition well_order_on :: "'A set \<Rightarrow> 'A rel \<Rightarrow> bool" where 
  "well_order_on A R \<longleftrightarrow> strict_total_order_on A R \<and> wf_on A R"

lemma well_order_wf_connected : 
  "well_order_on A R \<Longrightarrow> wf_on A R \<and> connected_on A R" 
  unfolding well_order_on_def 
  by (metis strict_total_order_connected)

lemma wf_on_wf : 
  "R \<subseteq> (A \<times> A) \<Longrightarrow> 
   wf_on A R \<Longrightarrow> 
   wf R"
  unfolding wf_on_def wf_def 
  by (metis UNIV_I mem_Sigma_iff subset_eq)

(* [TODO] The following proofs rely on wf_trancl, wf_irrefl, wf_asym *) 
(* Reorder the following lemmas [wf_trancl_wf], [wf_on_irrefl], [wf_on_asym] *) 

lemma wf_no_3_cycles : 
  "wf R \<Longrightarrow> (x, y) \<in> R \<Longrightarrow> (y, z) \<in> R \<Longrightarrow> (z, x) \<in> R \<Longrightarrow> False"
  apply (drule wf_trancl)
  apply (drule r_into_trancl)
  apply (drule r_into_trancl)
  apply (drule r_into_trancl)
  by (metis trancl_trans wf_asym)

lemma wf_connected_trans : 
  "R \<subseteq> (A \<times> A) \<Longrightarrow> 
   wf_on A R \<Longrightarrow> 
   connected_on A R \<Longrightarrow> 
   trans_on A R" 
  unfolding trans_on_def connected_on_def
  apply clarify 
  (* case analysis on whether x < z *) 
  apply (drule_tac x="x" in bspec, blast)
  apply (drule_tac x="z" in bspec, blast)
  apply (drule wf_on_wf, blast)
  apply (erule disjE, blast)
  apply (erule disjE)
   apply (frule_tac a="x" and x="z" in wf_not_sym)
  apply (metis wf_no_3_cycles)
  apply metis
  by (metis wf_asym)

lemma wf_connected_well_order : 
  "R \<subseteq> (A \<times> A) \<and> wf_on A R \<and> connected_on A R \<Longrightarrow> well_order_on A R" 
  unfolding well_order_on_def 
  by (metis irrefl_on_def irrefl_trans_connected_strict_total_order
      wf_connected_trans wf_irrefl wf_on_wf)

theorem well_order_iff_wf_connected : 
  "well_order_on A R \<longleftrightarrow> (R \<subseteq> (A \<times> A) \<and> wf_on A R \<and> connected_on A R)" 
  by (metis hw3.well_order_on_def strict_total_order_subset
      well_order_wf_connected wf_connected_well_order)

(* 5.1 *) 
definition minimal_element :: "'A set \<Rightarrow> 'A rel \<Rightarrow> 'A \<Rightarrow> bool" where 
  "minimal_element A R m \<longleftrightarrow> (m \<in> A \<and> (\<forall> x \<in> A . (x, m) \<in> R \<longrightarrow> x = m))"

lemma min_wf : 
  assumes Hsubset_min : "\<forall> B \<subseteq> A . B \<noteq> {} \<longrightarrow> (\<exists> m \<in> B . minimal_element B R m)"
    and Hirrefl : "irrefl_on A R" 
  shows "wf_on A R" 
  unfolding wf_on_def
proof (intro allI impI)
  fix P
  assume IH : "(\<forall>x\<in>A. (\<forall>y\<in>A. (y, x) \<in> R \<longrightarrow> P y) \<longrightarrow> P x)"

  \<comment> \<open> key step: instantiate B with "{z \<in> A . \<not> P z}" \<close>
  let ?B = "{z \<in> A . \<not> P z}" 
  let ?G = "\<forall> x \<in> A . P x"
  have "?B = {} \<or> ?B \<noteq> {}" by blast
  thus "?G"
  proof 
    assume "?B = {}"
    thus "?G" by blast
  next 
    assume "?B \<noteq> {}"
    have HS : "?B \<subseteq> A" by blast
    from Hsubset_min and HS and `?B \<noteq> {}` obtain m where mB : "m \<in> ?B" and Hmin : "minimal_element ?B R m"
      by (metis (mono_tags, lifting))
    have "\<forall>y \<in> A. (y, m) \<in> R \<longrightarrow> P y"
    proof (intro ballI impI)
      fix y assume yA : "y \<in> A" and yRm : "(y, m) \<in> R"
      show "P y" 
      proof (rule ccontr)
        assume HnPy : "\<not> (P y)"
        \<comment> \<open> key step: derive (m, m) \<in> R ---> contradiction \<close>
        then have "(m, m) \<in> R" using yA yRm Hmin unfolding minimal_element_def by blast
        thus False using Hirrefl mB unfolding irrefl_on_def by blast
      qed
    qed

    with IH and `m \<in> ?B` have "P m" by blast
    with `m \<in> ?B` show "\<forall>x \<in> A. P x" by blast
  qed
qed

lemma wf_min : 
  assumes wf : "wf_on A R"
  shows "\<forall> B \<subseteq> A . B \<noteq> {} \<longrightarrow> (\<exists> m \<in> B . minimal_element B R m)"
proof (intro allI impI)
  fix B
  assume HS : "B \<subseteq> A" and HC : "B \<noteq> {}"

  let ?G = "\<exists>m\<in>B. minimal_element B R m"
  show ?G 
  proof (rule ccontr)
    assume Hno_min : "\<not> ?G" 

    \<comment> \<open> key step: instantiate P with "\<lambda>x. x \<notin> B" \<close>
    from wf have IH: "(\<forall>x\<in>A. (\<forall>y\<in>A. (y, x) \<in> R \<longrightarrow> y \<notin> B) \<longrightarrow> x \<notin> B) \<longrightarrow> (\<forall>x\<in>A. x \<notin> B)"
      unfolding wf_on_def by (rule spec[of _ "\<lambda>x. x \<notin> B"])

    have "\<forall> x \<in> A . (\<forall> y \<in> A . (y, x) \<in> R \<longrightarrow> y \<notin> B) \<longrightarrow> x \<notin> B"
    proof (intro ballI impI)
      fix x assume xA : "x \<in> A" and Hpredm : "(\<forall> y \<in> A . (y, x) \<in> R \<longrightarrow> y \<notin> B)"
      show "x \<notin> B"
      proof (* avoid (rule ccontr) *)
        assume xB : "x \<in> B"

        have "minimal_element B R x"
          unfolding minimal_element_def using xA xB Hpredm HS by blast

        \<comment> \<open> key step: derive x to be the min element ---> contradiction \<close>
        hence ?G using xB by blast
        with Hno_min show False by contradiction
      qed 
    qed 

    with IH have "(\<forall>x\<in>A. x \<notin> B)" by blast 
    with HS have "B = {}" by blast
    with HC show False by contradiction
  qed
qed

(* Note this is stronger than what's in the homework *)
theorem wf_iff_min : 
  "R \<subseteq> (A \<times> A) \<Longrightarrow> 
   (wf_on A R \<longleftrightarrow> (irrefl_on A R \<and> (\<forall> B \<subseteq> A . B \<noteq> {} \<longrightarrow> (\<exists> m \<in> B . minimal_element B R m))))"
  using wf_min min_wf wf_irrefl wf_on_wf irrefl_on_def by metis

(* 5.2 *) 
experiment
begin

(* [!] Note the definition given in the homework is inaccurate. *)
definition "least_element A R m \<longleftrightarrow> (m \<in> A \<and> (\<forall> x \<in> A . (m, x) \<in> R))"

(*
  Counter Example 
  Let A = {1, 2} and R = {} (the empty relation).
  1. R is well-founded on A because there are no infinite descending chains.
  2. R is irreflexive (irrefl_on A R).
  3. Let B = A = {1, 2}. B is a non-empty subset of A.
  4. For m = 1 to be the 'least_element', (1, 2) must be in R. It is not.
  5. For m = 2 to be the 'least_element', (2, 1) must be in R. It is not.
  Therefore, no least element exists in B.
*)

lemma strict_partial_order_counterexample:
  fixes A :: "nat set" and R :: "nat rel"
  defines "A \<equiv> {1, 2}"
    and "R \<equiv> {}"
  shows "irrefl_on A R"           (* Irreflexive *)
    and "trans R"                 (* Transitive (vacuously) *)
    and "wf_on A R"               (* Well-founded *)
    and "\<exists> B \<subseteq> A. B \<noteq> {} \<and> \<not>(\<exists> m \<in> B. least_element B R m)"
proof -
  show "irrefl_on A R" unfolding irrefl_on_def R_def by blast
  show "trans R" unfolding trans_def R_def by blast
  show "wf_on A R" unfolding wf_on_def R_def by blast
  
  let ?B = "{1, 2}"
  have "?B \<subseteq> A" unfolding A_def by simp
  moreover have "\<not>(\<exists> m \<in> ?B. least_element ?B R m)"
    unfolding least_element_def R_def by auto
  ultimately show "\<exists> B \<subseteq> A. B \<noteq> {} \<and> \<not>(\<exists> m \<in> B. least_element B R m)" by blast
qed

end

definition least_element :: "'A set \<Rightarrow> 'A rel \<Rightarrow> 'A \<Rightarrow> bool" where 
  "least_element A R m \<longleftrightarrow> (m \<in> A \<and> (\<forall> x \<in> A . x \<noteq> m \<longrightarrow> (m, x) \<in> R))"

lemma connected_min_least : 
  assumes Hconnected : "connected_on A R"
    and Hmin : "minimal_element A R x"
  shows "least_element A R x"
  unfolding least_element_def
proof 
  show "x \<in> A" using Hmin unfolding minimal_element_def by blast
next 
  have xA : "x \<in> A" using Hmin unfolding minimal_element_def by blast
  show "\<forall>z\<in>A. z \<noteq> x \<longrightarrow> (x, z) \<in> R"
  proof (rule ballI, rule impI)
    fix z assume zA : "z \<in> A" and Hneq : "z \<noteq> x"
    consider "(x, z) \<in> R" | "(z, x) \<in> R" | "x = z" using Hconnected xA zA unfolding connected_on_def by blast
    then show "(x, z) \<in> R"
    proof cases
      case 1
      then show ?thesis by simp
    next
      case 2
      then have "(x, z) \<in> R" using zA Hmin unfolding minimal_element_def by blast
      then show ?thesis by simp
    next
      case 3
      then show ?thesis using Hneq by blast (* contradiction *)
    qed
  qed 
qed

lemma connected_least_min : 
  assumes Hconnected : "connected_on A R"
    and Hasym : "asym_on A R"
    and Hleast : "least_element A R x"
  shows "minimal_element A R x"
  unfolding minimal_element_def
proof 
  show "x \<in> A" using Hleast unfolding least_element_def by blast
next 
  have xA : "x \<in> A" using Hleast unfolding least_element_def by blast
  show "\<forall>z\<in>A. (z, x) \<in> R \<longrightarrow> z = x"
  proof (rule ballI, rule impI)
    fix z assume zA : "z \<in> A" and zRx : "(z, x) \<in> R"
    consider "(x, z) \<in> R" | "(z, x) \<in> R" | "x = z" using Hconnected xA zA unfolding connected_on_def by blast
    then show "z = x"
    proof cases
      case 1
      then show ?thesis using Hasym zRx xA zA unfolding asym_on_def by blast (* contradiction *)
    next
      case 2
      then have "z = x \<or> z \<noteq> x" by blast
      then show ?thesis 
      proof 
        assume "z = x" 
        thus ?thesis by simp
      next 
        assume "z \<noteq> x"
        then have "(x, z) \<in> R" using zA Hleast unfolding least_element_def by blast
        then show ?thesis using Hasym zRx xA zA unfolding asym_on_def by blast (* contradiction *)
      qed 
    next
      case 3
      then show ?thesis by simp
    qed
  qed 
qed

lemma connected_min_least_subset : 
  assumes Hconnected : "connected_on A R"
    and Hmin : "\<forall> B \<subseteq> A . B \<noteq> {} \<longrightarrow> (\<exists> m \<in> B . minimal_element B R m)"
  shows "\<forall> B \<subseteq> A . B \<noteq> {} \<longrightarrow> (\<exists> m \<in> B . least_element B R m)"
  using assms
  apply clarify
  by (smt (verit, best) connected_on_def least_element_def minimal_element_def subset_eq)

lemma connected_least_min_subset : 
  assumes Hconnected : "connected_on A R"
    and Hasym : "asym_on A R"
    and Hleast : "\<forall> B \<subseteq> A . B \<noteq> {} \<longrightarrow> (\<exists> m \<in> B . least_element B R m)"
  shows "\<forall> B \<subseteq> A . B \<noteq> {} \<longrightarrow> (\<exists> m \<in> B . minimal_element B R m)"
  using assms
  apply clarify
  by (meson asym_on_subset connected_least_min connected_on_def subset_iff)

lemma least_connected:
  assumes Hsubset_least: "\<forall>B \<subseteq> A. B \<noteq> {} \<longrightarrow> (\<exists>m \<in> B. least_element B R m)"
  shows "connected_on A R"
  unfolding connected_on_def
proof (intro ballI)
  fix x y
  assume xA: "x \<in> A" and yA: "y \<in> A"
  
  show "(x, y) \<in> R \<or> (y, x) \<in> R \<or> x = y"
  proof (cases "x = y")
    case True
    then show ?thesis by blast
  next
    case False
    \<comment> \<open>key step: use the subset {x, y} \<close>
    let ?B = "{x, y}"
    have "?B \<subseteq> A" using xA yA by blast
    moreover have "?B \<noteq> {}" by blast
    ultimately obtain m where mB: "m \<in> ?B" and is_least: "least_element ?B R m"
      using Hsubset_least by blast

    from mB consider "m = x" | "m = y" by blast
    then show ?thesis
    proof (cases)
      case 1 \<comment> \<open>m = x\<close>
      with is_least have "(x, y) \<in> R"
        unfolding least_element_def using False by auto
      then show ?thesis by blast
    next
      case 2 \<comment> \<open>m = y\<close>
      with is_least have "(y, x) \<in> R"
        unfolding least_element_def using False by blast
      then show ?thesis by blast
    qed
  qed
qed

lemma least_asym_wf : 
  assumes Hsubset_least : "\<forall> B \<subseteq> A . B \<noteq> {} \<longrightarrow> (\<exists> m \<in> B . least_element B R m)"
    and Hasym : "asym_on A R" 
  shows "wf_on A R" 
  using assms 
  by (metis connected_least_min_subset irrefl_on_if_asym_on least_connected min_wf) 

lemma well_order_least : 
  assumes wf : "well_order_on A R"
  shows "\<forall> B \<subseteq> A . B \<noteq> {} \<longrightarrow> (\<exists> m \<in> B . least_element B R m)"
  using assms
  by (metis well_order_iff_wf_connected wf_min connected_min_least_subset)

lemma least_asym_well_order : 
  assumes "R \<subseteq> A \<times> A" 
    and Hsubset_least : "\<forall> B \<subseteq> A . B \<noteq> {} \<longrightarrow> (\<exists> m \<in> B . least_element B R m)"
    and Hasym : "asym_on A R"
  shows "well_order_on A R" 
  using assms 
  by (metis well_order_iff_wf_connected least_asym_wf least_connected)

(* Note this is stronger than what's in the homework *)
theorem least_asym_iff_well_order : 
  "well_order_on A R \<longleftrightarrow> (R \<subseteq> (A \<times> A) \<and> asym_on A R \<and> (\<forall> B \<subseteq> A . B \<noteq> {} \<longrightarrow> (\<exists> m \<in> B . least_element B R m)))"
  by (metis asym_on_iff_irrefl_on_if_trans_on hw3.well_order_on_def least_asym_well_order
      strict_total_order_iff_irrefl_trans_connected well_order_least)

(* Ex 6 *)
definition P_sets :: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a rel \<Rightarrow> bool) \<Rightarrow> ('a rel) set" where 
  "P_sets A P = { R \<in> Pow (A \<times> A). P A R }"

definition closure_system :: "'a set \<Rightarrow> ('a rel) set \<Rightarrow> bool" where 
  "closure_system A Ps = ((A \<times> A) \<in> Ps \<and> (\<forall> S. S \<subseteq> Ps \<and> S \<noteq> {} \<longrightarrow> \<Inter> S \<in> Ps))" 

definition P_closure :: "'a set \<Rightarrow> 'a rel \<Rightarrow> ('a rel) set \<Rightarrow> 'a rel" where 
  "P_closure A R Ps = \<Inter> { P \<in> Ps . R \<subseteq> P }"

theorem P_closure_in_closure_system : 
  assumes HR: "R \<subseteq> A \<times> A"
      and HCl: "closure_system A (P_sets A P)"
  shows "P_closure A R (P_sets A P) \<in> P_sets A P"
  unfolding P_closure_def
proof -
  let ?Ps = "P_sets A P"
  let ?S = "{Pa \<in> ?Ps. R \<subseteq> Pa}"
  
  \<comment> \<open> Step 1: A \<times> A is in P_sets A P (top element) \<close>
  from HCl have HAA: "(A \<times> A) \<in> ?Ps" 
    unfolding closure_system_def by blast
  
  \<comment> \<open> Step 2: A \<times> A contains R, so it's in ?S \<close>
  from HAA HR have "(A \<times> A) \<in> ?S" by blast
  hence HneS: "?S \<noteq> {}" by blast
  
  \<comment> \<open> Step 3: ?S \<subseteq> ?Ps \<close>
  have HsubS: "?S \<subseteq> ?Ps" by blast
  
  \<comment> \<open> Step 4: By closure system property, \<Inter> ?S \<in> ?Ps \<close>
  from HCl have "\<forall>S. S \<subseteq> ?Ps \<and> S \<noteq> {} \<longrightarrow> \<Inter> S \<in> ?Ps"
    unfolding closure_system_def by blast

  \<comment> \<open> key point: instantiate S with ?S \<close>
  with HsubS HneS have "\<Inter> ?S \<in> ?Ps" by blast
  
  thus "\<Inter> {Pa \<in> ?Ps. R \<subseteq> Pa} \<in> ?Ps" by blast
qed

(* Ex 6.1 *)
lemma refl_on_prod : 
  "refl_on A (A \<times> A)"
  unfolding refl_on_def 
  by auto

theorem refl_on_closure_system : 
  shows "closure_system A (P_sets A refl_on)" 
  unfolding closure_system_def P_sets_def 
proof 
  have "refl_on A (A \<times> A)" using refl_on_prod by blast
  thus "A \<times> A \<in> {R \<in> Pow (A \<times> A). refl_on A R}" by blast
next 
  show "\<forall>S. S \<subseteq> {R \<in> Pow (A \<times> A). refl_on A R} \<and> S \<noteq> {} \<longrightarrow>
            \<Inter> S \<in> {R \<in> Pow (A \<times> A). refl_on A R}"
  proof (intro allI impI)
    fix S assume H: "S \<subseteq> {R \<in> Pow (A \<times> A). refl_on A R} \<and> S \<noteq> {}"
    hence HS: "S \<subseteq> {R \<in> Pow (A \<times> A). refl_on A R}" and HnS: "S \<noteq> {}" by auto
    have "refl_on A (\<Inter> S)" 
      unfolding refl_on_def 
    proof (intro ballI InterI)
      fix x X assume xA: "x \<in> A" and XS: "X \<in> S" 
      hence "refl_on A X" using HS by blast
      thus "(x, x) \<in> X" unfolding refl_on_def using xA by blast
    qed
    thus "\<Inter> S \<in> {R \<in> Pow (A \<times> A). refl_on A R}" using H by blast
  qed
qed

(* Ex 6.2 *) 
lemma not_irrefl_on_prod : 
  assumes "A \<noteq> {}"
  shows "\<not> irrefl_on A (A \<times> A)"
  unfolding irrefl_on_def 
proof 
  assume H: "\<forall>x\<in>A. (x, x) \<notin> A \<times> A"
  from assms obtain a where aA: "a \<in> A" by blast
  hence "(a, a) \<in> A \<times> A" by simp
  with H aA show False by blast
qed

theorem irrefl_on_closure_system : 
  assumes HA : "A \<noteq> {}"
  shows "\<not> closure_system A (P_sets A irrefl_on)" 
  unfolding closure_system_def P_sets_def 
proof
  assume "A \<times> A \<in> {R \<in> Pow (A \<times> A). irrefl_on A R} \<and>
          (\<forall>S. S \<subseteq> {R \<in> Pow (A \<times> A). irrefl_on A R} \<and> S \<noteq> {} \<longrightarrow>
               \<Inter> S \<in> {R \<in> Pow (A \<times> A). irrefl_on A R})"
  hence "A \<times> A \<in> {R \<in> Pow (A \<times> A). irrefl_on A R}" by blast 
  hence "irrefl_on A (A \<times> A)" by blast
  thus False using not_irrefl_on_prod HA by metis
qed

(* Ex 6.3 *) 
lemma sym_on_prod : 
  "sym_on A (A \<times> A)"
  unfolding sym_on_def 
  by auto

theorem sym_on_closure_system : 
  shows "closure_system A (P_sets A sym_on)" 
  unfolding closure_system_def P_sets_def 
proof
  have "sym_on A (A \<times> A)" using sym_on_prod by blast  
  thus "A \<times> A \<in> {R \<in> Pow (A \<times> A). sym_on A R}" by blast
next 
  show "\<forall>S. S \<subseteq> {R \<in> Pow (A \<times> A). sym_on A R} \<and> S \<noteq> {} \<longrightarrow>
            \<Inter> S \<in> {R \<in> Pow (A \<times> A). sym_on A R}"
  proof (intro allI impI)
    fix S assume H: "S \<subseteq> {R \<in> Pow (A \<times> A). sym_on A R} \<and> S \<noteq> {}"
    hence HS: "S \<subseteq> {R \<in> Pow (A \<times> A). sym_on A R}" and HnS: "S \<noteq> {}" by auto
    have "sym_on A (\<Inter> S)" 
      unfolding sym_on_def 
    proof (intro ballI ballI impI InterI)
      fix x y X assume xA: "x \<in> A" and yA: "y \<in> A"  and xyS : "(x, y) \<in> \<Inter> S" and XS : "X \<in> S"
      hence HX : "sym_on A X" using HS by blast
      have "(x, y) \<in> X" using xyS XS by blast
      thus "(y, x) \<in> X" using yA xA HX unfolding sym_on_def by blast
    qed
    thus "\<Inter> S \<in> {R \<in> Pow (A \<times> A). sym_on A R}" using H by blast
  qed
qed    

(* Ex 6.4 *) 
lemma not_asym_on_prod : 
  assumes "A \<noteq> {}"
  shows "\<not> asym_on A (A \<times> A)"
  unfolding asym_on_def 
proof 
  assume H: "\<forall>x\<in>A. \<forall>y\<in>A. (x, y) \<in> A \<times> A \<longrightarrow> (y, x) \<notin> A \<times> A"
  from assms obtain a where aA: "a \<in> A" by blast
  hence "(a, a) \<in> A \<times> A" by simp
  with H aA show False by blast
qed

theorem asym_on_closure_system : 
  assumes HA : "A \<noteq> {}"
  shows "\<not> closure_system A (P_sets A asym_on)" 
  unfolding closure_system_def P_sets_def 
proof
  assume "A \<times> A \<in> {R \<in> Pow (A \<times> A). asym_on A R} \<and>
          (\<forall>S. S \<subseteq> {R \<in> Pow (A \<times> A). asym_on A R} \<and> S \<noteq> {} \<longrightarrow>
               \<Inter> S \<in> {R \<in> Pow (A \<times> A). asym_on A R})"
  hence "A \<times> A \<in> {R \<in> Pow (A \<times> A). asym_on A R}" by blast 
  hence "asym_on A (A \<times> A)" by blast
  thus False using not_asym_on_prod HA by metis
qed

(* Ex 6.5 *) 
lemma not_antisym_on_prod : 
  assumes "A \<noteq> {}"
    and "\<forall> x . A \<noteq> {x}"
  shows "\<not> antisym_on A (A \<times> A)"
  unfolding antisym_on_def 
proof 
  assume H: "\<forall>x\<in>A. \<forall>y\<in>A. (x, y) \<in> A \<times> A \<longrightarrow> (y, x) \<in> A \<times> A \<longrightarrow> x = y"
  from assms(1) obtain a where aA: "a \<in> A" by blast
  from assms(2) have "A \<noteq> {a}" by blast
  with aA obtain b where bA: "b \<in> A" and neq: "b \<noteq> a" by blast
  hence "a = b" using aA H by simp
  with neq show False by blast
qed

theorem antisym_on_closure_system : 
  assumes HA0 : "A \<noteq> {}"
    and HA1 : "\<forall> x . A \<noteq> {x}"
  shows "\<not> closure_system A (P_sets A antisym_on)" 
  unfolding closure_system_def P_sets_def 
proof
  assume "A \<times> A \<in> {R \<in> Pow (A \<times> A). antisym_on A R} \<and>
          (\<forall>S. S \<subseteq> {R \<in> Pow (A \<times> A). antisym_on A R} \<and> S \<noteq> {} \<longrightarrow>
               \<Inter> S \<in> {R \<in> Pow (A \<times> A). antisym_on A R})"
  hence "A \<times> A \<in> {R \<in> Pow (A \<times> A). antisym_on A R}" by blast 
  hence "antisym_on A (A \<times> A)" by blast
  thus False using not_antisym_on_prod HA0 HA1 by metis
qed

(* Ex 6.6 *) 
lemma trans_on_prod : 
  "trans_on A (A \<times> A)"
  unfolding trans_on_def 
  by auto

theorem trans_on_closure_system : 
  shows "closure_system A (P_sets A trans_on)" 
  unfolding closure_system_def P_sets_def 
proof
  have "trans_on A (A \<times> A)" using trans_on_prod by blast  
  thus "A \<times> A \<in> {R \<in> Pow (A \<times> A). trans_on A R}" by blast
next 
  show "\<forall>S. S \<subseteq> {R \<in> Pow (A \<times> A). trans_on A R} \<and> S \<noteq> {} \<longrightarrow>
            \<Inter> S \<in> {R \<in> Pow (A \<times> A). trans_on A R}"
  proof (intro allI impI)
    fix S assume H: "S \<subseteq> {R \<in> Pow (A \<times> A). trans_on A R} \<and> S \<noteq> {}"
    hence HS: "S \<subseteq> {R \<in> Pow (A \<times> A). trans_on A R}" and HnS: "S \<noteq> {}" by auto
    have "trans_on A (\<Inter> S)" 
      unfolding trans_on_def 
    proof (intro ballI ballI ballI impI impI InterI)
      fix x y z X 
      assume xA: "x \<in> A" and yA: "y \<in> A" and zA : "z \<in> A" 
      and xyS : "(x, y) \<in> \<Inter> S" and yzS : "(y, z) \<in> \<Inter> S" and XS : "X \<in> S"
      hence HX : "trans_on A X" using HS by blast
      have xyX : "(x, y) \<in> X" using xyS XS by blast
      have yzX : "(y, z) \<in> X" using yzS XS by blast
      thus "(x, z) \<in> X" using yA xA zA HX xyX yzX unfolding trans_on_def by blast
    qed
    thus "\<Inter> S \<in> {R \<in> Pow (A \<times> A). trans_on A R}" using H by blast
  qed
qed    

(* Ex 9 *)
definition infinite_decreasing_sequence :: "'A rel \<Rightarrow> (nat \<Rightarrow> 'A) \<Rightarrow> bool" where 
  "infinite_decreasing_sequence R s = (\<forall> i . (s (Suc i), s i) \<in> R)"

lemma wf_no_infinite_decreasing_sequence : 
  assumes HS : "R \<subseteq> A \<times> A" 
    and Hwf : "wf_on A R"
  shows "\<not> (\<exists> (s :: nat \<Rightarrow> 'A) . infinite_decreasing_sequence R s)"
  (* Don't unfolding infinite_decreasing_sequence_def at this point ---> obtain will fail! *)
proof 
  assume "\<exists> (s :: nat \<Rightarrow> 'A) . infinite_decreasing_sequence R s"
  then obtain s where Hd : "infinite_decreasing_sequence R s" by blast
  then show False 
  proof - 
    let ?B = "range s" \<comment> \<open> key point \<close>
    have HB : "?B \<subseteq> A" using Hd HS unfolding infinite_decreasing_sequence_def by blast
    have "?B \<noteq> {}" using Hd HS HB unfolding infinite_decreasing_sequence_def by blast
    hence "(\<exists> m \<in> ?B . minimal_element ?B R m)" using HB Hwf wf_min by blast
    then obtain m where Hm : "minimal_element ?B R m" by blast 
    then obtain i where "m = s i" using Hm unfolding minimal_element_def by blast
    hence HC : "(s (Suc i), m) \<in> R" using Hd unfolding infinite_decreasing_sequence_def by blast
    hence "s (Suc i) = m" using Hm unfolding minimal_element_def by blast
    thus False using wf_irrefl Hwf wf_on_wf HC HS by metis
  qed
qed

lemma no_infinite_descreasing_sequence_irrefl : 
  assumes Hno_seq : "\<not> (\<exists> (s :: nat \<Rightarrow> 'A) . infinite_decreasing_sequence R s)"
  shows "irrefl_on A R"
proof (rule ccontr)
  assume "\<not> irrefl_on A R"
  \<comment> \<open> key step: construct an infinite decreasing sequence from x \<close>
  hence "\<exists> x \<in> A . (x, x) \<in> R" unfolding irrefl_on_def by blast
  then obtain x where xRx : "(x, x) \<in> R" by blast 
  hence "infinite_decreasing_sequence R (\<lambda> i . x)"
    unfolding infinite_decreasing_sequence_def by blast
  with Hno_seq show False by blast
qed

lemma refl_not_irrefl : 
  "A \<noteq> {} \<Longrightarrow> 
   refl_on A R \<Longrightarrow> 
   \<not> irrefl_on A R"
  by (simp add: irrefl_on_def refl_on_def)

lemma refl_infinite_descreasing_sequence : 
  assumes HA : "A \<noteq> {}" 
    and Hrefl : "refl_on A R"
  shows "(\<exists> (s :: nat \<Rightarrow> 'A) . infinite_decreasing_sequence R s)"
  by (metis no_infinite_descreasing_sequence_irrefl Hrefl HA refl_not_irrefl)

lemma no_infinite_decreasing_sequence_wf : 
  assumes HS : "R \<subseteq> A \<times> A" 
  and Hno_seq : "\<not> (\<exists> (s :: nat \<Rightarrow> 'A) . infinite_decreasing_sequence R s)"
  shows "wf_on A R"
proof (rule contrapos_np [OF Hno_seq])
  assume "\<not> wf_on A R"
  \<comment> \<open> key step: reasoning with the minimal element \<close>
  hence "\<not> ((\<forall> B \<subseteq> A . B \<noteq> {} \<longrightarrow> (\<exists> m \<in> B . minimal_element B R m)) \<and> irrefl_on A R)" using min_wf by blast
  hence "(\<exists> B \<subseteq> A . B \<noteq> {} \<and> (\<forall> m \<in> B . \<not> minimal_element B R m)) \<or> (\<not> irrefl_on A R)" by blast
  thus "\<exists>s. infinite_decreasing_sequence R s"
  proof 
    assume "\<exists> B \<subseteq> A . B \<noteq> {} \<and> (\<forall> m \<in> B . \<not>  minimal_element B R m)"
    then obtain B where HB : "B \<subseteq> A" and HnB : "B \<noteq> {}" and Hnm : "(\<forall> m \<in> B . \<not> minimal_element B R m)" by blast 
    hence "\<exists> x \<in> B . \<not> minimal_element B R x" by blast
    then obtain x where xB : "x \<in> B" and Hnx : "\<not> minimal_element B R x" by blast 
    hence "\<forall> y \<in> B . \<exists> z \<in> B . (z, y) \<in> R" using Hnm unfolding minimal_element_def by blast
    hence "\<exists>s. \<forall>n. s n \<in> B \<and> (s (Suc n), s n) \<in> R"
      \<comment> \<open> key point: use [dependent_nat_choice] to construct an infinite decreasing sequence \<close>
      using dependent_nat_choice[where P = "\<lambda> n x. x \<in> B" and Q = "\<lambda>n x y. (y, x) \<in> R"] xB by blast
    then obtain s where Hs : "\<forall>n. s n \<in> B \<and> (s (Suc n), s n) \<in> R" by blast
    hence "infinite_decreasing_sequence R s" 
      unfolding infinite_decreasing_sequence_def by blast
    thus "\<exists>s. infinite_decreasing_sequence R s" by blast
  next 
    assume "\<not> irrefl_on A R"
    show ?thesis using \<open>\<not> irrefl_on A R\<close> no_infinite_descreasing_sequence_irrefl by blast
  qed
qed

theorem wf_iff_no_infinite_decreasing_sequence : 
 "R \<subseteq> A \<times> A \<Longrightarrow>
  (wf_on A R \<longleftrightarrow> \<not> (\<exists> s . infinite_decreasing_sequence R s))"
  by (metis no_infinite_decreasing_sequence_wf wf_no_infinite_decreasing_sequence)

corollary wf_on_irrefl : 
  "R \<subseteq> A \<times> A \<Longrightarrow> 
   (wf_on A R \<longrightarrow> irrefl_on A R)" 
  by (metis wf_no_infinite_decreasing_sequence no_infinite_descreasing_sequence_irrefl)

lemma no_infinite_descreasing_sequence_asym : 
  assumes Hno_seq : "\<not> (\<exists> (s :: nat \<Rightarrow> 'A) . infinite_decreasing_sequence R s)"
  shows "asym_on A R"
proof (rule ccontr)
  assume "\<not> asym_on A R"
  \<comment> \<open> key step: construct an infinite decreasing sequence from x and y \<close>
  hence "\<exists> x \<in> A. \<exists> y \<in> A. (x, y) \<in> R \<and> (y, x) \<in> R" unfolding asym_on_def by blast
  then obtain x and y where xRy : "(x, y) \<in> R" and yRx : "(y, x) \<in> R" by blast 
  let ?s = "\<lambda> i . if even i then x else y"
  have "infinite_decreasing_sequence R ?s"
    unfolding infinite_decreasing_sequence_def 
  proof (intro allI)
    fix i 
    show "(?s (Suc i), ?s i) \<in> R" 
    proof (cases "even i")
      case True
      then show ?thesis using yRx by force
    next
      case False
      then show ?thesis using xRy by force
    qed
  qed

  with Hno_seq show False by blast
qed 

corollary wf_on_asym : 
  "R \<subseteq> A \<times> A \<Longrightarrow> 
   (wf_on A R \<longrightarrow> asym_on A R)" 
  by (metis wf_no_infinite_decreasing_sequence no_infinite_descreasing_sequence_asym)

(* Ex 10 *) 
(* Note this is slightly different from [wf_trancl] *)
lemma wf_trancl_wf:
  assumes HS : "R \<subseteq> A \<times> A" 
    and Hwf : "wf_on A R"
  shows "wf_on A (R\<^sup>+)"
  unfolding wf_on_def 
proof (intro allI impI)
  fix P assume IHRp : "\<forall>z\<in>A. (\<forall>y\<in>A. (y, z) \<in> R\<^sup>+ \<longrightarrow> P y) \<longrightarrow> P z"
  from Hwf have HwfR : "\<forall> Q . (\<forall> x \<in> A. (\<forall> y \<in> A. (y, x) \<in> R \<longrightarrow> Q y) \<longrightarrow> Q x) \<longrightarrow> (\<forall> x \<in> A. Q x)" unfolding wf_on_def by blast
  
  \<comment> \<open> key point: instantiate P with the right IH \<close>
  let ?P = "\<lambda> z . (\<forall>w\<in>A. (w, z) \<in> R\<^sup>+ \<longrightarrow> P w)"
  have Rind : "(\<forall> a \<in> A. (\<forall> b \<in> A. (b, a) \<in> R \<longrightarrow> ?P b) \<longrightarrow> ?P a) \<longrightarrow> (\<forall> a \<in> A. ?P a)" 
    using HwfR [rule_format, where Q = "?P"] by blast

  (*  \<forall>a\<in>A. 
          (\<forall>b\<in>A. (b, a) \<in> R \<longrightarrow> (\<forall>w\<in>A. (w, b) \<in> R\<^sup>+ \<longrightarrow> P w)) \<longrightarrow>
          (\<forall>w\<in>A. (w, a) \<in> R\<^sup>+ \<longrightarrow> P w) *)
  have "(\<forall> a \<in> A. (\<forall> b \<in> A. (b, a) \<in> R \<longrightarrow> ?P b) \<longrightarrow> ?P a)"
  proof (intro ballI impI impI impI)
    fix a w 
    assume IH : "\<forall>b\<in>A. (b, a) \<in> R \<longrightarrow> (\<forall>w\<in>A. (w, b) \<in> R\<^sup>+ \<longrightarrow> P w)" 
      and aA : "a \<in> A" and wA : "w \<in> A" and wRRa : "(w, a) \<in> R\<^sup>+"
    from wRRa show "P w" 
    proof (cases rule: tranclE)
      case base
      then show ?thesis 
      using IH r_into_trancl wA IHRp by fastforce
    next
      case (step c)
      then show ?thesis using IH wA HS by blast
    qed
  qed

  (* \<forall>a\<in>A. \<forall>w\<in>A. (w, a) \<in> R\<^sup>+ \<longrightarrow> P w *)
  hence "\<forall> a \<in> A. ?P a" using Rind by blast 
  thus "\<forall> a \<in> A . P a" using IHRp by blast
qed

lemma trancl_wf_wf:
  assumes HS : "R \<subseteq> A \<times> A" 
    and Hwf : "wf_on A (R\<^sup>+)"
  shows "wf_on A R"
proof - 
  have HRR : "(\<forall> B \<subseteq> A . B \<noteq> {} \<longrightarrow> (\<exists> m \<in> B . minimal_element B (R\<^sup>+) m))" using Hwf HS wf_min by blast 
  have HR : "(\<forall> B \<subseteq> A . B \<noteq> {} \<longrightarrow> (\<exists> m \<in> B . minimal_element B R m))" 
  proof (intro allI impI)
    fix B assume HBA : "B \<subseteq> A" and HB : "B \<noteq> {}" 
    with HRR obtain m where HmRR : "minimal_element B (R\<^sup>+) m" by blast
    hence "minimal_element B R m" using r_into_trancl unfolding minimal_element_def by blast 
    thus "\<exists>m\<in>B. minimal_element B R m" unfolding minimal_element_def by blast
  qed

  have "irrefl_on A (R\<^sup>+)" using irrefl_on_def wf_on_wf Hwf HS wf_irrefl
    by (metis trancl_subset_Sigma)
  hence "irrefl_on A R" by (meson HS Hwf irrefl_on_def r_into_trancl)  
  thus ?thesis using min_wf HS HR by blast
qed

theorem wf_iff_transcl_wf : 
  "R \<subseteq> A \<times> A \<Longrightarrow> 
   (wf_on A (R\<^sup>+) \<longleftrightarrow> wf_on A R)"
  by (metis trancl_wf_wf wf_trancl_wf)

(* Ex 11 *) 
definition lex_order :: "'A rel \<Rightarrow> 'A rel \<Rightarrow> ('A \<times> 'A) rel" where 
  "lex_order Ra Rb = {((a, b), (c, d)). (a, c) \<in> Ra \<or> (a = c \<and> (b, d) \<in> Rb) }"

(* Mostly generated by Claude Opus 4.5 with a few rounds of interactions! *)
lemma wf_lex_order : 
  assumes HSa : "Ra \<subseteq> A \<times> A"
    and HSb : "Rb \<subseteq> A \<times> A"
    and HS  : "(lex_order Ra Rb) \<subseteq> (A \<times> A) \<times> (A \<times> A)"
    and HRa : "wf_on A Ra" 
    and HRb : "wf_on A Rb" 
  shows "wf_on (A \<times> A) (lex_order Ra Rb)"
  unfolding wf_on_def 
proof (intro allI impI)
  fix P assume IH: "\<forall>x\<in>A \<times> A. (\<forall>y\<in>A \<times> A. (y, x) \<in> lex_order Ra Rb \<longrightarrow> P y) \<longrightarrow> P x"
  
  \<comment> \<open> We prove \<forall>x\<in>A \<times> A. P x using nested well-founded induction \<close>
  \<comment> \<open> Outer induction on first component (wrt Ra), inner on second (wrt Rb) \<close>
  
  \<comment> \<open> Key: define the outer induction predicate \<close>
  define Qa where "Qa \<equiv> \<lambda>a. \<forall>b\<in>A. P (a, b)"
  
  have "\<forall>a\<in>A. Qa a"
    using HRa unfolding wf_on_def
  proof (rule spec[where x="Qa", THEN mp])
    show "(\<forall>a\<in>A. (\<forall>a'\<in>A. (a', a) \<in> Ra \<longrightarrow> Qa a') \<longrightarrow> Qa a)"
    proof (intro ballI impI)
      fix a assume aA: "a \<in> A" and IHa: "\<forall>a'\<in>A. (a', a) \<in> Ra \<longrightarrow> Qa a'"
      \<comment> \<open> Need to show: Qa a = (\<forall>b\<in>A. P (a, b)) \<close>
      \<comment> \<open> Use inner induction on b wrt Rb \<close>
      show "Qa a" unfolding Qa_def
        using HRb unfolding wf_on_def
      proof (rule spec[where x="\<lambda>b. P (a, b)", THEN mp])
        show "\<forall>b\<in>A. (\<forall>b'\<in>A. (b', b) \<in> Rb \<longrightarrow> P (a, b')) \<longrightarrow> P (a, b)"
        proof (intro ballI impI)
          fix b assume bA: "b \<in> A" and IHb: "\<forall>b'\<in>A. (b', b) \<in> Rb \<longrightarrow> P (a, b')"
          \<comment> \<open> Need to show: P (a, b) \<close>
          \<comment> \<open> Use the main IH: show all lex-predecessors satisfy P \<close>
          
          have abAA: "(a, b) \<in> A \<times> A" using aA bA by blast
          
          \<comment> \<open> Show all lex-predecessors satisfy P \<close>
          have Hpred: "\<forall>y\<in>A \<times> A. (y, (a, b)) \<in> lex_order Ra Rb \<longrightarrow> P y"
          proof (intro ballI impI)
            fix y assume yAA: "y \<in> A \<times> A" and Hyx: "(y, (a, b)) \<in> lex_order Ra Rb"
            obtain a' b' where y_eq: "y = (a', b')" using prod.exhaust by blast
            from yAA y_eq have a'A: "a' \<in> A" and b'A: "b' \<in> A" by auto
            from Hyx y_eq have "(a', a) \<in> Ra \<or> (a' = a \<and> (b', b) \<in> Rb)"
              unfolding lex_order_def by auto
            thus "P y"
            proof
              assume "(a', a) \<in> Ra"
              \<comment> \<open> First component decreases: use outer IH \<close>
              hence "Qa a'" using IHa a'A by blast
              thus "P y" using y_eq b'A unfolding Qa_def by blast
            next
              assume "a' = a \<and> (b', b) \<in> Rb"
              \<comment> \<open> First component same, second decreases: use inner IH \<close>
              thus "P y" using y_eq IHb b'A by blast
            qed
          qed
          
          \<comment> \<open> Apply the main IH \<close>
          from IH abAA Hpred show "P (a, b)" by blast
        qed
      qed
    qed
  qed
  
  thus "\<forall>x\<in>A \<times> A. P x" unfolding Qa_def by auto
qed 

end