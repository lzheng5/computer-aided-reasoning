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
      fix x assume xA : "x \<in> A" and Hpred : "(\<forall> y \<in> A . (y, x) \<in> R \<longrightarrow> y \<notin> B)"
      show "x \<notin> B"
      proof (* avoid (rule ccontr) *)
        assume xB : "x \<in> B"

        have "minimal_element B R x"
          unfolding minimal_element_def using xA xB Hpred HS by blast

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

(* Ex 9 *)
definition infinite_decreasing_sequence :: "'A rel \<Rightarrow> (nat \<Rightarrow> 'A) \<Rightarrow> bool" where 
  "infinite_decreasing_sequence R s = (\<forall> i . (s (i + 1), s i) \<in> R)"

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
    hence HC : "(s (i + 1), m) \<in> R" using Hd unfolding infinite_decreasing_sequence_def by blast
    hence "s (i + 1) = m" using Hm unfolding minimal_element_def by blast
    thus False using wf_irrefl Hwf wf_on_wf HC HS by metis
  qed
qed

end