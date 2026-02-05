theory hw3 
imports Main
begin

abbreviation equiv_class :: "'A ⇒ 'A rel ⇒ 'A set" ("[_]⇩_" [1000, 999] 999) where 
 "equiv_class x E ≡ E `` {x}"

lemma "[x]⇩R = {y. (x, y) ∈ R}"
  by (simp add: Image_def)

(* 3.1 *)
theorem equiv_class_dec :                 
  "equiv A R ⟹ ∀ x y. ([x]⇩R = [y]⇩R) ∨ (disjnt ([x]⇩R) ([y]⇩R))"
  apply clarify
  by (simp add: disjnt_equiv_class equiv_class_eq_iff)

(* 3.2.a *) 
definition sym_part :: "'A rel ⇒ 'A rel" where 
  "sym_part R = {(x, y) | x y . (x, y) ∈ R ∧ (y, x) ∈ R}"

theorem preorder_induce_equiv : 
  "preorder_on A R ⟹ equiv A (sym_part R)"
  unfolding sym_part_def preorder_on_def equiv_def
  apply clarify
  apply (auto; simp add: refl_on_def sym_on_def trans_on_def) 
  by blast

(* 3.2.b *) 
definition quotient_order :: "'A rel ⇒ ('A set × 'A set) set" where
  "quotient_order R = {(X, Y). ∃x y. X = [x]⇩R ∧ Y = [y]⇩R ∧ (x, y) ∈ R}"

theorem quotient_poset : 
  "preorder_on A R ⟹ 
   E = (sym_part R) ⟹ 
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
definition total_on :: "'a set ⇒ 'a rel ⇒ bool" where
  "total_on A r ⟷ (∀x∈A. ∀y∈A. (x, y) ∈ r ∨ (y, x) ∈ r)"

theorem total_union_inverse : 
  "total_on A R ⟹ 
   R ⊆ A × A ⟹ 
   R ∪ R¯ = A × A"
  unfolding total_on_def 
  by auto

(* 4.2 *) 
definition strict_part :: "'A rel ⇒ 'A rel" where 
  "strict_part R = { (x, y) | x y . (x, y) ∈ R ∧ x ≠ y }"

definition strict_partial_order_on :: "'A set ⇒ 'A rel ⇒ bool" where 
  "strict_partial_order_on A R = (∃ P . partial_order_on A P ∧ R = strict_part P)"

definition "refl_part A R ≡ R ∪ (Id_on A)"

lemma refl_part_domain : 
  "R ⊆ A × A ⟹ (a, b) ∈ refl_part A R ⟹ (a ∈ A ∧ b ∈ A)"
  unfolding refl_part_def Id_on_def
  by blast

lemma refl_part_member : 
  "(a, b) ∈ R ⟹ (a, b) ∈ refl_part A R"
  unfolding refl_part_def Id_on_def 
  by blast

lemma refl_part_member_inv : 
 "(a, b) ∈ refl_part A R ⟹ a ≠ b ⟹ (a, b) ∈ R"
  unfolding refl_part_def Id_on_def
  by blast

lemma refl_refl_part : 
  "refl_on A (refl_part A R)"
  unfolding refl_part_def Id_on_def refl_on_def
  by auto 

lemma trans_refl_part : 
  "R ⊆ A × A ⟹ trans_on A R ⟹ trans (refl_part A R)"
  unfolding refl_part_def trans_on_def
  by blast 

lemma antisym_refl_part : 
  "R ⊆ A × A ⟹ irrefl_on A R ⟹ trans_on A R ⟹ antisym (refl_part A R)"
  unfolding trans_on_def antisym_on_def refl_part_def Id_on_def irrefl_on_def
  apply clarify
  apply (erule UnE, blast)
  by (erule UnE; blast)

theorem strict_partial_order_iff_irrefl_trans : 
  "R ⊆ A × A ⟹ 
   (strict_partial_order_on A R ⟷ (irrefl_on A R ∧ trans_on A R))"
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
  "strict_partial_order_on A R ⟹ 
   partial_order_on A (R ∪ (Id_on A))"
  unfolding strict_partial_order_on_def partial_order_on_def strict_part_def Id_on_def
  apply clarify
  apply auto
    apply (simp add: refl_on_def preorder_on_def trans_on_def, auto)
  by (simp add: preorder_on_def antisym_on_def trans_on_def)

(* 4.4 *) 
lemma preorder_irrefl_trans : 
  "preorder_on A R ⟹
   P = R - R¯ ⟹  
   (irrefl_on A P ∧ trans_on A P)"
  unfolding preorder_on_def trans_on_def irrefl_on_def
  by auto

lemma preorder_subset : 
  "preorder_on A R ⟹ 
   R ⊆ (A × A)" 
  unfolding preorder_on_def 
  by blast

theorem preorder_induce_strict_partial_order : 
  "preorder_on A R ⟹ 
   strict_partial_order_on A (R - R¯)"
  using preorder_irrefl_trans strict_partial_order_iff_irrefl_trans
  by (smt (verit, best) Diff_subset preorder_subset subset_trans)

(* 4.5 *) 
definition "total_order_on A R ≡ partial_order_on A R ∧ total_on A R"

definition strict_total_order_on :: "'A set ⇒ 'A rel ⇒ bool" where 
  "strict_total_order_on A R ⟷ (∃ P . total_order_on A P ∧ R = strict_part P)"

lemma partial_order_subset : 
  "partial_order_on A R ⟹ 
   R ⊆ (A × A)" 
  using partial_order_on_def preorder_subset 
  by blast

lemma strict_partial_order_subset : 
  "strict_partial_order_on A R ⟹ 
   R ⊆ (A × A)" 
  unfolding strict_partial_order_on_def 
  apply clarify 
  by (metis UnCI partial_order_onD(4) refl_part_def refl_part_domain
      strict_partial_order_induce_partial_order
      strict_partial_order_on_def)

lemma strict_total_order_strict_partial_order : 
  "strict_total_order_on A R ⟹ strict_partial_order_on A R"
  unfolding strict_total_order_on_def strict_partial_order_on_def total_order_on_def partial_order_on_def
  by auto

lemma strict_total_order_subset : 
  "strict_total_order_on A R ⟹ 
   R ⊆ (A × A)" 
  by (metis strict_total_order_strict_partial_order strict_partial_order_subset)

definition connected_on :: "'a set ⇒ 'a rel ⇒ bool" where
  "connected_on A r ⟷ (∀x∈A. ∀y∈A. (x, y) ∈ r ∨ (y, x) ∈ r ∨ x = y)"

lemma strict_total_order_connected : 
  "strict_total_order_on A R ⟹ connected_on A R" 
  unfolding strict_total_order_on_def connected_on_def total_order_on_def total_on_def strict_part_def
  by auto

lemma strict_total_order_irrefl_trans_connected : 
  "strict_total_order_on A R ⟹ (irrefl_on A R ∧ trans_on A R ∧ connected_on A R)"
  using strict_total_order_connected strict_total_order_strict_partial_order strict_partial_order_iff_irrefl_trans
  by (metis le_sup_iff partial_order_onD(4)
      strict_partial_order_induce_partial_order) 

lemma total_refl_part : 
  "connected_on A R ⟹ hw3.total_on A (refl_part A R)"
  unfolding refl_part_def total_on_def connected_on_def
  by blast

lemma strict_refl_part_member : 
  "R ⊆ A × A ⟹ (a, b) ∈ R ⟹ irrefl_on A R ⟹ (a, b) ∈ strict_part (refl_part A R)"
  unfolding refl_part_def strict_part_def Id_on_def irrefl_on_def 
  by blast
  
lemma strict_refl_part_member_inv : 
  "(a, b) ∈ strict_part (refl_part A R) ⟹ (a, b) ∈ R"
  unfolding refl_part_def strict_part_def Id_on_def irrefl_on_def 
  by blast
 
lemma irrefl_trans_connected_strict_total_order : 
  "(R ⊆ A × A ∧ irrefl_on A R ∧ trans_on A R ∧ connected_on A R) ⟹ strict_total_order_on A R"
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
  "strict_total_order_on A R ⟷ (R ⊆ A × A ∧ irrefl_on A R ∧ trans_on A R ∧ connected_on A R)"
  using strict_total_order_subset strict_total_order_irrefl_trans_connected irrefl_trans_connected_strict_total_order
  by metis

(* 4.6 *)
(* Have to redefine [well_order_on] *) 
definition well_order_on :: "'A set ⇒ 'A rel ⇒ bool" where 
  "well_order_on A R ⟷ strict_total_order_on A R ∧ wf_on A R"

lemma well_order_wf_connected : 
  "well_order_on A R ⟹ wf_on A R ∧ connected_on A R" 
  unfolding well_order_on_def 
  by (metis strict_total_order_connected)

lemma wf_on_wf : 
  "R ⊆ (A × A) ⟹ 
   wf_on A R ⟹ 
   wf R"
  unfolding wf_on_def wf_def 
  by (metis UNIV_I mem_Sigma_iff subset_eq)

(* [TODO] The following proofs rely on wf_trancl, wf_irrefl, wf_asym *) 
(* Reorder the following lemmas [wf_trancl_wf], [wf_on_irrefl], [wf_on_asym] *) 

lemma wf_no_3_cycles : 
  "wf R ⟹ (x, y) ∈ R ⟹ (y, z) ∈ R ⟹ (z, x) ∈ R ⟹ False"
  apply (drule wf_trancl)
  apply (drule r_into_trancl)
  apply (drule r_into_trancl)
  apply (drule r_into_trancl)
  by (metis trancl_trans wf_asym)

lemma wf_connected_trans : 
  "R ⊆ (A × A) ⟹ 
   wf_on A R ⟹ 
   connected_on A R ⟹ 
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
  "R ⊆ (A × A) ∧ wf_on A R ∧ connected_on A R ⟹ well_order_on A R" 
  unfolding well_order_on_def 
  by (metis irrefl_on_def irrefl_trans_connected_strict_total_order
      wf_connected_trans wf_irrefl wf_on_wf)

theorem well_order_iff_wf_connected : 
  "well_order_on A R ⟷ (R ⊆ (A × A) ∧ wf_on A R ∧ connected_on A R)" 
  by (metis hw3.well_order_on_def strict_total_order_subset
      well_order_wf_connected wf_connected_well_order)

(* 5.1 *) 
definition minimal_element :: "'A set ⇒ 'A rel ⇒ 'A ⇒ bool" where 
  "minimal_element A R m ⟷ (m ∈ A ∧ (∀ x ∈ A . (x, m) ∈ R ⟶ x = m))"

lemma min_wf : 
  assumes Hsubset_min : "∀ B ⊆ A . B ≠ {} ⟶ (∃ m ∈ B . minimal_element B R m)"
    and Hirrefl : "irrefl_on A R" 
  shows "wf_on A R" 
  unfolding wf_on_def
proof (intro allI impI)
  fix P
  assume IH : "(∀x∈A. (∀y∈A. (y, x) ∈ R ⟶ P y) ⟶ P x)"

  ― ‹ key step: instantiate B with "{z ∈ A . ¬ P z}" ›
  let ?B = "{z ∈ A . ¬ P z}" 
  let ?G = "∀ x ∈ A . P x"
  have "?B = {} ∨ ?B ≠ {}" by blast
  thus "?G"
  proof 
    assume "?B = {}"
    thus "?G" by blast
  next 
    assume "?B ≠ {}"
    have HS : "?B ⊆ A" by blast
    from Hsubset_min and HS and `?B ≠ {}` obtain m where mB : "m ∈ ?B" and Hmin : "minimal_element ?B R m"
      by (metis (mono_tags, lifting))
    have "∀y ∈ A. (y, m) ∈ R ⟶ P y"
    proof (intro ballI impI)
      fix y assume yA : "y ∈ A" and yRm : "(y, m) ∈ R"
      show "P y" 
      proof (rule ccontr)
        assume HnPy : "¬ (P y)"
        ― ‹ key step: derive (m, m) ∈ R ---> contradiction ›
        then have "(m, m) ∈ R" using yA yRm Hmin unfolding minimal_element_def by blast
        thus False using Hirrefl mB unfolding irrefl_on_def by blast
      qed
    qed

    with IH and `m ∈ ?B` have "P m" by blast
    with `m ∈ ?B` show "∀x ∈ A. P x" by blast
  qed
qed

lemma wf_min : 
  assumes wf : "wf_on A R"
  shows "∀ B ⊆ A . B ≠ {} ⟶ (∃ m ∈ B . minimal_element B R m)"
proof (intro allI impI)
  fix B
  assume HS : "B ⊆ A" and HC : "B ≠ {}"

  let ?G = "∃m∈B. minimal_element B R m"
  show ?G 
  proof (rule ccontr)
    assume Hno_min : "¬ ?G" 

    ― ‹ key step: instantiate P with "λx. x ∉ B" ›
    from wf have IH: "(∀x∈A. (∀y∈A. (y, x) ∈ R ⟶ y ∉ B) ⟶ x ∉ B) ⟶ (∀x∈A. x ∉ B)"
      unfolding wf_on_def by (rule spec[of _ "λx. x ∉ B"])

    have "∀ x ∈ A . (∀ y ∈ A . (y, x) ∈ R ⟶ y ∉ B) ⟶ x ∉ B"
    proof (intro ballI impI)
      fix x assume xA : "x ∈ A" and Hpredm : "(∀ y ∈ A . (y, x) ∈ R ⟶ y ∉ B)"
      show "x ∉ B"
      proof (* avoid (rule ccontr) *)
        assume xB : "x ∈ B"

        have "minimal_element B R x"
          unfolding minimal_element_def using xA xB Hpredm HS by blast

        ― ‹ key step: derive x to be the min element ---> contradiction ›
        hence ?G using xB by blast
        with Hno_min show False by contradiction
      qed 
    qed 

    with IH have "(∀x∈A. x ∉ B)" by blast 
    with HS have "B = {}" by blast
    with HC show False by contradiction
  qed
qed

(* Note this is stronger than what's in the homework *)
theorem wf_iff_min : 
  "R ⊆ (A × A) ⟹ 
   (wf_on A R ⟷ (irrefl_on A R ∧ (∀ B ⊆ A . B ≠ {} ⟶ (∃ m ∈ B . minimal_element B R m))))"
  using wf_min min_wf wf_irrefl wf_on_wf irrefl_on_def by metis

(* 5.2 *) 
experiment
begin

(* [!] Note the definition given in the homework is inaccurate. *)
definition "least_element A R m ⟷ (m ∈ A ∧ (∀ x ∈ A . (m, x) ∈ R))"

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
  defines "A ≡ {1, 2}"
    and "R ≡ {}"
  shows "irrefl_on A R"           (* Irreflexive *)
    and "trans R"                 (* Transitive (vacuously) *)
    and "wf_on A R"               (* Well-founded *)
    and "∃ B ⊆ A. B ≠ {} ∧ ¬(∃ m ∈ B. least_element B R m)"
proof -
  show "irrefl_on A R" unfolding irrefl_on_def R_def by blast
  show "trans R" unfolding trans_def R_def by blast
  show "wf_on A R" unfolding wf_on_def R_def by blast
  
  let ?B = "{1, 2}"
  have "?B ⊆ A" unfolding A_def by simp
  moreover have "¬(∃ m ∈ ?B. least_element ?B R m)"
    unfolding least_element_def R_def by auto
  ultimately show "∃ B ⊆ A. B ≠ {} ∧ ¬(∃ m ∈ B. least_element B R m)" by blast
qed

end

definition least_element :: "'A set ⇒ 'A rel ⇒ 'A ⇒ bool" where 
  "least_element A R m ⟷ (m ∈ A ∧ (∀ x ∈ A . x ≠ m ⟶ (m, x) ∈ R))"

lemma connected_min_least : 
  assumes Hconnected : "connected_on A R"
    and Hmin : "minimal_element A R x"
  shows "least_element A R x"
  unfolding least_element_def
proof 
  show "x ∈ A" using Hmin unfolding minimal_element_def by blast
next 
  have xA : "x ∈ A" using Hmin unfolding minimal_element_def by blast
  show "∀z∈A. z ≠ x ⟶ (x, z) ∈ R"
  proof (rule ballI, rule impI)
    fix z assume zA : "z ∈ A" and Hneq : "z ≠ x"
    consider "(x, z) ∈ R" | "(z, x) ∈ R" | "x = z" using Hconnected xA zA unfolding connected_on_def by blast
    then show "(x, z) ∈ R"
    proof cases
      case 1
      then show ?thesis by simp
    next
      case 2
      then have "(x, z) ∈ R" using zA Hmin unfolding minimal_element_def by blast
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
  show "x ∈ A" using Hleast unfolding least_element_def by blast
next 
  have xA : "x ∈ A" using Hleast unfolding least_element_def by blast
  show "∀z∈A. (z, x) ∈ R ⟶ z = x"
  proof (rule ballI, rule impI)
    fix z assume zA : "z ∈ A" and zRx : "(z, x) ∈ R"
    consider "(x, z) ∈ R" | "(z, x) ∈ R" | "x = z" using Hconnected xA zA unfolding connected_on_def by blast
    then show "z = x"
    proof cases
      case 1
      then show ?thesis using Hasym zRx xA zA unfolding asym_on_def by blast (* contradiction *)
    next
      case 2
      then have "z = x ∨ z ≠ x" by blast
      then show ?thesis 
      proof 
        assume "z = x" 
        thus ?thesis by simp
      next 
        assume "z ≠ x"
        then have "(x, z) ∈ R" using zA Hleast unfolding least_element_def by blast
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
    and Hmin : "∀ B ⊆ A . B ≠ {} ⟶ (∃ m ∈ B . minimal_element B R m)"
  shows "∀ B ⊆ A . B ≠ {} ⟶ (∃ m ∈ B . least_element B R m)"
  using assms
  apply clarify
  by (smt (verit, best) connected_on_def least_element_def minimal_element_def subset_eq)

lemma connected_least_min_subset : 
  assumes Hconnected : "connected_on A R"
    and Hasym : "asym_on A R"
    and Hleast : "∀ B ⊆ A . B ≠ {} ⟶ (∃ m ∈ B . least_element B R m)"
  shows "∀ B ⊆ A . B ≠ {} ⟶ (∃ m ∈ B . minimal_element B R m)"
  using assms
  apply clarify
  by (meson asym_on_subset connected_least_min connected_on_def subset_iff)

lemma least_connected:
  assumes Hsubset_least: "∀B ⊆ A. B ≠ {} ⟶ (∃m ∈ B. least_element B R m)"
  shows "connected_on A R"
  unfolding connected_on_def
proof (intro ballI)
  fix x y
  assume xA: "x ∈ A" and yA: "y ∈ A"
  
  show "(x, y) ∈ R ∨ (y, x) ∈ R ∨ x = y"
  proof (cases "x = y")
    case True
    then show ?thesis by blast
  next
    case False
    ― ‹key step: use the subset {x, y} ›
    let ?B = "{x, y}"
    have "?B ⊆ A" using xA yA by blast
    moreover have "?B ≠ {}" by blast
    ultimately obtain m where mB: "m ∈ ?B" and is_least: "least_element ?B R m"
      using Hsubset_least by blast

    from mB consider "m = x" | "m = y" by blast
    then show ?thesis
    proof (cases)
      case 1 ― ‹m = x›
      with is_least have "(x, y) ∈ R"
        unfolding least_element_def using False by auto
      then show ?thesis by blast
    next
      case 2 ― ‹m = y›
      with is_least have "(y, x) ∈ R"
        unfolding least_element_def using False by blast
      then show ?thesis by blast
    qed
  qed
qed

lemma least_asym_wf : 
  assumes Hsubset_least : "∀ B ⊆ A . B ≠ {} ⟶ (∃ m ∈ B . least_element B R m)"
    and Hasym : "asym_on A R" 
  shows "wf_on A R" 
  using assms 
  by (metis connected_least_min_subset irrefl_on_if_asym_on least_connected min_wf) 

lemma well_order_least : 
  assumes wf : "well_order_on A R"
  shows "∀ B ⊆ A . B ≠ {} ⟶ (∃ m ∈ B . least_element B R m)"
  using assms
  by (metis well_order_iff_wf_connected wf_min connected_min_least_subset)

lemma least_asym_well_order : 
  assumes "R ⊆ A × A" 
    and Hsubset_least : "∀ B ⊆ A . B ≠ {} ⟶ (∃ m ∈ B . least_element B R m)"
    and Hasym : "asym_on A R"
  shows "well_order_on A R" 
  using assms 
  by (metis well_order_iff_wf_connected least_asym_wf least_connected)

(* Note this is stronger than what's in the homework *)
theorem least_asym_iff_well_order : 
  "well_order_on A R ⟷ (R ⊆ (A × A) ∧ asym_on A R ∧ (∀ B ⊆ A . B ≠ {} ⟶ (∃ m ∈ B . least_element B R m)))"
  by (metis asym_on_iff_irrefl_on_if_trans_on hw3.well_order_on_def least_asym_well_order
      strict_total_order_iff_irrefl_trans_connected well_order_least)

(* Ex 6 *)
definition P_sets :: "'a set ⇒ ('a set ⇒ 'a rel ⇒ bool) ⇒ ('a rel) set" where 
  "P_sets A P = { R ∈ Pow (A × A). P A R }"

definition closure_system :: "'a set ⇒ ('a rel) set ⇒ bool" where 
  "closure_system A Ps = ((A × A) ∈ Ps ∧ (∀ S. S ⊆ Ps ∧ S ≠ {} ⟶ ⋂ S ∈ Ps))" 

definition P_closure :: "'a set ⇒ 'a rel ⇒ ('a rel) set ⇒ 'a rel" where 
  "P_closure A R Ps = ⋂ { P ∈ Ps . R ⊆ P }"

theorem P_closure_in_closure_system : 
  assumes HR: "R ⊆ A × A"
      and HCl: "closure_system A (P_sets A P)"
  shows "P_closure A R (P_sets A P) ∈ P_sets A P"
  unfolding P_closure_def
proof -
  let ?Ps = "P_sets A P"
  let ?S = "{Pa ∈ ?Ps. R ⊆ Pa}"
  
  ― ‹ Step 1: A × A is in P_sets A P (top element) ›
  from HCl have HAA: "(A × A) ∈ ?Ps" 
    unfolding closure_system_def by blast
  
  ― ‹ Step 2: A × A contains R, so it's in ?S ›
  from HAA HR have "(A × A) ∈ ?S" by blast
  hence HneS: "?S ≠ {}" by blast
  
  ― ‹ Step 3: ?S ⊆ ?Ps ›
  have HsubS: "?S ⊆ ?Ps" by blast
  
  ― ‹ Step 4: By closure system property, ⋂ ?S ∈ ?Ps ›
  from HCl have "∀S. S ⊆ ?Ps ∧ S ≠ {} ⟶ ⋂ S ∈ ?Ps"
    unfolding closure_system_def by blast

  ― ‹ key point: instantiate S with ?S ›
  with HsubS HneS have "⋂ ?S ∈ ?Ps" by blast
  
  thus "⋂ {Pa ∈ ?Ps. R ⊆ Pa} ∈ ?Ps" by blast
qed

(* Ex 6.1 *)
lemma refl_on_prod : 
  "refl_on A (A × A)"
  unfolding refl_on_def 
  by auto

theorem refl_on_closure_system : 
  shows "closure_system A (P_sets A refl_on)" 
  unfolding closure_system_def P_sets_def 
proof 
  have "refl_on A (A × A)" using refl_on_prod by blast
  thus "A × A ∈ {R ∈ Pow (A × A). refl_on A R}" by blast
next 
  show "∀S. S ⊆ {R ∈ Pow (A × A). refl_on A R} ∧ S ≠ {} ⟶
            ⋂ S ∈ {R ∈ Pow (A × A). refl_on A R}"
  proof (intro allI impI)
    fix S assume H: "S ⊆ {R ∈ Pow (A × A). refl_on A R} ∧ S ≠ {}"
    hence HS: "S ⊆ {R ∈ Pow (A × A). refl_on A R}" and HnS: "S ≠ {}" by auto
    have "refl_on A (⋂ S)" 
      unfolding refl_on_def 
    proof (intro ballI InterI)
      fix x X assume xA: "x ∈ A" and XS: "X ∈ S" 
      hence "refl_on A X" using HS by blast
      thus "(x, x) ∈ X" unfolding refl_on_def using xA by blast
    qed
    thus "⋂ S ∈ {R ∈ Pow (A × A). refl_on A R}" using H by blast
  qed
qed

(* Ex 6.2 *) 
lemma not_irrefl_on_prod : 
  assumes "A ≠ {}"
  shows "¬ irrefl_on A (A × A)"
  unfolding irrefl_on_def 
proof 
  assume H: "∀x∈A. (x, x) ∉ A × A"
  from assms obtain a where aA: "a ∈ A" by blast
  hence "(a, a) ∈ A × A" by simp
  with H aA show False by blast
qed

theorem irrefl_on_closure_system : 
  assumes HA : "A ≠ {}"
  shows "¬ closure_system A (P_sets A irrefl_on)" 
  unfolding closure_system_def P_sets_def 
proof
  assume "A × A ∈ {R ∈ Pow (A × A). irrefl_on A R} ∧
          (∀S. S ⊆ {R ∈ Pow (A × A). irrefl_on A R} ∧ S ≠ {} ⟶
               ⋂ S ∈ {R ∈ Pow (A × A). irrefl_on A R})"
  hence "A × A ∈ {R ∈ Pow (A × A). irrefl_on A R}" by blast 
  hence "irrefl_on A (A × A)" by blast
  thus False using not_irrefl_on_prod HA by metis
qed

(* Ex 6.3 *) 
lemma sym_on_prod : 
  "sym_on A (A × A)"
  unfolding sym_on_def 
  by auto

theorem sym_on_closure_system : 
  shows "closure_system A (P_sets A sym_on)" 
  unfolding closure_system_def P_sets_def 
proof
  have "sym_on A (A × A)" using sym_on_prod by blast  
  thus "A × A ∈ {R ∈ Pow (A × A). sym_on A R}" by blast
next 
  show "∀S. S ⊆ {R ∈ Pow (A × A). sym_on A R} ∧ S ≠ {} ⟶
            ⋂ S ∈ {R ∈ Pow (A × A). sym_on A R}"
  proof (intro allI impI)
    fix S assume H: "S ⊆ {R ∈ Pow (A × A). sym_on A R} ∧ S ≠ {}"
    hence HS: "S ⊆ {R ∈ Pow (A × A). sym_on A R}" and HnS: "S ≠ {}" by auto
    have "sym_on A (⋂ S)" 
      unfolding sym_on_def 
    proof (intro ballI ballI impI InterI)
      fix x y X assume xA: "x ∈ A" and yA: "y ∈ A"  and xyS : "(x, y) ∈ ⋂ S" and XS : "X ∈ S"
      hence HX : "sym_on A X" using HS by blast
      have "(x, y) ∈ X" using xyS XS by blast
      thus "(y, x) ∈ X" using yA xA HX unfolding sym_on_def by blast
    qed
    thus "⋂ S ∈ {R ∈ Pow (A × A). sym_on A R}" using H by blast
  qed
qed    

(* Ex 6.4 *) 
lemma not_asym_on_prod : 
  assumes "A ≠ {}"
  shows "¬ asym_on A (A × A)"
  unfolding asym_on_def 
proof 
  assume H: "∀x∈A. ∀y∈A. (x, y) ∈ A × A ⟶ (y, x) ∉ A × A"
  from assms obtain a where aA: "a ∈ A" by blast
  hence "(a, a) ∈ A × A" by simp
  with H aA show False by blast
qed

theorem asym_on_closure_system : 
  assumes HA : "A ≠ {}"
  shows "¬ closure_system A (P_sets A asym_on)" 
  unfolding closure_system_def P_sets_def 
proof
  assume "A × A ∈ {R ∈ Pow (A × A). asym_on A R} ∧
          (∀S. S ⊆ {R ∈ Pow (A × A). asym_on A R} ∧ S ≠ {} ⟶
               ⋂ S ∈ {R ∈ Pow (A × A). asym_on A R})"
  hence "A × A ∈ {R ∈ Pow (A × A). asym_on A R}" by blast 
  hence "asym_on A (A × A)" by blast
  thus False using not_asym_on_prod HA by metis
qed

(* Ex 6.5 *) 
lemma not_antisym_on_prod : 
  assumes "A ≠ {}"
    and "∀ x . A ≠ {x}"
  shows "¬ antisym_on A (A × A)"
  unfolding antisym_on_def 
proof 
  assume H: "∀x∈A. ∀y∈A. (x, y) ∈ A × A ⟶ (y, x) ∈ A × A ⟶ x = y"
  from assms(1) obtain a where aA: "a ∈ A" by blast
  from assms(2) have "A ≠ {a}" by blast
  with aA obtain b where bA: "b ∈ A" and neq: "b ≠ a" by blast
  hence "a = b" using aA H by simp
  with neq show False by blast
qed

theorem antisym_on_closure_system : 
  assumes HA0 : "A ≠ {}"
    and HA1 : "∀ x . A ≠ {x}"
  shows "¬ closure_system A (P_sets A antisym_on)" 
  unfolding closure_system_def P_sets_def 
proof
  assume "A × A ∈ {R ∈ Pow (A × A). antisym_on A R} ∧
          (∀S. S ⊆ {R ∈ Pow (A × A). antisym_on A R} ∧ S ≠ {} ⟶
               ⋂ S ∈ {R ∈ Pow (A × A). antisym_on A R})"
  hence "A × A ∈ {R ∈ Pow (A × A). antisym_on A R}" by blast 
  hence "antisym_on A (A × A)" by blast
  thus False using not_antisym_on_prod HA0 HA1 by metis
qed

(* Ex 6.6 *) 
lemma trans_on_prod : 
  "trans_on A (A × A)"
  unfolding trans_on_def 
  by auto

theorem trans_on_closure_system : 
  shows "closure_system A (P_sets A trans_on)" 
  unfolding closure_system_def P_sets_def 
proof
  have "trans_on A (A × A)" using trans_on_prod by blast  
  thus "A × A ∈ {R ∈ Pow (A × A). trans_on A R}" by blast
next 
  show "∀S. S ⊆ {R ∈ Pow (A × A). trans_on A R} ∧ S ≠ {} ⟶
            ⋂ S ∈ {R ∈ Pow (A × A). trans_on A R}"
  proof (intro allI impI)
    fix S assume H: "S ⊆ {R ∈ Pow (A × A). trans_on A R} ∧ S ≠ {}"
    hence HS: "S ⊆ {R ∈ Pow (A × A). trans_on A R}" and HnS: "S ≠ {}" by auto
    have "trans_on A (⋂ S)" 
      unfolding trans_on_def 
    proof (intro ballI ballI ballI impI impI InterI)
      fix x y z X 
      assume xA: "x ∈ A" and yA: "y ∈ A" and zA : "z ∈ A" 
      and xyS : "(x, y) ∈ ⋂ S" and yzS : "(y, z) ∈ ⋂ S" and XS : "X ∈ S"
      hence HX : "trans_on A X" using HS by blast
      have xyX : "(x, y) ∈ X" using xyS XS by blast
      have yzX : "(y, z) ∈ X" using yzS XS by blast
      thus "(x, z) ∈ X" using yA xA zA HX xyX yzX unfolding trans_on_def by blast
    qed
    thus "⋂ S ∈ {R ∈ Pow (A × A). trans_on A R}" using H by blast
  qed
qed    

(* Ex 9 *)
definition infinite_decreasing_sequence :: "'A rel ⇒ (nat ⇒ 'A) ⇒ bool" where 
  "infinite_decreasing_sequence R s = (∀ i . (s (Suc i), s i) ∈ R)"

lemma wf_no_infinite_decreasing_sequence : 
  assumes HS : "R ⊆ A × A" 
    and Hwf : "wf_on A R"
  shows "¬ (∃ (s :: nat ⇒ 'A) . infinite_decreasing_sequence R s)"
  (* Don't unfolding infinite_decreasing_sequence_def at this point ---> obtain will fail! *)
proof 
  assume "∃ (s :: nat ⇒ 'A) . infinite_decreasing_sequence R s"
  then obtain s where Hd : "infinite_decreasing_sequence R s" by blast
  then show False 
  proof - 
    let ?B = "range s" ― ‹ key point ›
    have HB : "?B ⊆ A" using Hd HS unfolding infinite_decreasing_sequence_def by blast
    have "?B ≠ {}" using Hd HS HB unfolding infinite_decreasing_sequence_def by blast
    hence "(∃ m ∈ ?B . minimal_element ?B R m)" using HB Hwf wf_min by blast
    then obtain m where Hm : "minimal_element ?B R m" by blast 
    then obtain i where "m = s i" using Hm unfolding minimal_element_def by blast
    hence HC : "(s (Suc i), m) ∈ R" using Hd unfolding infinite_decreasing_sequence_def by blast
    hence "s (Suc i) = m" using Hm unfolding minimal_element_def by blast
    thus False using wf_irrefl Hwf wf_on_wf HC HS by metis
  qed
qed

lemma no_infinite_descreasing_sequence_irrefl : 
  assumes Hno_seq : "¬ (∃ (s :: nat ⇒ 'A) . infinite_decreasing_sequence R s)"
  shows "irrefl_on A R"
proof (rule ccontr)
  assume "¬ irrefl_on A R"
  ― ‹ key step: construct an infinite decreasing sequence from x ›
  hence "∃ x ∈ A . (x, x) ∈ R" unfolding irrefl_on_def by blast
  then obtain x where xRx : "(x, x) ∈ R" by blast 
  hence "infinite_decreasing_sequence R (λ i . x)"
    unfolding infinite_decreasing_sequence_def by blast
  with Hno_seq show False by blast
qed

lemma refl_not_irrefl : 
  "A ≠ {} ⟹ 
   refl_on A R ⟹ 
   ¬ irrefl_on A R"
  by (simp add: irrefl_on_def refl_on_def)

lemma refl_infinite_descreasing_sequence : 
  assumes HA : "A ≠ {}" 
    and Hrefl : "refl_on A R"
  shows "(∃ (s :: nat ⇒ 'A) . infinite_decreasing_sequence R s)"
  by (metis no_infinite_descreasing_sequence_irrefl Hrefl HA refl_not_irrefl)

lemma no_infinite_decreasing_sequence_wf : 
  assumes HS : "R ⊆ A × A" 
  and Hno_seq : "¬ (∃ (s :: nat ⇒ 'A) . infinite_decreasing_sequence R s)"
  shows "wf_on A R"
proof (rule contrapos_np [OF Hno_seq])
  assume "¬ wf_on A R"
  ― ‹ key step: reasoning with the minimal element ›
  hence "¬ ((∀ B ⊆ A . B ≠ {} ⟶ (∃ m ∈ B . minimal_element B R m)) ∧ irrefl_on A R)" using min_wf by blast
  hence "(∃ B ⊆ A . B ≠ {} ∧ (∀ m ∈ B . ¬ minimal_element B R m)) ∨ (¬ irrefl_on A R)" by blast
  thus "∃s. infinite_decreasing_sequence R s"
  proof 
    assume "∃ B ⊆ A . B ≠ {} ∧ (∀ m ∈ B . ¬  minimal_element B R m)"
    then obtain B where HB : "B ⊆ A" and HnB : "B ≠ {}" and Hnm : "(∀ m ∈ B . ¬ minimal_element B R m)" by blast 
    hence "∃ x ∈ B . ¬ minimal_element B R x" by blast
    then obtain x where xB : "x ∈ B" and Hnx : "¬ minimal_element B R x" by blast 
    hence "∀ y ∈ B . ∃ z ∈ B . (z, y) ∈ R" using Hnm unfolding minimal_element_def by blast
    hence "∃s. ∀n. s n ∈ B ∧ (s (Suc n), s n) ∈ R"
      ― ‹ key point: use [dependent_nat_choice] to construct an infinite decreasing sequence ›
      using dependent_nat_choice[where P = "λ n x. x ∈ B" and Q = "λn x y. (y, x) ∈ R"] xB by blast
    then obtain s where Hs : "∀n. s n ∈ B ∧ (s (Suc n), s n) ∈ R" by blast
    hence "infinite_decreasing_sequence R s" 
      unfolding infinite_decreasing_sequence_def by blast
    thus "∃s. infinite_decreasing_sequence R s" by blast
  next 
    assume "¬ irrefl_on A R"
    show ?thesis using ‹¬ irrefl_on A R› no_infinite_descreasing_sequence_irrefl by blast
  qed
qed

theorem wf_iff_no_infinite_decreasing_sequence : 
 "R ⊆ A × A ⟹
  (wf_on A R ⟷ ¬ (∃ s . infinite_decreasing_sequence R s))"
  by (metis no_infinite_decreasing_sequence_wf wf_no_infinite_decreasing_sequence)

corollary wf_on_irrefl : 
  "R ⊆ A × A ⟹ 
   (wf_on A R ⟶ irrefl_on A R)" 
  by (metis wf_no_infinite_decreasing_sequence no_infinite_descreasing_sequence_irrefl)

lemma no_infinite_descreasing_sequence_asym : 
  assumes Hno_seq : "¬ (∃ (s :: nat ⇒ 'A) . infinite_decreasing_sequence R s)"
  shows "asym_on A R"
proof (rule ccontr)
  assume "¬ asym_on A R"
  ― ‹ key step: construct an infinite decreasing sequence from x and y ›
  hence "∃ x ∈ A. ∃ y ∈ A. (x, y) ∈ R ∧ (y, x) ∈ R" unfolding asym_on_def by blast
  then obtain x and y where xRy : "(x, y) ∈ R" and yRx : "(y, x) ∈ R" by blast 
  let ?s = "λ i . if even i then x else y"
  have "infinite_decreasing_sequence R ?s"
    unfolding infinite_decreasing_sequence_def 
  proof (intro allI)
    fix i 
    show "(?s (Suc i), ?s i) ∈ R" 
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
  "R ⊆ A × A ⟹ 
   (wf_on A R ⟶ asym_on A R)" 
  by (metis wf_no_infinite_decreasing_sequence no_infinite_descreasing_sequence_asym)

(* Ex 10 *) 
(* Note this is slightly different from [wf_trancl] *)
lemma wf_trancl_wf:
  assumes HS : "R ⊆ A × A" 
    and Hwf : "wf_on A R"
  shows "wf_on A (R⇧+)"
  unfolding wf_on_def 
proof (intro allI impI)
  fix P assume IHRp : "∀z∈A. (∀y∈A. (y, z) ∈ R⇧+ ⟶ P y) ⟶ P z"
  from Hwf have HwfR : "∀ Q . (∀ x ∈ A. (∀ y ∈ A. (y, x) ∈ R ⟶ Q y) ⟶ Q x) ⟶ (∀ x ∈ A. Q x)" unfolding wf_on_def by blast
  
  ― ‹ key point: instantiate P with the right IH ›
  let ?P = "λ z . (∀w∈A. (w, z) ∈ R⇧+ ⟶ P w)"
  have Rind : "(∀ a ∈ A. (∀ b ∈ A. (b, a) ∈ R ⟶ ?P b) ⟶ ?P a) ⟶ (∀ a ∈ A. ?P a)" 
    using HwfR [rule_format, where Q = "?P"] by blast

  (*  ∀a∈A. 
          (∀b∈A. (b, a) ∈ R ⟶ (∀w∈A. (w, b) ∈ R⇧+ ⟶ P w)) ⟶
          (∀w∈A. (w, a) ∈ R⇧+ ⟶ P w) *)
  have "(∀ a ∈ A. (∀ b ∈ A. (b, a) ∈ R ⟶ ?P b) ⟶ ?P a)"
  proof (intro ballI impI impI impI)
    fix a w 
    assume IH : "∀b∈A. (b, a) ∈ R ⟶ (∀w∈A. (w, b) ∈ R⇧+ ⟶ P w)" 
      and aA : "a ∈ A" and wA : "w ∈ A" and wRRa : "(w, a) ∈ R⇧+"
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

  (* ∀a∈A. ∀w∈A. (w, a) ∈ R⇧+ ⟶ P w *)
  hence "∀ a ∈ A. ?P a" using Rind by blast 
  thus "∀ a ∈ A . P a" using IHRp by blast
qed

lemma trancl_wf_wf:
  assumes HS : "R ⊆ A × A" 
    and Hwf : "wf_on A (R⇧+)"
  shows "wf_on A R"
proof - 
  have HRR : "(∀ B ⊆ A . B ≠ {} ⟶ (∃ m ∈ B . minimal_element B (R⇧+) m))" using Hwf HS wf_min by blast 
  have HR : "(∀ B ⊆ A . B ≠ {} ⟶ (∃ m ∈ B . minimal_element B R m))" 
  proof (intro allI impI)
    fix B assume HBA : "B ⊆ A" and HB : "B ≠ {}" 
    with HRR obtain m where HmRR : "minimal_element B (R⇧+) m" by blast
    hence "minimal_element B R m" using r_into_trancl unfolding minimal_element_def by blast 
    thus "∃m∈B. minimal_element B R m" unfolding minimal_element_def by blast
  qed

  have "irrefl_on A (R⇧+)" using irrefl_on_def wf_on_wf Hwf HS wf_irrefl
    by (metis trancl_subset_Sigma)
  hence "irrefl_on A R" by (meson HS Hwf irrefl_on_def r_into_trancl)  
  thus ?thesis using min_wf HS HR by blast
qed

theorem wf_iff_transcl_wf : 
  "R ⊆ A × A ⟹ 
   (wf_on A (R⇧+) ⟷ wf_on A R)"
  by (metis trancl_wf_wf wf_trancl_wf)

(* Ex 11 *) 
definition lex_order :: "'A rel ⇒ 'A rel ⇒ ('A × 'A) rel" where 
  "lex_order Ra Rb = {((a, b), (c, d)). (a, c) ∈ Ra ∨ (a = c ∧ (b, d) ∈ Rb) }"

(* Mostly generated by Claude Opus 4.5 with a few rounds of interactions! *)
lemma wf_lex_order : 
  assumes HSa : "Ra ⊆ A × A"
    and HSb : "Rb ⊆ A × A"  
    and HRa : "wf_on A Ra" 
    and HRb : "wf_on A Rb" 
  shows "wf_on (A × A) (lex_order Ra Rb)"
  unfolding wf_on_def 
proof (intro allI impI)
  fix P assume IH: "∀x∈A × A. (∀y∈A × A. (y, x) ∈ lex_order Ra Rb ⟶ P y) ⟶ P x"
  
  ― ‹ We prove ∀x∈A × A. P x using nested well-founded induction ›
  ― ‹ Outer induction on first component (wrt Ra), inner on second (wrt Rb) ›
  
  ― ‹ Key: define the outer induction predicate ›
  define Qa where "Qa ≡ λa. ∀b∈A. P (a, b)"
  
  have "∀a∈A. Qa a"
    using HRa unfolding wf_on_def
  proof (rule spec[where x="Qa", THEN mp])
    show "(∀a∈A. (∀a'∈A. (a', a) ∈ Ra ⟶ Qa a') ⟶ Qa a)"
    proof (intro ballI impI)
      fix a assume aA: "a ∈ A" and IHa: "∀a'∈A. (a', a) ∈ Ra ⟶ Qa a'"
      ― ‹ Need to show: Qa a = (∀b∈A. P (a, b)) ›
      ― ‹ Use inner induction on b wrt Rb ›
      show "Qa a" unfolding Qa_def
        using HRb unfolding wf_on_def
      proof (rule spec[where x="λb. P (a, b)", THEN mp])
        show "∀b∈A. (∀b'∈A. (b', b) ∈ Rb ⟶ P (a, b')) ⟶ P (a, b)"
        proof (intro ballI impI)
          fix b assume bA: "b ∈ A" and IHb: "∀b'∈A. (b', b) ∈ Rb ⟶ P (a, b')"
          ― ‹ Need to show: P (a, b) ›
          ― ‹ Use the main IH: show all lex-predecessors satisfy P ›
          
          have abAA: "(a, b) ∈ A × A" using aA bA by blast
          
          ― ‹ Show all lex-predecessors satisfy P ›
          have Hpred: "∀y∈A × A. (y, (a, b)) ∈ lex_order Ra Rb ⟶ P y"
          proof (intro ballI impI)
            fix y assume yAA: "y ∈ A × A" and Hyx: "(y, (a, b)) ∈ lex_order Ra Rb"
            obtain a' b' where y_eq: "y = (a', b')" using prod.exhaust by blast
            from yAA y_eq have a'A: "a' ∈ A" and b'A: "b' ∈ A" by auto
            from Hyx y_eq have "(a', a) ∈ Ra ∨ (a' = a ∧ (b', b) ∈ Rb)"
              unfolding lex_order_def by auto
            thus "P y"
            proof
              assume "(a', a) ∈ Ra"
              ― ‹ First component decreases: use outer IH ›
              hence "Qa a'" using IHa a'A by blast
              thus "P y" using y_eq b'A unfolding Qa_def by blast
            next
              assume "a' = a ∧ (b', b) ∈ Rb"
              ― ‹ First component same, second decreases: use inner IH ›
              thus "P y" using y_eq IHb b'A by blast
            qed
          qed
          
          ― ‹ Apply the main IH ›
          from IH abAA Hpred show "P (a, b)" by blast
        qed
      qed
    qed
  qed
  
  thus "∀x∈A × A. P x" unfolding Qa_def by auto
qed 

end