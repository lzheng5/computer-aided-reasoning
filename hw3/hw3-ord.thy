theory "hw3-ord" 
imports ZF 
begin

(* Lemma 5 *)
definition pred :: "i ⇒ (i ⇒ o) ⇒i" where 
  "pred(a, r) ≡ { y ∈ a . r(y) }"

abbreviation predm :: "i ⇒ i ⇒ i" where 
  "predm(x, a) ≡ pred(a, λ y . y ∈ x)"

lemma predm_Transset : 
  assumes Hp : "∀ x ∈ i . x = predm(x, i)"
  shows   "Transset(i)"
  unfolding Transset_def subset_def
proof (intro ballI ballI)
  fix x w assume xi : "x ∈ i" and wx : "w ∈ x"
  hence "x = { y ∈ i . y ∈ x }" using Hp unfolding pred_def by blast 
  hence "w ∈ { y ∈ i . y ∈ x }" using wx by simp
  thus "w ∈ i" using CollectD1 by blast
qed

lemma Transset_predm : 
  assumes Hp : "Transset(i)"
  shows   "∀ x ∈ i . x = predm(x, i)"
  unfolding pred_def 
proof (intro ballI)
  fix x assume xi : "x ∈ i"
  show "x = {y ∈ i . y ∈ x}" 
  proof (rule equalityI; rule subsetI)
    fix y assume yx : "y ∈ x"
    have "y ∈ i" using Hp xi yx unfolding Transset_def by blast
    thus "y ∈ {z ∈ i . z ∈ x}" using yx by blast
  next 
    fix y assume yp : "y ∈ {z ∈ i . z ∈ x}"
    thus "y ∈ x" using CollectD2 by blast
  qed
qed

theorem Transset_iff_predm : 
  "Transset(i) ⟷ (∀ x ∈ i . x = predm(x, i))" 
  using Transset_predm predm_Transset 
  by blast

(* Transset is truly transitive *)
definition set_trans :: "i ⇒ o" where 
  "set_trans(i) ≡ (∀b∈i. ∀a∈b. a ∈ i)"

definition set_trans' :: "i ⇒ o" where 
  "set_trans'(i) ≡ (∀ a b. a ∈ b ∧ b ∈ i ⟶ a ∈ i)"

lemma transset_trans : 
  "Transset(i) ⟹ set_trans(i)"
  unfolding Transset_def set_trans_def
  apply clarify 
  by blast

lemma trans_transset : 
  "set_trans(i) ⟹ Transset(i)" 
  unfolding Transset_def set_trans_def 
  apply clarify 
  by blast 

theorem transset_iff_trans : 
  "Transset(i) ⟷ set_trans(i)"
  using trans_transset transset_trans by auto
  
(* Lemma 8 *) 
lemma transset_union : 
  "Transset(i) ⟹ 
   Transset(j) ⟹ 
   Transset(i ∪ j)"
  unfolding Transset_def
  apply clarify 
  by blast

lemma ord_union : 
  "Ord(i) ⟹ 
   Ord(j) ⟹ 
   Ord(i ∪ j)"
  unfolding Ord_def
  apply clarify 
  using transset_union by blast

(* Note induction on the number of ordinals in A doesn't make sense *)
lemma transset_Union : 
  "∀ i ∈ A . Transset(i) ⟹ 
   Transset (⋃ A)"
  unfolding Transset_def 
  apply clarify 
  by blast

theorem ord_Union : 
  "∀ i ∈ A . Ord(i) ⟹ 
   Ord (⋃ A)"
  unfolding Ord_def 
  using transset_Union by blast

(* Lemma 10 *) 
(* Restrict r to the initial segment of x *)
definition res :: "i ⇒ i ⇒ i ⇒ i" where 
  "res(a, r, x) = restrict(r, pred(a, λ y . <y , x> ∈ r))"

end