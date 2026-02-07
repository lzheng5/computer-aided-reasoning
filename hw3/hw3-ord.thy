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

(* Unrelated *) 
thm_deps Fixedpt.induct

lemma mem_irrefl : 
  shows "a ∉ a" 
proof (intro notI)
  assume aa : "a ∈ a"
  have "∃ x ∈ {a} . ∀ y ∈ x . y ∉ {a}" using foundation [of "{a}"] by blast
  then obtain x where Hx : "x ∈ {a}" and Hc : "∀ y ∈ x . y ∉ {a}" by blast 
  hence "x = a" by blast 
  hence "a ∉ {a}" using aa Hc by blast
  thus False by blast 
qed

lemma mem_asym : 
  assumes ab : "a ∈ b" 
  shows "b ∉ a"
proof (intro notI)
  assume ba : "b ∈ a" 
  have "∃ x ∈ {a, b} . ∀ y ∈ x . y ∉ {a, b}" using foundation [of "{a, b}"] by blast
  then obtain x where Hx : "x ∈ {a, b}" and Hc : "∀ y ∈ x . y ∉ {a, b}" by blast 
  hence "x = a ∨ x = b" by blast 
  thus "False" 
  proof 
    assume "x = a" 
    hence "b ∉ {a, b}" using ba Hc by blast
    thus False by blast 
  next 
    assume "x = b" 
    hence "a ∉ {a, b}" using ab Hc by blast 
    thus False by blast
  qed 
qed 

lemma wf_Memrel: "wf(Memrel(A))"
  unfolding wf_def
proof 
  fix Z 
  have "Z = 0 ∨ (∃x∈Z. ∀y∈x. y∉Z)" using foundation by blast
  thus "Z = 0 ∨ (∃x∈Z. ∀y. ⟨y, x⟩ ∈ Memrel(A) ⟶ y ∉ Z)"
  proof 
    assume "Z = 0" 
    thus "Z = 0 ∨ (∃x∈Z. ∀y. ⟨y, x⟩ ∈ Memrel(A) ⟶ y ∉ Z)" by blast
  next 
    assume "∃x∈Z. ∀y∈x. y ∉ Z"
    then obtain x where xZ : "x ∈ Z" and HZ : "∀y∈x. y ∉ Z" by blast
    have "(∀y. ⟨y, x⟩ ∈ Memrel(A) ⟶ y ∉ Z)" 
    proof (intro allI impI)
      fix y assume "⟨y, x⟩ ∈ Memrel(A)" 
      hence "y ∈ x" using Memrel_iff by blast
      thus "y ∉ Z" using HZ by blast
    qed 
    thus "Z = 0 ∨ (∃x∈Z. ∀y. ⟨y, x⟩ ∈ Memrel(A) ⟶ y ∉ Z)" using xZ by blast
  qed
qed

lemma Transset_induct:
  assumes HT : "Transset(k)"
     and  Hk : "∀x∈k. (∀y∈x. P(y)) ⟶ P(x)"
   shows  "∀ i ∈ k. P(i)"
proof (intro ballI)
  fix i assume ik : "(i ∈ k)"
  have Hwf : "wf(Memrel(k))" using wf_Memrel by blast 

  thus "P(i)" using ik
  proof (rule wf_induct2) (* Cannot directly use wf_induct/wf_induct_raw as [a] is unbounded *)
    show "field(Memrel(k)) ⊆ k" unfolding field_def Memrel_def by blast
  next 
    fix x assume xk : "x ∈ k" and IH : "∀y. ⟨y, x⟩ ∈ Memrel(k) ⟶ P(y)"
    have "∀y∈x. P(y)" 
    proof (intro ballI)
      fix y assume yx : "y ∈ x"
      hence "⟨y, x⟩ ∈ Memrel(k)" using xk HT unfolding Transset_def by blast
      thus "P(y)" using IH by blast
    qed 
    thus "P(x)" using Hk xk by blast
  qed
qed

thm trans_induct

lemma Ord_linear:
     "Ord(i) ⟹ Ord(j) ⟹ i∈j | i=j | j∈i"
proof (induct i arbitrary: j rule: trans_induct)
  case (step i')
  note IHi = step
  show ?case using ‹Ord(j)›
  proof (induct j rule: trans_induct)
    case (step j')
    note IHj = step
    then show ?case using IHi
      by (blast dest: Ord_trans)

(*
Goal: i ∈ j ∨ i = j ∨ j ∈ i

Negate: ¬(i ∈ j) ∧ ¬(i = j) ∧ ¬(j ∈ i)

Now blast has: i ∉ j, i ≠ j, j ∉ i

Try to derive contradiction...

From extensionality (i ≠ j):
  Either ∃y. y ∈ i ∧ y ∉ j   OR   ∃w. w ∈ j ∧ w ∉ i

Branch 1: Assume y ∈ i ∧ y ∉ j
  Apply step_i: y ∈ j ∨ y = j ∨ j ∈ y
  - y ∈ j contradicts y ∉ j ✗
  - y = j means j ∈ i, contradicts j ∉ i ✗  
  - j ∈ y, then Ord_trans gives j ∈ i, contradicts j ∉ i ✗
  All branches closed!

Branch 2: Assume w ∈ j ∧ w ∉ i
  (Similar reasoning closes all branches)

---------------------------------------------------

Case on subset relation :
 
Case 1: i ⊆ j
  ├─ Case 1a: j ⊆ i  →  i = j  (by extensionality)
  └─ Case 1b: j ⊄ i  →  ∃w ∈ j. w ∉ i
                       By IH: i ∈ w ∨ i = w ∨ w ∈ i
                       Since w ∉ i, we get i ∈ w or i = w
                       Either way: i ∈ j (by transitivity)

Case 2: i ⊄ j  →  ∃y ∈ i. y ∉ j
  By IH: y ∈ j ∨ y = j ∨ j ∈ y
  Since y ∉ j, we get y = j or j ∈ y
  Either way: j ∈ i (by transitivity)
*)

  qed
qed

end