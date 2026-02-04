theory "hw3-ord" 
imports ZF 
begin

(* Lemma 5 *)
definition pred :: "i \<Rightarrow> i \<Rightarrow> (i \<Rightarrow> o) \<Rightarrow>i" where 
  "pred(x, a, r) \<equiv> { y \<in> a . r(y) }"

abbreviation predm :: "i \<Rightarrow> i \<Rightarrow> i" where 
  "predm(x, a) \<equiv> pred(x, a, \<lambda> y . y \<in> x)"

lemma predm_Transset : 
  assumes Hp : "\<forall> x \<in> i . x = predm(x, i)"
  shows   "Transset(i)"
  unfolding Transset_def subset_def
proof (intro ballI ballI)
  fix x w assume xi : "x \<in> i" and wx : "w \<in> x"
  hence "x = { y \<in> i . y \<in> x }" using Hp unfolding pred_def by blast 
  hence "w \<in> { y \<in> i . y \<in> x }" using wx by simp
  thus "w \<in> i" using CollectD1 by blast
qed

lemma Transset_predm : 
  assumes Hp : "Transset(i)"
  shows   "\<forall> x \<in> i . x = predm(x, i)"
  unfolding pred_def 
proof (intro ballI)
  fix x assume xi : "x \<in> i"
  show "x = {y \<in> i . y \<in> x}" 
  proof (rule equalityI; rule subsetI)
    fix y assume yx : "y \<in> x"
    have "y \<in> i" using Hp xi yx unfolding Transset_def by blast
    thus "y \<in> {z \<in> i . z \<in> x}" using yx by blast
  next 
    fix y assume yp : "y \<in> {z \<in> i . z \<in> x}"
    thus "y \<in> x" using CollectD2 by blast
  qed
qed

theorem Transset_iff_predm : 
  "Transset(i) \<longleftrightarrow> (\<forall> x \<in> i . x = predm(x, i))" 
  using Transset_predm predm_Transset 
  by blast

(* Transset is truly transitive *)
definition set_trans :: "i \<Rightarrow> o" where 
  "set_trans(i) \<equiv> (\<forall>b\<in>i. \<forall>a\<in>b. a \<in> i)"

definition set_trans' :: "i \<Rightarrow> o" where 
  "set_trans'(i) \<equiv> (\<forall> a b. a \<in> b \<and> b \<in> i \<longrightarrow> a \<in> i)"

lemma transset_trans : 
  "Transset(i) \<Longrightarrow> set_trans(i)"
  unfolding Transset_def set_trans_def
  apply clarify 
  by blast

lemma trans_transset : 
  "set_trans(i) \<Longrightarrow> Transset(i)" 
  unfolding Transset_def set_trans_def 
  apply clarify 
  by blast 

theorem transset_iff_trans : 
  "Transset(i) \<longleftrightarrow> set_trans(i)"
  using trans_transset transset_trans by auto
  
(* Lemma 8 *) 
lemma transset_union : 
  "Transset(i) \<Longrightarrow> 
   Transset(j) \<Longrightarrow> 
   Transset(i \<union> j)"
  unfolding Transset_def
  apply clarify 
  by blast

lemma ord_union : 
  "Ord(i) \<Longrightarrow> 
   Ord(j) \<Longrightarrow> 
   Ord(i \<union> j)"
  unfolding Ord_def
  apply clarify 
  using transset_union by blast

(* Note induction on the number of ordinals in A doesn't make sense *)
lemma transset_Union : 
  "\<forall> i \<in> A . Transset(i) \<Longrightarrow> 
   Transset (\<Union> A)"
  unfolding Transset_def 
  apply clarify 
  by blast

theorem ord_Union : 
  "\<forall> i \<in> A . Ord(i) \<Longrightarrow> 
   Ord (\<Union> A)"
  unfolding Ord_def 
  using transset_Union by blast

(* Lemma 10 *) 
definition res :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where 
  "res(a, r, x) = restrict(r, pred(x, a, \<lambda> y . <y , x> \<in> r))"

end