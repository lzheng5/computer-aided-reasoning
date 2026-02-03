theory "hw3-ord" 
imports ZF 
begin

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

end