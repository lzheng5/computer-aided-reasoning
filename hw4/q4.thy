theory q4 
  imports Main "HOL-Library.Multiset"
begin

(* Sorting Algorithms *) 

context linorder 
begin

section "Insertion Sort"

fun ins :: "'a ⇒ 'a list ⇒ 'a list" where
   "ins x [] = [x]"
 | "ins x (y # ys) = (if x ≤ y then x # (y # ys) else y # (ins x ys))"

fun isort :: "'a list ⇒ 'a list" where 
   "isort [] = []" 
 | "isort (x # xs) = ins x (isort xs)"

lemma add_mset_ins : 
   "add_mset a (mset xs) = mset (ins a xs)"
(* by (induction xs arbitrary: a; fastforce) *)
proof (induction xs arbitrary: a)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by fastforce
(* by (metis add_mset_commute ins.simps(2) mset.simps(2)) *)
qed

theorem isort_permute [simp]: 
   "mset (isort xs) = mset xs"
  apply (induction xs; simp)
  by (metis add_mset_ins)

lemma set_isort [simp]: "set (isort xs) = set xs"
proof -
  have "set_mset (mset (isort xs)) = set_mset (mset xs)"
    using isort_permute by simp
  then show ?thesis by (simp only: set_mset_mset)
qed

lemma ins_sorted : 
  "sorted xs ⟹ sorted (ins a xs)"
proof (induction xs arbitrary: a)
  case Nil
  then show ?case by simp
next
  case (Cons b xs)
  then show ?case 
  proof (cases "a ≤ b")
    case True
    then show ?thesis using Cons.prems by fastforce
  next
    case False
    hence "ins a (b # xs) = b # (ins a xs)" by simp
    then show ?thesis using Cons.prems Cons.IH False
    by (smt (verit) ins.elims local.linear local.sorted1
        local.sorted2)
  qed
qed

theorem isort_sorted : 
   "sorted (isort xs)"
  apply (induction xs; simp)
  by (metis ins_sorted)

section "Quick Sort"

fun qsort :: "'a list ⇒ 'a list" where 
   "qsort [] = []"
 | "qsort (x # xs) = qsort [y ← xs.¬ x ≤ y] @ [x] @ qsort [y ← xs . x ≤ y]"

lemma [code] : 
   "qsort [] = []" 
   "qsort (x # xs) = qsort [y ← xs. y < x] @ [x] @ qsort [y ← xs . x ≤ y]"
  by (simp_all add: not_le)

theorem qsort_permute [simp] :
  "mset (qsort xs) = mset xs"
proof (induction xs rule: qsort.induct)
  case 1
  then show ?case by simp
next
  case (2 x xs)
  have "qsort (x # xs) =  qsort [y ← xs. ¬ x ≤ y] @ [x] @ qsort [y ← xs . x ≤ y]" by simp
  moreover have "mset (filter (λy. ¬ x ≤ y) xs) + mset (filter ((≤) x) xs) = mset xs" by auto
  ultimately show ?case using "2.IH" by simp
qed

lemma set_qsort [simp]: "set (qsort xs) = set xs"
proof -
  have "set_mset (mset (qsort xs)) = set_mset (mset xs)"
    using qsort_permute by simp
  then show ?thesis by (simp only: set_mset_mset)
qed

theorem qsort_sorted :
  "sorted (qsort xs)" 
proof (induction xs rule: qsort.induct)
  case 1
  then show ?case by simp
next
  case (2 x xs)
  have "qsort (x # xs) =  qsort [y ← xs. ¬ x ≤ y] @ [x] @ qsort [y ← xs . x ≤ y]" by simp
  moreover have "sorted [x]" by simp
  ultimately show ?case using "2.IH" sorted_append by auto
qed

section "Equivalence"

theorem mset_sorted : 
  assumes Heq : "mset xs = mset ys"
      and Hxs : "sorted xs" 
      and Hys : "sorted ys" 
    shows "xs = ys"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case
  proof (cases ys)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a list)
    hence False using Nil.prems(1) by simp
    then show ?thesis by simp
  qed 
next
  case (Cons a xs')
  then show ?case 
  proof (cases ys)
    case Nil
    hence False using Cons.prems by simp
    then show ?thesis by simp
  next
    case (Cons b ys')
    have "a ∈ set (b # ys')" 
      using Cons.prems(1) ‹ys = b # ys'› 
      by (metis list.set_intros(1) set_mset_mset)
    hence "b ≤ a" using Cons.prems(3) ‹ys = b # ys'› 
      by auto
    moreover have "b ∈ set (a # xs')" 
      using Cons.prems(1) ‹ys = b # ys'›
      by (metis list.set_intros(1) set_mset_mset)
    hence "a ≤ b" using Cons.prems(2) 
      by auto
    ultimately have "a = b" by (simp add: antisym)
    moreover have "mset xs' = mset ys'" 
      using Cons.prems(1) ‹ys = b # ys'› ‹a = b› by simp
    moreover have "sorted xs'" using Cons.prems(2) by simp
    moreover have "sorted ys'" using Cons.prems(3) ‹ys = b # ys'› by simp
    ultimately have "xs' = ys'" using Cons.IH by blast
    then show ?thesis using ‹a = b› ‹ys = b # ys'› by simp
  qed
qed

corollary isort_qsort : 
  "isort xs = qsort xs" 
proof -
  have "mset (isort xs) = mset (qsort xs)" by auto
  thus ?thesis using mset_sorted isort_sorted qsort_sorted by blast
qed 

end

end