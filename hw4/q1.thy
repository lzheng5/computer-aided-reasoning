theory q1 
  imports Main
begin

fun m_bad_app :: "'a list ⇒ 'a list ⇒ 'a list ⇒ nat" where
  "m_bad_app [] [] _ = 0"
| "m_bad_app x [] _ = 1 + length x" 
| "m_bad_app [] y _ = length y"     
| "m_bad_app x y acc = 2 + length x + length acc" 

lemma bad_app_measure_1:
  assumes "x ≠ []" and "y = []"
  shows "m_bad_app y x acc < m_bad_app x y acc"
  using assms by (cases x) auto

lemma bad_app_measure_2:
  assumes "x = []" and "y ≠ []"
  shows "m_bad_app x (tl y) (hd y # acc) < m_bad_app x y acc"
  using assms by (cases y; cases "tl y") auto 

lemma bad_app_measure_3:
  assumes "x ≠ []" and "y ≠ []"
  shows "m_bad_app x [] (bad_app acc [] y) < m_bad_app x y acc"
  using assms by (cases x; cases y) auto

lemma bad_app_measure_4:
  assumes "x ≠ []" and "y ≠ []"
  shows "m_bad_app acc [] y < m_bad_app x y acc"
  using assms by (cases x; cases y; cases acc) auto

function bad_app :: "'a list ⇒ 'a list ⇒ 'a list ⇒ 'a list" where
  "bad_app [] [] acc = acc"
| "bad_app (x#xs) [] acc = bad_app [] (x#xs) acc"
| "bad_app [] (y#ys) acc = bad_app [] ys (y # acc)"
| "bad_app (x#xs) (y#ys) acc = bad_app (x#xs) [] (bad_app acc [] (y#ys))"
  by pat_completeness auto

termination bad_app
  apply (relation "measure (λ(x, y, acc). m_bad_app x y acc)")
  apply (rule wf_measure)
  using bad_app_measure_1 apply fastforce
  using bad_app_measure_2 apply fastforce
  using bad_app_measure_4 apply fastforce
  using bad_app_measure_3 apply fastforce
  done

lemma bad_app_nil_nil_acc:
  "bad_app [] [] acc = acc"
  by simp

lemma bad_app_x_nil_acc:
  assumes "x ≠ []"
  shows "bad_app x [] acc = bad_app [] x acc"
  using assms by (cases x) simp_all

lemma bad_app_nil_y_acc:
  "bad_app [] y acc = rev y @ acc"
  by (induction y arbitrary: acc) simp_all

lemma bad_app_cons_y_nil:
  assumes "x ≠ []" and "acc = []"
  shows "bad_app x y acc = rev x @ y"
  using assms
proof (induction x y acc rule: bad_app.induct)
  case (1 acc)
  then show ?case by simp
next
  case (2 x xs acc)
  then show ?case by (simp add: bad_app_nil_y_acc)
next
  case (3 y ys acc)
  then show ?case by simp
next
  case (4 x xs y ys acc)
  then have "acc = []" by simp
  have "bad_app (x # xs) (y # ys) [] = bad_app (x # xs) [] (bad_app [] [] (y # ys))"
    by simp
  also have "... = bad_app (x # xs) [] (y # ys)"
    by simp
  also have "... = bad_app [] (x # xs) (y # ys)"
    by simp
  also have "... = rev (x # xs) @ (y # ys)"
    by (simp add: bad_app_nil_y_acc)
  finally show ?case using "4.prems" by simp
qed

lemma bad_app_x_y_nil:
  "bad_app x y [] = (if x = [] then rev y else rev x @ y)"
  apply (cases x)
  apply (simp add: bad_app_nil_y_acc) 
  apply (simp add: bad_app_cons_y_nil)
  done 

end