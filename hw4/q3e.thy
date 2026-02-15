theory q3e
  imports Main
begin

section ‹Data Types›

type_synonym var = string

datatype if_atom = Bool bool | Var var

datatype norm_if_expr = 
  NAtom if_atom 
| NIfExpr if_atom norm_if_expr norm_if_expr

type_synonym if_assign = "(var × bool) list"

section ‹Lookup Functions›

fun lookup_var :: "var ⇒ if_assign ⇒ bool" where
  "lookup_var v [] = False"
| "lookup_var v ((x, val) # rest) = (if v = x then val else lookup_var v rest)"

fun lookup_atom :: "if_atom ⇒ if_assign ⇒ bool" where
  "lookup_atom (Bool b) _ = b"
| "lookup_atom (Var v) a = lookup_var v a"

section ‹Evaluation Function›

fun if_eval :: "norm_if_expr ⇒ if_assign ⇒ bool" where
  "if_eval (NAtom e) a = lookup_atom e a"
| "if_eval (NIfExpr x y z) a = (if lookup_atom x a then if_eval y a else if_eval z a)"

section ‹Assigned Predicate›

fun assignedp :: "if_atom ⇒ if_assign ⇒ bool" where
  "assignedp (Bool _) _ = True"
| "assignedp (Var v) a = (v ∈ set (map fst a))"

section ‹Validity Checker›

fun validp :: "norm_if_expr ⇒ if_assign ⇒ bool" where
  "validp (NAtom e) a = lookup_atom e a"
| "validp (NIfExpr x y z) a = 
    (if assignedp x a 
     then (if lookup_atom x a then validp y a else validp z a)
     else (case x of 
             Bool _ ⇒ False  ― ‹Should not happen since Bool is always assigned›
           | Var v ⇒ validp y ((v, True) # a) ∧ validp z ((v, False) # a)))"

section ‹Helper Lemmas›

lemma lookup_var_append:
  "lookup_var v (a @ b) = (if v ∈ set (map fst a) then lookup_var v a else lookup_var v b)"
proof (induction a)
  case Nil
  then show ?case by simp
next
  case (Cons p rest)
  obtain x val where p_def: "p = (x, val)" by fastforce
  then show ?case using Cons by auto
qed

lemma lookup_var_true_implies_in_fst:
  "lookup_var v a ⟹ v ∈ set (map fst a)"
proof (induction a)
  case Nil
  then show ?case by simp
next
  case (Cons p rest)
  obtain x val where p_def: "p = (x, val)" by fastforce
  then show ?case using Cons by (cases "v = x") auto
qed

lemma lookup_atom_true_implies_assigned:
  "lookup_atom e a ⟹ assignedp e a"
  by (cases e) (auto dest: lookup_var_true_implies_in_fst)

lemma lookup_atom_append:
  "lookup_atom e (a @ b) = (if assignedp e a then lookup_atom e a else lookup_atom e b)"
  by (cases e) (auto simp: lookup_var_append)

section ‹Soundness of validp›

theorem validp_sound:
  "validp e a ⟹ if_eval e (a @ b)"
proof (induction e a arbitrary: b rule: validp.induct)
  case (1 e a)
  then have "lookup_atom e a" by simp
  then have "assignedp e a" by (rule lookup_atom_true_implies_assigned)
  then have "lookup_atom e (a @ b) = lookup_atom e a" 
    by (simp add: lookup_atom_append)
  with ‹lookup_atom e a› show ?case by simp
next
  case (2 x y z a)
  show ?case
  proof (cases "assignedp x a")
    case True
    then show ?thesis
    proof (cases "lookup_atom x a")
      case True
      with ‹assignedp x a› have "validp y a" 
        using "2.prems" by simp
      then have "if_eval y (a @ b)" 
        using "2.IH"(1) ‹assignedp x a› True by simp
      moreover have "lookup_atom x (a @ b)" 
        using True ‹assignedp x a› lookup_atom_append by simp
      ultimately show ?thesis by simp
    next
      case False
      with ‹assignedp x a› have "validp z a" 
        using "2.prems" by simp
      then have "if_eval z (a @ b)" 
        using "2.IH"(2) ‹assignedp x a› False by simp
      moreover have "¬ lookup_atom x (a @ b)" 
        using False ‹assignedp x a› lookup_atom_append by simp
      ultimately show ?thesis by simp
    qed
  next
    case False
    then obtain v where x_var: "x = Var v" 
      by (cases x) auto
    from False x_var have v_notin: "v ∉ set (map fst a)" by simp
    from "2.prems" False x_var have 
      valid_y: "validp y ((v, True) # a)" and 
      valid_z: "validp z ((v, False) # a)" 
      by simp_all
    
    have ih_y: "if_eval y (((v, True) # a) @ b)" 
      using "2.IH"(3) False x_var valid_y by simp
    have ih_z: "if_eval z (((v, False) # a) @ b)" 
      using "2.IH"(4) False x_var valid_z by simp
    
    show ?thesis
    proof (cases "lookup_var v (a @ b)")
      case True
      then have "lookup_atom x (a @ b)" using x_var by simp
      moreover have "if_eval y ((v, True) # a @ b)" using ih_y by simp
      moreover have "if_eval y (a @ b) = if_eval y ((v, True) # a @ b)"
        using True v_notin by (metis append_Cons lookup_var_append)
      ultimately show ?thesis by simp
    next
      case False
      then have "¬ lookup_atom x (a @ b)" using x_var by simp
      moreover have "if_eval z ((v, False) # a @ b)" using ih_z by simp
      moreover have "if_eval z (a @ b) = if_eval z ((v, False) # a @ b)"
        using False v_notin by (metis append_Cons lookup_var_append)
      ultimately show ?thesis by simp
    qed
  qed
qed

end
