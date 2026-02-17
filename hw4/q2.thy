theory q2
  imports Main 
begin

function ack :: "nat ⇒ nat ⇒ nat" where
  "ack 0 m = Suc m"
| "ack (Suc n) 0 = ack n 1"
| "ack (Suc n) (Suc m) = ack n (ack (Suc n) m)"
  by pat_completeness auto

termination ack
  apply (relation "measures [λ(n, m). n, λ(n, m). m]")
  apply (rule wf_measures)
  apply simp
  apply simp
  apply simp
  done

end