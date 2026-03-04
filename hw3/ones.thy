theory ones
  imports Main "HOL-Library.Stream"
begin

subsection ‹Define "all elements satisfy predicate p"›

definition all_satisfy :: "('a ⇒ bool) ⇒ 'a stream set" where
  "all_satisfy p = gfp (λS. {s. p (shd s) ∧ stl s ∈ S})"

lemma all_satisfy_mono: "mono (λS. {s. p (shd s) ∧ stl s ∈ S})"
  by (rule monoI) auto

lemma all_satisfy_unfold: 
  "all_satisfy p = {s. p (shd s) ∧ stl s ∈ all_satisfy p}"
  unfolding all_satisfy_def
  by (rule gfp_unfold[OF all_satisfy_mono])

subsection ‹The stream of ones›

primcorec ones :: "nat stream" where
  "shd ones = 1"
| "stl ones = ones"

lemma ones_eq: "ones = SCons 1 ones"
  apply (coinduction rule: stream.coinduct) 
  apply auto
  using ones.code by simp

subsection ‹Proof using coinduction›

text ‹Define our coinductive hypothesis set›

definition is_ones :: "nat stream set" where
  "is_ones = {ones}"

theorem ones_all_one: "ones ∈ all_satisfy (λn. n = 1)"
  unfolding all_satisfy_def
proof -
  let ?f = "λS. {s. shd s = 1 ∧ stl s ∈ S}"
  ― ‹We show is_ones is a post-fixed point: is_ones ⊆ f(is_ones)›
  have "is_ones ⊆ ?f is_ones"
  proof
    fix s assume "s ∈ is_ones"
    hence "s = ones" by (simp add: is_ones_def)
    hence "shd s = 1" and "stl s = ones" by simp_all
    hence "stl s ∈ is_ones" by (simp add: is_ones_def)
    thus "s ∈ ?f is_ones"
      using ‹shd s = 1› by simp
  qed
  hence "is_ones ⊆ gfp ?f" by (rule gfp_upperbound)
  moreover have "ones ∈ is_ones" by (simp add: is_ones_def)
  ultimately show "ones ∈ gfp ?f" by auto
qed

subsection ‹Alternative proof using stream coinduction directly›

lemma snth_ones: "snth ones n = 1"
  by (induction n) simp_all

theorem ones_all_one_v2: "∀n ∈ sset ones. n = 1"
proof -
  have "sset ones = range (snth ones)" by (simp add: sset_range)
  also have "... = {1}" using snth_ones by auto
  finally show ?thesis by simp
qed

subsection ‹Using the stream library's stream_all›

theorem ones_all_one_v3: "stream_all (λn. n = 1) ones"
  using ones_all_one_v2 by (simp add: stream.pred_set)

end
