import OAI.NumberTheory.Jacobsthal.Estimates.OnePairCost

/-!
# Sharper numerical bounds on `exp γ` and `costMass`

`γ < eulerMascheroniSeq' 64 = harmonic 64 - 6 log 2`, with `harmonic 64` evaluated exactly and
`log 2` taken from Mathlib's nine-digit bounds; then `exp γ` via a Taylor bound.
-/

namespace JacobsthalLogSaving.Numerics

open Real

theorem harmonic_sixtyfour :
    (harmonic 64 : ℚ) = 623171679694215690971693339/131362987122535807501262400 := by
  norm_num [harmonic, Finset.sum_range_succ]

theorem eulerMascheroniSeq'_sixtyfour :
    eulerMascheroniSeq' 64 =
      (623171679694215690971693339/131362987122535807501262400 : ℝ) - 6 * log 2 := by
  rw [eulerMascheroniSeq', ite_eq_right (by norm_num), harmonic_sixtyfour]
  push_cast
  rw [show (64:ℝ) = 2^6 by norm_num, Real.log_pow]
  push_cast
  ring

theorem eulerMascheroniConstant_lt : eulerMascheroniConstant < 58501/100000 := by
  have h := eulerMascheroniConstant_lt_eulerMascheroniSeq' 64
  rw [eulerMascheroniSeq'_sixtyfour] at h
  have := Real.log_two_gt_d9
  norm_num at this h ⊢
  linarith

theorem exp_eulerMascheroniConstant_lt : exp eulerMascheroniConstant < 17951/10000 := by
  have h1 := Real.exp_lt_exp.mpr eulerMascheroniConstant_lt
  have h2 := Real.exp_bound' (x := 58501/100000) (by norm_num) (by norm_num) (n := 10) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
  norm_num at h2
  linarith

open OAI.Erdos970.NumberTheoryLean.BuchstabBridge in
theorem sieveA_lt : sieveA < 35902/10000 := by
  unfold sieveA
  linarith [exp_eulerMascheroniConstant_lt]

open OAI.Erdos970.Erdos970Dependency.InvariantCostBound in
theorem costMass_lt : costMass < 71804/10000 := by
  have h := costMass_le
  linarith [sieveA_lt]

end JacobsthalLogSaving.Numerics
