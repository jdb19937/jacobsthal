import JacobsthalLogSaving.Numerics.Gamma
import JacobsthalLogSaving.Numerics.FourthLoss

/-!
# The margin `1/100 + θ < 2·signedCoefficientI / costMass` for `θ = 1/20`

Certified constants: `costMass < 7.1804` (from `exp γ < 1.7951`) and `signedCoefficientI > 0.3326`
(from the exact values of the first four omission loss terms and the vendored factorial majorant for
the rest, all evaluated with Mathlib's nine-digit bounds on `log 2`).
-/

namespace JacobsthalLogSaving.Numerics

open Set MeasureTheory
open OAI.Erdos970 OAI.Erdos970.ErdosContinuousOmission OAI.Erdos970.ErdosOmissionBindings
open OAI.Erdos970.ErdosOmissionTail OAI.Erdos970.ErdosBoundaryIntegral
open JacobsthalLogSaving.Erdos970.ErdosOmissionBindings JacobsthalLogSaving.Erdos970.ErdosOmissionTail
open OAI.Erdos970.Erdos970Dependency.InvariantCostBound

/-- The factorial majorant of the vendored development, shifted by one index. -/
theorem omission_factorial_bound_shift (n : ℕ) :
    omissionLossTerm (n+4) ≤ (1:ℝ)/2*(3/Real.log 2-2)*weightedExpTerm (Real.log 2) (n+5) := by
  have h := actual_omission_factorial_bound (n+1)
  rwa [show n+1+3 = n+4 by omega, show n+1+4 = n+5 by omega] at h

theorem weighted_tail_five_hasSum :
    HasSum (fun n : ℕ => weightedExpTerm (Real.log 2) (n+5))
      (1+2*Real.log 2-(5:ℝ)/2*(Real.log 2)^2-(8:ℝ)/3*(Real.log 2)^3-(25:ℝ)/24*(Real.log 2)^4) := by
  have hh := (hasSum_nat_add_iff' 5).mpr (weightedExpTerm_hasSum (Real.log 2))
  rw [Real.exp_log (by norm_num : (0:ℝ)<2)] at hh
  convert! hh using 1
  norm_num [weightedExpTerm,expTerm,Finset.sum_range_succ]
  ring

theorem weighted_tail_five_lt :
    1+2*Real.log 2-(5:ℝ)/2*(Real.log 2)^2-(8:ℝ)/3*(Real.log 2)^3-(25:ℝ)/24*(Real.log 2)^4
      < (5665:ℝ)/100000 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  have e2 : (0.6931471803:ℝ) ^ 2 < Real.log 2 ^ 2 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have e3 : (0.6931471803:ℝ) ^ 3 < Real.log 2 ^ 3 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have e4 : (0.6931471803:ℝ) ^ 4 < Real.log 2 ^ 4 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  norm_num at e2 e3 e4 ⊢
  linarith

theorem mean_factor_lt : (1:ℝ)/2*(3/Real.log 2-2) < (11641:ℝ)/10000 := by
  have h1 := Real.log_two_gt_d9
  have hpos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h : 3/Real.log 2 < (43282:ℝ)/10000 := (div_lt_iff₀ hpos).mpr (by norm_num at h1 ⊢; linarith)
  linarith

/-- Tail of the omission loss series from the fifth term on. -/
theorem omission_tail_four_lt : (∑' n : ℕ, omissionLossTerm (n+4)) < (66:ℝ)/1000 := by
  have hl : Summable (fun n : ℕ => omissionLossTerm (n+4)) :=
    actual_loss_summable.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hu := weighted_tail_five_hasSum.summable.mul_left ((1:ℝ)/2*(3/Real.log 2-2))
  have hh := hl.tsum_le_tsum omission_factorial_bound_shift hu
  rw [tsum_mul_left, weighted_tail_five_hasSum.tsum_eq] at hh
  refine hh.trans_lt ?_
  have hC0 : 0 < (1:ℝ)/2*(3/Real.log 2-2) := by
    have := log_two_mean_factor_bounds.1
    positivity
  have hT0 : 0 ≤ 1+2*Real.log 2-(5:ℝ)/2*(Real.log 2)^2-(8:ℝ)/3*(Real.log 2)^3
      -(25:ℝ)/24*(Real.log 2)^4 :=
    weighted_tail_five_hasSum.nonneg (fun n => by unfold weightedExpTerm expTerm; positivity)
  have hm := mul_lt_mul'' mean_factor_lt weighted_tail_five_lt hC0.le hT0
  linarith

theorem second_third_loss_lt :
    omissionLossTerm 1 + omissionLossTerm 2 < (11316:ℝ)/10000 := by
  rw [actual_second_loss_value, actual_third_loss_value]
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  have e2 : (0.6931471803:ℝ) ^ 2 < Real.log 2 ^ 2 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  norm_num at e2 h1 h2 ⊢
  linarith

theorem first_four_loss_lt :
    (∑ n ∈ Finset.range 4, omissionLossTerm n) < (22680:ℝ)/10000 := by
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  rw [actual_first_loss_eq_one, fourth_loss_value]
  linarith [second_third_loss_lt, L4value_lt]

/-- `signedCoefficientI > 0.3326` (the crude vendored bound is `11/75 ≈ 0.1467`). -/
theorem signedCoefficientI_gt : (3326:ℝ)/10000 < signedCoefficientI := by
  have hfirst := first_four_loss_lt
  have htail := omission_tail_four_lt
  have hsplit := actual_loss_summable.sum_add_tsum_nat_add 4
  have htotal := actual_signed_loss_series
  linarith

/-- The margin needed for a logarithmic saving `θ = 1/20`, with slack `1/1000`. -/
theorem margin_one_twentieth :
    (1:ℝ)/100 + 1/20 + 1/1000 <
      2*OAI.Erdos970.ErdosBoundaryIntegral.signedCoefficientI/
        OAI.Erdos970.Erdos970Dependency.InvariantCostBound.costMass := by
  apply (lt_div_iff₀ costMass_pos).mpr
  nlinarith [signedCoefficientI_gt, costMass_lt, costMass_pos]

end JacobsthalLogSaving.Numerics

#print axioms JacobsthalLogSaving.Numerics.margin_one_twentieth
#print axioms JacobsthalLogSaving.Numerics.signedCoefficientI_gt
#print axioms JacobsthalLogSaving.Numerics.costMass_lt
