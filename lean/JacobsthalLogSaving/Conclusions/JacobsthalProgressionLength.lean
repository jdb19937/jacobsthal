import OAI.NumberTheory.Jacobsthal.Conclusions.JacobsthalProgressionLength

namespace JacobsthalLogSaving
open OAI


namespace Erdos970
open OAI.Erdos970

namespace NumberTheoryLean.JacobsthalProgressionLength
open OAI.Erdos970.NumberTheoryLean OAI.Erdos970.NumberTheoryLean.JacobsthalProgressionLength
open ProgressionSieve OAI.Erdos970.NumberTheoryLean.JacobsthalProgressionLength

/-- Progression-length bounds at the raised cutoff: the interval length satisfies
`x²/(16 t) ≤ Y ≤ x²/t` with `1 ≤ t ≤ l` (`t = l^θ`). -/
theorem source_progression_bounds_cutoff {x l t : ℝ} (hx : 4 ≤ x) (hl : 2 ≤ l)
    (hlx : l^2 ≤ x) (ht1 : 1 ≤ t) (htl : t ≤ l) (Y Z : ℕ)
    (hYlo : x^2/(16*t) ≤ (Y:ℝ)) (hYhi : (Y:ℝ) ≤ x^2/t)
    (hZlo : x*l/2 ≤ (Z:ℝ)) (hZhi : (Z:ℝ)+1 ≤ 2*x*l)
    (hZstrict : x*l < (Z:ℝ)+1) :
    x/(32*l^2) ≤ (progressionLength Y Z:ℝ) ∧
      (progressionLength Y Z:ℝ) ≤ (Y:ℝ)/(x*l)+1 ∧
      (progressionLength Y Z:ℝ) ≤ 2*x/l ∧ progressionLength Y Z ≤ Z := by
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < l := by linarith
  have ht0 : 0 < t := by linarith
  have hZ0 : (0:ℝ) < (Z:ℝ)+1 := by positivity
  have hT := progression_real_bounds Y Z
  have hlo : x/(32*l^2) ≤ (progressionLength Y Z:ℝ) := by
    calc
      _ ≤ x/(32*t*l) := div_le_div_of_nonneg_left hx0.le (by positivity) (by nlinarith)
      _ = (x^2/(16*t))/(2*x*l) := by field_simp <;> ring
      _ ≤ (x^2/(16*t))/((Z:ℝ)+1) :=
        div_le_div_of_nonneg_left (by positivity) hZ0 hZhi
      _ ≤ (Y:ℝ)/((Z:ℝ)+1) := div_le_div_of_nonneg_right hYlo hZ0.le
      _ ≤ _ := hT.1
  have hmid : (progressionLength Y Z:ℝ) ≤ (Y:ℝ)/(x*l)+1 := by
    have hh := div_le_div_of_nonneg_left (Nat.cast_nonneg Y) (mul_pos hx0 hl0) hZstrict.le
    linarith [hT.2]
  have hhi : (progressionLength Y Z:ℝ) ≤ 2*x/l := by
    have hlx' : l ≤ x := by nlinarith
    have hone : 1 ≤ x/l := (one_le_div hl0).mpr hlx'
    have hYx : (Y:ℝ)/(x*l) ≤ x/l := by
      calc
        _ ≤ (x^2/t)/(x*l) := div_le_div_of_nonneg_right hYhi (by positivity)
        _ = (x/l)/t := by field_simp <;> ring
        _ ≤ x/l := div_le_self (by positivity) ht1
    calc
      _ ≤ (Y:ℝ)/(x*l)+1 := hmid
      _ ≤ x/l+1 := by linarith
      _ ≤ 2*(x/l) := by linarith
      _ = _ := by ring
  refine ⟨hlo,hmid,hhi,?_⟩
  have hbound : 2*x/l ≤ x*l/2 := by
    apply (div_le_iff₀ hl0).mpr
    nlinarith
  exact_mod_cast hhi.trans (hbound.trans hZlo)

theorem progression_log_lower_cutoff {x l : ℝ} (hx : 0 < x) (hl : 0 < l)
    (hlarge : 32*l^2 ≤ Real.sqrt x) (Y Z : ℕ)
    (hT : x/(32*l^2) ≤ (progressionLength Y Z:ℝ)) :
    Real.log x/2 ≤ Real.log (progressionLength Y Z:ℝ) := by
  have hs : Real.sqrt x ≤ x/(32*l^2) := by
    apply (le_div_iff₀ (by positivity : 0 < 32*l^2)).mpr
    have hh := mul_le_mul_of_nonneg_left hlarge (Real.sqrt_nonneg x)
    nlinarith [Real.sq_sqrt hx.le]
  have hh := Real.log_le_log (Real.sqrt_pos.mpr hx) (hs.trans hT)
  simpa only [Real.log_sqrt hx.le] using hh
end NumberTheoryLean.JacobsthalProgressionLength


end Erdos970

end JacobsthalLogSaving
