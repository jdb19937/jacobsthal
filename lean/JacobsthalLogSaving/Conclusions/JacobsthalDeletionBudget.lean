import OAI.NumberTheory.Jacobsthal.Conclusions.JacobsthalProgressionLength

namespace JacobsthalLogSaving
open OAI


namespace Erdos970
open OAI.Erdos970

namespace NumberTheoryLean.JacobsthalDeletionBudget
open OAI.Erdos970.NumberTheoryLean
open ProgressionSieve

/-- The deletion budget in terms of `Y`: with `T ≤ Y/(xl) + 1` and `log T ≥ l/2`,
`x·deletionBudget ≤ 255(3x + 2Y/l²)`. -/
theorem source_deletion_budget_cutoff {x l : ℝ} (hx : 0 < x) (hl : 1 ≤ l) (Y Z : ℕ)
    (hT : (progressionLength Y Z:ℝ) ≤ (Y:ℝ)/(x*l)+1)
    (hlog : l/2 ≤ Real.log (progressionLength Y Z:ℝ)) :
    x*deletionBudget Y Z ≤ 255*(3*x+2*(Y:ℝ)/l^2) := by
  have hl0 : 0 < l := by linarith
  have hlog0 : 0 < Real.log (progressionLength Y Z:ℝ) := by linarith
  have hquot : (progressionLength Y Z:ℝ)/Real.log (progressionLength Y Z:ℝ) ≤
      ((Y:ℝ)/(x*l)+1)/(l/2) := by
    calc
      _ ≤ ((Y:ℝ)/(x*l)+1)/Real.log (progressionLength Y Z:ℝ) :=
        div_le_div_of_nonneg_right hT hlog0.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hlog
  have hxl : x/l ≤ x := div_le_self hx.le hl
  have heq : x*(((Y:ℝ)/(x*l)+1)/(l/2)) = 2*(Y:ℝ)/l^2+2*(x/l) := by
    field_simp <;> ring
  unfold deletionBudget
  calc
    _ = 255*(x+x*((progressionLength Y Z:ℝ)/Real.log (progressionLength Y Z:ℝ))) := by ring
    _ ≤ 255*(x+x*(((Y:ℝ)/(x*l)+1)/(l/2))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 255)
      have := mul_le_mul_of_nonneg_left hquot hx.le
      linarith
    _ = 255*(x+(2*(Y:ℝ)/l^2+2*(x/l))) := by rw [heq]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 255)
      linarith
end NumberTheoryLean.JacobsthalDeletionBudget


end Erdos970

end JacobsthalLogSaving
