import OAI.NumberTheory.Jacobsthal.Conclusions.JacobsthalSourceRounding

namespace JacobsthalLogSaving
open OAI


namespace Erdos970
open OAI.Erdos970

namespace NumberTheoryLean.JacobsthalSurvivorScale
open OAI.Erdos970.NumberTheoryLean

/-- The survivor lower bound `c·Y·V₀/B²` in terms of `Y`, `log w` and `l = log x`, where
`B = L/log w` with `l ≤ L ≤ 2l`. -/
theorem normalized_scale_lower_cutoff {l L w V0 Y c0 : ℝ}
    (hl : 0 < l) (hlL : l ≤ L) (hLl : L ≤ 2*l)
    (hw : 1 < w) (hc0 : 0 < c0) (hY : 0 ≤ Y) (hV : c0/Real.log w ≤ V0) :
    c0*Y*Real.log w/(4*l^2) ≤ Y*V0/(L/Real.log w)^2 := by
  have hL : 0 < L := hl.trans_le hlL
  have hlog : 0 < Real.log w := Real.log_pos hw
  have hdiv : L/Real.log w ≤ (2*l)/Real.log w := div_le_div_of_nonneg_right hLl hlog.le
  have hdl : 0 < L/Real.log w := div_pos hL hlog
  have hdu : 0 < (2*l)/Real.log w := by positivity
  have hsq : (L/Real.log w)^2 ≤ ((2*l)/Real.log w)^2 := by nlinarith
  have hnum : Y*(c0/Real.log w) ≤ Y*V0 := mul_le_mul_of_nonneg_left hV hY
  calc
    _ = (Y*(c0/Real.log w))/((2*l)/Real.log w)^2 := by
      field_simp [hl.ne',hlog.ne'] <;> ring
    _ ≤ (Y*(c0/Real.log w))/(L/Real.log w)^2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hdl) hsq
    _ ≤ _ := div_le_div_of_nonneg_right hnum (sq_nonneg _)
end NumberTheoryLean.JacobsthalSurvivorScale


end Erdos970

end JacobsthalLogSaving
