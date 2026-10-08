import JacobsthalLogSaving.Conclusions.IteratedLogScales
import JacobsthalLogSaving.Conclusions.JacobsthalSurvivorScale
import OAI.NumberTheory.Jacobsthal.Sieve.ClosedEulerIndividualUpper

namespace JacobsthalLogSaving
open OAI

namespace Erdos970.NumberTheoryLean.IteratedLogBudget
open OAI.Erdos970 OAI.Erdos970.NumberTheoryLean

open _root_.Filter IteratedLogScales JacobsthalTerminalScales
open JacobsthalLogSaving.Erdos970.NumberTheoryLean.JacobsthalSurvivorScale
open JacobsthalLogSaving.Erdos970.NumberTheoryLean.JacobsthalDeletionBudget
open ProgressionSieve
open ErdosInverseBoxHeight (cutoffShift cutoffShift_nonneg cutoffShift_le_one)
open scoped Topology

/-- The deletion loss is smaller than the survivor lower bound once `k` is rescaled to
`u = A k/log log 3k`: the `Y`-proportional part of the budget is beaten by the choice of `A`,
and the `u`-proportional part by `Y ≫ u (log u)³`. -/
theorem separation (c : ℝ) (hc : 0 < c) :
    ∃ A : ℝ, 3 ≤ A ∧ ∀ᶠ k : ℝ in atTop,
      k * deletionBudget (terminalY (rescale A k)) (terminalCutoff (rescale A k)) <
        c * ((terminalY (rescale A k) : ℝ) *
          SmallSieveFinite.smallEuler ⌊ErdosInverseBoxHeight.sourceW
            (terminalTop (rescale A k))⌋₊ /
          (ErdosInverseBoxHeight.sourceB (terminalTop (rescale A k))) ^ 2) := by
  let c0 : ℝ := Real.exp (-Real.eulerMascheroniConstant) / 2
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  let A : ℝ := max 3 (16320 / (c * c0))
  have hA : 3 ≤ A := le_max_left _ _
  have hA0 : 0 < A := by linarith
  have hAb : 16320 ≤ A * (c * c0) :=
    (div_le_iff₀ (mul_pos hc hc0)).mp (le_max_right _ _)
  refine ⟨A, hA, ?_⟩
  have hu := rescale_tendsto A hA
  have hWT := terminal_w_tendsto.comp hu
  let Kc : ℝ := 783360 / (c * c0 * A)
  have hKc : 0 < Kc := by dsimp [Kc]; positivity
  have hcube := (isLittleO_log_rpow_rpow_atTop (3:ℝ) (s := 1) (by norm_num)).bound
    (inv_pos.mpr hKc)
  filter_upwards [hu.eventually eventual_terminal_numerics,
    hu.eventually eventual_terminal_logs,
    hWT.eventually ErdosInverseEuler.smallEuler_log_bounds,
    eventual_loglog_bounds, eventual_loglog_le_logW A hA,
    hu.eventually hcube] with k hn hl he hk hll hcube
  let u := rescale A k
  let w := ErdosInverseBoxHeight.sourceW (terminalTop u)
  obtain ⟨hx, hlog, _hlogs, _hTop, hYlo, _hYhi, _hTcut, hTle, hTL⟩ := hn
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hlog0 : 0 < Real.log u := by linarith
  have hlog1 : 1 ≤ Real.log u := by linarith
  have hl2 : 0 < (Real.log u)^2 := by positivity
  have hw2 : 2 ≤ w := he.1
  have hw1 : 1 < w := by linarith
  have hlogw : 0 < Real.log w := Real.log_pos hw1
  have hV : c0 / Real.log w ≤ SmallSieveFinite.smallEuler ⌊w⌋₊ := by
    calc
      _ = Real.exp (-Real.eulerMascheroniConstant) / (2 * Real.log w) := by
        dsimp [c0]
        ring
      _ ≤ _ := he.2.2.1
  have hY0 : (0:ℝ) ≤ (terminalY u : ℝ) := Nat.cast_nonneg _
  have hscale := normalized_scale_lower_cutoff hlog0 hl.2.2.2.2.1 hl.2.2.2.2.2 hw1 hc0 hY0 hV
  have hbudget := source_deletion_budget_cutoff hu0 hlog1 (terminalY u) (terminalCutoff u) hTle hTL
  have ht := cutoff_power_bounds hlog1
  have hYlo' : u^2/(16*Real.log u) ≤ (terminalY u : ℝ) := by
    calc u^2/(16*Real.log u) ≤ u^2/(16*(Real.log u)^cutoffShift) :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith [ht.2])
      _ ≤ _ := hYlo
  have hcube' : Kc*(Real.log u)^3 ≤ u := by
    have h := hcube
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_one, abs_of_pos hu0,
      abs_of_nonneg (Real.rpow_nonneg hlog0.le _)] at h
    have h3 : (Real.log u)^((3:ℝ)) = (Real.log u)^3 := by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [h3] at h
    exact (le_inv_mul_iff₀ hKc).mp h
  -- the `Y`-proportional term
  have hterm2 : (4*Real.log w/A)*(255*(2*(terminalY u:ℝ)/(Real.log u)^2)) ≤
      c*c0*(terminalY u:ℝ)*Real.log w/(8*(Real.log u)^2) := by
    rw [show (4*Real.log w/A)*(255*(2*(terminalY u:ℝ)/(Real.log u)^2)) =
        (2040/A)*((terminalY u:ℝ)*Real.log w/(Real.log u)^2) by ring,
      show c*c0*(terminalY u:ℝ)*Real.log w/(8*(Real.log u)^2) =
        (c*c0/8)*((terminalY u:ℝ)*Real.log w/(Real.log u)^2) by ring]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [div_le_div_iff₀ hA0 (by norm_num)]
    have hcomm : c*c0*A = A*(c*c0) := by ring
    rw [hcomm]
    linarith
  -- the `u`-proportional term
  have hterm1 : (4*Real.log w/A)*(255*(3*u)) <
      c*c0*(terminalY u:ℝ)*Real.log w/(8*(Real.log u)^2) := by
    have hYbig : 24480*u*(Real.log u)^2/(c*c0*A) < (terminalY u:ℝ) := by
      have h2 : u*(Kc*(Real.log u)^3)/(16*Real.log u) ≤ u^2/(16*Real.log u) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        calc u*(Kc*(Real.log u)^3) ≤ u*u := mul_le_mul_of_nonneg_left hcube' hu0.le
          _ = u^2 := (sq u).symm
      have h3 : u*(Kc*(Real.log u)^3)/(16*Real.log u) = 48960*u*(Real.log u)^2/(c*c0*A) := by
        dsimp [Kc]
        field_simp <;> ring
      have h4 : 24480*u*(Real.log u)^2/(c*c0*A) < 48960*u*(Real.log u)^2/(c*c0*A) := by
        apply div_lt_div_of_pos_right _ (by positivity)
        have hpos : 0 < u*(Real.log u)^2 := mul_pos hu0 hl2
        linarith
      linarith [hYlo']
    rw [show (4*Real.log w/A)*(255*(3*u)) = (3060*u/A)*Real.log w by ring,
      show c*c0*(terminalY u:ℝ)*Real.log w/(8*(Real.log u)^2) =
        (c*c0*(terminalY u:ℝ)/(8*(Real.log u)^2))*Real.log w by ring]
    apply mul_lt_mul_of_pos_right _ hlogw
    rw [div_lt_div_iff₀ hA0 (by positivity)]
    have h := (div_lt_iff₀ (by positivity : 0 < c*c0*A)).mp hYbig
    have e1 : 3060*u*(8*(Real.log u)^2) = 24480*u*(Real.log u)^2 := by ring
    have e2 : c*c0*(terminalY u:ℝ)*A = (terminalY u:ℝ)*(c*c0*A) := by ring
    rw [e1, e2]
    exact h
  have hnonneg : 0 ≤ 255*(3*u+2*(terminalY u:ℝ)/(Real.log u)^2) := by positivity
  calc
    k * deletionBudget (terminalY u) (terminalCutoff u) =
        (loglog k / A) * (u * deletionBudget (terminalY u) (terminalCutoff u)) := by
      dsimp [u, rescale]
      field_simp [hA0.ne', hk.2.1.ne']
    _ ≤ (loglog k / A) * (255*(3*u+2*(terminalY u:ℝ)/(Real.log u)^2)) :=
      mul_le_mul_of_nonneg_left hbudget (div_pos hk.2.1 hA0).le
    _ ≤ (4*Real.log w/A) * (255*(3*u+2*(terminalY u:ℝ)/(Real.log u)^2)) := by
      apply mul_le_mul_of_nonneg_right _ hnonneg
      exact div_le_div_of_nonneg_right hll hA0.le
    _ = (4*Real.log w/A)*(255*(3*u)) + (4*Real.log w/A)*(255*(2*(terminalY u:ℝ)/(Real.log u)^2)) := by
      ring
    _ < c*c0*(terminalY u:ℝ)*Real.log w/(8*(Real.log u)^2) +
        c*c0*(terminalY u:ℝ)*Real.log w/(8*(Real.log u)^2) := by linarith [hterm1, hterm2]
    _ = c*(c0*(terminalY u:ℝ)*Real.log w/(4*(Real.log u)^2)) := by ring
    _ ≤ c*((terminalY u : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊/
        (Real.log (terminalTop u)/Real.log w)^2) :=
      mul_le_mul_of_nonneg_left hscale hc.le
    _ = _ := rfl

end Erdos970.NumberTheoryLean.IteratedLogBudget

end JacobsthalLogSaving
