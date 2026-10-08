import JacobsthalLogSaving.Conclusions.IteratedLogBudget
import JacobsthalLogSaving.Conclusions.IteratedLogFinite
import JacobsthalLogSaving.Conclusions.SourceRootCompletion
import OAI.NumberTheory.Jacobsthal.Estimates.RootCutoffSurvivors

namespace JacobsthalLogSaving
open OAI

namespace Erdos970.NumberTheoryLean.IteratedLogBound
open OAI.Erdos970 OAI.Erdos970.NumberTheoryLean

open _root_.Filter IteratedLogScales JacobsthalTerminalScales
open StoppedCountVertex StoppedCountAdapters LogarithmicBinPartition
open RootCutoffSurvivors ProgressionSieve
open ErdosInverseBoxHeight (cutoffShift cutoffShift_nonneg cutoffShift_le_one)
open scoped Topology

/-- From the survivor lower bound at the root of the tree to Theorem A. -/
theorem of_source_root_lower (c : ℝ) (hc : 0 < c)
    (z : ℝ → PrimeHistories.Node)
    (hLower : ∀ᶠ top : ℝ in atTop, ∀ a : ℕ → ℕ,
      c * ((ErdosInverseBoxHeight.sourceY top : ℝ) *
        SmallSieveFinite.smallEuler ⌊ErdosInverseBoxHeight.sourceW top⌋₊ /
        (ErdosInverseBoxHeight.sourceB top) ^ 2) ≤
      countSurvivors (ErdosInverseBoxHeight.sourceY top)
        (LargePrimeDeletion.cutoffPrimes ⌊ErdosInverseBoxHeight.sourceW top⌋₊) a
        (rootVertex (z top) ∅ (sourcePrimeSet (ErdosInverseBoxHeight.sourceW top) top)
          ((ErdosInverseBoxHeight.sourceY top : ℝ) *
            SmallSieveFinite.smallEuler ⌊ErdosInverseBoxHeight.sourceW top⌋₊))) :
    Targets.JacobsthalLogSavingBound cutoffShift := by
  obtain ⟨A, hA, hbudget⟩ := IteratedLogBudget.separation c hc
  have hA0 : 0 < A := by linarith
  have hu := rescale_tendsto A hA
  have hData : ∀ᶠ k : ℝ in atTop,
      ∃ m : ℕ, (∀ k' : ℕ, (k' : ℝ) = k → Targets.IsJacobsthalBound k' m) ∧
        (m : ℝ) ≤ 2 * A ^ 2 * k ^ 2 / ((Real.log (3 * k)) ^ cutoffShift * (loglog k) ^ 2) := by
    filter_upwards [hu.eventually eventual_terminal_numerics,
      hu.eventually terminal_w_le_top,
      hbudget, (terminal_top_tendsto.comp hu).eventually hLower,
      eventual_rescale_lower A hA, eventual_loglog_bounds] with k hn hw hb hl hroot hk
    refine ⟨terminalY (rescale A k), ?_, ?_⟩
    · intro k' hk'
      apply isJacobsthalBound_of_cutoff_lower _ _ k' hn.2.2.2.2.2.2.1
      · exact cutoff_lower_of_root_lower _ hw (z (terminalTop (rescale A k))) hl
      · simpa only [hk', Function.comp_def, terminalY] using hb
    · have hYhi := hn.2.2.2.2.2.1
      have hk0 : 0 < k := by linarith [hk.1]
      have h3k : 1 < 3 * k := by linarith
      have hlog3k : 0 < Real.log (3 * k) := Real.log_pos h3k
      have hroot0 : 0 < Real.sqrt (3 * k) := Real.sqrt_pos.mpr (by linarith)
      have hu0 : 0 < rescale A k := hroot0.trans_le hroot
      have hlu : Real.log (3 * k) / 2 ≤ Real.log (rescale A k) := by
        have := Real.log_le_log hroot0 hroot
        rwa [Real.log_sqrt (show (0:ℝ) ≤ 3 * k by linarith)] at this
      have hpow : (Real.log (3 * k)) ^ cutoffShift / 2 ≤ (Real.log (rescale A k)) ^ cutoffShift := by
        have h0 : 0 ≤ (Real.log (3 * k)) ^ cutoffShift := Real.rpow_nonneg hlog3k.le _
        have hdiv : (Real.log (3 * k) / 2) ^ cutoffShift =
            (Real.log (3 * k)) ^ cutoffShift / (2:ℝ) ^ cutoffShift :=
          Real.div_rpow hlog3k.le (by norm_num) _
        have h2 : (2:ℝ) ^ cutoffShift ≤ 2 := by
          calc (2:ℝ) ^ cutoffShift ≤ (2:ℝ) ^ (1:ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) cutoffShift_le_one
            _ = 2 := Real.rpow_one 2
        have h2pos : 0 < (2:ℝ) ^ cutoffShift := Real.rpow_pos_of_pos (by norm_num) _
        calc (Real.log (3 * k)) ^ cutoffShift / 2 ≤
              (Real.log (3 * k)) ^ cutoffShift / (2:ℝ) ^ cutoffShift :=
              div_le_div_of_nonneg_left h0 h2pos h2
          _ = (Real.log (3 * k) / 2) ^ cutoffShift := hdiv.symm
          _ ≤ _ := Real.rpow_le_rpow (by positivity) hlu cutoffShift_nonneg
      have hpos : 0 < (Real.log (3 * k)) ^ cutoffShift := Real.rpow_pos_of_pos hlog3k _
      have hll0 : 0 < loglog k := hk.2.1
      calc (terminalY (rescale A k) : ℝ) ≤
            (rescale A k) ^ 2 / (Real.log (rescale A k)) ^ cutoffShift := hYhi
        _ ≤ (rescale A k) ^ 2 / ((Real.log (3 * k)) ^ cutoffShift / 2) :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hpow
        _ = 2 * A ^ 2 * k ^ 2 / ((Real.log (3 * k)) ^ cutoffShift * (loglog k) ^ 2) := by
          simp only [rescale, div_pow, mul_pow]
          field_simp <;> ring
  apply IteratedLogFinite.of_eventually cutoffShift cutoffShift_nonneg
  refine ⟨2 * A ^ 2, by positivity, ?_⟩
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ))
    atTop atTop).eventually hData] with k hk
  obtain ⟨m, hm, hb⟩ := hk
  exact ⟨m, hm k rfl, hb⟩

end Erdos970.NumberTheoryLean.IteratedLogBound

namespace Erdos970.Erdos970Final
open OAI.Erdos970

/-- Theorem A at the cutoff `z²/(log z)^(2A)`, `A = 1 + 1/25`: the saving exponent is
`cutoffShift = 2/25`. -/
theorem jacobsthal_log_saving_cutoffShift :
    NumberTheoryLean.Targets.JacobsthalLogSavingBound ErdosInverseBoxHeight.cutoffShift := by
  obtain ⟨c, hc, hLower⟩ := source_root_survivor_lower
  exact NumberTheoryLean.IteratedLogBound.of_source_root_lower c hc
    (ErdosCorrectionLimit.sourceRootNode (1 / 100)) hLower

end Erdos970.Erdos970Final

end JacobsthalLogSaving
