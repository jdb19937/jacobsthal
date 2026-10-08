import JacobsthalLogSaving.Conclusions.IteratedLogScales
import OAI.NumberTheory.Jacobsthal.Conclusions.JacobsthalFinite

namespace JacobsthalLogSaving
open OAI

namespace Erdos970.NumberTheoryLean.IteratedLogFinite
open OAI.Erdos970 OAI.Erdos970.NumberTheoryLean

open _root_.Filter IteratedLogScales
open scoped BigOperators Topology

theorem log_three_mul_nonneg (k : ℕ) : 0 ≤ Real.log (3 * (k : ℝ)) := by
  rcases Nat.eq_zero_or_pos k with h | h
  · simp [h]
  · exact Real.log_nonneg (by
      have : (1:ℝ) ≤ k := by exact_mod_cast h
      linarith)

/-- Absorb the bounded range of `k` without changing any interval quantifier. -/
theorem of_eventually (θ : ℝ) (hθ : 0 ≤ θ)
    (hlarge : ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∃ m : ℕ, Targets.IsJacobsthalBound k m ∧
        (m : ℝ) ≤ C * (k : ℝ) ^ 2 / ((Real.log (3 * (k : ℝ))) ^ θ * (loglog k) ^ 2)) :
    Targets.JacobsthalLogSavingBound θ := by
  obtain ⟨C, hC, hlarge⟩ := hlarge
  obtain ⟨K, hK⟩ := eventually_atTop.mp hlarge
  let weight : ℕ → ℝ := fun k =>
    (((k + 1) * (k + 1).factorial : ℕ) : ℝ) * ((Real.log (3 * (k : ℝ))) ^ θ * (loglog k) ^ 2)
  let D : ℝ := C + ∑ k ∈ Finset.range K, weight k
  have hw (k : ℕ) : 0 ≤ weight k :=
    mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (log_three_mul_nonneg k) θ) (sq_nonneg _))
  have hCD : C ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => hw k)
  have hD : 0 < D := hC.trans_le hCD
  refine ⟨D, hD, ?_⟩
  intro k hk
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog3 : 0 < Real.log (3 * (k : ℝ)) := Real.log_pos (by linarith)
  have hden : 0 < (Real.log (3 * (k : ℝ))) ^ θ * (loglog k) ^ 2 :=
    mul_pos (Real.rpow_pos_of_pos hlog3 θ) (sq_pos_of_pos (loglog_pos hkR))
  by_cases hKk : K ≤ k
  · obtain ⟨m, hm, hb⟩ := hK k hKk
    refine ⟨m, hm, ?_⟩
    show (m : ℝ) ≤ D * (k : ℝ) ^ 2 / ((Real.log (3 * (k : ℝ))) ^ θ * (loglog k) ^ 2)
    exact hb.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCD (sq_nonneg _)) hden.le)
  · refine ⟨(k + 1) * (k + 1).factorial,
      JacobsthalFinite.factorial_isJacobsthalBound k, ?_⟩
    show (((k + 1) * (k + 1).factorial : ℕ) : ℝ) ≤
      D * (k : ℝ) ^ 2 / ((Real.log (3 * (k : ℝ))) ^ θ * (loglog k) ^ 2)
    apply (le_div_iff₀ hden).mpr
    have hsum : weight k ≤ ∑ i ∈ Finset.range K, weight i :=
      Finset.single_le_sum (fun i _ => hw i) (Finset.mem_range.mpr (by omega))
    have hweight : weight k ≤ D := hsum.trans (by dsimp [D]; linarith)
    have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    calc (((k + 1) * (k + 1).factorial : ℕ) : ℝ) *
          ((Real.log (3 * (k : ℝ))) ^ θ * (loglog k) ^ 2) = weight k := rfl
      _ ≤ D := hweight
      _ ≤ D * (k : ℝ) ^ 2 := le_mul_of_one_le_right hD.le hk2

end Erdos970.NumberTheoryLean.IteratedLogFinite

end JacobsthalLogSaving
