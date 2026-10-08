import JacobsthalLogSaving.Conclusions.IteratedLogBound

/-!
# Jacobsthal's function beyond the square: a logarithmic saving

Main theorem of the repository (Theorem A of the paper with `θ = 2/25`): there is `C > 0`
such that for every `k ≥ 1` there is `m ≤ C k²/((log 3k)^(2/25) (log log 3k)²)` with the
property that among any `m` consecutive integers one is coprime to every `n` having at most
`k` distinct prime factors.  Equivalently `h(k) ≤ C k² (log 3k)^(-2/25) (log log 3k)^(-2)`
for Jacobsthal's function `h`.

The proof under `JacobsthalLogSaving/` runs the sieve of the vendored development
(`OAI/`, OpenAI's proof of `h(k) ≪ k²/(log log 3k)²`) on an interval of length
`⌊z²/(log z)^(2A)⌋` with `A = 1 + 1/25` instead of `⌊z²/(log z)²⌋`.  Everything the vendored
development proves about the sieve tree is reused unchanged; the files under
`JacobsthalLogSaving/` are those that mention the interval length, with the definition
`ErdosInverseBoxHeight.sourceY` changed, the root-gap limits shifted by `cutoffShift = 2A − 2`,
the positivity margin re-proved from constants certified under `JacobsthalLogSaving/Numerics/`
(`I > 0.3326`, `M_g < 7.1804`), and the final budget comparison redone.
`AxiomCheck.lean` verifies that the theorems below depend only on `propext`,
`Classical.choice` and `Quot.sound`.
-/

namespace JacobsthalLogSaving
open OAI

/-- Theorem A, `θ = 2/25`, with the Jacobsthal property written out. -/
theorem jacobsthal_log_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k → ∃ m : ℕ,
      (∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
        ∀ a : ℤ, ∃ i : ℕ, i < m ∧ (a + i).natAbs.Coprime n) ∧
      (m : ℝ) ≤ C * (k : ℝ) ^ 2 /
        ((Real.log (3 * (k : ℝ))) ^ ((2:ℝ)/25) * (Real.log (Real.log (3 * (k : ℝ)))) ^ 2) := by
  have h := Erdos970.Erdos970Final.jacobsthal_log_saving_cutoffShift
  rw [Erdos970.ErdosInverseBoxHeight.cutoffShift_eq] at h
  obtain ⟨C, hC, hk⟩ := h
  refine ⟨C, hC, fun k hk0 => ?_⟩
  obtain ⟨m, hm, hb⟩ := hk k hk0
  exact ⟨m, hm, hb⟩

end JacobsthalLogSaving
