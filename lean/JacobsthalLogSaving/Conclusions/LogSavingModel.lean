import OAI.NumberTheory.Jacobsthal.Model

namespace JacobsthalLogSaving
open OAI

namespace Erdos970.NumberTheoryLean.Targets
open OAI.Erdos970 OAI.Erdos970.NumberTheoryLean OAI.Erdos970.NumberTheoryLean.Targets

/-- Theorem A with saving exponent `θ`: there is `C > 0` such that for every `k ≥ 1` some
`m ≤ C k²/((log 3k)^θ (log log 3k)²)` is a Jacobsthal bound for `k`, i.e. every `m`
consecutive integers contain one coprime to any `n` with at most `k` distinct prime factors. -/
def JacobsthalLogSavingBound (θ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
    ∃ m : ℕ, IsJacobsthalBound k m ∧
      (m : ℝ) ≤ C * (k : ℝ) ^ 2 /
        ((Real.log (3 * (k : ℝ))) ^ θ * (Real.log (Real.log (3 * (k : ℝ)))) ^ 2)

end Erdos970.NumberTheoryLean.Targets

end JacobsthalLogSaving
