module

public import Bounds
public import FiniteProof

/-!
# Certified finite counterexample for Erdős Problem 415

This proves the statements in `Challenge.lean` using certified totient values,
finite enumeration and the universal-pattern bound in `Bounds.lean`.
The result formalizes Przemek Chojecki, *Consecutive Totient Patterns*,
Proposition 1.2: https://www.ulam.ai/research/erdos415-sol.pdf.
-/

@[expose] public section

namespace Erdos415

/-- At cutoff 826 the maximum universal length is three, although a decreasing
block of length four occurs and an increasing block of length four does not. -/
theorem finite_counterexample826 : FiniteCounterexample826 := by
  exact ⟨F_826_eq_three AllStrictPatterns826_3 noIncreasing826,
    decreasing826, noIncreasing826⟩

/-- Decreasing is not always absent at the first non-universal length. -/
theorem not_decreasingAlwaysMissing : ¬ DecreasingAlwaysMissing := by
  intro h
  obtain ⟨hf, hd, _⟩ := finite_counterexample826
  have hmissing := h 826 (by decide)
  rw [hf] at hmissing
  exact hmissing hd

end Erdos415
