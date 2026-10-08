module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Perm.Basic

/-!
# A finite counterexample for the strict-pattern reading of Erdős Problem 415

For a cutoff $n$, let $F(n)$ be the largest length $k \leq n$ for which
every strict rank permutation is realized by a block of consecutive totients
ending at or before $n$. Ranks are assigned to positions, and each permutation
may use a different block. The zero-length block supplies the empty convention.

At $n=826$, all six length-three patterns occur, but the increasing length-four
pattern does not. Nevertheless, the decreasing length-four block beginning at
823 occurs. Its totients are $(822,408,400,348)$. Thus $F(826)=3$, and decreasing
is not always absent at the first non-universal length.

This formalizes Przemek Chojecki, *Consecutive Totient Patterns* (2026-07-13),
Proposition 1.2, Section 4 and Appendix A:
https://www.ulam.ai/research/erdos415-sol.pdf.
The original questions and their strict/weak-order ambiguity are recorded at
https://www.erdosproblems.com/415.

This is an existing finite counterexample and a partial negative answer under
the specified strict-pattern interpretation. It makes no novelty claim, no
asymptotic claim, and no claim about natural weak-order frequencies.
The deliberate statement holes below are supplied by the separate Solution.
-/

@[expose] public section

namespace Erdos415

/-- Position `i` in the length-`k` block starting at the positive integer `m+1`. -/
def block (m k : ℕ) (i : Fin k) : ℕ := Nat.totient (m + i.val + 1)

/-- The permutation assigns a strict rank to each position of a block. -/
def Realizes (m k : ℕ) (π : Equiv.Perm (Fin k)) : Prop :=
  ∀ i j : Fin k, block m k i < block m k j ↔ π i < π j

/-- Every strict permutation occurs in a block ending at or before the cutoff. -/
def AllStrictPatterns (n k : ℕ) : Prop :=
  ∀ π : Equiv.Perm (Fin k), ∃ m : ℕ, m + k ≤ n ∧ Realizes m k π

/-- The greatest universal length bounded by the cutoff, including the empty block. -/
noncomputable def F (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range (n + 1)).filter (fun k => AllStrictPatterns n k)).sup id

/-- A strictly decreasing block of length `k` ending at or before `n`. -/
def HasDecreasing (n k : ℕ) : Prop :=
  ∃ m : ℕ, m + k ≤ n ∧
    ∀ i j : Fin k, i < j → block m k j < block m k i

/-- A strictly increasing block of length `k` ending at or before `n`. -/
def HasIncreasing (n k : ℕ) : Prop :=
  ∃ m : ℕ, m + k ≤ n ∧
    ∀ i j : Fin k, i < j → block m k i < block m k j

/-- The necessary cutoff interpretation of decreasing being the first missing pattern.
This asks for absence at the first non-universal length, not uniqueness. -/
def DecreasingAlwaysMissing : Prop :=
  ∀ n : ℕ, 1 ≤ n → ¬ HasDecreasing n (F n + 1)

/-- The source's finite counterexample, stated with the inclusive cutoff 826. -/
def FiniteCounterexample826 : Prop :=
  F 826 = 3 ∧ HasDecreasing 826 4 ∧ ¬ HasIncreasing 826 4

set_option warn.sorry false in
/-- At cutoff 826 the maximum universal length is three, although a decreasing
block of length four occurs and an increasing block of length four does not. -/
theorem finite_counterexample826 : FiniteCounterexample826 := by sorry

set_option warn.sorry false in
/-- Decreasing is not always absent at the first non-universal length. -/
theorem not_decreasingAlwaysMissing : ¬ DecreasingAlwaysMissing := by sorry

end Erdos415
