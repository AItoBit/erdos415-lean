module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

/-!
# Erdős Problem 415: statement draft

These definitions are proposed statements, not proved theorems or a solution.
The original file was supplied as an uncompiled draft. This project pins a Lean/Mathlib
environment and checks that the definitions elaborate.
Source: https://www.erdosproblems.com/415 and https://www.erdosproblems.com/forum/thread/415.
Related manuscript: Przemek Chojecki, Consecutive Totient Patterns (2026-07-13),
https://www.ulam.ai/research/erdos415-sol.pdf.
The finite counterexample below reproduces that manuscript's Proposition 1.2.
No proof from that manuscript or an existing Lean file is copied here.
-/

namespace Erdos415

open Filter

def block (m k : ℕ) (i : Fin k) : ℕ := Nat.totient (m + i.val + 1)

/-- `π i` is the rank of position `i`, not the position of rank `i`. -/
def Realizes (m k : ℕ) (π : Equiv.Perm (Fin k)) : Prop :=
  ∀ i j : Fin k, block m k i < block m k j ↔ π i < π j

/-- Each permutation may have a different starting point. -/
def AllStrictPatterns (n k : ℕ) : Prop :=
  ∀ π : Equiv.Perm (Fin k), ∃ m : ℕ, m + k ≤ n ∧ Realizes m k π

/-- Include zero as the empty-block convention; maximize only over `k ≤ n`. -/
noncomputable def F (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range (n + 1)).filter (fun k => AllStrictPatterns n k)).sup id

def HasDecreasing (n k : ℕ) : Prop :=
  ∃ m : ℕ, m + k ≤ n ∧
    ∀ i j : Fin k, i < j → block m k j < block m k i

def HasIncreasing (n k : ℕ) : Prop :=
  ∃ m : ℕ, m + k ≤ n ∧
    ∀ i j : Fin k, i < j → block m k i < block m k j

noncomputable def iterLog : ℕ → ℝ → ℝ
  | 0, x => x
  | r + 1, x => Real.log (iterLog r x)

/-- Literal constant question: the source does not explicitly exclude `c = 0`. -/
def LiteralConstantQuestion : Prop :=
  ∃ c : ℝ, Tendsto (fun n : ℕ => (F n : ℝ) / iterLog 3 (n : ℝ)) atTop (nhds c)

/-- Separate positive-leading-constant interpretation. -/
def PositiveConstantQuestion : Prop :=
  ∃ c : ℝ, 0 < c ∧
    Tendsto (fun n : ℕ => (F n : ℝ) / iterLog 3 (n : ℝ)) atTop (nhds c)

/-- A necessary cutoff interpretation of 'the first missing pattern is decreasing'.
It asserts absence of decreasing at the first length lacking universality;
it does not assert that decreasing is the unique missing pattern. -/
def DecreasingAlwaysMissing : Prop :=
  ∀ n : ℕ, 1 ≤ n → ¬ HasDecreasing n (F n + 1)

/-- Pairwise comparisons encode equality as well, since the values are naturals. -/
def SameWeakOrder {k : ℕ} (a b : Fin k → ℕ) : Prop :=
  ∀ i j : Fin k, a i < a j ↔ b i < b j

def naturalPattern (k : ℕ) (i : Fin k) : ℕ := Nat.totient (i.val + 1)

noncomputable def weakCount (n k : ℕ) (a : Fin k → ℕ) : ℕ := by
  classical
  exact ((Finset.range (n + 1)).filter
    (fun m => m + k ≤ n ∧ SameWeakOrder (block m k) a)).card

def WeakDensity (k : ℕ) (a : Fin k → ℕ) (d : ℝ) : Prop :=
  Tendsto (fun n : ℕ => (weakCount n k a : ℝ) / (n : ℝ)) atTop (nhds d)

/-- Chosen density interpretation, not a claim that the source uniquely specifies it.
This formulation additionally requires that every compared density exists. -/
def NaturalMostFrequentInDensity : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ d : ℝ, WeakDensity k (naturalPattern k) d ∧
    ∀ a : Fin k → ℕ, ∃ e : ℝ, WeakDensity k a e ∧ e ≤ d

/-- Computationally reproduced, but not kernel-proved in this file. -/
def FiniteCounterexample826 : Prop :=
  F 826 = 3 ∧ HasDecreasing 826 4 ∧ ¬ HasIncreasing 826 4

end Erdos415
