module

public import Erdos415

/-!
# Bounding the universal strict-pattern length

An increasing length-four block is necessary for universality at every length
at least four. Together with universality at length three, its absence proves
that the maximum universal length equals three.
-/

@[expose] public section

namespace Erdos415

/-- A universal family of blocks of length at least four contains an increasing block
of length four, by restricting the identity pattern to its first four positions. -/
theorem hasIncreasing_four_of_allStrictPatterns {n k : ℕ}
    (h : AllStrictPatterns n k) (hk : 4 ≤ k) : HasIncreasing n 4 := by
  obtain ⟨m, hmn, hm⟩ := h (Equiv.refl (Fin k))
  refine ⟨m, by omega, ?_⟩
  intro i j hij
  let i' : Fin k := ⟨i.val, lt_of_lt_of_le i.isLt hk⟩
  let j' : Fin k := ⟨j.val, lt_of_lt_of_le j.isLt hk⟩
  have hij' : i' < j' := hij
  exact (hm i' j').mpr hij'

/-- Universality at length three and absence of an increasing block of length four
force the finite maximum to equal three. -/
theorem F_eq_three_of_patterns {n : ℕ} (hn : 3 ≤ n)
    (hthree : AllStrictPatterns n 3) (hfour : ¬ HasIncreasing n 4) : F n = 3 := by
  classical
  apply Nat.le_antisymm
  · unfold F
    apply Finset.sup_le
    intro k hk
    have hp : AllStrictPatterns n k := (Finset.mem_filter.mp hk).2
    change k ≤ 3
    by_contra hle
    exact hfour (hasIncreasing_four_of_allStrictPatterns hp (by omega))
  · unfold F
    have hm : 3 ∈ (Finset.range (n + 1)).filter (fun k => AllStrictPatterns n k) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hthree⟩
    exact Finset.le_sup (f := id) hm


/-- The preceding bound specialized to the cutoff 826. -/
theorem F_826_eq_three (hthree : AllStrictPatterns 826 3)
    (hfour : ¬ HasIncreasing 826 4) : F 826 = 3 :=
  F_eq_three_of_patterns (by omega) hthree hfour

end Erdos415
