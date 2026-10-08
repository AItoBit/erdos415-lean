module

public import Erdos415
public import Certificate
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Perm

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-!
# Finite totient pattern proofs for Erdős Problem 415

Six explicit blocks realize the strict patterns of length three. The block
starting at 823 is decreasing, and the certified table excludes every increasing
block of length four up to 826. The exhaustive checks use `decide +kernel`.
-/

namespace Erdos415
open Certificate

theorem realizes_iff_lookup (m : ℕ) (hm : m + 3 ≤ 826) (π : Equiv.Perm (Fin 3)) :
    Realizes m 3 π ↔ ∀ i j : Fin 3,
      values[m + i.val + 1]?.getD 0 < values[m + j.val + 1]?.getD 0 ↔ π i < π j := by
  unfold Realizes block
  apply forall_congr'
  intro i
  apply forall_congr'
  intro j
  rw [values_correct _ (by omega), values_correct _ (by omega)]

theorem AllStrictPatterns826_3 : AllStrictPatterns 826 3 := by
  intro π
  fin_cases π <;> first
  | exact ⟨104, by norm_num, (realizes_iff_lookup _ (by norm_num) _).mpr (by decide +kernel)⟩
  | exact ⟨5, by norm_num, (realizes_iff_lookup _ (by norm_num) _).mpr (by decide +kernel)⟩
  | exact ⟨4, by norm_num, (realizes_iff_lookup _ (by norm_num) _).mpr (by decide +kernel)⟩
  | exact ⟨15, by norm_num, (realizes_iff_lookup _ (by norm_num) _).mpr (by decide +kernel)⟩
  | exact ⟨12, by norm_num, (realizes_iff_lookup _ (by norm_num) _).mpr (by decide +kernel)⟩
  | exact ⟨312, by norm_num, (realizes_iff_lookup _ (by norm_num) _).mpr (by decide +kernel)⟩

theorem decreasing826 : HasDecreasing 826 4 := by
  refine ⟨822, by norm_num, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    norm_num [block, phi_823, phi_824, phi_825, phi_826] at *

theorem table_no_increasing : ∀ m : Fin 823,
    ¬(values[m.val + 1]?.getD 0 < values[m.val + 2]?.getD 0 ∧
      values[m.val + 2]?.getD 0 < values[m.val + 3]?.getD 0 ∧
      values[m.val + 3]?.getD 0 < values[m.val + 4]?.getD 0) := by
  decide +kernel

theorem noIncreasing826 : ¬ HasIncreasing 826 4 := by
  rintro ⟨m, hm, h⟩
  apply table_no_increasing ⟨m, by omega⟩
  have h01 := h 0 1 (by decide)
  have h12 := h 1 2 (by decide)
  have h23 := h 2 3 (by decide)
  change Nat.totient (m + 1) < Nat.totient (m + 2) at h01
  change Nat.totient (m + 2) < Nat.totient (m + 3) at h12
  change Nat.totient (m + 3) < Nat.totient (m + 4) at h23
  rw [values_correct _ (by omega), values_correct _ (by omega)] at h01 h12 h23
  exact ⟨h01, h12, h23⟩
end Erdos415
