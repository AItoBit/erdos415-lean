# Submission audit

Checked on 2026-10-08. Outcome: **INCOMPLETE** as a verified-result submission. No full or partial theorem has been proved in the supplied Lean file.

## Statement correspondence

| Mathematical clause | Lean representation | Audit finding |
|---|---|---|
| Consecutive totients beginning at a positive integer | `block m k i = Nat.totient (m + i.val + 1)` | Starts at `m+1`, with `m : ℕ`; covers positive starting integers. |
| A prescribed strict rank pattern | `Realizes m k π` | Ranks attach to positions. Pairwise strict comparisons exclude ties. |
| Every strict permutation appears below a cutoff | `AllStrictPatterns n k` | The starting point depends on the permutation; `m+k ≤ n` is required. |
| Largest universally realized length | `F n` | Restricts to `k ≤ n`; uses the empty block as the zero-length convention. |
| Constant-limit questions | `LiteralConstantQuestion`, `PositiveConstantQuestion` | Distinguished deliberately: allowing zero is weaker than requiring a positive constant. |
| First missing pattern is decreasing | `DecreasingAlwaysMissing` | A qualified cutoff interpretation; does not assert uniqueness. |
| Natural ordering and its frequency | `SameWeakOrder`, `NaturalMostFrequentInDensity` | Weak comparisons encode ties. Density existence is an additional explicit interpretation. |
| Finite example at 826 | `FiniteCounterexample826` | Defines a conjunction; supplies no proof. |

The independent agent found no obvious discrepancy in the strict-pattern definitions. Ambiguous readings remain labeled and are not frozen as uniquely faithful resolutions of the source. At zero, empty universality holds and `F 0` is zero. Real logarithms and division are totalized at small inputs, while the constant questions concern limits at infinity.

## Dependencies

`block → Realizes → AllStrictPatterns → F`.

`block → HasDecreasing, HasIncreasing`.

`F, iterLog → LiteralConstantQuestion, PositiveConstantQuestion`.

`F, HasDecreasing → DecreasingAlwaysMissing`.

`block, SameWeakOrder → weakCount → WeakDensity → NaturalMostFrequentInDensity`.

`F, HasDecreasing, HasIncreasing → FiniteCounterexample826`.

All these nodes are definitions. None is a proved research result.

## Finite evidence

A separate agent ran an exact integer totient sieve through 826. It found all six strict length-three patterns and fifteen of the twenty-four length-four patterns. The increasing length-four pattern was absent. At the decreasing witness `m=822`, the values are `(822, 408, 400, 348)`. The reproducible script is `compute826.py`; the packaging agent also ran it independently with the same assertions.

Downward heredity of universality explains the mathematical inference `F(826)=3`: extend any smaller rank permutation by appending larger ranks, then restrict a realizing block to its initial positions. This argument and the finite enumeration are not proved in Lean here. No finite experiment establishes an asymptotic question.

## Verification and limitations

`lake --wfail build Erdos415` passed with exit status 0 and no warnings on Lean 4.35.0-rc3, Mathlib commit `0db6cb99b412983de54b59ecc1b0b2747542cda3`. The initial supplied documentation described an uncompiled draft. The build exposed one source error, fixed by marking `iterLog` as `noncomputable`, because it uses `Real.log`. Packaging also added the module header and public visibility and narrowed imports. Proposition bodies and quantifiers were preserved.

The supplied file contains no theorem declaration, `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide`. Comments mentioning unproved status are documentation. There is no theorem axiom audit to report because the file proves no theorem.

The sources include manuscript claims and interpretations, not an independently verified full proof. The overall mathematical status is not inferred from this file or from failure to prove anything. Palomar eligibility and author/maintainer identity have not been established for a proved-result submission.
