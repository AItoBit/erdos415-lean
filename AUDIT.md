# Submission audit

Audit date: 2026-10-08. Target: the finite counterexample in Chojecki, Consecutive Totient Patterns (2026-07-13), Proposition 1.2, Section 4 and Appendix A: https://www.ulam.ai/research/erdos415-sol.pdf.

## Frozen statement

| Source clause | Lean representation | Interpretation |
|---|---|---|
| Consecutive positive integers | `block m k i` | First integer `m+1`, last integer `m+k`. |
| Strict rank pattern | `Realizes m k π` | Ranks attach to positions; ties excluded. |
| Every permutation below cutoff | `AllStrictPatterns n k` | Witness depends on permutation; endpoint at most `n`. |
| Largest universal length | `F n` | Length at most `n`; empty length included. |
| Decreasing first missing pattern | `DecreasingAlwaysMissing` | Necessary absence condition at length `F n+1`; no uniqueness claim. |
| Finite counterexample | `FiniteCounterexample826` | `F 826=3`, decreasing length four present, increasing length four absent. |

An independent agent verified source correspondence. All eight shared definitions in Challenge have the same bodies as Erdos415. Source start 823 corresponds to `m=822`. The target was frozen before proof construction and was not weakened. The empty convention gives `F 0=0`.

## Proof dependencies

Mathlib prime/product totient lemmas → `phi_0` … `phi_826` → `values_eq` → `values_correct`.

`values_correct` → six witnesses → `AllStrictPatterns826_3`.

`values_correct` + exhaustive table check over `Fin 823` → `noIncreasing826`.

`phi_823` … `phi_826` → `decreasing826`.

Identity-pattern restriction → `F_eq_three_of_patterns` → `F_826_eq_three`.

`F_826_eq_three`, `decreasing826`, `noIncreasing826` → `finite_counterexample826` → `not_decreasingAlwaysMissing`.

The bound uses the identity permutation restricted to its first four positions. Exhaustive absence covers `m=0,…,822`, precisely all permitted starts. All 827 certified totient values agree with a separate integer sieve. The six length-three witnesses have `m=104,5,4,15,12,312`.

Checks use proved Mathlib arithmetic facts and `decide +kernel`. Implementation modules have no `native_decide`, `sorry`, `admit`, custom axiom, `unsafe`, `implemented_by` or `extern`. Challenge alone has two deliberate holes; Solution does not import it.

## Verification status

Outcome: **PARTIAL RESULT PROVED**. `lake --wfail build Erdos415 Bounds Certificate FiniteProof Solution Challenge` passed with no warnings (2019 jobs). Both submitted theorems have exactly the standard axiom dependencies `[propext, Classical.choice, Quot.sound]`, as reported by `#print axioms`; neither depends on `sorryAx`. The independent audit agent separately ran the final axiom check and approved the optimized certificate, exact targets and source correspondence. The upstream formalization.yaml v0.4 schema check passes. Full Palomar mechanical preflight and intake are pending.

## Production and limitations

Alexander supplied the definitions and is the responsible author and maintainer. Codex agents constructed proofs and packaging and performed a separate source/proof audit. No human expert review or source-author endorsement is claimed. This formalizes an existing partial result; no novelty or full resolution of 415 is claimed.

Original proposition bodies and quantifiers were preserved. Packaging added module/public visibility, narrowed imports, and made `iterLog` noncomputable because it uses `Real.log`. Other questions remain unproved proposition definitions. Weak-order density and positive-constant conventions are explicit interpretations. The manuscript's asymptotic argument and the unavailable supplied discussion PDF were not verified. The Python count of fifteen length-four patterns is supplementary evidence, not a separately proved Lean theorem.
