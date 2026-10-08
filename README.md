# A finite counterexample for Erdős Problem 415

This project formalizes the finite counterexample at cutoff 826 in Przemek Chojecki's [Consecutive Totient Patterns](https://www.ulam.ai/research/erdos415-sol.pdf), Proposition 1.2, Section 4 and Appendix A (2026-07-13).

Every strict rank pattern of length three occurs in consecutive totients ending at or before 826. An increasing block of length four is absent, but the decreasing block starting at 823 has totients `(822, 408, 400, 348)`. The maximum universal length is therefore three. Decreasing is not always absent at the first non-universal length.

This is an existing partial negative result under a specified reading of [Problem 415](https://www.erdosproblems.com/415). No novelty, complete solution, asymptotic result or natural weak-order frequency result is claimed.

## Compared statements

`Challenge.lean` imports only Mathlib and has two deliberate proof holes:

- `Erdos415.finite_counterexample826`: `F 826 = 3`, a decreasing length-four block occurs, and no increasing length-four block occurs.
- `Erdos415.not_decreasingAlwaysMissing`: the proposed necessary cutoff condition for decreasing to be the first missing pattern fails.

`Solution.lean` supplies the proofs and does not import Challenge. `comparator.json` selects these declarations. The permitted axioms are `propext`, `Quot.sound` and `Classical.choice`; no additional axiom is permitted.

The cutoff is inclusive. A block starting at `m+1` ends at `m+k`, with `m+k ≤ n`. Ranks attach to positions, ties are excluded, and different permutations may use different blocks. Length zero is included in `F`. The missing-decreasing condition asks for absence, not uniqueness.

## Proof architecture

`Certificate.lean` proves totient values from zero through 826 using Mathlib's prime and product recurrence lemmas. A proved list identity connects these facts to an indexed table. `FiniteProof.lean` checks six length-three witnesses, the decreasing witness, and absence of an increasing length-four block at every possible start, using `decide +kernel`. `Bounds.lean` restricts the identity pattern at any universal length at least four, so the absent increasing block bounds every universal length by three.

The supplementary Python sieve `compute826.py` reproduces the example. Its count of fifteen strict length-four patterns is numerical evidence; Lean does not separately prove that count.

## Scope and provenance

Alexander supplied the original definitions and directs this project as responsible maintainer. Codex agents constructed the finite proof and general bound and prepared the submission. A separate Codex agent audited source correspondence and finite values. No human expert review or source-author endorsement is claimed. No earlier Lean proof was copied or used as a project dependency; no comprehensive prior-formalization search is claimed.

`Erdos415.lean` retains additional unproved proposition definitions. Its literal constant and positive-constant questions are distinct. Its natural-order frequency definition uses weak ordering and assumes compared densities exist. Those explicit interpretations are outside the compared results. The manuscript's asymptotic argument is not verified here. The supplied discussion PDF was unavailable.

## Verification

Lean is pinned to 4.35.0-rc3 and Mathlib to `0db6cb99b412983de54b59ecc1b0b2747542cda3`.

```sh
lake exe cache get
lake --wfail build Erdos415 Bounds Certificate FiniteProof Solution Challenge
```

Warnings for the two intentional Challenge holes are suppressed locally at those declarations. Implementation modules have no proof holes. See [AUDIT.md](AUDIT.md) for current verification status. The workflow `palomar-preflight.yml` runs Palomar's full pinned reusable mechanical preflight; a passing local build alone is insufficient for intake.

Repository source license: Apache-2.0. Cited sources and dependencies retain their own licenses.
