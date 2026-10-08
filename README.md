# Erdős Problem 415: statement draft

This project records proposed Lean definitions for the questions about ordering patterns of consecutive Euler totients in [Erdős Problem 415](https://www.erdosproblems.com/415).

**It contains no proved theorem and is not a solution of Problem 415.** In particular, `FiniteCounterexample826` is a proposition definition, not a certificate or proof. There is currently no Challenge/Solution pair for Palomar.

## Scope

`Realizes` encodes strict ordering by assigning a rank to each position. `AllStrictPatterns` allows a different starting point for each permutation, and `F` maximizes over lengths bounded by the cutoff. Separate definitions record the literal constant question, its positive-constant interpretation, and a qualified first-missing-decreasing-pattern question.

The natural-order question uses weak ordering. `NaturalMostFrequentInDensity` chooses an asymptotic-density interpretation and additionally requires every compared density to exist. This is an explicit interpretation, not an assertion that the source uniquely specifies it.

## Sources and provenance

- [Problem 415](https://www.erdosproblems.com/415) and its [discussion](https://www.erdosproblems.com/forum/thread/415).
- Przemek Chojecki, [Consecutive Totient Patterns](https://www.ulam.ai/research/erdos415-sol.pdf), dated 2026-07-13 in the supplied draft.

The Lean definitions were supplied by the repository maintainer in `Erdos415.lean`. Their original documentation states that no proof from the manuscript or an existing Lean file was copied. This publication adds project packaging and an audit; it does not establish that provenance beyond the supplied account. Codex assisted with packaging and compilation, and a separate Codex agent audited the statements and reproduced the finite computation.

The original reference to a supplied discussion PDF could not be checked because that PDF was not provided with this submission request. The cited manuscript's asymptotic argument has not been independently verified in this project. No novelty or complete resolution is claimed.

## Verification

The project pins Lean 4.35.0-rc3 and Mathlib commit `0db6cb99b412983de54b59ecc1b0b2747542cda3`.

```sh
lake exe cache get
lake --wfail build Erdos415
```

See [AUDIT.md](AUDIT.md) for the verification status and statement audit. Compiling definitions checks that they are well-formed; it does not prove the propositions they define.

## Palomar status

Not submitted. A nonempty list of proved result declarations, an auditable Challenge, a matching Solution, Comparator configuration, truthful formalization metadata, and passing mechanical preflight are still needed. These files must not be manufactured around unproved definitions to imply that the problem has been solved.

License: Apache-2.0 for this repository's source; cited sources and dependencies retain their own licenses.
