# CLAUDE.md

This file provides guidance to Claude Code when working with this repository.

## Project Overview

Lean 4 formalization of Karl Popper's axiomatic theory of conditional probability, following the derivations in Appendix *v ("Derivations in the Formal Theory of Probability") of *The Logic of Scientific Discovery* (Routledge, 2002).

From six axioms (A1–A6) the project formalizes Popper's main derivation,
including the absolute-probability results (75), (96), and (97). It then
constructs a nontrivial Mathlib `BooleanAlgebra` on the quotient by
probabilistic equivalence.

## Building

```bash
lake build
```

Uses Lean 4.28.0-rc1 with Mathlib.

## Project Structure

- `PopperProbability/Popper.lean` — Axioms, probability lemmas, absolute probability, D1/D2, and Huntington laws
- `PopperProbability/QuotientBooleanAlgebra.lean` — `PEq` setoid, quotient operations, substitution principle, and the `BooleanAlgebra`/`Nontrivial` instances
- `PopperProbability.lean` — Root import file

## Popper's Axiom System

`PopperProbability` is a typeclass parameterized by `S : Type`:
- `cp : S → S → ℝ` — conditional probability, `cp x y` means Pr(X | Y)
- `a : S → S → S` — conjunction, `a x y` means X & Y
- `n : S → S` — negation, `n x` means ~X

The constant `k` (common value of all Pr(X | X)) is defined as `k_val` with a
`local notation "k"` that transparently resolves the type parameter `S`.

The axioms:
- **A1**: Non-triviality — distinct probability values exist
- **A2**: Substitution — if ∀ Z, Pr(X | Z) = Pr(Y | Z), then ∀ W, Pr(W | X) = Pr(W | Y)
- **A3**: Pr(X | X) = Pr(Y | Y) for all X, Y
- **A4**: Pr(X & Y | Z) ≤ Pr(X | Z) (monotonicity)
- **A5**: Pr(X & Y | Z) = Pr(X | Y & Z) · Pr(Y | Z) (multiplication rule)
- **A6**: Pr(X | X) ≠ Pr(Y | X) → Pr(X | X) = Pr(Z | X) + Pr(~Z | X)

## Proof Structure

The file is organized into sections following the lemma numbering:

| Section | Lemmas | Key result |
|---------|--------|------------|
| Basic | 2–5 | k² ≤ k, so 0 ≤ k ≤ 1 |
| NonNegativity | 6–14 | 0 ≤ Pr(X \| Y) |
| Bounds | 15–18 | Pr(X \| Y) ≤ k ≤ 1 |
| KEqualsOne | 19–27 | k = 1 |
| Idempotence | 28–30 | Pr(X & X \| Y) = Pr(X \| Y) |
| Commutativity | 31–40 | Pr(X & Y \| Z) = Pr(Y & X \| Z) |
| Associativity | 41–62 | Pr((X & Y) & Z \| W) = Pr(X & (Y & Z) \| W) |
| Complementation | 63–70 | Pr(X & Y \| Z) + Pr(~X & Y \| Z) = Pr(Y \| Z) + Pr(~Z \| Z) |
| InclusionExclusion | 71–80 | Pr(X ∨ Y \| Z) = Pr(X \| Z) + Pr(Y \| Z) - Pr(X & Y \| Z) |
| Distribution | 81–86 | Conjunction distributes over disjunction |
| Complement/DoubleNegation | 87–94 | Complementation and Pr(~~X \| Z) = Pr(X \| Z) |
| AbsoluteProbability | 75, 96–97 | Pr(X \| Y)Pr(Y) = Pr(X&Y), and the ratio theorem |
| Substitution | 90–100 | Congruence / substitution principles |
| BooleanAlgebra | — | Nontrivial `BooleanAlgebra (EventQuotient S)` instance |

## Naming Conventions

Key theorem names:
- `cp_self_eq_k` — Pr(X | X) = k
- `cp_nonneg` — 0 ≤ Pr(X | Y)
- `cp_le_k`, `cp_le_one` — upper bounds
- `k_eq_one` — k = 1
- `cp_self_eq_one` — Pr(X | X) = 1
- `cp_idem` — idempotence
- `cp_comm` — commutativity
- `cp_assoc` — associativity
- `cp_compl` — complementation law
- `cp_incl_excl` — inclusion-exclusion
- `cp_double_neg` — double negation
- `cp_neg_congr` — negation congruence
- `absProb`, `absProb_mul`, `cp_eq_absProb_div` — absolute probability and Popper's formulas (75), (96), and (97)
- `PEq` — probabilistic equivalence relation
- `EventQuotient` — quotient by `PEq`, with `BooleanAlgebra` and `Nontrivial` instances

## Proof Style

- Most proofs use `linarith`, `nlinarith`, `calc` chains, and direct rewriting
- `nlinarith` handles nonlinear arithmetic (products of probabilities)
- The associativity proof (Lemmas 41–62) is the longest chain, using a cyclic permutation argument for the reverse inequality
