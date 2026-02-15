# Popper-DITFTOP-lean

A Lean 4 formalization of Karl Popper's axiomatic theory of conditional probability, following the derivations in Popper and Miller's 1994 paper "Deductive Inference in the Theory of Probability" (DITFTOP).

## Overview

Starting from just six axioms (A1--A6) on a conditional probability function Pr(X | Y), we derive ~100 lemmas culminating in the result that the quotient of the proposition space under probabilistic equivalence forms a Boolean algebra. The entire proof chain is verified in Lean 4 with Mathlib.

## Popper's Axioms

| Axiom | Name | Statement |
|-------|------|-----------|
| A1 | Non-triviality | There exist X, Y, C, D such that Pr(X \| Y) &ne; Pr(C \| D) |
| A2 | Substitution | If &forall;Z, Pr(X \| Z) = Pr(Y \| Z), then &forall;W, Pr(W \| X) = Pr(W \| Y) |
| A3 | Self-conditional equality | Pr(X \| X) = Pr(Y \| Y) for all X, Y |
| A4 | Monotonicity | Pr(X & Y \| Z) &le; Pr(X \| Z) |
| A5 | Multiplication rule | Pr(X & Y \| Z) = Pr(X \| Y & Z) &middot; Pr(Y \| Z) |
| A6 | Complementation | Pr(X \| X) &ne; Pr(Y \| X) &rarr; Pr(X \| X) = Pr(Z \| X) + Pr(&not;Z \| X) |

## Key Results

The formalization establishes, in order:

1. **k&sup2; &le; k** and therefore **0 &le; k &le; 1**, where k is the common value of all Pr(X \| X) (Lemmas 2--5)
2. **Non-negativity**: 0 &le; Pr(X \| Y) for all X, Y (Lemmas 6--14)
3. **Upper bound**: Pr(X \| Y) &le; k &le; 1 (Lemmas 15--18)
4. **k = 1** (Lemmas 19--25)
5. **Idempotence**: Pr(X & X \| Y) = Pr(X \| Y) (Lemmas 28--30)
6. **Commutativity**: Pr(X & Y \| Z) = Pr(Y & X \| Z) (Lemmas 31--40)
7. **Associativity**: Pr((X & Y) & Z \| W) = Pr(X & (Y & Z) \| W) (Lemmas 41--62)
8. **Complementation**: Pr(X & Y \| Z) + Pr(&not;X & Y \| Z) = Pr(Y \| Z) + Pr(&not;Z \| Z) (Lemmas 63--70)
9. **Inclusion-exclusion**: Pr(X &or; Y \| Z) = Pr(X \| Z) + Pr(Y \| Z) - Pr(X & Y \| Z) (Lemmas 71--80)
10. **Distribution**: conjunction distributes over disjunction (Lemmas 81--86)
11. **Double negation**: Pr(&not;&not;X \| Z) = Pr(X \| Z) (Lemmas 87--89)
12. **Substitution/congruence** principles (Lemmas 90--100)
13. **Boolean algebra**: the quotient under probabilistic equivalence satisfies axioms (i)--(vii) of a Boolean algebra

## Project Structure

```
PopperProbability/
  Popper.lean          -- Complete formalization (all axioms and lemmas)
PopperProbability.lean -- Root import file
lakefile.toml          -- Lean 4 / Mathlib project configuration
lean-toolchain         -- Lean 4.28.0-rc1
```

## Building

Requires [Lean 4](https://lean-lang.org/) and [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

```bash
lake build
```

## References

- K. Popper, "Two Autonomous Axiom Systems for the Calculus of Probabilities," *British Journal for the Philosophy of Science* 6 (1955), 51--57.
- K. Popper and D. Miller, "Deductive Inference in the Theory of Probability," unpublished manuscript (1994).
