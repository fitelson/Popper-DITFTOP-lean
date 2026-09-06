# Popper-DITFTOP-lean

A Lean 4 formalization of Karl Popper's axiomatic theory of conditional probability, following the derivations in Appendix \*v ("Derivations in the Formal Theory of Probability") of Popper's *Logic of Scientific Discovery* (DITFTOP).

## Overview

Starting from six axioms (A1--A6) on a conditional probability function Pr(X | Y), we formalize Popper's main derivation, including his absolute-probability formulas, and construct a nontrivial Mathlib `BooleanAlgebra` on the quotient of propositions by probabilistic equivalence. Repeated or purely transitional numbered displays are sometimes folded into the proof of the next substantive result.

## Popper's Axioms

| Axiom | Name | Statement |
|-------|------|-----------|
| A1 | Non-triviality | There exist X, Y, C, D such that Pr(X \| Y) &ne; Pr(C \| D). Classically this is equivalent to Popper's free-variable formulation. |
| A2 | Substitution | If &forall;Z, Pr(X \| Z) = Pr(Y \| Z), then &forall;W, Pr(W \| X) = Pr(W \| Y) |
| A3 | Self-conditional equality | Pr(X \| X) = Pr(Y \| Y) for all X, Y |
| A4 | Monotonicity | Pr(X & Y \| Z) &le; Pr(X \| Z) |
| A5 | Multiplication rule | Pr(X & Y \| Z) = Pr(X \| Y & Z) &middot; Pr(Y \| Z) |
| A6 | Complementation | Pr(X \| X) &ne; Pr(Y \| X) &rarr; Pr(X \| X) = Pr(Z \| X) + Pr(&not;Z \| X) |

The theorem `ax_A1_popper` derives Popper's original free-variable form of A1
from the compact nontriviality field above.

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
11. **Complementation and double negation**: Pr((X&Y) &or; (X&not;Y) \| Z) = Pr(X \| Z), and Pr(&not;&not;X \| Z) = Pr(X \| Z) (Lemmas 87--94)
12. **Absolute probability** and the usual ratio theorem when Pr(Y) &ne; 0 (Lemmas 75, 96, and 97)
13. **Substitution/congruence** principles (Lemmas 90--100 and property D)
14. **Boolean algebra**: `EventQuotient S` is a nontrivial Mathlib `BooleanAlgebra`

## Formal Boolean-Algebra Endpoint

`PEq X Y` means that X and Y have the same conditional probability under every condition. The formalization packages `PEq` as a `Setoid`, defines `EventQuotient S` as the corresponding quotient, and lifts:

- conjunction to lattice infimum;
- the Boolean sum `~(~X & ~Y)` to lattice supremum;
- negation to Boolean complement;
- contradiction and tautology classes to bottom and top.

The quotient module proves absorption, distributivity, the top and bottom laws, both complement laws, and nontriviality. It then supplies actual `Lattice`, `DistribLattice`, `BooleanAlgebra`, and `Nontrivial` instances. Ordinary Lean equality on the quotient realizes Popper's unrestricted substitution principle (D).

## Project Structure

```
PopperProbability/
  Popper.lean                  -- Axioms and Popper's derivation
  QuotientBooleanAlgebra.lean  -- Quotient construction and BooleanAlgebra instance
PopperProbability.lean         -- Root import file
lakefile.toml                  -- Lean 4 / Mathlib project configuration
lean-toolchain                 -- Lean 4.28.0-rc1
```

## Building

Requires [Lean 4](https://lean-lang.org/) and [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

```bash
lake build
```

## References

- K. Popper, *The Logic of Scientific Discovery*, Routledge, 2002. Appendix \*v: "Derivations in the Formal Theory of Probability."
