import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Popper's Axiomatic Theory of Conditional Probability

A complete Lean 4 formalization of Karl Popper's axiomatic theory of
conditional probability, following his 1955 paper "Two Autonomous Axiom
Systems for the Calculus of Probabilities" and the 1994 Popper–Miller paper.

## Overview

Starting from six axioms (A1–A6) on a conditional probability function
`cp : S → S → ℝ`, we derive:

* **Lemmas 1–5**: k² ≤ k, hence 0 ≤ k ≤ 1
* **Lemmas 6–14**: Non-negativity: 0 ≤ Pr(X | Y)
* **Lemmas 15–18**: Bounds: 0 ≤ Pr(X | Y) ≤ k ≤ 1
* **Lemmas 19–27**: k = 1
* **Lemmas 28–30**: Idempotence: Pr(X & X | Y) = Pr(X | Y)
* **Lemmas 31–40**: Commutativity: Pr(X & Y | Z) = Pr(Y & X | Z)
* **Lemmas 41–62**: Associativity: Pr((X & Y) & Z | W) = Pr(X & (Y & Z) | W)
* **Lemmas 63–70**: Complementation: Pr(X & Y | Z) + Pr(~X & Y | Z) = Pr(Y | Z) + Pr(~Z | Z)
* **Lemmas 71–80**: Inclusion-exclusion
* **Lemmas 81–86**: Distribution laws
* **Lemmas 87–89**: Double negation: Pr(~~X | Z) = Pr(X | Z)
* **Lemmas 90–100**: Substitution / congruence principles
* **Boolean algebra**: The quotient under probabilistic equivalence forms a Boolean algebra
-/

-- ============================================================
-- Axioms
-- ============================================================

/-- Popper's axiomatic system for conditional probability.

  * `S` is a type of propositions/sentences.
  * `cp x y` represents the conditional probability Pr(X | Y).
  * `a x y` represents the conjunction X & Y.
  * `n x` represents the negation ~X.

  The axioms are from Popper's 1955 paper. -/
structure PopperProbability where
  /-- The type of propositions -/
  S : Type
  /-- Conditional probability: `cp x y` means Pr(X | Y) -/
  cp : S → S → ℝ
  /-- Conjunction: `a x y` means X & Y -/
  a : S → S → S
  /-- Negation: `n x` means ~X -/
  n : S → S
  /-- A1 (Non-triviality): There exist distinct probability values -/
  ax_A1 : ∃ x y c d : S, cp x y ≠ cp c d
  /-- A2 (Substitution): If X and Y agree in probability under all conditions,
      they are intersubstitutable in the conditioning position -/
  ax_A2 : ∀ (x y : S), (∀ z : S, cp x z = cp y z) → ∀ w : S, cp w x = cp w y
  /-- A3 (Self-conditional equality): All self-conditional probabilities are equal -/
  ax_A3 : ∀ (x y : S), cp x x = cp y y
  /-- A4 (Monotonicity): Pr(X & Y | Z) ≤ Pr(X | Z) -/
  ax_A4 : ∀ (x y z : S), cp (a x y) z ≤ cp x z
  /-- A5 (Multiplication / Chain rule): Pr(X & Y | Z) = Pr(X | Y & Z) · Pr(Y | Z) -/
  ax_A5 : ∀ (x y z : S), cp (a x y) z = cp x (a y z) * cp y z
  /-- A6 (Complementation): If Pr(X|X) ≠ Pr(Y|X), then Pr(X|X) = Pr(Z|X) + Pr(~Z|X) -/
  ax_A6 : ∀ (x y z : S), cp x x ≠ cp y x → cp x x = cp z x + cp (n z) x

namespace PopperProbability

variable {P : PopperProbability}

/-- S is nonempty (follows from A1). -/
instance instNonemptyS : Nonempty P.S := by
  obtain ⟨x, _, _, _, _⟩ := P.ax_A1
  exact ⟨x⟩

/-- The constant k: the common value of all Pr(X | X).
    By A3, all self-conditional probabilities are equal. -/
noncomputable def k (P : PopperProbability) : ℝ :=
  P.cp (Classical.arbitrary P.S) (Classical.arbitrary P.S)

/-- Lemma 1 (Convention): Every self-conditional probability equals k. -/
theorem cp_self_eq_k (x : P.S) : P.cp x x = P.k := by
  unfold k
  exact P.ax_A3 x _

-- ============================================================
-- Basic Properties (Lemmas 2–5)
-- ============================================================

/-- Lemma 2a: Pr((X & X) & X | X) ≤ Pr(X & X | X) -/
theorem lemma_2a (x : P.S) :
    P.cp (P.a (P.a x x) x) x ≤ P.cp (P.a x x) x :=
  P.ax_A4 (P.a x x) x x

/-- Lemma 2b: Pr(X & X | X) ≤ Pr(X | X) -/
theorem lemma_2b (x : P.S) :
    P.cp (P.a x x) x ≤ P.cp x x :=
  P.ax_A4 x x x

/-- Lemma 2c: Pr((X & X) & X | X) ≤ k -/
theorem lemma_2c (x : P.S) :
    P.cp (P.a (P.a x x) x) x ≤ P.k := by
  calc P.cp (P.a (P.a x x) x) x
      ≤ P.cp (P.a x x) x := lemma_2a x
    _ ≤ P.cp x x := lemma_2b x
    _ = P.k := P.cp_self_eq_k x

/-- Lemma 3a: Pr((X & X) & X | X) = Pr(X & X | X & X) · Pr(X | X) -/
theorem lemma_3a (x : P.S) :
    P.cp (P.a (P.a x x) x) x = P.cp (P.a x x) (P.a x x) * P.cp x x :=
  P.ax_A5 (P.a x x) x x

/-- Lemma 3b: Pr((X & X) & X | X) = k² -/
theorem lemma_3b (x : P.S) :
    P.cp (P.a (P.a x x) x) x = P.k * P.k := by
  rw [lemma_3a x, P.cp_self_eq_k (P.a x x), P.cp_self_eq_k x]

/-- Lemma 4: k² ≤ k -/
theorem k_sq_le_k : P.k * P.k ≤ P.k := by
  have ⟨x, _, _, _, _⟩ := P.ax_A1
  calc P.k * P.k = P.cp (P.a (P.a x x) x) x := (lemma_3b x).symm
    _ ≤ P.k := lemma_2c x

/-- Lemma 5: 0 ≤ k ∧ k ≤ 1 -/
theorem k_bounds : 0 ≤ P.k ∧ P.k ≤ 1 := by
  constructor <;> nlinarith [k_sq_le_k (P := P)]

theorem k_nonneg : 0 ≤ P.k := k_bounds.1

theorem k_le_one : P.k ≤ 1 := k_bounds.2

-- ============================================================
-- Non-negativity (Lemmas 6–14)
-- ============================================================

/-- Lemma 6a: If k ≠ Pr(X|Y), then k = Pr(Z|Y) + Pr(~Z|Y) for all Z -/
theorem lemma_6a (x y z : P.S) (h : P.k ≠ P.cp x y) :
    P.k = P.cp z y + P.cp (P.n z) y := by
  have hself : P.cp y y = P.k := P.cp_self_eq_k y
  have hne : P.cp y y ≠ P.cp x y := hself ▸ h
  have := P.ax_A6 y x z hne
  linarith [P.cp_self_eq_k y]

/-- Lemma 6: If k ≠ Pr(X|Y), then k = k + Pr(~Y|Y) -/
theorem lemma_6 (x y : P.S) (h : P.k ≠ P.cp x y) :
    P.k = P.k + P.cp (P.n y) y := by
  have := lemma_6a x y y h
  rw [P.cp_self_eq_k y] at this
  exact this

/-- Lemma 7: If k ≠ Pr(X|Y), then Pr(~Y|Y) = 0 -/
theorem lemma_7 (x y : P.S) (h : P.k ≠ P.cp x y) :
    P.cp (P.n y) y = 0 := by
  linarith [lemma_6 x y h]

/-- Lemma 8: Pr(X & ~Y | Y) = Pr(X | ~Y & Y) · Pr(~Y | Y) -/
theorem lemma_8 (x y : P.S) :
    P.cp (P.a x (P.n y)) y = P.cp x (P.a (P.n y) y) * P.cp (P.n y) y :=
  P.ax_A5 x (P.n y) y

/-- Lemma 9a: If k ≠ Pr(X|Y), then Pr(X & ~Y | Y) = 0 -/
theorem lemma_9a (x y : P.S) (h : P.k ≠ P.cp x y) :
    P.cp (P.a x (P.n y)) y = 0 := by
  rw [lemma_8 x y, lemma_7 x y h, mul_zero]

/-- Lemma 9b: Pr(X & ~Y | Y) ≤ Pr(X | Y) -/
theorem lemma_9b (x y : P.S) :
    P.cp (P.a x (P.n y)) y ≤ P.cp x y :=
  P.ax_A4 x (P.n y) y

/-- Lemma 10: If k ≠ Pr(X|Y), then 0 ≤ Pr(X|Y) -/
theorem lemma_10 (x y : P.S) (h : P.k ≠ P.cp x y) :
    0 ≤ P.cp x y := by
  linarith [lemma_9a x y h, lemma_9b x y]

/-- Lemma 11: Pr(X|Y) < 0 → k = Pr(X|Y) (contrapositive of Lemma 10) -/
theorem lemma_11 (x y : P.S) (h : P.cp x y < 0) :
    P.k = P.cp x y := by
  by_contra hne
  linarith [lemma_10 x y hne]

/-- Lemma 12: k = Pr(X|Y) → 0 ≤ Pr(X|Y) -/
theorem lemma_12 (x y : P.S) (h : P.k = P.cp x y) :
    0 ≤ P.cp x y := by
  rw [← h]; exact k_nonneg

/-- Lemma 14: 0 ≤ Pr(X|Y) for all X, Y (non-negativity) -/
theorem cp_nonneg (x y : P.S) : 0 ≤ P.cp x y := by
  by_cases h : P.k = P.cp x y
  · exact lemma_12 x y h
  · exact lemma_10 x y h

-- ============================================================
-- Probability Bounds (Lemmas 15–18)
-- ============================================================

/-- Lemma 15: 0 ≤ Pr(~X | Y) -/
theorem cp_neg_nonneg (x y : P.S) : 0 ≤ P.cp (P.n x) y :=
  cp_nonneg (P.n x) y

/-- Lemma 16a: If k ≠ Pr(X|Y), then k = Pr(X|Y) + Pr(~X|Y) -/
theorem lemma_16a (x y : P.S) (h : P.k ≠ P.cp x y) :
    P.k = P.cp x y + P.cp (P.n x) y :=
  lemma_6a x y x h

/-- Lemma 16: If k ≠ Pr(X|Y), then k ≥ Pr(X|Y) -/
theorem lemma_16 (x y : P.S) (h : P.k ≠ P.cp x y) :
    P.k ≥ P.cp x y := by
  linarith [lemma_16a x y h, cp_neg_nonneg x y]

/-- Lemma 17: Pr(X|Y) ≤ k -/
theorem cp_le_k (x y : P.S) : P.cp x y ≤ P.k := by
  by_cases h : P.k = P.cp x y
  · linarith
  · linarith [lemma_16 x y h]

/-- Lemma 18: 0 ≤ Pr(X|Y) ≤ k ≤ 1 -/
theorem cp_bounds (x y : P.S) : 0 ≤ P.cp x y ∧ P.cp x y ≤ P.k ∧ P.k ≤ 1 :=
  ⟨cp_nonneg x y, cp_le_k x y, k_le_one⟩

-- ============================================================
-- k = 1 (Lemmas 19–27)
-- ============================================================

/-- Lemma 19: Pr(X | X & X) = k (sandwich argument) -/
theorem cp_self_conj (x : P.S) : P.cp x (P.a x x) = P.k := by
  apply le_antisymm
  · exact cp_le_k x (P.a x x)
  · calc P.k = P.cp (P.a x x) (P.a x x) := (P.cp_self_eq_k _).symm
      _ ≤ P.cp x (P.a x x) := P.ax_A4 x x (P.a x x)

/-- Lemma 20: Pr(X | X & (X & X)) = k -/
theorem cp_self_triple_conj (x : P.S) : P.cp x (P.a x (P.a x x)) = P.k := by
  apply le_antisymm
  · exact cp_le_k x _
  · calc P.k = P.cp (P.a x (P.a x x)) (P.a x (P.a x x)) :=
          (P.cp_self_eq_k _).symm
      _ ≤ P.cp x (P.a x (P.a x x)) := P.ax_A4 x (P.a x x) _

/-- Lemma 21a: Pr(X & X | X & X) = Pr(X | X & (X & X)) · Pr(X | X & X) -/
theorem lemma_21a (x : P.S) :
    P.cp (P.a x x) (P.a x x) = P.cp x (P.a x (P.a x x)) * P.cp x (P.a x x) :=
  P.ax_A5 x x (P.a x x)

/-- Lemma 21: k = k² -/
theorem k_eq_k_sq : P.k = P.k * P.k := by
  have ⟨x, _, _, _, _⟩ := P.ax_A1
  calc P.k = P.cp (P.a x x) (P.a x x) := (P.cp_self_eq_k _).symm
    _ = P.cp x (P.a x (P.a x x)) * P.cp x (P.a x x) := lemma_21a x
    _ = P.k * P.k := by rw [cp_self_triple_conj x, cp_self_conj x]

/-- Lemma 23: If there exists a non-zero probability, then k = 1 -/
theorem k_eq_one_of_nonzero (h : ∃ x y : P.S, P.cp x y ≠ 0) : P.k = 1 := by
  obtain ⟨x, y, hne⟩ := h
  have hfact : P.k * (P.k - 1) = 0 := by nlinarith [k_eq_k_sq (P := P)]
  rcases mul_eq_zero.mp hfact with hk0 | hk1
  · exfalso; apply hne
    have hle : P.cp x y ≤ P.k := cp_le_k x y
    have hge : 0 ≤ P.cp x y := cp_nonneg x y
    linarith
  · linarith

/-- Lemma 24: There exists a non-zero probability -/
theorem exists_nonzero : ∃ x y : P.S, P.cp x y ≠ 0 := by
  obtain ⟨x, y, c, d, hne⟩ := P.ax_A1
  by_contra h
  push_neg at h
  exact hne (by rw [h x y, h c d])

/-- Lemma 25: k = 1 -/
theorem k_eq_one : P.k = 1 := k_eq_one_of_nonzero exists_nonzero

/-- Corollary: Pr(X | X) = 1 for all X -/
theorem cp_self_eq_one (x : P.S) : P.cp x x = 1 := by
  rw [P.cp_self_eq_k x, k_eq_one]

/-- Lemma 26: There exist X, Y such that Pr(Y | X) ≠ k -/
theorem exists_ne_k : ∃ (x y : P.S), P.cp y x ≠ P.k := by
  obtain ⟨x, y, c, d, hne⟩ := P.ax_A1
  by_contra h
  push_neg at h
  exact hne (by rw [h y x, h d c])

/-- Lemma 27: There exists X such that Pr(~X | X) = 0 -/
theorem exists_neg_zero : ∃ x : P.S, P.cp (P.n x) x = 0 := by
  obtain ⟨x, y, hne⟩ := exists_ne_k
  exact ⟨x, lemma_7 y x hne.symm⟩

-- ============================================================
-- Idempotence (Lemmas 28–30)
-- ============================================================

/-- Lemma 28a: Pr(X & Y | X & Y) = 1 -/
theorem cp_conj_self_eq_one (x y : P.S) :
    P.cp (P.a x y) (P.a x y) = 1 := cp_self_eq_one _

/-- Lemma 28b: Pr(X & Y | X & Y) ≤ Pr(X | X & Y) -/
theorem lemma_28b (x y : P.S) :
    P.cp (P.a x y) (P.a x y) ≤ P.cp x (P.a x y) :=
  P.ax_A4 x y (P.a x y)

/-- Lemma 28c: Pr(X | X & Y) ≤ 1 -/
theorem lemma_28c (x y : P.S) : P.cp x (P.a x y) ≤ 1 := by
  linarith [cp_le_k x (P.a x y), k_eq_one (P := P)]

/-- Lemma 28: Pr(X | X & Y) = 1 -/
theorem cp_fst_conj (x y : P.S) : P.cp x (P.a x y) = 1 := by
  linarith [cp_conj_self_eq_one x y, lemma_28b x y, lemma_28c x y]

/-- Lemma 29: Pr(X & X | Y) = Pr(X | X & Y) · Pr(X | Y) -/
theorem lemma_29 (x y : P.S) :
    P.cp (P.a x x) y = P.cp x (P.a x y) * P.cp x y :=
  P.ax_A5 x x y

/-- Lemma 30: Pr(X & X | Y) = Pr(X | Y) (idempotence) -/
theorem cp_idem (x y : P.S) : P.cp (P.a x x) y = P.cp x y := by
  rw [lemma_29 x y, cp_fst_conj x y, one_mul]

-- ============================================================
-- Commutativity (Lemmas 31–40)
-- ============================================================

/-- Lemma 31: Pr(X | Y & Z) ≤ 1 -/
theorem cp_le_one (x y : P.S) : P.cp x y ≤ 1 := by
  linarith [cp_le_k x y, k_eq_one (P := P)]

/-- Lemma 32: Pr(X & Y | Z) ≤ Pr(Y | Z) (second monotony) -/
theorem cp_conj_le_snd (x y z : P.S) :
    P.cp (P.a x y) z ≤ P.cp y z := by
  have h5 := P.ax_A5 x y z
  have hle := cp_le_one x (P.a y z)
  have hnn := cp_nonneg y z
  nlinarith

/-- Lemma 33: Pr(X & (Y & Z) | X & (Y & Z)) = 1 -/
theorem cp_triple_self (x y z : P.S) :
    P.cp (P.a x (P.a y z)) (P.a x (P.a y z)) = 1 :=
  cp_self_eq_one _

/-- Lemma 34: Pr(Y & Z | X & (Y & Z)) = 1 -/
theorem cp_snd_in_conj (x y z : P.S) :
    P.cp (P.a y z) (P.a x (P.a y z)) = 1 := by
  apply le_antisymm
  · exact cp_le_one _ _
  · calc (1 : ℝ) = P.cp (P.a x (P.a y z)) (P.a x (P.a y z)) :=
          (cp_self_eq_one _).symm
      _ ≤ P.cp (P.a y z) (P.a x (P.a y z)) := cp_conj_le_snd x (P.a y z) _

/-- Lemma 35: Pr(Y | X & (Y & Z)) = 1 -/
theorem cp_fst_of_snd_conj (x y z : P.S) :
    P.cp y (P.a x (P.a y z)) = 1 := by
  apply le_antisymm
  · exact cp_le_one _ _
  · calc (1 : ℝ) = P.cp (P.a y z) (P.a x (P.a y z)) :=
          (cp_snd_in_conj x y z).symm
      _ ≤ P.cp y (P.a x (P.a y z)) := P.ax_A4 y z _

/-- Lemma 36: Pr(Y & X | Y & Z) = Pr(X | Y & Z) -/
theorem cp_swap_fst (x y z : P.S) :
    P.cp (P.a y x) (P.a y z) = P.cp x (P.a y z) := by
  have h5 := P.ax_A5 y x (P.a y z)
  rw [cp_fst_of_snd_conj x y z, one_mul] at h5
  exact h5

/-- Lemma 37: Pr((Y & X) & Y | Z) = Pr(X & Y | Z) -/
theorem cp_perm_triple (x y z : P.S) :
    P.cp (P.a (P.a y x) y) z = P.cp (P.a x y) z := by
  have h1 := P.ax_A5 (P.a y x) y z
  rw [cp_swap_fst x y z] at h1
  linarith [P.ax_A5 x y z]

/-- Lemma 38: Pr(Y & X | Z) ≥ Pr(X & Y | Z) -/
theorem cp_conj_ge (x y z : P.S) :
    P.cp (P.a y x) z ≥ P.cp (P.a x y) z := by
  calc P.cp (P.a x y) z = P.cp (P.a (P.a y x) y) z := (cp_perm_triple x y z).symm
    _ ≤ P.cp (P.a y x) z := P.ax_A4 (P.a y x) y z

/-- Lemma 39: Pr(X & Y | Z) ≥ Pr(Y & X | Z) -/
theorem cp_conj_ge' (x y z : P.S) :
    P.cp (P.a x y) z ≥ P.cp (P.a y x) z :=
  cp_conj_ge y x z

/-- Lemma 40: Pr(X & Y | Z) = Pr(Y & X | Z) (commutativity) -/
theorem cp_comm (x y z : P.S) :
    P.cp (P.a x y) z = P.cp (P.a y x) z :=
  le_antisymm (cp_conj_ge x y z) (cp_conj_ge' x y z)

-- ============================================================
-- Associativity (Lemmas 41–62)
-- ============================================================

-- Part 1: Showing Pr(X & (Y & Z) | (X & Y) & Z) = 1

/-- Lemma 41: Pr(X & Y | W & ((X & Y) & Z)) = 1 -/
theorem cp_conj_in_assoc (x y z w : P.S) :
    P.cp (P.a x y) (P.a w (P.a (P.a x y) z)) = 1 :=
  cp_fst_of_snd_conj w (P.a x y) z

/-- Lemma 42c: Pr(X | W & ((X & Y) & Z)) = 1 -/
theorem cp_fst_in_assoc (x y z w : P.S) :
    P.cp x (P.a w (P.a (P.a x y) z)) = 1 := by
  apply le_antisymm (cp_le_one _ _)
  calc (1 : ℝ) = P.cp (P.a x y) (P.a w (P.a (P.a x y) z)) :=
        (cp_conj_in_assoc x y z w).symm
    _ ≤ P.cp x (P.a w (P.a (P.a x y) z)) := P.ax_A4 x y _

/-- Lemma 42: Pr(Y | W & ((X & Y) & Z)) = 1 -/
theorem cp_snd_in_assoc (x y z w : P.S) :
    P.cp y (P.a w (P.a (P.a x y) z)) = 1 := by
  apply le_antisymm (cp_le_one _ _)
  calc (1 : ℝ) = P.cp (P.a x y) (P.a w (P.a (P.a x y) z)) :=
        (cp_conj_in_assoc x y z w).symm
    _ ≤ P.cp y (P.a w (P.a (P.a x y) z)) := cp_conj_le_snd x y _

/-- Lemma 43: Pr(X | (Y & Z) & ((X & Y) & Z)) = 1 -/
theorem lemma_43 (x y z : P.S) :
    P.cp x (P.a (P.a y z) (P.a (P.a x y) z)) = 1 :=
  cp_fst_in_assoc x y z (P.a y z)

/-- Lemma 44: Pr(X & (Y & Z) | (X & Y) & Z) = Pr(Y & Z | (X & Y) & Z) -/
theorem lemma_44 (x y z : P.S) :
    P.cp (P.a x (P.a y z)) (P.a (P.a x y) z) =
    P.cp (P.a y z) (P.a (P.a x y) z) := by
  have h := P.ax_A5 x (P.a y z) (P.a (P.a x y) z)
  rw [lemma_43 x y z, one_mul] at h
  exact h

/-- Lemma 46: Pr(Y | Z & ((X & Y) & Z)) = 1 -/
theorem lemma_46 (x y z : P.S) :
    P.cp y (P.a z (P.a (P.a x y) z)) = 1 :=
  cp_snd_in_assoc x y z z

/-- Lemma 47: Pr(Z | (X & Y) & Z) = 1 -/
theorem cp_z_in_assoc (x y z : P.S) :
    P.cp z (P.a (P.a x y) z) = 1 := by
  apply le_antisymm (cp_le_one _ _)
  calc (1 : ℝ) = P.cp (P.a (P.a x y) z) (P.a (P.a x y) z) :=
        (cp_self_eq_one _).symm
    _ ≤ P.cp z (P.a (P.a x y) z) := cp_conj_le_snd (P.a x y) z _

/-- Lemma 48i: Pr(Y & Z | (X & Y) & Z) = 1 -/
theorem lemma_48i (x y z : P.S) :
    P.cp (P.a y z) (P.a (P.a x y) z) = 1 := by
  have h := P.ax_A5 y z (P.a (P.a x y) z)
  rw [lemma_46 x y z, cp_z_in_assoc x y z, one_mul] at h
  exact h

/-- Lemma 48: Pr(X & (Y & Z) | (X & Y) & Z) = 1 -/
theorem cp_right_assoc_given_left (x y z : P.S) :
    P.cp (P.a x (P.a y z)) (P.a (P.a x y) z) = 1 := by
  rw [lemma_44 x y z, lemma_48i x y z]

-- Part 2: Three-factor expansion and the key inequalities

/-- Lemma 49: Three-factor expansion of deeply nested conjunction.
    Pr(X & (Y & (Z & W)) | W) = Pr(Z & W | Y & (X & W)) · Pr(Y | X & W) · Pr(X | W) -/
theorem lemma_49 (x y z w : P.S) :
    P.cp (P.a x (P.a y (P.a z w))) w =
    P.cp (P.a z w) (P.a y (P.a x w)) * P.cp y (P.a x w) * P.cp x w := by
  calc P.cp (P.a x (P.a y (P.a z w))) w
      = P.cp (P.a (P.a y (P.a z w)) x) w := cp_comm x (P.a y (P.a z w)) w
    _ = P.cp (P.a y (P.a z w)) (P.a x w) * P.cp x w :=
        P.ax_A5 (P.a y (P.a z w)) x w
    _ = P.cp (P.a (P.a z w) y) (P.a x w) * P.cp x w := by
        rw [cp_comm y (P.a z w) (P.a x w)]
    _ = P.cp (P.a z w) (P.a y (P.a x w)) * P.cp y (P.a x w) * P.cp x w := by
        rw [P.ax_A5 (P.a z w) y (P.a x w), mul_assoc]

/-- Lemma 50: Three-factor expansion of triple conjunction.
    Pr(X & (Y & Z) | W) = Pr(Z | Y & (X & W)) · Pr(Y | X & W) · Pr(X | W) -/
theorem lemma_50 (x y z w : P.S) :
    P.cp (P.a x (P.a y z)) w =
    P.cp z (P.a y (P.a x w)) * P.cp y (P.a x w) * P.cp x w := by
  calc P.cp (P.a x (P.a y z)) w
      = P.cp (P.a (P.a y z) x) w := cp_comm x (P.a y z) w
    _ = P.cp (P.a y z) (P.a x w) * P.cp x w :=
        P.ax_A5 (P.a y z) x w
    _ = P.cp (P.a z y) (P.a x w) * P.cp x w := by
        rw [cp_comm y z (P.a x w)]
    _ = P.cp z (P.a y (P.a x w)) * P.cp y (P.a x w) * P.cp x w := by
        rw [P.ax_A5 z y (P.a x w), mul_assoc]

/-- Lemma 51: Pr(X & (Y & Z) | W) ≥ Pr(X & (Y & (Z & W)) | W) -/
theorem lemma_51 (x y z w : P.S) :
    P.cp (P.a x (P.a y z)) w ≥ P.cp (P.a x (P.a y (P.a z w))) w := by
  rw [lemma_50, lemma_49]
  have hle := P.ax_A4 z w (P.a y (P.a x w))
  have hnn1 := cp_nonneg y (P.a x w)
  have hnn2 := cp_nonneg x w
  have hnn3 := cp_nonneg (P.a z w) (P.a y (P.a x w))
  have hnn4 := cp_nonneg z (P.a y (P.a x w))
  nlinarith [mul_le_mul_of_nonneg_right hle (mul_nonneg hnn1 hnn2)]

/-- Lemma 52: Pr(X & (Y & (Z & W)) | (X & Y) & (Z & W)) = 1 -/
theorem lemma_52 (x y z w : P.S) :
    P.cp (P.a x (P.a y (P.a z w))) (P.a (P.a x y) (P.a z w)) = 1 :=
  cp_right_assoc_given_left x y (P.a z w)

/-- Lemma 53: Pr((X & (Y & (Z & W))) & (X & Y) | Z & W) = Pr(X & Y | Z & W) -/
theorem lemma_53 (x y z w : P.S) :
    P.cp (P.a (P.a x (P.a y (P.a z w))) (P.a x y)) (P.a z w) =
    P.cp (P.a x y) (P.a z w) := by
  have h := P.ax_A5 (P.a x (P.a y (P.a z w))) (P.a x y) (P.a z w)
  rw [lemma_52 x y z w, one_mul] at h
  exact h

/-- Lemma 54: Pr(X & (Y & (Z & W)) | Z & W) ≥ Pr(X & Y | Z & W) -/
theorem lemma_54 (x y z w : P.S) :
    P.cp (P.a x (P.a y (P.a z w))) (P.a z w) ≥
    P.cp (P.a x y) (P.a z w) := by
  calc P.cp (P.a x y) (P.a z w)
      = P.cp (P.a (P.a x (P.a y (P.a z w))) (P.a x y)) (P.a z w) :=
        (lemma_53 x y z w).symm
    _ ≤ P.cp (P.a x (P.a y (P.a z w))) (P.a z w) :=
        P.ax_A4 (P.a x (P.a y (P.a z w))) (P.a x y) _

/-- Lemma 55: Pr((X & (Y & (Z & W))) & Z | W) ≥ Pr((X & Y) & Z | W) -/
theorem lemma_55 (x y z w : P.S) :
    P.cp (P.a (P.a x (P.a y (P.a z w))) z) w ≥
    P.cp (P.a (P.a x y) z) w := by
  have h1 := P.ax_A5 (P.a x (P.a y (P.a z w))) z w
  have h2 := P.ax_A5 (P.a x y) z w
  have h54 := lemma_54 x y z w
  have hnn := cp_nonneg z w
  nlinarith

/-- Lemma 56: Pr(X & (Y & (Z & W)) | W) ≥ Pr((X & Y) & Z | W) -/
theorem lemma_56 (x y z w : P.S) :
    P.cp (P.a x (P.a y (P.a z w))) w ≥
    P.cp (P.a (P.a x y) z) w := by
  calc P.cp (P.a (P.a x y) z) w
      ≤ P.cp (P.a (P.a x (P.a y (P.a z w))) z) w := lemma_55 x y z w
    _ ≤ P.cp (P.a x (P.a y (P.a z w))) w :=
        P.ax_A4 (P.a x (P.a y (P.a z w))) z w

/-- Lemma 57: Pr(X & (Y & Z) | W) ≥ Pr((X & Y) & Z | W) -/
theorem cp_right_ge_left (x y z w : P.S) :
    P.cp (P.a x (P.a y z)) w ≥ P.cp (P.a (P.a x y) z) w := by
  calc P.cp (P.a (P.a x y) z) w
      ≤ P.cp (P.a x (P.a y (P.a z w))) w := lemma_56 x y z w
    _ ≤ P.cp (P.a x (P.a y z)) w := lemma_51 x y z w

-- Part 3: The reverse inequality and final associativity

/-- Lemma 61: Pr((X & Y) & Z | W) ≥ Pr(X & (Y & Z) | W) -/
theorem cp_left_ge_right (x y z w : P.S) :
    P.cp (P.a (P.a x y) z) w ≥ P.cp (P.a x (P.a y z)) w := by
  calc P.cp (P.a x (P.a y z)) w
      = P.cp (P.a (P.a y z) x) w := cp_comm x (P.a y z) w
    _ ≤ P.cp (P.a y (P.a z x)) w := cp_right_ge_left y z x w
    _ = P.cp (P.a (P.a z x) y) w := cp_comm y (P.a z x) w
    _ ≤ P.cp (P.a z (P.a x y)) w := cp_right_ge_left z x y w
    _ = P.cp (P.a (P.a x y) z) w := cp_comm z (P.a x y) w

/-- Lemma 62: Pr((X & Y) & Z | W) = Pr(X & (Y & Z) | W) (associativity) -/
theorem cp_assoc (x y z w : P.S) :
    P.cp (P.a (P.a x y) z) w = P.cp (P.a x (P.a y z)) w :=
  le_antisymm (cp_right_ge_left x y z w) (cp_left_ge_right x y z w)

-- ============================================================
-- Complementation (Lemmas 63–70)
-- ============================================================

/-- Lemma 63a: Pr(~Y | Y) ≠ 0 → ∀ Z, Pr(Z | Y) = 1 -/
theorem lemma_63a (y : P.S) (h : P.cp (P.n y) y ≠ 0) :
    ∀ z : P.S, P.cp z y = 1 := by
  intro z
  by_contra hne
  have : P.cp (P.n y) y = 0 := by
    have hk : P.k ≠ P.cp z y := by
      rw [k_eq_one]; exact fun h => hne h.symm
    exact lemma_7 z y hk
  exact h this

/-- Lemma 64b: Pr(~Y | Y) = 0 → Pr(X | Y) + Pr(~X | Y) = 1 + Pr(~Y | Y) -/
theorem lemma_64b (x y : P.S) (h : P.cp (P.n y) y = 0) :
    P.cp x y + P.cp (P.n x) y = 1 + P.cp (P.n y) y := by
  have hne : P.k ≠ P.cp (P.n y) y := by
    rw [k_eq_one]; linarith [cp_nonneg (P.n y) y]
  have h6 := lemma_6a (P.n y) y x hne
  linarith [k_eq_one (P := P)]

/-- Lemma 64c: Pr(~Y | Y) ≠ 0 → Pr(X | Y) + Pr(~X | Y) = 1 + Pr(~Y | Y) -/
theorem lemma_64c (x y : P.S) (h : P.cp (P.n y) y ≠ 0) :
    P.cp x y + P.cp (P.n x) y = 1 + P.cp (P.n y) y := by
  have hall := lemma_63a y h
  rw [hall x, hall (P.n x), hall (P.n y)]

/-- Lemma 64: Pr(X | Y) + Pr(~X | Y) = 1 + Pr(~Y | Y) (complementation law) -/
theorem cp_compl (x y : P.S) :
    P.cp x y + P.cp (P.n x) y = 1 + P.cp (P.n y) y := by
  by_cases h : P.cp (P.n y) y = 0
  · exact lemma_64b x y h
  · exact lemma_64c x y h

/-- Lemma 65: Pr(X | Y) + Pr(~X | Y) = Pr(Z | Y) + Pr(~Z | Y) -/
theorem cp_compl_inv (x y z : P.S) :
    P.cp x y + P.cp (P.n x) y = P.cp z y + P.cp (P.n z) y := by
  linarith [cp_compl x y, cp_compl z y]

/-- Lemma 66: Instance of Lemma 65 with conditioned on Y & W -/
theorem cp_compl_inv_cond (x y z w : P.S) :
    P.cp x (P.a y w) + P.cp (P.n x) (P.a y w) =
    P.cp z (P.a y w) + P.cp (P.n z) (P.a y w) :=
  cp_compl_inv x (P.a y w) z

/-- Lemma 67: Pr(X & Y | W) + Pr(~X & Y | W) = Pr(Z & Y | W) + Pr(~Z & Y | W) -/
theorem cp_conj_compl_inv (x y z w : P.S) :
    P.cp (P.a x y) w + P.cp (P.a (P.n x) y) w =
    P.cp (P.a z y) w + P.cp (P.a (P.n z) y) w := by
  have h66 := cp_compl_inv_cond x y z w
  rw [P.ax_A5 x y w, P.ax_A5 (P.n x) y w, P.ax_A5 z y w, P.ax_A5 (P.n z) y w]
  nlinarith [cp_nonneg y w]

/-- Lemma 68: Pr(X & Y | Z) + Pr(~X & Y | Z) = Pr(Z & Y | Z) + Pr(~Z & Y | Z) -/
theorem lemma_68 (x y z : P.S) :
    P.cp (P.a x y) z + P.cp (P.a (P.n x) y) z =
    P.cp (P.a z y) z + P.cp (P.a (P.n z) y) z :=
  cp_conj_compl_inv x y z z

/-- Lemma 69: Pr(~Z & Y | Z) = Pr(~Z | Z) -/
theorem cp_neg_conj (y z : P.S) :
    P.cp (P.a (P.n z) y) z = P.cp (P.n z) z := by
  by_cases h : P.cp (P.n z) z = 0
  · have hle := P.ax_A4 (P.n z) y z
    have hnn := cp_nonneg (P.a (P.n z) y) z
    linarith
  · have hall := lemma_63a z h
    rw [hall (P.a (P.n z) y), hall (P.n z)]

/-- Lemma 70a_i: Pr(Z | Z & Y) = 1 -/
theorem cp_fst_of_conj (z y : P.S) :
    P.cp z (P.a z y) = 1 := cp_fst_conj z y

/-- Lemma 70a_ii: ∀ U, Pr(Y & Z | U) = Pr(Z & Y | U) -/
theorem cp_conj_comm (y z : P.S) :
    ∀ u : P.S, P.cp (P.a y z) u = P.cp (P.a z y) u :=
  fun u => cp_comm y z u

/-- Lemma 70a_iii: Pr(W | Y & Z) = Pr(W | Z & Y) (via A2) -/
theorem cp_cond_comm (w y z : P.S) :
    P.cp w (P.a y z) = P.cp w (P.a z y) :=
  P.ax_A2 (P.a y z) (P.a z y) (cp_conj_comm y z) w

/-- Lemma 70a: Pr(Z & Y | Z) = Pr(Y | Z) -/
theorem cp_conj_fst_cond (y z : P.S) :
    P.cp (P.a z y) z = P.cp y z := by
  have h := P.ax_A5 z y z
  rw [cp_cond_comm z y z] at h
  rw [h, cp_fst_of_conj z y, one_mul]

/-- Lemma 70: Pr(X & Y | Z) + Pr(~X & Y | Z) = Pr(Y | Z) + Pr(~Z | Z) -/
theorem cp_conj_compl (x y z : P.S) :
    P.cp (P.a x y) z + P.cp (P.a (P.n x) y) z =
    P.cp y z + P.cp (P.n z) z := by
  linarith [lemma_68 x y z, cp_neg_conj y z, cp_conj_fst_cond y z]

-- ============================================================
-- Inclusion-Exclusion (Lemmas 71–80)
-- ============================================================

/-- Lemma 72: Pr(~X & X | Y) = Pr(~Y | Y) -/
theorem cp_contra (x y : P.S) :
    P.cp (P.a (P.n x) x) y = P.cp (P.n y) y := by
  have h70 := cp_conj_compl x x y
  rw [cp_idem] at h70
  linarith

/-- Lemma 73: Pr(~X & X | Y) + Pr(~(~X & X) | Y) = 1 + Pr(~Y | Y) -/
theorem lemma_73 (x y : P.S) :
    P.cp (P.a (P.n x) x) y + P.cp (P.n (P.a (P.n x) x)) y =
    1 + P.cp (P.n y) y :=
  cp_compl (P.a (P.n x) x) y

/-- Lemma 74: Pr(~(~X & X) | Y) = 1 -/
theorem cp_neg_contra (x y : P.S) :
    P.cp (P.n (P.a (P.n x) x)) y = 1 := by
  linarith [lemma_73 x y, cp_contra x y]

/-- Lemma 76: Pr(X & ~Y | Z) = Pr(X | Z) - Pr(X & Y | Z) + Pr(~Z | Z) -/
theorem cp_conj_neg (x y z : P.S) :
    P.cp (P.a x (P.n y)) z =
    P.cp x z - P.cp (P.a x y) z + P.cp (P.n z) z := by
  have h70 := cp_conj_compl y x z
  rw [cp_comm y x z, cp_comm (P.n y) x z] at h70
  linarith

/-- Lemma 77: Pr(~X & ~Y | Z) = Pr(~X | Z) - Pr(~X & Y | Z) + Pr(~Z | Z) -/
theorem lemma_77 (x y z : P.S) :
    P.cp (P.a (P.n x) (P.n y)) z =
    P.cp (P.n x) z - P.cp (P.a (P.n x) y) z + P.cp (P.n z) z :=
  cp_conj_neg (P.n x) y z

/-- Lemma 78: Pr(~X & ~Y | Z) = 1 - Pr(X|Z) - Pr(Y|Z) + Pr(X&Y|Z) + Pr(~Z|Z) -/
theorem cp_demorgan (x y z : P.S) :
    P.cp (P.a (P.n x) (P.n y)) z =
    1 - P.cp x z - P.cp y z + P.cp (P.a x y) z + P.cp (P.n z) z := by
  have h77 := lemma_77 x y z
  have hcx := cp_compl x z
  have h70 := cp_conj_compl x y z
  linarith

/-- Lemma 79: Pr(~(~X & ~Y) | Z) = Pr(X|Z) + Pr(Y|Z) - Pr(X&Y|Z)
    (inclusion-exclusion) -/
theorem cp_incl_excl (x y z : P.S) :
    P.cp (P.n (P.a (P.n x) (P.n y))) z =
    P.cp x z + P.cp y z - P.cp (P.a x y) z := by
  have h78 := cp_demorgan x y z
  have hc := cp_compl (P.a (P.n x) (P.n y)) z
  linarith

/-- Lemma 80: Inclusion-exclusion with arbitrary condition Y & W -/
theorem cp_incl_excl_cond (x y z w : P.S) :
    P.cp (P.n (P.a (P.n y) (P.n z))) (P.a x w) =
    P.cp y (P.a x w) + P.cp z (P.a x w) - P.cp (P.a y z) (P.a x w) :=
  cp_incl_excl y z (P.a x w)

-- ============================================================
-- Distribution (Lemmas 81–86)
-- ============================================================

/-- Lemma 81: Pr(X & ~(~Y & ~Z) | W) = Pr(X&Y|W) + Pr(X&Z|W) - Pr(X&(Y&Z)|W) -/
theorem cp_conj_disj (x y z w : P.S) :
    P.cp (P.a x (P.n (P.a (P.n y) (P.n z)))) w =
    P.cp (P.a x y) w + P.cp (P.a x z) w - P.cp (P.a x (P.a y z)) w := by
  have h80 := cp_incl_excl_cond x y z w
  rw [cp_comm x (P.n (P.a (P.n y) (P.n z))) w,
      cp_comm x y w, cp_comm x z w, cp_comm x (P.a y z) w,
      P.ax_A5 (P.n (P.a (P.n y) (P.n z))) x w,
      P.ax_A5 y x w, P.ax_A5 z x w, P.ax_A5 (P.a y z) x w]
  nlinarith [cp_nonneg x w]

/-- Lemma 82: Pr(X & (Y & Z) | W) = Pr((X & X) & (Y & Z) | W) -/
theorem lemma_82 (x y z w : P.S) :
    P.cp (P.a x (P.a y z)) w = P.cp (P.a (P.a x x) (P.a y z)) w := by
  rw [P.ax_A5 x (P.a y z) w, P.ax_A5 (P.a x x) (P.a y z) w, cp_idem]

/-- Lemma 84: Pr(X & (Y & Z) | W) = Pr((X & Y) & (X & Z) | W) -/
theorem cp_conj_distrib (x y z w : P.S) :
    P.cp (P.a x (P.a y z)) w = P.cp (P.a (P.a x y) (P.a x z)) w :=
  calc P.cp (P.a x (P.a y z)) w
      _ = P.cp (P.a (P.a x x) (P.a y z)) w := lemma_82 x y z w
      _ = P.cp (P.a x (P.a x (P.a y z))) w := cp_assoc x x (P.a y z) w
      _ = P.cp (P.a (P.a x (P.a y z)) x) w := cp_comm x (P.a x (P.a y z)) w
      _ = P.cp (P.a (P.a (P.a x y) z) x) w := by
          rw [P.ax_A5 (P.a x (P.a y z)) x w, P.ax_A5 (P.a (P.a x y) z) x w,
              cp_assoc x y z (P.a x w)]
      _ = P.cp (P.a (P.a x y) (P.a z x)) w := cp_assoc (P.a x y) z x w
      _ = P.cp (P.a (P.a z x) (P.a x y)) w := cp_comm (P.a x y) (P.a z x) w
      _ = P.cp (P.a (P.a x z) (P.a x y)) w := by
          rw [P.ax_A5 (P.a z x) (P.a x y) w, P.ax_A5 (P.a x z) (P.a x y) w,
              cp_comm z x (P.a (P.a x y) w)]
      _ = P.cp (P.a (P.a x y) (P.a x z)) w := cp_comm (P.a x z) (P.a x y) w

/-- Lemma 85: Inclusion-exclusion for X&Y and X&Z -/
theorem lemma_85 (x y z w : P.S) :
    P.cp (P.n (P.a (P.n (P.a x y)) (P.n (P.a x z)))) w =
    P.cp (P.a x y) w + P.cp (P.a x z) w - P.cp (P.a (P.a x y) (P.a x z)) w :=
  cp_incl_excl (P.a x y) (P.a x z) w

/-- Lemma 86: Pr(X & ~(~Y & ~Z) | W) = Pr(~(~(X&Y) & ~(X&Z)) | W) -/
theorem cp_distrib_equiv (x y z w : P.S) :
    P.cp (P.a x (P.n (P.a (P.n y) (P.n z)))) w =
    P.cp (P.n (P.a (P.n (P.a x y)) (P.n (P.a x z)))) w := by
  have h81 := cp_conj_disj x y z w
  have h85 := lemma_85 x y z w
  have h84 := cp_conj_distrib x y z w
  linarith

-- ============================================================
-- Double Negation (Lemmas 87–89)
-- ============================================================

/-- Helper: Pr(~(~Y & ~~Y) | X & Z) = 1 -/
theorem cp_taut_one (x y z : P.S) :
    P.cp (P.n (P.a (P.n y) (P.n (P.n y)))) (P.a x z) = 1 := by
  have hcontra := cp_contra (P.n y) (P.a x z)
  have hcomm := cp_comm (P.n (P.n y)) (P.n y) (P.a x z)
  have hcontra2 : P.cp (P.a (P.n y) (P.n (P.n y))) (P.a x z) =
      P.cp (P.n (P.a x z)) (P.a x z) := by linarith
  have hcl := cp_compl (P.a (P.n y) (P.n (P.n y))) (P.a x z)
  linarith

/-- Lemma 87: Pr(~(~Y & ~~Y) & X | W) = Pr(X | W) -/
theorem cp_taut_conj (x y w : P.S) :
    P.cp (P.a (P.n (P.a (P.n y) (P.n (P.n y)))) x) w = P.cp x w := by
  have h5 := P.ax_A5 (P.n (P.a (P.n y) (P.n (P.n y)))) x w
  rw [cp_taut_one x y w, one_mul] at h5
  exact h5

/-- Lemma 88: Pr(~~X | Z) = Pr(X | Z) (double negation elimination) -/
theorem cp_double_neg (x z : P.S) :
    P.cp (P.n (P.n x)) z = P.cp x z := by
  have h1 := cp_compl (P.n x) z
  have h2 := cp_compl x z
  linarith

/-- Lemma 89: Pr(~~X & Y | Z) = Pr(X & Y | Z) -/
theorem cp_double_neg_conj (x y z : P.S) :
    P.cp (P.a (P.n (P.n x)) y) z = P.cp (P.a x y) z := by
  rw [P.ax_A5 (P.n (P.n x)) y z, P.ax_A5 x y z,
      cp_double_neg x (P.a y z)]

-- ============================================================
-- Substitution Principles (Lemmas 90–100)
-- ============================================================

/-- Lemma 90: Pr(X | Z) = Pr(Y | Z) → Pr(~X | Z) = Pr(~Y | Z) -/
theorem cp_neg_congr (x y z : P.S) (h : P.cp x z = P.cp y z) :
    P.cp (P.n x) z = P.cp (P.n y) z := by
  have h1 := cp_compl x z
  have h2 := cp_compl y z
  linarith

/-- Lemma 91: Pr(~((~X & ~Y) & ~Z) | W) = Pr(~(~X & (~Y & ~Z)) | W) -/
theorem cp_disj_assoc (x y z w : P.S) :
    P.cp (P.n (P.a (P.a (P.n x) (P.n y)) (P.n z))) w =
    P.cp (P.n (P.a (P.n x) (P.a (P.n y) (P.n z)))) w := by
  have hassoc := cp_assoc (P.n x) (P.n y) (P.n z) w
  exact cp_neg_congr _ _ w hassoc

/-- Lemma 93: Pr(~(~X & ~Y) | Z) = Pr(~(~Y & ~X) | Z) -/
theorem cp_disj_comm (x y z : P.S) :
    P.cp (P.n (P.a (P.n x) (P.n y))) z =
    P.cp (P.n (P.a (P.n y) (P.n x))) z := by
  have hcomm := cp_comm (P.n x) (P.n y) z
  exact cp_neg_congr _ _ z hcomm

/-- Lemma 94: Pr(~(~X & ~X) | Y) = Pr(X | Y) -/
theorem cp_disj_idem (x y : P.S) :
    P.cp (P.n (P.a (P.n x) (P.n x))) y = P.cp x y := by
  have hidem := cp_idem (P.n x) y
  have hdneg := cp_double_neg x y
  have hneg := cp_neg_congr _ _ y hidem
  linarith [cp_compl (P.a (P.n x) (P.n x)) y, cp_compl (P.n x) y,
            cp_compl x y]

/-- Lemma 95: Pr(X | Y) = Pr(X | Y & ~(~Z & ~~Z)) -/
theorem cp_cond_taut (x y z : P.S) :
    P.cp x y = P.cp x (P.a y (P.n (P.a (P.n z) (P.n (P.n z))))) := by
  symm
  apply P.ax_A2
  intro u
  rw [cp_comm y (P.n (P.a (P.n z) (P.n (P.n z)))) u,
      P.ax_A5 (P.n (P.a (P.n z) (P.n (P.n z)))) y u,
      cp_taut_one y z u, one_mul]

/-- Lemma 96: Pr(X | Y & ~(~W & W)) = Pr(X | Y) -/
theorem cp_cond_taut' (x y w : P.S) :
    P.cp x (P.a y (P.n (P.a (P.n w) w))) = P.cp x y := by
  symm
  apply P.ax_A2
  intro u
  rw [cp_comm y (P.n (P.a (P.n w) w)) u,
      P.ax_A5 (P.n (P.a (P.n w) w)) y u,
      cp_neg_contra w (P.a y u), one_mul]

/-- Lemma 98: (∀ Z, Pr(X | Z) = Pr(Y | Z)) → Pr(X & W | V) = Pr(Y & W | V) -/
theorem cp_conj_congr_fst (x y w v : P.S)
    (h : ∀ z : P.S, P.cp x z = P.cp y z) :
    P.cp (P.a x w) v = P.cp (P.a y w) v := by
  rw [P.ax_A5 x w v, P.ax_A5 y w v, h (P.a w v)]

/-- Lemma 99: (∀ Z, Pr(X | Z) = Pr(Y | Z)) → Pr(W | X & V) = Pr(W | Y & V) -/
theorem cp_cond_congr (x y w v : P.S)
    (h : ∀ z : P.S, P.cp x z = P.cp y z) :
    P.cp w (P.a x v) = P.cp w (P.a y v) := by
  apply P.ax_A2
  intro u
  exact cp_conj_congr_fst x y v u h

/-- Lemma 100: Pairwise equivalent propositions remain equivalent in conjunctions -/
theorem cp_conj_congr (x y w v u : P.S)
    (hxy : ∀ z : P.S, P.cp x z = P.cp y z)
    (hwv : ∀ z : P.S, P.cp w z = P.cp v z) :
    P.cp (P.a x w) u = P.cp (P.a y v) u := by
  rw [P.ax_A5 x w u, P.ax_A5 y v u, hxy (P.a w u)]
  have : P.cp w u = P.cp v u := hwv u
  have h_cond := cp_cond_congr w v y u hwv
  rw [hwv u, h_cond]

-- ============================================================
-- Boolean Algebra Structure
-- ============================================================

/-- Definition D1: X ≡ Y iff ∀ Z, Pr(X | Z) = Pr(Y | Z) -/
def PEq (P : PopperProbability) (x y : P.S) : Prop :=
  ∀ z : P.S, P.cp x z = P.cp y z

/-- Property (A): Reflexivity -/
theorem peq_refl (x : P.S) : P.PEq x x := fun _ => rfl

/-- Property (B): Symmetry -/
theorem peq_symm (x y : P.S) (h : P.PEq x y) : P.PEq y x :=
  fun z => (h z).symm

/-- Property (C): Transitivity -/
theorem peq_trans (x y z : P.S) (hxy : P.PEq x y) (hyz : P.PEq y z) :
    P.PEq x z :=
  fun w => (hxy w).trans (hyz w)

/-- Property (D): Substitutability in all positions -/
theorem peq_subst_cond (x y w : P.S) (h : P.PEq x y) :
    ∀ v : P.S, P.cp v (P.a x w) = P.cp v (P.a y w) :=
  fun v => cp_cond_congr x y v w h

theorem peq_subst_neg (x y : P.S) (h : P.PEq x y) :
    P.PEq (P.n x) (P.n y) :=
  fun z => cp_neg_congr x y z (h z)

theorem peq_subst_conj (x y w : P.S) (h : P.PEq x y) :
    P.PEq (P.a x w) (P.a y w) :=
  fun z => cp_conj_congr_fst x y w z h

-- D2: X + Y = ~(~X & ~Y) (disjunction, used directly without a new definition)

/-- Axiom (iii): X + Y ≡ Y + X (commutativity of disjunction) -/
theorem disj_comm (x y : P.S) :
    P.PEq (P.n (P.a (P.n x) (P.n y))) (P.n (P.a (P.n y) (P.n x))) :=
  fun z => cp_disj_comm x y z

/-- Axiom (iv): (X + Y) + Z ≡ X + (Y + Z) (associativity of disjunction) -/
theorem disj_assoc (x y z : P.S) :
    P.PEq (P.n (P.a (P.n (P.n (P.a (P.n x) (P.n y)))) (P.n z)))
           (P.n (P.a (P.n x) (P.n (P.n (P.a (P.n y) (P.n z)))))) := by
  intro w
  have h1 := cp_double_neg_conj (P.a (P.n x) (P.n y)) (P.n z) w
  have h2 := cp_double_neg (P.a (P.n y) (P.n z)) w
  have hn1 := cp_neg_congr (P.a (P.n (P.n (P.a (P.n x) (P.n y)))) (P.n z))
    (P.a (P.a (P.n x) (P.n y)) (P.n z)) w h1
  have hassoc := cp_assoc (P.n x) (P.n y) (P.n z) w
  have hn2 := cp_neg_congr (P.a (P.a (P.n x) (P.n y)) (P.n z))
    (P.a (P.n x) (P.a (P.n y) (P.n z))) w hassoc
  have h3 : P.cp (P.a (P.n x) (P.n (P.n (P.a (P.n y) (P.n z))))) w =
    P.cp (P.a (P.n x) (P.a (P.n y) (P.n z))) w := by
    rw [P.ax_A5 (P.n x) (P.n (P.n (P.a (P.n y) (P.n z)))) w,
        P.ax_A5 (P.n x) (P.a (P.n y) (P.n z)) w,
        cp_double_neg (P.a (P.n y) (P.n z)) w,
        cp_cond_congr (P.n (P.n (P.a (P.n y) (P.n z))))
            (P.a (P.n y) (P.n z)) (P.n x) w
            (fun z' => cp_double_neg _ z')]
  have hn3 := cp_neg_congr
    (P.a (P.n x) (P.n (P.n (P.a (P.n y) (P.n z)))))
    (P.a (P.n x) (P.a (P.n y) (P.n z))) w h3
  linarith

/-- Axiom (v): X + X ≡ X (idempotence of disjunction) -/
theorem disj_idem (x : P.S) :
    P.PEq (P.n (P.a (P.n x) (P.n x))) x :=
  fun y => cp_disj_idem x y

-- Axioms (i) and (ii) are closure properties, automatically
-- satisfied by the type system:
-- (i)  If a, b : S then ~(~a & ~b) : S  (closure under disjunction)
-- (ii) If a : S then ~a : S              (closure under negation)

/-- Axiom (vi): (X & Y) + (X & ~Y) ≡ X (complementation law) -/
theorem compl_law (x y : P.S) :
    P.PEq (P.n (P.a (P.n (P.a x y)) (P.n (P.a x (P.n y))))) x :=
  fun w => by
    have h86 := cp_distrib_equiv x y (P.n y) w
    have hcomm := cp_comm x (P.n (P.a (P.n y) (P.n (P.n y)))) w
    have htaut := cp_taut_conj x y w
    linarith

/-- Axiom (vii): There exist distinct elements (non-triviality) -/
theorem nontrivial : ∃ a b : P.S, ¬P.PEq a b := by
  obtain ⟨x, hx⟩ := exists_neg_zero (P := P)
  refine ⟨P.n x, P.n (P.a (P.n x) x), fun h => ?_⟩
  have := h x
  rw [hx, cp_neg_contra x x] at this
  linarith

end PopperProbability
