import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Popper's Axiomatic Theory of Conditional Probability

A Lean 4 formalization of Karl Popper's axiomatic theory of conditional
probability, following the derivations in Appendix *v
("Derivations in the Formal Theory of Probability") of Popper's
*The Logic of Scientific Discovery* (Routledge, 2002).

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
* **Lemmas 87–94**: Complementation, double negation, and Boolean-sum laws
* **Lemmas 95–100**: Absolute/conditional probability and congruence principles
* **Boolean algebra**: The quotient under probabilistic equivalence has a
  nontrivial `BooleanAlgebra` instance (constructed in `QuotientBooleanAlgebra.lean`)
-/

-- ============================================================
-- Axioms
-- ============================================================

/-- Popper's axiomatic system for conditional probability.

  * `S` is a type of propositions/sentences (the class parameter).
  * `cp x y` represents the conditional probability Pr(X | Y).
  * `a x y` represents the conjunction X & Y.
  * `n x` represents the negation ~X.

  The axioms are from Popper's 1955 paper. -/
class PopperProbability (S : Type) where
  /-- Conditional probability: `cp x y` means Pr(X | Y) -/
  cp : S → S → ℝ
  /-- Conjunction: `a x y` means X & Y -/
  a : S → S → S
  /-- Negation: `n x` means ~X -/
  n : S → S
  /-- A1 (Non-triviality): There exist distinct probability values.
      Classically, this is equivalent to Popper's free-variable formulation. -/
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

variable {S : Type} [PopperProbability S]

/-- S is nonempty (follows from A1). -/
instance instNonemptyS : Nonempty S := by
  obtain ⟨x, _, _, _, _⟩ := ax_A1 (S := S)
  exact ⟨x⟩

/-- Popper's free-variable presentation of A1 follows from the compact
    nontriviality field used in `PopperProbability`. -/
theorem ax_A1_popper (x y : S) : ∃ c d : S, cp x y ≠ cp c d := by
  obtain ⟨u, v, c, d, huvcd⟩ := ax_A1 (S := S)
  by_cases h : cp x y = cp u v
  · exact ⟨c, d, fun hcd => huvcd (h.symm.trans hcd)⟩
  · exact ⟨u, v, h⟩

/-- The constant k: the common value of all Pr(X | X).
    By A3, all self-conditional probabilities are equal. -/
noncomputable def k_val : ℝ :=
  cp (Classical.arbitrary S) (Classical.arbitrary S)

/-- Bare `k` automatically resolves the type parameter `S`. -/
local notation "k" => @k_val S _

/-- Lemma 1 (Convention): Every self-conditional probability equals k. -/
theorem cp_self_eq_k (x : S) : cp x x = k := by
  unfold k_val
  exact ax_A3 x _

-- ============================================================
-- Basic Properties (Lemmas 2–5)
-- ============================================================

/-- Lemma 2a: Pr((X & X) & X | X) ≤ Pr(X & X | X) -/
theorem lemma_2a (x : S) :
    cp (a (a x x) x) x ≤ cp (a x x) x :=
  ax_A4 (a x x) x x

/-- Lemma 2b: Pr(X & X | X) ≤ Pr(X | X) -/
theorem lemma_2b (x : S) :
    cp (a x x) x ≤ cp x x :=
  ax_A4 x x x

/-- Lemma 2c: Pr((X & X) & X | X) ≤ k -/
theorem lemma_2c (x : S) :
    cp (a (a x x) x) x ≤ k := by
  calc cp (a (a x x) x) x
      ≤ cp (a x x) x := lemma_2a x
    _ ≤ cp x x := lemma_2b x
    _ = k := cp_self_eq_k x

/-- Lemma 3a: Pr((X & X) & X | X) = Pr(X & X | X & X) · Pr(X | X) -/
theorem lemma_3a (x : S) :
    cp (a (a x x) x) x = cp (a x x) (a x x) * cp x x :=
  ax_A5 (a x x) x x

/-- Lemma 3b: Pr((X & X) & X | X) = k² -/
theorem lemma_3b (x : S) :
    cp (a (a x x) x) x = k * k := by
  rw [lemma_3a x, cp_self_eq_k (a x x), cp_self_eq_k x]

/-- Lemma 4: k² ≤ k -/
theorem k_sq_le_k : k * k ≤ k := by
  have ⟨x, _, _, _, _⟩ := ax_A1 (S := S)
  calc k * k = cp (a (a x x) x) x := (lemma_3b x).symm
    _ ≤ k := lemma_2c x

/-- Lemma 5: 0 ≤ k ∧ k ≤ 1 -/
theorem k_bounds : 0 ≤ k ∧ k ≤ 1 := by
  constructor <;> nlinarith [k_sq_le_k (S := S)]

theorem k_nonneg : 0 ≤ k := k_bounds.1

theorem k_le_one : k ≤ 1 := k_bounds.2

-- ============================================================
-- Non-negativity (Lemmas 6–14)
-- ============================================================

/-- Lemma 6a: If k ≠ Pr(X|Y), then k = Pr(Z|Y) + Pr(~Z|Y) for all Z -/
theorem lemma_6a (x y z : S) (h : k ≠ cp x y) :
    k = cp z y + cp (n z) y := by
  have hself : cp y y = k := cp_self_eq_k y
  have hne : cp y y ≠ cp x y := hself ▸ h
  have := ax_A6 y x z hne
  linarith [cp_self_eq_k y]

/-- Lemma 6: If k ≠ Pr(X|Y), then k = k + Pr(~Y|Y) -/
theorem lemma_6 (x y : S) (h : k ≠ cp x y) :
    k = k + cp (n y) y := by
  have := lemma_6a x y y h
  rw [cp_self_eq_k y] at this
  exact this

/-- Lemma 7: If k ≠ Pr(X|Y), then Pr(~Y|Y) = 0 -/
theorem lemma_7 (x y : S) (h : k ≠ cp x y) :
    cp (n y) y = 0 := by
  linarith [lemma_6 x y h]

/-- Lemma 8: Pr(X & ~Y | Y) = Pr(X | ~Y & Y) · Pr(~Y | Y) -/
theorem lemma_8 (x y : S) :
    cp (a x (n y)) y = cp x (a (n y) y) * cp (n y) y :=
  ax_A5 x (n y) y

/-- Lemma 9a: If k ≠ Pr(X|Y), then Pr(X & ~Y | Y) = 0 -/
theorem lemma_9a (x y : S) (h : k ≠ cp x y) :
    cp (a x (n y)) y = 0 := by
  rw [lemma_8 x y, lemma_7 x y h, mul_zero]

/-- Lemma 9b: Pr(X & ~Y | Y) ≤ Pr(X | Y) -/
theorem lemma_9b (x y : S) :
    cp (a x (n y)) y ≤ cp x y :=
  ax_A4 x (n y) y

/-- Lemma 10: If k ≠ Pr(X|Y), then 0 ≤ Pr(X|Y) -/
theorem lemma_10 (x y : S) (h : k ≠ cp x y) :
    0 ≤ cp x y := by
  linarith [lemma_9a x y h, lemma_9b x y]

/-- Lemma 11: Pr(X|Y) < 0 → k = Pr(X|Y) (contrapositive of Lemma 10) -/
theorem lemma_11 (x y : S) (h : cp x y < 0) :
    k = cp x y := by
  by_contra hne
  linarith [lemma_10 x y hne]

/-- Lemma 12: k = Pr(X|Y) → 0 ≤ Pr(X|Y) -/
theorem lemma_12 (x y : S) (h : k = cp x y) :
    0 ≤ cp x y := by
  rw [← h]; exact k_nonneg

/-- Lemma 14: 0 ≤ Pr(X|Y) for all X, Y (non-negativity) -/
theorem cp_nonneg (x y : S) : 0 ≤ cp x y := by
  by_cases h : k = cp x y
  · exact lemma_12 x y h
  · exact lemma_10 x y h

-- ============================================================
-- Probability Bounds (Lemmas 15–18)
-- ============================================================

/-- Lemma 15: 0 ≤ Pr(~X | Y) -/
theorem cp_neg_nonneg (x y : S) : 0 ≤ cp (n x) y :=
  cp_nonneg (n x) y

/-- Lemma 16a: If k ≠ Pr(X|Y), then k = Pr(X|Y) + Pr(~X|Y) -/
theorem lemma_16a (x y : S) (h : k ≠ cp x y) :
    k = cp x y + cp (n x) y :=
  lemma_6a x y x h

/-- Lemma 16: If k ≠ Pr(X|Y), then k ≥ Pr(X|Y) -/
theorem lemma_16 (x y : S) (h : k ≠ cp x y) :
    k ≥ cp x y := by
  linarith [lemma_16a x y h, cp_neg_nonneg x y]

/-- Lemma 17: Pr(X|Y) ≤ k -/
theorem cp_le_k (x y : S) : cp x y ≤ k := by
  by_cases h : k = cp x y
  · linarith
  · linarith [lemma_16 x y h]

/-- Lemma 18: 0 ≤ Pr(X|Y) ≤ k ≤ 1 -/
theorem cp_bounds (x y : S) : 0 ≤ cp x y ∧ cp x y ≤ k ∧ k ≤ 1 :=
  ⟨cp_nonneg x y, cp_le_k x y, k_le_one⟩

-- ============================================================
-- k = 1 (Lemmas 19–27)
-- ============================================================

/-- Lemma 19: Pr(X | X & X) = k (sandwich argument) -/
theorem cp_self_conj (x : S) : cp x (a x x) = k := by
  apply le_antisymm
  · exact cp_le_k x (a x x)
  · calc k = cp (a x x) (a x x) := (cp_self_eq_k _).symm
      _ ≤ cp x (a x x) := ax_A4 x x (a x x)

/-- Lemma 20: Pr(X | X & (X & X)) = k -/
theorem cp_self_triple_conj (x : S) : cp x (a x (a x x)) = k := by
  apply le_antisymm
  · exact cp_le_k x _
  · calc k = cp (a x (a x x)) (a x (a x x)) :=
          (cp_self_eq_k _).symm
      _ ≤ cp x (a x (a x x)) := ax_A4 x (a x x) _

/-- Lemma 21a: Pr(X & X | X & X) = Pr(X | X & (X & X)) · Pr(X | X & X) -/
theorem lemma_21a (x : S) :
    cp (a x x) (a x x) = cp x (a x (a x x)) * cp x (a x x) :=
  ax_A5 x x (a x x)

/-- Lemma 21: k = k² -/
theorem k_eq_k_sq : k = k * k := by
  have ⟨x, _, _, _, _⟩ := ax_A1 (S := S)
  calc k = cp (a x x) (a x x) := (cp_self_eq_k _).symm
    _ = cp x (a x (a x x)) * cp x (a x x) := lemma_21a x
    _ = k * k := by rw [cp_self_triple_conj x, cp_self_conj x]

/-- Lemma 23: If there exists a non-zero probability, then k = 1 -/
theorem k_eq_one_of_nonzero (h : ∃ x y : S, cp x y ≠ 0) : k = 1 := by
  obtain ⟨x, y, hne⟩ := h
  have hfact : k * (k - 1) = 0 := by nlinarith [k_eq_k_sq (S := S)]
  rcases mul_eq_zero.mp hfact with hk0 | hk1
  · exfalso; apply hne
    have hle : cp x y ≤ k := cp_le_k x y
    have hge : 0 ≤ cp x y := cp_nonneg x y
    linarith
  · linarith

/-- Lemma 24: There exists a non-zero probability -/
theorem exists_nonzero : ∃ x y : S, cp x y ≠ 0 := by
  obtain ⟨x, y, c, d, hne⟩ := ax_A1 (S := S)
  by_contra h
  push_neg at h
  exact hne (by rw [h x y, h c d])

/-- Lemma 25: k = 1 -/
theorem k_eq_one : k = 1 := k_eq_one_of_nonzero exists_nonzero

/-- Corollary: Pr(X | X) = 1 for all X -/
theorem cp_self_eq_one (x : S) : cp x x = 1 := by
  rw [cp_self_eq_k x, k_eq_one]

/-- Lemma 26: There exist X, Y such that Pr(Y | X) ≠ k -/
theorem exists_ne_k : ∃ (x y : S), cp y x ≠ k := by
  obtain ⟨x, y, c, d, hne⟩ := ax_A1 (S := S)
  by_contra h
  push_neg at h
  exact hne (by rw [h y x, h d c])

/-- Lemma 27: There exists X such that Pr(~X | X) = 0 -/
theorem exists_neg_zero : ∃ x : S, cp (n x) x = 0 := by
  obtain ⟨x, y, hne⟩ := exists_ne_k (S := S)
  exact ⟨x, lemma_7 y x hne.symm⟩

-- ============================================================
-- Idempotence (Lemmas 28–30)
-- ============================================================

/-- Lemma 28a: Pr(X & Y | X & Y) = 1 -/
theorem cp_conj_self_eq_one (x y : S) :
    cp (a x y) (a x y) = 1 := cp_self_eq_one _

/-- Lemma 28b: Pr(X & Y | X & Y) ≤ Pr(X | X & Y) -/
theorem lemma_28b (x y : S) :
    cp (a x y) (a x y) ≤ cp x (a x y) :=
  ax_A4 x y (a x y)

/-- Lemma 28c: Pr(X | X & Y) ≤ 1 -/
theorem lemma_28c (x y : S) : cp x (a x y) ≤ 1 := by
  linarith [cp_le_k x (a x y), k_eq_one (S := S)]

/-- Lemma 28: Pr(X | X & Y) = 1 -/
theorem cp_fst_conj (x y : S) : cp x (a x y) = 1 := by
  linarith [cp_conj_self_eq_one x y, lemma_28b x y, lemma_28c x y]

/-- Lemma 29: Pr(X & X | Y) = Pr(X | X & Y) · Pr(X | Y) -/
theorem lemma_29 (x y : S) :
    cp (a x x) y = cp x (a x y) * cp x y :=
  ax_A5 x x y

/-- Lemma 30: Pr(X & X | Y) = Pr(X | Y) (idempotence) -/
theorem cp_idem (x y : S) : cp (a x x) y = cp x y := by
  rw [lemma_29 x y, cp_fst_conj x y, one_mul]

-- ============================================================
-- Commutativity (Lemmas 31–40)
-- ============================================================

/-- Lemma 31: Pr(X | Y & Z) ≤ 1 -/
theorem cp_le_one (x y : S) : cp x y ≤ 1 := by
  linarith [cp_le_k x y, k_eq_one (S := S)]

/-- Lemma 32: Pr(X & Y | Z) ≤ Pr(Y | Z) (second monotony) -/
theorem cp_conj_le_snd (x y z : S) :
    cp (a x y) z ≤ cp y z := by
  have h5 := ax_A5 x y z
  have hle := cp_le_one x (a y z)
  have hnn := cp_nonneg y z
  nlinarith

/-- Lemma 33: Pr(X & (Y & Z) | X & (Y & Z)) = 1 -/
theorem cp_triple_self (x y z : S) :
    cp (a x (a y z)) (a x (a y z)) = 1 :=
  cp_self_eq_one _

/-- Lemma 34: Pr(Y & Z | X & (Y & Z)) = 1 -/
theorem cp_snd_in_conj (x y z : S) :
    cp (a y z) (a x (a y z)) = 1 := by
  apply le_antisymm
  · exact cp_le_one _ _
  · calc (1 : ℝ) = cp (a x (a y z)) (a x (a y z)) :=
          (cp_self_eq_one _).symm
      _ ≤ cp (a y z) (a x (a y z)) := cp_conj_le_snd x (a y z) _

/-- Lemma 35: Pr(Y | X & (Y & Z)) = 1 -/
theorem cp_fst_of_snd_conj (x y z : S) :
    cp y (a x (a y z)) = 1 := by
  apply le_antisymm
  · exact cp_le_one _ _
  · calc (1 : ℝ) = cp (a y z) (a x (a y z)) :=
          (cp_snd_in_conj x y z).symm
      _ ≤ cp y (a x (a y z)) := ax_A4 y z _

/-- Lemma 36: Pr(Y & X | Y & Z) = Pr(X | Y & Z) -/
theorem cp_swap_fst (x y z : S) :
    cp (a y x) (a y z) = cp x (a y z) := by
  have h5 := ax_A5 y x (a y z)
  rw [cp_fst_of_snd_conj x y z, one_mul] at h5
  exact h5

/-- Lemma 37: Pr((Y & X) & Y | Z) = Pr(X & Y | Z) -/
theorem cp_perm_triple (x y z : S) :
    cp (a (a y x) y) z = cp (a x y) z := by
  have h1 := ax_A5 (a y x) y z
  rw [cp_swap_fst x y z] at h1
  linarith [ax_A5 x y z]

/-- Lemma 38: Pr(Y & X | Z) ≥ Pr(X & Y | Z) -/
theorem cp_conj_ge (x y z : S) :
    cp (a y x) z ≥ cp (a x y) z := by
  calc cp (a x y) z = cp (a (a y x) y) z := (cp_perm_triple x y z).symm
    _ ≤ cp (a y x) z := ax_A4 (a y x) y z

/-- Lemma 39: Pr(X & Y | Z) ≥ Pr(Y & X | Z) -/
theorem cp_conj_ge' (x y z : S) :
    cp (a x y) z ≥ cp (a y x) z :=
  cp_conj_ge y x z

/-- Lemma 40: Pr(X & Y | Z) = Pr(Y & X | Z) (commutativity) -/
theorem cp_comm (x y z : S) :
    cp (a x y) z = cp (a y x) z :=
  le_antisymm (cp_conj_ge x y z) (cp_conj_ge' x y z)

-- ============================================================
-- Associativity (Lemmas 41–62)
-- ============================================================

-- Part 1: Showing Pr(X & (Y & Z) | (X & Y) & Z) = 1

/-- Lemma 41: Pr(X & Y | W & ((X & Y) & Z)) = 1 -/
theorem cp_conj_in_assoc (x y z w : S) :
    cp (a x y) (a w (a (a x y) z)) = 1 :=
  cp_fst_of_snd_conj w (a x y) z

/-- Lemma 42c: Pr(X | W & ((X & Y) & Z)) = 1 -/
theorem cp_fst_in_assoc (x y z w : S) :
    cp x (a w (a (a x y) z)) = 1 := by
  apply le_antisymm (cp_le_one _ _)
  calc (1 : ℝ) = cp (a x y) (a w (a (a x y) z)) :=
        (cp_conj_in_assoc x y z w).symm
    _ ≤ cp x (a w (a (a x y) z)) := ax_A4 x y _

/-- Lemma 42: Pr(Y | W & ((X & Y) & Z)) = 1 -/
theorem cp_snd_in_assoc (x y z w : S) :
    cp y (a w (a (a x y) z)) = 1 := by
  apply le_antisymm (cp_le_one _ _)
  calc (1 : ℝ) = cp (a x y) (a w (a (a x y) z)) :=
        (cp_conj_in_assoc x y z w).symm
    _ ≤ cp y (a w (a (a x y) z)) := cp_conj_le_snd x y _

/-- Lemma 43: Pr(X | (Y & Z) & ((X & Y) & Z)) = 1 -/
theorem lemma_43 (x y z : S) :
    cp x (a (a y z) (a (a x y) z)) = 1 :=
  cp_fst_in_assoc x y z (a y z)

/-- Lemma 44: Pr(X & (Y & Z) | (X & Y) & Z) = Pr(Y & Z | (X & Y) & Z) -/
theorem lemma_44 (x y z : S) :
    cp (a x (a y z)) (a (a x y) z) =
    cp (a y z) (a (a x y) z) := by
  have h := ax_A5 x (a y z) (a (a x y) z)
  rw [lemma_43 x y z, one_mul] at h
  exact h

/-- Lemma 46: Pr(Y | Z & ((X & Y) & Z)) = 1 -/
theorem lemma_46 (x y z : S) :
    cp y (a z (a (a x y) z)) = 1 :=
  cp_snd_in_assoc x y z z

/-- Lemma 47: Pr(Z | (X & Y) & Z) = 1 -/
theorem cp_z_in_assoc (x y z : S) :
    cp z (a (a x y) z) = 1 := by
  apply le_antisymm (cp_le_one _ _)
  calc (1 : ℝ) = cp (a (a x y) z) (a (a x y) z) :=
        (cp_self_eq_one _).symm
    _ ≤ cp z (a (a x y) z) := cp_conj_le_snd (a x y) z _

/-- Lemma 48i: Pr(Y & Z | (X & Y) & Z) = 1 -/
theorem lemma_48i (x y z : S) :
    cp (a y z) (a (a x y) z) = 1 := by
  have h := ax_A5 y z (a (a x y) z)
  rw [lemma_46 x y z, cp_z_in_assoc x y z, one_mul] at h
  exact h

/-- Lemma 48: Pr(X & (Y & Z) | (X & Y) & Z) = 1 -/
theorem cp_right_assoc_given_left (x y z : S) :
    cp (a x (a y z)) (a (a x y) z) = 1 := by
  rw [lemma_44 x y z, lemma_48i x y z]

-- Part 2: Three-factor expansion and the key inequalities

/-- Lemma 49: Three-factor expansion of deeply nested conjunction.
    Pr(X & (Y & (Z & W)) | W) = Pr(Z & W | Y & (X & W)) · Pr(Y | X & W) · Pr(X | W) -/
theorem lemma_49 (x y z w : S) :
    cp (a x (a y (a z w))) w =
    cp (a z w) (a y (a x w)) * cp y (a x w) * cp x w := by
  calc cp (a x (a y (a z w))) w
      = cp (a (a y (a z w)) x) w := cp_comm x (a y (a z w)) w
    _ = cp (a y (a z w)) (a x w) * cp x w :=
        ax_A5 (a y (a z w)) x w
    _ = cp (a (a z w) y) (a x w) * cp x w := by
        rw [cp_comm y (a z w) (a x w)]
    _ = cp (a z w) (a y (a x w)) * cp y (a x w) * cp x w := by
        rw [ax_A5 (a z w) y (a x w), mul_assoc]

/-- Lemma 50: Three-factor expansion of triple conjunction.
    Pr(X & (Y & Z) | W) = Pr(Z | Y & (X & W)) · Pr(Y | X & W) · Pr(X | W) -/
theorem lemma_50 (x y z w : S) :
    cp (a x (a y z)) w =
    cp z (a y (a x w)) * cp y (a x w) * cp x w := by
  calc cp (a x (a y z)) w
      = cp (a (a y z) x) w := cp_comm x (a y z) w
    _ = cp (a y z) (a x w) * cp x w :=
        ax_A5 (a y z) x w
    _ = cp (a z y) (a x w) * cp x w := by
        rw [cp_comm y z (a x w)]
    _ = cp z (a y (a x w)) * cp y (a x w) * cp x w := by
        rw [ax_A5 z y (a x w), mul_assoc]

/-- Lemma 51: Pr(X & (Y & Z) | W) ≥ Pr(X & (Y & (Z & W)) | W) -/
theorem lemma_51 (x y z w : S) :
    cp (a x (a y z)) w ≥ cp (a x (a y (a z w))) w := by
  rw [lemma_50, lemma_49]
  have hle := ax_A4 z w (a y (a x w))
  have hnn1 := cp_nonneg y (a x w)
  have hnn2 := cp_nonneg x w
  have hnn3 := cp_nonneg (a z w) (a y (a x w))
  have hnn4 := cp_nonneg z (a y (a x w))
  nlinarith [mul_le_mul_of_nonneg_right hle (mul_nonneg hnn1 hnn2)]

/-- Lemma 52: Pr(X & (Y & (Z & W)) | (X & Y) & (Z & W)) = 1 -/
theorem lemma_52 (x y z w : S) :
    cp (a x (a y (a z w))) (a (a x y) (a z w)) = 1 :=
  cp_right_assoc_given_left x y (a z w)

/-- Lemma 53: Pr((X & (Y & (Z & W))) & (X & Y) | Z & W) = Pr(X & Y | Z & W) -/
theorem lemma_53 (x y z w : S) :
    cp (a (a x (a y (a z w))) (a x y)) (a z w) =
    cp (a x y) (a z w) := by
  have h := ax_A5 (a x (a y (a z w))) (a x y) (a z w)
  rw [lemma_52 x y z w, one_mul] at h
  exact h

/-- Lemma 54: Pr(X & (Y & (Z & W)) | Z & W) ≥ Pr(X & Y | Z & W) -/
theorem lemma_54 (x y z w : S) :
    cp (a x (a y (a z w))) (a z w) ≥
    cp (a x y) (a z w) := by
  calc cp (a x y) (a z w)
      = cp (a (a x (a y (a z w))) (a x y)) (a z w) :=
        (lemma_53 x y z w).symm
    _ ≤ cp (a x (a y (a z w))) (a z w) :=
        ax_A4 (a x (a y (a z w))) (a x y) _

/-- Lemma 55: Pr((X & (Y & (Z & W))) & Z | W) ≥ Pr((X & Y) & Z | W) -/
theorem lemma_55 (x y z w : S) :
    cp (a (a x (a y (a z w))) z) w ≥
    cp (a (a x y) z) w := by
  have h1 := ax_A5 (a x (a y (a z w))) z w
  have h2 := ax_A5 (a x y) z w
  have h54 := lemma_54 x y z w
  have hnn := cp_nonneg z w
  nlinarith

/-- Lemma 56: Pr(X & (Y & (Z & W)) | W) ≥ Pr((X & Y) & Z | W) -/
theorem lemma_56 (x y z w : S) :
    cp (a x (a y (a z w))) w ≥
    cp (a (a x y) z) w := by
  calc cp (a (a x y) z) w
      ≤ cp (a (a x (a y (a z w))) z) w := lemma_55 x y z w
    _ ≤ cp (a x (a y (a z w))) w :=
        ax_A4 (a x (a y (a z w))) z w

/-- Lemma 57: Pr(X & (Y & Z) | W) ≥ Pr((X & Y) & Z | W) -/
theorem cp_right_ge_left (x y z w : S) :
    cp (a x (a y z)) w ≥ cp (a (a x y) z) w := by
  calc cp (a (a x y) z) w
      ≤ cp (a x (a y (a z w))) w := lemma_56 x y z w
    _ ≤ cp (a x (a y z)) w := lemma_51 x y z w

-- Part 3: The reverse inequality and final associativity

/-- Lemma 61: Pr((X & Y) & Z | W) ≥ Pr(X & (Y & Z) | W) -/
theorem cp_left_ge_right (x y z w : S) :
    cp (a (a x y) z) w ≥ cp (a x (a y z)) w := by
  calc cp (a x (a y z)) w
      = cp (a (a y z) x) w := cp_comm x (a y z) w
    _ ≤ cp (a y (a z x)) w := cp_right_ge_left y z x w
    _ = cp (a (a z x) y) w := cp_comm y (a z x) w
    _ ≤ cp (a z (a x y)) w := cp_right_ge_left z x y w
    _ = cp (a (a x y) z) w := cp_comm z (a x y) w

/-- Lemma 62: Pr((X & Y) & Z | W) = Pr(X & (Y & Z) | W) (associativity) -/
theorem cp_assoc (x y z w : S) :
    cp (a (a x y) z) w = cp (a x (a y z)) w :=
  le_antisymm (cp_right_ge_left x y z w) (cp_left_ge_right x y z w)

-- ============================================================
-- Complementation (Lemmas 63–70)
-- ============================================================

/-- Lemma 63a: Pr(~Y | Y) ≠ 0 → ∀ Z, Pr(Z | Y) = 1 -/
theorem lemma_63a (y : S) (h : cp (n y) y ≠ 0) :
    ∀ z : S, cp z y = 1 := by
  intro z
  by_contra hne
  have : cp (n y) y = 0 := by
    have hk : k ≠ cp z y := by
      rw [k_eq_one]; exact fun h => hne h.symm
    exact lemma_7 z y hk
  exact h this

/-- Lemma 64b: Pr(~Y | Y) = 0 → Pr(X | Y) + Pr(~X | Y) = 1 + Pr(~Y | Y) -/
theorem lemma_64b (x y : S) (h : cp (n y) y = 0) :
    cp x y + cp (n x) y = 1 + cp (n y) y := by
  have hne : k ≠ cp (n y) y := by
    rw [k_eq_one]; linarith [cp_nonneg (n y) y]
  have h6 := lemma_6a (n y) y x hne
  linarith [k_eq_one (S := S)]

/-- Lemma 64c: Pr(~Y | Y) ≠ 0 → Pr(X | Y) + Pr(~X | Y) = 1 + Pr(~Y | Y) -/
theorem lemma_64c (x y : S) (h : cp (n y) y ≠ 0) :
    cp x y + cp (n x) y = 1 + cp (n y) y := by
  have hall := lemma_63a y h
  rw [hall x, hall (n x), hall (n y)]

/-- Lemma 64: Pr(X | Y) + Pr(~X | Y) = 1 + Pr(~Y | Y) (complementation law) -/
theorem cp_compl (x y : S) :
    cp x y + cp (n x) y = 1 + cp (n y) y := by
  by_cases h : cp (n y) y = 0
  · exact lemma_64b x y h
  · exact lemma_64c x y h

/-- Lemma 65: Pr(X | Y) + Pr(~X | Y) = Pr(Z | Y) + Pr(~Z | Y) -/
theorem cp_compl_inv (x y z : S) :
    cp x y + cp (n x) y = cp z y + cp (n z) y := by
  linarith [cp_compl x y, cp_compl z y]

/-- Lemma 66: Instance of Lemma 65 with conditioned on Y & W -/
theorem cp_compl_inv_cond (x y z w : S) :
    cp x (a y w) + cp (n x) (a y w) =
    cp z (a y w) + cp (n z) (a y w) :=
  cp_compl_inv x (a y w) z

/-- Lemma 67: Pr(X & Y | W) + Pr(~X & Y | W) = Pr(Z & Y | W) + Pr(~Z & Y | W) -/
theorem cp_conj_compl_inv (x y z w : S) :
    cp (a x y) w + cp (a (n x) y) w =
    cp (a z y) w + cp (a (n z) y) w := by
  have h66 := cp_compl_inv_cond x y z w
  rw [ax_A5 x y w, ax_A5 (n x) y w, ax_A5 z y w, ax_A5 (n z) y w]
  nlinarith [cp_nonneg y w]

/-- Lemma 68: Pr(X & Y | Z) + Pr(~X & Y | Z) = Pr(Z & Y | Z) + Pr(~Z & Y | Z) -/
theorem lemma_68 (x y z : S) :
    cp (a x y) z + cp (a (n x) y) z =
    cp (a z y) z + cp (a (n z) y) z :=
  cp_conj_compl_inv x y z z

/-- Lemma 69: Pr(~Z & Y | Z) = Pr(~Z | Z) -/
theorem cp_neg_conj (y z : S) :
    cp (a (n z) y) z = cp (n z) z := by
  by_cases h : cp (n z) z = 0
  · have hle := ax_A4 (n z) y z
    have hnn := cp_nonneg (a (n z) y) z
    linarith
  · have hall := lemma_63a z h
    rw [hall (a (n z) y), hall (n z)]

/-- Lemma 70a_i: Pr(Z | Z & Y) = 1 -/
theorem cp_fst_of_conj (z y : S) :
    cp z (a z y) = 1 := cp_fst_conj z y

/-- Lemma 70a_ii: ∀ U, Pr(Y & Z | U) = Pr(Z & Y | U) -/
theorem cp_conj_comm (y z : S) :
    ∀ u : S, cp (a y z) u = cp (a z y) u :=
  fun u => cp_comm y z u

/-- Lemma 70a_iii: Pr(W | Y & Z) = Pr(W | Z & Y) (via A2) -/
theorem cp_cond_comm (w y z : S) :
    cp w (a y z) = cp w (a z y) :=
  ax_A2 (a y z) (a z y) (cp_conj_comm y z) w

/-- Lemma 70a: Pr(Z & Y | Z) = Pr(Y | Z) -/
theorem cp_conj_fst_cond (y z : S) :
    cp (a z y) z = cp y z := by
  have h := ax_A5 z y z
  rw [cp_cond_comm z y z] at h
  rw [h, cp_fst_of_conj z y, one_mul]

/-- Lemma 70: Pr(X & Y | Z) + Pr(~X & Y | Z) = Pr(Y | Z) + Pr(~Z | Z) -/
theorem cp_conj_compl (x y z : S) :
    cp (a x y) z + cp (a (n x) y) z =
    cp y z + cp (n z) z := by
  linarith [lemma_68 x y z, cp_neg_conj y z, cp_conj_fst_cond y z]

-- ============================================================
-- Inclusion-Exclusion (Lemmas 71–80)
-- ============================================================

/-- Lemma 72: Pr(~X & X | Y) = Pr(~Y | Y) -/
theorem cp_contra (x y : S) :
    cp (a (n x) x) y = cp (n y) y := by
  have h70 := cp_conj_compl x x y
  rw [cp_idem] at h70
  linarith

/-- Lemma 73: Pr(~X & X | Y) + Pr(~(~X & X) | Y) = 1 + Pr(~Y | Y) -/
theorem lemma_73 (x y : S) :
    cp (a (n x) x) y + cp (n (a (n x) x)) y =
    1 + cp (n y) y :=
  cp_compl (a (n x) x) y

/-- Lemma 74: Pr(~(~X & X) | Y) = 1 -/
theorem cp_neg_contra (x y : S) :
    cp (n (a (n x) x)) y = 1 := by
  linarith [lemma_73 x y, cp_contra x y]

/-- The mirror form of Lemma 74: Pr(~(X & ~X) | Y) = 1. -/
theorem cp_neg_contra_mirror (x y : S) :
    cp (n (a x (n x))) y = 1 := by
  have hcomm := cp_comm x (n x) y
  have hc₁ := cp_compl (a x (n x)) y
  have hc₂ := cp_compl (a (n x) x) y
  linarith [cp_neg_contra x y]

/-- Absolute probability, defined as conditioning on a canonical tautology. -/
noncomputable def absProb (x : S) : ℝ :=
  cp x (n (a (n (Classical.arbitrary S)) (Classical.arbitrary S)))

/-- Lemma 75: absolute probability may be evaluated using any tautology
    of the form `~(~Y & Y)`. -/
theorem absProb_eq_cp_neg_contra (x y : S) :
    absProb x = cp x (n (a (n y) y)) := by
  unfold absProb
  apply ax_A2
  intro z
  rw [cp_neg_contra, cp_neg_contra]

/-- The mirror form of Lemma 75, using `~(Y & ~Y)`. -/
theorem absProb_eq_cp_neg_contra_mirror (x y : S) :
    absProb x = cp x (n (a y (n y))) := by
  calc
    absProb x = cp x (n (a (n y) y)) := absProb_eq_cp_neg_contra x y
    _ = cp x (n (a y (n y))) := by
      apply ax_A2
      intro z
      rw [cp_neg_contra, cp_neg_contra_mirror]

/-- The four displayed forms in Popper's Lemma 75. -/
theorem absProb_forms (x y : S) :
    absProb x = cp x (n (a (n x) x)) ∧
    absProb x = cp x (n (a x (n x))) ∧
    absProb x = cp x (n (a (n y) y)) ∧
    absProb x = cp x (n (a y (n y))) :=
  ⟨absProb_eq_cp_neg_contra x x,
   absProb_eq_cp_neg_contra_mirror x x,
   absProb_eq_cp_neg_contra x y,
   absProb_eq_cp_neg_contra_mirror x y⟩

/-- Lemma 76: Pr(X & ~Y | Z) = Pr(X | Z) - Pr(X & Y | Z) + Pr(~Z | Z) -/
theorem cp_conj_neg (x y z : S) :
    cp (a x (n y)) z =
    cp x z - cp (a x y) z + cp (n z) z := by
  have h70 := cp_conj_compl y x z
  rw [cp_comm y x z, cp_comm (n y) x z] at h70
  linarith

/-- Lemma 77: Pr(~X & ~Y | Z) = Pr(~X | Z) - Pr(~X & Y | Z) + Pr(~Z | Z) -/
theorem lemma_77 (x y z : S) :
    cp (a (n x) (n y)) z =
    cp (n x) z - cp (a (n x) y) z + cp (n z) z :=
  cp_conj_neg (n x) y z

/-- Lemma 78: Pr(~X & ~Y | Z) = 1 - Pr(X|Z) - Pr(Y|Z) + Pr(X&Y|Z) + Pr(~Z|Z) -/
theorem cp_demorgan (x y z : S) :
    cp (a (n x) (n y)) z =
    1 - cp x z - cp y z + cp (a x y) z + cp (n z) z := by
  have h77 := lemma_77 x y z
  have hcx := cp_compl x z
  have h70 := cp_conj_compl x y z
  linarith

/-- Lemma 79: Pr(~(~X & ~Y) | Z) = Pr(X|Z) + Pr(Y|Z) - Pr(X&Y|Z)
    (inclusion-exclusion) -/
theorem cp_incl_excl (x y z : S) :
    cp (n (a (n x) (n y))) z =
    cp x z + cp y z - cp (a x y) z := by
  have h78 := cp_demorgan x y z
  have hc := cp_compl (a (n x) (n y)) z
  linarith

/-- Lemma 80: Inclusion-exclusion with arbitrary condition Y & W -/
theorem cp_incl_excl_cond (x y z w : S) :
    cp (n (a (n y) (n z))) (a x w) =
    cp y (a x w) + cp z (a x w) - cp (a y z) (a x w) :=
  cp_incl_excl y z (a x w)

-- ============================================================
-- Distribution (Lemmas 81–86)
-- ============================================================

/-- Lemma 81: Pr(X & ~(~Y & ~Z) | W) = Pr(X&Y|W) + Pr(X&Z|W) - Pr(X&(Y&Z)|W) -/
theorem cp_conj_disj (x y z w : S) :
    cp (a x (n (a (n y) (n z)))) w =
    cp (a x y) w + cp (a x z) w - cp (a x (a y z)) w := by
  have h80 := cp_incl_excl_cond x y z w
  rw [cp_comm x (n (a (n y) (n z))) w,
      cp_comm x y w, cp_comm x z w, cp_comm x (a y z) w,
      ax_A5 (n (a (n y) (n z))) x w,
      ax_A5 y x w, ax_A5 z x w, ax_A5 (a y z) x w]
  nlinarith [cp_nonneg x w]

/-- Lemma 82: Pr(X & (Y & Z) | W) = Pr((X & X) & (Y & Z) | W) -/
theorem lemma_82 (x y z w : S) :
    cp (a x (a y z)) w = cp (a (a x x) (a y z)) w := by
  rw [ax_A5 x (a y z) w, ax_A5 (a x x) (a y z) w, cp_idem]

/-- Lemma 84: Pr(X & (Y & Z) | W) = Pr((X & Y) & (X & Z) | W) -/
theorem cp_conj_distrib (x y z w : S) :
    cp (a x (a y z)) w = cp (a (a x y) (a x z)) w :=
  calc cp (a x (a y z)) w
      _ = cp (a (a x x) (a y z)) w := lemma_82 x y z w
      _ = cp (a x (a x (a y z))) w := cp_assoc x x (a y z) w
      _ = cp (a (a x (a y z)) x) w := cp_comm x (a x (a y z)) w
      _ = cp (a (a (a x y) z) x) w := by
          rw [ax_A5 (a x (a y z)) x w, ax_A5 (a (a x y) z) x w,
              cp_assoc x y z (a x w)]
      _ = cp (a (a x y) (a z x)) w := cp_assoc (a x y) z x w
      _ = cp (a (a z x) (a x y)) w := cp_comm (a x y) (a z x) w
      _ = cp (a (a x z) (a x y)) w := by
          rw [ax_A5 (a z x) (a x y) w, ax_A5 (a x z) (a x y) w,
              cp_comm z x (a (a x y) w)]
      _ = cp (a (a x y) (a x z)) w := cp_comm (a x z) (a x y) w

/-- Lemma 85: Inclusion-exclusion for X&Y and X&Z -/
theorem lemma_85 (x y z w : S) :
    cp (n (a (n (a x y)) (n (a x z)))) w =
    cp (a x y) w + cp (a x z) w - cp (a (a x y) (a x z)) w :=
  cp_incl_excl (a x y) (a x z) w

/-- Lemma 86: Pr(X & ~(~Y & ~Z) | W) = Pr(~(~(X&Y) & ~(X&Z)) | W) -/
theorem cp_distrib_equiv (x y z w : S) :
    cp (a x (n (a (n y) (n z)))) w =
    cp (n (a (n (a x y)) (n (a x z)))) w := by
  have h81 := cp_conj_disj x y z w
  have h85 := lemma_85 x y z w
  have h84 := cp_conj_distrib x y z w
  linarith

-- ============================================================
-- Complementation and Double Negation (Lemmas 87–89)
-- ============================================================

/-- Helper: Pr(~(~Y & ~~Y) | X & Z) = 1 -/
theorem cp_taut_one (x y z : S) :
    cp (n (a (n y) (n (n y)))) (a x z) = 1 := by
  have hcontra := cp_contra (n y) (a x z)
  have hcomm := cp_comm (n (n y)) (n y) (a x z)
  have hcontra2 : cp (a (n y) (n (n y))) (a x z) =
      cp (n (a x z)) (a x z) := by linarith
  have hcl := cp_compl (a (n y) (n (n y))) (a x z)
  linarith

/-- Lemma 87: Pr(~(~Y & ~~Y) & X | W) = Pr(X | W) -/
theorem cp_taut_conj (x y w : S) :
    cp (a (n (a (n y) (n (n y)))) x) w = cp x w := by
  have h5 := ax_A5 (n (a (n y) (n (n y)))) x w
  rw [cp_taut_one x y w, one_mul] at h5
  exact h5

/-- Lemma 88: Pr((X&Y) + (X&~Y) | W) = Pr(X | W). -/
theorem cp_complementation (x y w : S) :
    cp (n (a (n (a x y)) (n (a x (n y))))) w = cp x w := by
  have h86 := cp_distrib_equiv x y (n y) w
  have hcomm := cp_comm x (n (a (n y) (n (n y)))) w
  have htaut := cp_taut_conj x y w
  linarith

/-- Auxiliary double-negation elimination used in Lemma 89. -/
theorem cp_double_neg (x z : S) :
    cp (n (n x)) z = cp x z := by
  have h1 := cp_compl (n x) z
  have h2 := cp_compl x z
  linarith

/-- Lemma 89: Pr(~~X & Y | Z) = Pr(X & Y | Z) -/
theorem cp_double_neg_conj (x y z : S) :
    cp (a (n (n x)) y) z = cp (a x y) z := by
  rw [ax_A5 (n (n x)) y z, ax_A5 x y z,
      cp_double_neg x (a y z)]

-- ============================================================
-- Boolean Sum and Substitution Principles (Lemmas 90–100)
-- ============================================================

/-- Lemma 90: Pr(X | Z) = Pr(Y | Z) → Pr(~X | Z) = Pr(~Y | Z) -/
theorem cp_neg_congr (x y z : S) (h : cp x z = cp y z) :
    cp (n x) z = cp (n y) z := by
  have h1 := cp_compl x z
  have h2 := cp_compl y z
  linarith

/-- Lemma 91: Pr(~((~X & ~Y) & ~Z) | W) = Pr(~(~X & (~Y & ~Z)) | W) -/
theorem cp_disj_assoc (x y z w : S) :
    cp (n (a (a (n x) (n y)) (n z))) w =
    cp (n (a (n x) (a (n y) (n z)))) w := by
  have hassoc := cp_assoc (n x) (n y) (n z) w
  exact cp_neg_congr _ _ w hassoc

/-- Lemma 93: Pr(~(~X & ~Y) | Z) = Pr(~(~Y & ~X) | Z) -/
theorem cp_disj_comm (x y z : S) :
    cp (n (a (n x) (n y))) z =
    cp (n (a (n y) (n x))) z := by
  have hcomm := cp_comm (n x) (n y) z
  exact cp_neg_congr _ _ z hcomm

/-- Lemma 94: Pr(~(~X & ~X) | Y) = Pr(X | Y) -/
theorem cp_disj_idem (x y : S) :
    cp (n (a (n x) (n x))) y = cp x y := by
  have hidem := cp_idem (n x) y
  have hdneg := cp_double_neg x y
  have hneg := cp_neg_congr _ _ y hidem
  linarith [cp_compl (a (n x) (n x)) y, cp_compl (n x) y,
            cp_compl x y]

/-- Lemma 95: Pr(X | Y) = Pr(X | Y & ~(~Z & ~~Z)) -/
theorem cp_cond_taut (x y z : S) :
    cp x y = cp x (a y (n (a (n z) (n (n z))))) := by
  symm
  apply ax_A2
  intro u
  rw [cp_comm y (n (a (n z) (n (n z)))) u,
      ax_A5 (n (a (n z) (n (n z)))) y u,
      cp_taut_one y z u, one_mul]

/-- Auxiliary mirror form of Lemma 95. -/
theorem cp_cond_taut' (x y w : S) :
    cp x (a y (n (a (n w) w))) = cp x y := by
  symm
  apply ax_A2
  intro u
  rw [cp_comm y (n (a (n w) w)) u,
      ax_A5 (n (a (n w) w)) y u,
      cp_neg_contra w (a y u), one_mul]

/-- Lemma 96: Pr(X | Y) * Pr(Y) = Pr(X & Y). -/
theorem absProb_mul (x y : S) :
    cp x y * absProb y = absProb (a x y) := by
  unfold absProb
  rw [ax_A5, cp_cond_taut']

/-- Lemma 97: if Pr(Y) is nonzero, then
    Pr(X | Y) = Pr(X & Y) / Pr(Y). -/
theorem cp_eq_absProb_div (x y : S) (h : absProb y ≠ 0) :
    cp x y = absProb (a x y) / absProb y := by
  exact (eq_div_iff h).2 (absProb_mul x y)

/-- Lemma 98: (∀ Z, Pr(X | Z) = Pr(Y | Z)) → Pr(X & W | V) = Pr(Y & W | V) -/
theorem cp_conj_congr_fst (x y w v : S)
    (h : ∀ z : S, cp x z = cp y z) :
    cp (a x w) v = cp (a y w) v := by
  rw [ax_A5 x w v, ax_A5 y w v, h (a w v)]

/-- Lemma 99: (∀ Z, Pr(X | Z) = Pr(Y | Z)) → Pr(W | X & V) = Pr(W | Y & V) -/
theorem cp_cond_congr (x y w v : S)
    (h : ∀ z : S, cp x z = cp y z) :
    cp w (a x v) = cp w (a y v) := by
  apply ax_A2
  intro u
  exact cp_conj_congr_fst x y v u h

/-- Lemma 100: Pairwise equivalent propositions remain equivalent in conjunctions -/
theorem cp_conj_congr (x y w v u : S)
    (hxy : ∀ z : S, cp x z = cp y z)
    (hwv : ∀ z : S, cp w z = cp v z) :
    cp (a x w) u = cp (a y v) u := by
  rw [ax_A5 x w u, ax_A5 y v u, hxy (a w u)]
  have h_cond := cp_cond_congr w v y u hwv
  rw [hwv u, h_cond]

-- ============================================================
-- Boolean Equivalence and Huntington Axioms
-- ============================================================

/-- Definition D1: X ≡ Y iff ∀ Z, Pr(X | Z) = Pr(Y | Z) -/
def PEq (x y : S) : Prop :=
  ∀ z : S, cp x z = cp y z

/-- Property (A): Reflexivity -/
theorem peq_refl (x : S) : PEq x x := fun _ => rfl

/-- Property (B): Symmetry -/
theorem peq_symm (x y : S) (h : PEq x y) : PEq y x :=
  fun z => (h z).symm

/-- Property (C): Transitivity -/
theorem peq_trans (x y z : S) (hxy : PEq x y) (hyz : PEq y z) :
    PEq x z :=
  fun w => (hxy w).trans (hyz w)

/-- Substitution of equivalent propositions in a conjunct occurring as a
    conditioning argument. -/
theorem peq_subst_cond (x y w : S) (h : PEq x y) :
    ∀ v : S, cp v (a x w) = cp v (a y w) :=
  fun v => cp_cond_congr x y v w h

theorem peq_subst_neg (x y : S) (h : PEq x y) :
    PEq (n x) (n y) :=
  fun z => cp_neg_congr x y z (h z)

theorem peq_subst_conj (x y w : S) (h : PEq x y) :
    PEq (a x w) (a y w) :=
  fun z => cp_conj_congr_fst x y w z h

/-- Simultaneous substitution in both arguments of conjunction. -/
theorem peq_subst_conj₂ (x x' y y' : S) (hx : PEq x x') (hy : PEq y y') :
    PEq (a x y) (a x' y') :=
  fun z => cp_conj_congr x x' y y' z hx hy

/-- Simultaneous substitution in both arguments of conditional probability. -/
theorem peq_subst_cp (x x' y y' : S) (hx : PEq x x') (hy : PEq y y') :
    cp x y = cp x' y' :=
  (hx y).trans (ax_A2 y y' hy x')

/-- Definition D2: Boolean sum (disjunction). -/
def disj (x y : S) : S :=
  n (a (n x) (n y))

/-- Simultaneous substitution in both arguments of disjunction. -/
theorem peq_subst_disj (x x' y y' : S) (hx : PEq x x') (hy : PEq y y') :
    PEq (disj x y) (disj x' y') := by
  apply peq_subst_neg
  exact peq_subst_conj₂ _ _ _ _ (peq_subst_neg x x' hx) (peq_subst_neg y y' hy)

/-- Axiom (iii): X + Y ≡ Y + X (commutativity of disjunction) -/
theorem disj_comm (x y : S) :
    PEq (disj x y) (disj y x) :=
  fun z => by simpa [disj] using cp_disj_comm x y z

/-- Lemma 92 / Axiom (iv): (X + Y) + Z ≡ X + (Y + Z). -/
theorem disj_assoc (x y z : S) :
    PEq (disj (disj x y) z) (disj x (disj y z)) := by
  intro w
  have h1 := cp_double_neg_conj (a (n x) (n y)) (n z) w
  have hn1 := cp_neg_congr (a (n (n (a (n x) (n y)))) (n z))
    (a (a (n x) (n y)) (n z)) w h1
  have hassoc := cp_assoc (n x) (n y) (n z) w
  have hn2 := cp_neg_congr (a (a (n x) (n y)) (n z))
    (a (n x) (a (n y) (n z))) w hassoc
  have h3 : cp (a (n x) (n (n (a (n y) (n z))))) w =
    cp (a (n x) (a (n y) (n z))) w := by
    rw [ax_A5 (n x) (n (n (a (n y) (n z)))) w,
        ax_A5 (n x) (a (n y) (n z)) w,
        cp_double_neg (a (n y) (n z)) w,
        cp_cond_congr (n (n (a (n y) (n z))))
            (a (n y) (n z)) (n x) w
            (fun z' => cp_double_neg _ z')]
  have hn3 := cp_neg_congr
    (a (n x) (n (n (a (n y) (n z)))))
    (a (n x) (a (n y) (n z))) w h3
  simpa [disj] using hn1.trans (hn2.trans hn3.symm)

/-- Axiom (v): X + X ≡ X (idempotence of disjunction) -/
theorem disj_idem (x : S) :
    PEq (disj x x) x :=
  fun y => by simpa [disj] using cp_disj_idem x y

-- Axioms (i) and (ii) are closure properties, automatically
-- satisfied by the type system:
-- (i)  If x, y : S then disj x y : S              (closure under disjunction)
-- (ii) If x : S then n x : S                    (closure under negation)

/-- Axiom (vi): (X & Y) + (X & ~Y) ≡ X (complementation law) -/
theorem compl_law (x y : S) :
    PEq (disj (a x y) (a x (n y))) x :=
  fun w => by simpa [disj] using cp_complementation x y w

/-- Axiom (vii): There exist distinct elements (non-triviality) -/
theorem nontrivial : ∃ x y : S, ¬PEq x y := by
  obtain ⟨x, hx⟩ := exists_neg_zero (S := S)
  refine ⟨n x, n (a (n x) x), fun h => ?_⟩
  have := h x
  rw [hx, cp_neg_contra x x] at this
  linarith

end PopperProbability
