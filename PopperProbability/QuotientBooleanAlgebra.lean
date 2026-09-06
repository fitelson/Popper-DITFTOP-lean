import PopperProbability.Popper

/-!
# The Boolean Algebra of Popper Events

This file forms the quotient of the proposition type by Popper's probabilistic
equivalence `PEq`. Conjunction, disjunction, and negation descend to the
quotient, where they determine a nontrivial Mathlib `BooleanAlgebra`.
-/

namespace PopperProbability

variable {S : Type} [PopperProbability S]

/-- Probabilistic equivalence as a Lean setoid. -/
def peqSetoid (S : Type) [PopperProbability S] : Setoid S where
  r := PEq
  iseqv :=
    ⟨peq_refl, (fun h => peq_symm _ _ h),
      (fun h₁ h₂ => peq_trans _ _ _ h₁ h₂)⟩

/-- Propositions modulo probabilistic equivalence. -/
abbrev EventQuotient (S : Type) [PopperProbability S] :=
  Quotient (peqSetoid S)

namespace EventQuotient

/-- Equality of quotient classes is exactly probabilistic equivalence. -/
theorem mk_eq_mk_iff (x y : S) :
    Quotient.mk (peqSetoid S) x = Quotient.mk (peqSetoid S) y ↔ PEq x y :=
  ⟨Quotient.exact, Quot.sound⟩

/-- Popper's substitution principle (D): equal quotient elements may be
    substituted in every quotient-valued or externally valued expression. -/
theorem substitution {α : Sort*} (f : EventQuotient S → α)
    {x y : EventQuotient S} (h : x = y) : f x = f y :=
  congrArg f h

/-- Proposition-valued form of Popper's substitution principle (D). -/
theorem substitution_iff (p : EventQuotient S → Prop)
    {x y : EventQuotient S} (h : x = y) : p x ↔ p y := by
  subst y
  rfl

instance instMin : Min (EventQuotient S) where
  min := Quotient.map₂ a fun {_ _} hx {_ _} hy => by
    change PEq _ _ at hx
    change PEq _ _ at hy
    change PEq _ _
    exact peq_subst_conj₂ _ _ _ _ hx hy

instance instMax : Max (EventQuotient S) where
  max := Quotient.map₂ disj fun {_ _} hx {_ _} hy => by
    change PEq _ _ at hx
    change PEq _ _ at hy
    change PEq _ _
    exact peq_subst_disj _ _ _ _ hx hy

instance instCompl : Compl (EventQuotient S) where
  compl := Quotient.map n fun {_ _} h => by
    change PEq _ _ at h
    change PEq _ _
    exact peq_subst_neg _ _ h

private theorem inf_comm_q (x y : EventQuotient S) : x ⊓ y = y ⊓ x := by
  induction x, y using Quotient.inductionOn₂ with
  | _ x y => exact Quot.sound (fun z => cp_comm x y z)

private theorem inf_assoc_q (x y z : EventQuotient S) :
    x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  induction x, y, z using Quotient.inductionOn₃ with
  | _ x y z => exact Quot.sound (fun w => cp_assoc x y z w)

private theorem sup_comm_q (x y : EventQuotient S) : x ⊔ y = y ⊔ x := by
  induction x, y using Quotient.inductionOn₂ with
  | _ x y => exact Quot.sound (disj_comm x y)

private theorem sup_assoc_q (x y z : EventQuotient S) :
    x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  induction x, y, z using Quotient.inductionOn₃ with
  | _ x y z => exact Quot.sound (disj_assoc x y z)

private theorem peq_sup_inf_self (x y : S) : PEq (disj x (a x y)) x := by
  intro z
  have hxx : cp (a x (a x y)) z = cp (a x y) z := by
    calc
      cp (a x (a x y)) z = cp (a (a x x) y) z := (cp_assoc x x y z).symm
      _ = cp (a x y) z :=
        cp_conj_congr_fst (a x x) x y z (fun u => cp_idem x u)
  unfold disj
  rw [cp_incl_excl]
  linarith

private theorem sup_inf_self_q (x y : EventQuotient S) :
    x ⊔ x ⊓ y = x := by
  induction x, y using Quotient.inductionOn₂ with
  | _ x y => exact Quot.sound (peq_sup_inf_self x y)

private theorem peq_inf_sup_self (x y : S) : PEq (a x (disj x y)) x := by
  apply peq_trans (x := a x (disj x y))
    (y := disj (a x x) (a x y)) (z := x)
  · intro w
    exact cp_distrib_equiv x x y w
  · apply peq_trans (y := disj x (a x y))
    · exact peq_subst_disj _ _ _ _ (fun w => cp_idem x w) (peq_refl _)
    · exact peq_sup_inf_self x y

private theorem inf_sup_self_q (x y : EventQuotient S) :
    x ⊓ (x ⊔ y) = x := by
  induction x, y using Quotient.inductionOn₂ with
  | _ x y => exact Quot.sound (peq_inf_sup_self x y)

noncomputable instance instLattice : Lattice (EventQuotient S) :=
  Lattice.mk' sup_comm_q sup_assoc_q inf_comm_q inf_assoc_q
    sup_inf_self_q inf_sup_self_q

private theorem inf_sup_distrib_q (x y z : EventQuotient S) :
    x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z := by
  induction x, y, z using Quotient.inductionOn₃ with
  | _ x y z => exact Quot.sound (fun w => cp_distrib_equiv x y z w)

noncomputable instance instDistribLattice : DistribLattice (EventQuotient S) :=
  DistribLattice.ofInfSupLe fun x y z => (inf_sup_distrib_q x y z).le

private noncomputable def topRep : S :=
  n (a (n (Classical.arbitrary S)) (Classical.arbitrary S))

private noncomputable def botRep : S :=
  a (n (Classical.arbitrary S)) (Classical.arbitrary S)

noncomputable instance instTop : Top (EventQuotient S) :=
  ⟨Quotient.mk (peqSetoid S) topRep⟩

noncomputable instance instBot : Bot (EventQuotient S) :=
  ⟨Quotient.mk (peqSetoid S) botRep⟩

private theorem peq_inf_top (x : S) : PEq (a x topRep) x := by
  intro z
  calc
    cp (a x topRep) z = cp (a topRep x) z := cp_comm x topRep z
    _ = cp topRep (a x z) * cp x z := ax_A5 topRep x z
    _ = cp x z := by
      unfold topRep
      rw [cp_neg_contra, one_mul]

private theorem inf_top_q (x : EventQuotient S) : x ⊓ ⊤ = x := by
  induction x using Quotient.inductionOn with
  | _ x => exact Quot.sound (peq_inf_top x)

private theorem peq_bot_sup (x : S) : PEq (disj botRep x) x := by
  have hmeet : PEq (a (n botRep) (n x)) (n x) := by
    apply peq_trans (y := a (n x) (n botRep))
    · exact fun z => cp_comm (n botRep) (n x) z
    · apply peq_trans (y := a (n x) topRep)
      · exact peq_subst_conj₂ _ _ _ _ (peq_refl _) (fun _ => rfl)
      · exact peq_inf_top (n x)
  unfold disj
  exact peq_trans _ _ _ (peq_subst_neg _ _ hmeet)
    (fun z => cp_double_neg x z)

private theorem bot_sup_q (x : EventQuotient S) : ⊥ ⊔ x = x := by
  induction x using Quotient.inductionOn with
  | _ x => exact Quot.sound (peq_bot_sup x)

private theorem inf_compl_bot_q (x : EventQuotient S) : x ⊓ xᶜ = ⊥ := by
  induction x using Quotient.inductionOn with
  | _ x =>
      apply Quot.sound
      intro z
      calc
        cp (a x (n x)) z = cp (a (n x) x) z := cp_comm x (n x) z
        _ = cp (n z) z := cp_contra x z
        _ = cp botRep z := by
          unfold botRep
          exact (cp_contra (Classical.arbitrary S) z).symm

private theorem sup_compl_top_q (x : EventQuotient S) : x ⊔ xᶜ = ⊤ := by
  induction x using Quotient.inductionOn with
  | _ x =>
      apply Quot.sound
      intro z
      unfold disj topRep
      have hcomm := cp_comm (n x) (n (n x)) z
      have hneg := cp_neg_congr _ _ z hcomm
      rw [hneg, cp_neg_contra, cp_neg_contra]

/-- Popper's quotient is a Boolean algebra in Mathlib's structural sense. -/
noncomputable instance instBooleanAlgebra : BooleanAlgebra (EventQuotient S) where
  compl := (·ᶜ)
  sdiff := fun x y => x ⊓ yᶜ
  himp := fun x y => y ⊔ xᶜ
  inf_compl_le_bot x := (inf_compl_bot_q x).le
  top_le_sup_compl x := (sup_compl_top_q x).ge
  le_top x := inf_eq_left.mp (inf_top_q x)
  bot_le x := sup_eq_right.mp (bot_sup_q x)
  sdiff_eq _ _ := rfl
  himp_eq _ _ := rfl

/-- Popper's nontriviality axiom yields at least two quotient elements. -/
noncomputable instance instNontrivial : Nontrivial (EventQuotient S) where
  exists_pair_ne := by
    obtain ⟨x, y, hxy⟩ := nontrivial (S := S)
    refine ⟨Quotient.mk (peqSetoid S) x, Quotient.mk (peqSetoid S) y, ?_⟩
    intro h
    apply hxy
    exact Quotient.exact h

end EventQuotient

end PopperProbability
