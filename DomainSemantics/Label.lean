import DomainSemantics.Term

/-! # Label equality

Shapes in the gluing model carry syntactic labels (raw terms). Labels are
compared up to definitional equality in a context `Δ`; this file defines
the three label relations (term labels `(A, a)`, Π/Σ labels `(A, B)`,
Id labels `(A, a, b)`) and proves that they are partial equivalence
relations preserved by typed substitution.

These are *plain* definitional equality: there is no syntactic-equality
escape clause, so they are symmetric and transitive but **not reflexive**
on arbitrary terms. Reflexivity holds exactly on well-typed labels, which
is why the order on shapes is reflexive only on well-formed shapes
(`Shape.WF`), and why every reflexivity lemma downstream takes a context. -/

namespace DomainSemantics

/-- Equality of term labels: `a` and `a'` are the same argument, at the
same type. -/
def LabelEq (Δ : List Term) (A a A' a' : Term) : Prop :=
  (∃ u, Δ ⊢ A ≡ A' : .sort u) ∧ Δ ⊢ a ≡ a' : A

/-- Equality of type labels: the domain `A` a λ-shape is about. -/
def TyEq (Δ : List Term) (A A' : Term) : Prop := ∃ u, Δ ⊢ A ≡ A' : .sort u

/-- Equality of Π/Σ labels `(A, B)`. Componentwise, which is a priori finer
than `Δ ⊢ Π A B ≡ Π A' B'`; that the two agree is the inversion theorem. -/
def PiLabelEq (Δ : List Term) (A B A' B' : Term) : Prop :=
  (∃ u, Δ ⊢ A ≡ A' : .sort u) ∧ ∃ v, A :: Δ ⊢ B ≡ B' : .sort v

/-- Equality of Id labels `(A, a, b)`. -/
def IdLabelEq (Δ : List Term) (A a b A' a' b' : Term) : Prop :=
  (∃ u, Δ ⊢ A ≡ A' : .sort u) ∧ Δ ⊢ a ≡ a' : A ∧ Δ ⊢ b ≡ b' : A

namespace LabelEq

theorem refl (hA : Δ ⊢ A : .sort u) (ha : Δ ⊢ a : A) : LabelEq Δ A a A a := ⟨⟨u, hA⟩, ha⟩

theorem symm : LabelEq Δ A a A' a' → LabelEq Δ A' a' A a
  | ⟨⟨u, h1⟩, h2⟩ => ⟨⟨u, h1.symm⟩, h1.defeqDF h2.symm⟩

theorem trans : LabelEq Δ A a A' a' → LabelEq Δ A' a' A'' a'' → LabelEq Δ A a A'' a''
  | ⟨⟨u, h1⟩, h2⟩, ⟨⟨_, h3⟩, h4⟩ => ⟨⟨u, h1.trans' h3⟩, h2.trans (h1.symm.defeqDF h4)⟩

/-- Labels are stable under typed substitution. -/
theorem subst (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ) :
    LabelEq Δ A a A' a' → LabelEq Θ (A.subst τ) (a.subst τ) (A'.subst τ) (a'.subst τ)
  | ⟨⟨u, h1⟩, h2⟩ => ⟨⟨u, h1.subst hΘ W⟩, h2.subst hΘ W⟩

end LabelEq

namespace TyEq

theorem refl (hA : Δ ⊢ A : .sort u) : TyEq Δ A A := ⟨u, hA⟩

theorem symm : TyEq Δ A A' → TyEq Δ A' A
  | ⟨u, h⟩ => ⟨u, h.symm⟩

theorem trans : TyEq Δ A A' → TyEq Δ A' A'' → TyEq Δ A A''
  | ⟨u, h1⟩, ⟨_, h2⟩ => ⟨u, h1.trans' h2⟩

theorem refl_l : TyEq Δ A A' → TyEq Δ A A
  | ⟨u, h⟩ => ⟨u, h.hasType.1⟩

theorem refl_r : TyEq Δ A A' → TyEq Δ A' A'
  | ⟨u, h⟩ => ⟨u, h.hasType.2⟩

theorem subst (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ) :
    TyEq Δ A A' → TyEq Θ (A.subst τ) (A'.subst τ)
  | ⟨u, h⟩ => ⟨u, h.subst hΘ W⟩

/-- The type label of an entry agrees with the type of its argument. -/
theorem of_labelEq : LabelEq Δ A a A' a' → TyEq Δ A A' := (·.1)

end TyEq

namespace PiLabelEq

theorem refl (hA : Δ ⊢ A : .sort u) (hB : A :: Δ ⊢ B : .sort v) : PiLabelEq Δ A B A B :=
  ⟨⟨u, hA⟩, v, hB⟩

theorem symm (hΔ : ⊢ Δ) : PiLabelEq Δ A B A' B' → PiLabelEq Δ A' B' A B
  | ⟨⟨u, h1⟩, v, h2⟩ => ⟨⟨u, h1.symm⟩, v, (h1.defeqDF_l hΔ h2).symm⟩

theorem trans (hΔ : ⊢ Δ) :
    PiLabelEq Δ A B A' B' → PiLabelEq Δ A' B' A'' B'' → PiLabelEq Δ A B A'' B''
  | ⟨⟨u, h1⟩, v, h2⟩, ⟨⟨_, h3⟩, _, h4⟩ =>
    ⟨⟨u, h1.trans' h3⟩, v, h2.trans' (h1.symm.defeqDF_l hΔ h4)⟩

theorem subst (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ) :
    PiLabelEq Δ A B A' B' → PiLabelEq Θ (A.subst τ) (B.subst τ.lift) (A'.subst τ) (B'.subst τ.lift)
  | ⟨⟨u, h1⟩, v, h2⟩ =>
    have hA := h1.hasType.1.subst hΘ W
    have hΘA : ⊢ A.subst τ :: Θ := ⟨hΘ, _, hA⟩
    ⟨⟨u, h1.subst hΘ W⟩, v, h2.subst hΘA (W.lift h1.hasType.1 hA)⟩

end PiLabelEq

namespace IdLabelEq

theorem refl (hA : Δ ⊢ A : .sort u) (ha : Δ ⊢ a : A) (hb : Δ ⊢ b : A) :
    IdLabelEq Δ A a b A a b := ⟨⟨u, hA⟩, ha, hb⟩

theorem symm : IdLabelEq Δ A a b A' a' b' → IdLabelEq Δ A' a' b' A a b
  | ⟨⟨u, h1⟩, h2, h3⟩ => ⟨⟨u, h1.symm⟩, h1.defeqDF h2.symm, h1.defeqDF h3.symm⟩

theorem trans : IdLabelEq Δ A a b A' a' b' → IdLabelEq Δ A' a' b' A'' a'' b'' →
    IdLabelEq Δ A a b A'' a'' b''
  | ⟨⟨u, h1⟩, h2, h3⟩, ⟨⟨_, h4⟩, h5, h6⟩ =>
    ⟨⟨u, h1.trans' h4⟩, h2.trans (h1.symm.defeqDF h5), h3.trans (h1.symm.defeqDF h6)⟩

theorem subst (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ) :
    IdLabelEq Δ A a b A' a' b' →
    IdLabelEq Θ (A.subst τ) (a.subst τ) (b.subst τ) (A'.subst τ) (a'.subst τ) (b'.subst τ)
  | ⟨⟨u, h1⟩, h2, h3⟩ => ⟨⟨u, h1.subst hΘ W⟩, h2.subst hΘ W, h3.subst hΘ W⟩

end IdLabelEq
