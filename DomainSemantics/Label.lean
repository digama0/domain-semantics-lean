import DomainSemantics.Term

/-! # Label equality

Shapes in the gluing model carry syntactic labels (raw terms). Labels are
compared up to definitional equality in a context `Δ`; this file defines
the three label relations (term labels `(A, a)`, Π/Σ labels `(A, B)`,
Id labels `(A, a, b)`) and proves that they are equivalence relations
preserved by typed substitution. The syntactic-equality disjunct keeps
them reflexive on ill-typed labels, so the order on shapes stays a
preorder on all shapes. -/

namespace DomainSemantics

/-! ## Label equality

Labels are compared up to definitional equality in a context `Δ`. The
syntactic-equality disjunct makes the relation reflexive on ill-typed
labels too, so that `LE Δ` is a preorder on *all* shapes; on well-typed
labels it is subsumed by the defeq disjunct. -/

/-- Equality of term labels `(A, a)` (a term `a` of type `A`) in `Δ`. -/
def LabelEq (Δ : List Term) (A a A' a' : Term) : Prop :=
  (A = A' ∧ a = a') ∨ ((∃ u, Δ ⊢ A ≡ A' : .sort u) ∧ Δ ⊢ a ≡ a' : A)

/-- Equality of Π-labels `(A, B)` in `Δ`. -/
def PiLabelEq (Δ : List Term) (A B A' B' : Term) : Prop :=
  (A = A' ∧ B = B') ∨ ((∃ u, Δ ⊢ A ≡ A' : .sort u) ∧ ∃ v, A :: Δ ⊢ B ≡ B' : .sort v)

/-- Equality of Id-labels `(A, a, b)` in `Δ`. -/
def IdLabelEq (Δ : List Term) (A a b A' a' b' : Term) : Prop :=
  (A = A' ∧ a = a' ∧ b = b') ∨
    ((∃ u, Δ ⊢ A ≡ A' : .sort u) ∧ Δ ⊢ a ≡ a' : A ∧ Δ ⊢ b ≡ b' : A)

namespace LabelEq

theorem refl : LabelEq Δ A a A a := .inl ⟨rfl, rfl⟩

theorem symm : LabelEq Δ A a A' a' → LabelEq Δ A' a' A a
  | .inl ⟨h1, h2⟩ => .inl ⟨h1.symm, h2.symm⟩
  | .inr ⟨⟨u, h1⟩, h2⟩ => .inr ⟨⟨u, h1.symm⟩, h1.defeqDF h2.symm⟩

theorem trans : LabelEq Δ A a A' a' → LabelEq Δ A' a' A'' a'' → LabelEq Δ A a A'' a''
  | .inl ⟨rfl, rfl⟩, h => h
  | h, .inl ⟨rfl, rfl⟩ => h
  | .inr ⟨⟨u, h1⟩, h2⟩, .inr ⟨⟨_, h3⟩, h4⟩ =>
    .inr ⟨⟨u, h1.trans' h3⟩, h2.trans (h1.symm.defeqDF h4)⟩

/-- Labels are stable under typed substitution. -/
theorem subst (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ) :
    LabelEq Δ A a A' a' → LabelEq Θ (A.subst τ) (a.subst τ) (A'.subst τ) (a'.subst τ)
  | .inl ⟨rfl, rfl⟩ => .inl ⟨rfl, rfl⟩
  | .inr ⟨⟨u, h1⟩, h2⟩ => .inr ⟨⟨u, h1.subst hΘ W⟩, h2.subst hΘ W⟩

end LabelEq

namespace PiLabelEq

theorem refl : PiLabelEq Δ A B A B := .inl ⟨rfl, rfl⟩

theorem symm (hΔ : ⊢ Δ) : PiLabelEq Δ A B A' B' → PiLabelEq Δ A' B' A B
  | .inl ⟨h1, h2⟩ => .inl ⟨h1.symm, h2.symm⟩
  | .inr ⟨⟨u, h1⟩, v, h2⟩ => .inr ⟨⟨u, h1.symm⟩, v, (h1.defeqDF_l hΔ h2).symm⟩

theorem trans (hΔ : ⊢ Δ) :
    PiLabelEq Δ A B A' B' → PiLabelEq Δ A' B' A'' B'' → PiLabelEq Δ A B A'' B''
  | .inl ⟨rfl, rfl⟩, h => h
  | h, .inl ⟨rfl, rfl⟩ => h
  | .inr ⟨⟨u, h1⟩, v, h2⟩, .inr ⟨⟨_, h3⟩, _, h4⟩ =>
    .inr ⟨⟨u, h1.trans' h3⟩, v, h2.trans' (h1.symm.defeqDF_l hΔ h4)⟩

theorem subst (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ) :
    PiLabelEq Δ A B A' B' → PiLabelEq Θ (A.subst τ) (B.subst τ.lift) (A'.subst τ) (B'.subst τ.lift)
  | .inl ⟨rfl, rfl⟩ => .inl ⟨rfl, rfl⟩
  | .inr ⟨⟨u, h1⟩, v, h2⟩ =>
    have hA := h1.hasType.1.subst hΘ W
    have hΘA : ⊢ A.subst τ :: Θ := ⟨hΘ, _, hA⟩
    .inr ⟨⟨u, h1.subst hΘ W⟩, v, h2.subst hΘA (W.lift h1.hasType.1 hA)⟩

end PiLabelEq

namespace IdLabelEq

theorem refl : IdLabelEq Δ A a b A a b := .inl ⟨rfl, rfl, rfl⟩

theorem symm : IdLabelEq Δ A a b A' a' b' → IdLabelEq Δ A' a' b' A a b
  | .inl ⟨h1, h2, h3⟩ => .inl ⟨h1.symm, h2.symm, h3.symm⟩
  | .inr ⟨⟨u, h1⟩, h2, h3⟩ => .inr ⟨⟨u, h1.symm⟩, h1.defeqDF h2.symm, h1.defeqDF h3.symm⟩

theorem trans : IdLabelEq Δ A a b A' a' b' → IdLabelEq Δ A' a' b' A'' a'' b'' →
    IdLabelEq Δ A a b A'' a'' b''
  | .inl ⟨rfl, rfl, rfl⟩, h => h
  | h, .inl ⟨rfl, rfl, rfl⟩ => h
  | .inr ⟨⟨u, h1⟩, h2, h3⟩, .inr ⟨⟨_, h4⟩, h5, h6⟩ =>
    .inr ⟨⟨u, h1.trans' h4⟩, h2.trans (h1.symm.defeqDF h5), h3.trans (h1.symm.defeqDF h6)⟩

theorem subst (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ) :
    IdLabelEq Δ A a b A' a' b' →
    IdLabelEq Θ (A.subst τ) (a.subst τ) (b.subst τ) (A'.subst τ) (a'.subst τ) (b'.subst τ)
  | .inl ⟨rfl, rfl, rfl⟩ => .inl ⟨rfl, rfl, rfl⟩
  | .inr ⟨⟨u, h1⟩, h2, h3⟩ => .inr ⟨⟨u, h1.subst hΘ W⟩, h2.subst hΘ W, h3.subst hΘ W⟩

end IdLabelEq

end DomainSemantics
