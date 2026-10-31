import DomainSemantics.DefEq

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
(`Shape.WF`), and why every reflexivity lemma downstream takes a context.

Last comes `Stable`, what an `app` or `snd` clause carries in place of
"the argument has type `A₀` in `Γ`, and the label is `A₀` at the stage".
It is the weaker of the two, and the one that survives a move to a
smaller context. -/

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
  TyEq Δ A A' ∧ TyEq (A :: Δ) B B'

/-- Equality of Id labels `(A, a, b)`. -/
def IdLabelEq (Δ : List Term) (A a b A' a' b' : Term) : Prop :=
  TyEq Δ A A' ∧ Δ ⊢ a ≡ a' : A ∧ Δ ⊢ b ≡ b' : A

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

theorem right : LabelEq Δ A a A' a' → LabelEq Δ A' a A' a'
  | ⟨⟨u, h1⟩, h2⟩ => ⟨⟨u, h1.hasType.2⟩, h1.defeqDF h2⟩

/-- Move a same-type label equality along an equality of types. -/
theorem retype (hT : TyEq Δ A A') : LabelEq Δ A a A b → LabelEq Δ A' a A' b
  | ⟨_, h2⟩ => let ⟨u, h⟩ := hT; ⟨⟨u, h.hasType.2⟩, h.defeqDF h2⟩

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

/-- **Retyping along the equation.**  The conclusion does not mention the
sort level, so the witness is destructured rather than chosen — which is
what keeps this choice-free, unlike `h.defeqDF`. -/
theorem defeqDF : TyEq Δ A A' → (Δ ⊢ a ≡ b : A) → Δ ⊢ a ≡ b : A'
  | ⟨_, h⟩ => h.defeqDF

end TyEq

namespace PiLabelEq

/-- The label equality packaged as one equation of Π types.  Choice-free:
both witnesses are destructured and the result re-hides its own level. -/
theorem forallE (hΔ : ⊢ Δ) :
    PiLabelEq Δ A B A' B' → TyEq Δ (.forallE A B) (.forallE A' B')
  | ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ => ⟨_, h1.forallEDF₀ hΔ h2⟩

/-- The same for Σ. -/
theorem sigma (hΔ : ⊢ Δ) :
    PiLabelEq Δ A B A' B' → TyEq Δ (.sigma A B) (.sigma A' B')
  | ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ => ⟨_, h1.sigmaDF₀ hΔ h2⟩

end PiLabelEq

namespace IdLabelEq

/-- And for the identity type. -/
protected theorem id {r : Bool} :
    IdLabelEq Δ A a b A' a' b' → TyEq Δ (.id r A a b) (.id r A' a' b')
  | ⟨⟨_, h1⟩, h2, h3⟩ => ⟨_, .idDF h1 h2 h3⟩

end IdLabelEq

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

/-- **A query term is stable at a label.**  Reading the term at the stage
and at any later stage out of `Γ` gives two terms equal *at the label*, and
this stays true under any substitution of the ambient context.

This is what an `app` or `snd` clause carries in place of "the argument has
type `A₀` in `Γ`, and the label is `A₀` at the stage".  The two are
interderivable where the argument's typing is at hand (`Stable.of_typed`),
but only this one survives a move to a *smaller* context: strengthening a
typing out of `Γ'` is not available in this syntax, while the stages a
smaller context admits extend to ones the larger context admits
(`Ctx.SubstEq.extend`).  The quantification over later ambient
substitutions is the same device `Shape.Compat` uses, and for the same
reason: a property of a stage has to be stable under the stage moving. -/
def Stable (Δ Γ : List Term) (σ : Subst) (a A : Term) : Prop :=
  ∀ ⦃Θ τ σ₂⦄, ⊢ Θ → Ctx.SubstEq Θ τ τ Δ → Ctx.SubstEq Θ (σ.comp τ) σ₂ Γ →
    Θ ⊢ a.subst (σ.comp τ) ≡ a.subst σ₂ : A.subst τ

namespace Stable

/-- The usual way to get one: the term is typed in `Γ`, and the label is
that type at the stage. -/
theorem of_typed (ha : Γ ⊢ a : A₀) (hTy : TyEq Δ A (A₀.subst σ)) :
    Stable Δ Γ σ a A := by
  intro Θ τ σ₂ hΘ V W
  have hT : TyEq Θ (A.subst τ) (A₀.subst (σ.comp τ)) := by
    have := hTy.subst hΘ V; rwa [subst_subst] at this
  exact hT.symm.defeqDF (ha.subst' hΘ W)

/-- What the clauses use it for: the query term moves with the stage. -/
theorem move (hΔ : ⊢ Δ) (H : Stable Δ Γ σ a A) (W : Ctx.SubstEq Δ σ σ₂ Γ) :
    Δ ⊢ a.subst σ ≡ a.subst σ₂ : A := by
  have h := H hΔ (.id hΔ) (σ₂ := σ₂) (by rwa [Subst.comp_id])
  rwa [Subst.comp_id, subst_id] at h

/-- The label moves by a `TyEq`. -/
theorem retype (hTy : TyEq Δ A A') (H : Stable Δ Γ σ a A) : Stable Δ Γ σ a A' :=
  fun _ _ _ hΘ V W => (hTy.subst hΘ V).defeqDF (H hΘ V W)

/-- Along a substitution of the ambient context — immediate, since that is
what the definition quantifies over. -/
theorem subst (V : Ctx.SubstEq Θ τ₀ τ₀ Δ) (H : Stable Δ Γ σ a A) :
    Stable Θ Γ (σ.comp τ₀) a (A.subst τ₀) := by
  intro Ξ τ σ₂ hΞ V' W
  rw [Subst.comp_assoc] at W
  have h := H hΞ (V'.comp' hΞ V) W
  rw [Subst.comp_assoc, subst_subst]
  exact h

/-- To a definitionally equal context. -/
theorem ctx (W₀ : Ctx.SubstEq Γ' .id .id Γ) (H : Stable Δ Γ σ a A) :
    Stable Δ Γ' σ a A := by
  intro Θ τ σ₂ hΘ V W
  have hW := W.comp' hΘ W₀
  rw [Subst.id_comp, Subst.id_comp] at hW
  exact H hΘ V hW

/-- At a later stage. -/
theorem stage (W₀ : Ctx.SubstEq Δ σ σ₂ Γ) (H : Stable Δ Γ σ a A) :
    Stable Δ Γ σ₂ a A := by
  intro Θ τ σ₃ hΘ V W
  have hmid : Ctx.SubstEq Θ (σ.comp τ) (σ₂.comp τ) Γ := V.comp' hΘ W₀
  exact (H hΘ V hmid).symm.trans (H hΘ V (hmid.trans hΘ W))

/-- Into a larger context, the term lifted along it. -/
theorem weak' (hΓ : ⊢ Γ) (WΓ : Ctx.Lift' l Γ Γ')
    (H : Stable Δ Γ (σ'.lift_l l) a A) : Stable Δ Γ' σ' (a.lift' l) A := by
  intro Θ τ σ₂ hΘ V W
  have hW := W.lift_l WΓ hΓ
  rw [Subst.lift_l_comp] at hW
  simp only [subst_lift', Subst.lift_l_comp]
  exact H hΘ V hW

/-- And back down, which is the point: the label is a statement about the
ambient context, and the stages the smaller context admits are the larger
one's, restricted. -/
theorem unweak (WΓ : Ctx.Lift' l Γ Γ') (hd : Ctx.SubstEq Δ σ' σ' Γ')
    (H : Stable Δ Γ' σ' (a.lift' l) A) : Stable Δ Γ (σ'.lift_l l) a A := by
  intro Θ τ σ₂ hΘ V W
  rw [← Subst.lift_l_comp] at W
  obtain ⟨σ₂', W', rfl⟩ := (V.comp hΘ hd).extend WΓ W
  have h := H hΘ V W'
  rw [subst_lift', subst_lift'] at h
  rw [← Subst.lift_l_comp]
  exact h

/-- Under a substitution of the term's own context. -/
theorem substTerm (Wθ : Ctx.SubstEq Γ' θ θ Γ) (H : Stable Δ Γ (θ.comp σ) a A) :
    Stable Δ Γ' σ (a.subst θ) A := by
  intro Θ τ σ₂ hΘ V W
  have hW : Ctx.SubstEq Θ ((θ.comp σ).comp τ) (θ.comp σ₂) Γ := by
    rw [Subst.comp_assoc]; exact W.comp' hΘ Wθ
  have h := H hΘ V hW
  rw [Subst.comp_assoc] at h
  simp only [subst_subst]
  exact h

end Stable
