import DomainSemantics.Interp

/-! # Admissibility and the soundness statement

`Interp` is the core definition; everything else about it is a lemma.
This file adds the two things that are genuinely *new data* rather than
properties of `Interp` — admissibility of a valuation, and the saturated
form of typing — and then states what soundness says.

The other repo bundles its properties into `RawTermProperties` and
`RawJudgment`, because they are established simultaneously by one
induction over a structure that also carries category-theoretic data.  We
do not need the bundle: directedness, naturality and the substitution
lemma are unconditional facts about `Interp`, so they are lemmas in
`Interp.lean`, and only the two judgment-indexed properties — `SoundEq`
and `SoundTy` — are stated here.

| his | here |
|---|---|
| `SourceAdmissible σ ρ` | `Adm` |
| `HasIdeality Γ t` | a lemma: `Interp` is directed |
| `HasRenaming` + `HasSubstitution` | a lemma: `Interp.subst` |
| reindexing along `σ` (functoriality, free) | a lemma: `Interp.natural` |
| `HasEquality Γ t t'` | `SoundEq` |
| `HasFixedness Γ t A` | `SoundTy`, via `InterpTyped` |
| `PiReady Γ A B` | absent; it collapses into directedness |
| `RawJudgment` (6 fields) | `SoundEq` and `SoundTy`, proved together |

Two of his notions have no counterpart because they are artefacts of the
ideal-theoretic setting rather than content: `RawValue = ΩLower` (a value
is a single shape here, and the lower set is `Interp`'s own downward
closure) and the `rank`/`piStage`/`piLimit` fixed point (the level index
does that work). -/

namespace DomainSemantics

/-! ## Admissibility

Master's `Valuation.Fits`, by recursion on the context rather than as an
inductive, and with the stage threaded through.  His `SourceAdmissible`
asks the same of each slot: the slot is a genuine value, it is a fixed
point of the decoder of its type, and the type's own interpretation is
saturated.  Here "fixed point of the decoder" is `TShape.HasType`, and
"saturated" is the `∃ b'` clause — master's, and the place where the
downward closure that `HasType` does not have is put in by hand. -/

def Adm (Δ : List Term) : List Term → Subst → Valuation → Prop
  | [], _, ρ => ρ = Valuation.nil
  | A :: Γ, σ, ρ =>
      Adm Δ Γ σ.tail ρ.tail ∧
      TShape.WF Δ (ρ 0) ∧
      (∃ a, Interp Γ A Δ σ.tail ρ.tail a ∧ TShape.HasType Δ (ρ 0) a) ∧
      ∀ b, Interp Γ A Δ σ.tail ρ.tail b →
        ∃ b', TShape.LE Δ b b' ∧ Interp Γ A Δ σ.tail ρ.tail b' ∧
          TShape.HasType Δ b' TShape.type

/-! ## The saturated form of typing

`InterpTyped` is where the downward closure lives.  `HasType` is not
monotone on the left, so "every approximant of `t` is typed at `A`" cannot
be said directly; what is true, and what the induction proves, is that
every approximant is *below* one that is typed.  This is master's
`InterpTyped` and the other repo's `rawExtend ⟦A⟧ ⟦t⟧ = ⟦t⟧`. -/

def InterpTyped (Γ : List Term) (t A : Term) (Δ : List Term) (σ : Subst)
    (ρ : Valuation) (m : TShape) : Prop :=
  ∃ m' a, TShape.LE Δ m m' ∧ Interp Γ t Δ σ ρ m' ∧ Interp Γ A Δ σ ρ a ∧
    TShape.HasType Δ m' a

/-! ## What soundness says

Each is quantified over a **stage**: a context to live in, a typed
substitution into it, and an admissible valuation.  His stage is only the
substitution, because his contexts are well formed by construction and his
substitutions are morphisms; ours has to carry both facts explicitly,
which is the "no quotient, preservation lemmas instead" policy applied to
the presheaf structure. -/

/-- The two terms have the same approximants at every stage: master's
`SoundEq`, his `HasEquality`, and the semantic content of a definitional
equality. -/
def SoundEq (Γ : List Term) (t t' : Term) : Prop :=
  ∀ {{Δ σ ρ}}, ⊢ Δ → Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ σ ρ →
    ∀ {m}, Interp Γ t Δ σ ρ m ↔ Interp Γ t' Δ σ ρ m

/-- Every approximant of `t` is below a typed one: master's `SoundTy`, his
`HasFixedness`. -/
def SoundTy (Γ : List Term) (t A : Term) : Prop :=
  ∀ {{Δ σ ρ}}, ⊢ Δ → Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ σ ρ →
    ∀ {m}, Interp Γ t Δ σ ρ m → InterpTyped Γ t A Δ σ ρ m

theorem SoundEq.refl {Γ : List Term} {t : Term} : SoundEq Γ t t :=
  fun _ _ _ _ _ _ => Iff.rfl

theorem SoundEq.symm {Γ : List Term} {t t' : Term} (h : SoundEq Γ t t') : SoundEq Γ t' t :=
  fun _ _ _ hΔ W hA => (h hΔ W hA).symm

theorem SoundEq.trans {Γ : List Term} {t t' t'' : Term}
    (h : SoundEq Γ t t') (h' : SoundEq Γ t' t'') : SoundEq Γ t t'' :=
  fun _ _ _ hΔ W hA => (h hΔ W hA).trans (h' hΔ W hA)

/-- Typing transports along a semantic equality, which is what lets the
soundness induction state `SoundTy` for the left-hand term only. -/
theorem SoundTy.of_eq {Γ : List Term} {t t' A : Term}
    (he : SoundEq Γ t t') (h : SoundTy Γ t A) : SoundTy Γ t' A := by
  intro Δ σ ρ hΔ W hA m hm
  have ⟨m', a, hle, hm', ha, hty⟩ := h hΔ W hA ((he hΔ W hA).2 hm)
  exact ⟨m', a, hle, (he hΔ W hA).1 hm', ha, hty⟩

/-! ## The target

The one theorem this branch is for.  Master needs `LogRel.lean` and
`Adequacy.lean` on top of its soundness theorem to get inversion; here the
labels carry the syntax through the model, so the inversion principles of
§6 are corollaries of this statement alone. -/

theorem IsDefEq.sound {Γ : List Term} {t t' A : Term}
    (hΓ : ⊢ Γ) (H : Γ ⊢ t ≡ t' : A) : SoundEq Γ t t' ∧ SoundTy Γ t A := by
  sorry
