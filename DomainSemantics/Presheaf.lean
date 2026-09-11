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

Master's `Valuation.Fits`, with the stage threaded through.  The shape is
master's and it matters: `Fits` is **indexed by a base context** and grows
the valuated part with `cons`, rather than recursing on all of `Γ` with a
condition per slot.  That is what makes `nil` a constructor, and hence
what makes the all-`⊥` valuation admissible for free — which is how both
master and the other repo run inversion.  Recursing on `Γ` instead loses
it, and with it every inversion theorem.

So `Adm Δ Γ₀ Γ σ ρ` reads: at the stage `(Δ, σ)`, `ρ` is an admissible
valuation for `Γ`, relative to the base `Γ₀` that `Γ` extends.  Slots
below the base get `⊥`.

Each `cons` asks what his `SourceAdmissible` asks of a slot: the type's own
interpretation is saturated (the `b'` premise, which is where the
downward closure `HasType` does not have is put in by hand), the slot has
a type among the type's approximants, and the slot is a fixed point of the
decoder of that type — here, `TShape.HasType`.  The `WF` premise is what
master gets for free from its shapes being a `WF` subtype. -/

inductive Adm (Δ : List Term) : List Term → List Term → Subst → Valuation → Prop where
  | nil {Γ σ} : Adm Δ Γ Γ σ Valuation.nil
  | cons {Γ₀ Γ A σ ρ x a} :
      Adm Δ Γ₀ Γ σ.tail ρ →
      (∀ b, Interp Δ Γ A σ.tail ρ b →
        ∃ b', TShape.LE Δ b b' ∧ Interp Δ Γ A σ.tail ρ b' ∧
          TShape.HasType Δ b' TShape.type) →
      Interp Δ Γ A σ.tail ρ a →
      TShape.WF Δ x →
      TShape.HasType Δ x a →
      Adm Δ Γ₀ (A :: Γ) σ (ρ.push x)

/-- The all-bottom valuation is admissible, for free.  This is the whole
reason for the base-context index, and the hypothesis every inversion
theorem is run under. -/
theorem Adm.bot {Δ Γ : List Term} {σ : Subst} : Adm Δ Γ Γ σ Valuation.nil := .nil

/-- Admissible valuations are well formed, slotwise. -/
theorem Adm.wf {Δ Γ₀ Γ : List Term} {σ ρ} (h : Adm Δ Γ₀ Γ σ ρ) : Valuation.WF Δ ρ := by
  induction h with
  | nil => intro i; exact trivial
  | cons _ _ _ hx _ ih => exact Valuation.WF.push ih hx

/-! ## The saturated form of typing

`InterpTyped` is where the downward closure lives.  `HasType` is not
monotone on the left, so "every approximant of `t` is typed at `A`" cannot
be said directly; what is true, and what the induction proves, is that
every approximant is *below* one that is typed.  This is master's
`InterpTyped` and the other repo's `rawExtend ⟦A⟧ ⟦t⟧ = ⟦t⟧`. -/

def InterpTyped (Δ Γ : List Term) (t A : Term) (σ : Subst)
    (ρ : Valuation) (m : TShape) : Prop :=
  ∃ m' a, TShape.LE Δ m m' ∧ Interp Δ Γ t σ ρ m' ∧ Interp Δ Γ A σ ρ a ∧
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
  ∀ {{Δ Γ₀ σ ρ}}, ⊢ Δ → Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ₀ Γ σ ρ →
    ∀ {m}, Interp Δ Γ t σ ρ m ↔ Interp Δ Γ t' σ ρ m

/-- Every approximant of `t` is below a typed one: master's `SoundTy`, his
`HasFixedness`. -/
def SoundTy (Γ : List Term) (t A : Term) : Prop :=
  ∀ {{Δ Γ₀ σ ρ}}, ⊢ Δ → Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ₀ Γ σ ρ →
    ∀ {m}, Interp Δ Γ t σ ρ m → InterpTyped Δ Γ t A σ ρ m

theorem SoundEq.refl {Γ : List Term} {t : Term} : SoundEq Γ t t :=
  fun _ _ _ _ _ _ _ => Iff.rfl

theorem SoundEq.symm {Γ : List Term} {t t' : Term} (h : SoundEq Γ t t') : SoundEq Γ t' t :=
  fun _ _ _ _ hΔ W hA => (h hΔ W hA).symm

theorem SoundEq.trans {Γ : List Term} {t t' t'' : Term}
    (h : SoundEq Γ t t') (h' : SoundEq Γ t' t'') : SoundEq Γ t t'' :=
  fun _ _ _ _ hΔ W hA => (h hΔ W hA).trans (h' hΔ W hA)

/-- Typing transports along a semantic equality, which is what lets the
soundness induction state `SoundTy` for the left-hand term only. -/
theorem SoundTy.of_eq {Γ : List Term} {t t' A : Term}
    (he : SoundEq Γ t t') (h : SoundTy Γ t A) : SoundTy Γ t' A := by
  intro Δ Γ₀ σ ρ hΔ W hA m hm
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
