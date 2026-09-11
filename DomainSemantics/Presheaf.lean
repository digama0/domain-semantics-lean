import DomainSemantics.Interp

/-! # The soundness invariant

This is the thing soundness is about: the other repo's `RawJudgment`, the
bundle of properties that one induction on `IsDefEq` establishes, written
out over the notions this branch actually has.

The shape of the argument is his, not master's.  Master proves soundness
and then a *separate* logical relation (`LogRel.lean`) and *adequacy*
(`Adequacy.lean`), 4.9k lines, to get inversion out.  Here inversion comes
from the syntactic labels the shapes carry, so soundness is the whole
proof and `RawJudgment` is its statement:

    IsDefEq.rawSoundness : ⊢ Γ → Γ ⊢ t ≡ t' : A → RawJudgment Γ t t' A

Everything below is a definition.  The induction that proves the theorem
is item 5 of `presheaf-plan.md`.

## Correspondence with the other repo

| his | here |
|---|---|
| `SourceAdmissible σ ρ` | `Adm` |
| a stage `σ : Γ₁ ⟶ Γ` | `Stage`, which also carries `⊢ Δ` and the typing of `σ` |
| `HasIdeality Γ t` | `HasIdeality` — directedness of the approximant set |
| `HasEquality Γ t t'` | `HasEquality` — the two approximant sets coincide |
| `HasFixedness Γ t A` | `HasFixedness` — every approximant is typed, via `InterpTyped` |
| `HasRenaming` + `HasSubstitution` | `HasSubstitution`, in master's `∃ ρ'` form |
| reindexing along `σ` (functoriality, free) | `HasNaturality` — a *theorem* here, since our stage is raw syntax |
| `PiReady Γ A B` | absent: it collapses into `HasIdeality` (§4.4) |
| `regular` + `type`/`left`/`right` + `equal` + `fixed` | the fields of `RawJudgment` |

Two of his notions have no counterpart because they are artefacts of the
ideal-theoretic setting rather than content: `RawValue = ΩLower` (a value
is a single shape here, and the lower set is `Interp`'s own downward
closure) and the `rank`/`piStage`/`piLimit` fixed point (the level index
does that work). -/

namespace DomainSemantics

/-! ## Valuations along a stage -/

/-- Drop the head, for going under a binder in the context. -/
def Valuation.tail (ρ : Valuation) : Valuation := fun i => ρ (i+1)

/-- Reindex a valuation along a substitution of the stage. -/
def Valuation.subst (ρ : Valuation) (τ : Subst) : Valuation := fun i => (ρ i).subst τ

@[simp] theorem Valuation.tail_push {ρ : Valuation} {u} : (ρ.push u).tail = ρ := rfl

/-! ## Admissibility

Master's `Valuation.Fits`, by recursion on the context rather than as an
inductive, and with the stage threaded through.  His `SourceAdmissible`
asks the same three things of each slot: the slot is a genuine value, it
is a fixed point of the decoder of its type, and the type's own
interpretation is saturated.  Here "fixed point of the decoder" is
`TShape.HasType`, and "saturated" is the `∃ b'` clause — master's, and the
place where the downward closure that `HasType` does not have is put in by
hand. -/

def Adm (Δ : List Term) : List Term → Subst → Valuation → Prop
  | [], _, ρ => ρ = Valuation.nil
  | A :: Γ, σ, ρ =>
      Adm Δ Γ σ.tail ρ.tail ∧
      TShape.WF Δ (ρ 0) ∧
      (∃ a, Interp Γ A Δ σ.tail ρ.tail a ∧ TShape.HasType Δ (ρ 0) a) ∧
      ∀ b, Interp Γ A Δ σ.tail ρ.tail b →
        ∃ b', TShape.LE Δ b b' ∧ Interp Γ A Δ σ.tail ρ.tail b' ∧
          TShape.HasType Δ b' TShape.type

/-- Everything a property of a raw term is quantified over: a context `Δ`
to live in, a typed substitution `σ` from `Γ` into it, and an admissible
valuation.  His stage is just the substitution, because his contexts are
already well-formed by construction and his substitutions are morphisms;
ours has to carry both facts explicitly, which is the "no quotient,
preservation lemmas instead" policy applied to the presheaf structure. -/
structure Stage (Γ Δ : List Term) (σ : Subst) (ρ : Valuation) : Prop where
  ctx : ⊢ Δ
  subst : Ctx.SubstEq Δ σ σ Γ
  adm : Adm Δ Γ σ ρ

/-! ## The saturated form of typing

`InterpTyped` is where the downward closure lives.  `HasType` is not
monotone on the left, so "every approximant of `t` is typed at `A`" cannot
be said directly; what is true, and what the induction proves, is that
every approximant is *below* one that is typed. -/

def InterpTyped (Γ : List Term) (t A : Term) (Δ : List Term) (σ : Subst)
    (ρ : Valuation) (m : TShape) : Prop :=
  ∃ m' a, TShape.LE Δ m m' ∧ Interp Γ t Δ σ ρ m' ∧ Interp Γ A Δ σ ρ a ∧
    TShape.HasType Δ m' a

/-! ## The properties of a raw term -/

/-- The approximant set is directed: his `HasIdeality`.  Together with
`Interp.mono` this says `⟦t⟧` is an ideal, which is what makes it a value
in his sense without ever building `ΩLower`. -/
def HasIdeality (Γ : List Term) (t : Term) : Prop :=
  ∀ {Δ σ ρ}, Stage Γ Δ σ ρ → ∀ {m m'},
    Interp Γ t Δ σ ρ m → Interp Γ t Δ σ ρ m' →
    ∃ m'', Interp Γ t Δ σ ρ m'' ∧ TShape.LE Δ m m'' ∧ TShape.LE Δ m' m''

/-- The two terms have the same approximants: his `HasEquality`, and the
semantic content of a definitional equality. -/
def HasEquality (Γ : List Term) (t t' : Term) : Prop :=
  ∀ {Δ σ ρ}, Stage Γ Δ σ ρ → ∀ {m}, Interp Γ t Δ σ ρ m ↔ Interp Γ t' Δ σ ρ m

/-- Every approximant of `t` is below a typed one: his `HasFixedness`,
master's `SoundTy`. -/
def HasFixedness (Γ : List Term) (t A : Term) : Prop :=
  ∀ {Δ σ ρ}, Stage Γ Δ σ ρ → ∀ {m},
    Interp Γ t Δ σ ρ m → InterpTyped Γ t A Δ σ ρ m

/-- Naturality in the stage: the interpretation commutes with reindexing
along a typed substitution of the *stage*.  For him this is functoriality
of a presheaf and costs nothing; here the stage is raw syntax, so it is a
property to be proved, and it is the reason every shape-level notion had
to be shown stable under `Shape.subst`. -/
def HasNaturality (Γ : List Term) (t : Term) : Prop :=
  ∀ {Δ σ ρ}, Stage Γ Δ σ ρ → ∀ {Θ τ}, ⊢ Θ → Ctx.SubstEq Θ τ τ Δ → ∀ {m},
    Interp Γ t Δ σ ρ m → Interp Γ t Θ (σ.comp τ) (ρ.subst τ) (m.subst τ)

/-- Substitution in the *term*, in master's `∃ ρ'` form: an approximant of
`t[θ]` is an approximant of `t` under some valuation whose slots
approximate the `θ i`.  The stage moves from `σ` to `θ.comp σ`, which is
the only place the two kinds of substitution meet. -/
def HasSubstitution (Γ : List Term) (t : Term) : Prop :=
  ∀ {Γ' θ Δ σ ρ}, Stage Γ' Δ σ ρ → Ctx.SubstEq Γ' θ θ Γ → ∀ {m},
    (Interp Γ' (t.subst θ) Δ σ ρ m ↔
      ∃ ρ', Interp Γ t Δ (θ.comp σ) ρ' m ∧ ∀ i, Interp Γ' (θ i) Δ σ ρ (ρ' i))

/-- His `RawTermProperties`: the properties that belong to a term on its
own, independently of any type or partner. -/
structure TermProperties (Γ : List Term) (t : Term) : Prop where
  ideality : HasIdeality Γ t
  naturality : HasNaturality Γ t
  substitution : HasSubstitution Γ t

/-! ## The invariant -/

/-- The soundness invariant, his `RawJudgment`.  One induction on
`IsDefEq` establishes all six fields at once; they are mutually needed,
which is why they travel together rather than as separate theorems.

`regular` says the type is itself a type, `type`/`left`/`right` are the
term-level properties of the three terms involved, `equal` is the
definitional equality made semantic, and `fixed` is the typing. -/
structure RawJudgment (Γ : List Term) (t t' A : Term) : Prop where
  regular : ∃ r, HasFixedness Γ A (.sort r)
  type : TermProperties Γ A
  left : TermProperties Γ t
  right : TermProperties Γ t'
  equal : HasEquality Γ t t'
  fixed : HasFixedness Γ t A

/-- Master's names for the two fields that get used downstream. -/
abbrev SoundEq (Γ : List Term) (t t' : Term) : Prop := HasEquality Γ t t'
abbrev SoundTy (Γ : List Term) (t A : Term) : Prop := HasFixedness Γ t A

/-- The right-hand term is typed too, by transporting along `equal`. -/
theorem RawJudgment.fixed_right {Γ : List Term} {t t' A : Term}
    (J : RawJudgment Γ t t' A) : HasFixedness Γ t' A := by
  intro Δ σ ρ hS m hm
  have ⟨m', a, hle, hm', ha, hty⟩ := J.fixed hS (J.equal hS |>.2 hm)
  exact ⟨m', a, hle, (J.equal hS).1 hm', ha, hty⟩

theorem RawJudgment.symm {Γ : List Term} {t t' A : Term}
    (J : RawJudgment Γ t t' A) : RawJudgment Γ t' t A where
  regular := J.regular
  type := J.type
  left := J.right
  right := J.left
  equal := fun hS => (J.equal hS).symm
  fixed := J.fixed_right

/-- Transitivity ignores the middle type, exactly as his
`RawJudgment.trans` does: the two judgments may assign `t'` different but
definitionally equal types, and nothing in the bundle depends on which. -/
theorem RawJudgment.trans {Γ : List Term} {t t' t'' A A' : Term}
    (J : RawJudgment Γ t t' A) (J' : RawJudgment Γ t' t'' A') :
    RawJudgment Γ t t'' A where
  regular := J.regular
  type := J.type
  left := J.left
  right := J'.right
  equal := fun hS => (J.equal hS).trans (J'.equal hS)
  fixed := J.fixed

/-! ## The target

The one theorem this branch is for.  Master needs `LogRel.lean` and
`Adequacy.lean` on top of its soundness theorem to get inversion; here the
labels carry the syntax through the model, so the inversion principles of
§6 are corollaries of this statement alone. -/

theorem IsDefEq.rawSoundness {Γ : List Term} {t t' A : Term}
    (hΓ : ⊢ Γ) (H : Γ ⊢ t ≡ t' : A) : RawJudgment Γ t t' A := by
  sorry
