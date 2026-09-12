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
| `HasIdeality Γ t` | `SoundDir`, proved *with* soundness (§4.5) |
| `HasRenaming` + `HasSubstitution` | a lemma: `Interp.subst` |
| reindexing along `σ` (functoriality, free) | a lemma: `Interp.subst` |
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

/-- Directedness of the approximant set: his `HasIdeality`, and the third
conclusion of the soundness induction.

This is not a lemma about `Interp` on its own, and that is forced rather
than a choice.  Joining two λ-shapes means appending their graphs, and the
`lam` rule demands the result be well formed, whose coherence conjunct
includes the cross pairs: entries from the two graphs whose labels become
definitionally equal at some later stage must have compatible outputs
there.  Discharging that needs the body's interpretation to be invariant
under replacing its stage by a definitionally equal one (`Interp.stage`),
and the hypothesis of *that* is a typed substitution equality, which only
the soundness statement carries.  §4.5 of `presheaf-plan.md` spells it
out; it is the one place the other repo's bundling is forced. -/
def SoundDir (Γ : List Term) (t : Term) : Prop :=
  ∀ {{Δ Γ₀ σ ρ}}, ⊢ Δ → Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ₀ Γ σ ρ →
    ∀ {m₁ m₂}, Interp Δ Γ t σ ρ m₁ → Interp Δ Γ t σ ρ m₂ →
      TShape.Compat Δ m₁ m₂ ∧ Interp Δ Γ t σ ρ (m₁.join m₂)

/-- Admissibility is stable along a substitution of the stage: the
`Adm`-level companion of `Interp.subst`, needed to move a whole judgment
to a later stage. -/
theorem Adm.subst {Δ Θ Γ₀ Γ : List Term} {σ τ : Subst} {ρ : Valuation}
    (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ) (h : Adm Δ Γ₀ Γ σ ρ) :
    Adm Θ Γ₀ Γ (σ.comp τ) (ρ.subst τ) := by
  sorry

/-! ## Terms with no rule but `bot`

`star` is interpreted by `⊥` and nothing else — that is what makes
`unit_eta` sound — so soundness is automatic for any congruence relating
two such terms, and these three facts are all it takes. -/

theorem Interp.of_bot {Δ Γ σ ρ} {t : Term} {m : TShape} (h : m.2 = Shape.bot) :
    Interp Δ Γ t σ ρ m := by
  have hm : m = Shape.T (n := m.1) m.2 := rfl
  rw [h] at hm
  exact hm ▸ .bot

theorem TShape.HasType.bot_bot {Δ : List Term} {m : TShape} (h : m.2 = Shape.bot) :
    TShape.HasType Δ m TShape.bot := by
  show Shape.HasType Δ (Shape.lift (max m.1 0) m.2) (Shape.lift (max m.1 0) TShape.bot.2)
  rw [h]
  simp only [Shape.lift_bot]
  exact Shape.HasType.bot (Shape.HasType.bot Shape.HasType.sort)

theorem TShape.join_eq_bot {a b : TShape} (ha : a.2 = Shape.bot) (hb : b.2 = Shape.bot) :
    (a.join b).2 = Shape.bot := by
  show (Shape.lift (max a.1 b.1) a.2).join (Shape.lift (max a.1 b.1) b.2) = Shape.bot
  rw [ha, hb]
  simp only [Shape.lift_bot]
  cases max a.1 b.1 <;> rfl

theorem TShape.Compat.of_bot {Δ : List Term} {a b : TShape} (ha : a.2 = Shape.bot) :
    TShape.Compat Δ a b := by
  show Shape.Compat Δ (Shape.lift (max a.1 b.1) a.2) (Shape.lift (max a.1 b.1) b.2)
  rw [ha]
  simp only [Shape.lift_bot]
  cases max a.1 b.1 <;> trivial

/-- Soundness for a congruence between two terms that only `⊥` approximates. -/
theorem sound_of_bot {Γ : List Term} {t t' A : Term}
    (h : ∀ {Δ Γ' σ ρ m}, Interp Δ Γ' t σ ρ m → m.2 = Shape.bot)
    (h' : ∀ {Δ Γ' σ ρ m}, Interp Δ Γ' t' σ ρ m → m.2 = Shape.bot) :
    SoundEq Γ t t' ∧ SoundTy Γ t A ∧ SoundDir Γ t ∧ SoundDir Γ t' := by
  refine ⟨fun _ _ _ _ _ _ _ _ =>
      ⟨fun hm => Interp.of_bot (h hm), fun hm => Interp.of_bot (h' hm)⟩,
    fun _ _ _ _ _ _ _ _ hm => ⟨_, TShape.bot, TShape.LE.refl hm.wf, hm, Interp.of_bot rfl,
      TShape.HasType.bot_bot (h hm)⟩, ?_, ?_⟩ <;>
    intro Δ Γ₀ σ ρ _ _ _ m₁ m₂ hm₁ hm₂
  · exact ⟨TShape.Compat.of_bot (h hm₁),
      Interp.of_bot (TShape.join_eq_bot (h hm₁) (h hm₂))⟩
  · exact ⟨TShape.Compat.of_bot (h' hm₁),
      Interp.of_bot (TShape.join_eq_bot (h' hm₁) (h' hm₂))⟩

/-! ## Proof irrelevance

Everything typed at a proposition collapses to `⊥`, which is what makes
the `proofIrrel` rule sound: the two proofs have the same approximants
because both have only `⊥`.

The proof is `Shape.HasType.proofIrrel` reached after **normalising every
shape to one level**.  That normalisation is forced: `HasType` transports
only upward (§4.5c), so the argument cannot be assembled at the canonical
level of the conclusion, and instead every hypothesis is read at a common
level and the conclusion — an equation with `⊥` — is transported back
down by `Shape.lift_eq_bot`. -/

theorem Interp.eq_bot_of_prop {Γ : List Term} {p t : Term}
    (hp : SoundTy Γ p .prop) (ht : SoundTy Γ t p)
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ)
    (hAdm : Adm Δ Γ₀ Γ σ ρ) {m} (H : Interp Δ Γ t σ ρ m) : m.2 = Shape.bot := by
  obtain ⟨m', a, hle, hm', ha, hty⟩ := ht hΔ W hAdm H
  obtain ⟨a', b, hlea, ha', hb, htya⟩ := hp hΔ W hAdm ha
  have km : m'.1 ≤ max (max m'.1 a.1) (max a'.1 b.1) :=
    Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..)
  have ka : a.1 ≤ max (max m'.1 a.1) (max a'.1 b.1) :=
    Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..)
  have ka' : a'.1 ≤ max (max m'.1 a.1) (max a'.1 b.1) :=
    Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..)
  have kb : b.1 ≤ max (max m'.1 a.1) (max a'.1 b.1) :=
    Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..)
  -- everything at one level
  have hty' := TShape.HasType.def hΔ hm'.wf ha.wf km ka hty
  have hlea' := (TShape.LE.def ka ka').1 hlea
  have htya' := TShape.HasType.def hΔ ha'.wf hb.wf ka' kb htya
  have hble : Shape.LE Δ (b.2.lift (max (max m'.1 a.1) (max a'.1 b.1))) (Shape.sort false) := by
    have := (TShape.LE.def kb (Nat.zero_le _)).1 (Interp.le_sort hb)
    rwa [show Shape.lift (max (max m'.1 a.1) (max a'.1 b.1)) (TShape.sort false).2
        = Shape.sort false from Shape.lift_sort] at this
  have wm := (Shape.lift_wf km).2 hm'.wf
  have wa' := (Shape.lift_wf ka').2 ha'.wf
  -- the collapse, read back down through the order and the lift
  refine TShape.le_bot ?_ hle
  refine Shape.lift_eq_bot (Δ := Δ) km ?_
  rcases Shape.le_prop_cases hble with hbb | hbb
  · -- the type's type is `⊥`, so everything below collapses outright
    rw [hbb] at htya'
    have ha'bot := Shape.HasType.bot_r htya'
    rw [ha'bot] at hlea'
    rw [Shape.le_bot_iff.1 hlea'] at hty'
    exact Shape.HasType.bot_r hty'
  · rw [hbb] at htya'
    exact Shape.HasType.proofIrrel hΔ wa' wm htya'
      (Shape.HasType.mono_r hΔ wm wa' hty' hlea' htya')

/-- Soundness for a congruence whose two sides both collapse to `⊥` at
every stage.  `sound_of_bot`, with the collapse allowed to depend on the
stage — which is what proof irrelevance needs, since the collapse is a
consequence of typing rather than of the term's shape. -/
theorem sound_of_bot_at {Γ : List Term} {t t' A : Term}
    (hty : SoundTy Γ t A)
    (h : ∀ {Δ Γ₀ : List Term} {σ ρ}, ⊢ Δ → Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ₀ Γ σ ρ →
      ∀ {m}, Interp Δ Γ t σ ρ m → m.2 = Shape.bot)
    (h' : ∀ {Δ Γ₀ : List Term} {σ ρ}, ⊢ Δ → Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ₀ Γ σ ρ →
      ∀ {m}, Interp Δ Γ t' σ ρ m → m.2 = Shape.bot) :
    SoundEq Γ t t' ∧ SoundTy Γ t A ∧ SoundDir Γ t ∧ SoundDir Γ t' := by
  refine ⟨fun _ _ _ _ hΔ W hA _ =>
      ⟨fun hm => Interp.of_bot (h hΔ W hA hm), fun hm => Interp.of_bot (h' hΔ W hA hm)⟩,
    hty, ?_, ?_⟩ <;>
    intro Δ Γ₀ σ ρ hΔ W hA m₁ m₂ hm₁ hm₂
  · exact ⟨TShape.Compat.of_bot (h hΔ W hA hm₁),
      Interp.of_bot (TShape.join_eq_bot (h hΔ W hA hm₁) (h hΔ W hA hm₂))⟩
  · exact ⟨TShape.Compat.of_bot (h' hΔ W hA hm₁),
      Interp.of_bot (TShape.join_eq_bot (h' hΔ W hA hm₁) (h' hΔ W hA hm₂))⟩

/-! ## Atoms

`sort`, `unit`, `nat` and `zero` are interpreted by the shapes below one
fixed shape, so all four conclusions come from four facts about that shape
and its type.  In particular `SoundTy` can pick the canonical shape itself
as the saturating witness, which is why no case analysis on the
approximant is needed. -/

theorem sound_atom {Γ : List Term} {t A : Term} {s a : TShape}
    (hle : ∀ {Δ Γ' σ ρ m}, Interp Δ Γ' t σ ρ m → TShape.LE Δ m s)
    (hmk : ∀ {Δ Γ' σ ρ m}, TShape.WF Δ m → TShape.LE Δ m s → Interp Δ Γ' t σ ρ m)
    (ha : ∀ {Δ Γ' σ ρ}, Interp Δ Γ' A σ ρ a)
    (hws : ∀ {Δ : List Term}, TShape.WF Δ s)
    (hsa : ∀ {Δ : List Term}, TShape.HasType Δ s a) :
    SoundEq Γ t t ∧ SoundTy Γ t A ∧ SoundDir Γ t ∧ SoundDir Γ t := by
  refine ⟨fun _ _ _ _ _ _ _ _ => Iff.rfl,
    fun _ _ _ _ _ _ _ _ hm => ⟨s, a, hle hm, hmk hws (TShape.LE.refl hws), ha, hsa⟩,
    ?_, ?_⟩ <;>
    intro Δ Γ₀ σ ρ hΔ _ _ m₁ m₂ hm₁ hm₂ <;>
    exact ⟨TShape.Compat.of_common_upper hΔ hws (hle hm₁) (hle hm₂),
      hmk (TShape.WF.join hΔ
          (TShape.Compat.of_common_upper hΔ hws (hle hm₁) (hle hm₂)) hm₁.wf hm₂.wf)
        (TShape.join_le (hle hm₁) (hle hm₂))⟩

/-! ## The target

The one theorem this branch is for.  Master needs `LogRel.lean` and
`Adequacy.lean` on top of its soundness theorem to get inversion; here the
labels carry the syntax through the model, so the inversion principles of
§6 are corollaries of this statement alone. -/

theorem IsDefEq.sound {Γ : List Term} {t t' A : Term}
    (hΓ : ⊢ Γ) (H : Γ ⊢ t ≡ t' : A) :
    SoundEq Γ t t' ∧ SoundTy Γ t A ∧ SoundDir Γ t ∧ SoundDir Γ t' := by
  induction H with
  -- structural rules: no stage or valuation changes, so these are pure
  -- bookkeeping on the four conclusions
  | symm _ ih =>
    have ⟨he, hty, hd, hd'⟩ := ih hΓ
    exact ⟨he.symm, SoundTy.of_eq he hty, hd', hd⟩
  | trans _ _ ih₁ ih₂ =>
    have ⟨he₁, hty₁, hd₁, _⟩ := ih₁ hΓ
    have ⟨he₂, _, _, hd₂⟩ := ih₂ hΓ
    exact ⟨he₁.trans he₂, hty₁, hd₁, hd₂⟩
  | trans' _ _ ih₁ ih₂ =>
    have ⟨he₁, hty₁, hd₁, _⟩ := ih₁ hΓ
    have ⟨he₂, _, _, hd₂⟩ := ih₂ hΓ
    exact ⟨he₁.trans he₂, hty₁, hd₁, hd₂⟩
  -- conversion: only the *type*'s interpretation moves, and `SoundEq` of
  -- the two types is exactly what moves it
  | defeqDF _ _ ihAB ih =>
    have ⟨heAB, _, _, _⟩ := ihAB hΓ
    have ⟨he, hty, hd, hd'⟩ := ih hΓ
    refine ⟨he, ?_, hd, hd'⟩
    intro Δ Γ₀ σ ρ hΔ W hA m hm
    have ⟨m', a, hle, hm', ha, hht⟩ := hty hΔ W hA hm
    exact ⟨m', a, hle, hm', (heAB hΔ W hA).1 ha, hht⟩
  -- everything below is one rule of the induction, each an independent
  -- obligation; see §4.6 of `presheaf-plan.md` for what each needs
  | bvar => sorry
  | sort =>
    exact sound_atom Interp.le_sort (fun hw h => .sort hw h) Interp.sort' trivial
      (fun {_} => by simpa [TShape.HasType, TShape.sort] using Shape.HasType.sort)
  | @unit _ r =>
    exact sound_atom Interp.le_unit (fun hw h => .unit hw h) Interp.sort' trivial
      (fun {_} => by
        simpa [TShape.HasType] using
          Shape.HasTypeS.unit (show (r : Bool) ≤ r by cases r <;> decide))
  | star => exact sound_of_bot (fun H => by cases H; rfl) (fun H => by cases H; rfl)
  | appDF => sorry
  | lamDF => sorry
  | forallEDF => sorry
  -- Σ now has real rules, mirroring Π, so these are no longer vacuous
  | sigmaDF => sorry
  | pairDF => sorry
  | fstDF => sorry
  | sndDF => sorry
  | beta => sorry
  | eta => sorry
  | unit_eta => sorry
  -- unblocked by the Σ rules: `fst` now reads the first component off a
  -- pair shape, so the two sides really can have the same approximants
  | pair_fst => sorry
  | pair_snd => sorry
  | fst_snd => sorry
  | nat =>
    exact sound_atom Interp.le_nat (fun hw h => .nat hw h) Interp.sort' trivial
      (fun {_} => by simpa [TShape.HasType] using Shape.HasTypeS.nat)
  | zero =>
    exact sound_atom Interp.le_zero (fun hw h => .zero hw h) Interp.nat' trivial
      (fun {_} => by simpa [TShape.HasType] using Shape.HasTypeS.zero)
  | succDF => sorry
  | natCaseDF => sorry
  | natCase_zero => sorry
  | natCase_succ => sorry
  | YDF => sorry
  | Y_unfold => sorry
  | idDF => sorry
  | reflDF => sorry
  | trDF => sorry
  | tr_refl => sorry
  -- both proofs collapse to `⊥`, which is exactly what the rule says
  | proofIrrel _ _ _ ihp ihh ihh' =>
    exact sound_of_bot_at (ihh hΓ).2.1
      (fun hΔ W hA _ hm => Interp.eq_bot_of_prop (ihp hΓ).2.1 (ihh hΓ).2.1 hΔ W hA hm)
      (fun hΔ W hA _ hm => Interp.eq_bot_of_prop (ihp hΓ).2.1 (ihh' hΓ).2.1 hΔ W hA hm)
