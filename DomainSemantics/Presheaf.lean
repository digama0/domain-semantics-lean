import DomainSemantics.Interp
import DomainSemantics.Regular

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
| `HasFixedness Γ t A` | `SoundTy` |
| `PiReady Γ A B` | absent; it collapses into directedness |
| `RawJudgment` (6 fields) | `SoundEq` and `SoundTy`, proved together |

Two of his notions have no counterpart because they are artefacts of the
ideal-theoretic setting rather than content: `RawValue = ΩLower` (a value
is a single shape here, and the lower set is `Interp`'s own downward
closure) and the `rank`/`piStage`/`piLimit` fixed point (the level index
does that work). -/

namespace DomainSemantics

@[simp] theorem Subst.id_comp {σ : Subst} : Subst.id.comp σ = σ := by
  funext i; rfl

/-- The stage an instantiation is read at: `(one a).comp σ` is `σ`
extended by `a[σ]`. -/
theorem Subst.one_comp {a : Term} {σ : Subst} :
    (Subst.one a).comp σ = σ.cons (a.subst σ) := by
  rw [Subst.cons_comp, Subst.id_comp]

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
interpretation is saturated (the `b'` premise), the slot has a type among
the type's approximants, and the slot is a fixed point of the decoder of
that type — here, `TShape.HasType`.  The `WF` premise is what master gets
for free from its shapes being a `WF` subtype.

The second premise used to be `∃ b', b ≤ b' ∧ Interp b' ∧ HasType b' type`,
standing in for a downward closure typing did not have.  It has one now
(`TShape.HasType.mono_l`), so it says directly that every approximant of
`A` is a type. -/

inductive Adm (Δ : List Term) : List Term → List Term → Subst → Valuation → Prop where
  | nil {Γ σ} : Adm Δ Γ Γ σ Valuation.nil
  | cons {Γ₀ Γ A σ ρ x a} :
      Adm Δ Γ₀ Γ σ.tail ρ →
      (∀ b, Interp Δ Γ A σ.tail ρ b → TShape.HasType Δ b TShape.type) →
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

/-- Weakening the stage by one slot: `A` at `σ.tail` under `ρ` is
`A.lift` at `σ` under `ρ.push x`.  `Interp.weak'` at `Lift.refl.skip`. -/
theorem Interp.weak_one {Δ Γ Γ' : List Term} {A : Term} {σ ρ x m}
    (H : Interp Δ Γ A σ.tail ρ m) : Interp Δ Γ' A.lift σ (ρ.push x) m :=
  Interp.weak' (l := Lift.refl.skip) (Subst.tail_eq_lift_l ▸ H) (fun _ => rfl)

/-- The slot a variable reads is typed at an approximant of its type.
This is the content of `Adm` that `SoundTy`'s `bvar` case needs, and the
reason `Adm` is an inductive rather than a predicate on slots: the type of
slot `i` lives in the context *below* it, so the statement has to be
weakened back up one binder at a time. -/
theorem Adm.lookup {Δ Γ₀ Γ : List Term} {σ ρ} (h : Adm Δ Γ₀ Γ σ ρ) :
    ∀ {i A}, Lookup Γ i A → ∃ a, Interp Δ Γ A σ ρ a ∧ TShape.HasType Δ (ρ i) a := by
  induction h with
  -- below the base context every slot is `⊥`, which is typed at `⊥`
  | nil => exact fun _ => ⟨TShape.bot, .bot, TShape.HasType.bot_bot rfl⟩
  | cons _ _ ha _ hxa ih =>
    intro i A' hl
    cases hl with
    | zero => exact ⟨_, Interp.weak_one ha, hxa⟩
    | succ hl =>
      obtain ⟨b, hb, hty⟩ := ih hl
      exact ⟨b, Interp.weak_one hb, hty⟩

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

/-- Every approximant of `t` is typed at an approximant of `A`: master's
`SoundTy`, his `HasFixedness`, and the other repo's
`rawExtend ⟦A⟧ ⟦t⟧ = ⟦t⟧`.

Master and the first version here said something weaker — every
approximant is *below* one that is typed, master's `InterpTyped` — because
typing was not a lower set and this statement was not provable.  It is one
now (`TShape.HasType.mono_l`), so the saturating witness is gone: the two
are equivalent, and the consumers that used to end in a `mono_l` no longer
need one. -/
structure SoundTy (Γ : List Term) (t A : Term) : Prop where
  /-- The syntactic typing.  Free at every site that proves a `SoundTy` —
  each `IsDefEq` rule carries it — and what the `StrongSound` machinery
  needs to produce a *reflexivity* where a semantic `SoundEq.refl` would
  have been free. -/
  typed : Γ ⊢ t : A
  /-- Every approximant of `t` is typed at an approximant of `A`. -/
  approx : ∀ {{Δ Γ₀ σ ρ}}, ⊢ Δ → Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ₀ Γ σ ρ →
    ∀ {m}, Interp Δ Γ t σ ρ m → ∃ a, Interp Δ Γ A σ ρ a ∧ TShape.HasType Δ m a

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
    (hs : Γ ⊢ t ≡ t' : A) (he : SoundEq Γ t t') (h : SoundTy Γ t A) : SoundTy Γ t' A := by
  refine ⟨hs.hasType.2, ?_⟩
  intro Δ Γ₀ σ ρ hΔ W hA m hm
  exact h.approx hΔ W hA ((he hΔ W hA).2 hm)

/-- Directedness of the approximant set: his `HasIdeality`.

**Not** a conclusion of `IsDefEq.sound`, and not a lemma about `Interp`
alone either — it is `IsDefEq.dir`, its own induction on *typing*.  Two
things decide that.

It cannot be about raw terms, because joining two λ-shapes appends their
graphs and the `lam` rule demands the result well formed, whose coherence
conjunct includes the cross pairs: entries of the two graphs whose labels
become definitionally equal at a later stage must have compatible outputs
there.  Discharging that moves both bodies to one stage along the label
equation, and the hypothesis of `IsDefEq.stage` is a *typed* substitution
equality — so the binder's annotation has to be typed, which a raw term
does not say.  That is the whole residue of the other repo's quotient,
where a stage is a morphism and carries its typing.

But it need not travel with `SoundEq`/`SoundTy` either, and it should not:
the hypothesis here is `Valuation.WF`, not `Adm`, so the recursive call
under a binder — at the joined argument slot — has nothing to type.  With
`Adm` it would need the joined slot typed at an approximant of `⟦A⟧`,
which is `SoundJoin` and, at Σ, unproved.  His `IsIdealValued` is likewise
directedness at *every* shape, and master's `compat_join` takes no `Fits`.
His bundling into `RawTermProperties` is forced only because his
application is a sup over `sourceQuery` and needs `PiReady` plus
fixedness to collapse; ours names the label and looks up once.

The conclusion is his `IsDirected` — a common upper bound *in the set* —
rather than master's `Compat ∧ join`, which is `Interp.Dir.join`. -/
def SoundDir (Γ : List Term) (t : Term) : Prop :=
  ∀ {{Δ : List Term}} {σ ρ}, ⊢ Δ → Ctx.SubstEq Δ σ σ Γ → Valuation.WF Δ ρ →
    Interp.Dir Δ Γ t σ ρ

-- There is no `Adm.subst`.  Moving a judgment to a later stage is only
-- ever needed inside directedness, whose hypothesis is `Valuation.WF`, and
-- that moves by `TShape.WF.subst` slotwise (`Valuation.WF.subst`).  The
-- other repo needs `SourceAdmissible.pullback` because its admissibility
-- carries the decoder fixed-point condition on every slot.

/-! ## Terms with no rule but `bot`

`star` is interpreted by `⊥` and nothing else — that is what makes
`unit_eta` sound — so soundness is automatic for any congruence relating
two such terms, and these three facts are all it takes. -/

theorem Interp.of_bot {Δ Γ σ ρ} {t : Term} {m : TShape} (h : m.2 = Shape.bot) :
    Interp Δ Γ t σ ρ m := by
  have hm : m = Shape.T (n := m.1) m.2 := rfl
  rw [h] at hm
  exact hm ▸ .bot

theorem TShape.Compat.of_bot {Δ : List Term} {a b : TShape} (ha : a.2 = Shape.bot) :
    TShape.Compat Δ a b := by
  show Shape.Compat Δ (Shape.lift (max a.1 b.1) a.2) (Shape.lift (max a.1 b.1) b.2)
  rw [ha]
  simp only [Shape.lift_bot]
  cases max a.1 b.1 <;> trivial

/-- Soundness for a congruence between two terms that only `⊥` approximates. -/
theorem sound_of_bot {Γ : List Term} {t t' A : Term} (hty : Γ ⊢ t : A)
    (h : ∀ {Δ Γ' σ ρ m}, Interp Δ Γ' t σ ρ m → m.2 = Shape.bot)
    (h' : ∀ {Δ Γ' σ ρ m}, Interp Δ Γ' t' σ ρ m → m.2 = Shape.bot) :
    SoundEq Γ t t' ∧ SoundTy Γ t A :=
  ⟨fun _ _ _ _ _ _ _ _ =>
      ⟨fun hm => Interp.of_bot (h hm), fun hm => Interp.of_bot (h' hm)⟩,
    hty, fun _ _ _ _ _ _ _ _ hm =>
      ⟨TShape.bot, Interp.of_bot rfl, TShape.HasType.bot_bot (h hm)⟩⟩

/-- Directedness for such a term: `⊥` is its own upper bound. -/
theorem dir_of_bot {Γ : List Term} {t : Term}
    (h : ∀ {Δ Γ' σ ρ m}, Interp Δ Γ' t σ ρ m → m.2 = Shape.bot) : SoundDir Γ t :=
  by
  intro _ _ _ _ _ _ _ _ hm₁ hm₂
  exact ⟨TShape.bot, trivial, Interp.of_bot rfl,
    TShape.bot_le' (h hm₁), TShape.bot_le' (h hm₂)⟩

/-! ## Proof irrelevance

Everything typed at a proposition collapses to `⊥`, which is what makes
the `proofIrrel` rule sound: the two proofs have the same approximants
because both have only `⊥`.

The proof is `TShape.HasType.proofIrrel`, applied directly: with typing
over `TShape` there is nothing to normalise, since both `mono_r` and the
order are level-free.  The old version read every hypothesis at a common
level and transported the conclusion back down with `Shape.lift_eq_bot`. -/

theorem Interp.eq_bot_of_prop {Γ : List Term} {p t : Term}
    (hp : SoundTy Γ p .prop) (ht : SoundTy Γ t p)
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ)
    (hAdm : Adm Δ Γ₀ Γ σ ρ) {m} (H : Interp Δ Γ t σ ρ m) : m.2 = Shape.bot := by
  obtain ⟨a, ha, hty⟩ := ht.approx hΔ W hAdm H
  obtain ⟨b, hb, htya⟩ := hp.approx hΔ W hAdm ha
  rcases TShape.le_prop_cases (Interp.le_sort hb) with hbb | hbb
  · -- the type's type is `⊥`, so everything below it collapses outright
    exact TShape.HasType.bot_r hΔ (TShape.HasType.bot_r hΔ hbb htya) hty
  · -- the type is a proposition, so its inhabitants are `⊥`
    exact TShape.HasType.proofIrrel hΔ hty (htya.sort_level hbb (k' := 0))

/-- **A unit type is inhabited only by `⊥`.**  The `bot` clause is the only
one whose type can be a `unit` shape; `mono_r` first moves the type up to
the canonical one, which is where `cases` can see that. -/
theorem TShape.HasType.unit_r {Δ : List Term} (hΔ : ⊢ Δ) {m a : TShape} {r : Bool}
    (ha : TShape.LE Δ a (TShape.unit r)) (h : TShape.HasType Δ m a) :
    m.2 = Shape.bot := by
  cases TShape.HasType.mono_r hΔ h (TShape.unit r) ha (.unit (Bool.le_true' r)) with
  | bot _ => rfl
  | refl _ hc _ =>
    obtain ⟨M, _, _, h2⟩ := TShape.LE.at_succ hc
    exact absurd h2 (fun x => x)

/-- Everything typed at the unit type collapses, which is what makes
`unit_eta` sound: both sides have only `⊥`. -/
theorem Interp.eq_bot_of_unit {Γ : List Term} {e : Term} {r : Bool}
    (ht : SoundTy Γ e (.unit r))
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ)
    (hAdm : Adm Δ Γ₀ Γ σ ρ) {m} (H : Interp Δ Γ e σ ρ m) : m.2 = Shape.bot :=
  have ⟨_, ha, hty⟩ := ht.approx hΔ W hAdm H
  TShape.HasType.unit_r hΔ (Interp.le_unit ha) hty

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
    SoundEq Γ t t' ∧ SoundTy Γ t A :=
  ⟨fun _ _ _ _ hΔ W hA _ =>
      ⟨fun hm => Interp.of_bot (h hΔ W hA hm), fun hm => Interp.of_bot (h' hΔ W hA hm)⟩, hty⟩

/-! ## Atoms

`sort`, `unit`, `nat` and `zero` are interpreted by the shapes below one
fixed shape, so both conclusions come from three facts about that shape
and its type: everything is below it, the type has a canonical
interpretation, and the shape is typed at it.  No case analysis on the
approximant is needed — `mono_l` brings the canonical typing down to it. -/

theorem sound_atom {Γ : List Term} {t A : Term} {s a : TShape} (hty : Γ ⊢ t : A)
    (hle : ∀ {Δ Γ' σ ρ m}, Interp Δ Γ' t σ ρ m → TShape.LE Δ m s)
    (ha : ∀ {Δ Γ' σ ρ}, Interp Δ Γ' A σ ρ a)
    (hsa : ∀ {Δ : List Term}, TShape.HasType Δ s a) :
    SoundEq Γ t t ∧ SoundTy Γ t A :=
  ⟨fun _ _ _ _ _ _ _ _ => Iff.rfl,
    hty, fun _ _ _ _ hΔ _ _ _ hm => ⟨a, ha, TShape.HasType.mono_l hΔ hsa (hle hm)⟩⟩

/-- Directedness for a variable: its slot bounds everything. -/
theorem dir_bvar {Γ : List Term} {i : Nat} : SoundDir Γ (.bvar i) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  refine ⟨ρ i, hwρ i, .bvar (hwρ i) (TShape.LE.refl (hwρ i)), ?_, ?_⟩
  · cases h₁ with
    | bot => exact TShape.bot_le' rfl
    | bvar _ hle => exact hle
  · cases h₂ with
    | bot => exact TShape.bot_le' rfl
    | bvar _ hle => exact hle

/-- Directedness for such a term: the canonical shape bounds everything. -/
theorem dir_atom {Γ : List Term} {t : Term} {s : TShape}
    (hle : ∀ {Δ Γ' σ ρ m}, Interp Δ Γ' t σ ρ m → TShape.LE Δ m s)
    (hmk : ∀ {Δ Γ' σ ρ m}, TShape.WF Δ m → TShape.LE Δ m s → Interp Δ Γ' t σ ρ m)
    (hws : ∀ {Δ : List Term}, TShape.WF Δ s) : SoundDir Γ t :=
  by
  intro _ _ _ _ _ _ _ _ hm₁ hm₂
  exact ⟨s, hws, hmk hws (TShape.LE.refl hws), hle hm₁, hle hm₂⟩

/-- `SoundTy` at a sort, as a typing of the approximant *itself*.

`SoundTy` only says that an approximant is *below* a typed shape, and the
step that brings the typing back down is `mono_l` -- so this is exactly
the lemma that was out of reach before types became lower sets.  `mono_r`
first moves the type from whatever approximates the sort up to the sort
itself, along `Interp.le_sort`. -/
theorem SoundTy.hasType {Γ : List Term} {A : Term} {u : Bool} (h : SoundTy Γ A (.sort u))
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {b : TShape} (hb : Interp Δ Γ A σ ρ b) : TShape.HasType Δ b (TShape.sort u) := by
  have ⟨a, ha, hty⟩ := h.approx hΔ W hAdm hb
  exact TShape.HasType.mono_r hΔ hty _ (Interp.le_sort ha) .sort

/-- `SoundTy` at a sort, as the `Adm.cons` field wants it: every
approximant of `A` is a *type*.  `cumul` moves the sort up to `.type`. -/
theorem SoundTy.isType {Γ : List Term} {A : Term} {u : Bool} (h : SoundTy Γ A (.sort u))
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {b : TShape} (hb : Interp Δ Γ A σ ρ b) : TShape.HasType Δ b TShape.type :=
  (h.hasType hΔ W hAdm hb).cumul rfl (Bool.le_true' u)

/-- The `SoundTy` half of `forallEDF`, in isolation: a Π-type's
interpretation is typed at its sort.

This is the obligation that was out of reach before `HasType` became a
lower set: the Π's approximant is below the canonical Π-shape, and the
step that brings the typing back down to it is `mono_l`. -/
theorem sound_forallE_ty {Γ : List Term} {A B : Term} {u v : Bool}
    (ihA : SoundTy Γ A (.sort u))
    (ihB : SoundTy (A :: Γ) B (.sort v))
    (hAty : Γ ⊢ A : .sort u) :
    SoundTy Γ (.forallE A B) (.sort v) := by
  refine ⟨.forallEDF hAty ihB.typed ihB.typed, ?_⟩
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  cases hm with
  | bot =>
    exact ⟨TShape.sort v, Interp.sort', .bot .sort⟩
  | forallE hA hd hwf hlab hdom hbody hw hle =>
    refine ⟨TShape.sort v, Interp.sort', TShape.HasType.mono_l hΔ ?_ hle⟩
    -- the domain half is now the constructor's own premise; only the
    -- codomain runs an induction hypothesis
    refine .forallE hd (fun e he => ?_) hwf
    · -- the codomain, at the stage extended by the entry's label: the
      -- entry's own data is exactly what `Adm.cons` and `SubstEq.cons` ask for
      obtain ⟨_, hty⟩ := hlab e he
      have hwe := hwf.2.2.2.1 e he
      have W' : Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A :: Γ) :=
        .cons W hAty (hty.defeqDF hwe.2.1)
      have hAdm' : Adm Δ Γ₀ (A :: Γ) (σ.cons e.tm) (ρ.push (Shape.T e.inp)) :=
        .cons hAdm (fun _ hb => ihA.isType hΔ W hAdm hb) hA hwe.2.2.1 (hdom e he)
      exact ihB.hasType hΔ W' hAdm' (hbody e he)

/-- One direction of the `SoundEq` half of `forallEDF`.

A Π-shape carries the *syntax* `(A[σ], B[σ.lift])` as its label, so the
two sides of the congruence do not produce the same shapes on the nose --
`⟦∀ A B⟧` is built over one label and `⟦∀ A' B'⟧` over another.  What
saves the statement is that `Shape.LE` compares labels up to definitional
equality: the two Π-shapes are `≈`-equivalent, and an approximant of one
is an approximant of the other by `LE.trans` alone.  Everything else in
the constructor -- the domain shape, the graph, the `HasDom` premises --
is reused verbatim.

The context of the body's interpretation changes from `A :: Γ` to
`A' :: Γ`, and that is free: `Interp` never looks at its context index
(`Interp.ctx`).  It is the *stage* that carries the content, and the
stage is untouched. -/
theorem sound_forallE_eq_of {Γ : List Term} {A A' B B' : Term} {u v : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (hBB' : A :: Γ ⊢ B ≡ B' : .sort v)
    (ihA : SoundEq Γ A A') (ihAty : SoundTy Γ A (.sort u))
    (ihB : SoundEq (A :: Γ) B B')
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {m : TShape} (H : Interp Δ Γ (.forallE A B) σ ρ m) :
    Interp Δ Γ (.forallE A' B') σ ρ m := by
  have ⟨⟨_, hAσ⟩, _, hBσ⟩ :
      PiLabelEq Δ (A.subst σ) (B.subst σ.lift) (A'.subst σ) (B'.subst σ.lift) :=
    PiLabelEq.subst hΔ W ⟨⟨u, hAA'⟩, v, hBB'⟩
  cases H with
  | bot => exact .bot
  | forallE hA hd hwf hlab hdom hbody hw hle =>
    refine .forallE ((ihA hΔ W hAdm).1 hA) hd
      ⟨⟨_, hAσ.hasType.2⟩, ⟨_, (hAσ.defeqDF_l hΔ hBσ).hasType.2⟩, hwf.2.2⟩
      (fun e he => ?_) hdom (fun e he => ?_) hw
      (hle.trans hΔ (TShape.LE.T.2
        ⟨⟨⟨_, hAσ⟩, _, hBσ⟩, .refl hwf.2.2.1, .refl hwf.2.2.2⟩))
    · obtain ⟨_, hty⟩ := hlab e he
      exact ⟨_, hty.trans' hAσ⟩
    · -- the body, at the stage extended by the entry's label
      obtain ⟨_, hty⟩ := hlab e he
      have hwe := hwf.2.2.2.1 e he
      have W' : Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A :: Γ) :=
        .cons W hAA'.hasType.1 (hty.defeqDF hwe.2.1)
      have hAdm' : Adm Δ Γ₀ (A :: Γ) (σ.cons e.tm) (ρ.push (Shape.T e.inp)) :=
        .cons hAdm (fun _ hb => ihAty.isType hΔ W hAdm hb) hA hwe.2.2.1 (hdom e he)
      exact Interp.ctx ((ihB hΔ W' hAdm').1 (hbody e he))

/-- The `SoundEq` half of `forallEDF`: the two Π-types have the same
approximants at every stage.

Both directions are the same argument, run on the mirrored data -- which
is exactly why the rule carries its codomain premise twice, once over
each domain.  Without the `A' :: Γ` copy the backward direction would
have no induction hypothesis to run. -/
theorem sound_forallE_eq {Γ : List Term} {A A' B B' : Term} {u v : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u)
    (hB : A :: Γ ⊢ B ≡ B' : .sort v) (hB' : A' :: Γ ⊢ B ≡ B' : .sort v)
    (ihA : SoundEq Γ A A') (ihAty : SoundTy Γ A (.sort u))
    (ihB : SoundEq (A :: Γ) B B') (ihB' : SoundEq (A' :: Γ) B B') :
    SoundEq Γ (.forallE A B) (.forallE A' B') := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  exact ⟨sound_forallE_eq_of hAA' hB ihA ihAty ihB hΔ W hAdm,
    sound_forallE_eq_of hAA'.symm hB'.symm ihA.symm (SoundTy.of_eq hAA' ihA ihAty) ihB'.symm
      hΔ W hAdm⟩

/-! ## Σ, which mirrors Π

`Interp.sigma`'s clauses are `Interp.forallE`'s with the head changed, so
these two are `sound_forallE_ty` and `sound_forallE_eq` with the head
changed.  The one real difference is the sort: the `TShape.HasType.sigma`
clause types its outputs at `.type` where `forallE` types them at the
same sort as the Π, so the codomain's typing needs `cumul` on the way in
— which is `SoundTy.isType` rather than `SoundTy.hasType`. -/

/-- The `SoundTy` half of `sigmaDF`. -/
theorem sound_sigma_ty {Γ : List Term} {A B : Term} {u v : Bool}
    (ihA : SoundTy Γ A (.sort u))
    (ihB : SoundTy (A :: Γ) B (.sort v))
    (hAty : Γ ⊢ A : .sort u) :
    SoundTy Γ (.sigma A B) .type := by
  refine ⟨.sigmaDF hAty ihB.typed ihB.typed, ?_⟩
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  cases hm with
  | bot => exact ⟨TShape.type, Interp.sort', .bot .sort⟩
  | sigma hA hd hwf hlab hdom hbody hw hle =>
    refine ⟨TShape.type, Interp.sort', TShape.HasType.mono_l hΔ ?_ hle⟩
    refine .sigma hd (fun e he => ?_) hwf
    obtain ⟨_, hty⟩ := hlab e he
    have hwe := hwf.2.2.2.1 e he
    have W' : Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A :: Γ) :=
      .cons W hAty (hty.defeqDF hwe.2.1)
    have hAdm' : Adm Δ Γ₀ (A :: Γ) (σ.cons e.tm) (ρ.push (Shape.T e.inp)) :=
      .cons hAdm (fun _ hb => ihA.isType hΔ W hAdm hb) hA hwe.2.2.1 (hdom e he)
    exact ihB.isType hΔ W' hAdm' (hbody e he)

/-- One direction of the `SoundEq` half of `sigmaDF`; see
`sound_forallE_eq_of` for what carries it. -/
theorem sound_sigma_eq_of {Γ : List Term} {A A' B B' : Term} {u v : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (hBB' : A :: Γ ⊢ B ≡ B' : .sort v)
    (ihA : SoundEq Γ A A') (ihAty : SoundTy Γ A (.sort u))
    (ihB : SoundEq (A :: Γ) B B')
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {m : TShape} (H : Interp Δ Γ (.sigma A B) σ ρ m) :
    Interp Δ Γ (.sigma A' B') σ ρ m := by
  have ⟨⟨_, hAσ⟩, _, hBσ⟩ :
      PiLabelEq Δ (A.subst σ) (B.subst σ.lift) (A'.subst σ) (B'.subst σ.lift) :=
    PiLabelEq.subst hΔ W ⟨⟨u, hAA'⟩, v, hBB'⟩
  cases H with
  | bot => exact .bot
  | sigma hA hd hwf hlab hdom hbody hw hle =>
    refine .sigma ((ihA hΔ W hAdm).1 hA) hd
      ⟨⟨_, hAσ.hasType.2⟩, ⟨_, (hAσ.defeqDF_l hΔ hBσ).hasType.2⟩, hwf.2.2⟩
      (fun e he => ?_) hdom (fun e he => ?_) hw
      (hle.trans hΔ (TShape.LE.T.2
        ⟨⟨⟨_, hAσ⟩, _, hBσ⟩, .refl hwf.2.2.1, .refl hwf.2.2.2⟩))
    · obtain ⟨_, hty⟩ := hlab e he
      exact ⟨_, hty.trans' hAσ⟩
    · obtain ⟨_, hty⟩ := hlab e he
      have hwe := hwf.2.2.2.1 e he
      have W' : Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A :: Γ) :=
        .cons W hAA'.hasType.1 (hty.defeqDF hwe.2.1)
      have hAdm' : Adm Δ Γ₀ (A :: Γ) (σ.cons e.tm) (ρ.push (Shape.T e.inp)) :=
        .cons hAdm (fun _ hb => ihAty.isType hΔ W hAdm hb) hA hwe.2.2.1 (hdom e he)
      exact Interp.ctx ((ihB hΔ W' hAdm').1 (hbody e he))

/-- The `SoundEq` half of `sigmaDF`. -/
theorem sound_sigma_eq {Γ : List Term} {A A' B B' : Term} {u v : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u)
    (hB : A :: Γ ⊢ B ≡ B' : .sort v) (hB' : A' :: Γ ⊢ B ≡ B' : .sort v)
    (ihA : SoundEq Γ A A') (ihAty : SoundTy Γ A (.sort u))
    (ihB : SoundEq (A :: Γ) B B') (ihB' : SoundEq (A' :: Γ) B B') :
    SoundEq Γ (.sigma A B) (.sigma A' B') := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  exact ⟨sound_sigma_eq_of hAA' hB ihA ihAty ihB hΔ W hAdm,
    sound_sigma_eq_of hAA'.symm hB'.symm ihA.symm (SoundTy.of_eq hAA' ihA ihAty) ihB'.symm
      hΔ W hAdm⟩

/-! ## Stage invariance

The interpretation depends on its stage only up to definitional equality.
Master needs no such lemma, its shapes carrying no labels; the other repo
gets it from the quotient, two definitionally equal substitutions being
the *same* morphism of `Ctx`.  Here it is a theorem, and — this is the
point — a theorem about a **typed** term, not about `Interp` alone.

For a raw `t` the statement is false.  Take `t = .forallE A B` with `A`
ill-typed in `Γ` but `A[σ]` typed in `Δ`: the `forallE` rule holds with
label `A[σ]`, and nothing relates it to `A[σ']`, because no rule types a
label in `Γ` — `hlab` types labels in `Δ`.  So the induction is on a
typing derivation, which is exactly what supplies `Δ ⊢ A[σ] ≡ A[σ'] : sort u`
for each label, by `IsDefEq.subst'`. -/

theorem IsDefEq.stage {Γ : List Term} {t t' A : Term} (hΓ : ⊢ Γ)
    (H : Γ ⊢ t ≡ t' : A) {Δ : List Term} {σ σ' : Subst} (hΔ : ⊢ Δ)
    (W : Ctx.SubstEq Δ σ σ' Γ) {ρ m} :
    Interp Δ Γ t σ ρ m → Interp Δ Γ t σ' ρ m := by
  sorry

/-! ## Directedness

Directedness is always established through a **common upper bound**: that
is the whole content of `Interp.Dir`, and compatibility and the join come
off it by `Interp.Dir.join`.  `Compat` has no introduction rule of its
own, so there is no other way.

The Π case is the other repo's `BasisAction.pi_isDirected` — bound the two
domain shapes inside `⟦A⟧`, append the two graphs, and the generator is
monotone in both — resting on his `GraphValid.internallyCompatible` for
the appended graph's cross pairs.  That argument transfers step for step,
with `IsDefEq.stage` doing the work his quotient does for free:

| his | ours |
|---|---|
| the label equation puts both memberships in one lower set | `IsDefEq.stage` |
| `Compatible.upper` | the join of the two inputs |
| monotonicity of the codomain family in its argument | `Interp.mono_val` |
| `IsIdealValued` at that upper bound | the codomain's own `SoundDir` |
| `Compatible.of_common_upper` | ours, same name |

His `IsIdealValued` is directedness at *every* argument shape, with no
"the argument is in `⟦A⟧`" side condition, because his body action coerces
its argument through `rawExtend ⟦A⟧` first.  Ours is `SoundDir` under a
`Valuation.WF` hypothesis, which asks nothing of the slot either — and
that is what keeps `SoundJoin` out of this proof. -/

/-- **Directedness of a type's extension**: two compatible shapes typed at
an approximant of `⟦A⟧` have a *typed upper bound* there.

The elementary shadow of the other repo's
`CodeAssignment.rawExtend_isDirected`.  There a value is an *ideal* and
semantic typing is the fixed point `rawExtend ⟦A⟧ x = x`, so the shape
this asks for is literally `rawExtend ⟦A⟧ (x ⊔ y)`: it dominates both
because both are already fixed points below the join, it is typed by
idempotence, and it is directed because `rawExtend` is a `bind₂` of
ideals — three facts free from the ideal structure, none an induction.  A
value here is a *single shape*, so there is no retraction to appeal to and
the fact is content.

Upper-bound form, to match his `IsDirected`, which never mentions the
join.  The join form is out of reach anyway: the `pair` clause of
`HasType` types a pair at a *dominating* first component, and two
compatible pairs can carry incompatible dominators, so there need be no
code to read at `x ⊔ y`.  He never meets this, having no Σ-types.

**Its one consumer is `tr`** (`IsDefEq.dir`), where two approximants are
typed at two approximants of the motive and the joined witness has to be
typed at the joined motive; master does it with `TShape.HasType.join'` at
an arbitrary type, which is the lemma this branch removed.  Π and λ do not
need it, now that directedness runs under `Valuation.WF`. -/
def SoundJoin (Γ : List Term) (A : Term) : Prop :=
  ∀ {{Δ Γ₀ : List Term}} {σ ρ}, ⊢ Δ → Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ₀ Γ σ ρ →
    ∀ {a x y}, Interp Δ Γ A σ ρ a → TShape.WF Δ x → TShape.WF Δ y →
      TShape.HasType Δ x a → TShape.HasType Δ y a → TShape.Compat Δ x y →
      ∃ z, TShape.WF Δ z ∧ TShape.LE Δ x z ∧ TShape.LE Δ y z ∧ TShape.HasType Δ z a

/-- **`SoundJoin` holds, for every type.**  Once a Σ-value is a first
component and a graph (§5.1b), the subject join is `TShape.HasType.join`:
no `Interp`, no `Adm`, no induction on `A` — the pairs' graphs append and
their first components join by the inner induction.  The definition is
kept because its consumers quantify over it; this is the only proof any
of them will ever need. -/
theorem sound_join {Γ : List Term} {A : Term} : SoundJoin Γ A := by
  intro Δ Γ₀ σ ρ hΔ _ _ a x y _ hx hy hxa hya hc
  exact ⟨x.join y, TShape.WF.join hΔ hc hx hy, (TShape.le_join hΔ hx hy hc).1,
    (TShape.le_join hΔ hx hy hc).2, TShape.HasType.join hΔ hc hxa hya⟩

/-- What `SoundJoin` is for: with typing lower-closed, a typed *upper
bound* types the join itself.  Every consumer of a relational lookup needs
this, since the lookup's `join` rule returns `y₁ ⊔ y₂` and the two sides
come typed separately. -/
theorem SoundJoin.hasType_join {Γ : List Term} {A : Term} (h : SoundJoin Γ A)
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ)
    (hAdm : Adm Δ Γ₀ Γ σ ρ) {a x y : TShape} (ha : Interp Δ Γ A σ ρ a)
    (hxa : TShape.HasType Δ x a) (hya : TShape.HasType Δ y a)
    (hc : TShape.Compat Δ x y) : TShape.HasType Δ (x.join y) a :=
  have ⟨z, _, hxz, hyz, hza⟩ :=
    h hΔ W hAdm ha hxa.wf.1 hya.wf.1 hxa hya hc
  TShape.HasType.mono_l hΔ hza (TShape.join_le hΔ hxz hyz)

/-- The common upper bound of two Π-shapes: same labels (both come from
the same term at the same stage), domains joined by `A`'s directedness,
graphs appended.

All the content is the appended graph's coherence, and there the cross
pairs; see the section comment.  The domain of the joined shape is a type
because each domain is — the `Interp.forallE` premise added for exactly
this — and `HasType.join` at a *sort* is available. -/
theorem sound_forallE_ub {Γ : List Term} {A B : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B ≡ B : .sort v)
    (ihAdir : SoundDir Γ A) (ihBdir : SoundDir (A :: Γ) B)
    {Δ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hwρ : Valuation.WF Δ ρ)
    {n₁ n₂} {d₁ : Shape n₁} {g₁ : ShapeFun n₁} {d₂ : Shape n₂} {g₂ : ShapeFun n₂}
    (hA₁ : Interp Δ Γ A σ ρ (Shape.T d₁))
    (hd₁ : TShape.HasType Δ (Shape.T d₁) TShape.type)
    (hwf₁ : Shape.WF (n := n₁+1) Δ (.forallE (A.subst σ) (B.subst σ.lift) d₁ g₁))
    (hlab₁ : ∀ e ∈ g₁, ∃ w, Δ ⊢ e.ty ≡ A.subst σ : .sort w)
    (hdom₁ : ∀ e ∈ g₁, TShape.HasType Δ (Shape.T e.inp) (Shape.T d₁))
    (hbody₁ : ∀ e ∈ g₁,
      Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push (Shape.T e.inp)) (Shape.T e.out))
    (hA₂ : Interp Δ Γ A σ ρ (Shape.T d₂))
    (hd₂ : TShape.HasType Δ (Shape.T d₂) TShape.type)
    (hwf₂ : Shape.WF (n := n₂+1) Δ (.forallE (A.subst σ) (B.subst σ.lift) d₂ g₂))
    (hlab₂ : ∀ e ∈ g₂, ∃ w, Δ ⊢ e.ty ≡ A.subst σ : .sort w)
    (hdom₂ : ∀ e ∈ g₂, TShape.HasType Δ (Shape.T e.inp) (Shape.T d₂))
    (hbody₂ : ∀ e ∈ g₂,
      Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push (Shape.T e.inp)) (Shape.T e.out)) :
    ∃ s, TShape.WF Δ s ∧ Interp Δ Γ (.forallE A B) σ ρ s ∧
      TShape.LE Δ (Shape.T (n := n₁+1) (.forallE (A.subst σ) (B.subst σ.lift) d₁ g₁)) s ∧
      TShape.LE Δ (Shape.T (n := n₂+1) (.forallE (A.subst σ) (B.subst σ.lift) d₂ g₂)) s := by
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hAty⟩
  have k₁ : n₁ ≤ max n₁ n₂ := Nat.le_max_left ..
  have k₂ : n₂ ≤ max n₁ n₂ := Nat.le_max_right ..
  -- the joined domain, from `A`'s own directedness
  have ⟨hcd, hdj⟩ := (ihAdir hΔ W hwρ).join hΔ hA₁ hA₂
  have hcd' : Shape.Compat Δ (d₁.lift (max n₁ n₂)) (d₂.lift (max n₁ n₂)) :=
    (TShape.Compat.def k₁ k₂).1 hcd
  have hwd₁ : Shape.WF Δ d₁ := hwf₁.2.2.1
  have hwd₂ : Shape.WF Δ d₂ := hwf₂.2.2.1
  have hwdj : Shape.WF Δ ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂))) :=
    Shape.WF.join hΔ hcd' ((Shape.lift_wf k₁).2 hwd₁) ((Shape.lift_wf k₂).2 hwd₂)
  have hdj' : Interp Δ Γ A σ ρ
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) := hdj
  -- and its typing, from the two domains' own, joined at a *sort*
  have hdjty : TShape.HasType Δ
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) TShape.type :=
    TShape.HasType.join_sort hΔ rfl (hd₁.lift_subject hΔ k₁) (hd₂.lift_subject hΔ k₂) hcd'
  have hled₁ : TShape.LE Δ (Shape.T d₁)
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) :=
    (TShape.LE.def hΔ k₁ (Nat.le_refl _)).2 <| by
      rw [Shape.lift_self]
      exact (Shape.le_join hΔ ((Shape.lift_wf k₁).2 hwd₁)
        ((Shape.lift_wf k₂).2 hwd₂) hcd').1
  have hled₂ : TShape.LE Δ (Shape.T d₂)
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) :=
    (TShape.LE.def hΔ k₂ (Nat.le_refl _)).2 <| by
      rw [Shape.lift_self]
      exact (Shape.le_join hΔ ((Shape.lift_wf k₁).2 hwd₁)
        ((Shape.lift_wf k₂).2 hwd₂) hcd').2
  -- each graph entry's input, typed at the joined domain
  have hdomj₁ : ∀ e ∈ g₁, TShape.HasType Δ (Shape.T e.inp)
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) := fun e he =>
    TShape.HasType.mono_r hΔ (hdom₁ e he) _ hled₁ hdjty
  have hdomj₂ : ∀ e ∈ g₂, TShape.HasType Δ (Shape.T e.inp)
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) := fun e he =>
    TShape.HasType.mono_r hΔ (hdom₂ e he) _ hled₂ hdjty
  -- **the cross pairs**
  have hcross : ShapeFun.Compat Shape.Compat Δ
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁)
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂) := by
    intro e he e' he' Θ τ hΘ Wτ hlab hin
    obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
    obtain ⟨b, hb, rfl⟩ := ShapeFun.mem_lift.1 he'
    have hwa := hwf₁.2.2.2.1 a ha
    have hwb := hwf₂.2.2.2.1 b hb
    have Wc : Ctx.SubstEq Θ (σ.comp τ) (σ.comp τ) Γ := Ctx.SubstEq.comp hΘ Wτ W
    have hwρτ : Valuation.WF Θ (ρ.subst τ) := Valuation.WF.subst hΘ Wτ hwρ
    -- the two inputs, read at the common level, and their join
    rw [← Shape.lift_subst, ← Shape.lift_subst] at hin
    have hwx₁ : TShape.WF Θ (Shape.T ((a.inp.subst τ).lift (max n₁ n₂))) :=
      (Shape.lift_wf k₁).2 (Shape.WF.subst hΘ Wτ hwa.2.2.1)
    have hwx₂ : TShape.WF Θ (Shape.T ((b.inp.subst τ).lift (max n₁ n₂))) :=
      (Shape.lift_wf k₂).2 (Shape.WF.subst hΘ Wτ hwb.2.2.1)
    have hcx : TShape.Compat Θ (Shape.T ((a.inp.subst τ).lift (max n₁ n₂)))
        (Shape.T ((b.inp.subst τ).lift (max n₁ n₂))) := TShape.Compat.T.2 hin
    have hwxj := TShape.WF.join hΘ hcx hwx₁ hwx₂
    have ⟨hjx₁, hjx₂⟩ := TShape.le_join hΘ hwx₁ hwx₂ hcx
    -- the label equation, which is what puts the two bodies at one stage
    obtain ⟨_, hla⟩ := hlab₁ a ha
    have hlaτ := hla.subst hΘ Wτ
    have heq : Θ ⊢ b.tm.subst τ ≡ a.tm.subst τ : (A.subst σ).subst τ :=
      hlaτ.defeqDF hlab.2.symm
    rw [subst_subst] at heq
    have Wcons : Ctx.SubstEq Θ ((σ.comp τ).cons (b.tm.subst τ))
        ((σ.comp τ).cons (a.tm.subst τ)) (A :: Γ) := .cons Wc hAty heq
    have Wdiag : Ctx.SubstEq Θ ((σ.comp τ).cons (a.tm.subst τ))
        ((σ.comp τ).cons (a.tm.subst τ)) (A :: Γ) := .cons Wc hAty heq.hasType.2
    -- the two bodies, at that one stage and above that one slot
    have hb₁ := (hbody₁ a ha).subst hΘ Wτ
    have hb₂0 := (hbody₂ b hb).subst hΘ Wτ
    rw [Subst.cons_comp, Valuation.subst_push] at hb₁ hb₂0
    have hb₂ := IsDefEq.stage hΓA hB hΘ Wcons hb₂0
    have hB₁ := Interp.mono_val hΘ (Valuation.LE.push.2
      ⟨Valuation.LE.refl hwρτ,
        TShape.LE.trans hΘ (TShape.LE.le_lift hΘ (m := Shape.T (a.inp.subst τ)) k₁
          (Shape.WF.subst hΘ Wτ hwa.2.2.1)) hjx₁⟩) hb₁
    have hB₂ := Interp.mono_val hΘ (Valuation.LE.push.2
      ⟨Valuation.LE.refl hwρτ,
        TShape.LE.trans hΘ (TShape.LE.le_lift hΘ (m := Shape.T (b.inp.subst τ)) k₂
          (Shape.WF.subst hΘ Wτ hwb.2.2.1)) hjx₂⟩) hb₂
    obtain ⟨_, _, _, hs₁, hs₂⟩ :=
      ihBdir hΘ Wdiag (Valuation.WF.push hwρτ hwxj) hB₁ hB₂
    rw [← Shape.lift_subst, ← Shape.lift_subst]
    exact (TShape.Compat.def k₁ k₂).1
      (TShape.Compat.of_common_upper hΘ (by assumption) hs₁ hs₂)
  -- the two Π-shapes are compatible, so their join is well formed
  obtain ⟨_, hAσ⟩ := hwf₁.1
  obtain ⟨_, hBσ⟩ := hwf₁.2.1
  have hcS : Shape.Compat (n := max n₁ n₂ + 1) Δ
      (.forallE (A.subst σ) (B.subst σ.lift) (d₁.lift (max n₁ n₂))
        (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁))
      (.forallE (A.subst σ) (B.subst σ.lift) (d₂.lift (max n₁ n₂))
        (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂)) :=
    ⟨PiLabelEq.refl hAσ hBσ, hcd', hcross⟩
  have hwS₁ : Shape.WF Δ (Shape.lift (n := n₁+1) (max n₁ n₂ + 1)
      (.forallE (A.subst σ) (B.subst σ.lift) d₁ g₁)) :=
    (Shape.lift_wf (Nat.succ_le_succ k₁)).2 hwf₁
  have hwS₂ : Shape.WF Δ (Shape.lift (n := n₂+1) (max n₁ n₂ + 1)
      (.forallE (A.subst σ) (B.subst σ.lift) d₂ g₂)) :=
    (Shape.lift_wf (Nat.succ_le_succ k₂)).2 hwf₂
  have hwSJ : Shape.WF (n := max n₁ n₂ + 1) Δ
      (.forallE (A.subst σ) (B.subst σ.lift)
        ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))
        (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁ ++
          ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂)) :=
    Shape.WF.join hΔ hcS hwS₁ hwS₂
  refine ⟨Shape.T (n := max n₁ n₂ + 1) (.forallE (A.subst σ) (B.subst σ.lift)
      ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁ ++ ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂)),
    hwSJ, .forallE hdj' hdjty hwSJ ?_ ?_ ?_ hwSJ (TShape.LE.refl hwSJ),
    (TShape.LE.def hΔ (Nat.succ_le_succ k₁) (Nat.le_refl _)).2 ?_,
    (TShape.LE.def hΔ (Nat.succ_le_succ k₂) (Nat.le_refl _)).2 ?_⟩
  · -- labels
    intro e he
    match List.mem_append.1 he with
    | .inl he => obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he; exact hlab₁ a ha
    | .inr he => obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he; exact hlab₂ a ha
  · -- inputs typed at the joined domain
    intro e he
    match List.mem_append.1 he with
    | .inl he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact TShape.HasType.mono_l hΔ (hdomj₁ a ha)
        (TShape.LE.lift_le hΔ (m := Shape.T a.inp) k₁ (hwf₁.2.2.2.1 a ha).2.2.1)
    | .inr he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact TShape.HasType.mono_l hΔ (hdomj₂ a ha)
        (TShape.LE.lift_le hΔ (m := Shape.T a.inp) k₂ (hwf₂.2.2.2.1 a ha).2.2.1)
  · -- bodies
    intro e he
    match List.mem_append.1 he with
    | .inl he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact Interp.lift hΔ k₁ (Interp.mono_val hΔ (Valuation.LE.push.2
        ⟨Valuation.LE.refl hwρ,
          TShape.LE.le_lift hΔ (m := Shape.T a.inp) k₁ (hwf₁.2.2.2.1 a ha).2.2.1⟩)
        (hbody₁ a ha))
    | .inr he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact Interp.lift hΔ k₂ (Interp.mono_val hΔ (Valuation.LE.push.2
        ⟨Valuation.LE.refl hwρ,
          TShape.LE.le_lift hΔ (m := Shape.T a.inp) k₂ (hwf₂.2.2.2.1 a ha).2.2.1⟩)
        (hbody₂ a ha))
  · rw [Shape.lift_self]; exact (Shape.le_join hΔ hwS₁ hwS₂ hcS).1
  · rw [Shape.lift_self]; exact (Shape.le_join hΔ hwS₁ hwS₂ hcS).2

/-- Directedness of a Π-type's interpretation: the `forallEDF` case of
`IsDefEq.dir`. -/
theorem sound_forallE_dir {Γ : List Term} {A B : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B ≡ B : .sort v)
    (ihAdir : SoundDir Γ A) (ihBdir : SoundDir (A :: Γ) B) :
    SoundDir Γ (.forallE A B) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | forallE hA₁ hd₁ hwf₁ hlab₁ hdom₁ hbody₁ hw₁ hle₁ =>
    cases h₂ with
    | bot =>
      refine ⟨_, ?_, ?_, hle₁, TShape.bot_le' rfl⟩
      · exact hwf₁
      · exact .forallE hA₁ hd₁ hwf₁ hlab₁ hdom₁ hbody₁ hwf₁ (TShape.LE.refl hwf₁)
    | forallE hA₂ hd₂ hwf₂ hlab₂ hdom₂ hbody₂ hw₂ hle₂ =>
      obtain ⟨s, hws, hs, hs₁, hs₂⟩ := sound_forallE_ub hΓ hAty hB ihAdir ihBdir
        hΔ W hwρ hA₁ hd₁ hwf₁ hlab₁ hdom₁ hbody₁ hA₂ hd₂ hwf₂ hlab₂ hdom₂ hbody₂
      exact ⟨s, hws, hs, TShape.LE.trans hΔ hle₁ hs₁, TShape.LE.trans hΔ hle₂ hs₂⟩

/-- The common upper bound of two Σ-shapes: same labels (both come from
the same term at the same stage), domains joined by `A`'s directedness,
graphs appended.

All the content is the appended graph's coherence, and there the cross
pairs; see the section comment.  The domain of the joined shape is a type
because each domain is — the `Interp.sigma` premise added for exactly
this — and `HasType.join` at a *sort* is available. -/
theorem sound_sigma_ub {Γ : List Term} {A B : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B ≡ B : .sort v)
    (ihAdir : SoundDir Γ A) (ihBdir : SoundDir (A :: Γ) B)
    {Δ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hwρ : Valuation.WF Δ ρ)
    {n₁ n₂} {d₁ : Shape n₁} {g₁ : ShapeFun n₁} {d₂ : Shape n₂} {g₂ : ShapeFun n₂}
    (hA₁ : Interp Δ Γ A σ ρ (Shape.T d₁))
    (hd₁ : TShape.HasType Δ (Shape.T d₁) TShape.type)
    (hwf₁ : Shape.WF (n := n₁+1) Δ (.sigma (A.subst σ) (B.subst σ.lift) d₁ g₁))
    (hlab₁ : ∀ e ∈ g₁, ∃ w, Δ ⊢ e.ty ≡ A.subst σ : .sort w)
    (hdom₁ : ∀ e ∈ g₁, TShape.HasType Δ (Shape.T e.inp) (Shape.T d₁))
    (hbody₁ : ∀ e ∈ g₁,
      Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push (Shape.T e.inp)) (Shape.T e.out))
    (hA₂ : Interp Δ Γ A σ ρ (Shape.T d₂))
    (hd₂ : TShape.HasType Δ (Shape.T d₂) TShape.type)
    (hwf₂ : Shape.WF (n := n₂+1) Δ (.sigma (A.subst σ) (B.subst σ.lift) d₂ g₂))
    (hlab₂ : ∀ e ∈ g₂, ∃ w, Δ ⊢ e.ty ≡ A.subst σ : .sort w)
    (hdom₂ : ∀ e ∈ g₂, TShape.HasType Δ (Shape.T e.inp) (Shape.T d₂))
    (hbody₂ : ∀ e ∈ g₂,
      Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push (Shape.T e.inp)) (Shape.T e.out)) :
    ∃ s, TShape.WF Δ s ∧ Interp Δ Γ (.sigma A B) σ ρ s ∧
      TShape.LE Δ (Shape.T (n := n₁+1) (.sigma (A.subst σ) (B.subst σ.lift) d₁ g₁)) s ∧
      TShape.LE Δ (Shape.T (n := n₂+1) (.sigma (A.subst σ) (B.subst σ.lift) d₂ g₂)) s := by
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hAty⟩
  have k₁ : n₁ ≤ max n₁ n₂ := Nat.le_max_left ..
  have k₂ : n₂ ≤ max n₁ n₂ := Nat.le_max_right ..
  -- the joined domain, from `A`'s own directedness
  have ⟨hcd, hdj⟩ := (ihAdir hΔ W hwρ).join hΔ hA₁ hA₂
  have hcd' : Shape.Compat Δ (d₁.lift (max n₁ n₂)) (d₂.lift (max n₁ n₂)) :=
    (TShape.Compat.def k₁ k₂).1 hcd
  have hwd₁ : Shape.WF Δ d₁ := hwf₁.2.2.1
  have hwd₂ : Shape.WF Δ d₂ := hwf₂.2.2.1
  have hwdj : Shape.WF Δ ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂))) :=
    Shape.WF.join hΔ hcd' ((Shape.lift_wf k₁).2 hwd₁) ((Shape.lift_wf k₂).2 hwd₂)
  have hdj' : Interp Δ Γ A σ ρ
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) := hdj
  -- and its typing, from the two domains' own, joined at a *sort*
  have hdjty : TShape.HasType Δ
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) TShape.type :=
    TShape.HasType.join_sort hΔ rfl (hd₁.lift_subject hΔ k₁) (hd₂.lift_subject hΔ k₂) hcd'
  have hled₁ : TShape.LE Δ (Shape.T d₁)
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) :=
    (TShape.LE.def hΔ k₁ (Nat.le_refl _)).2 <| by
      rw [Shape.lift_self]
      exact (Shape.le_join hΔ ((Shape.lift_wf k₁).2 hwd₁)
        ((Shape.lift_wf k₂).2 hwd₂) hcd').1
  have hled₂ : TShape.LE Δ (Shape.T d₂)
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) :=
    (TShape.LE.def hΔ k₂ (Nat.le_refl _)).2 <| by
      rw [Shape.lift_self]
      exact (Shape.le_join hΔ ((Shape.lift_wf k₁).2 hwd₁)
        ((Shape.lift_wf k₂).2 hwd₂) hcd').2
  -- each graph entry's input, typed at the joined domain
  have hdomj₁ : ∀ e ∈ g₁, TShape.HasType Δ (Shape.T e.inp)
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) := fun e he =>
    TShape.HasType.mono_r hΔ (hdom₁ e he) _ hled₁ hdjty
  have hdomj₂ : ∀ e ∈ g₂, TShape.HasType Δ (Shape.T e.inp)
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) := fun e he =>
    TShape.HasType.mono_r hΔ (hdom₂ e he) _ hled₂ hdjty
  -- **the cross pairs**
  have hcross : ShapeFun.Compat Shape.Compat Δ
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁)
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂) := by
    intro e he e' he' Θ τ hΘ Wτ hlab hin
    obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
    obtain ⟨b, hb, rfl⟩ := ShapeFun.mem_lift.1 he'
    have hwa := hwf₁.2.2.2.1 a ha
    have hwb := hwf₂.2.2.2.1 b hb
    have Wc : Ctx.SubstEq Θ (σ.comp τ) (σ.comp τ) Γ := Ctx.SubstEq.comp hΘ Wτ W
    have hwρτ : Valuation.WF Θ (ρ.subst τ) := Valuation.WF.subst hΘ Wτ hwρ
    -- the two inputs, read at the common level, and their join
    rw [← Shape.lift_subst, ← Shape.lift_subst] at hin
    have hwx₁ : TShape.WF Θ (Shape.T ((a.inp.subst τ).lift (max n₁ n₂))) :=
      (Shape.lift_wf k₁).2 (Shape.WF.subst hΘ Wτ hwa.2.2.1)
    have hwx₂ : TShape.WF Θ (Shape.T ((b.inp.subst τ).lift (max n₁ n₂))) :=
      (Shape.lift_wf k₂).2 (Shape.WF.subst hΘ Wτ hwb.2.2.1)
    have hcx : TShape.Compat Θ (Shape.T ((a.inp.subst τ).lift (max n₁ n₂)))
        (Shape.T ((b.inp.subst τ).lift (max n₁ n₂))) := TShape.Compat.T.2 hin
    have hwxj := TShape.WF.join hΘ hcx hwx₁ hwx₂
    have ⟨hjx₁, hjx₂⟩ := TShape.le_join hΘ hwx₁ hwx₂ hcx
    -- the label equation, which is what puts the two bodies at one stage
    obtain ⟨_, hla⟩ := hlab₁ a ha
    have hlaτ := hla.subst hΘ Wτ
    have heq : Θ ⊢ b.tm.subst τ ≡ a.tm.subst τ : (A.subst σ).subst τ :=
      hlaτ.defeqDF hlab.2.symm
    rw [subst_subst] at heq
    have Wcons : Ctx.SubstEq Θ ((σ.comp τ).cons (b.tm.subst τ))
        ((σ.comp τ).cons (a.tm.subst τ)) (A :: Γ) := .cons Wc hAty heq
    have Wdiag : Ctx.SubstEq Θ ((σ.comp τ).cons (a.tm.subst τ))
        ((σ.comp τ).cons (a.tm.subst τ)) (A :: Γ) := .cons Wc hAty heq.hasType.2
    -- the two bodies, at that one stage and above that one slot
    have hb₁ := (hbody₁ a ha).subst hΘ Wτ
    have hb₂0 := (hbody₂ b hb).subst hΘ Wτ
    rw [Subst.cons_comp, Valuation.subst_push] at hb₁ hb₂0
    have hb₂ := IsDefEq.stage hΓA hB hΘ Wcons hb₂0
    have hB₁ := Interp.mono_val hΘ (Valuation.LE.push.2
      ⟨Valuation.LE.refl hwρτ,
        TShape.LE.trans hΘ (TShape.LE.le_lift hΘ (m := Shape.T (a.inp.subst τ)) k₁
          (Shape.WF.subst hΘ Wτ hwa.2.2.1)) hjx₁⟩) hb₁
    have hB₂ := Interp.mono_val hΘ (Valuation.LE.push.2
      ⟨Valuation.LE.refl hwρτ,
        TShape.LE.trans hΘ (TShape.LE.le_lift hΘ (m := Shape.T (b.inp.subst τ)) k₂
          (Shape.WF.subst hΘ Wτ hwb.2.2.1)) hjx₂⟩) hb₂
    obtain ⟨_, _, _, hs₁, hs₂⟩ :=
      ihBdir hΘ Wdiag (Valuation.WF.push hwρτ hwxj) hB₁ hB₂
    rw [← Shape.lift_subst, ← Shape.lift_subst]
    exact (TShape.Compat.def k₁ k₂).1
      (TShape.Compat.of_common_upper hΘ (by assumption) hs₁ hs₂)
  -- the two Σ-shapes are compatible, so their join is well formed
  obtain ⟨_, hAσ⟩ := hwf₁.1
  obtain ⟨_, hBσ⟩ := hwf₁.2.1
  have hcS : Shape.Compat (n := max n₁ n₂ + 1) Δ
      (.sigma (A.subst σ) (B.subst σ.lift) (d₁.lift (max n₁ n₂))
        (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁))
      (.sigma (A.subst σ) (B.subst σ.lift) (d₂.lift (max n₁ n₂))
        (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂)) :=
    ⟨PiLabelEq.refl hAσ hBσ, hcd', hcross⟩
  have hwS₁ : Shape.WF Δ (Shape.lift (n := n₁+1) (max n₁ n₂ + 1)
      (.sigma (A.subst σ) (B.subst σ.lift) d₁ g₁)) :=
    (Shape.lift_wf (Nat.succ_le_succ k₁)).2 hwf₁
  have hwS₂ : Shape.WF Δ (Shape.lift (n := n₂+1) (max n₁ n₂ + 1)
      (.sigma (A.subst σ) (B.subst σ.lift) d₂ g₂)) :=
    (Shape.lift_wf (Nat.succ_le_succ k₂)).2 hwf₂
  have hwSJ : Shape.WF (n := max n₁ n₂ + 1) Δ
      (.sigma (A.subst σ) (B.subst σ.lift)
        ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))
        (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁ ++
          ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂)) :=
    Shape.WF.join hΔ hcS hwS₁ hwS₂
  refine ⟨Shape.T (n := max n₁ n₂ + 1) (.sigma (A.subst σ) (B.subst σ.lift)
      ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁ ++ ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂)),
    hwSJ, .sigma hdj' hdjty hwSJ ?_ ?_ ?_ hwSJ (TShape.LE.refl hwSJ),
    (TShape.LE.def hΔ (Nat.succ_le_succ k₁) (Nat.le_refl _)).2 ?_,
    (TShape.LE.def hΔ (Nat.succ_le_succ k₂) (Nat.le_refl _)).2 ?_⟩
  · -- labels
    intro e he
    match List.mem_append.1 he with
    | .inl he => obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he; exact hlab₁ a ha
    | .inr he => obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he; exact hlab₂ a ha
  · -- inputs typed at the joined domain
    intro e he
    match List.mem_append.1 he with
    | .inl he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact TShape.HasType.mono_l hΔ (hdomj₁ a ha)
        (TShape.LE.lift_le hΔ (m := Shape.T a.inp) k₁ (hwf₁.2.2.2.1 a ha).2.2.1)
    | .inr he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact TShape.HasType.mono_l hΔ (hdomj₂ a ha)
        (TShape.LE.lift_le hΔ (m := Shape.T a.inp) k₂ (hwf₂.2.2.2.1 a ha).2.2.1)
  · -- bodies
    intro e he
    match List.mem_append.1 he with
    | .inl he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact Interp.lift hΔ k₁ (Interp.mono_val hΔ (Valuation.LE.push.2
        ⟨Valuation.LE.refl hwρ,
          TShape.LE.le_lift hΔ (m := Shape.T a.inp) k₁ (hwf₁.2.2.2.1 a ha).2.2.1⟩)
        (hbody₁ a ha))
    | .inr he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact Interp.lift hΔ k₂ (Interp.mono_val hΔ (Valuation.LE.push.2
        ⟨Valuation.LE.refl hwρ,
          TShape.LE.le_lift hΔ (m := Shape.T a.inp) k₂ (hwf₂.2.2.2.1 a ha).2.2.1⟩)
        (hbody₂ a ha))
  · rw [Shape.lift_self]; exact (Shape.le_join hΔ hwS₁ hwS₂ hcS).1
  · rw [Shape.lift_self]; exact (Shape.le_join hΔ hwS₁ hwS₂ hcS).2

/-- Directedness of a Σ-type's interpretation: the `sigmaDF` case of
`IsDefEq.dir`. -/
theorem sound_sigma_dir {Γ : List Term} {A B : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B ≡ B : .sort v)
    (ihAdir : SoundDir Γ A) (ihBdir : SoundDir (A :: Γ) B) :
    SoundDir Γ (.sigma A B) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | sigma hA₁ hd₁ hwf₁ hlab₁ hdom₁ hbody₁ hw₁ hle₁ =>
    cases h₂ with
    | bot =>
      refine ⟨_, ?_, ?_, hle₁, TShape.bot_le' rfl⟩
      · exact hwf₁
      · exact .sigma hA₁ hd₁ hwf₁ hlab₁ hdom₁ hbody₁ hwf₁ (TShape.LE.refl hwf₁)
    | sigma hA₂ hd₂ hwf₂ hlab₂ hdom₂ hbody₂ hw₂ hle₂ =>
      obtain ⟨s, hws, hs, hs₁, hs₂⟩ := sound_sigma_ub hΓ hAty hB ihAdir ihBdir
        hΔ W hwρ hA₁ hd₁ hwf₁ hlab₁ hdom₁ hbody₁ hA₂ hd₂ hwf₂ hlab₂ hdom₂ hbody₂
      exact ⟨s, hws, hs, TShape.LE.trans hΔ hle₁ hs₁, TShape.LE.trans hΔ hle₂ hs₂⟩

/-! ## λ

The λ analogue of `sound_forallE_ub`, with the domain *label* in place of
the Π label and the body in place of the codomain.  The one structural
difference is that the λ-shape's domain shape is not part of the shape:
`Interp.lam`'s `d` is a `TShape` beside it, so the join of the two `d`s
needs no level bookkeeping. -/

/-- The common upper bound of two λ-shapes: one label (both come from the
same term at the same stage), graphs appended. -/
theorem sound_lam_ub {Γ : List Term} {A B b : Term} {u : Bool}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hb : A :: Γ ⊢ b : B)
    (ihAdir : SoundDir Γ A) (ihbdir : SoundDir (A :: Γ) b)
    {Δ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hwρ : Valuation.WF Δ ρ)
    {n₁ n₂} {d₁ d₂ : TShape} {g₁ : ShapeFun n₁} {g₂ : ShapeFun n₂}
    (hA₁ : Interp Δ Γ A σ ρ d₁)
    (hd₁ : TShape.HasType Δ d₁ TShape.type)
    (hwf₁ : Shape.WF (n := n₁+1) Δ (.lam (A.subst σ) g₁))
    (hdom₁ : ∀ e ∈ g₁, TShape.HasType Δ e.inp.T d₁)
    (hbody₁ : ∀ e ∈ g₁, Interp Δ (A :: Γ) b (σ.cons e.tm) (ρ.push e.inp.T) e.out.T)
    (hA₂ : Interp Δ Γ A σ ρ d₂)
    (hd₂ : TShape.HasType Δ d₂ TShape.type)
    (hwf₂ : Shape.WF (n := n₂+1) Δ (.lam (A.subst σ) g₂))
    (hdom₂ : ∀ e ∈ g₂, TShape.HasType Δ e.inp.T d₂)
    (hbody₂ : ∀ e ∈ g₂, Interp Δ (A :: Γ) b (σ.cons e.tm) (ρ.push e.inp.T) e.out.T) :
    ∃ s, TShape.WF Δ s ∧ Interp Δ Γ (.lam A b) σ ρ s ∧
      TShape.LE Δ (Shape.T (n := n₁+1) (.lam (A.subst σ) g₁)) s ∧
      TShape.LE Δ (Shape.T (n := n₂+1) (.lam (A.subst σ) g₂)) s := by
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hAty⟩
  have k₁ : n₁ ≤ max n₁ n₂ := Nat.le_max_left ..
  have k₂ : n₂ ≤ max n₁ n₂ := Nat.le_max_right ..
  -- the joined domain shape, from `A`'s own directedness
  have ⟨hcd, hdj⟩ := (ihAdir hΔ W hwρ).join hΔ hA₁ hA₂
  have hdjty : TShape.HasType Δ (d₁.join d₂) TShape.type :=
    TShape.HasType.join_sort' hΔ rfl hd₁ hd₂ hcd
  have ⟨hled₁, hled₂⟩ := TShape.le_join hΔ hA₁.wf hA₂.wf hcd
  have hdomj₁ : ∀ e ∈ g₁, TShape.HasType Δ e.inp.T (d₁.join d₂) := fun e he =>
    TShape.HasType.mono_r hΔ (hdom₁ e he) _ hled₁ hdjty
  have hdomj₂ : ∀ e ∈ g₂, TShape.HasType Δ e.inp.T (d₁.join d₂) := fun e he =>
    TShape.HasType.mono_r hΔ (hdom₂ e he) _ hled₂ hdjty
  -- **the cross pairs**: the body at the join of two entries' inputs, a
  -- valuation that is well formed but not admissible
  have hcross : ShapeFun.Compat Shape.Compat Δ
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁)
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂) := by
    intro e he e' he' Θ τ hΘ Wτ hlab hin
    obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
    obtain ⟨c, hc, rfl⟩ := ShapeFun.mem_lift.1 he'
    have hwa := hwf₁.2.2.1.1 a ha
    have hwc := hwf₂.2.2.1.1 c hc
    have Wc : Ctx.SubstEq Θ (σ.comp τ) (σ.comp τ) Γ := Ctx.SubstEq.comp hΘ Wτ W
    have hwρτ : Valuation.WF Θ (ρ.subst τ) := Valuation.WF.subst hΘ Wτ hwρ
    rw [← Shape.lift_subst, ← Shape.lift_subst] at hin
    have hwx₁ : TShape.WF Θ (Shape.T ((a.inp.subst τ).lift (max n₁ n₂))) :=
      (Shape.lift_wf k₁).2 (Shape.WF.subst hΘ Wτ hwa.2.2.1)
    have hwx₂ : TShape.WF Θ (Shape.T ((c.inp.subst τ).lift (max n₁ n₂))) :=
      (Shape.lift_wf k₂).2 (Shape.WF.subst hΘ Wτ hwc.2.2.1)
    have hcx : TShape.Compat Θ (Shape.T ((a.inp.subst τ).lift (max n₁ n₂)))
        (Shape.T ((c.inp.subst τ).lift (max n₁ n₂))) := TShape.Compat.T.2 hin
    have hwxj := TShape.WF.join hΘ hcx hwx₁ hwx₂
    have ⟨hjx₁, hjx₂⟩ := TShape.le_join hΘ hwx₁ hwx₂ hcx
    -- the label equation, which puts the two bodies at one stage.  The
    -- entry's type is the domain label, by `Shape.WF` — this is what the
    -- λ-shape's label buys, and it holds at this non-admissible stage
    obtain ⟨_, hla⟩ := hwf₁.2.2.2 a ha
    have hlaτ := hla.subst hΘ Wτ
    have heq : Θ ⊢ c.tm.subst τ ≡ a.tm.subst τ : (A.subst σ).subst τ :=
      hlaτ.defeqDF hlab.2.symm
    rw [subst_subst] at heq
    have Wcons : Ctx.SubstEq Θ ((σ.comp τ).cons (c.tm.subst τ))
        ((σ.comp τ).cons (a.tm.subst τ)) (A :: Γ) := .cons Wc hAty heq
    have Wdiag : Ctx.SubstEq Θ ((σ.comp τ).cons (a.tm.subst τ))
        ((σ.comp τ).cons (a.tm.subst τ)) (A :: Γ) := .cons Wc hAty heq.hasType.2
    have hb₁ := (hbody₁ a ha).subst hΘ Wτ
    have hb₂0 := (hbody₂ c hc).subst hΘ Wτ
    rw [Subst.cons_comp, Valuation.subst_push] at hb₁ hb₂0
    have hb₂ := IsDefEq.stage hΓA hb hΘ Wcons hb₂0
    have hB₁ := Interp.mono_val hΘ (Valuation.LE.push.2
      ⟨Valuation.LE.refl hwρτ,
        TShape.LE.trans hΘ (TShape.LE.le_lift hΘ (m := Shape.T (a.inp.subst τ)) k₁
          (Shape.WF.subst hΘ Wτ hwa.2.2.1)) hjx₁⟩) hb₁
    have hB₂ := Interp.mono_val hΘ (Valuation.LE.push.2
      ⟨Valuation.LE.refl hwρτ,
        TShape.LE.trans hΘ (TShape.LE.le_lift hΘ (m := Shape.T (c.inp.subst τ)) k₂
          (Shape.WF.subst hΘ Wτ hwc.2.2.1)) hjx₂⟩) hb₂
    obtain ⟨_, _, _, hs₁, hs₂⟩ :=
      ihbdir hΘ Wdiag (Valuation.WF.push hwρτ hwxj) hB₁ hB₂
    rw [← Shape.lift_subst, ← Shape.lift_subst]
    exact (TShape.Compat.def k₁ k₂).1
      (TShape.Compat.of_common_upper hΘ (by assumption) hs₁ hs₂)
  -- the two λ-shapes are compatible, so their join is well formed
  have hcS : Shape.Compat (n := max n₁ n₂ + 1) Δ
      (.lam (A.subst σ) (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁))
      (.lam (A.subst σ) (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂)) :=
    ⟨hwf₁.dom, hcross⟩
  have hwS₁ : Shape.WF Δ (Shape.lift (n := n₁+1) (max n₁ n₂ + 1) (.lam (A.subst σ) g₁)) :=
    (Shape.lift_wf (Nat.succ_le_succ k₁)).2 hwf₁
  have hwS₂ : Shape.WF Δ (Shape.lift (n := n₂+1) (max n₁ n₂ + 1) (.lam (A.subst σ) g₂)) :=
    (Shape.lift_wf (Nat.succ_le_succ k₂)).2 hwf₂
  have hwSJ : Shape.WF (n := max n₁ n₂ + 1) Δ
      (.lam (A.subst σ) (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁ ++
        ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂)) :=
    Shape.WF.join hΔ hcS hwS₁ hwS₂
  refine ⟨Shape.T (n := max n₁ n₂ + 1) (.lam (A.subst σ)
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁ ++ ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂)),
    hwSJ, .lam hdj hdjty hwSJ ?_ ?_ hwSJ (TShape.LE.refl hwSJ),
    (TShape.LE.def hΔ (Nat.succ_le_succ k₁) (Nat.le_refl _)).2 ?_,
    (TShape.LE.def hΔ (Nat.succ_le_succ k₂) (Nat.le_refl _)).2 ?_⟩
  · -- inputs typed at the joined domain
    intro e he
    match List.mem_append.1 he with
    | .inl he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact TShape.HasType.mono_l hΔ (hdomj₁ a ha)
        (TShape.LE.lift_le hΔ (m := Shape.T a.inp) k₁ (hwf₁.2.2.1.1 a ha).2.2.1)
    | .inr he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact TShape.HasType.mono_l hΔ (hdomj₂ a ha)
        (TShape.LE.lift_le hΔ (m := Shape.T a.inp) k₂ (hwf₂.2.2.1.1 a ha).2.2.1)
  · -- bodies
    intro e he
    match List.mem_append.1 he with
    | .inl he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact Interp.lift hΔ k₁ (Interp.mono_val hΔ (Valuation.LE.push.2
        ⟨Valuation.LE.refl hwρ,
          TShape.LE.le_lift hΔ (m := Shape.T a.inp) k₁ (hwf₁.2.2.1.1 a ha).2.2.1⟩)
        (hbody₁ a ha))
    | .inr he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact Interp.lift hΔ k₂ (Interp.mono_val hΔ (Valuation.LE.push.2
        ⟨Valuation.LE.refl hwρ,
          TShape.LE.le_lift hΔ (m := Shape.T a.inp) k₂ (hwf₂.2.2.1.1 a ha).2.2.1⟩)
        (hbody₂ a ha))
  · rw [Shape.lift_self]; exact (Shape.le_join hΔ hwS₁ hwS₂ hcS).1
  · rw [Shape.lift_self]; exact (Shape.le_join hΔ hwS₁ hwS₂ hcS).2

/-- Directedness of a λ: the `lamDF` case of `IsDefEq.dir`. -/
theorem sound_lam_dir {Γ : List Term} {A B b : Term} {u : Bool}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hb : A :: Γ ⊢ b : B)
    (ihAdir : SoundDir Γ A) (ihbdir : SoundDir (A :: Γ) b) :
    SoundDir Γ (.lam A b) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | lam hA₁ hd₁ hwf₁ hdom₁ hbody₁ hw₁ hle₁ =>
    cases h₂ with
    | bot =>
      refine ⟨_, ?_, ?_, hle₁, TShape.bot_le' rfl⟩
      · exact hwf₁
      · exact .lam hA₁ hd₁ hwf₁ hdom₁ hbody₁ hwf₁ (TShape.LE.refl hwf₁)
    | lam hA₂ hd₂ hwf₂ hdom₂ hbody₂ hw₂ hle₂ =>
      obtain ⟨s, hws, hs, hs₁, hs₂⟩ := sound_lam_ub hΓ hAty hb ihAdir ihbdir
        hΔ W hwρ hA₁ hd₁ hwf₁ hdom₁ hbody₁ hA₂ hd₂ hwf₂ hdom₂ hbody₂
      exact ⟨s, hws, hs, TShape.LE.trans hΔ hle₁ hs₁, TShape.LE.trans hΔ hle₂ hs₂⟩

/-! ### Choosing a code for every entry

The λ's own typing is built from the *bodies'* types: one code per entry
of the graph, each an approximant of `B` at that entry's slot.  The
soundness hypothesis delivers them one at a time (`∃ c, …`), so they have
to be collected into a list — and then brought to one level, since a
graph is a list at one level.  These two utilities are that, and nothing
about this model. -/

/-- The maximum of a list of levels, above a floor. -/
def levelMax {α : Type _} (f : α → Nat) (k : Nat) : List α → Nat
  | [] => k
  | e :: g => max (f e) (levelMax f k g)

theorem le_levelMax {α : Type _} {f : α → Nat} {k : Nat} :
    ∀ {g : List α}, k ≤ levelMax f k g
  | [] => Nat.le_refl _
  | _ :: g => Nat.le_trans (le_levelMax (g := g)) (Nat.le_max_right ..)

theorem mem_le_levelMax {α : Type _} {f : α → Nat} {k : Nat} :
    ∀ {g : List α} {e}, e ∈ g → f e ≤ levelMax f k g
  | _ :: g, e, he => by
    match List.mem_cons.1 he with
    | .inl h => exact h ▸ Nat.le_max_left ..
    | .inr h => exact Nat.le_trans (mem_le_levelMax (g := g) h) (Nat.le_max_right ..)

/-- **A graph of a family's values is coherent.**  Two entries whose
labels become definitionally equal at a later stage name one slot of the
family, their inputs join there, and the family's directedness puts both
values under one shape — the argument of `sound_lam_ub`'s cross pairs,
with the *codomain* in place of the body.  It is what makes the Π-shape
built below well formed. -/
theorem graph_coherent {Γ Δ : List Term} {A B : Term} {σ ρ} {u v : Bool}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v)
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hwρ : Valuation.WF Δ ρ)
    (ihBdir : SoundDir (A :: Γ) B) {k} {f : ShapeFun k}
    (hent : ∀ e ∈ f, Shape.WF Δ e.inp)
    (hlab : ∀ e ∈ f, TyEq Δ e.ty (A.subst σ))
    (hbody : ∀ e ∈ f, Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push e.inp.T) e.out.T) :
    ShapeFun.Compat Shape.Compat Δ f f := by
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hAty⟩
  intro e he e' he' Θ τ hΘ Wτ hlabq hin
  have Wc : Ctx.SubstEq Θ (σ.comp τ) (σ.comp τ) Γ := Ctx.SubstEq.comp hΘ Wτ W
  have hwρτ : Valuation.WF Θ (ρ.subst τ) := Valuation.WF.subst hΘ Wτ hwρ
  have hwx₁ : TShape.WF Θ (Shape.T (e.inp.subst τ)) := Shape.WF.subst hΘ Wτ (hent e he)
  have hwx₂ : TShape.WF Θ (Shape.T (e'.inp.subst τ)) := Shape.WF.subst hΘ Wτ (hent e' he')
  have hcx : TShape.Compat Θ (Shape.T (e.inp.subst τ)) (Shape.T (e'.inp.subst τ)) :=
    TShape.Compat.T.2 hin
  have hwxj := TShape.WF.join hΘ hcx hwx₁ hwx₂
  have ⟨hjx₁, hjx₂⟩ := TShape.le_join hΘ hwx₁ hwx₂ hcx
  -- the label equation puts the two bodies at one stage
  have hlaτ := (hlab e he).choose_spec.subst hΘ Wτ
  have heq : Θ ⊢ e'.tm.subst τ ≡ e.tm.subst τ : (A.subst σ).subst τ :=
    hlaτ.defeqDF hlabq.2.symm
  rw [subst_subst] at heq
  have Wcons : Ctx.SubstEq Θ ((σ.comp τ).cons (e'.tm.subst τ))
      ((σ.comp τ).cons (e.tm.subst τ)) (A :: Γ) := .cons Wc hAty heq
  have Wdiag : Ctx.SubstEq Θ ((σ.comp τ).cons (e.tm.subst τ))
      ((σ.comp τ).cons (e.tm.subst τ)) (A :: Γ) := .cons Wc hAty heq.hasType.2
  have hb₁ := (hbody e he).subst hΘ Wτ
  have hb₂0 := (hbody e' he').subst hΘ Wτ
  rw [Subst.cons_comp, Valuation.subst_push] at hb₁ hb₂0
  have hb₂ := IsDefEq.stage hΓA hB hΘ Wcons hb₂0
  obtain ⟨_, _, _, hs₁, hs₂⟩ := ihBdir hΘ Wdiag (Valuation.WF.push hwρτ hwxj)
    (Interp.mono_val hΘ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρτ, hjx₁⟩) hb₁)
    (Interp.mono_val hΘ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρτ, hjx₂⟩) hb₂)
  exact TShape.Compat.T.1 (TShape.Compat.of_common_upper hΘ (by assumption) hs₁ hs₂)

/-- **The type of a λ.**

Master's `sound_lam` merges two codomain graphs with `join'` at an
arbitrary type; here the Π-shape that types a λ-shape is *built from that
λ-shape*: one entry per entry of its graph, with the same label and
input, and with the body's own type as the output.  The codes come from
`SoundTy b B` one entry at a time, so they are collected
(`List.exists_pairs`) and lifted to one level (`levelMax`) — a graph is a
list at one level, and that is the only bookkeeping here.

The generator of `HasType.lam` is then the λ's own graph paired with
those codes: each entry covers itself, and its code is the Π-entry built
from it.  The one real obligation is the Π-shape's coherence, which is
`graph_coherent`, i.e. one call to the codomain's directedness. -/
theorem sound_lam_ty {Γ : List Term} {A B b : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v)
    (hlam : Γ ⊢ .lam A b : .forallE A B)
    (ihAty : SoundTy Γ A (.sort u)) (ihBty : SoundTy (A :: Γ) B (.sort v))
    (ihbty : SoundTy (A :: Γ) b B) (ihBdir : SoundDir (A :: Γ) B) :
    SoundTy Γ (.lam A b) (.forallE A B) := by
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hAty⟩
  refine ⟨hlam, ?_⟩
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  have hwρ := hAdm.wf
  cases hm with
  | bot => exact ⟨TShape.bot, .bot, .bot (.bot .sort)⟩
  | @lam _ _ _ _ n g d _ _ hA hd hwf hdom hbody hw hle =>
    -- every entry's stage is admissible: its label is typed at the domain
    have hstage : ∀ e ∈ g, Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A :: Γ) ∧
        Adm Δ Γ₀ (A :: Γ) (σ.cons e.tm) (ρ.push e.inp.T) := by
      intro e he
      have hwe := hwf.2.2.1.1 e he
      have hty := (hwf.2.2.2 e he).choose_spec
      exact ⟨.cons W hAty (hty.defeqDF hwe.2.1),
        .cons hAdm (fun _ hc => ihAty.isType hΔ W hAdm hc) hA hwe.2.2.1 (hdom e he)⟩
    -- a code for every entry, collected and brought to one level
    obtain ⟨g₀, hmap, hall⟩ := List.exists_pairs (β := TShape)
      (P := fun e c => Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push e.inp.T) c ∧
        TShape.HasType Δ e.out.T c)
      (fun e he => ihbty.approx hΔ (hstage e he).1 (hstage e he).2 (hbody e he))
    obtain ⟨k, hkn, hkd, hkc⟩ : ∃ k, n ≤ k ∧ d.1 ≤ k ∧ ∀ p ∈ g₀, (Prod.snd p : TShape).1 ≤ k :=
      ⟨levelMax (fun p => (Prod.snd p : TShape).1) (max n d.1) g₀,
        Nat.le_trans (Nat.le_max_left ..) le_levelMax,
        Nat.le_trans (Nat.le_max_right ..) le_levelMax,
        fun p hp => mem_le_levelMax (f := fun p => (Prod.snd p : TShape).1) hp⟩
    -- the codomain graph, one entry per entry of the λ's
    obtain ⟨f, hf⟩ : ∃ f : ShapeFun k, ∀ e, e ∈ f ↔ ∃ p ∈ g₀,
        e = ⟨p.1.ty, p.1.tm, p.1.inp.lift k, (Prod.snd p : TShape).2.lift k⟩ :=
      ⟨g₀.map fun p => ⟨p.1.ty, p.1.tm, p.1.inp.lift k, (Prod.snd p : TShape).2.lift k⟩,
        fun e => by simp [List.mem_map, eq_comm]⟩
    -- each pair's first component is an entry of `g`
    have hg₀g : ∀ p ∈ g₀, p.1 ∈ g := fun p hp => hmap ▸ List.mem_map.2 ⟨p, hp, rfl⟩
    have hpwf : ∀ p ∈ g₀, TShape.WF Δ (Prod.snd p : TShape) := fun p hp => (hall p hp).1.wf
    have hdty : TShape.HasType Δ (Shape.T (d.2.lift k)) TShape.type :=
      hd.lift_subject hΔ hkd
    have hdle : TShape.LE Δ d (Shape.T (d.2.lift k)) :=
      TShape.LE.le_lift hΔ (m := d) hkd hd.wf.1
    -- the Π-shape's premises, entry by entry
    have hfent : ∀ e ∈ f, (∃ u, Δ ⊢ e.ty : .sort u) ∧ Δ ⊢ e.tm : e.ty ∧
        Shape.WF Δ e.inp ∧ Shape.WF Δ e.out := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := (hf e).1 he
      have hwe := hwf.2.2.1.1 p.1 (hg₀g p hp)
      exact ⟨hwe.1, hwe.2.1, (Shape.lift_wf hkn).2 hwe.2.2.1,
        (Shape.lift_wf (hkc p hp)).2 (hpwf p hp)⟩
    have hflab : ∀ e ∈ f, TyEq Δ e.ty (A.subst σ) := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := (hf e).1 he
      exact hwf.2.2.2 p.1 (hg₀g p hp)
    have hfdom : ∀ e ∈ f, TShape.HasType Δ e.inp.T (Shape.T (d.2.lift k)) := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := (hf e).1 he
      exact TShape.HasType.mono_r hΔ
        ((hdom p.1 (hg₀g p hp)).lift_subject hΔ hkn) _ hdle hdty
    have hfbody : ∀ e ∈ f,
        Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push e.inp.T) e.out.T := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := (hf e).1 he
      have hwe := hwf.2.2.1.1 p.1 (hg₀g p hp)
      refine Interp.mono hΔ ((Shape.lift_wf (hkc p hp)).2 (hpwf p hp))
        (TShape.LE.lift_le hΔ (m := (Prod.snd p : TShape)) (hkc p hp) (hpwf p hp)) ?_
      exact Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
        TShape.LE.le_lift hΔ (m := p.1.inp.T) hkn hwe.2.2.1⟩) (hall p hp).1
    -- so the Π-shape is well formed and interprets `Π A B`
    have hAσ : Δ ⊢ A.subst σ : .sort u := hAty.subst hΔ W
    have hΔA : ⊢ (A.subst σ :: Δ) := ⟨hΔ, _, hAσ⟩
    have hwfPi : Shape.WF (n := k+1) Δ
        (.forallE (A.subst σ) (B.subst σ.lift) (d.2.lift k) f) :=
      ⟨⟨u, hAσ⟩, ⟨v, hB.subst hΔA (W.lift hAty hAσ)⟩,
        (Shape.lift_wf hkd).2 hd.wf.1,
        fun e he => hfent e he,
        graph_coherent hΓ hAty hB hΔ W hwρ ihBdir (fun e he => (hfent e he).2.2.1)
          hflab hfbody⟩
    have hPi : Interp Δ Γ (.forallE A B) σ ρ
        (Shape.T (n := k+1) (.forallE (A.subst σ) (B.subst σ.lift) (d.2.lift k) f)) :=
      .forallE (Interp.mono hΔ ((Shape.lift_wf hkd).2 hd.wf.1)
          (TShape.LE.lift_le hΔ (m := d) hkd hd.wf.1) hA)
        hdty hwfPi (fun e he => (hflab e he).imp fun _ h => h) hfdom hfbody
        hwfPi (TShape.LE.refl hwfPi)
    -- and it types the λ-shape, with the λ's own graph as the generator
    refine ⟨_, hPi, TShape.HasType.mono_l hΔ (TShape.HasType.lam (g₀ := g₀)
      hdty (fun e he => ?_) hwf hwfPi (fun e he => ?_) (fun e he => ?_)
      (fun p hp => ?_) (fun p hp => (hall p hp).2) (TyEq.refl hAσ)) hle⟩
    · -- the Π-entries are types
      obtain ⟨p, hp, rfl⟩ := (hf e).1 he
      exact (ihBty.isType hΔ (hstage p.1 (hg₀g p hp)).1 (hstage p.1 (hg₀g p hp)).2
        (hall p hp).1).lift_subject hΔ (hkc p hp)
    · -- the generator's entries are well formed
      rw [hmap] at he
      exact ⟨(hwf.2.2.1.1 e he).2.2.1, (hwf.2.2.1.1 e he).2.2.2⟩
    · -- every entry of `g` is covered by the generator, namely by itself
      rw [hmap]
      exact TEvaluates.refl hwf.2.2.1 e he
    · -- and each generator code is the Π-entry built from it
      refine TEvaluates.lower
        (TShape.LE.le_lift hΔ (m := (Prod.snd p : TShape)) (hkc p hp) (hpwf p hp)) ?_
      refine TEvaluates.entry _ ((hf _).2 ⟨p, hp, rfl⟩)
        ⟨TyEq.refl_l (hwf.2.2.2 p.1 (hg₀g p hp)),
          (hwf.2.2.1.1 p.1 (hg₀g p hp)).2.1⟩ ?_
      exact TShape.LE.lift_le hΔ (m := p.1.inp.T) hkn (hwf.2.2.1.1 p.1 (hg₀g p hp)).2.2.1

/-- One direction of the `SoundEq` half of `lamDF`.

A λ-shape carries only its *domain* label, so the two sides differ in
that one term — and `Shape.LE` compares it up to definitional equality,
so one λ-shape is below the other with the same graph.  The bodies move
by their own `SoundEq` at each entry's stage (which is unchanged: the
stage term is the entry's label, not the binder's annotation) and then
`Interp.ctx` for the context whose head changed. -/
theorem sound_lam_eq_of {Γ : List Term} {A A' b b' : Term} {u : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u)
    (ihA : SoundEq Γ A A') (ihAty : SoundTy Γ A (.sort u)) (ihb : SoundEq (A :: Γ) b b')
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {m : TShape} (H : Interp Δ Γ (.lam A b) σ ρ m) :
    Interp Δ Γ (.lam A' b') σ ρ m := by
  have hAσ : TyEq Δ (A.subst σ) (A'.subst σ) := ⟨u, hAA'.subst hΔ W⟩
  cases H with
  | lam hA hd hwf hdom hbody hw hle =>
    have hwf' : Shape.WF Δ (Shape.lam (A'.subst σ) _) :=
      ⟨hwf.1, hwf.2.1, hwf.2.2.1, fun e he => TyEq.trans (hwf.2.2.2 e he) hAσ⟩
    refine .lam ((ihA hΔ W hAdm).1 hA) hd hwf' hdom (fun e he => ?_) hw
      (hle.trans hΔ (TShape.LE.T.2
        ⟨ShapeFun.LE.refl hwf.2.2.1, hwf.1, hwf.2.1, hAσ, hwf.2.2.2⟩))
    -- the body, at the stage extended by the entry's label
    have hwe := hwf.2.2.1.1 e he
    have W' : Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A :: Γ) :=
      .cons W hAA'.hasType.1 ((hwf.2.2.2 e he).choose_spec.defeqDF hwe.2.1)
    have hAdm' : Adm Δ Γ₀ (A :: Γ) (σ.cons e.tm) (ρ.push (Shape.T e.inp)) :=
      .cons hAdm (fun _ hc => ihAty.isType hΔ W hAdm hc) hA hwe.2.2.1 (hdom e he)
    exact Interp.ctx ((ihb hΔ W' hAdm').1 (hbody e he))
  | bot => exact .bot

/-- The `SoundEq` half of `lamDF`, both directions on the mirrored data —
which is why the rule carries its body premise twice, once over each
domain. -/
theorem sound_lam_eq {Γ : List Term} {A A' b b' : Term} {u : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u)
    (ihA : SoundEq Γ A A') (ihAty : SoundTy Γ A (.sort u))
    (ihb : SoundEq (A :: Γ) b b') (ihb' : SoundEq (A' :: Γ) b b') :
    SoundEq Γ (.lam A b) (.lam A' b') := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  exact ⟨sound_lam_eq_of hAA' ihA ihAty ihb hΔ W hAdm,
    sound_lam_eq_of hAA'.symm ihA.symm (SoundTy.of_eq hAA' ihA ihAty) ihb'.symm hΔ W hAdm⟩

/-! ## Pairs

A pair shape's components are the two arguments' own, so the common upper
bound is componentwise: the labels agree (both come from the same term at
the same stage), and each component joins by its argument's directedness.
The non-degeneracy conjunct of `WF` comes for free from `Shape.WF.join`,
which is why the bound is taken as the *join of the two lifted shapes*
rather than assembled from the two component bounds. -/

/-- The common upper bound of two pair shapes: first components joined by
the first component's directedness, graphs appended, generators
concatenated.  This is `sound_lam_ub` with a first component alongside,
and it is *easier* than the λ case: each entry keeps its own label and its
own slot, so no stage has to move.  The cross pairs are the two graphs'
outputs, which are approximants of one term and so compatible by its
directedness. -/
theorem dir_pair_ub {Γ : List Term} {A B a b : Term}
    (ihA : SoundDir Γ A) (iha : SoundDir Γ a) (ihb : SoundDir Γ b)
    {Δ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hwρ : Valuation.WF Δ ρ)
    {n₁ n₂} {x₁ : Shape n₁} {x₂ : Shape n₂} {d₁ d₂ : TShape}
    {g₁ : List (Entry (Shape n₁) × TShape)} {g₂ : List (Entry (Shape n₂) × TShape)}
    (ha₁ : Interp Δ Γ a σ ρ (Shape.T x₁)) (hA₁ : Interp Δ Γ A σ ρ d₁)
    (hd₁ : TShape.HasType Δ d₁ TShape.type)
    (hwf₁ : Shape.WF (n := n₁+1) Δ (.pair (A.subst σ) x₁ (g₁.map Prod.fst)))
    (hlab₁ : ∀ e ∈ g₁, Δ ⊢ e.1.tm ≡ a.subst σ : e.1.ty)
    (hdom₁ : ∀ e ∈ g₁, TShape.HasType Δ e.1.inp.T d₁)
    (hinp₁ : ∀ e ∈ g₁, Interp Δ Γ a σ ρ e.1.inp.T)
    (hout₁ : ∀ e ∈ g₁, Interp Δ Γ b σ ρ e.1.out.T)
    (hbody₁ : ∀ e ∈ g₁, Interp Δ (A :: Γ) B (σ.cons e.1.tm) (ρ.push e.1.inp.T) e.2)
    (hty₁ : ∀ e ∈ g₁, TShape.HasType Δ e.1.out.T e.2)
    (ha₂ : Interp Δ Γ a σ ρ (Shape.T x₂)) (hA₂ : Interp Δ Γ A σ ρ d₂)
    (hd₂ : TShape.HasType Δ d₂ TShape.type)
    (hwf₂ : Shape.WF (n := n₂+1) Δ (.pair (A.subst σ) x₂ (g₂.map Prod.fst)))
    (hlab₂ : ∀ e ∈ g₂, Δ ⊢ e.1.tm ≡ a.subst σ : e.1.ty)
    (hdom₂ : ∀ e ∈ g₂, TShape.HasType Δ e.1.inp.T d₂)
    (hinp₂ : ∀ e ∈ g₂, Interp Δ Γ a σ ρ e.1.inp.T)
    (hout₂ : ∀ e ∈ g₂, Interp Δ Γ b σ ρ e.1.out.T)
    (hbody₂ : ∀ e ∈ g₂, Interp Δ (A :: Γ) B (σ.cons e.1.tm) (ρ.push e.1.inp.T) e.2)
    (hty₂ : ∀ e ∈ g₂, TShape.HasType Δ e.1.out.T e.2) :
    ∃ s, TShape.WF Δ s ∧ Interp Δ Γ (.pair A B a b) σ ρ s ∧
      TShape.LE Δ (Shape.T (n := n₁+1) (.pair (A.subst σ) x₁ (g₁.map Prod.fst))) s ∧
      TShape.LE Δ (Shape.T (n := n₂+1) (.pair (A.subst σ) x₂ (g₂.map Prod.fst))) s := by
  have k₁ : n₁ ≤ max n₁ n₂ := Nat.le_max_left ..
  have k₂ : n₂ ≤ max n₁ n₂ := Nat.le_max_right ..
  -- the joined first component and the joined domain
  obtain ⟨hcx, hjx⟩ := (iha hΔ W hwρ).join hΔ ha₁ ha₂
  obtain ⟨hcd, hjd⟩ := (ihA hΔ W hwρ).join hΔ hA₁ hA₂
  have hdjty : TShape.HasType Δ (d₁.join d₂) TShape.type :=
    TShape.HasType.join_sort' hΔ rfl hd₁ hd₂ hcd
  have ⟨hled₁, hled₂⟩ := TShape.le_join hΔ hA₁.wf hA₂.wf hcd
  obtain ⟨_, hAσ⟩ := hwf₁.2.2.2.2.1
  -- **the cross pairs**: two outputs of one term, at a later stage
  have hcross : ShapeFun.Compat Shape.Compat Δ
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) (g₁.map Prod.fst))
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) (g₂.map Prod.fst)) := by
    intro e he e' he' Θ τ hΘ Wτ _ _
    obtain ⟨p, hp, rfl⟩ := ShapeFun.mem_lift.1 he
    obtain ⟨p', hp', rfl⟩ := ShapeFun.mem_lift.1 he'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hp'
    have hb₁ := (hout₁ q hq).subst hΘ Wτ
    have hb₂ := (hout₂ q' hq').subst hΘ Wτ
    obtain ⟨_, hwz, _, hz₁, hz₂⟩ :=
      ihb hΘ (Ctx.SubstEq.comp hΘ Wτ W) (Valuation.WF.subst hΘ Wτ hwρ) hb₁ hb₂
    have hcc : TShape.Compat Θ (Shape.T (q.1.out.subst τ)) (Shape.T (q'.1.out.subst τ)) := by
      have := TShape.Compat.of_common_upper hΘ hwz hz₁ hz₂
      simpa [TShape.subst_T] using this
    simp only [← Shape.lift_subst]
    exact (TShape.Compat.def k₁ k₂).1 hcc
  -- the two pair shapes are compatible, so their join is well formed
  have hcS : Shape.Compat (n := (max n₁ n₂)+1) Δ
      (.pair (A.subst σ) (x₁.lift (max n₁ n₂)) (ShapeFun.lift (Shape.lift (max n₁ n₂)) (g₁.map Prod.fst)))
      (.pair (A.subst σ) (x₂.lift (max n₁ n₂)) (ShapeFun.lift (Shape.lift (max n₁ n₂)) (g₂.map Prod.fst))) :=
    ⟨TyEq.refl hAσ, (TShape.Compat.def k₁ k₂).1 hcx, hcross⟩
  have hw₁ : Shape.WF Δ (Shape.lift (n := n₁+1) ((max n₁ n₂)+1)
      (.pair (A.subst σ) x₁ (g₁.map Prod.fst))) := (Shape.lift_wf (Nat.succ_le_succ k₁)).2 hwf₁
  have hw₂ : Shape.WF Δ (Shape.lift (n := n₂+1) ((max n₁ n₂)+1)
      (.pair (A.subst σ) x₂ (g₂.map Prod.fst))) := (Shape.lift_wf (Nat.succ_le_succ k₂)).2 hwf₂
  have hwS := Shape.WF.join hΔ hcS hw₁ hw₂
  -- the two generators, lifted to the common level
  have hG₁ : ((g₁.map fun p =>
      ((⟨p.1.ty, p.1.tm, p.1.inp.lift (max n₁ n₂), p.1.out.lift (max n₁ n₂)⟩ : Entry (Shape (max n₁ n₂))), p.2)).map Prod.fst)
      = ShapeFun.lift (Shape.lift (max n₁ n₂)) (g₁.map Prod.fst) := by
    simp [ShapeFun.lift, List.map_map, Function.comp_def]
  have hG₂ : ((g₂.map fun p =>
      ((⟨p.1.ty, p.1.tm, p.1.inp.lift (max n₁ n₂), p.1.out.lift (max n₁ n₂)⟩ : Entry (Shape (max n₁ n₂))), p.2)).map Prod.fst)
      = ShapeFun.lift (Shape.lift (max n₁ n₂)) (g₂.map Prod.fst) := by
    simp [ShapeFun.lift, List.map_map, Function.comp_def]
  have hwS' : Shape.WF (n := (max n₁ n₂)+1) Δ (.pair (A.subst σ) ((x₁.lift (max n₁ n₂)).join (x₂.lift (max n₁ n₂)))
      (((g₁.map fun p =>
          ((⟨p.1.ty, p.1.tm, p.1.inp.lift (max n₁ n₂), p.1.out.lift (max n₁ n₂)⟩ : Entry (Shape (max n₁ n₂))), p.2)) ++
        g₂.map fun p =>
          ((⟨p.1.ty, p.1.tm, p.1.inp.lift (max n₁ n₂), p.1.out.lift (max n₁ n₂)⟩ : Entry (Shape (max n₁ n₂))), p.2)).map Prod.fst)) := by
    rw [List.map_append, hG₁, hG₂]; exact hwS
  refine ⟨Shape.T (n := (max n₁ n₂)+1) (.pair (A.subst σ) ((x₁.lift (max n₁ n₂)).join (x₂.lift (max n₁ n₂)))
      (((g₁.map fun p =>
          ((⟨p.1.ty, p.1.tm, p.1.inp.lift (max n₁ n₂), p.1.out.lift (max n₁ n₂)⟩ : Entry (Shape (max n₁ n₂))), p.2)) ++
        g₂.map fun p =>
          ((⟨p.1.ty, p.1.tm, p.1.inp.lift (max n₁ n₂), p.1.out.lift (max n₁ n₂)⟩ : Entry (Shape (max n₁ n₂))),
            p.2)).map Prod.fst)), hwS', ?_,
    (TShape.LE.def hΔ (Nat.succ_le_succ k₁) (Nat.le_refl _)).2 ?_,
    (TShape.LE.def hΔ (Nat.succ_le_succ k₂) (Nat.le_refl _)).2 ?_⟩
  · refine Interp.pair (g₀ := (g₁.map fun p =>
        ((⟨p.1.ty, p.1.tm, p.1.inp.lift (max n₁ n₂), p.1.out.lift (max n₁ n₂)⟩ : Entry (Shape (max n₁ n₂))), p.2)) ++
        g₂.map fun p =>
          ((⟨p.1.ty, p.1.tm, p.1.inp.lift (max n₁ n₂), p.1.out.lift (max n₁ n₂)⟩ : Entry (Shape (max n₁ n₂))), p.2))
      hjx hjd hdjty hwS' ?_ ?_ ?_ ?_ ?_ ?_ hwS' (TShape.LE.refl hwS')
    all_goals
      intro e he
      match List.mem_append.1 he with
      | .inl he =>
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 he
        first
          | exact hlab₁ q hq
          | exact TShape.HasType.mono_r hΔ (TShape.HasType.mono_l hΔ (hdom₁ q hq)
              (TShape.LE.lift_le hΔ (m := q.1.inp.T) k₁ (hdom₁ q hq).wf.1)) _ hled₁ hdjty
          | exact Interp.lift hΔ k₁ (hinp₁ q hq)
          | exact Interp.lift hΔ k₁ (hout₁ q hq)
          | exact Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
              TShape.LE.le_lift hΔ (m := q.1.inp.T) k₁ (hdom₁ q hq).wf.1⟩) (hbody₁ q hq)
          | exact TShape.HasType.mono_l hΔ (hty₁ q hq)
              (TShape.LE.lift_le hΔ (m := q.1.out.T) k₁ (hty₁ q hq).wf.1)
      | .inr he =>
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 he
        first
          | exact hlab₂ q hq
          | exact TShape.HasType.mono_r hΔ (TShape.HasType.mono_l hΔ (hdom₂ q hq)
              (TShape.LE.lift_le hΔ (m := q.1.inp.T) k₂ (hdom₂ q hq).wf.1)) _ hled₂ hdjty
          | exact Interp.lift hΔ k₂ (hinp₂ q hq)
          | exact Interp.lift hΔ k₂ (hout₂ q hq)
          | exact Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
              TShape.LE.le_lift hΔ (m := q.1.inp.T) k₂ (hdom₂ q hq).wf.1⟩) (hbody₂ q hq)
          | exact TShape.HasType.mono_l hΔ (hty₂ q hq)
              (TShape.LE.lift_le hΔ (m := q.1.out.T) k₂ (hty₂ q hq).wf.1)
  · rw [Shape.lift_self, List.map_append, hG₁, hG₂]
    exact (Shape.le_join hΔ hw₁ hw₂ hcS).1
  · rw [Shape.lift_self, List.map_append, hG₁, hG₂]
    exact (Shape.le_join hΔ hw₁ hw₂ hcS).2

/-- Directedness of a pair: the `pairDF` case of `IsDefEq.dir`. -/
theorem dir_pair {Γ : List Term} {A B a b : Term}
    (ihA : SoundDir Γ A) (iha : SoundDir Γ a) (ihb : SoundDir Γ b) :
    SoundDir Γ (.pair A B a b) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | pair ha₁ hA₁ hd₁ hwf₁ hlab₁ hdom₁ hinp₁ hout₁ hbody₁ hty₁ hw₁ hle₁ =>
    cases h₂ with
    | bot =>
      exact ⟨_, hw₁, .pair ha₁ hA₁ hd₁ hwf₁ hlab₁ hdom₁ hinp₁ hout₁ hbody₁ hty₁ hw₁ hle₁,
        TShape.LE.refl hw₁, TShape.bot_le' rfl⟩
    | pair ha₂ hA₂ hd₂ hwf₂ hlab₂ hdom₂ hinp₂ hout₂ hbody₂ hty₂ hw₂ hle₂ =>
      obtain ⟨s, hws, hs, hs₁, hs₂⟩ :=
        dir_pair_ub ihA iha ihb hΔ W hwρ ha₁ hA₁ hd₁ hwf₁ hlab₁ hdom₁ hinp₁ hout₁ hbody₁ hty₁
          ha₂ hA₂ hd₂ hwf₂ hlab₂ hdom₂ hinp₂ hout₂ hbody₂ hty₂
      exact ⟨s, hws, hs, hle₁.trans hΔ hs₁, hle₂.trans hΔ hs₂⟩

/-! ## Application

Directedness at `app` is where the λ-shape's domain label pays for itself
(§5.5b).  Two `app` derivations for the same term look their arguments up
in two λ-shapes of `F`, at those shapes' own labels `A₁`, `A₂`.  A common
upper bound of the two λ-shapes is a λ-shape, its graph covers both, and
the order on λ-shapes makes its label definitionally equal to both — so
the two lookups become lookups in *one* graph at *one* query, whose
outputs the graph's coherence makes joinable.  No typing of `F` or of the
argument is used, which is what lets `SoundDir` stay over `Valuation.WF`
and be proved before soundness. -/

/-- Above a λ-shape there is only a λ-shape. -/
theorem TShape.LE.lam_ub {Δ : List Term} {n} {A : Term} {g : ShapeFun n} {z : TShape}
    (h : TShape.LE Δ (Shape.T (n := n+1) (ShapeS.lam A g)) z) :
    ∃ (k : Nat) (A' : Term) (g' : ShapeFun k), z = Shape.T (n := k+1) (ShapeS.lam A' g') := by
  obtain ⟨j, t⟩ := z
  obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ h
  cases j with
  | zero => cases t <;> exact absurd h2 (fun x => x)
  | succ j =>
    cases t with
    | lam A' g' => exact ⟨j, A', g', rfl⟩
    | _ => exact absurd h2 (fun x => x)

/-- And its domain label is the same one. -/
theorem TShape.LE.lam_dom {Δ : List Term} {n k} {A A' : Term}
    {g : ShapeFun n} {g' : ShapeFun k}
    (h : TShape.LE Δ (Shape.T (n := n+1) (ShapeS.lam A g))
      (Shape.T (n := k+1) (ShapeS.lam A' g'))) : TyEq Δ A A' := by
  obtain ⟨M, _, _, h2⟩ := TShape.LE.at_succ h
  exact h2.2.2.2.1

/-- Directedness for `.app`: the `appDF` case of `IsDefEq.dir`. -/
theorem dir_app {Γ : List Term} {F a : Term}
    (ihF : SoundDir Γ F) (iha : SoundDir Γ a) : SoundDir Γ (.app F a) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | app hF₁ ha₁ hev₁ hw₁ hle₁ =>
    cases h₂ with
    | bot =>
      exact ⟨_, hw₁, .app hF₁ ha₁ hev₁ hw₁ hle₁, TShape.LE.refl hw₁, TShape.bot_le' rfl⟩
    | app hF₂ ha₂ hev₂ hw₂ hle₂ =>
      -- one λ-shape above both, and one shape above both arguments
      obtain ⟨z, hwz, hz, hz₁, hz₂⟩ := ihF hΔ W hwρ hF₁ hF₂
      obtain ⟨k, A, g, rfl⟩ := TShape.LE.lam_ub hz₁
      obtain ⟨x, hwx, hx, hx₁, hx₂⟩ := iha hΔ W hwρ ha₁ ha₂
      have hwg : ShapeFun.WF Δ (Shape.WF Δ) g := hwz.2.2.1
      have hout : ∀ e ∈ g, TShape.WF Δ e.out.T := fun e he => (hwg.1 e he).2.2.2
      -- both lookups move into the big graph, at its label and its input
      have hmove {n'} {A' : Term} {g' : ShapeFun n'} {x' y' : TShape}
          (hF' : Interp Δ Γ F σ ρ (Shape.T (n := n'+1) (ShapeS.lam A' g')))
          (hz' : TShape.LE Δ (Shape.T (n := n'+1) (ShapeS.lam A' g'))
            (Shape.T (n := k+1) (ShapeS.lam A g)))
          (hx' : TShape.LE Δ x' x)
          (hev : TEvaluates Δ g' A' (a.subst σ) x' y') :
          TEvaluates Δ g A (a.subst σ) x y' :=
        TEvaluates.mono_inp hΔ hx' <| TEvaluates.trans hΔ
          (TShape.LE.lam_decomp hΔ hz' hF'.wf hwz (TEvaluates.refl hwg))
          (TEvaluates.retype (TShape.LE.lam_dom hz') hev)
      have hev₁' := hmove hF₁ hz₁ hx₁ hev₁
      have hev₂' := hmove hF₂ hz₂ hx₂ hev₂
      have hc := TEvaluates.compat hΔ hwg.2 hwx hev₁' hev₂'
      have hwy := TShape.WF.join hΔ hc (TEvaluates.wf hΔ hout hev₁')
        (TEvaluates.wf hΔ hout hev₂')
      refine ⟨_, hwy, .app hz hx (.join hc hev₁' hev₂') hwy (TShape.LE.refl hwy),
        hle₁.trans hΔ ?_, hle₂.trans hΔ ?_⟩
      · exact (TShape.le_join hΔ (TEvaluates.wf hΔ hout hev₁')
          (TEvaluates.wf hΔ hout hev₂') hc).1
      · exact (TShape.le_join hΔ (TEvaluates.wf hΔ hout hev₁')
          (TEvaluates.wf hΔ hout hev₂') hc).2

/-! ## The first projection

`Interp.fst` reads the first component off a pair shape, so both halves
are the pair's: `SoundEq` is the argument's clause by clause, and for
`SoundTy` the component's typing is the `HasType.pair` clause's own
`hxd`, brought down by `mono_l` and retyped at the Σ's domain by
`mono_r`.  The second projection is not here: its type is `B[fst p]`, and
relating that to the Σ's codomain graph needs `Interp.inst`. -/

/-- Above a pair shape there is only a pair shape. -/
theorem TShape.LE.pair_ub {Δ : List Term} {n} {A : Term} {x : Shape n} {g : ShapeFun n}
    {z : TShape} (h : TShape.LE Δ (Shape.T (n := n+1) (ShapeS.pair A x g)) z) :
    ∃ (k : Nat) (A' : Term) (x' : Shape k) (g' : ShapeFun k),
      z = Shape.T (n := k+1) (ShapeS.pair A' x' g') := by
  obtain ⟨j, t⟩ := z
  obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ h
  cases j with
  | zero => cases t <;> exact absurd h2 (fun x => x)
  | succ j =>
    cases t with
    | pair A' x' g' => exact ⟨j, A', x', g', rfl⟩
    | _ => exact absurd h2 (fun x => x)

/-- And its domain label is the same one. -/
theorem TShape.LE.pair_dom {Δ : List Term} {n k} {A A' : Term} {x : Shape n} {x' : Shape k}
    {g : ShapeFun n} {g' : ShapeFun k}
    (h : TShape.LE Δ (Shape.T (n := n+1) (ShapeS.pair A x g))
      (Shape.T (n := k+1) (ShapeS.pair A' x' g'))) : TyEq Δ A A' := by
  obtain ⟨M, _, _, h2⟩ := TShape.LE.at_succ h
  exact h2.2.2.2.2.1

/-- Directedness for `.fst`: the first component of the argument's own
upper bound, which is a pair shape because it is above one. -/
theorem dir_fst {Γ : List Term} {p : Term} (h : SoundDir Γ p) : SoundDir Γ (.fst p) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | fst hp₁ hw₁ hle₁ =>
    cases h₂ with
    | bot => exact ⟨_, hw₁, .fst hp₁ hw₁ hle₁, TShape.LE.refl hw₁, TShape.bot_le' rfl⟩
    | fst hp₂ _ hle₂ =>
      obtain ⟨z, hwz, hz, hz₁, hz₂⟩ := h hΔ W hwρ hp₁ hp₂
      obtain ⟨k, A', x', g', rfl⟩ := TShape.LE.pair_ub hz₁
      obtain ⟨_, hx₁, _⟩ := TShape.LE.pair_decomp hΔ hz₁ hp₁.wf hwz (TEvaluates.refl hwz.2.2.1)
      obtain ⟨_, hx₂, _⟩ := TShape.LE.pair_decomp hΔ hz₂ hp₂.wf hwz (TEvaluates.refl hwz.2.2.1)
      exact ⟨Shape.T x', hwz.2.2.2.2.2,
        .fst hz hwz.2.2.2.2.2 (TShape.LE.refl hwz.2.2.2.2.2),
        hle₁.trans hΔ hx₁, hle₂.trans hΔ hx₂⟩

/-- Directedness for `.snd`.  Now that the second component is a graph
this is `dir_app`, not `dir_fst`: the two lookups move into the upper
bound's graph, at its label and its first component, and the graph's
coherence joins them. -/
theorem dir_snd {Γ : List Term} {p : Term} (h : SoundDir Γ p) : SoundDir Γ (.snd p) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | snd hp₁ hev₁ hw₁ hle₁ =>
    cases h₂ with
    | bot => exact ⟨_, hw₁, .snd hp₁ hev₁ hw₁ hle₁, TShape.LE.refl hw₁, TShape.bot_le' rfl⟩
    | snd hp₂ hev₂ _ hle₂ =>
      obtain ⟨z, hwz, hz, hz₁, hz₂⟩ := h hΔ W hwρ hp₁ hp₂
      obtain ⟨k, A', x', g', rfl⟩ := TShape.LE.pair_ub hz₁
      have hout : ∀ e ∈ g', TShape.WF Δ e.out.T := fun e he => (hwz.2.2.1.1 e he).2.2.2
      have hmove {n} {A₀ : Term} {x : Shape n} {g : ShapeFun n} {y : TShape}
          (hp : Interp Δ Γ p σ ρ (Shape.T (n := n+1) (ShapeS.pair A₀ x g)))
          (hz' : TShape.LE Δ (Shape.T (n := n+1) (ShapeS.pair A₀ x g))
            (Shape.T (n := k+1) (ShapeS.pair A' x' g')))
          (hev : TEvaluates Δ g A₀ ((Term.fst p).subst σ) (Shape.T x) y) :
          TEvaluates Δ g' A' ((Term.fst p).subst σ) (Shape.T x') y :=
        have ⟨_, hx, hcov⟩ := TShape.LE.pair_decomp hΔ hz' hp.wf hwz (TEvaluates.refl hwz.2.2.1)
        TEvaluates.mono_inp hΔ hx
          (TEvaluates.trans hΔ hcov (TEvaluates.retype (TShape.LE.pair_dom hz') hev))
      have hev₁' := hmove hp₁ hz₁ hev₁
      have hev₂' := hmove hp₂ hz₂ hev₂
      have hc := TEvaluates.compat hΔ hwz.2.2.1.2 (TShape.WF.T.2 hwz.2.2.2.2.2) hev₁' hev₂'
      have hwy := TShape.WF.join hΔ hc (TEvaluates.wf hΔ hout hev₁')
        (TEvaluates.wf hΔ hout hev₂')
      exact ⟨_, hwy, .snd hz (.join hc hev₁' hev₂') hwy (TShape.LE.refl hwy),
        hle₁.trans hΔ (TShape.le_join hΔ (TEvaluates.wf hΔ hout hev₁')
          (TEvaluates.wf hΔ hout hev₂') hc).1,
        hle₂.trans hΔ (TShape.le_join hΔ (TEvaluates.wf hΔ hout hev₁')
          (TEvaluates.wf hΔ hout hev₂') hc).2⟩

/-! ## The β-rules of Σ

A projection of a pair has the component's approximants.  `fst` is two
inversions and a one-entry-free pair (the graph may be empty, so the
backward direction builds `pair A[σ] m []`).  `snd` is the lookup
unfolded, exactly as `beta` is for Π: forward, every entry's output is an
approximant of `b` and the joins go by `b`'s directedness; backward, the
single entry `(A[σ], a[σ], x, m)` carries the type witness that
`SoundTy b (B[a])` and `Interp.inst` supply. -/

/-- The first projection of a pair: the `pair_fst` case. -/
theorem sound_pair_fst {Γ : List Term} {A B a b : Term} {u : Bool}
    (hA : Γ ⊢ A : .sort u) : SoundEq Γ (.fst (.pair A B a b)) a := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  obtain ⟨n, s⟩ := m
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  constructor
  · intro h
    cases h with
    | bot => exact .bot
    | fst hp hw hle =>
      cases hp with
      | pair ha _ _ hwf' _ _ _ _ _ _ _ hle' =>
        exact ha.mono hΔ hw (hle.trans hΔ (TShape.LE.pair_decomp hΔ hle' hle'.wf hwf'
          (TEvaluates.refl hwf'.2.2.1)).2.1)
  · intro h
    by_cases hb : s.IsBot
    · rw [Shape.WF.eq_bot_of_isBot (s := s) h.wf hb]; exact .bot
    · have hwf : Shape.WF (n := n+1) Δ (ShapeS.pair (A.subst σ) s []) :=
        ⟨fun hbb => hb hbb.1, nofun, ⟨nofun, nofun⟩, nofun, TyEq.refl hAσ, h.wf⟩
      exact .fst (.pair (g₀ := []) (d := Shape.T (n := 0) Shape.bot) h .bot (.bot .sort) hwf
        nofun nofun nofun nofun nofun nofun hwf (TShape.LE.refl hwf))
        h.wf (TShape.LE.refl h.wf)

/-- The second projection of a pair: the `pair_snd` case. -/
theorem sound_pair_snd {Γ : List Term} {A B a b : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u) (ha : Γ ⊢ a : A)
    (hfst : Γ ⊢ .fst (.pair A B a b) ≡ a : A)
    (ihAty : SoundTy Γ A (.sort u))
    (ihaty : SoundTy Γ a A) (ihbty : SoundTy Γ b (B.inst a))
    (ihadir : SoundDir Γ a) (ihbdir : SoundDir Γ b) :
    SoundEq Γ (.snd (.pair A B a b)) b := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  obtain ⟨n, s⟩ := m
  have hwρ := hAdm.wf
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  have haσ : Δ ⊢ a.subst σ : A.subst σ := ha.subst hΔ W
  constructor
  · intro h
    cases h with
    | bot => exact .bot
    | snd hp hev hw hle =>
      -- every entry's output is an approximant of `b`, and the lookup's
      -- joins are `b`'s own directedness
      have key : ∀ {n'} {gg : ShapeFun n'} {A₀ tm₀ : Term} {x₀ c : TShape},
          (∀ e ∈ gg, Interp Δ Γ b σ ρ e.out.T) → TEvaluates Δ gg A₀ tm₀ x₀ c →
          Interp Δ Γ b σ ρ c := by
        intro n' gg A₀ tm₀ x₀ c hgg hc
        induction hc with
        | bot => exact .bot
        | entry e he _ _ => exact hgg e he
        | lower hle'' _ ih => exact ih.mono hΔ hle''.wf hle''
        | join _ _ _ ih₁ ih₂ => exact ((ihbdir hΔ W hwρ).join hΔ ih₁ ih₂).2
      cases hp with
      | pair _ _ _ hwf' _ _ _ hout _ _ _ hle' =>
        have hcov := (TShape.LE.pair_decomp hΔ hle' hle'.wf hwf'
          (TEvaluates.refl hwf'.2.2.1)).2.2
        refine (key ?_ (TEvaluates.trans hΔ hcov hev)).mono hΔ hw hle
        intro e he
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 he
        exact hout q hq
  · intro h
    by_cases hb : s.IsBot
    · rw [Shape.WF.eq_bot_of_isBot (s := s) h.wf hb]; exact .bot
    · -- the single entry, with the type witness the second component needs
      obtain ⟨c, hc, hty⟩ := ihbty.approx hΔ W hAdm h
      obtain ⟨x, hbody, hx⟩ := (Interp.inst (A := A) (b := B) hΔ (ihadir hΔ W hwρ) hwρ).1 hc
      obtain ⟨d, hd, hxd⟩ := ihaty.approx hΔ W hAdm hx
      obtain ⟨k, hkx, hkn⟩ : ∃ k, x.1 ≤ k ∧ n ≤ k :=
        ⟨max x.1 n, Nat.le_max_left .., Nat.le_max_right ..⟩
      have hwx : Shape.WF Δ (x.2.lift k) := (Shape.lift_wf hkx).2 hx.wf
      have hws : Shape.WF Δ (s.lift k) := (Shape.lift_wf hkn).2 h.wf
      have hnb : ¬ (s.lift k).IsBot := fun hbb => hb ((Shape.lift_isBot hkn).1 hbb)
      have hwf : Shape.WF (n := k+1) Δ (ShapeS.pair (A.subst σ) (x.2.lift k)
          [⟨A.subst σ, a.subst σ, x.2.lift k, s.lift k⟩]) := by
        refine ⟨fun hbb => by simp at hbb, ?_, ⟨?_, ?_⟩, ?_, TyEq.refl hAσ, hwx⟩
        · intro e₀ he₀; cases he₀ with | head => exact hnb | tail _ h => nomatch h
        · intro e₀ he₀
          cases he₀ with
          | head => exact ⟨⟨u, hAσ⟩, haσ, hwx, hws⟩
          | tail _ h => nomatch h
        · intro e₀ he₀ e₁ he₁ Θ τ hΘ Wτ _ _
          cases he₀ with
          | tail _ h => nomatch h
          | head =>
            cases he₁ with
            | tail _ h => nomatch h
            | head => exact (Shape.WF.subst hΘ Wτ hws).coherent
        · intro e₀ he₀
          cases he₀ with | head => exact TyEq.refl hAσ | tail _ h => nomatch h
      refine .snd (.pair (g₀ := [(⟨A.subst σ, a.subst σ, x.2.lift k, s.lift k⟩, c)])
          (Interp.lift hΔ hkx hx) hd (ihAty.isType hΔ W hAdm hd) hwf ?_ ?_ ?_ ?_ ?_ ?_ hwf
          (TShape.LE.refl hwf))
        (.entry ⟨A.subst σ, a.subst σ, x.2.lift k, s.lift k⟩ (.head _)
          ⟨TyEq.refl hAσ, IsDefEq.subst hΔ W hfst.symm⟩ (TShape.LE.refl hwx)) h.wf
        (TShape.LE.le_lift (m := ⟨n, s⟩) hΔ hkn h.wf)
      all_goals
        intro e₀ he₀
        cases he₀ with
        | tail _ hnil => nomatch hnil
        | head =>
          first
            | exact haσ
            | exact hxd.lift_subject hΔ hkx
            | exact Interp.lift hΔ hkx hx
            | exact Interp.lift (m := ⟨n, s⟩) hΔ hkn h
            | (refine Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
                 TShape.LE.le_lift hΔ hkx hx.wf⟩) ?_
               rw [← Subst.one_comp]; exact hbody)
            | exact hty.lift_subject hΔ hkn

/-- Soundness for `fstDF`. -/
theorem sound_fst {Γ : List Term} {A B p p' : Term} {u v : Bool}
    (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v)
    (ihe : SoundEq Γ p p') (ihty : SoundTy Γ p (.sigma A B)) :
    SoundEq Γ (.fst p) (.fst p') ∧ SoundTy Γ (.fst p) A := by
  constructor
  · intro Δ Γ₀ σ ρ hΔ W hAdm m
    constructor
    · intro h
      cases h with
      | bot => exact .bot
      | fst hp hw hle => exact .fst ((ihe hΔ W hAdm).1 hp) hw hle
    · intro h
      cases h with
      | bot => exact .bot
      | fst hp hw hle => exact .fst ((ihe hΔ W hAdm).2 hp) hw hle
  · refine ⟨.fstDF hA hB ihty.typed, ?_⟩
    intro Δ Γ₀ σ ρ hΔ W hAdm m hm
    cases hm with
    | bot => exact ⟨TShape.bot, .bot, .bot (.bot .sort)⟩
    | fst hp _ hle =>
      obtain ⟨s, hs, hty⟩ := ihty.approx hΔ W hAdm hp
      cases hty with
      | pair _ _ _ hwSg hxd _ _ _ _ =>
        cases hs with
        | sigma hA hd₀ hwf _ _ _ _ hleS =>
          obtain ⟨_, hdd, _⟩ :=
            TShape.LE.sigma_decomp hΔ hleS hwSg hwf (TEvaluates.refl hwf.2.2.2)
          exact ⟨_, hA, TShape.HasType.mono_r hΔ
            (TShape.HasType.mono_l hΔ hxd hle) _ hdd hd₀⟩

/-- **The type of a pair**, the Σ mirror of `sound_lam_ty` — and shorter,
because `Interp.pair` already carries the codes: a pair's graph is
certified by a generator whose codes are approximants of `B` at each
entry's slot, so the Σ-shape's graph is that generator, lifted to one
level.  The only thing the clause does not carry is a typing of the
first component at the *same* domain shape its entries are typed at, and
that is one call each to `SoundTy a A` and `A`'s directedness. -/
theorem sound_pair_ty {Γ : List Term} {A B a b : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v)
    (hpair : Γ ⊢ .pair A B a b : .sigma A B)
    (ihAty : SoundTy Γ A (.sort u)) (ihAdir : SoundDir Γ A) (ihaty : SoundTy Γ a A)
    (ihBty : SoundTy (A :: Γ) B (.sort v)) (ihBdir : SoundDir (A :: Γ) B) :
    SoundTy Γ (.pair A B a b) (.sigma A B) := by
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hAty⟩
  refine ⟨hpair, ?_⟩
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  have hwρ := hAdm.wf
  cases hm with
  | bot => exact ⟨TShape.bot, .bot, .bot (.bot .sort)⟩
  | @pair _ _ _ _ n x g₀ d _ _ _ _ ha hA hd hwp hlab hdom hinp _ hcode hcty hw hle =>
    -- the first component, typed at a domain shape joined with the clause's
    obtain ⟨c, hc, hxc⟩ := ihaty.approx hΔ W hAdm ha
    obtain ⟨hcd, hdj⟩ := (ihAdir hΔ W hwρ).join hΔ hA hc
    have hdjty : TShape.HasType Δ (d.join c) TShape.type :=
      TShape.HasType.join_sort' hΔ rfl hd (ihAty.isType hΔ W hAdm hc) hcd
    obtain ⟨hled, hlec⟩ := TShape.le_join hΔ hA.wf hc.wf hcd
    -- one level for the codes, the joined domain and the graph
    obtain ⟨k, hkn, hkd, hkc⟩ : ∃ k, n ≤ k ∧ (d.join c).1 ≤ k ∧
        ∀ p ∈ g₀, (Prod.snd p : TShape).1 ≤ k :=
      ⟨levelMax (fun p => (Prod.snd p : TShape).1) (max n (d.join c).1) g₀,
        Nat.le_trans (Nat.le_max_left ..) le_levelMax,
        Nat.le_trans (Nat.le_max_right ..) le_levelMax,
        fun p hp => mem_le_levelMax (f := fun p => (Prod.snd p : TShape).1) hp⟩
    obtain ⟨f, hf⟩ : ∃ f : ShapeFun k, ∀ e, e ∈ f ↔ ∃ p ∈ g₀,
        e = ⟨p.1.ty, p.1.tm, p.1.inp.lift k, (Prod.snd p : TShape).2.lift k⟩ :=
      ⟨g₀.map fun p => ⟨p.1.ty, p.1.tm, p.1.inp.lift k, (Prod.snd p : TShape).2.lift k⟩,
        fun e => by simp [List.mem_map, eq_comm]⟩
    have hg₀g : ∀ p ∈ g₀, p.1 ∈ g₀.map (·.1) := fun p hp => List.mem_map.2 ⟨p, hp, rfl⟩
    have hpwf : ∀ p ∈ g₀, TShape.WF Δ (Prod.snd p : TShape) := fun p hp => (hcode p hp).wf
    have hdty : TShape.HasType Δ (Shape.T ((d.join c).2.lift k)) TShape.type :=
      hdjty.lift_subject hΔ hkd
    have hdle : TShape.LE Δ (d.join c) (Shape.T ((d.join c).2.lift k)) :=
      TShape.LE.le_lift hΔ (m := d.join c) hkd hdjty.wf.1
    -- the Σ-shape's premises, entry by entry
    have hfent : ∀ e ∈ f, (∃ u, Δ ⊢ e.ty : .sort u) ∧ Δ ⊢ e.tm : e.ty ∧
        Shape.WF Δ e.inp ∧ Shape.WF Δ e.out := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := (hf e).1 he
      have hwe := hwp.2.2.1.1 p.1 (hg₀g p hp)
      exact ⟨hwe.1, hwe.2.1, (Shape.lift_wf hkn).2 hwe.2.2.1,
        (Shape.lift_wf (hkc p hp)).2 (hpwf p hp)⟩
    have hflab : ∀ e ∈ f, TyEq Δ e.ty (A.subst σ) := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := (hf e).1 he
      exact hwp.2.2.2.1 p.1 (hg₀g p hp)
    have hfdom : ∀ e ∈ f, TShape.HasType Δ e.inp.T (Shape.T ((d.join c).2.lift k)) := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := (hf e).1 he
      exact TShape.HasType.mono_r hΔ
        ((TShape.HasType.mono_r hΔ (hdom p hp) _ hled hdjty).lift_subject hΔ hkn) _ hdle hdty
    have hfbody : ∀ e ∈ f,
        Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push e.inp.T) e.out.T := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := (hf e).1 he
      have hwe := hwp.2.2.1.1 p.1 (hg₀g p hp)
      refine Interp.mono hΔ ((Shape.lift_wf (hkc p hp)).2 (hpwf p hp))
        (TShape.LE.lift_le hΔ (m := (Prod.snd p : TShape)) (hkc p hp) (hpwf p hp)) ?_
      exact Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
        TShape.LE.le_lift hΔ (m := p.1.inp.T) hkn hwe.2.2.1⟩) (hcode p hp)
    have hAσ : Δ ⊢ A.subst σ : .sort u := hAty.subst hΔ W
    have hΔA : ⊢ (A.subst σ :: Δ) := ⟨hΔ, _, hAσ⟩
    have hwfSg : Shape.WF (n := k+1) Δ
        (.sigma (A.subst σ) (B.subst σ.lift) ((d.join c).2.lift k) f) :=
      ⟨⟨u, hAσ⟩, ⟨v, hB.subst hΔA (W.lift hAty hAσ)⟩,
        (Shape.lift_wf hkd).2 hdjty.wf.1,
        fun e he => hfent e he,
        graph_coherent hΓ hAty hB hΔ W hwρ ihBdir (fun e he => (hfent e he).2.2.1)
          hflab hfbody⟩
    have hSg : Interp Δ Γ (.sigma A B) σ ρ
        (Shape.T (n := k+1) (.sigma (A.subst σ) (B.subst σ.lift) ((d.join c).2.lift k) f)) :=
      .sigma (Interp.mono hΔ ((Shape.lift_wf hkd).2 hdjty.wf.1)
          (TShape.LE.lift_le hΔ (m := d.join c) hkd hdjty.wf.1) hdj)
        hdty hwfSg (fun e he => (hflab e he).imp fun _ h => h) hfdom hfbody
        hwfSg (TShape.LE.refl hwfSg)
    -- and it types the pair-shape, with the clause's own generator
    refine ⟨_, hSg, TShape.HasType.mono_l hΔ (TShape.HasType.pair (g₀ := g₀)
      hdty (fun e he => ?_) hwp hwfSg
      (TShape.HasType.mono_r hΔ (TShape.HasType.mono_r hΔ hxc _ hlec hdjty) _ hdle hdty)
      (fun e he => ?_) (fun e he => ?_) (fun p hp => ?_) hcty (TyEq.refl hAσ)) hle⟩
    · -- the Σ-entries are types
      obtain ⟨p, hp, rfl⟩ := (hf e).1 he
      have hwe := hwp.2.2.1.1 p.1 (hg₀g p hp)
      have W' : Ctx.SubstEq Δ (σ.cons p.1.tm) (σ.cons p.1.tm) (A :: Γ) :=
        .cons W hAty ((hwp.2.2.2.1 p.1 (hg₀g p hp)).choose_spec.defeqDF hwe.2.1)
      have hAdm' : Adm Δ Γ₀ (A :: Γ) (σ.cons p.1.tm) (ρ.push p.1.inp.T) :=
        .cons hAdm (fun _ hc' => ihAty.isType hΔ W hAdm hc') hA hwe.2.2.1 (hdom p hp)
      exact (ihBty.isType hΔ W' hAdm' (hcode p hp)).lift_subject hΔ (hkc p hp)
    · -- the generator's entries are well formed
      exact ⟨(hwp.2.2.1.1 e he).2.2.1, (hwp.2.2.1.1 e he).2.2.2⟩
    · -- every entry is covered by itself
      exact TEvaluates.refl hwp.2.2.1 e he
    · -- and each code is the Σ-entry built from it
      refine TEvaluates.lower
        (TShape.LE.le_lift hΔ (m := (Prod.snd p : TShape)) (hkc p hp) (hpwf p hp)) ?_
      refine TEvaluates.entry _ ((hf _).2 ⟨p, hp, rfl⟩)
        ⟨TyEq.refl_l (hwp.2.2.2.1 p.1 (hg₀g p hp)),
          (hwp.2.2.1.1 p.1 (hg₀g p hp)).2.1⟩ ?_
      exact TShape.LE.lift_le hΔ (m := p.1.inp.T) hkn (hwp.2.2.1.1 p.1 (hg₀g p hp)).2.2.1

/-- One direction of the `SoundEq` half of `pairDF`.  A pair-shape's only
label is its domain, and its entries' label terms name the *first
component*, so the two things that move are that label (up to `TyEq`, as
at λ) and those terms (along `a ≡ a'`, at the entry's own type).  The
codomain's values do not move at all: their stage is the entry's label
term, which is unchanged. -/
theorem sound_pair_eq_of {Γ : List Term} {A A' B B' a a' b b' : Term} {u : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (haa' : Γ ⊢ a ≡ a' : A)
    (ihA : SoundEq Γ A A') (ihAty : SoundTy Γ A (.sort u))
    (iha : SoundEq Γ a a') (ihb : SoundEq Γ b b') (ihB : SoundEq (A :: Γ) B B')
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {m : TShape} (H : Interp Δ Γ (.pair A B a b) σ ρ m) :
    Interp Δ Γ (.pair A' B' a' b') σ ρ m := by
  have hAσ : TyEq Δ (A.subst σ) (A'.subst σ) := ⟨u, hAA'.subst hΔ W⟩
  have haσ : Δ ⊢ a.subst σ ≡ a'.subst σ : A.subst σ := haa'.subst hΔ W
  cases H with
  | bot => exact .bot
  | @pair _ _ _ _ n x g₀ d _ _ _ _ ha hA hd hwp hlab hdom hinp hout hcode hcty hw hle =>
    have hwp' : Shape.WF (n := n+1) Δ (ShapeS.pair (A'.subst σ) x (g₀.map (·.1))) :=
      ⟨hwp.1, hwp.2.1, hwp.2.2.1,
        fun e he => TyEq.trans (hwp.2.2.2.1 e he) hAσ,
        TyEq.refl_r hAσ, hwp.2.2.2.2.2⟩
    refine .pair ((iha hΔ W hAdm).1 ha) ((ihA hΔ W hAdm).1 hA) hd hwp'
      (fun e he => ?_) hdom (fun e he => (iha hΔ W hAdm).1 (hinp e he))
      (fun e he => (ihb hΔ W hAdm).1 (hout e he)) (fun e he => ?_) hcty hw
      (hle.trans hΔ (TShape.LE.T.2
        ⟨Shape.LE.refl hwp.2.2.2.2.2, ShapeFun.LE.refl hwp.2.2.1, hwp.1, hwp.2.1,
          hAσ, hwp.2.2.2.1⟩))
    · -- the entry's label term names the new first component
      exact (hlab e he).trans
        (((hwp.2.2.2.1 e.1 (List.mem_map.2 ⟨e, he, rfl⟩)).choose_spec).symm.defeqDF haσ)
    · -- the codomain's value, at the entry's own stage
      have hwe := hwp.2.2.1.1 e.1 (List.mem_map.2 ⟨e, he, rfl⟩)
      have W' : Ctx.SubstEq Δ (σ.cons e.1.tm) (σ.cons e.1.tm) (A :: Γ) :=
        .cons W hAA'.hasType.1
          ((hwp.2.2.2.1 e.1 (List.mem_map.2 ⟨e, he, rfl⟩)).choose_spec.defeqDF hwe.2.1)
      have hAdm' : Adm Δ Γ₀ (A :: Γ) (σ.cons e.1.tm) (ρ.push e.1.inp.T) :=
        .cons hAdm (fun _ hc => ihAty.isType hΔ W hAdm hc) hA hwe.2.2.1 (hdom e he)
      exact Interp.ctx ((ihB hΔ W' hAdm').1 (hcode e he))

/-- The `SoundEq` half of `pairDF`. -/
theorem sound_pair_eq {Γ : List Term} {A A' B B' a a' b b' : Term} {u : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (haa' : Γ ⊢ a ≡ a' : A)
    (ihA : SoundEq Γ A A') (ihAty : SoundTy Γ A (.sort u))
    (iha : SoundEq Γ a a') (ihb : SoundEq Γ b b')
    (ihB : SoundEq (A :: Γ) B B') (ihB' : SoundEq (A' :: Γ) B B') :
    SoundEq Γ (.pair A B a b) (.pair A' B' a' b') := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  exact ⟨sound_pair_eq_of hAA' haa' ihA ihAty iha ihb ihB hΔ W hAdm,
    sound_pair_eq_of hAA'.symm (hAA'.defeqDF haa'.symm) ihA.symm
      (SoundTy.of_eq hAA' ihA ihAty) iha.symm ihb.symm ihB'.symm hΔ W hAdm⟩

/-! ## The second projection

`Interp.snd` is a query at `fst p` (§4.7a), so the codomain family's
lookup that types the second component is at that label, and the value
read off is an approximant of `B[fst p]` — provided the query's *type* is
the Σ's domain.  That is what the typed approximant gives: the Σ-shape's
graph labels are all `≡ A[σ]`, and a lookup that reaches a non-`⊥` output
went through one of them.

`sound_graph_lookup` is `sound_beta_lookup` for a codomain graph, Π's or
Σ's: every lookup in it at a label of the domain's type is an approximant
of the codomain at that label, each entry moved there by `IsDefEq.stage`
along its own label equation and the joins by the codomain's
directedness. -/
theorem sound_graph_lookup {Γ Δ : List Term} {A B : Term} {σ ρ} {u : Bool}
    (hΓA : ⊢ (A :: Γ)) (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v)
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ)
    {n} {g : ShapeFun n}
    (hbody : ∀ e ∈ g, Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push e.inp.T) e.out.T)
    {ty tm : Term} {x : TShape} (hx : TShape.WF Δ x)
    (hdir : SoundDir (A :: Γ) B) (hwρ : Valuation.WF Δ ρ)
    (hq : Δ ⊢ tm : ty) (hty : TyEq Δ ty (A.subst σ)) :
    ∀ {c : TShape}, TEvaluates Δ g ty tm x c →
      Interp Δ (A :: Γ) B (σ.cons tm) (ρ.push x) c := by
  have Wtm : Ctx.SubstEq Δ (σ.cons tm) (σ.cons tm) (A :: Γ) :=
    .cons W hA (hty.choose_spec.defeqDF hq)
  intro c hc
  induction hc with
  | bot => exact .bot
  | @entry ej hej hlabj hin =>
    obtain ⟨⟨_, htyj⟩, htmj⟩ := hlabj
    have Wcons : Ctx.SubstEq Δ (σ.cons ej.tm) (σ.cons tm) (A :: Γ) :=
      .cons W hA (hty.choose_spec.defeqDF (htyj.defeqDF htmj))
    exact Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hin⟩)
      (IsDefEq.stage hΓA hB hΔ Wcons (hbody ej hej))
  | lower hle' _ ih => exact ih.mono hΔ hle'.wf hle'
  | join _ _ _ ih₁ ih₂ =>
    exact ((hdir hΔ Wtm (Valuation.WF.push hwρ hx)).join hΔ ih₁ ih₂).2

/-- Directedness of an instantiation, from the two terms' own.

`Interp.inst` reads an approximant of `b[a]` as an approximant of `b` at a
slot approximating `a`, so two of them go to one slot by `a`'s
directedness and then to one shape by `b`'s.  Needed at `beta` (the
lookup's `join` rule lands on two approximants of `b[a]`) and at
`Y_unfold`. -/
theorem dir_inst {Γ : List Term} {A a b : Term} {u : Bool}
    (hA : Γ ⊢ A : .sort u) (ha : Γ ⊢ a : A)
    (iha : SoundDir Γ a) (ihb : SoundDir (A :: Γ) b) : SoundDir Γ (b.inst a) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  have hinst : ∀ {m : TShape}, Interp Δ Γ (b.inst a) σ ρ m ↔
      ∃ x, Interp Δ (A :: Γ) b ((Subst.one a).comp σ) (ρ.push x) m ∧
        Interp Δ Γ a σ ρ x := fun {_} => Interp.inst hΔ (iha hΔ W hwρ) hwρ
  obtain ⟨x₁, hb₁, hx₁⟩ := hinst.1 h₁
  obtain ⟨x₂, hb₂, hx₂⟩ := hinst.1 h₂
  obtain ⟨x, hwx, hx, hxle₁, hxle₂⟩ := iha hΔ W hwρ hx₁ hx₂
  have W' : Ctx.SubstEq Δ ((Subst.one a).comp σ) ((Subst.one a).comp σ) (A :: Γ) := by
    rw [Subst.one_comp]; exact .cons W hA (ha.subst hΔ W)
  obtain ⟨s, hws, hs, hs₁, hs₂⟩ := ihb hΔ W' (Valuation.WF.push hwρ hwx)
    (Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hxle₁⟩) hb₁)
    (Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hxle₂⟩) hb₂)
  exact ⟨s, hws, hinst.2 ⟨x, hs, hx⟩, hs₁, hs₂⟩

/-! ## The type of an application

The chain is the one `lam_entry_ty` walks, carrying a *typing* along it.
An approximant of `app f a` is below a lookup in the function's λ-shape at
the argument's label; `HasType.lam` covers that graph by its generator
`g₀`, whose entries' codes are lookups in the Π-shape's graph; and that
graph is covered by the canonical Π-shape's, whose outputs are the
codomain's interpretations.  So each code is a lookup in the canonical
graph at the canonical query, which `sound_graph_lookup` turns into an
approximant of `B` at the stage extended by `a[σ]`, and `Interp.inst`
into one of `B[a]`.

The slot works out, and this is where Π differs from Σ (§4.7b): the
generator sits *below* the λ-entry's input — coverage is a lookup at the
entry's own input — and that input is below the argument's shape, so the
slot the code is read at approximates `a`.  The `pair` clause's dominator
sits above, which is why the same argument does not run at `snd`.

The `join` rule of the lookup lands on two typed shapes, and typing their
join is exactly `SoundJoin` (§5.1) — not only `tr`'s business, as the plan
had it, but every consumer's of a relational lookup.  It is `sound_join`,
proved once and for all. -/
theorem sound_app_ty {Γ : List Term} {A B f a : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) (ha : Γ ⊢ a : A)
    (happ : Γ ⊢ .app f a : B.inst a)
    (hfty : SoundTy Γ f (.forallE A B)) (hBaty : SoundTy Γ (B.inst a) (.sort v))
    (hadir : SoundDir Γ a) (hBdir : SoundDir (A :: Γ) B) :
    SoundTy Γ (.app f a) (B.inst a) := by
  have hjoin : SoundJoin Γ (B.inst a) := sound_join
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
  refine ⟨happ, ?_⟩
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  have hwρ := hAdm.wf
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  have haσ : Δ ⊢ a.subst σ : A.subst σ := ha.subst hΔ W
  cases hm with
  | bot => exact ⟨TShape.bot, .bot, .bot (.bot .sort)⟩
  | @app _ _ _ _ _ _ n g x y A₁ hF hx hev hw hle =>
    obtain ⟨s, hs, hfsty⟩ := hfty.approx hΔ W hAdm hF
    cases hfsty with
    | @lam _ _ _ _ _ _ _ _ _ g₀ hd hfout hwg hwPi hwg₀ hg hg₀ev hg₀ty hdomA =>
      cases hs with
      | @forallE _ _ _ _ nc gc dc _ _ hAint hdty hwf hlab hdomc hbody hwm hlePi =>
        obtain ⟨hPiLab, _, hcov⟩ :=
          TShape.LE.forallE_decomp hΔ hlePi hwPi hwf (TEvaluates.refl hwf.2.2.2)
        -- a lookup in the canonical graph at the canonical query is an
        -- approximant of `B[a]`
        have toI : ∀ {c : TShape},
            TEvaluates Δ gc (A.subst σ) (a.subst σ) x c →
            Interp Δ Γ (B.inst a) σ ρ c := by
          intro c hc
          refine (Interp.inst (A := A) (b := B) hΔ (hadir hΔ W hwρ) hwρ).2 ⟨x, ?_, hx⟩
          rw [Subst.one_comp]
          exact sound_graph_lookup hΓA hA hB hΔ W hbody hx.wf hBdir hwρ haσ
            (TyEq.refl hAσ) hc
        -- the λ-shape's label is the domain, so its entries' labels are too
        have hA₁ : TyEq Δ A₁ (A.subst σ) := hdomA.trans hPiLab.1
        -- the generator's codes, at the canonical query
        have inner : ∀ {ty tm : Term} {xi : TShape}, LabelEq Δ ty tm A₁ (a.subst σ) →
            TShape.LE Δ xi x → ∀ {w : TShape}, TEvaluates Δ (g₀.map (·.1)) ty tm xi w →
              ∃ c, Interp Δ Γ (B.inst a) σ ρ c ∧ TShape.HasType Δ w c := by
          intro ty tm xi hlabq hxi w hw'
          induction hw' with
          | bot => exact ⟨TShape.bot, .bot, .bot (.bot .sort)⟩
          | @entry q hq hlabq' hinq =>
            obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
            have hlabc : LabelEq Δ p.1.ty p.1.tm (A.subst σ) (a.subst σ) :=
              ⟨TyEq.trans (hlabq'.trans hlabq).1 hA₁, (hlabq'.trans hlabq).2⟩
            refine ⟨_, toI (TEvaluates.mono hΔ hlabc (hinq.trans hΔ hxi)
              (TEvaluates.trans hΔ hcov (hg₀ev p hp))), hg₀ty p hp⟩
          | lower hle' _ ih =>
            obtain ⟨c, hIc, hct⟩ := ih
            exact ⟨c, hIc, TShape.HasType.mono_l hΔ hct hle'⟩
          | join hcj _ _ ih₁ ih₂ =>
            obtain ⟨c₁, hI₁, ht₁⟩ := ih₁
            obtain ⟨c₂, hI₂, ht₂⟩ := ih₂
            obtain ⟨c, hwc, hIc, hlc₁, hlc₂⟩ :=
              dir_inst (b := B) hA ha hadir hBdir hΔ W hwρ hI₁ hI₂
            have hcty := hBaty.isType hΔ W hAdm hIc
            exact ⟨c, hIc, hjoin.hasType_join hΔ W hAdm hIc
              (TShape.HasType.mono_r hΔ ht₁ _ hlc₁ hcty)
              (TShape.HasType.mono_r hΔ ht₂ _ hlc₂ hcty) hcj⟩
        -- and the λ-shape's own lookup, entry by entry
        have key : ∀ {w : TShape}, TEvaluates Δ g A₁ (a.subst σ) x w →
            ∃ c, Interp Δ Γ (B.inst a) σ ρ c ∧ TShape.HasType Δ w c := by
          intro w hw'
          induction hw' with
          | bot => exact ⟨TShape.bot, .bot, .bot (.bot .sort)⟩
          | @entry e he hlabe hine => exact inner hlabe hine (hg e he)
          | lower hle' _ ih =>
            obtain ⟨c, hIc, hct⟩ := ih
            exact ⟨c, hIc, TShape.HasType.mono_l hΔ hct hle'⟩
          | join hcj _ _ ih₁ ih₂ =>
            obtain ⟨c₁, hI₁, ht₁⟩ := ih₁
            obtain ⟨c₂, hI₂, ht₂⟩ := ih₂
            obtain ⟨c, hwc, hIc, hlc₁, hlc₂⟩ :=
              dir_inst (b := B) hA ha hadir hBdir hΔ W hwρ hI₁ hI₂
            have hcty := hBaty.isType hΔ W hAdm hIc
            exact ⟨c, hIc, hjoin.hasType_join hΔ W hAdm hIc
              (TShape.HasType.mono_r hΔ ht₁ _ hlc₁ hcty)
              (TShape.HasType.mono_r hΔ ht₂ _ hlc₂ hcty) hcj⟩
        obtain ⟨c, hIc, hct⟩ := key hev
        exact ⟨c, hIc, TShape.HasType.mono_l hΔ hct hle⟩

/-! ## The `app` label

`Interp.app` looks the argument up at the λ-shape's own domain label, so
the query type is pinned at every well-formed valuation: every entry's type
is that label, by `Shape.WF`.  What typing adds, at an admissible stage, is
that the label is the *syntactic* domain `A[σ]` of the function's Π-type:
`HasType.lam` requires the label to agree with the Π-shape's domain, and
the Π-shape approximating `Π A B` is labelled by `A[σ]`.  This is the η
condition of §4.5: a slot of type `Π A B` holds only λ-shapes labelled by
(something definitionally equal to) `A[σ]`, as `λ A (f↑ 0)` is. -/
theorem Interp.lam_label_ty {Γ Γ₀ Δ : List Term} {f A B : Term} {σ ρ}
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    (hty : SoundTy Γ f (.forallE A B))
    {n} {A' : Term} {g : ShapeFun n}
    (hf : Interp Δ Γ f σ ρ (Shape.T (n := n+1) (ShapeS.lam A' g))) :
    TyEq Δ A' (A.subst σ) := by
  obtain ⟨s, hs, hsty⟩ := hty.approx hΔ W hAdm hf
  cases hsty with
  | lam _ _ _ hwPi _ _ _ _ hdom =>
    cases hs with
    | forallE _ _ hwf _ _ _ _ hle =>
      obtain ⟨hPi, _, _⟩ :=
        TShape.LE.forallE_decomp hΔ hle hwPi hwf (TEvaluates.refl hwf.2.2.2)
      exact hdom.trans hPi.1

/-- Every entry of such a λ-shape is at the syntactic domain. -/
theorem Interp.lam_entry_ty {Γ Γ₀ Δ : List Term} {f A B : Term} {σ ρ}
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    (hty : SoundTy Γ f (.forallE A B))
    {n} {A' : Term} {g : ShapeFun n}
    (hf : Interp Δ Γ f σ ρ (Shape.T (n := n+1) (ShapeS.lam A' g)))
    {e : Entry (Shape n)} (he : e ∈ g) : TyEq Δ e.ty (A.subst σ) :=
  ((hf.wf : Shape.WF (n := n+1) Δ (ShapeS.lam A' g)).2.2.2 e he).trans
    (Interp.lam_label_ty hΔ W hAdm hty hf)

/-- The `SoundEq` half of `appDF`: the same shape is read out of the same
graph, at a query whose term has moved along `a ≡ a'`.  The query's *type*
is the λ-shape's label, so the equation has to be transported there, and
`Interp.lam_label_ty` is what says the label is `A[σ]`. -/
theorem sound_app_eq_of {Γ : List Term} {A B f f' a a' : Term}
    (haa' : Γ ⊢ a ≡ a' : A) (hfty : SoundTy Γ f (.forallE A B))
    (ihf : SoundEq Γ f f') (iha : SoundEq Γ a a')
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {m : TShape} (H : Interp Δ Γ (.app f a) σ ρ m) :
    Interp Δ Γ (.app f' a') σ ρ m := by
  cases H with
  | bot => exact .bot
  | app hF hx hev hw hle =>
    have hA₁ := Interp.lam_label_ty hΔ W hAdm hfty hF
    refine .app ((ihf hΔ W hAdm).1 hF) ((iha hΔ W hAdm).1 hx) ?_ hw hle
    exact TEvaluates.mono hΔ
      ⟨hA₁.refl_l, hA₁.choose_spec.symm.defeqDF (haa'.subst hΔ W)⟩
      (TShape.LE.refl hx.wf) hev

/-- The `SoundEq` half of `appDF`. -/
theorem sound_app_eq {Γ : List Term} {A B f f' a a' : Term}
    (hff' : Γ ⊢ f ≡ f' : .forallE A B) (haa' : Γ ⊢ a ≡ a' : A)
    (hfty : SoundTy Γ f (.forallE A B))
    (ihf : SoundEq Γ f f') (iha : SoundEq Γ a a') :
    SoundEq Γ (.app f a) (.app f' a') := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  exact ⟨sound_app_eq_of haa' hfty ihf iha hΔ W hAdm,
    sound_app_eq_of haa'.symm (SoundTy.of_eq hff' ihf hfty) ihf.symm iha.symm hΔ W hAdm⟩

/-! ## The type of a second projection

`sound_app_ty`, transposed.  `Interp.snd` is a lookup in the pair's graph
at the pair's own domain label and at the term `fst p`, so every step of
the application's chain has a counterpart: `HasType.pair` covers that
graph by its generator, whose codes are lookups in the Σ-shape's graph,
and that graph is covered by the canonical Σ-shape's, whose outputs are
the codomain's interpretations.

What makes it run is (β) (§5.1b): the generator sits *below* the pair
entry's input, as λ's does, and that input is below the first component
`x`, which is itself an approximant of `fst p` — the `fst` rule says so.
With the old single second component the code was read at a *dominator*
of `x`, above everything, and §4.7b is the record of why that could not
be repaired. -/
theorem sound_snd_ty {Γ : List Term} {A B p : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v)
    (hfst : Γ ⊢ .fst p : A) (hsnd : Γ ⊢ .snd p : B.inst (.fst p))
    (hpty : SoundTy Γ p (.sigma A B)) (hBfty : SoundTy Γ (B.inst (.fst p)) (.sort v))
    (hfdir : SoundDir Γ (.fst p)) (hBdir : SoundDir (A :: Γ) B) :
    SoundTy Γ (.snd p) (B.inst (.fst p)) := by
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
  have hjoin : SoundJoin Γ (B.inst (.fst p)) := sound_join
  refine ⟨hsnd, ?_⟩
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  have hwρ := hAdm.wf
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  have hfσ : Δ ⊢ (Term.fst p).subst σ : A.subst σ := hfst.subst hΔ W
  cases hm with
  | bot => exact ⟨TShape.bot, .bot, .bot (.bot .sort)⟩
  | @snd _ _ _ _ _ n A₀ x g y hp hev hw hle =>
    obtain ⟨s, hs, hpsty⟩ := hpty.approx hΔ W hAdm hp
    cases hpsty with
    | @pair _ _ _ _ _ _ _ _ _ _ g₀ hd hfout hwp hwSg hxd hwg₀ hg hg₀ev hg₀ty hdomA =>
      cases hs with
      | @sigma _ _ _ _ nc gc dc _ _ hAint hdty hwf hlab hdomc hbody hwm hleSg =>
        obtain ⟨hSgLab, _, hcov⟩ :=
          TShape.LE.sigma_decomp hΔ hleSg hwSg hwf (TEvaluates.refl hwf.2.2.2)
        -- the first component is an approximant of `fst p`
        have hxw : TShape.WF Δ (Shape.T x) := hp.wf.2.2.2.2.2
        have hxI : Interp Δ Γ (.fst p) σ ρ (Shape.T x) :=
          .fst hp hxw (TShape.LE.refl hxw)
        -- a lookup in the canonical graph at the canonical query is an
        -- approximant of `B[fst p]`
        have toI : ∀ {c : TShape},
            TEvaluates Δ gc (A.subst σ) ((Term.fst p).subst σ) (Shape.T x) c →
            Interp Δ Γ (B.inst (.fst p)) σ ρ c := by
          intro c hc
          refine (Interp.inst (A := A) (b := B) hΔ (hfdir hΔ W hwρ) hwρ).2 ⟨Shape.T x, ?_, hxI⟩
          rw [Subst.one_comp]
          exact sound_graph_lookup hΓA hA hB hΔ W hbody hxw hBdir hwρ hfσ
            (TyEq.refl hAσ) hc
        -- the pair's label is the domain, so its entries' labels are too
        have hA₁ : TyEq Δ A₀ (A.subst σ) := hdomA.trans hSgLab.1
        -- the generator's codes, at the canonical query
        have inner : ∀ {ty tm : Term} {xi : TShape},
            LabelEq Δ ty tm A₀ ((Term.fst p).subst σ) →
            TShape.LE Δ xi (Shape.T x) → ∀ {w : TShape},
              TEvaluates Δ (g₀.map (·.1)) ty tm xi w →
              ∃ c, Interp Δ Γ (B.inst (.fst p)) σ ρ c ∧ TShape.HasType Δ w c := by
          intro ty tm xi hlabq hxi w hw'
          induction hw' with
          | bot => exact ⟨TShape.bot, .bot, .bot (.bot .sort)⟩
          | @entry q hq hlabq' hinq =>
            obtain ⟨pe, hpe, rfl⟩ := List.mem_map.1 hq
            have hlabc : LabelEq Δ pe.1.ty pe.1.tm (A.subst σ) ((Term.fst p).subst σ) :=
              ⟨TyEq.trans (hlabq'.trans hlabq).1 hA₁, (hlabq'.trans hlabq).2⟩
            refine ⟨_, toI (TEvaluates.mono hΔ hlabc (hinq.trans hΔ hxi)
              (TEvaluates.trans hΔ hcov (hg₀ev pe hpe))), hg₀ty pe hpe⟩
          | lower hle' _ ih =>
            obtain ⟨c, hIc, hct⟩ := ih
            exact ⟨c, hIc, TShape.HasType.mono_l hΔ hct hle'⟩
          | join hcj _ _ ih₁ ih₂ =>
            obtain ⟨c₁, hI₁, ht₁⟩ := ih₁
            obtain ⟨c₂, hI₂, ht₂⟩ := ih₂
            obtain ⟨c, hwc, hIc, hlc₁, hlc₂⟩ :=
              dir_inst (b := B) hA hfst hfdir hBdir hΔ W hwρ hI₁ hI₂
            have hcty := hBfty.isType hΔ W hAdm hIc
            exact ⟨c, hIc, hjoin.hasType_join hΔ W hAdm hIc
              (TShape.HasType.mono_r hΔ ht₁ _ hlc₁ hcty)
              (TShape.HasType.mono_r hΔ ht₂ _ hlc₂ hcty) hcj⟩
        -- and the pair's own lookup, entry by entry
        have key : ∀ {w : TShape}, TEvaluates Δ g A₀ ((Term.fst p).subst σ) (Shape.T x) w →
            ∃ c, Interp Δ Γ (B.inst (.fst p)) σ ρ c ∧ TShape.HasType Δ w c := by
          intro w hw'
          induction hw' with
          | bot => exact ⟨TShape.bot, .bot, .bot (.bot .sort)⟩
          | @entry e he hlabe hine => exact inner hlabe hine (hg e he)
          | lower hle' _ ih =>
            obtain ⟨c, hIc, hct⟩ := ih
            exact ⟨c, hIc, TShape.HasType.mono_l hΔ hct hle'⟩
          | join hcj _ _ ih₁ ih₂ =>
            obtain ⟨c₁, hI₁, ht₁⟩ := ih₁
            obtain ⟨c₂, hI₂, ht₂⟩ := ih₂
            obtain ⟨c, hwc, hIc, hlc₁, hlc₂⟩ :=
              dir_inst (b := B) hA hfst hfdir hBdir hΔ W hwρ hI₁ hI₂
            have hcty := hBfty.isType hΔ W hAdm hIc
            exact ⟨c, hIc, hjoin.hasType_join hΔ W hAdm hIc
              (TShape.HasType.mono_r hΔ ht₁ _ hlc₁ hcty)
              (TShape.HasType.mono_r hΔ ht₂ _ hlc₂ hcty) hcj⟩
        obtain ⟨c, hIc, hct⟩ := key hev
        exact ⟨c, hIc, TShape.HasType.mono_l hΔ hct hle⟩

/-- The Σ analogue of `Interp.lam_label_ty`: a typed approximant of a
Σ-typed term is labelled by the syntactic domain. -/
theorem Interp.pair_label_ty {Γ Γ₀ Δ : List Term} {p A B : Term} {σ ρ}
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    (hty : SoundTy Γ p (.sigma A B))
    {n} {A₀ : Term} {x : Shape n} {g : ShapeFun n}
    (hp : Interp Δ Γ p σ ρ (Shape.T (n := n+1) (ShapeS.pair A₀ x g))) :
    TyEq Δ A₀ (A.subst σ) := by
  obtain ⟨s, hs, hsty⟩ := hty.approx hΔ W hAdm hp
  cases hsty with
  | pair _ _ _ hwSg _ _ _ _ _ hdom =>
    cases hs with
    | sigma _ _ hwf _ _ _ _ hle =>
      obtain ⟨hSg, _, _⟩ :=
        TShape.LE.sigma_decomp hΔ hle hwSg hwf (TEvaluates.refl hwf.2.2.2)
      exact hdom.trans hSg.1

/-- The `SoundEq` half of `sndDF`: the same shape is read out of the same
graph, at a query whose term has moved along `fst p ≡ fst p'`.  As at
`app`, the query's *type* is the pair's own label, so the equation is
transported there by `Interp.pair_label_ty`. -/
theorem sound_snd_eq_of {Γ : List Term} {A B p p' : Term} {u v : Bool}
    (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) (hpp' : Γ ⊢ p ≡ p' : .sigma A B)
    (hpty : SoundTy Γ p (.sigma A B)) (ihp : SoundEq Γ p p')
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {m : TShape} (H : Interp Δ Γ (.snd p) σ ρ m) :
    Interp Δ Γ (.snd p') σ ρ m := by
  cases H with
  | bot => exact .bot
  | snd hp hev hw hle =>
    have hA₀ := Interp.pair_label_ty hΔ W hAdm hpty hp
    refine .snd ((ihp hΔ W hAdm).1 hp) ?_ hw hle
    exact TEvaluates.mono hΔ
      ⟨hA₀.refl_l, hA₀.choose_spec.symm.defeqDF
        ((IsDefEq.fstDF hA hB hpp').subst hΔ W)⟩
      (TShape.LE.refl (TShape.WF.T.2 hp.wf.2.2.2.2.2)) hev

/-- The `SoundEq` half of `sndDF`. -/
theorem sound_snd_eq {Γ : List Term} {A B p p' : Term} {u v : Bool}
    (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) (hpp' : Γ ⊢ p ≡ p' : .sigma A B)
    (hpty : SoundTy Γ p (.sigma A B)) (ihp : SoundEq Γ p p') :
    SoundEq Γ (.snd p) (.snd p') := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  exact ⟨sound_snd_eq_of hA hB hpp' hpty ihp hΔ W hAdm,
    sound_snd_eq_of hA hB hpp'.symm (SoundTy.of_eq hpp' ihp hpty) ihp.symm hΔ W hAdm⟩

/-! ## The identity type

`Interp.id` is **label-only**: the interpretation of `.id r A a b` is the
set of shapes below one fixed `id`-shape, whose label is the stage's
substitution instance of `(A, a, b)`.  So all three conclusions come from
that one shape, as for the atoms — the difference is only that the shape
depends on the stage, which `sound_atom`/`dir_atom` do not allow. -/

/-- The canonical `id`-shape at a stage, and its well-formedness. -/
theorem Shape.WF.id_of {Γ Δ : List Term} {σ} {A a b : Term} {u : Bool} {r : Bool}
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ)
    (hA : Γ ⊢ A : .sort u) (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : A) :
    Shape.WF (n := 1) Δ (ShapeS.id r (A.subst σ) (a.subst σ) (b.subst σ)) :=
  ⟨⟨u, hA.subst hΔ W⟩, ha.subst hΔ W, hb.subst hΔ W⟩

/-- The two `id`-shapes of a congruence are order-equivalent: the clause
compares their labels up to definitional equality, which is exactly what
the premises give. -/
theorem TShape.LE.id_of {Γ Δ : List Term} {σ} {A A' a a' b b' : Term} {u r : Bool}
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ)
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (haa' : Γ ⊢ a ≡ a' : A) (hbb' : Γ ⊢ b ≡ b' : A) :
    TShape.LE Δ (Shape.T (n := 1) (ShapeS.id r (A.subst σ) (a.subst σ) (b.subst σ)))
      (Shape.T (n := 1) (ShapeS.id r (A'.subst σ) (a'.subst σ) (b'.subst σ))) :=
  TShape.LE.T.2 ⟨rfl, ⟨u, hAA'.subst hΔ W⟩, haa'.subst hΔ W, hbb'.subst hΔ W⟩

/-- Soundness for `idDF`.  Both directions of `SoundEq` are the same
`LE.trans`, run on the mirrored premises. -/
theorem sound_id {Γ : List Term} {A A' a a' b b' : Term} {u r : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (haa' : Γ ⊢ a ≡ a' : A) (hbb' : Γ ⊢ b ≡ b' : A) :
    SoundEq Γ (.id r A a b) (.id r A' a' b') ∧ SoundTy Γ (.id r A a b) (.sort r) := by
  have hAA'' : Γ ⊢ A' ≡ A : .sort u := hAA'.symm
  have haa'' : Γ ⊢ a' ≡ a : A' := hAA'.defeqDF haa'.symm
  have hbb'' : Γ ⊢ b' ≡ b : A' := hAA'.defeqDF hbb'.symm
  constructor
  · intro Δ Γ₀ σ ρ hΔ W _ m
    constructor
    · intro h
      cases h with
      | bot => exact .bot
      | id hw hle => exact .id hw (hle.trans hΔ (TShape.LE.id_of hΔ W hAA' haa' hbb'))
    · intro h
      cases h with
      | bot => exact .bot
      | id hw hle => exact .id hw (hle.trans hΔ (TShape.LE.id_of hΔ W hAA'' haa'' hbb''))
  · refine ⟨.idDF hAA'.hasType.1 haa'.hasType.1 hbb'.hasType.1, ?_⟩
    intro Δ Γ₀ σ ρ hΔ W _ m h
    refine ⟨TShape.sort r, Interp.sort', ?_⟩
    cases h with
    | bot => exact .bot .sort
    | id hw hle =>
      exact TShape.HasType.mono_l hΔ
        (.id (by cases r <;> decide)
          (Shape.WF.id_of hΔ W hAA'.hasType.1 haa'.hasType.1 hbb'.hasType.1)) hle

/-- Directedness for `.id`: the canonical shape bounds everything. -/
theorem dir_id {Γ : List Term} {A a b : Term} {u r : Bool}
    (hA : Γ ⊢ A : .sort u) (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : A) :
    SoundDir Γ (.id r A a b) := by
  intro Δ σ ρ hΔ W _ m₁ m₂ h₁ h₂
  have hw : TShape.WF Δ (Shape.T (n := 1) (ShapeS.id r (A.subst σ) (a.subst σ) (b.subst σ))) :=
    Shape.WF.id_of hΔ W hA ha hb
  refine ⟨_, hw, .id hw (TShape.LE.refl hw), ?_, ?_⟩
  · cases h₁ with
    | bot => exact TShape.bot_le' rfl
    | id _ hle => exact hle
  · cases h₂ with
    | bot => exact TShape.bot_le' rfl
    | id _ hle => exact hle

/-! ## The two unary formers

`.succ N` and `.refl a` wrap their argument's shape, so directedness is
their argument's: the bound is the wrapper applied to the argument's
bound, and `TShape.LE.succ_of` / `refl_of` carry the order through. -/

/-- Soundness for `succDF`.  `SoundEq` is the argument's, clause by
clause; `SoundTy` needs the argument's shape to be a numeral, which is
`TShape.HasType.isNumeral` applied to its own typing at `nat`. -/
theorem sound_succ {Γ : List Term} {N N' : Term}
    (ihe : SoundEq Γ N N') (ihty : SoundTy Γ N .nat) :
    SoundEq Γ (.succ N) (.succ N') ∧ SoundTy Γ (.succ N) .nat := by
  constructor
  · intro Δ Γ₀ σ ρ hΔ W hAdm m
    constructor
    · intro h
      cases h with
      | bot => exact .bot
      | succ hv hw hle => exact .succ ((ihe hΔ W hAdm).1 hv) hw hle
    · intro h
      cases h with
      | bot => exact .bot
      | succ hv hw hle => exact .succ ((ihe hΔ W hAdm).2 hv) hw hle
  · refine ⟨.succDF ihty.typed, ?_⟩
    intro Δ Γ₀ σ ρ hΔ W hAdm m hm
    refine ⟨TShape.nat, Interp.nat', ?_⟩
    cases hm with
    | bot => exact .bot .nat
    | succ hv _ hle =>
      obtain ⟨c, hc, hvc⟩ := ihty.approx hΔ W hAdm hv
      exact TShape.HasType.mono_l hΔ
        (.succ (TShape.HasType.isNumeral hΔ (Interp.le_nat hc) hvc)) hle

/-- Soundness for `reflDF`.  At `r = false` only `bot` interprets `.refl`,
and `bot` is typed at anything that is a type; at `r = true` the `refl`
clause's bound is the `id`-shape itself. -/
theorem sound_refl {Γ : List Term} {A a a' : Term} {u r : Bool}
    (hA : Γ ⊢ A : .sort u) (haa' : Γ ⊢ a ≡ a' : A)
    (hid : Γ ⊢ Term.id r A a a : .sort r) (ihe : SoundEq Γ a a') :
    SoundEq Γ (.refl r a) (.refl r a') ∧ SoundTy Γ (.refl r a) (.id r A a a) := by
  constructor
  · intro Δ Γ₀ σ ρ hΔ W hAdm m
    constructor
    · intro h
      cases h with
      | bot => exact .bot
      | refl hv hw hle => exact .refl ((ihe hΔ W hAdm).1 hv) hw hle
    · intro h
      cases h with
      | bot => exact .bot
      | refl hv hw hle => exact .refl ((ihe hΔ W hAdm).2 hv) hw hle
  · refine ⟨.reflDF hA haa'.hasType.1 hid, ?_⟩
    intro Δ Γ₀ σ ρ hΔ W hAdm m hm
    have hwid : TShape.WF Δ
        (Shape.T (n := 1) (ShapeS.id r (A.subst σ) (a.subst σ) (a.subst σ))) :=
      Shape.WF.id_of hΔ W hA haa'.hasType.1 haa'.hasType.1
    have hidty : TShape.HasType Δ
        (Shape.T (n := 1) (ShapeS.id r (A.subst σ) (a.subst σ) (a.subst σ))) TShape.type :=
      .id (Bool.le_true' r) hwid
    refine ⟨_, .id hwid (TShape.LE.refl hwid), ?_⟩
    cases hm with
    | bot => exact .bot hidty
    | refl hv hw hle =>
      exact TShape.HasType.mono_l hΔ
        (.refl hv.wf (TShape.LE.refl hwid) hidty) hle

/-- Directedness for `.succ`: the other repo's `succ_isDirected`. -/
theorem dir_succ {Γ : List Term} {N : Term} (h : SoundDir Γ N) : SoundDir Γ (.succ N) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | succ hv₁ _ hle₁ =>
    cases h₂ with
    | bot =>
      refine ⟨_, ?_, ?_, hle₁, TShape.bot_le' rfl⟩
      · exact hv₁.wf
      · exact .succ hv₁ hv₁.wf (TShape.LE.refl hv₁.wf)
    | succ hv₂ _ hle₂ =>
      obtain ⟨z, hwz, hz, hz₁, hz₂⟩ := h hΔ W hwρ hv₁ hv₂
      refine ⟨_, ?_, ?_, hle₁.trans hΔ (TShape.LE.succ_of hΔ hz₁),
        hle₂.trans hΔ (TShape.LE.succ_of hΔ hz₂)⟩
      · exact hwz
      · exact .succ hz hwz (TShape.LE.refl hwz)

/-- Above a `succ`-shape there is only a `succ`-shape. -/
theorem TShape.LE.succ_ub {Δ : List Term} {n} {v : Shape n} {z : TShape}
    (h : TShape.LE Δ (Shape.T (n := n+1) (ShapeS.succ v)) z) :
    ∃ (k : Nat) (w : Shape k), z = Shape.T (n := k+1) (ShapeS.succ w) := by
  obtain ⟨j, t⟩ := z
  obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ h
  cases j with
  | zero => cases t <;> exact absurd h2 (fun x => x)
  | succ j =>
    cases t with
    | succ w => exact ⟨j, w, rfl⟩
    | _ => exact absurd h2 (fun x => x)

/-- And the order between two of them is the order between their
predecessors: the converse of `TShape.LE.succ_of`. -/
theorem TShape.LE.succ_decomp {Δ : List Term} (hΔ : ⊢ Δ) {n k} {v : Shape n} {w : Shape k}
    (h : TShape.LE Δ (Shape.T (n := n+1) (ShapeS.succ v))
      (Shape.T (n := k+1) (ShapeS.succ w))) : TShape.LE Δ v.T w.T := by
  obtain ⟨M, hkM, hnM, h2⟩ := TShape.LE.at_succ h
  exact (TShape.LE.def hΔ (Nat.le_of_succ_le_succ hnM) hkM).2 h2

/-- No shape is above both `zero` and a `succ`. -/
theorem TShape.LE.zero_succ_absurd {Δ : List Term} {n} {v : Shape n} {z : TShape}
    (h₁ : TShape.LE Δ TShape.zero z)
    (h₂ : TShape.LE Δ (Shape.T (n := n+1) (ShapeS.succ v)) z) : False := by
  obtain ⟨j, t⟩ := z
  obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ h₁
  obtain ⟨M', _, _, h2'⟩ := TShape.LE.src_succ h₂
  cases j with
  | zero => cases t <;> exact absurd h2 (fun x => x)
  | succ j => cases t <;> first | exact absurd h2 (fun x => x) | exact absurd h2' (fun x => x)

/-- A `succ`-shape is not below `zero`. -/
theorem TShape.LE.succ_zero_absurd {Δ : List Term} {n} {v : Shape n}
    (h : TShape.LE Δ (Shape.T (n := n+1) (ShapeS.succ v)) TShape.zero) : False := by
  obtain ⟨_, _, _, h2⟩ := TShape.LE.src_succ h
  exact absurd h2 (fun x => x)

/-- Nor is `zero` below a `succ`-shape. -/
theorem TShape.LE.zero_succ_absurd' {Δ : List Term} {n} {v : Shape n}
    (h : TShape.LE Δ TShape.zero (Shape.T (n := n+1) (ShapeS.succ v))) : False := by
  obtain ⟨_, _, _, h2⟩ := TShape.LE.src_succ h
  exact absurd h2 (fun x => x)

/-- Directedness for `.natCase`.

Three cases have content.  Two `zero` branches join by `a`'s
directedness; a `zero` branch against a `succ` branch is impossible,
since `M` would have two incompatible interpretations (`zero_succ_absurd`)
and its own directedness says it does not; and two `succ` branches carry
two label terms for the body's binder, each `M[σ]`'s predecessor, which
`IsDefEq.succ_inj` identifies — that is the one place this needs a
syntactic inversion, and it is a syntactic theorem, not a consequence of
soundness. -/
theorem dir_natCase {Γ : List Term} {C M a b B : Term} (hΓ : ⊢ Γ)
    (hb : Term.nat :: Γ ⊢ b : B)
    (ihM : SoundDir Γ M) (iha : SoundDir Γ a) (ihb : SoundDir (Term.nat :: Γ) b) :
    SoundDir Γ (.natCase C M a b) := by
  have hΓN : ⊢ (Term.nat :: Γ) := ⟨hΓ, _, .nat⟩
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | natCase_zero hM₁ hz₁ ha₁ =>
    cases h₂ with
    | bot => exact ⟨_, ha₁.wf, .natCase_zero hM₁ hz₁ ha₁, TShape.LE.refl ha₁.wf,
        TShape.bot_le' rfl⟩
    | natCase_zero _ _ ha₂ =>
      obtain ⟨s, hws, hs, hs₁, hs₂⟩ := iha hΔ W hwρ ha₁ ha₂
      exact ⟨s, hws, .natCase_zero hM₁ hz₁ hs, hs₁, hs₂⟩
    | natCase_succ hM₂ _ _ _ =>
      obtain ⟨_, hwz, _, hz₁, hz₂⟩ := ihM hΔ W hwρ hM₁ hM₂
      exact absurd (TShape.LE.zero_succ_absurd hz₁ hz₂) not_false
  | @natCase_succ _ _ _ _ _ _ _ _ n₁ v₁ t₁ hM₁ hwv₁ heq₁ hbody₁ =>
    cases h₂ with
    | bot => exact ⟨_, hbody₁.wf, .natCase_succ hM₁ hwv₁ heq₁ hbody₁,
        TShape.LE.refl hbody₁.wf, TShape.bot_le' rfl⟩
    | natCase_zero hM₂ _ _ =>
      obtain ⟨_, hwz, _, hz₁, hz₂⟩ := ihM hΔ W hwρ hM₁ hM₂
      exact absurd (TShape.LE.zero_succ_absurd hz₂ hz₁) not_false
    | @natCase_succ _ _ _ _ _ _ _ _ n₂ v₂ t₂ hM₂ hwv₂ heq₂ hbody₂ =>
      -- one `succ`-shape above both, so one slot above both predecessors
      obtain ⟨z, hwz, hz, hz₁, hz₂⟩ := ihM hΔ W hwρ hM₁ hM₂
      obtain ⟨k, w, rfl⟩ := TShape.LE.succ_ub hz₁
      have hv₁ := TShape.LE.succ_decomp hΔ hz₁
      have hv₂ := TShape.LE.succ_decomp hΔ hz₂
      -- the two label terms are one, by `succ` injectivity
      have ht : Δ ⊢ t₂ ≡ t₁ : Term.nat := IsDefEq.succ_inj hΔ (heq₁.symm.trans heq₂).symm
      have Wcons : Ctx.SubstEq Δ (σ.cons t₂) (σ.cons t₁) (Term.nat :: Γ) :=
        .cons W .nat ht
      have Wdiag : Ctx.SubstEq Δ (σ.cons t₁) (σ.cons t₁) (Term.nat :: Γ) :=
        .cons W .nat ht.hasType.2
      have hbody₂' := IsDefEq.stage hΓN hb hΔ Wcons hbody₂
      -- both bodies at that one slot, and joined there
      have hB₁ := Interp.mono_val hΔ (Valuation.LE.push.2
        ⟨Valuation.LE.refl hwρ, hv₁⟩) hbody₁
      have hB₂ := Interp.mono_val hΔ (Valuation.LE.push.2
        ⟨Valuation.LE.refl hwρ, hv₂⟩) hbody₂'
      have hww : TShape.WF Δ w.T := hwz
      obtain ⟨s, hws, hs, hs₁, hs₂⟩ :=
        ihb hΔ Wdiag (Valuation.WF.push hwρ hww) hB₁ hB₂
      exact ⟨s, hws, .natCase_succ hz hww heq₁ hs, hs₁, hs₂⟩

/-- Directedness for `.Y`.

The fixed point's rule refers to the relation it is defining, so the two
derivations are two towers of unfoldings and the argument is an induction
on the first one: its own sub-derivation's induction hypothesis, applied
to the second derivation's sub-derivation, gives a slot above both, and
the two bodies — which sit at those two slots and at *one* stage, since
the label term `(Y A b)[σ]` is the term itself and not a probe — join
there by the body's directedness.

No typing of the tower is used: `Interp.Y` carries none.  The two typing
hypotheses here are only to name the stage `σ.cons ((Y A b)[σ])` as a
substitution into `A :: Γ`, which is what lets the body's `SoundDir` be
applied at all. -/
theorem dir_Y_aux {Δ : List Term} (hΔ : ⊢ Δ) {Γ : List Term} {t : Term} {σ ρ} {m₁ : TShape}
    (h₁ : Interp Δ Γ t σ ρ m₁) :
    ∀ {A b : Term}, t = .Y A b → Valuation.WF Δ ρ →
      Ctx.SubstEq Δ (σ.cons ((A.Y b).subst σ)) (σ.cons ((A.Y b).subst σ)) (A :: Γ) →
      SoundDir (A :: Γ) b → ∀ {m₂}, Interp Δ Γ t σ ρ m₂ →
        ∃ s, TShape.WF Δ s ∧ Interp Δ Γ t σ ρ s ∧ TShape.LE Δ m₁ s ∧ TShape.LE Δ m₂ s := by
  induction h₁ with
  | @Y _ _ _ _ _ _ _ hx₁ hwx₁ hbody₁ ihx₁ _ =>
    rintro A b ⟨⟩ hwρ WY ihb m₂ h₂
    cases h₂ with
    | bot =>
      exact ⟨_, hbody₁.wf, .Y hx₁ hwx₁ hbody₁, TShape.LE.refl hbody₁.wf, TShape.bot_le' rfl⟩
    | Y hx₂ hwx₂ hbody₂ =>
      -- one tower above both, by the first derivation's own induction
      obtain ⟨z, hwz, hz, hz₁, hz₂⟩ := ihx₁ rfl hwρ WY ihb hx₂
      -- and the two bodies at that one slot
      obtain ⟨s, hws, hs, hs₁, hs₂⟩ := ihb hΔ WY (Valuation.WF.push hwρ hwz)
        (Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hz₁⟩) hbody₁)
        (Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hz₂⟩) hbody₂)
      exact ⟨s, hws, .Y hz hwz hs, hs₁, hs₂⟩
  | bot =>
    exact fun _ _ _ _ _ h₂ => ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | _ => intro A b hne; cases hne

theorem dir_Y {Γ : List Term} {A b : Term} {u : Bool} (hA : Γ ⊢ A : .sort u)
    (hY : Γ ⊢ .Y A b : A) (ihb : SoundDir (A :: Γ) b) : SoundDir Γ (.Y A b) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  exact dir_Y_aux hΔ h₁ rfl hwρ (.cons W hA (hY.subst hΔ W)) ihb h₂

/-- Directedness for `.refl`.  At `r = false` there is no `refl` rule and
`cases` leaves only `bot`, so the statement needs no side condition. -/
theorem dir_refl {Γ : List Term} {a : Term} {r : Bool} (h : SoundDir Γ a) :
    SoundDir Γ (.refl r a) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | refl hv₁ _ hle₁ =>
    cases h₂ with
    | bot =>
      refine ⟨_, ?_, ?_, hle₁, TShape.bot_le' rfl⟩
      · exact hv₁.wf
      · exact .refl hv₁ hv₁.wf (TShape.LE.refl hv₁.wf)
    | refl hv₂ _ hle₂ =>
      obtain ⟨z, hwz, hz, hz₁, hz₂⟩ := h hΔ W hwρ hv₁ hv₂
      refine ⟨_, ?_, ?_, hle₁.trans hΔ (TShape.LE.refl_of hΔ hz₁),
        hle₂.trans hΔ (TShape.LE.refl_of hΔ hz₂)⟩
      · exact hwz
      · exact .refl hz hwz (TShape.LE.refl hwz)

/-- Above a `refl`-shape there is only a `refl`-shape, and the order
between two of them is the order between their witnesses — `succ_ub` and
`succ_decomp` for the other unary former. -/
theorem TShape.LE.refl_ub {Δ : List Term} {n} {v : Shape n} {z : TShape}
    (h : TShape.LE Δ (Shape.T (n := n+1) (ShapeS.refl v)) z) :
    ∃ (k : Nat) (w : Shape k), z = Shape.T (n := k+1) (ShapeS.refl w) := by
  obtain ⟨j, t⟩ := z
  obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ h
  cases j with
  | zero => cases t <;> exact absurd h2 (fun x => x)
  | succ j =>
    cases t with
    | refl w => exact ⟨j, w, rfl⟩
    | _ => exact absurd h2 (fun x => x)

theorem TShape.LE.refl_decomp {Δ : List Term} (hΔ : ⊢ Δ) {n k} {v : Shape n} {w : Shape k}
    (h : TShape.LE Δ (Shape.T (n := n+1) (ShapeS.refl v))
      (Shape.T (n := k+1) (ShapeS.refl w))) : TShape.LE Δ v.T w.T := by
  obtain ⟨M, hkM, hnM, h2⟩ := TShape.LE.at_succ h
  exact (TShape.LE.def hΔ (Nat.le_of_succ_le_succ hnM) hkM).2 h2

/-- **Directedness for `.tr`** — the case the plan called open, and the
one consumer of `SoundJoin`.

Everything in the `tr` clause is joined slotwise: the witness shape `v`
(which interprets both endpoints, so it is the *join*, not an upper
bound, taken twice), the type `vA`, the motive's value `cb` at the joined
slot, and the transported shape `m'`.  Three of the clause's premises are
typings, and each is a subject join at one type: `v` at `vA₁ ⊔ vA₂`, `cb`
at `type`, `m'` at `cb₁ ⊔ cb₂` — `TShape.HasType.join`, which is why this
case waited for it.  The proof premise is moved by `H`'s own
directedness: a shape above two `refl`s is a `refl`, above both
witnesses. -/
theorem dir_tr {Γ : List Term} {r : Bool} {A a b C X H : Term} {u : Bool} (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A : .sort u) (hb : Γ ⊢ b : A)
    (ihA : SoundDir Γ A) (iha : SoundDir Γ a) (ihb : SoundDir Γ b)
    (ihC : SoundDir (A :: Γ) C) (ihX : SoundDir Γ X) (ihH : SoundDir Γ H) :
    SoundDir Γ (.tr r A a b C X H) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | tr hw₁ hle₁ hX₁ ha₁ hb₁ hA₁ hwv₁ hvA₁ hC₁ hcb₁ hm'₁ hH₁ heq₁ =>
    cases h₂ with
    | bot =>
      exact ⟨_, hX₁.wf, .tr hX₁.wf (TShape.LE.refl hX₁.wf) hX₁ ha₁ hb₁ hA₁ hwv₁ hvA₁
        hC₁ hcb₁ hm'₁ hH₁ heq₁, hle₁, TShape.bot_le' rfl⟩
    | tr hw₂ hle₂ hX₂ ha₂ hb₂ hA₂ hwv₂ hvA₂ hC₂ hcb₂ hm'₂ hH₂ _ =>
      -- the witness: the join interprets both endpoints
      have ⟨hcv, hav⟩ := Interp.Dir.join hΔ (iha hΔ W hwρ) ha₁ ha₂
      have ⟨_, hbv⟩ := Interp.Dir.join hΔ (ihb hΔ W hwρ) hb₁ hb₂
      have hwv := TShape.WF.join hΔ hcv hwv₁ hwv₂
      have hvle := TShape.le_join hΔ hwv₁ hwv₂ hcv
      -- its type
      have ⟨hcA, hAv⟩ := Interp.Dir.join hΔ (ihA hΔ W hwρ) hA₁ hA₂
      have hvAty := TShape.HasType.join hΔ hcA hvA₁.isType hvA₂.isType
      have hvAle := TShape.le_join hΔ hvA₁.isType.wf.1 hvA₂.isType.wf.1 hcA
      have hty : TShape.HasType Δ _ _ := TShape.HasType.join hΔ hcv
        (hvA₁.mono_r hΔ _ hvAle.1 hvAty) (hvA₂.mono_r hΔ _ hvAle.2 hvAty)
      -- the motive, at the joined slot
      have WA : Ctx.SubstEq Δ (σ.cons (b.subst σ)) (σ.cons (b.subst σ)) (A :: Γ) :=
        .cons W hA (hb.subst hΔ W)
      have hC₁' := Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hvle.1⟩) hC₁
      have hC₂' := Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hvle.2⟩) hC₂
      have ⟨hccb, hcbv⟩ :=
        Interp.Dir.join hΔ (ihC hΔ WA (Valuation.WF.push hwρ hwv)) hC₁' hC₂'
      have hcbty := TShape.HasType.join hΔ hccb hcb₁ hcb₂
      have hcble := TShape.le_join hΔ hcb₁.wf.1 hcb₂.wf.1 hccb
      -- the transported shape
      have ⟨hcm, hXv⟩ := Interp.Dir.join hΔ (ihX hΔ W hwρ) hX₁ hX₂
      have hm'ty := TShape.HasType.join hΔ hcm
        (hm'₁.mono_r hΔ _ hcble.1 hcbty) (hm'₂.mono_r hΔ _ hcble.2 hcbty)
      have hm'le := TShape.le_join hΔ hm'₁.wf.1 hm'₂.wf.1 hcm
      -- and the proof premise, by `H`'s own directedness
      have hwm' := TShape.WF.join hΔ hcm hm'₁.wf.1 hm'₂.wf.1
      refine ⟨_, hwm', .tr hwm' (TShape.LE.refl hwm')
          hXv hav hbv hAv hwv hty hcbv hcbty hm'ty ?_ heq₁,
        hle₁.trans hΔ hm'le.1, hle₂.trans hΔ hm'le.2⟩
      intro hr
      obtain ⟨s, hws, hs, hs₁, hs₂⟩ := ihH hΔ W hwρ (hH₁ hr) (hH₂ hr)
      obtain ⟨k, w, rfl⟩ := TShape.LE.refl_ub hs₁
      exact Interp.mono hΔ hwv
        (TShape.LE.refl_of hΔ (TShape.join_le hΔ (TShape.LE.refl_decomp hΔ hs₁)
          (TShape.LE.refl_decomp hΔ hs₂))) hs

/-! ## β

The rule is padded with typings of both sides, so only `SoundEq` has
content (the other repo's `of_typings` observation).

`→` is the graph lookup unfolded: the function's λ-shape is covered by the
rule's own graph, each of whose entries carries the body at the entry's
label and input, and the entry's label is definitionally the argument, so
`IsDefEq.stage` puts the body at the argument's stage and `Interp.inst`
reads it as an approximant of `e[e']`.  The lookup's `join` rule lands on
two of those, which is why `dir_inst` is needed.  No typing of the input
is used: the body is evaluated at the entry's own input.

`←` builds the one-entry λ-shape `[(A[σ], e'[σ], x, m)]` and looks `m` up
in it.  The input is typed because `SoundTy e' A` types *every*
approximant of `e'`, so nothing has to be enlarged. -/

/-- Every lookup in a λ-shape of `lam A e`, at the argument's label, is an
approximant of `e[e']`.  The `→` half of β, with the graph as a
parameter so that the induction on the lookup has something to name. -/
theorem sound_beta_lookup {Γ Δ : List Term} {A B e e' : Term} {σ ρ} {u : Bool}
    (hΓA : ⊢ (A :: Γ)) (hA : Γ ⊢ A : .sort u) (hbe : A :: Γ ⊢ e : B)
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ)
    {n} {g : ShapeFun n} (hwf : Shape.WF (n := n+1) Δ (.lam (A.subst σ) g))
    (hbody : ∀ e₀ ∈ g, Interp Δ (A :: Γ) e (σ.cons e₀.tm) (ρ.push e₀.inp.T) e₀.out.T)
    {x : TShape} (hx : Interp Δ Γ e' σ ρ x)
    (hdir : Interp.Dir Δ Γ (e.inst e') σ ρ)
    (hinst : ∀ {m : TShape}, Interp Δ Γ (e.inst e') σ ρ m ↔
      ∃ x, Interp Δ (A :: Γ) e ((Subst.one e').comp σ) (ρ.push x) m ∧ Interp Δ Γ e' σ ρ x) :
    ∀ {c : TShape}, TEvaluates Δ g (A.subst σ) (e'.subst σ) x c →
      Interp Δ Γ (e.inst e') σ ρ c := by
  intro c hc
  induction hc with
  | bot => exact .bot
  | @entry ej hej hlab hin =>
    have hwe := hwf.2.2.1.1 ej hej
    obtain ⟨⟨_, hty⟩, htm⟩ := hlab
    have Wcons : Ctx.SubstEq Δ (σ.cons ej.tm) (σ.cons (e'.subst σ)) (A :: Γ) :=
      .cons W hA (hty.defeqDF htm)
    refine hinst.2 ⟨ej.inp.T, ?_, hx.mono hΔ hwe.2.2.1 hin⟩
    rw [Subst.one_comp]
    exact IsDefEq.stage hΓA hbe hΔ Wcons (hbody ej hej)
  | lower hle' _ ih => exact ih.mono hΔ hle'.wf hle'
  | join _ _ _ ih₁ ih₂ => exact (hdir.join hΔ ih₁ ih₂).2

theorem sound_beta {Γ : List Term} {A B e e' : Term} {u : Bool}
    (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u) (hbe : A :: Γ ⊢ e : B) (he' : Γ ⊢ e' : A)
    (ihA : SoundTy Γ A (.sort u)) (ihe' : SoundTy Γ e' A)
    (ihe'dir : SoundDir Γ e') (ihedir : SoundDir (A :: Γ) e) :
    SoundEq Γ (.app (.lam A e) e') (e.inst e') := by
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  have hwρ : Valuation.WF Δ ρ := hAdm.wf
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  have he'σ : Δ ⊢ e'.subst σ : A.subst σ := he'.subst hΔ W
  have hinst : ∀ {m : TShape}, Interp Δ Γ (e.inst e') σ ρ m ↔
      ∃ x, Interp Δ (A :: Γ) e ((Subst.one e').comp σ) (ρ.push x) m ∧
        Interp Δ Γ e' σ ρ x := fun {_} => Interp.inst hΔ (ihe'dir hΔ W hwρ) hwρ
  have hdir := dir_inst (b := e) hA he' ihe'dir ihedir hΔ W hwρ
  constructor
  · intro h
    cases h with
    | bot => exact .bot
    | app hF hx hev hw hle =>
      cases hF with
      | lam hAint hd hwf hdom hbody hwlam hlelam =>
        -- the function's λ-shape is covered by the rule's own graph, and
        -- the order makes its label the domain, so the lookup moves there
        have hev' := TEvaluates.trans hΔ
          (TShape.LE.lam_decomp hΔ hlelam hwlam hwf (TEvaluates.refl hwf.2.2.1))
          (TEvaluates.retype (TShape.LE.lam_dom hlelam) hev)
        exact (sound_beta_lookup hΓA hA hbe hΔ W hwf hbody hx hdir hinst hev').mono hΔ hw hle
  · intro h
    obtain ⟨n, s⟩ := m
    by_cases hb : s.IsBot
    · rw [Shape.WF.eq_bot_of_isBot (s := s) h.wf hb]; exact .bot
    · obtain ⟨x, hbody, hx⟩ := hinst.1 h
      obtain ⟨d, hd, hxd⟩ := ihe'.approx hΔ W hAdm hx
      -- one entry, at a level above both the argument's shape and the value
      obtain ⟨k, hkx, hkn⟩ : ∃ k, x.1 ≤ k ∧ n ≤ k :=
        ⟨max x.1 n, Nat.le_max_left .., Nat.le_max_right ..⟩
      have hwx : Shape.WF Δ (x.2.lift k) := (Shape.lift_wf hkx).2 hx.wf
      have hws : Shape.WF Δ (s.lift k) := (Shape.lift_wf hkn).2 h.wf
      have hnb : ¬ (s.lift k).IsBot := fun hbb => hb ((Shape.lift_isBot hkn).1 hbb)
      have hwg : Shape.WF (n := k+1) Δ (.lam (A.subst σ)
          [⟨A.subst σ, e'.subst σ, x.2.lift k, s.lift k⟩]) := by
        refine ⟨by simp, ?_, ⟨?_, ?_⟩, ?_⟩
        · intro e₀ he₀; cases he₀ with | head => exact hnb | tail _ h => nomatch h
        · intro e₀ he₀
          cases he₀ with
          | head => exact ⟨⟨u, hAσ⟩, he'σ, hwx, hws⟩
          | tail _ h => nomatch h
        · intro e₀ he₀ e₁ he₁ Θ τ hΘ Wτ _ _
          cases he₀ with
          | tail _ h => nomatch h
          | head =>
            cases he₁ with
            | tail _ h => nomatch h
            | head => exact (Shape.WF.subst hΘ Wτ hws).coherent
        · intro e₀ he₀
          cases he₀ with | head => exact TyEq.refl hAσ | tail _ h => nomatch h
      have hlam : Interp Δ Γ (.lam A e) σ ρ (Shape.T (n := k+1) (.lam (A.subst σ)
          [⟨A.subst σ, e'.subst σ, x.2.lift k, s.lift k⟩])) := by
        refine .lam hd (ihA.isType hΔ W hAdm hd) hwg ?_ ?_ hwg (TShape.LE.refl hwg)
        · intro e₀ he₀
          cases he₀ with
          | head => exact hxd.lift_subject hΔ hkx
          | tail _ h => nomatch h
        · intro e₀ he₀
          cases he₀ with
          | tail _ h => nomatch h
          | head =>
            refine Interp.lift (m := ⟨n, s⟩) hΔ hkn ?_
            refine Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
              TShape.LE.le_lift hΔ hkx hx.wf⟩) ?_
            rw [← Subst.one_comp]; exact hbody
      exact .app hlam (Interp.lift hΔ hkx hx)
        (.entry ⟨A.subst σ, e'.subst σ, x.2.lift k, s.lift k⟩ (.head _)
          (LabelEq.refl hAσ he'σ) (TShape.LE.refl hwx)) h.wf
        (TShape.LE.le_lift (m := ⟨n, s⟩) hΔ hkn h.wf)

/-! ## The remaining computation rules

`natCase` on a numeral, and the fixed point's unfolding.  Each is padded
with typings of both sides, so only `SoundEq` has content, and in each the
two `Interp` rules line up on the nose: the mismatched pairs are ruled out
because `zero` and a `succ`-shape have no order between them, and the
matching pair is the rule's own premise, modulo the stage move that the
label term forces. -/

/-- `natCase C zero a b` and `a`. -/
theorem sound_natCase_zero {Γ : List Term} {C a b : Term} :
    SoundEq Γ (.natCase C .zero a b) a := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h with
    | bot => exact .bot
    | natCase_zero _ _ ha => exact ha
    | natCase_succ hM _ _ _ =>
      cases hM with
      | zero _ hle => exact absurd (TShape.LE.succ_zero_absurd hle) not_false
  · have hz : TShape.WF Δ TShape.zero := trivial
    exact .natCase_zero (.zero hz (TShape.LE.refl hz)) .zero h

/-- `natCase C (succ n) a b` and `b[n]`. -/
theorem sound_natCase_succ {Γ : List Term} {C a b n : Term}
    (hΓ : ⊢ Γ) (hn : Γ ⊢ n : .nat) (hb : Term.nat :: Γ ⊢ b : B)
    (ihndir : SoundDir Γ n) : SoundEq Γ (.natCase C (.succ n) a b) (b.inst n) := by
  have hΓN : ⊢ (Term.nat :: Γ) := ⟨hΓ, _, .nat⟩
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  have hwρ : Valuation.WF Δ ρ := hAdm.wf
  have hnσ : Δ ⊢ n.subst σ : Term.nat := hn.subst hΔ W
  have hinst : ∀ {m : TShape}, Interp Δ Γ (b.inst n) σ ρ m ↔
      ∃ x, Interp Δ (Term.nat :: Γ) b ((Subst.one n).comp σ) (ρ.push x) m ∧
        Interp Δ Γ n σ ρ x := fun {_} => Interp.inst hΔ (ihndir hΔ W hwρ) hwρ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h with
    | bot => exact .bot
    | natCase_zero hM _ =>
      cases hM with
      | succ _ _ hle => exact absurd (TShape.LE.zero_succ_absurd' hle) not_false
    | natCase_succ hM hwv heq hbody =>
      -- the two labels for the binder are one, by `succ` injectivity
      have ht : Δ ⊢ n.subst σ ≡ _ : Term.nat := IsDefEq.succ_inj hΔ heq
      cases hM with
      | succ hv hw hle =>
        refine hinst.2 ⟨_, ?_, hv.mono hΔ (TShape.WF.T.2 hwv) (TShape.LE.succ_decomp hΔ hle)⟩
        rw [Subst.one_comp]
        refine IsDefEq.stage hΓN hb hΔ ?_ hbody
        exact .cons W .nat ht.symm
  · obtain ⟨x, hbody, hx⟩ := hinst.1 h
    obtain ⟨k, v⟩ := x
    refine .natCase_succ (.succ hx (TShape.WF.T.2 hx.wf) (TShape.LE.refl hx.wf))
      hx.wf (.succDF hnσ) ?_
    rw [← Subst.one_comp]; exact hbody

/-- `Y A b` and its unfolding `b[Y A b]`: the fixed point's rule *is* the
instantiation, so both directions are `Interp.inst` at the tower below. -/
theorem sound_Y_unfold {Γ : List Term} {A b : Term} {u : Bool}
    (hA : Γ ⊢ A : .sort u) (hY : Γ ⊢ .Y A b : A) (ihYdir : SoundDir Γ (.Y A b)) :
    SoundEq Γ (.Y A b) (b.inst (.Y A b)) := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  have hwρ : Valuation.WF Δ ρ := hAdm.wf
  have hinst : ∀ {m : TShape}, Interp Δ Γ (b.inst (.Y A b)) σ ρ m ↔
      ∃ x, Interp Δ (A :: Γ) b ((Subst.one (.Y A b)).comp σ) (ρ.push x) m ∧
        Interp Δ Γ (.Y A b) σ ρ x := fun {_} => Interp.inst hΔ (ihYdir hΔ W hwρ) hwρ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h with
    | bot => exact .bot
    | Y hx hwx hbody =>
      refine hinst.2 ⟨_, ?_, hx⟩
      rw [Subst.one_comp]; exact hbody
  · obtain ⟨x, hbody, hx⟩ := hinst.1 h
    refine .Y hx hx.wf ?_
    rw [← Subst.one_comp]; exact hbody

/-! ## `natCase`, congruence

The two branches are the two premises', and the only work is at `succ`:
the body lives at the stage extended by the label term `t` and at the slot
`v`, so the body's `SoundEq` needs `(σ.cons t)` to be a substitution into
`nat :: Γ` — which `succ_regular` gives, `t` being a `succ`'s argument —
and needs the slot to be **admissible**, i.e. typed at `nat`.  Nothing in
`Interp.natCase_succ` says so; what does is `SoundTy M nat`, through
`HasType.isNumeral`: the shape `succ v` is typed at an approximant of
`⟦nat⟧`, hence a numeral, hence so is `v`. -/
theorem sound_natCase_of {Γ : List Term} {C C' M M' a a' b b' : Term}
    (hMM' : Γ ⊢ M ≡ M' : Term.nat)
    (ihM : SoundEq Γ M M') (ihMty : SoundTy Γ M Term.nat)
    (iha : SoundEq Γ a a') (ihb : SoundEq (Term.nat :: Γ) b b')
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {m : TShape} (H : Interp Δ Γ (.natCase C M a b) σ ρ m) :
    Interp Δ Γ (.natCase C' M' a' b') σ ρ m := by
  cases H with
  | bot => exact .bot
  | natCase_zero hM hz ha =>
    exact .natCase_zero ((ihM hΔ W hAdm).1 hM) (((hMM'.subst hΔ W).symm).trans hz)
      ((iha hΔ W hAdm).1 ha)
  | @natCase_succ _ _ _ _ _ _ _ _ n v t hM hwv heq hbody =>
    -- the label term is a numeral's argument, so it is typed
    have ht : Δ ⊢ t : Term.nat := heq.succ_regular (.inr rfl)
    -- and the slot is typed at `nat`, because `M`'s shape is
    obtain ⟨c, hc, hty⟩ := ihMty.approx hΔ W hAdm hM
    have hvnat : TShape.HasType Δ v.T TShape.nat :=
      (TShape.HasType.isNumeral hΔ (Interp.le_nat hc) hty).pred.hasType
    have Wcons : Ctx.SubstEq Δ (σ.cons t) (σ.cons t) (Term.nat :: Γ) := .cons W .nat ht
    have hAdm' : Adm Δ Γ₀ (Term.nat :: Γ) (σ.cons t) (ρ.push v.T) :=
      .cons hAdm (fun _ hb => TShape.HasType.mono_l hΔ .nat (Interp.le_nat hb))
        Interp.nat' (TShape.WF.T.2 hwv) hvnat
    exact .natCase_succ ((ihM hΔ W hAdm).1 hM) hwv
      (((hMM'.subst hΔ W).symm).trans heq)
      ((ihb hΔ Wcons hAdm').1 hbody)

/-- The `SoundEq` half of `natCaseDF`. -/
theorem sound_natCase {Γ : List Term} {C C' M M' a a' b b' : Term}
    (hMM' : Γ ⊢ M ≡ M' : Term.nat)
    (ihM : SoundEq Γ M M') (ihMty : SoundTy Γ M Term.nat)
    (iha : SoundEq Γ a a') (ihb : SoundEq (Term.nat :: Γ) b b') :
    SoundEq Γ (.natCase C M a b) (.natCase C' M' a' b') := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  exact ⟨sound_natCase_of hMM' ihM ihMty iha ihb hΔ W hAdm,
    sound_natCase_of hMM'.symm ihM.symm (SoundTy.of_eq hMM' ihM ihMty) iha.symm ihb.symm
      hΔ W hAdm⟩

/-- **The type of a `natCase`.**

The type is `C[M]` and each branch is typed at `C` instantiated at a
*different* term — `zero` in one branch, `succ t` in the other — so the
whole content is moving the motive's stage.  Both `Interp` clauses carry
what that takes: the branch's defining equation (`M[σ] ≡ zero`,
`M[σ] ≡ succ t`), which `IsDefEq.stage` turns into a move of the
motive's extended stage, and an approximant of `M` at the branch's own
shape (`zero`, `succ v`), which is the slot `Interp.inst` reads the
motive at.  The `succ` branch is the same argument one weakening up: the
body's type is `C↑[succ #0]`, so the motive comes back by
`Interp.unweak`. -/
theorem sound_natCase_ty {Γ : List Term} {C M a b : Term} {v : Bool} (hΓ : ⊢ Γ)
    (hC : Term.nat :: Γ ⊢ C : .sort v)
    (hnc : Γ ⊢ .natCase C M a b : C.inst M)
    (iha : SoundTy Γ a (C.inst .zero))
    (ihb : SoundTy (Term.nat :: Γ) b ((C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0))))
    (ihMty : SoundTy Γ M Term.nat) (ihMdir : SoundDir Γ M) :
    SoundTy Γ (.natCase C M a b) (C.inst M) := by
  have hΓN : ⊢ (Term.nat :: Γ) := ⟨hΓ, _, .nat⟩
  have hzdir : SoundDir Γ (Term.zero) :=
    dir_atom Interp.le_zero (fun hw h => .zero hw h) trivial
  refine ⟨hnc, ?_⟩
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  have hwρ := hAdm.wf
  cases hm with
  | bot => exact ⟨TShape.bot, .bot, .bot (.bot .sort)⟩
  | natCase_zero hMz hz hma =>
    obtain ⟨c, hc, hct⟩ := iha.approx hΔ W hAdm hma
    obtain ⟨x, hCx, hxz⟩ :=
      (Interp.inst (A := Term.nat) (b := C) hΔ (hzdir hΔ W hwρ) hwρ).1 hc
    rw [Subst.one_comp] at hCx
    have W0 : Ctx.SubstEq Δ (σ.cons (Term.zero.subst σ)) (σ.cons (M.subst σ))
        (Term.nat :: Γ) := .cons W .nat hz.symm
    refine ⟨c, (Interp.inst (A := Term.nat) (b := C) hΔ (ihMdir hΔ W hwρ) hwρ).2
      ⟨x, ?_, Interp.mono hΔ hxz.wf (Interp.le_zero hxz) hMz⟩, hct⟩
    rw [Subst.one_comp]
    exact IsDefEq.stage hΓN hC hΔ W0 hCx
  | @natCase_succ _ _ _ _ _ _ _ _ n w t hMs hwv heq hmb =>
    -- the branch's stage, and that it is admissible
    have ht : Δ ⊢ t : Term.nat := heq.succ_regular (.inr rfl)
    have Wcons : Ctx.SubstEq Δ (σ.cons t) (σ.cons t) (Term.nat :: Γ) := .cons W .nat ht
    obtain ⟨cM, hcM, htyM⟩ := ihMty.approx hΔ W hAdm hMs
    have hvnat : TShape.HasType Δ w.T TShape.nat :=
      (TShape.HasType.isNumeral hΔ (Interp.le_nat hcM) htyM).pred.hasType
    have hwv' : TShape.WF Δ w.T := TShape.WF.T.2 hwv
    have hAdm' : Adm Δ Γ₀ (Term.nat :: Γ) (σ.cons t) (ρ.push w.T) :=
      .cons hAdm (fun _ hb => TShape.HasType.mono_l hΔ .nat (Interp.le_nat hb))
        Interp.nat' hwv' hvnat
    -- the body's type, unfolded one `inst` and one weakening
    obtain ⟨c, hc, hct⟩ := ihb.approx hΔ Wcons hAdm' hmb
    obtain ⟨y, hCy, hsy⟩ := (Interp.inst (A := Term.nat) (b := C.lift' (.cons (.skip .refl)))
      hΔ (dir_succ (dir_bvar (Γ := Term.nat :: Γ)) hΔ Wcons (Valuation.WF.push hwρ hwv'))
      (Valuation.WF.push hwρ hwv')).1 hc
    rw [Subst.one_comp] at hCy
    have hCy' : Interp Δ (Term.nat :: Γ) C (σ.cons ((Term.succ (.bvar 0)).subst (σ.cons t)))
        (ρ.push y) c := by
      have h := Interp.unweak hCy (Γ := Term.nat :: Γ) (t := C) (l := .cons (.skip .refl))
        (ρ := ρ.push y) (fun i => by cases i <;> rfl) rfl
      rwa [← Subst.lift_l_cons, ← Subst.tail_eq_lift_l] at h
    -- `succ #0` at this stage is `succ t`, and the slot is below `succ w`
    have hyle : TShape.LE Δ y (Shape.T (n := n+1) (ShapeS.succ w)) := by
      cases hsy with
      | bot => exact TShape.bot_le' rfl
      | @succ _ _ _ _ _ n' v' hv _ hle =>
        refine hle.trans hΔ (TShape.LE.succ_of hΔ (a := v'.T) (b := w.T) ?_)
        cases hv with
        | bot => exact TShape.bot_le' rfl
        | bvar _ h1 => exact h1
    have W1 : Ctx.SubstEq Δ (σ.cons ((Term.succ (.bvar 0)).subst (σ.cons t)))
        (σ.cons (M.subst σ)) (Term.nat :: Γ) := .cons W .nat heq.symm
    refine ⟨c, (Interp.inst (A := Term.nat) (b := C) hΔ (ihMdir hΔ W hwρ) hwρ).2
      ⟨y, ?_, Interp.mono hΔ hsy.wf hyle hMs⟩, hct⟩
    rw [Subst.one_comp]
    exact IsDefEq.stage hΓN hC hΔ W1 hCy'

/-! ## The fixed point

`Interp.Y` is a tower of unfoldings, so both halves are inductions on the
derivation with the term generalized, as `dir_Y_aux` already is: each
level's induction hypothesis supplies what the next level's stage needs —
for `SoundTy` the typing of the slot (which is what `Adm.cons` asks
for), and for `SoundEq` the inner tower already moved to the other side. -/

/-- The type of a fixed point: the body is typed at `A↑` one slot up, and
`Interp.unweak` brings that back to `A`.  The slot the body is read at is
the previous level of the tower, typed by the induction hypothesis — which
is exactly the `Adm.cons` obligation. -/
theorem sound_Y_ty_aux {Δ : List Term} (hΔ : ⊢ Δ) {Γ₀ Γ : List Term} {t : Term} {σ ρ}
    {m : TShape} (H : Interp Δ Γ t σ ρ m) :
    ∀ {A b : Term} {u : Bool}, t = .Y A b →
      Γ ⊢ A : .sort u → Γ ⊢ .Y A b : A →
      Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ₀ Γ σ ρ →
      SoundTy Γ A (.sort u) → SoundTy (A :: Γ) b A.lift →
      ∃ c, Interp Δ Γ A σ ρ c ∧ TShape.HasType Δ m c := by
  induction H with
  | @Y Γ' σ' ρ' m' A b x hx hwx hbody ihx _ =>
    rintro A' b' u ⟨⟩ hA hY W hAdm ihA ihb
    obtain ⟨cx, hcx, htyx⟩ := ihx rfl hA hY W hAdm ihA ihb
    have WY : Ctx.SubstEq Δ (σ'.cons ((Term.Y A b).subst σ'))
        (σ'.cons ((Term.Y A b).subst σ')) (A :: Γ') := .cons W hA (hY.subst hΔ W)
    have hAdm' : Adm Δ Γ₀ (A :: Γ') (σ'.cons ((Term.Y A b).subst σ')) (ρ'.push _) :=
      .cons hAdm (fun _ hb => ihA.isType hΔ W hAdm hb) hcx hwx htyx
    obtain ⟨c, hc, hct⟩ := ihb.approx hΔ WY hAdm' hbody
    exact ⟨c, Interp.unweak hc (Γ := Γ') (t := A) (l := .skip .refl) (fun i => rfl) rfl, hct⟩
  | bot => exact fun _ _ _ _ _ _ _ => ⟨TShape.bot, .bot, .bot (.bot .sort)⟩
  | _ => intro A b u hne; cases hne

theorem sound_Y_ty {Γ : List Term} {A b : Term} {u : Bool}
    (hA : Γ ⊢ A : .sort u) (hY : Γ ⊢ .Y A b : A)
    (ihA : SoundTy Γ A (.sort u)) (ihb : SoundTy (A :: Γ) b A.lift) :
    SoundTy Γ (.Y A b) A := by
  refine ⟨hY, ?_⟩
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  exact sound_Y_ty_aux hΔ hm rfl hA hY W hAdm ihA ihb

/-- The congruence: the tower moves one level at a time.  The inner
unfolding is the induction hypothesis, the body moves by its own
`SoundEq` (at the *old* context, then `Interp.ctx` to the new one), and
the stage — which names the fixed point itself — moves by
`IsDefEq.stage` along the congruence being proved. -/
theorem sound_Y_eq_aux {Δ : List Term} (hΔ : ⊢ Δ) {Γ₀ Γ : List Term} {t : Term} {σ ρ}
    {m : TShape} (H : Interp Δ Γ t σ ρ m) :
    ∀ {A A' b b' : Term} {u : Bool}, t = .Y A b → ⊢ Γ →
      Γ ⊢ A ≡ A' : .sort u → Γ ⊢ .Y A b : A → Γ ⊢ .Y A b ≡ .Y A' b' : A →
      A' :: Γ ⊢ b' : A'.lift →
      Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ₀ Γ σ ρ →
      SoundTy Γ A (.sort u) → SoundTy (A :: Γ) b A.lift → SoundEq (A :: Γ) b b' →
      Interp Δ Γ (.Y A' b') σ ρ m := by
  induction H with
  | @Y Γ' σ' ρ' m' A b x hx hwx hbody ihx _ =>
    rintro A₁ A' b₁ b' u ⟨⟩ hΓ hAA' hY hYY' hb' W hAdm ihA ihbty ihbeq
    -- the inner tower, already moved
    have hx' := ihx rfl hΓ hAA' hY hYY' hb' W hAdm ihA ihbty ihbeq
    -- the slot is typed, so the body's stage is admissible
    obtain ⟨cx, hcx, htyx⟩ :=
      sound_Y_ty_aux hΔ hx rfl hAA'.hasType.1 hY W hAdm ihA ihbty
    have WY : Ctx.SubstEq Δ (σ'.cons ((Term.Y A b).subst σ'))
        (σ'.cons ((Term.Y A b).subst σ')) (A :: Γ') :=
      .cons W hAA'.hasType.1 (hY.subst hΔ W)
    have hAdm' : Adm Δ Γ₀ (A :: Γ') (σ'.cons ((Term.Y A b).subst σ')) (ρ'.push _) :=
      .cons hAdm (fun _ hb => ihA.isType hΔ W hAdm hb) hcx hwx htyx
    -- the body, at the other side and at the other stage
    have hbody' := (ihbeq hΔ WY hAdm').1 hbody
    have W' : Ctx.SubstEq Δ (σ'.cons ((Term.Y A b).subst σ'))
        (σ'.cons ((Term.Y A' b').subst σ')) (A' :: Γ') :=
      .cons W hAA'.hasType.2 ((hAA'.subst hΔ W).defeqDF (hYY'.subst hΔ W))
    have hΓA' : ⊢ (A' :: Γ') := ⟨hΓ, _, hAA'.hasType.2⟩
    exact .Y hx' hwx (IsDefEq.stage hΓA' hb' hΔ W' hbody'.ctx)
  | bot => exact fun _ _ _ _ _ _ _ _ _ _ _ => .bot
  | _ => intro A₁ A' b₁ b' u hne; cases hne

/-- The `SoundEq` half of `YDF`. -/
theorem sound_Y_eq {Γ : List Term} {A A' b b' : Term} {u : Bool} (hΓ : ⊢ Γ)
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (hYY' : Γ ⊢ .Y A b ≡ .Y A' b' : A)
    (hb : A :: Γ ⊢ b ≡ b' : A.lift) (hb' : A' :: Γ ⊢ b ≡ b' : A'.lift)
    (ihAeq : SoundEq Γ A A') (ihA : SoundTy Γ A (.sort u))
    (ihbty : SoundTy (A :: Γ) b A.lift) (ihbeq : SoundEq (A :: Γ) b b')
    (ihbty' : SoundTy (A' :: Γ) b' A'.lift) (ihbeq' : SoundEq (A' :: Γ) b' b) :
    SoundEq Γ (.Y A b) (.Y A' b') := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  refine ⟨fun h => sound_Y_eq_aux hΔ h rfl hΓ hAA' hYY'.hasType.1 hYY' hb'.hasType.2
      W hAdm ihA ihbty ihbeq, fun h => ?_⟩
  have hY' : Γ ⊢ .Y A' b' : A' := hAA'.defeqDF hYY'.hasType.2
  exact sound_Y_eq_aux hΔ h rfl hΓ hAA'.symm hY'
    (hAA'.defeqDF hYY'.symm) hb.hasType.1 W hAdm
    (SoundTy.of_eq hAA' ihAeq ihA) ihbty' ihbeq'

/-! ## Transport

`Interp.tr` carries its motive's value at the stage extended by `b` —
the term the motive's binder is instantiated with — and the whole of
`SoundTy` is that this *is* `Interp.inst`'s decomposition of `C[b]`, with
the clause's own `v` as the slot.  `SoundEq` moves each premise with its
own induction hypothesis; the motive takes three steps (its `SoundEq`,
then `Interp.ctx` for the domain that changed, then `IsDefEq.stage` for
the stage term that changed), which is the pattern `YDF` already uses. -/

theorem sound_tr_eq_of {Γ : List Term} {A A' a a' b b' C C' X X' H H' : Term}
    {u v : Bool} {r : Bool} (hΓ : ⊢ Γ)
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (haa' : Γ ⊢ a ≡ a' : A) (hbb' : Γ ⊢ b ≡ b' : A)
    (hC' : A' :: Γ ⊢ C' : .sort v)
    (ihA : SoundTy Γ A (.sort u))
    (ihAeq : SoundEq Γ A A') (ihaeq : SoundEq Γ a a') (ihbeq : SoundEq Γ b b')
    (ihCeq : SoundEq (A :: Γ) C C') (ihXeq : SoundEq Γ X X') (ihHeq : SoundEq Γ H H')
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {m : TShape} (hm : Interp Δ Γ (.tr r A a b C X H) σ ρ m) :
    Interp Δ Γ (.tr r A' a' b' C' X' H') σ ρ m := by
  cases hm with
  | bot => exact .bot
  | tr hw hle hX ha hb hA hwv hvA hC hcb hm' hH heq =>
    have hΓA' : ⊢ (A' :: Γ) := ⟨hΓ, _, hAA'.hasType.2⟩
    have WC : Ctx.SubstEq Δ (σ.cons (b.subst σ)) (σ.cons (b.subst σ)) (A :: Γ) :=
      .cons W hAA'.hasType.1 (hbb'.hasType.1.subst hΔ W)
    have hAdm' : Adm Δ Γ₀ (A :: Γ) (σ.cons (b.subst σ)) (ρ.push _) :=
      .cons hAdm (fun _ hc => ihA.isType hΔ W hAdm hc) hA hwv hvA
    have WC' : Ctx.SubstEq Δ (σ.cons (b.subst σ)) (σ.cons (b'.subst σ)) (A' :: Γ) :=
      .cons W hAA'.hasType.2 ((hAA'.subst hΔ W).defeqDF (hbb'.subst hΔ W))
    refine .tr hw hle ((ihXeq hΔ W hAdm).1 hX) ((ihaeq hΔ W hAdm).1 ha)
      ((ihbeq hΔ W hAdm).1 hb) ((ihAeq hΔ W hAdm).1 hA) hwv hvA
      (IsDefEq.stage hΓA' hC' hΔ WC' ((ihCeq hΔ WC hAdm').1 hC).ctx)
      hcb hm' (fun hr => (ihHeq hΔ W hAdm).1 (hH hr))
      -- the endpoints' equation moves along the congruences
      (((hAA'.subst hΔ W).defeqDF
        (((haa'.subst hΔ W).symm.trans heq).trans (hbb'.subst hΔ W))))

/-- The `SoundEq` half of `trDF`. -/
theorem sound_tr_eq {Γ : List Term} {A A' a a' b b' C C' X X' H H' : Term}
    {u v : Bool} {r : Bool} (hΓ : ⊢ Γ)
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (haa' : Γ ⊢ a ≡ a' : A) (hbb' : Γ ⊢ b ≡ b' : A)
    (hC : A :: Γ ⊢ C ≡ C' : .sort v) (hC' : A' :: Γ ⊢ C ≡ C' : .sort v)
    (ihA : SoundTy Γ A (.sort u))
    (ihAeq : SoundEq Γ A A') (ihaeq : SoundEq Γ a a') (ihbeq : SoundEq Γ b b')
    (ihCeq : SoundEq (A :: Γ) C C') (ihCeq' : SoundEq (A' :: Γ) C C')
    (ihXeq : SoundEq Γ X X') (ihHeq : SoundEq Γ H H') :
    SoundEq Γ (.tr r A a b C X H) (.tr r A' a' b' C' X' H') := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  refine ⟨sound_tr_eq_of hΓ hAA' haa' hbb' hC'.hasType.2 ihA ihAeq ihaeq ihbeq ihCeq ihXeq ihHeq
      hΔ W hAdm, ?_⟩
  exact sound_tr_eq_of hΓ hAA'.symm (hAA'.defeqDF haa'.symm) (hAA'.defeqDF hbb'.symm)
    hC.hasType.1 (SoundTy.of_eq hAA' ihAeq ihA) ihAeq.symm ihaeq.symm ihbeq.symm ihCeq'.symm
    ihXeq.symm ihHeq.symm hΔ W hAdm

/-- The `SoundTy` half: the motive's value *is* an approximant of `C[b]`,
read at the clause's own witness shape. -/
theorem sound_tr_ty {Γ : List Term} {A a b C X H : Term} {r : Bool}
    (htr : Γ ⊢ .tr r A a b C X H : C.inst b)
    (ihbdir : SoundDir Γ b) :
    SoundTy Γ (.tr r A a b C X H) (C.inst b) := by
  refine ⟨htr, ?_⟩
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  have hwρ := hAdm.wf
  cases hm with
  | bot => exact ⟨TShape.bot, .bot, .bot (.bot .sort)⟩
  | tr hw hle hX ha hbv hA hwv hvA hC hcb hm' hH _ =>
    refine ⟨_, (Interp.inst (A := A) (b := C) hΔ (ihbdir hΔ W hwρ) hwρ).2
      ⟨_, ?_, hbv⟩, TShape.HasType.mono_l hΔ hm' hle⟩
    rw [Subst.one_comp]
    exact hC

/-- **`tr` at `refl` is the transported value.**  Forward is one `mono`:
the clause's `m'` is an approximant of `X`.  Backward is the clause
rebuilt around the value's own typing: `SoundTy X (C[a])` gives a code,
`Interp.inst` splits it into the motive at a slot approximating `a`, and
that slot serves as the witness `v` — including for the proof premise,
since `refl`'s shape is `refl` of whatever interprets `a`. -/
theorem sound_tr_refl_eq {Γ : List Term} {A a C X : Term} {u v : Bool} {r : Bool}
    (hA : Γ ⊢ A : .sort u) (ha : Γ ⊢ a : A)
    (ihA : SoundTy Γ A (.sort u)) (ihaty : SoundTy Γ a A) (ihadir : SoundDir Γ a)
    (ihC : SoundTy (A :: Γ) C (.sort v)) (ihx : SoundTy Γ X (C.inst a)) :
    SoundEq Γ (.tr r A a a C X (.refl r a)) X := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  have hwρ := hAdm.wf
  constructor
  · intro h
    cases h with
    | bot => exact .bot
    | tr hw hle hX _ _ _ _ _ _ _ _ _ _ => exact Interp.mono hΔ hw hle hX
  · intro h
    obtain ⟨c, hc, hct⟩ := ihx.approx hΔ W hAdm h
    obtain ⟨x₀, hC₀, ha₀⟩ :=
      (Interp.inst (A := A) (b := C) hΔ (ihadir hΔ W hwρ) hwρ).1 hc
    rw [Subst.one_comp] at hC₀
    obtain ⟨vA, hvA, htyx₀⟩ := ihaty.approx hΔ W hAdm ha₀
    have Wa : Ctx.SubstEq Δ (σ.cons (a.subst σ)) (σ.cons (a.subst σ)) (A :: Γ) :=
      .cons W hA (ha.subst hΔ W)
    have hAdm' : Adm Δ Γ₀ (A :: Γ) (σ.cons (a.subst σ)) (ρ.push x₀) :=
      .cons hAdm (fun _ hd => ihA.isType hΔ W hAdm hd) hvA ha₀.wf htyx₀
    refine .tr h.wf (TShape.LE.refl h.wf) h ha₀ ha₀ hvA ha₀.wf htyx₀ hC₀
      (ihC.isType hΔ Wa hAdm' hC₀) hct ?_ (ha.subst hΔ W)
    rintro rfl
    exact .refl ha₀ ha₀.wf (TShape.LE.refl ha₀.wf)

/-! ## Inversion at the level of `SoundEq`

The labels are in the shapes, so a semantic equality of two types yields
the *syntactic* equalities of their labels: probe with the type's own
label-only approximant, move it across with the equality at the identity
stage and the `⊥` valuation (admissible for free, `Adm.bot`), and read the
label back off the order.

These are stated over `SoundEq` rather than over `Γ ⊢ · ≡ · : _` so that
they are available *before* soundness — `StrongSound.uniq` needs them, and
`IsDefEq.strongSound` needs `uniq`.  `Inversion.lean` derives the
syntactic corollaries by feeding them `IsDefEq.sound`. -/

/-- **A one-entry Π-approximant**: a value of the codomain at a typed
slot, packaged as an approximant of the Π-type itself.  Master's
`WShapeFun.single`, and the probe the codomain inversion below needs: it
is how a fact about `B` is pushed into a fact about `Π A B`, where the
semantic equality of two Π-types can see it.

The level bookkeeping is the same as everywhere: the domain shape, the
slot and the value live at three levels and the entry needs one. -/
theorem Interp.forallE_single {Γ Δ : List Term} {A B t : Term} {σ ρ} {u v : Bool}
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hwρ : Valuation.WF Δ ρ)
    (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) (ht : Δ ⊢ t : A.subst σ)
    {d x c : TShape} (hdint : Interp Δ Γ A σ ρ d) (hdty : TShape.HasType Δ d TShape.type)
    (hxd : TShape.HasType Δ x d) (hc : Interp Δ (A :: Γ) B (σ.cons t) (ρ.push x) c) :
    ∃ (k : Nat) (dk xk ck : Shape k),
      Interp Δ Γ (.forallE A B) σ ρ (Shape.T (n := k+1)
        (.forallE (A.subst σ) (B.subst σ.lift) dk [⟨A.subst σ, t, xk, ck⟩])) ∧
      TShape.LE Δ c (Shape.T ck) ∧ TShape.LE Δ (Shape.T xk) x := by
  obtain ⟨k, hkd, hkx, hkc⟩ : ∃ k, d.1 ≤ k ∧ x.1 ≤ k ∧ c.1 ≤ k :=
    ⟨max (max d.1 x.1) c.1, Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..),
      Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..), Nat.le_max_right ..⟩
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  have hΔA : ⊢ (A.subst σ :: Δ) := ⟨hΔ, _, hAσ⟩
  have hwd : Shape.WF Δ (d.2.lift k) := (Shape.lift_wf hkd).2 hdty.wf.1
  have hwx : Shape.WF Δ (x.2.lift k) := (Shape.lift_wf hkx).2 hxd.wf.1
  have hwc : Shape.WF Δ (c.2.lift k) := (Shape.lift_wf hkc).2 hc.wf
  have hwf : Shape.WF (n := k+1) Δ
      (.forallE (A.subst σ) (B.subst σ.lift) (d.2.lift k)
        [⟨A.subst σ, t, x.2.lift k, c.2.lift k⟩]) := by
    refine ⟨⟨u, hAσ⟩, ⟨v, hB.subst hΔA (W.lift hA hAσ)⟩, hwd, ?_, ?_⟩
    · intro e he
      cases List.mem_singleton.1 he
      exact ⟨⟨u, hAσ⟩, ht, hwx, hwc⟩
    · intro e he e' he' Θ τ hΘ Wτ _ _
      cases List.mem_singleton.1 he
      cases List.mem_singleton.1 he'
      exact Shape.WF.coherent (Shape.WF.subst hΘ Wτ hwc)
  refine ⟨k, _, _, _, .forallE ?_ ?_ hwf ?_ ?_ ?_ hwf (TShape.LE.refl hwf),
    TShape.LE.le_lift hΔ (m := c) hkc hc.wf,
    TShape.LE.lift_le hΔ (m := x) hkx hxd.wf.1⟩
  · exact Interp.mono hΔ hwd (TShape.LE.lift_le hΔ (m := d) hkd hdty.wf.1) hdint
  · exact hdty.lift_subject hΔ hkd
  · intro e he; cases List.mem_singleton.1 he; exact ⟨u, hAσ⟩
  · intro e he
    cases List.mem_singleton.1 he
    exact TShape.HasType.mono_r hΔ (hxd.lift_subject hΔ hkx) _
      (TShape.LE.le_lift hΔ (m := d) hkd hdty.wf.1) (hdty.lift_subject hΔ hkd)
  · intro e he
    cases List.mem_singleton.1 he
    refine Interp.mono hΔ hwc (TShape.LE.lift_le hΔ (m := c) hkc hc.wf) ?_
    exact Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
      TShape.LE.le_lift hΔ (m := x) hkx hxd.wf.1⟩) hc

/-- The Σ twin of `Interp.forallE_single`. -/
theorem Interp.sigma_single {Γ Δ : List Term} {A B t : Term} {σ ρ} {u v : Bool}
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hwρ : Valuation.WF Δ ρ)
    (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) (ht : Δ ⊢ t : A.subst σ)
    {d x c : TShape} (hdint : Interp Δ Γ A σ ρ d) (hdty : TShape.HasType Δ d TShape.type)
    (hxd : TShape.HasType Δ x d) (hc : Interp Δ (A :: Γ) B (σ.cons t) (ρ.push x) c) :
    ∃ (k : Nat) (dk xk ck : Shape k),
      Interp Δ Γ (.sigma A B) σ ρ (Shape.T (n := k+1)
        (.sigma (A.subst σ) (B.subst σ.lift) dk [⟨A.subst σ, t, xk, ck⟩])) ∧
      TShape.LE Δ c (Shape.T ck) ∧ TShape.LE Δ (Shape.T xk) x := by
  obtain ⟨k, hkd, hkx, hkc⟩ : ∃ k, d.1 ≤ k ∧ x.1 ≤ k ∧ c.1 ≤ k :=
    ⟨max (max d.1 x.1) c.1, Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..),
      Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..), Nat.le_max_right ..⟩
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  have hΔA : ⊢ (A.subst σ :: Δ) := ⟨hΔ, _, hAσ⟩
  have hwd : Shape.WF Δ (d.2.lift k) := (Shape.lift_wf hkd).2 hdty.wf.1
  have hwx : Shape.WF Δ (x.2.lift k) := (Shape.lift_wf hkx).2 hxd.wf.1
  have hwc : Shape.WF Δ (c.2.lift k) := (Shape.lift_wf hkc).2 hc.wf
  have hwf : Shape.WF (n := k+1) Δ
      (.sigma (A.subst σ) (B.subst σ.lift) (d.2.lift k)
        [⟨A.subst σ, t, x.2.lift k, c.2.lift k⟩]) := by
    refine ⟨⟨u, hAσ⟩, ⟨v, hB.subst hΔA (W.lift hA hAσ)⟩, hwd, ?_, ?_⟩
    · intro e he
      cases List.mem_singleton.1 he
      exact ⟨⟨u, hAσ⟩, ht, hwx, hwc⟩
    · intro e he e' he' Θ τ hΘ Wτ _ _
      cases List.mem_singleton.1 he
      cases List.mem_singleton.1 he'
      exact Shape.WF.coherent (Shape.WF.subst hΘ Wτ hwc)
  refine ⟨k, _, _, _, .sigma ?_ ?_ hwf ?_ ?_ ?_ hwf (TShape.LE.refl hwf),
    TShape.LE.le_lift hΔ (m := c) hkc hc.wf,
    TShape.LE.lift_le hΔ (m := x) hkx hxd.wf.1⟩
  · exact Interp.mono hΔ hwd (TShape.LE.lift_le hΔ (m := d) hkd hdty.wf.1) hdint
  · exact hdty.lift_subject hΔ hkd
  · intro e he; cases List.mem_singleton.1 he; exact ⟨u, hAσ⟩
  · intro e he
    cases List.mem_singleton.1 he
    exact TShape.HasType.mono_r hΔ (hxd.lift_subject hΔ hkx) _
      (TShape.LE.le_lift hΔ (m := d) hkd hdty.wf.1) (hdty.lift_subject hΔ hkd)
  · intro e he
    cases List.mem_singleton.1 he
    refine Interp.mono hΔ hwc (TShape.LE.lift_le hΔ (m := c) hkc hc.wf) ?_
    exact Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
      TShape.LE.le_lift hΔ (m := x) hkx hxd.wf.1⟩) hc

/-- **The codomains of two semantically equal Π-types agree, semantically.**
`forallE_inv` reads the *labels* off the two Π-shapes; this reads the
*graphs*.  A value of the first codomain at a typed slot becomes a
one-entry approximant of the Π-type (`Interp.forallE_single`); the
semantic equality carries it to the other Π-type, whose clause covers
that entry by a lookup in its own graph; and `sound_graph_lookup` turns
that lookup back into a value of the second codomain at the same slot. -/
theorem SoundEq.forallE_cod {Γ : List Term} {A₀ B₀ A₁ B₁ : Term} {u v u' v' : Bool}
    (hΓ : ⊢ Γ) (hA₀ : Γ ⊢ A₀ : .sort u) (hB₀ : A₀ :: Γ ⊢ B₀ : .sort v)
    (hA₁ : Γ ⊢ A₁ : .sort u') (hB₁ : A₁ :: Γ ⊢ B₁ : .sort v')
    (hB₁dir : SoundDir (A₁ :: Γ) B₁)
    (H : SoundEq Γ (.forallE A₀ B₀) (.forallE A₁ B₁))
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {t : Term} (ht : Δ ⊢ t : A₀.subst σ)
    {d x c : TShape} (hdint : Interp Δ Γ A₀ σ ρ d) (hdty : TShape.HasType Δ d TShape.type)
    (hxd : TShape.HasType Δ x d)
    (hc : Interp Δ (A₀ :: Γ) B₀ (σ.cons t) (ρ.push x) c) :
    Interp Δ (A₁ :: Γ) B₁ (σ.cons t) (ρ.push x) c := by
  have hwρ := hAdm.wf
  obtain ⟨k, dk, xk, ck, hprobe, hcle, hxle⟩ :=
    Interp.forallE_single hΔ W hwρ hA₀ hB₀ ht hdint hdty hxd hc
  have hpr := (H hΔ W hAdm).1 hprobe
  cases hpr with
  | forallE hA₁int hd₁ hwf₁ hlab₁ hdom₁ hbody₁ hw₁ hle₁ =>
    obtain ⟨hPi, _, hcov⟩ :=
      TShape.LE.forallE_decomp hΔ hle₁ hprobe.wf hwf₁ (TEvaluates.refl hwf₁.2.2.2)
    have hev := hcov ⟨A₀.subst σ, t, xk, ck⟩ (by simp)
    have hB := sound_graph_lookup (B := B₁) ⟨hΓ, _, hA₁⟩ hA₁ hB₁ hΔ W hbody₁
      (TShape.WF.T.2 (hprobe.wf.2.2.2.1 _ (by simp)).2.2.1) hB₁dir hwρ ht hPi.1 hev
    exact Interp.mono hΔ hc.wf hcle (Interp.mono_val hΔ (Valuation.LE.push.2
      ⟨Valuation.LE.refl hwρ, hxle⟩) hB)

/-- The Σ twin of `SoundEq.forallE_cod`. -/
theorem SoundEq.sigma_cod {Γ : List Term} {A₀ B₀ A₁ B₁ : Term} {u v u' v' : Bool}
    (hΓ : ⊢ Γ) (hA₀ : Γ ⊢ A₀ : .sort u) (hB₀ : A₀ :: Γ ⊢ B₀ : .sort v)
    (hA₁ : Γ ⊢ A₁ : .sort u') (hB₁ : A₁ :: Γ ⊢ B₁ : .sort v')
    (hB₁dir : SoundDir (A₁ :: Γ) B₁)
    (H : SoundEq Γ (.sigma A₀ B₀) (.sigma A₁ B₁))
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {t : Term} (ht : Δ ⊢ t : A₀.subst σ)
    {d x c : TShape} (hdint : Interp Δ Γ A₀ σ ρ d) (hdty : TShape.HasType Δ d TShape.type)
    (hxd : TShape.HasType Δ x d)
    (hc : Interp Δ (A₀ :: Γ) B₀ (σ.cons t) (ρ.push x) c) :
    Interp Δ (A₁ :: Γ) B₁ (σ.cons t) (ρ.push x) c := by
  have hwρ := hAdm.wf
  obtain ⟨k, dk, xk, ck, hprobe, hcle, hxle⟩ :=
    Interp.sigma_single hΔ W hwρ hA₀ hB₀ ht hdint hdty hxd hc
  have hpr := (H hΔ W hAdm).1 hprobe
  cases hpr with
  | sigma hA₁int hd₁ hwf₁ hlab₁ hdom₁ hbody₁ hw₁ hle₁ =>
    obtain ⟨hSg, _, hcov⟩ :=
      TShape.LE.sigma_decomp hΔ hle₁ hprobe.wf hwf₁ (TEvaluates.refl hwf₁.2.2.2)
    have hev := hcov ⟨A₀.subst σ, t, xk, ck⟩ (by simp)
    have hB := sound_graph_lookup (B := B₁) ⟨hΓ, _, hA₁⟩ hA₁ hB₁ hΔ W hbody₁
      (TShape.WF.T.2 (hprobe.wf.2.2.2.1 _ (by simp)).2.2.1) hB₁dir hwρ ht hSg.1 hev
    exact Interp.mono hΔ hc.wf hcle (Interp.mono_val hΔ (Valuation.LE.push.2
      ⟨Valuation.LE.refl hwρ, hxle⟩) hB)

/-- **Instantiating two semantically equal codomains at one argument.**
`Interp.inst` splits an approximant of `B[a]` into the codomain at a slot
approximating `a`; `SoundTy a A` types that slot, which is what the
one-entry probe needs; and `forallE_cod` moves it across.  This is the
semantic half of type uniqueness at `app` — the half that was waiting for
`Interp.inst`. -/
theorem SoundEq.inst_cod {Γ : List Term} {A₀ A₁ B₀ B₁ a : Term} {u v u' v' : Bool}
    (hΓ : ⊢ Γ) (hA₀ : Γ ⊢ A₀ : .sort u) (hB₀ : A₀ :: Γ ⊢ B₀ : .sort v)
    (hA₁ : Γ ⊢ A₁ : .sort u') (hB₁ : A₁ :: Γ ⊢ B₁ : .sort v')
    (hB₀dir : SoundDir (A₀ :: Γ) B₀) (hB₁dir : SoundDir (A₁ :: Γ) B₁)
    (ha₀ : SoundTy Γ a A₀) (ha₁ : SoundTy Γ a A₁) (hadir : SoundDir Γ a)
    (ihA₀ : SoundTy Γ A₀ (.sort u)) (ihA₁ : SoundTy Γ A₁ (.sort u'))
    (H : SoundEq Γ (.forallE A₀ B₀) (.forallE A₁ B₁)) :
    SoundEq Γ (B₀.inst a) (B₁.inst a) := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  have hwρ := hAdm.wf
  constructor
  · intro h
    obtain ⟨x, hb, hx⟩ := (Interp.inst (A := A₀) (b := B₀) hΔ (hadir hΔ W hwρ) hwρ).1 h
    rw [Subst.one_comp] at hb
    obtain ⟨d, hd, hxd⟩ := ha₀.approx hΔ W hAdm hx
    refine (Interp.inst (A := A₁) (b := B₁) hΔ (hadir hΔ W hwρ) hwρ).2 ⟨x, ?_, hx⟩
    rw [Subst.one_comp]
    exact SoundEq.forallE_cod hΓ hA₀ hB₀ hA₁ hB₁ hB₁dir H hΔ W hAdm
      (ha₀.typed.subst hΔ W) hd (ihA₀.isType hΔ W hAdm hd) hxd hb
  · intro h
    obtain ⟨x, hb, hx⟩ := (Interp.inst (A := A₁) (b := B₁) hΔ (hadir hΔ W hwρ) hwρ).1 h
    rw [Subst.one_comp] at hb
    obtain ⟨d, hd, hxd⟩ := ha₁.approx hΔ W hAdm hx
    refine (Interp.inst (A := A₀) (b := B₀) hΔ (hadir hΔ W hwρ) hwρ).2 ⟨x, ?_, hx⟩
    rw [Subst.one_comp]
    exact SoundEq.forallE_cod hΓ hA₁ hB₁ hA₀ hB₀ hB₀dir H.symm hΔ W hAdm
      (ha₁.typed.subst hΔ W) hd (ihA₁.isType hΔ W hAdm hd) hxd hb

/-- The Σ twin, for `snd`. -/
theorem SoundEq.inst_cod_sigma {Γ : List Term} {A₀ A₁ B₀ B₁ a : Term} {u v u' v' : Bool}
    (hΓ : ⊢ Γ) (hA₀ : Γ ⊢ A₀ : .sort u) (hB₀ : A₀ :: Γ ⊢ B₀ : .sort v)
    (hA₁ : Γ ⊢ A₁ : .sort u') (hB₁ : A₁ :: Γ ⊢ B₁ : .sort v')
    (hB₀dir : SoundDir (A₀ :: Γ) B₀) (hB₁dir : SoundDir (A₁ :: Γ) B₁)
    (ha₀ : SoundTy Γ a A₀) (ha₁ : SoundTy Γ a A₁) (hadir : SoundDir Γ a)
    (ihA₀ : SoundTy Γ A₀ (.sort u)) (ihA₁ : SoundTy Γ A₁ (.sort u'))
    (H : SoundEq Γ (.sigma A₀ B₀) (.sigma A₁ B₁)) :
    SoundEq Γ (B₀.inst a) (B₁.inst a) := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  have hwρ := hAdm.wf
  constructor
  · intro h
    obtain ⟨x, hb, hx⟩ := (Interp.inst (A := A₀) (b := B₀) hΔ (hadir hΔ W hwρ) hwρ).1 h
    rw [Subst.one_comp] at hb
    obtain ⟨d, hd, hxd⟩ := ha₀.approx hΔ W hAdm hx
    refine (Interp.inst (A := A₁) (b := B₁) hΔ (hadir hΔ W hwρ) hwρ).2 ⟨x, ?_, hx⟩
    rw [Subst.one_comp]
    exact SoundEq.sigma_cod hΓ hA₀ hB₀ hA₁ hB₁ hB₁dir H hΔ W hAdm
      (ha₀.typed.subst hΔ W) hd (ihA₀.isType hΔ W hAdm hd) hxd hb
  · intro h
    obtain ⟨x, hb, hx⟩ := (Interp.inst (A := A₁) (b := B₁) hΔ (hadir hΔ W hwρ) hwρ).1 h
    rw [Subst.one_comp] at hb
    obtain ⟨d, hd, hxd⟩ := ha₁.approx hΔ W hAdm hx
    refine (Interp.inst (A := A₀) (b := B₀) hΔ (hadir hΔ W hwρ) hwρ).2 ⟨x, ?_, hx⟩
    rw [Subst.one_comp]
    exact SoundEq.sigma_cod hΓ hA₁ hB₁ hA₀ hB₀ hB₀dir H.symm hΔ W hAdm
      (ha₁.typed.subst hΔ W) hd (ihA₁.isType hΔ W hAdm hd) hxd hb

theorem SoundEq.sort_inv {Γ : List Term} {u v : Bool}
    (hΓ : ⊢ Γ) (H : SoundEq Γ (Term.sort u) (Term.sort v)) : u = v := by
  have h := (H hΓ (Ctx.SubstEq.id hΓ) Adm.bot).1 Interp.sort'
  have hle := Interp.le_sort h
  exact (TShape.LE.def_mp (Nat.le_refl 0) (Nat.le_refl 0)) hle

theorem SoundEq.forallE_inv {Γ : List Term} {A₀ B₀ A₁ B₁ : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hA₀ : Γ ⊢ A₀ : .sort u) (hB₀ : A₀ :: Γ ⊢ B₀ : .sort v)
    (H : SoundEq Γ (Term.forallE A₀ B₀) (Term.forallE A₁ B₁)) :
    ∃ u v, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ A₀ :: Γ ⊢ B₀ ≡ B₁ : .sort v := by
  -- the probe: the Π's own label, with nothing else in it
  have hprobe : Interp Γ Γ (.forallE A₀ B₀) Subst.id Valuation.nil
      (Shape.T (n := 1) (Shape.piAtom (A₀.subst Subst.id) (B₀.subst Subst.id.lift))) := by
    refine Interp.piAtom (u := u) (v := v) ?_ ?_
    · simpa using hA₀
    · simpa using hB₀
  -- the equality moves it across, at the identity stage and the `⊥` valuation
  have hmove := (H hΓ (Ctx.SubstEq.id hΓ) Adm.bot).1 hprobe
  simp only [subst_id, Subst.lift_id] at hmove
  -- and the label reads back off it
  have hlab := Interp.le_piAtom hmove
  simp only [subst_id, Subst.lift_id] at hlab
  obtain ⟨u', hu⟩ := hlab.1
  obtain ⟨v', hv⟩ := hlab.2
  exact ⟨u', v', hu, hv⟩

/-- The same at Σ, with `sigmaAtom` as the probe. -/
theorem SoundEq.sigma_inv {Γ : List Term} {A₀ B₀ A₁ B₁ : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hA₀ : Γ ⊢ A₀ : .sort u) (hB₀ : A₀ :: Γ ⊢ B₀ : .sort v)
    (H : SoundEq Γ (Term.sigma A₀ B₀) (Term.sigma A₁ B₁)) :
    ∃ u v, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ A₀ :: Γ ⊢ B₀ ≡ B₁ : .sort v := by
  have hprobe : Interp Γ Γ (.sigma A₀ B₀) Subst.id Valuation.nil
      (Shape.T (n := 1) (Shape.sigmaAtom (A₀.subst Subst.id) (B₀.subst Subst.id.lift))) := by
    refine Interp.sigmaAtom (u := u) (v := v) ?_ ?_
    · simpa using hA₀
    · simpa using hB₀
  have hmove := (H hΓ (Ctx.SubstEq.id hΓ) Adm.bot).1 hprobe
  simp only [subst_id, Subst.lift_id] at hmove
  have hlab := Interp.le_sigmaAtom hmove
  simp only [subst_id, Subst.lift_id] at hlab
  obtain ⟨u', hu⟩ := hlab.1
  obtain ⟨v', hv⟩ := hlab.2
  exact ⟨u', v', hu, hv⟩

/-- The *semantic* half of Σ domain inversion, at every stage: an
approximant of the domain moves across by being wrapped as the domain of
an otherwise empty Σ-shape.  Master's `SoundEq.sigma_inv`, first
component.  The syntactic `sigma_inv` above does not give this — a
definitional equality of domains becomes a `SoundEq` only through
soundness. -/
theorem SoundEq.sigma_dom {Γ : List Term} {A B A' B' : Term} {u u' v v' : Bool}
    (hA : SoundTy Γ A (.sort u)) (hB : A :: Γ ⊢ B : .sort v)
    (hA' : SoundTy Γ A' (.sort u')) (hB' : A' :: Γ ⊢ B' : .sort v')
    (H : SoundEq Γ (.sigma A B) (.sigma A' B')) : SoundEq Γ A A' := by
  suffices key : ∀ {A B A' B' : Term} {u v : Bool}, SoundTy Γ A (.sort u) →
      A :: Γ ⊢ B : .sort v → SoundEq Γ (.sigma A B) (.sigma A' B') →
      ∀ {Δ Γ₀ σ ρ}, ⊢ Δ → Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ₀ Γ σ ρ →
      ∀ {m}, Interp Δ Γ A σ ρ m → Interp Δ Γ A' σ ρ m by
    intro Δ Γ₀ σ ρ hΔ W hAdm m
    exact ⟨key hA hB H hΔ W hAdm, key hA' hB' H.symm hΔ W hAdm⟩
  intro A B A' B' u v hA hB H Δ Γ₀ σ ρ hΔ W hAdm m hm
  have ⟨⟨_, hAσ⟩, _, hBσ⟩ := PiLabelEq.subst hΔ W ⟨⟨u, hA.typed⟩, v, hB⟩
  have hw : Shape.WF (n := m.1+1) Δ (ShapeS.sigma (A.subst σ) (B.subst σ.lift) m.2 []) :=
    ⟨⟨_, hAσ.hasType.1⟩, ⟨_, hBσ.hasType.1⟩, hm.wf,
      fun _ he => absurd he List.not_mem_nil, fun _ he => absurd he List.not_mem_nil⟩
  have hprobe : Interp Δ Γ (.sigma A B) σ ρ
      (Shape.T (n := m.1+1) (ShapeS.sigma (A.subst σ) (B.subst σ.lift) m.2 [])) :=
    .sigma hm (hA.isType hΔ W hAdm hm) hw nofun nofun nofun hw (TShape.LE.refl hw)
  have hmove := (H hΔ W hAdm).1 hprobe
  cases hmove with
  | sigma hA'' _ hwf _ _ _ _ hle =>
    obtain ⟨_, hdd, _⟩ := TShape.LE.sigma_decomp hΔ hle hw hwf (TEvaluates.refl hwf.2.2.2)
    exact Interp.mono hΔ hm.wf hdd hA''

/-- Inversion at `id`.  The `id` former is label-only, so it needs no
atom: its own interpretation at the identity stage *is* the probe, and the
order between two `id`-shapes is the triple of equations. -/
theorem SoundEq.id_inv {Γ : List Term} {r : Bool} {A₀ a₀ b₀ A₁ a₁ b₁ : Term} {u : Bool}
    (hΓ : ⊢ Γ) (hA₀ : Γ ⊢ A₀ : .sort u) (ha₀ : Γ ⊢ a₀ : A₀) (hb₀ : Γ ⊢ b₀ : A₀)
    (H : SoundEq Γ (.id r A₀ a₀ b₀) (.id r A₁ a₁ b₁)) :
    ∃ u, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ Γ ⊢ a₀ ≡ a₁ : A₀ ∧ Γ ⊢ b₀ ≡ b₁ : A₀ := by
  have hw : TShape.WF Γ (Shape.T (n := 1)
      (ShapeS.id r (A₀.subst Subst.id) (a₀.subst Subst.id) (b₀.subst Subst.id))) :=
    Shape.WF.id_of hΓ (Ctx.SubstEq.id hΓ) hA₀ ha₀ hb₀
  have hmove := (H hΓ (Ctx.SubstEq.id hΓ) Adm.bot).1 (.id hw (TShape.LE.refl hw))
  cases hmove with
  | id _ hle =>
    obtain ⟨M, _, _, h2⟩ := TShape.LE.at_succ hle
    obtain ⟨_, ⟨u', hA⟩, ha, hb⟩ := h2
    simp only [subst_id] at hA ha hb
    exact ⟨u', hA, ha, hb⟩

/-! ## The target

The one theorem this branch is for.  Master needs `LogRel.lean` and
`Adequacy.lean` on top of its soundness theorem to get inversion; here the
labels carry the syntax through the model, so the inversion principles of
§6 are corollaries of this statement alone. -/

/-- **Directedness**, its own induction on typing.

Every non-congruence rule is an identity on the two conclusions: the
structural rules permute them, `defeqDF` changes only the type, and the
computation rules carry typings of both sides (the other repo's
`of_typings` observation), so their conclusions are their premises'.  Only
one case per term former has content, and each is the corresponding
`isDirected` lemma of the other repo. -/
theorem IsDefEq.dir {Γ : List Term} {t t' A : Term}
    (hΓ : ⊢ Γ) (H : Γ ⊢ t ≡ t' : A) : SoundDir Γ t ∧ SoundDir Γ t' := by
  induction H with
  -- structural: pure bookkeeping
  | symm _ ih => exact ⟨(ih hΓ).2, (ih hΓ).1⟩
  | trans _ _ ih₁ ih₂ => exact ⟨(ih₁ hΓ).1, (ih₂ hΓ).2⟩
  | trans' _ _ ih₁ ih₂ => exact ⟨(ih₁ hΓ).1, (ih₂ hΓ).2⟩
  | defeqDF _ _ _ ih => exact ih hΓ
  -- atoms: the canonical shape bounds everything
  | sort => exact ⟨dir_atom Interp.le_sort (fun hw h => .sort hw h) trivial,
      dir_atom Interp.le_sort (fun hw h => .sort hw h) trivial⟩
  | unit => exact ⟨dir_atom Interp.le_unit (fun hw h => .unit hw h) trivial,
      dir_atom Interp.le_unit (fun hw h => .unit hw h) trivial⟩
  | nat => exact ⟨dir_atom Interp.le_nat (fun hw h => .nat hw h) trivial,
      dir_atom Interp.le_nat (fun hw h => .nat hw h) trivial⟩
  | zero => exact ⟨dir_atom Interp.le_zero (fun hw h => .zero hw h) trivial,
      dir_atom Interp.le_zero (fun hw h => .zero hw h) trivial⟩
  | star => exact ⟨dir_of_bot (fun .bot => rfl), dir_of_bot (fun .bot => rfl)⟩
  -- Π: the other repo's `pi_isDirected`, with `IsDefEq.stage` for the
  -- cross pairs of the appended graph
  | forallEDF hAA' hB hB' ihA ihB ihB' =>
    exact ⟨sound_forallE_dir hΓ hAA'.hasType.1 hB.hasType.1 (ihA hΓ).1
        (ihB ⟨hΓ, _, hAA'.hasType.1⟩).1,
      sound_forallE_dir hΓ hAA'.hasType.2 hB'.hasType.2 (ihA hΓ).2
        (ihB' ⟨hΓ, _, hAA'.hasType.2⟩).2⟩
  -- `bvar` reads the slot's well-formedness off `Valuation.WF`; the rest
  -- are one per term former, each the other repo's `*_isDirected`
  | bvar => exact ⟨dir_bvar, dir_bvar⟩
  -- the λ-shape's domain label is what makes this one standalone (§5.5b)
  | appDF _ _ _ _ _ _ _ ihf iha _ =>
    exact ⟨dir_app (ihf hΓ).1 (iha hΓ).1, dir_app (ihf hΓ).2 (iha hΓ).2⟩
  -- λ: Π's argument, with the body in place of the codomain
  | lamDF hAA' hB hbody hbody' _ ihA _ ihb ihb' _ =>
    exact ⟨sound_lam_dir hΓ hAA'.hasType.1 hbody.hasType.1 (ihA hΓ).1
        (ihb ⟨hΓ, _, hAA'.hasType.1⟩).1,
      sound_lam_dir hΓ hAA'.hasType.2 hbody'.hasType.2 (ihA hΓ).2
        (ihb' ⟨hΓ, _, hAA'.hasType.2⟩).2⟩
  | sigmaDF hAA' hB hB' ihA ihB ihB' =>
    exact ⟨sound_sigma_dir hΓ hAA'.hasType.1 hB.hasType.1 (ihA hΓ).1
        (ihB ⟨hΓ, _, hAA'.hasType.1⟩).1,
      sound_sigma_dir hΓ hAA'.hasType.2 hB'.hasType.2 (ihA hΓ).2
        (ihB' ⟨hΓ, _, hAA'.hasType.2⟩).2⟩
  | pairDF hAA' _ _ _ _ _ _ ihA _ _ iha ihb _ _ =>
    exact ⟨dir_pair (ihA hΓ).1 (iha hΓ).1 (ihb hΓ).1,
      dir_pair (ihA hΓ).2 (iha hΓ).2 (ihb hΓ).2⟩
  | fstDF _ _ _ _ _ ih => exact ⟨dir_fst (ih hΓ).1, dir_fst (ih hΓ).2⟩
  | sndDF _ _ _ _ _ _ ih _ => exact ⟨dir_snd (ih hΓ).1, dir_snd (ih hΓ).2⟩
  | succDF _ ih => exact ⟨dir_succ (ih hΓ).1, dir_succ (ih hΓ).2⟩
  | natCaseDF _ _ _ hbb' _ _ ihM iha ihb _ =>
    exact ⟨dir_natCase hΓ hbb'.hasType.1 (ihM hΓ).1 (iha hΓ).1 (ihb ⟨hΓ, _, .nat⟩).1,
      dir_natCase hΓ hbb'.hasType.2 (ihM hΓ).2 (iha hΓ).2 (ihb ⟨hΓ, _, .nat⟩).2⟩
  | idDF hAA' haa' hbb' ihA iha ihb =>
    exact ⟨dir_id hAA'.hasType.1 haa'.hasType.1 hbb'.hasType.1,
      dir_id hAA'.hasType.2 (hAA'.defeqDF haa'.hasType.2) (hAA'.defeqDF hbb'.hasType.2)⟩
  | reflDF _ _ _ _ iha _ => exact ⟨dir_refl (iha hΓ).1, dir_refl (iha hΓ).2⟩
  -- the case `SoundJoin` was for: two transports are typed at two
  -- approximants of the motive, and the witness above both has to be
  -- typed at the motive above both.  Every other case is an upper bound
  -- with no typing to preserve, which is why they run under
  -- `Valuation.WF` with no admissibility in sight
  | trDF hAA' haa' hbb' hC hC' hxx' hhh' _ _ ihA iha ihb ihC ihC' ihx ihh =>
    exact ⟨dir_tr hΓ hAA'.hasType.1 hbb'.hasType.1 (ihA hΓ).1 (iha hΓ).1 (ihb hΓ).1
        (ihC ⟨hΓ, _, hAA'.hasType.1⟩).1 (ihx hΓ).1 (ihh hΓ).1,
      dir_tr hΓ hAA'.hasType.2 (hAA'.defeqDF hbb'.hasType.2) (ihA hΓ).2 (iha hΓ).2 (ihb hΓ).2
        (ihC' ⟨hΓ, _, hAA'.hasType.2⟩).2 (ihx hΓ).2 (ihh hΓ).2⟩
  -- the computation rules are padded with typings of both sides, so each
  -- of these is its two premises' conclusions
  | beta _ _ _ _ _ _ _ _ ih₃ ih₄ => exact ⟨(ih₃ hΓ).1, (ih₄ hΓ).1⟩
  | eta _ _ ih₁ ih₂ => exact ⟨(ih₂ hΓ).1, (ih₁ hΓ).1⟩
  | unit_eta _ ih => exact ⟨dir_of_bot (fun .bot => rfl), (ih hΓ).1⟩
  | pair_fst _ _ _ _ _ _ _ ih₃ _ ih₅ => exact ⟨(ih₅ hΓ).1, (ih₃ hΓ).1⟩
  | pair_snd _ _ _ _ _ _ _ _ ih₄ ih₅ => exact ⟨(ih₅ hΓ).1, (ih₄ hΓ).1⟩
  | fst_snd _ _ ih₁ ih₂ => exact ⟨(ih₂ hΓ).1, (ih₁ hΓ).1⟩
  | natCase_zero _ _ _ _ _ ih₂ _ ih₄ => exact ⟨(ih₄ hΓ).1, (ih₂ hΓ).1⟩
  | natCase_succ _ _ _ _ _ _ _ _ _ _ ih₅ ih₆ => exact ⟨(ih₅ hΓ).1, (ih₆ hΓ).1⟩
  | Y_unfold _ _ _ _ _ _ ih₃ ih₄ => exact ⟨(ih₃ hΓ).1, (ih₄ hΓ).1⟩
  | tr_refl _ _ _ _ _ _ _ _ ih₄ ih₅ => exact ⟨(ih₅ hΓ).1, (ih₄ hΓ).1⟩
  | proofIrrel _ _ _ _ ih₂ ih₃ => exact ⟨(ih₂ hΓ).1, (ih₃ hΓ).1⟩
  -- the fixed point: an induction on the tower of unfoldings, inside
  | YDF h1 h2 h3 ihA ihb ihb' =>
    have hY := IsDefEq.YDF h1 h2 h3
    exact ⟨dir_Y h1.hasType.1 hY.hasType.1 (ihb ⟨hΓ, _, h1.hasType.1⟩).1,
      dir_Y h1.hasType.2 (h1.defeqDF hY.hasType.2) (ihb' ⟨hΓ, _, h1.hasType.2⟩).2⟩

/-! ## The soundness theorem

Two conclusions, as master's: the terms have the same approximants
(`SoundEq`, his `HasEquality`) and every approximant of the left one is
below a typed one (`SoundTy`, his `HasFixedness`).  Directedness is
`IsDefEq.dir` above; his `HasSubstitution`/`HasRenaming` are
`Interp.substTerm`/`Interp.weak'`; his `PiReady` dissolves into
`IsDefEq.dir` of the domain and the codomain; his `regular` is never
used, here or there. -/

theorem IsDefEq.sound {Γ : List Term} {t t' A : Term}
    (hΓ : ⊢ Γ) (H : Γ ⊢ t ≡ t' : A) :
    SoundEq Γ t t' ∧ SoundTy Γ t A := by
  induction H with
  -- structural rules: no stage or valuation changes, so these are pure
  -- bookkeeping on the two conclusions
  | @symm _ _ _ _ hs ih =>
    have ⟨he, hty⟩ := ih hΓ
    exact ⟨he.symm, SoundTy.of_eq hs he hty⟩
  | trans _ _ ih₁ ih₂ =>
    have ⟨he₁, hty₁⟩ := ih₁ hΓ
    have ⟨he₂, _⟩ := ih₂ hΓ
    exact ⟨he₁.trans he₂, hty₁⟩
  | trans' _ _ ih₁ ih₂ =>
    have ⟨he₁, hty₁⟩ := ih₁ hΓ
    have ⟨he₂, _⟩ := ih₂ hΓ
    exact ⟨he₁.trans he₂, hty₁⟩
  -- conversion: only the *type*'s interpretation moves, and `SoundEq` of
  -- the two types is exactly what moves it
  | @defeqDF _ _ _ _ _ _ hAB _ ihAB ih =>
    have ⟨heAB, _⟩ := ihAB hΓ
    have ⟨he, hty⟩ := ih hΓ
    refine ⟨he, hAB.defeqDF hty.typed, ?_⟩
    intro Δ Γ₀ σ ρ hΔ W hA m hm
    have ⟨a, ha, hht⟩ := hty.approx hΔ W hA hm
    exact ⟨a, (heAB hΔ W hA).1 ha, hht⟩
  -- everything below is one rule of the induction, each an independent
  -- obligation; see §4 of `presheaf-proof-strategy.md` for what each needs
  -- the slot's typing is `Adm`'s own, read off at the index by `Adm.lookup`
  | @bvar _ _ _ _ hl hA _ =>
    refine ⟨SoundEq.refl, .bvar hl hA, ?_⟩
    intro Δ Γ₀ σ ρ hΔ W hAdm m hm
    obtain ⟨a, ha, hty⟩ := hAdm.lookup hl
    refine ⟨a, ha, TShape.HasType.mono_l hΔ hty ?_⟩
    cases hm with
    | bot => exact TShape.bot_le' rfl
    | bvar _ hle => exact hle
  | sort =>
    exact sound_atom .sort Interp.le_sort Interp.sort' .sort
  | @unit _ r =>
    exact sound_atom .unit Interp.le_unit Interp.sort' (.unit (fun x => x))
  | star => exact sound_of_bot .star (fun .bot => rfl) (fun .bot => rfl)
  -- the lookup, typed: `SoundEq` moves the query's term along `a ≡ a'`,
  -- and `SoundTy` walks the generator chain of `HasType.lam`
  | @appDF _ A u B v f f' a a' hA hB hff' haa' hBinst ihA ihB ihf iha ihBinst =>
    have hΓA : ⊢ (A :: _) := ⟨hΓ, _, hA.hasType.1⟩
    refine ⟨sound_app_eq hff' haa' (ihf hΓ).2 (ihf hΓ).1 (iha hΓ).1,
      sound_app_ty hΓ hA.hasType.1 hB.hasType.1 haa'.hasType.1
        (.appDF hA hB hff'.hasType.1 haa'.hasType.1 hBinst.hasType.1)
        (ihf hΓ).2 (ihBinst hΓ).2 (IsDefEq.dir hΓ haa').1 (IsDefEq.dir hΓA hB).1⟩
  | @lamDF _ A A' u B v body body' hAA' hB hbody hbody' hPi ihA ihB ihbody ihbody' ihPi =>
    have hΓA : ⊢ (A :: _) := ⟨hΓ, _, hAA'.hasType.1⟩
    have hΓA' : ⊢ (A' :: _) := ⟨hΓ, _, hAA'.hasType.2⟩
    exact ⟨sound_lam_eq hAA' (ihA hΓ).1 (ihA hΓ).2 (ihbody hΓA).1 (ihbody' hΓA').1,
      sound_lam_ty hΓ hAA'.hasType.1 hB (IsDefEq.lamDF hAA' hB hbody hbody' hPi).hasType.1
        (ihA hΓ).2 (ihB hΓA).2 (ihbody hΓA).2 (IsDefEq.dir hΓA hB).1⟩
  -- the two halves proved above
  | forallEDF hAA' hB hB' ihA ihB ihB' =>
    have ⟨heA, htyA⟩ := ihA hΓ
    have ⟨heB, htyB⟩ := ihB ⟨hΓ, _, hAA'.hasType.1⟩
    have ⟨heB', _⟩ := ihB' ⟨hΓ, _, hAA'.hasType.2⟩
    exact ⟨sound_forallE_eq hAA' hB hB' heA htyA heB heB',
      sound_forallE_ty htyA htyB hAA'.hasType.1⟩
  -- Σ now has real rules, mirroring Π, so these are no longer vacuous
  | sigmaDF hAA' hB hB' ihA ihB ihB' =>
    have ⟨heA, htyA⟩ := ihA hΓ
    have ⟨heB, htyB⟩ := ihB ⟨hΓ, _, hAA'.hasType.1⟩
    have ⟨heB', _⟩ := ihB' ⟨hΓ, _, hAA'.hasType.2⟩
    exact ⟨sound_sigma_eq hAA' hB hB' heA htyA heB heB',
      sound_sigma_ty htyA htyB hAA'.hasType.1⟩
  | @pairDF _ A A' u B v B' a a' b b' hAA' hB hB' haa' hbb' hBa hSg
      ihA ihB ihB' iha ihb ihBa ihSg =>
    have hΓA : ⊢ (A :: _) := ⟨hΓ, _, hAA'.hasType.1⟩
    have hΓA' : ⊢ (A' :: _) := ⟨hΓ, _, hAA'.hasType.2⟩
    exact ⟨sound_pair_eq hAA' haa' (ihA hΓ).1 (ihA hΓ).2 (iha hΓ).1 (ihb hΓ).1
        (ihB hΓA).1 (ihB' hΓA').1,
      sound_pair_ty hΓ hAA'.hasType.1 hB.hasType.1
        (IsDefEq.pairDF hAA' hB hB' haa' hbb' hBa hSg).hasType.1
        (ihA hΓ).2 (IsDefEq.dir hΓ hAA').1 (iha hΓ).2 (ihB hΓA).2
        (IsDefEq.dir hΓA hB).1⟩
  | fstDF hA hB _ _ _ ih => exact sound_fst hA hB (ih hΓ).1 (ih hΓ).2
  | @sndDF _ A u B v p p' hA hB hpp' hBfst ihA ihB ihp ihBfst =>
    have hΓA : ⊢ (A :: _) := ⟨hΓ, _, hA.hasType.1⟩
    have hfst := IsDefEq.fstDF hA hB hpp'.hasType.1
    exact ⟨sound_snd_eq hA hB hpp' (ihp hΓ).2 (ihp hΓ).1,
      sound_snd_ty hΓ hA hB hfst (.sndDF hA hB hpp'.hasType.1 hBfst.hasType.1)
        (ihp hΓ).2 (ihBfst hΓ).2
        (IsDefEq.dir hΓ hfst).1 (IsDefEq.dir hΓA hB).1⟩
  -- padded with typings of both sides, so `SoundTy` is the IH for the
  -- left-hand side and only `SoundEq` has content
  | @beta _ A u e B e' hA hbe he' hredex _ ihA ihe ihe' ihredex _ =>
    have hΓA : ⊢ (A :: _) := ⟨hΓ, _, hA.hasType.1⟩
    exact ⟨sound_beta hΓ hA.hasType.1 hbe.hasType.1 he'.hasType.1 (ihA hΓ).2 (ihe' hΓ).2
        (IsDefEq.dir hΓ he').1 (IsDefEq.dir hΓA hbe).1,
      (ihredex hΓ).2⟩
  | eta => sorry
  | @unit_eta _ _ r _ ih =>
    exact sound_of_bot_at
      (sound_of_bot (t := .star r) (t' := .star r) (A := .unit r) .star
        (fun .bot => rfl) (fun .bot => rfl)).2
      (by intro _ _ _ _ _ _ _ _ h; cases h; rfl)
      (by intro _ _ _ _ hΔ W hAdm _ h; exact Interp.eq_bot_of_unit (ih hΓ).2 hΔ W hAdm h)
  -- unblocked by the Σ rules: `fst` now reads the first component off a
  -- pair shape, so the two sides really can have the same approximants
  -- the β-rules of Σ: the projection's approximants are the component's,
  -- and the typing then comes from the component's by `SoundTy.of_eq`
  | @pair_fst _ A u B v a b hA hB ha hb hfst ihA _ iha _ _ =>
    have he := sound_pair_fst (B := B) (a := a) (b := b) hA.hasType.1
    exact ⟨he, SoundTy.of_eq (.symm (.pair_fst hA hB ha hb hfst)) he.symm (iha hΓ).2⟩
  | @pair_snd _ A u B v a b hA hB ha hb hsnd ihA _ iha ihb _ =>
    -- `snd`'s rule is a query at `fst`, so this case needs the β-rule for
    -- `fst` as well, which its own premises give
    have hpair := IsDefEq.pairDF hA hB hB ha hb
      (IsDefEq.inst_cod hΓ hA.hasType.1 ha.hasType.1 hB) (IsDefEq.sigmaDF hA hB hB)
    have hfst := IsDefEq.pair_fst hA.hasType.1 hB.hasType.1 ha.hasType.1 hb.hasType.1
      (IsDefEq.fstDF hA.hasType.1 hB.hasType.1 hpair)
    have he := sound_pair_snd (B := B) (v := v) hΓ hA.hasType.1 ha.hasType.1 hfst
      (ihA hΓ).2 (iha hΓ).2 (ihb hΓ).2 (IsDefEq.dir hΓ ha).1 (IsDefEq.dir hΓ hb).1
    exact ⟨he, SoundTy.of_eq (.symm (.pair_snd hA hB ha hb hsnd)) he.symm (ihb hΓ).2⟩
  | fst_snd => sorry
  | nat =>
    exact sound_atom .nat Interp.le_nat Interp.sort' .nat
  | zero =>
    exact sound_atom .zero Interp.le_zero Interp.nat' .zero
  | succDF _ ih => exact sound_succ (ih hΓ).1 (ih hΓ).2
  | @natCaseDF _ v C C' M M' a a' b b' hCC' hMM' haa' hbb' hCM _ ihM iha ihb ihCM =>
    exact ⟨sound_natCase hMM' (ihM hΓ).1 (ihM hΓ).2 (iha hΓ).1 (ihb ⟨hΓ, _, .nat⟩).1,
      sound_natCase_ty hΓ hCC'.hasType.1
        (IsDefEq.natCaseDF hCC' hMM' haa' hbb' hCM).hasType.1
        (iha hΓ).2 (ihb ⟨hΓ, _, .nat⟩).2 (ihM hΓ).2 (IsDefEq.dir hΓ hMM').1⟩
  -- the computation rules again: padded, so `SoundTy` is an IH
  | natCase_zero _ _ _ _ _ _ _ ihredex => exact ⟨sound_natCase_zero, (ihredex hΓ).2⟩
  | @natCase_succ _ C v n a b _ hn _ hb _ _ _ _ _ _ ihredex _ =>
    exact ⟨sound_natCase_succ hΓ hn.hasType.1 hb.hasType.1 (IsDefEq.dir hΓ hn).1,
      (ihredex hΓ).2⟩
  | @YDF _ A A' u b b' hAA' hb hb' ihA ihb ihb' =>
    have hΓA : ⊢ (A :: _) := ⟨hΓ, _, hAA'.hasType.1⟩
    have hΓA' : ⊢ (A' :: _) := ⟨hΓ, _, hAA'.hasType.2⟩
    have hYY' : _ ⊢ Term.Y A b ≡ Term.Y A' b' : A := .YDF hAA' hb hb'
    exact ⟨sound_Y_eq hΓ hAA' hYY' hb hb' (ihA hΓ).1 (ihA hΓ).2
        (ihb hΓA).2 (ihb hΓA).1
        (SoundTy.of_eq hb' (ihb' hΓA').1 (ihb' hΓA').2) (ihb' hΓA').1.symm,
      sound_Y_ty hAA'.hasType.1 hYY'.hasType.1 (ihA hΓ).2 (ihb hΓA).2⟩
  | @Y_unfold _ A u b hA hb hY hunf _ _ ihY _ =>
    exact ⟨sound_Y_unfold hA.hasType.1 hY.hasType.1 (IsDefEq.dir hΓ hY).1, (ihY hΓ).2⟩
  | idDF hAA' haa' hbb' _ _ _ => exact sound_id hAA' haa' hbb'
  | reflDF hA haa' hid _ iha _ => exact sound_refl hA haa' hid (iha hΓ).1
  | @trDF _ A A' u a a' b b' v C C' X X' r H H' hAA' haa' hbb' hC hC' hXX' hHH' hCb hid
      ihA iha ihb ihC ihC' ihX ihH =>
    have hΓA : ⊢ (A :: _) := ⟨hΓ, _, hAA'.hasType.1⟩
    have hΓA' : ⊢ (A' :: _) := ⟨hΓ, _, hAA'.hasType.2⟩
    exact ⟨sound_tr_eq hΓ hAA' haa' hbb' hC hC' (ihA hΓ).2 (ihA hΓ).1 (iha hΓ).1 (ihb hΓ).1
        (ihC hΓA).1 (ihC' hΓA').1 (ihX hΓ).1 (ihH hΓ).1,
      sound_tr_ty (IsDefEq.trDF hAA' haa' hbb' hC hC' hXX' hHH' hCb hid).hasType.1
        (IsDefEq.dir hΓ hbb').1⟩
  | @tr_refl _ A u a v C X r hA ha hC hx htr ihA iha ihC ihx ihtr =>
    exact ⟨sound_tr_refl_eq hA ha (ihA hΓ).2 (iha hΓ).2 (IsDefEq.dir hΓ ha).1
        (ihC ⟨hΓ, _, hA⟩).2 (ihx hΓ).2,
      (ihtr hΓ).2⟩
  -- both sides are typed at a proposition, so both collapse to `⊥`
  | proofIrrel _ _ _ ih₁ ih₂ ih₃ =>
    exact sound_of_bot_at (ih₂ hΓ).2
      (by intro _ _ _ _ hΔ W hAdm _ h
          exact Interp.eq_bot_of_prop (ih₁ hΓ).2 (ih₂ hΓ).2 hΔ W hAdm h)
      (by intro _ _ _ _ hΔ W hAdm _ h
          exact Interp.eq_bot_of_prop (ih₁ hΓ).2 (ih₃ hΓ).2 hΔ W hAdm h)
