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
| `HasFixedness Γ t A` | `SoundTy` |
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
def SoundTy (Γ : List Term) (t A : Term) : Prop :=
  ∀ {{Δ Γ₀ σ ρ}}, ⊢ Δ → Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ₀ Γ σ ρ →
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
    (he : SoundEq Γ t t') (h : SoundTy Γ t A) : SoundTy Γ t' A := by
  intro Δ Γ₀ σ ρ hΔ W hA m hm
  exact h hΔ W hA ((he hΔ W hA).2 hm)

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
theorem sound_of_bot {Γ : List Term} {t t' A : Term}
    (h : ∀ {Δ Γ' σ ρ m}, Interp Δ Γ' t σ ρ m → m.2 = Shape.bot)
    (h' : ∀ {Δ Γ' σ ρ m}, Interp Δ Γ' t' σ ρ m → m.2 = Shape.bot) :
    SoundEq Γ t t' ∧ SoundTy Γ t A :=
  ⟨fun _ _ _ _ _ _ _ _ =>
      ⟨fun hm => Interp.of_bot (h hm), fun hm => Interp.of_bot (h' hm)⟩,
    fun _ _ _ _ _ _ _ _ hm =>
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
  obtain ⟨a, ha, hty⟩ := ht hΔ W hAdm H
  obtain ⟨b, hb, htya⟩ := hp hΔ W hAdm ha
  rcases TShape.le_prop_cases (Interp.le_sort hb) with hbb | hbb
  · -- the type's type is `⊥`, so everything below it collapses outright
    exact TShape.HasType.bot_r hΔ (TShape.HasType.bot_r hΔ hbb htya) hty
  · -- the type is a proposition, so its inhabitants are `⊥`
    exact TShape.HasType.proofIrrel hΔ hty (htya.sort_level hbb (k' := 0))

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
    SoundEq Γ t t ∧ SoundTy Γ t A :=
  ⟨fun _ _ _ _ _ _ _ _ => Iff.rfl,
    fun _ _ _ _ hΔ _ _ _ hm => ⟨a, ha, TShape.HasType.mono_l hΔ hsa (hle hm)⟩⟩

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
  have ⟨a, ha, hty⟩ := h hΔ W hAdm hb
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
    sound_forallE_eq_of hAA'.symm hB'.symm ihA.symm (SoundTy.of_eq ihA ihAty) ihB'.symm
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
  | bvar => sorry
  | appDF => sorry
  | lamDF => sorry
  | sigmaDF => sorry
  | pairDF => sorry
  | fstDF => sorry
  | sndDF => sorry
  | succDF => sorry
  | natCaseDF => sorry
  | idDF => sorry
  | reflDF => sorry
  | trDF => sorry
  -- the computation rules are padded with typings of both sides, so each
  -- of these is its two premises' conclusions
  | beta _ _ _ _ _ _ _ _ ih₃ ih₄ => exact ⟨(ih₃ hΓ).1, (ih₄ hΓ).1⟩
  | eta _ _ ih₁ ih₂ => exact ⟨(ih₂ hΓ).1, (ih₁ hΓ).1⟩
  | unit_eta _ ih => exact ⟨dir_of_bot (fun .bot => rfl), (ih hΓ).1⟩
  | pair_fst _ _ _ _ _ _ _ _ _ ih₅ => exact ⟨(ih₅ hΓ).1, sorry⟩
  | pair_snd _ _ _ _ _ _ _ _ _ ih₅ => exact ⟨(ih₅ hΓ).1, sorry⟩
  | fst_snd _ _ _ ih₂ => exact ⟨(ih₂ hΓ).1, sorry⟩
  | natCase_zero => sorry
  | natCase_succ => sorry
  | YDF => sorry
  | Y_unfold => sorry
  | tr_refl => sorry
  | proofIrrel => sorry

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
  | symm _ ih =>
    have ⟨he, hty⟩ := ih hΓ
    exact ⟨he.symm, SoundTy.of_eq he hty⟩
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
  | defeqDF _ _ ihAB ih =>
    have ⟨heAB, _⟩ := ihAB hΓ
    have ⟨he, hty⟩ := ih hΓ
    refine ⟨he, ?_⟩
    intro Δ Γ₀ σ ρ hΔ W hA m hm
    have ⟨a, ha, hht⟩ := hty hΔ W hA hm
    exact ⟨a, (heAB hΔ W hA).1 ha, hht⟩
  -- everything below is one rule of the induction, each an independent
  -- obligation; see §4 of `presheaf-proof-strategy.md` for what each needs
  | bvar => sorry
  | sort =>
    refine sound_atom Interp.le_sort (fun hw h => .sort hw h) Interp.sort' trivial fun {_} => ?_
    exact .sort
  | @unit _ r =>
    refine sound_atom Interp.le_unit (fun hw h => .unit hw h) Interp.sort' trivial fun {_} => ?_
    exact .unit (fun x => x)
  | star => exact sound_of_bot (fun .bot => rfl) (fun .bot => rfl)
  | appDF => sorry
  | lamDF => sorry
  -- the two halves proved above
  | forallEDF hAA' hB hB' ihA ihB ihB' =>
    have ⟨heA, htyA⟩ := ihA hΓ
    have ⟨heB, htyB⟩ := ihB ⟨hΓ, _, hAA'.hasType.1⟩
    have ⟨heB', _⟩ := ihB' ⟨hΓ, _, hAA'.hasType.2⟩
    exact ⟨sound_forallE_eq hAA' hB hB' heA htyA heB heB',
      sound_forallE_ty htyA htyB hAA'.hasType.1⟩
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
      (fun {_} => .nat)
  | zero =>
    exact sound_atom Interp.le_zero (fun hw h => .zero hw h) Interp.nat' trivial
      (fun {_} => .zero)
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
  | proofIrrel => sorry
