import DomainSemantics.Interp
import DomainSemantics.Canon
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

/-- The stage an instantiation is read at: `(one a).comp σ` is `σ`
extended by `a[σ]`. -/
theorem Subst.one_comp {a : Term} {σ : Subst} :
    (Subst.one a).comp σ = σ.cons (a.subst σ) := by
  rw [Subst.cons_comp, Subst.id_comp]

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

/-- **Saturation**: every approximant of `t` is below an approximant that
is *hereditarily* typed at an approximant of `A`.

This is the original's `HasFixedness` — `rawExtend ⟦A⟧ ⟦t⟧ = ⟦t⟧` — read
through "ideal = set of approximants".  `Shape.Dom` itself is not
downward closed, and this form is: it is what every slot in the model
needs (`Adm`), and what η reads its typed inputs off (§4.5g). -/
def SoundDom (Γ : List Term) (t A : Term) : Prop :=
  ∀ {{Δ Γ₀ : List Term}} {{σ ρ}}, ⊢ Δ → Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ₀ Γ σ ρ →
    ∀ {m}, Interp Δ Γ t σ ρ m →
      ∃ m' a, Interp Δ Γ t σ ρ m' ∧ TShape.LE Δ m m' ∧
        Interp Δ Γ A σ ρ a ∧ TShape.Slot Δ (A.subst σ) a (t.subst σ) m'

/-- Every approximant of `t`, read as a code, names `t`: what saturation
at a sort says, and what an atom's top shape gives by downward closure. -/
def CodeAt (Γ : List Term) (t : Term) : Prop :=
  ∀ {{Δ Γ₀ : List Term}} {{σ ρ}}, ⊢ Δ → Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ₀ Γ σ ρ →
    ∀ {m}, Interp Δ Γ t σ ρ m → TShape.CodeCanonS Δ (t.subst σ) m

/-- **On a filtering type a value names its term iff it does so as a
code**: the heads that differ are λ and pair, which are typed only at
binders. -/
theorem TShape.ValCanon.of_filter {Δ : List Term} {t : Term} {m a : TShape}
    (h : TShape.HasType Δ m a) (hnb : ¬ a.IsBinder) (hc : TShape.CodeCanonS Δ t m) :
    TShape.ValCanon Δ t m := by
  obtain ⟨n, s⟩ := m
  cases n with
  | zero => exact hc
  | succ n =>
    cases s with
    | lam | pair => cases h <;> exact (hnb trivial).elim
    | _ => first | exact hc | trivial

/-- At `nat` (and any other filtering code) saturation is just typing:
nothing below such a code binds, so `Dom` is `HasType` there, and the
names are read as codes, where they are downward closed. -/
theorem SoundDom.of_typedAt {Γ : List Term} {t A : Term}
    (hnb : ∀ {Δ : List Term} {σ ρ : _} {a : TShape}, Interp Δ Γ A σ ρ a → ¬ a.IsBinder)
    (h : TypedAt Γ t A) (hct : CodeAt Γ t) (hcA : CodeAt Γ A) : SoundDom Γ t A := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  obtain ⟨a, ha, hty⟩ := h hΔ W hAdm hm
  exact ⟨m, a, hm, TShape.LE.refl hty.wf.1, ha, (.of_dom (TShape.NamedO.of_not_binder (hnb ha) hty) (TShape.ValCanon.of_filter hty (hnb ha) (hct hΔ W hAdm hm))),
    hcA hΔ W hAdm ha⟩

/-- An atom's approximants are below one canonical top shape. -/
theorem CodeAt.of_top {Γ : List Term} {t : Term} {s : TShape}
    (hle : ∀ {Δ Γ' σ ρ m}, Interp Δ Γ' t σ ρ m → TShape.LE Δ m s)
    (hs : ∀ {Δ : List Term} {σ}, ⊢ Δ → Ctx.SubstEq Δ σ σ Γ → TShape.CodeCanonS Δ (t.subst σ) s) :
    CodeAt Γ t := by
  intro Δ Γ₀ σ ρ hΔ W _ m hm
  exact TShape.CodeCanonS.mono hΔ (hle hm) (hs hΔ W)

theorem CodeAt.nat {Γ : List Term} : CodeAt Γ Term.nat :=
  CodeAt.of_top Interp.le_nat (s := TShape.nat)
    (fun _ _ => show TyEq _ _ _ from TyEq.refl .nat)

theorem CodeAt.sort {Γ : List Term} {r : Bool} : CodeAt Γ (Term.sort r) :=
  CodeAt.of_top Interp.le_sort (s := TShape.sort r)
    (fun _ _ => (TShape.CodeCanonS.sort_iff (k := 0)).2 (TyEq.refl .sort))

/-- A numeral names whatever it stands for: it carries no names. -/
theorem TShape.ValCanon.of_nat {Δ : List Term} {t : Term} {v : TShape} (hΔ : ⊢ Δ)
    (h : TShape.HasType Δ v TShape.nat) : TShape.ValCanon Δ t v :=
  Shape.ValCanon.of_numeral
    (TShape.HasType.isNumeral hΔ (TShape.LE.refl (a := TShape.nat) trivial) h)

/-- So a term of type `nat` names itself, read as a code. -/
theorem CodeAt.of_nat {Γ : List Term} {t : Term} (h : TypedAt Γ t Term.nat) : CodeAt Γ t := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  obtain ⟨c, hc, hty⟩ := h hΔ W hAdm hm
  exact Shape.ValCanon.toCode
    (Shape.ValCanon.of_numeral (TShape.HasType.isNumeral hΔ (Interp.le_nat hc) hty))

/-- `nat`'s approximants are `⊥` or `nat`. -/
theorem SoundDom.nat {Γ : List Term} {t : Term} (h : TypedAt Γ t Term.nat) :
    SoundDom Γ t Term.nat :=
  SoundDom.of_typedAt (fun ha => TShape.not_binder_of_le (Interp.le_nat ha) (fun h => h)) h
    (CodeAt.of_nat h) CodeAt.nat

/-- At a sort the code only filters. -/
theorem SoundDom.of_sort {Γ : List Term} {t : Term} {r : Bool} (h : TypedAt Γ t (.sort r))
    (hct : CodeAt Γ t) : SoundDom Γ t (.sort r) :=
  SoundDom.of_typedAt (fun ha => TShape.not_binder_of_le (Interp.le_sort ha) (fun h => h)) h
    hct CodeAt.sort

theorem SoundDom.codeAt {Γ : List Term} {T : Term} {u : Bool} (h : SoundDom Γ T (.sort u)) :
    CodeAt Γ T := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  obtain ⟨m', _, hm', hle, _, hNV, _⟩ := h hΔ W hAdm hm
  have hcan := hNV.val
  exact TShape.CodeCanonS.mono hΔ hle  hcan.toCode

/-- Saturation transports along an equality of terms, both sides being
the same set of approximants; the slot carries its own code, so moving
the name along the equation takes nothing extra (`Slot.defeq`). -/
theorem SoundDom.of_eq {Γ : List Term} {t t' A : Term} (hs : Γ ⊢ t ≡ t' : A)
    (he : SoundEq Γ t t') (h : SoundDom Γ t A) : SoundDom Γ t' A := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  obtain ⟨m', c, hm', hle, hc, hslot⟩ := h hΔ W hAdm ((he hΔ W hAdm).2 hm)
  exact ⟨m', c, (he hΔ W hAdm).1 hm', hle, hc, hslot.defeq hΔ (hs.subst hΔ W)⟩

/-- And along an equality of *types*, which is what `defeqDF` moves. -/
theorem SoundDom.of_tyEq {Γ : List Term} {t A B : Term} {u : Bool} (hs : Γ ⊢ A ≡ B : .sort u)
    (hAB : SoundEq Γ A B) (h : SoundDom Γ t A) : SoundDom Γ t B := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  obtain ⟨m', c, hm', hle, hc, hslot⟩ := h hΔ W hAdm hm
  exact ⟨m', c, hm', hle, (hAB hΔ W hAdm).1 hc,
    hslot.conv (TyEq.symm ⟨u, hs.subst hΔ W⟩)⟩

/-- **A variable's slot is hereditarily typed and names the variable** —
that is what `Adm` says, and it is the base case of saturation. -/
theorem SoundDom.bvar {Γ : List Term} {i : Nat} {A : Term} (hl : Lookup Γ i A) :
    SoundDom Γ (.bvar i) A := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  obtain ⟨a, ha, hn, hac⟩ := hAdm.lookupCanon hl
  exact ⟨ρ i, a, .bvar (hAdm.wf i) (TShape.LE.refl (hAdm.wf i)), Interp.le_bvar hm, ha, hn, hac⟩

theorem SoundEq.refl {Γ : List Term} {t : Term} : SoundEq Γ t t :=
  fun _ _ _ _ _ _ _ => Iff.rfl

theorem SoundEq.symm {Γ : List Term} {t t' : Term} (h : SoundEq Γ t t') : SoundEq Γ t' t :=
  fun _ _ _ _ hΔ W hA => (h hΔ W hA).symm

theorem SoundEq.trans {Γ : List Term} {t t' t'' : Term}
    (h : SoundEq Γ t t') (h' : SoundEq Γ t' t'') : SoundEq Γ t t'' :=
  fun _ _ _ _ hΔ W hA => (h hΔ W hA).trans (h' hΔ W hA)

/-- **Typing follows from saturation.**  An approximant sits below a
hereditarily typed one, and typing is lower-closed, so the dominator's
code types it.  This is what replaces the lookup inductions the Σ-side
used to need: with `sound_join` on `Dom` (§4.7e), the way to type a
lookup value is to saturate the term it approximates. -/
theorem SoundTy.of_dom {Γ : List Term} {t A : Term} (hty : Γ ⊢ t : A)
    (h : SoundDom Γ t A) : SoundTy Γ t A := by
  refine ⟨hty, ?_⟩
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  obtain ⟨_, a, _, hle, ha, hdom, _⟩ := h hΔ W hAdm hm
  exact ⟨a, ha, TShape.HasType.mono_l hΔ hdom.hasType hle⟩

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
order are level-free. -/

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
  | refl hc _ =>
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

/-- When every approximant is `⊥` there is nothing to saturate: `⊥` is
hereditarily typed at `⊥`, which approximates every type. -/
theorem SoundDom.of_bot {Γ : List Term} {t A : Term}
    (h : ∀ {Δ Γ₀ : List Term} {σ ρ}, ⊢ Δ → Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ₀ Γ σ ρ →
      ∀ {m}, Interp Δ Γ t σ ρ m → m.2 = Shape.bot) :
    SoundDom Γ t A := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  obtain ⟨n, s'⟩ := m
  have hb : s' = Shape.bot := h hΔ W hAdm hm
  subst hb
  exact ⟨_, TShape.bot, hm, TShape.LE.refl hm.wf, .bot, (.of_dom (TShape.NamedO.bot (n := n) (.bot (.bot .sort))) (TShape.ValCanon.of_bot rfl)), TShape.CodeCanonS.bot⟩

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

/-- `SoundTy`'s two halves as the predicates `Interp.lean` states them:
`Term.Pinned`'s conditions are these, at the subterm they belong to. -/
theorem SoundTy.typedAt {Γ : List Term} {t A : Term} (h : SoundTy Γ t A) :
    TypedAt Γ t A := by
  intro _ _ _ _ hΔ W hAdm _ hm; exact h.approx hΔ W hAdm hm

theorem SoundTy.isTypeAt {Γ : List Term} {A : Term} {u : Bool}
    (h : SoundTy Γ A (.sort u)) (hd : SoundDom Γ A (.sort u)) : IsTypeAt Γ A := by
  intro _ _ _ _ hΔ W hAdm _ hb; exact ⟨h.isType hΔ W hAdm hb, hd.codeAt hΔ W hAdm hb⟩

/-! ### The canonical valuation at a single substitution

`Interp.to_substTerm` returns *some* valuation approximating `θ`, and
`SoundTy` is read at admissible ones — so to use a subterm's `SoundTy`
after a substitution one needs the returned valuation to be admissible,
which it need not be (admissibility is not upward closed, §3.1d).

At a **single** substitution it is, and the valuation is canonical: the
source valuation with the argument's approximant pushed on.  This is the
depth-0 case of the original's `SingleSubstitution`, and it is the level
`Interp.inst` itself works at. -/

/-- The valuation `to_substTerm` returns at `Subst.one a` is below the
canonical `ρ.push (ρ' 0)`, which approximates `one a` and is admissible.
No join is needed and nothing grows: slot `0` is already an approximant
of `a`, so `SoundTy a A` types it, and the type `A` lives *below* the
substituted variable, so its own approximant does not move. -/
theorem Valuation.Approx.canon_one {Γ Γ₀ Δ : List Term} {A a : Term} {σ ρ ρ'}
    (hΔ : ⊢ Δ) (hΓ : ⊢ Γ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ) (hadom : SoundDom Γ a A)
    (hρ' : Valuation.Approx Δ Γ (Subst.one a) σ ρ ρ') :
    ∃ x, Valuation.LE Δ ρ' (ρ.push x) ∧
      Valuation.Approx Δ Γ (Subst.one a) σ ρ (ρ.push x) ∧
      Adm Δ Γ₀ (A :: Γ) ((Subst.one a).comp σ) (ρ.push x) := by
  have hwρ : Valuation.WF Δ ρ := hAdm.wf
  -- the slot is the argument's approximant, enlarged until it is
  -- hereditarily typed — which is all the extended stage asks of it
  obtain ⟨x, α, hx, hlex, hα, hNV, hαc⟩ := hadom hΔ W hAdm (hρ' 0)
  have hxα := hNV.dom
  have hxc := hNV.val
  refine ⟨x, fun i => ?_, fun i => ?_, ?_⟩
  · cases i with
    | zero => exact hlex
    | succ i => exact Interp.le_bvar (Γ := Γ) (i := i) (σ := σ) (hρ' (i + 1))
  · cases i with
    | zero => exact hx
    | succ i => exact .bvar (hwρ i) (TShape.LE.refl (hwρ i))
  · rw [Subst.one_comp]
    exact Adm.cons hAdm hΓ hα hx.wf (.of_dom hxα hxc) hαc

/-- `canon_one` packaged as `Subst.Saturates`: a single substitution
saturates, which is the hypothesis `Interp.to_substTerm` reads its
clause conditions under. -/
theorem Subst.Saturates.one {Γ Γ₀ Δ : List Term} {A a : Term} {σ ρ}
    (hΔ : ⊢ Δ) (hΓ : ⊢ Γ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ) (hadom : SoundDom Γ a A) :
    Subst.Saturates Δ Γ₀ (A :: Γ) Γ (Subst.one a) σ ρ := fun hρ' =>
  let h := Valuation.Approx.canon_one hΔ hΓ W hAdm hadom hρ'
  ⟨_, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2⟩

theorem sound_forallE_ty {Γ : List Term} {A B : Term} {u v : Bool} (ihAd : SoundDom Γ A (.sort u))
    (ihB : SoundTy (A :: Γ) B (.sort v))
    (hAty : Γ ⊢ A : .sort u) :
    SoundTy Γ (.forallE A B) (.sort v) := by
  refine ⟨.forallEDF hAty ihB.typed ihB.typed, ?_⟩
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  cases hm with
  | bot =>
    exact ⟨TShape.sort v, Interp.sort', .bot .sort⟩
  | forallE hA hd hwf hNV hbody hw hle =>
    refine ⟨TShape.sort v, Interp.sort', TShape.HasType.mono_l hΔ ?_ hle⟩
    -- the domain half is now the constructor's own premise; only the
    -- codomain runs an induction hypothesis
    refine .forallE hd (fun e he => ?_) hwf
    · -- the codomain, at the stage extended by the entry's label: the
      -- entry's own data is exactly what `Adm.cons` and `SubstEq.cons` ask for
      have hwe := hwf.2.2.2.1.1 e he
      have W' : Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A :: Γ) :=
        .cons W hAty hwe.2.1
      have hAdm' : Adm Δ Γ₀ (A :: Γ) (σ.cons e.tm) (ρ.push (Shape.T e.inp)) :=
        .cons hAdm W.wf hA hwe.2.2.1 (hNV e he)
          (ihAd.codeAt hΔ W hAdm hA)
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
    (ihA : SoundEq Γ A A') (ihAtyD : SoundDom Γ A (.sort u))
    (ihB : SoundEq (A :: Γ) B B')
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {m : TShape} (H : Interp Δ Γ (.forallE A B) σ ρ m) :
    Interp Δ Γ (.forallE A' B') σ ρ m := by
  have ⟨⟨_, hAσ⟩, _, hBσ⟩ :
      PiLabelEq Δ (A.subst σ) (B.subst σ.lift) (A'.subst σ) (B'.subst σ.lift) :=
    PiLabelEq.subst hΔ W ⟨⟨u, hAA'⟩, v, hBB'⟩
  have hΓA' : ⊢ (A' :: Γ) := ⟨W.wf, _, hAA'.hasType.2⟩
  cases H with
  | bot => exact .bot
  | forallE hA hd hwf hNV hbody hw hle hAt hBt =>
    have hdom := fun e he => (hNV e he).dom
    have hcan := fun e he => (hNV e he).val
    refine .forallE ((ihA hΔ W hAdm).1 hA) hd
      ⟨⟨_, hAσ.hasType.2⟩, ⟨_, (hAσ.defeqDF_l hΔ hBσ).hasType.2⟩, 
        Shape.WF.name (Shape.WFO.wf hwf.2.2.1)
          ((Shape.WFO.canon hwf.2.2.1).conv ⟨_, hAσ.symm⟩),
        ShapeFun.WF.name ((ShapeFun.WF.forget hwf.2.2.2.1).retype ⟨_, hAσ⟩)
          (fun e he => (ShapeFun.WF.canon hwf.2.2.2.1 e he).conv
            ⟨_, (hAσ.hasType.2).instDF hΔ .sort (hAσ.defeqDF_l hΔ hBσ).symm
              (hAσ.defeqDF ((hwf.2.2.2.1.1 e he).2.1))⟩), trivial⟩
      (fun e he => .of_dom (hdom e he) (hcan e he)) (fun e he => ?_) hw
      (hle.trans hΔ (TShape.LE.T.2
        ⟨⟨⟨_, hAσ⟩, _, hBσ⟩, .refl (Shape.WFO.wf hwf.2.2.1),
          .refl (ShapeFun.WF.forget hwf.2.2.2.1),
          Shape.WFO.canon hwf.2.2.1, ShapeFun.WF.canon hwf.2.2.2.1⟩))
      ⟨u, hAA'.hasType.2⟩ ⟨v, IsDefEq.ctx_id hΓA' (Ctx.SubstEq.defeqHead W.wf hAA')
        hBB'.hasType.2⟩
    · -- the body, at the stage extended by the entry's label
      have hwe := hwf.2.2.2.1.1 e he
      have W' : Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A :: Γ) :=
        .cons W hAA'.hasType.1 hwe.2.1
      have hAdm' : Adm Δ Γ₀ (A :: Γ) (σ.cons e.tm) (ρ.push (Shape.T e.inp)) :=
        .cons hAdm W.wf hA hwe.2.2.1 (hNV e he)
          (ihAtyD.codeAt hΔ W hAdm hA)
      exact Interp.ctx ((ihB hΔ W' hAdm').1 (hbody e he)) hΓA'
        (Ctx.SubstEq.defeqHead W.wf hAA')

/-- The `SoundEq` half of `forallEDF`: the two Π-types have the same
approximants at every stage.

Both directions are the same argument, run on the mirrored data -- which
is exactly why the rule carries its codomain premise twice, once over
each domain.  Without the `A' :: Γ` copy the backward direction would
have no induction hypothesis to run. -/
theorem sound_forallE_eq {Γ : List Term} {A A' B B' : Term} {u v : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u)
    (hB : A :: Γ ⊢ B ≡ B' : .sort v) (hB' : A' :: Γ ⊢ B ≡ B' : .sort v)
    (ihA : SoundEq Γ A A') (ihAtyD : SoundDom Γ A (.sort u))
    (ihB : SoundEq (A :: Γ) B B') (ihB' : SoundEq (A' :: Γ) B B') :
    SoundEq Γ (.forallE A B) (.forallE A' B') := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  exact ⟨sound_forallE_eq_of hAA' hB ihA ihAtyD ihB hΔ W hAdm,
    sound_forallE_eq_of hAA'.symm hB'.symm ihA.symm
      (SoundDom.of_eq hAA' ihA ihAtyD) ihB'.symm
      hΔ W hAdm⟩

/-! ## Σ, which mirrors Π

`Interp.sigma`'s clauses are `Interp.forallE`'s with the head changed, so
these two are `sound_forallE_ty and `sound_forallE_eq` with the head  The one real difference is the sort: the `TShape.HasType.sigma`
clause types its outputs at `.type` where `forallE` types them at the
same sort as the Π, so the codomain's typing needs `cumul` on the way in
— which is `SoundTy.isType` rather than `SoundTy.hasType`. -/

/-- The `SoundTy` half of `sigmaDF`. -/
theorem sound_sigma_ty {Γ : List Term} {A B : Term} {u v : Bool} (ihAd : SoundDom Γ A (.sort u))
    (ihB : SoundTy (A :: Γ) B (.sort v))
    (hAty : Γ ⊢ A : .sort u) :
    SoundTy Γ (.sigma A B) .type := by
  refine ⟨.sigmaDF hAty ihB.typed ihB.typed, ?_⟩
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  cases hm with
  | bot => exact ⟨TShape.type, Interp.sort', .bot .sort⟩
  | sigma hA hd hwf hNV hbody hw hle =>
    refine ⟨TShape.type, Interp.sort', TShape.HasType.mono_l hΔ ?_ hle⟩
    refine .sigma hd (fun e he => ?_) hwf
    have hwe := hwf.2.2.2.1.1 e he
    have W' : Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A :: Γ) :=
      .cons W hAty hwe.2.1
    have hAdm' : Adm Δ Γ₀ (A :: Γ) (σ.cons e.tm) (ρ.push (Shape.T e.inp)) :=
      .cons hAdm W.wf hA hwe.2.2.1 (hNV e he)
        (ihAd.codeAt hΔ W hAdm hA)
    exact ihB.isType hΔ W' hAdm' (hbody e he)

/-- **A forallE-type names itself**: its labels are its own, its domain
is an approximant of `A`, and its codomain entries are approximants of `B`
at stages extended by their labels, each of which names itself by its
own saturation. -/
theorem CodeAt.forallE {Γ : List Term} {A B : Term} {u v : Bool}
    (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) :
    CodeAt Γ (.forallE A B) := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  cases hm with
  | bot => exact TShape.CodeCanonS.bot
  | forallE hA hd hwf hNV hbody hw hle =>
    exact TShape.CodeCanonS.mono hΔ hle  ⟨v, (IsDefEq.forallEDF hAty hB hB).subst hΔ W⟩

/-- **A sigma-type names itself**: its labels are its own, its domain
is an approximant of `A`, and its codomain entries are approximants of `B`
at stages extended by their labels, each of which names itself by its
own saturation. -/
theorem CodeAt.sigma {Γ : List Term} {A B : Term} {u v : Bool}
    (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) :
    CodeAt Γ (.sigma A B) := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  cases hm with
  | bot => exact TShape.CodeCanonS.bot
  | sigma hA hd hwf hNV hbody hw hle =>
    exact TShape.CodeCanonS.mono hΔ hle  ⟨true, (IsDefEq.sigmaDF hAty hB hB).subst hΔ W⟩

/-- One direction of the `SoundEq` half of `sigmaDF`; see
`sound_forallE_eq_of` for what it. -/
theorem sound_sigma_eq_of {Γ : List Term} {A A' B B' : Term} {u v : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (hBB' : A :: Γ ⊢ B ≡ B' : .sort v)
    (ihA : SoundEq Γ A A') (ihAtyD : SoundDom Γ A (.sort u))
    (ihB : SoundEq (A :: Γ) B B')
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {m : TShape} (H : Interp Δ Γ (.sigma A B) σ ρ m) :
    Interp Δ Γ (.sigma A' B') σ ρ m := by
  have ⟨⟨_, hAσ⟩, _, hBσ⟩ :
      PiLabelEq Δ (A.subst σ) (B.subst σ.lift) (A'.subst σ) (B'.subst σ.lift) :=
    PiLabelEq.subst hΔ W ⟨⟨u, hAA'⟩, v, hBB'⟩
  have hΓA' : ⊢ (A' :: Γ) := ⟨W.wf, _, hAA'.hasType.2⟩
  cases H with
  | bot => exact .bot
  | sigma hA hd hwf hNV hbody hw hle hAt hBt =>
    have hdom := fun e he => (hNV e he).dom
    have hcan := fun e he => (hNV e he).val
    refine .sigma ((ihA hΔ W hAdm).1 hA) hd
      ⟨⟨_, hAσ.hasType.2⟩, ⟨_, (hAσ.defeqDF_l hΔ hBσ).hasType.2⟩, 
        Shape.WF.name (Shape.WFO.wf hwf.2.2.1)
          ((Shape.WFO.canon hwf.2.2.1).conv ⟨_, hAσ.symm⟩),
        ShapeFun.WF.name ((ShapeFun.WF.forget hwf.2.2.2.1).retype ⟨_, hAσ⟩)
          (fun e he => (ShapeFun.WF.canon hwf.2.2.2.1 e he).conv
            ⟨_, (hAσ.hasType.2).instDF hΔ .sort (hAσ.defeqDF_l hΔ hBσ).symm
              (hAσ.defeqDF ((hwf.2.2.2.1.1 e he).2.1))⟩), trivial⟩
      (fun e he => .of_dom (hdom e he) (hcan e he)) (fun e he => ?_) hw
      (hle.trans hΔ (TShape.LE.T.2
        ⟨⟨⟨_, hAσ⟩, _, hBσ⟩, .refl (Shape.WFO.wf hwf.2.2.1),
          .refl (ShapeFun.WF.forget hwf.2.2.2.1),
          Shape.WFO.canon hwf.2.2.1, ShapeFun.WF.canon hwf.2.2.2.1⟩))
      ⟨u, hAA'.hasType.2⟩ ⟨v, IsDefEq.ctx_id hΓA' (Ctx.SubstEq.defeqHead W.wf hAA')
        hBB'.hasType.2⟩
    · have hwe := hwf.2.2.2.1.1 e he
      have W' : Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A :: Γ) :=
        .cons W hAA'.hasType.1 hwe.2.1
      have hAdm' : Adm Δ Γ₀ (A :: Γ) (σ.cons e.tm) (ρ.push (Shape.T e.inp)) :=
        .cons hAdm W.wf hA hwe.2.2.1 (hNV e he)
          (ihAtyD.codeAt hΔ W hAdm hA)
      exact Interp.ctx ((ihB hΔ W' hAdm').1 (hbody e he)) hΓA'
        (Ctx.SubstEq.defeqHead W.wf hAA')

/-- The `SoundEq` half of `sigmaDF`. -/
theorem sound_sigma_eq {Γ : List Term} {A A' B B' : Term} {u v : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u)
    (hB : A :: Γ ⊢ B ≡ B' : .sort v) (hB' : A' :: Γ ⊢ B ≡ B' : .sort v)
    (ihA : SoundEq Γ A A') (ihAtyD : SoundDom Γ A (.sort u))
    (ihB : SoundEq (A :: Γ) B B') (ihB' : SoundEq (A' :: Γ) B B') :
    SoundEq Γ (.sigma A B) (.sigma A' B') := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  exact ⟨sound_sigma_eq_of hAA' hB ihA ihAtyD ihB hΔ W hAdm,
    sound_sigma_eq_of hAA'.symm hB'.symm ihA.symm
      (SoundDom.of_eq hAA' ihA ihAtyD) ihB'.symm
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
    Interp Δ Γ t σ ρ m → Interp Δ Γ t σ' ρ m :=
  Interp.stage hΔ hΓ H.annot.1 W

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
      TShape.NamedO Δ none a x → TShape.NamedO Δ none a y → TShape.Compat Δ x y →
      ∃ z, TShape.WF Δ z ∧ TShape.LE Δ x z ∧ TShape.LE Δ y z ∧ TShape.NamedO Δ none a z

/-- **`SoundJoin` holds, for every type.**  The subject join is
`TShape.NamedO.join`: no `Interp`, no `Adm`, no induction on `A`.  It is
stated with `Dom` rather than `HasType` because that is what survives
the graph-free Σ-value (§4.7e): `HasType` reads the second component's
code at a *dominator* of the first, and two dominators need not be
compatible, while `Dom` reads it at the first component itself, which
the shapes' own compatibility covers. -/
theorem sound_join {Γ : List Term} {A : Term} : SoundJoin Γ A := by
  intro Δ Γ₀ σ ρ hΔ _ _ a x y _ hx hy hxa hya hc
  exact ⟨x.join y, TShape.WF.join hΔ hc hx hy, (TShape.le_join hΔ hx hy hc).1,
    (TShape.le_join hΔ hx hy hc).2, TShape.NamedO.join hΔ hc hxa hya⟩

theorem sound_forallE_ub {Γ : List Term} {A B : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B ≡ B : .sort v)
    (ihAdir : SoundDir Γ A) (ihBdir : SoundDir (A :: Γ) B)
    {Δ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hwρ : Valuation.WF Δ ρ)
    {n₁ n₂} {d₁ : Shape n₁} {g₁ : ShapeFun n₁} {d₂ : Shape n₂} {g₂ : ShapeFun n₂}
    (hA₁ : Interp Δ Γ A σ ρ (Shape.T d₁))
    (hd₁ : TShape.HasType Δ (Shape.T d₁) TShape.type)
    (hwf₁ : Shape.WF (n := n₁+1) Δ (.forallE (A.subst σ) (B.subst σ.lift) d₁ g₁))
    (hNV₁ : ∀ e ∈ g₁, TShape.Named Δ (Shape.T d₁) e.tm (Shape.T e.inp))
    (hbody₁ : ∀ e ∈ g₁,
      Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push (Shape.T e.inp)) (Shape.T e.out))
    (hA₂ : Interp Δ Γ A σ ρ (Shape.T d₂))
    (hd₂ : TShape.HasType Δ (Shape.T d₂) TShape.type)
    (hwf₂ : Shape.WF (n := n₂+1) Δ (.forallE (A.subst σ) (B.subst σ.lift) d₂ g₂))
    (hNV₂ : ∀ e ∈ g₂, TShape.Named Δ (Shape.T d₂) e.tm (Shape.T e.inp))
    (hbody₂ : ∀ e ∈ g₂,
      Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push (Shape.T e.inp)) (Shape.T e.out)) :
    ∃ s, TShape.WF Δ s ∧ Interp Δ Γ (.forallE A B) σ ρ s ∧
      TShape.LE Δ (Shape.T (n := n₁+1) (.forallE (A.subst σ) (B.subst σ.lift) d₁ g₁)) s ∧
      TShape.LE Δ (Shape.T (n := n₂+1) (.forallE (A.subst σ) (B.subst σ.lift) d₂ g₂)) s := by
  have hdom₁ := fun e he => (hNV₁ e he).dom
  have hcan₁ := fun e he => (hNV₁ e he).val
  have hdom₂ := fun e he => (hNV₂ e he).dom
  have hcan₂ := fun e he => (hNV₂ e he).val
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hAty⟩
  have k₁ : n₁ ≤ max n₁ n₂ := Nat.le_max_left ..
  have k₂ : n₂ ≤ max n₁ n₂ := Nat.le_max_right ..
  -- the joined domain, from `A`'s own directedness
  have ⟨hcd, hdj⟩ := (ihAdir hΔ W hwρ).join hΔ hA₁ hA₂
  have hcd' : Shape.Compat Δ (d₁.lift (max n₁ n₂)) (d₂.lift (max n₁ n₂)) :=
    (TShape.Compat.def k₁ k₂).1 hcd
  have hwd₁ : Shape.WF Δ d₁ := Shape.WFO.wf hwf₁.2.2.1
  have hwd₂ : Shape.WF Δ d₂ := Shape.WFO.wf hwf₂.2.2.1
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
  have hdomj₁ : ∀ e ∈ g₁, TShape.NamedO Δ none
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) (Shape.T e.inp) :=
    fun e he =>
    TShape.NamedO.mono_r hΔ (hdom₁ e he) hled₁ hdjty
  have hdomj₂ : ∀ e ∈ g₂, TShape.NamedO Δ none
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) (Shape.T e.inp) :=
    fun e he =>
    TShape.NamedO.mono_r hΔ (hdom₂ e he) hled₂ hdjty
  -- **the cross pairs**
  have hcross : ShapeFun.Compat Shape.Compat Δ (A.subst σ)
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁)
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂) := by
    intro e he e' he' Θ τ hΘ Wτ hlab hin
    obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
    obtain ⟨b, hb, rfl⟩ := ShapeFun.mem_lift.1 he'
    have hwa := hwf₁.2.2.2.1.1 a ha
    have hwb := hwf₂.2.2.2.1.1 b hb
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
    have heq : Θ ⊢ b.tm.subst τ ≡ a.tm.subst τ : (A.subst σ).subst τ := hlab.2.symm
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
    hwSJ, .forallE hdj' hdjty hwSJ ?_ ?_ hwSJ (TShape.LE.refl hwSJ) ⟨u, hAty⟩ ⟨v, hB⟩,
    (TShape.LE.def hΔ (Nat.succ_le_succ k₁) (Nat.le_refl _)).2 ?_,
    (TShape.LE.def hΔ (Nat.succ_le_succ k₂) (Nat.le_refl _)).2 ?_⟩
  · -- inputs typed at the joined domain, with their names
    intro e he
    match List.mem_append.1 he with
    | .inl he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact .of_dom (TShape.NamedO.lift_subject hΔ (hdomj₁ a ha) (by omega))
        ((Shape.ValCanon.lift hΔ k₁).2 (hcan₁ a ha))
    | .inr he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact .of_dom (TShape.NamedO.lift_subject hΔ (hdomj₂ a ha) (by omega))
        ((Shape.ValCanon.lift hΔ k₂).2 (hcan₂ a ha))
  · -- bodies
    intro e he
    match List.mem_append.1 he with
    | .inl he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact Interp.lift hΔ k₁ (Interp.mono_val hΔ (Valuation.LE.push.2
        ⟨Valuation.LE.refl hwρ,
          TShape.LE.le_lift hΔ (m := Shape.T a.inp) k₁ (hwf₁.2.2.2.1.1 a ha).2.2.1⟩)
        (hbody₁ a ha))
    | .inr he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact Interp.lift hΔ k₂ (Interp.mono_val hΔ (Valuation.LE.push.2
        ⟨Valuation.LE.refl hwρ,
          TShape.LE.le_lift hΔ (m := Shape.T a.inp) k₂ (hwf₂.2.2.2.1.1 a ha).2.2.1⟩)
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
  | forallE hA₁ hd₁ hwf₁ hNV hbody₁ hw₁ hle₁ hAt hBt =>
    have hdom₁ := fun e he => (hNV e he).dom
    have hcan₁ := fun e he => (hNV e he).val
    cases h₂ with
    | bot =>
      refine ⟨_, ?_, ?_, hle₁, TShape.bot_le' rfl⟩
      · exact hwf₁
      · exact .forallE hA₁ hd₁  hwf₁ (fun e he => .of_dom (hdom₁ e he) (hcan₁ e he)) hbody₁ hwf₁ (TShape.LE.refl hwf₁) hAt hBt
    | forallE hA₂ hd₂ hwf₂ hNV hbody₂ hw₂ hle₂ _ _ =>
      have hdom₂ := fun e he => (hNV e he).dom
      have hcan₂ := fun e he => (hNV e he).val
      obtain ⟨s, hws, hs, hs₁, hs₂⟩ := sound_forallE_ub hΓ hAty hB ihAdir ihBdir
        hΔ W hwρ hA₁ hd₁ hwf₁ (fun e he => .of_dom (hdom₁ e he) (hcan₁ e he)) hbody₁ hA₂ hd₂ hwf₂ (fun e he => .of_dom (hdom₂ e he) (hcan₂ e he)) hbody₂
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
    (hNV₁ : ∀ e ∈ g₁, TShape.Named Δ (Shape.T d₁) e.tm (Shape.T e.inp))
    (hbody₁ : ∀ e ∈ g₁,
      Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push (Shape.T e.inp)) (Shape.T e.out))
    (hA₂ : Interp Δ Γ A σ ρ (Shape.T d₂))
    (hd₂ : TShape.HasType Δ (Shape.T d₂) TShape.type)
    (hwf₂ : Shape.WF (n := n₂+1) Δ (.sigma (A.subst σ) (B.subst σ.lift) d₂ g₂))
    (hNV₂ : ∀ e ∈ g₂, TShape.Named Δ (Shape.T d₂) e.tm (Shape.T e.inp))
    (hbody₂ : ∀ e ∈ g₂,
      Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push (Shape.T e.inp)) (Shape.T e.out)) :
    ∃ s, TShape.WF Δ s ∧ Interp Δ Γ (.sigma A B) σ ρ s ∧
      TShape.LE Δ (Shape.T (n := n₁+1) (.sigma (A.subst σ) (B.subst σ.lift) d₁ g₁)) s ∧
      TShape.LE Δ (Shape.T (n := n₂+1) (.sigma (A.subst σ) (B.subst σ.lift) d₂ g₂)) s := by
  have hdom₁ := fun e he => (hNV₁ e he).dom
  have hcan₁ := fun e he => (hNV₁ e he).val
  have hdom₂ := fun e he => (hNV₂ e he).dom
  have hcan₂ := fun e he => (hNV₂ e he).val
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hAty⟩
  have k₁ : n₁ ≤ max n₁ n₂ := Nat.le_max_left ..
  have k₂ : n₂ ≤ max n₁ n₂ := Nat.le_max_right ..
  -- the joined domain, from `A`'s own directedness
  have ⟨hcd, hdj⟩ := (ihAdir hΔ W hwρ).join hΔ hA₁ hA₂
  have hcd' : Shape.Compat Δ (d₁.lift (max n₁ n₂)) (d₂.lift (max n₁ n₂)) :=
    (TShape.Compat.def k₁ k₂).1 hcd
  have hwd₁ : Shape.WF Δ d₁ := Shape.WFO.wf hwf₁.2.2.1
  have hwd₂ : Shape.WF Δ d₂ := Shape.WFO.wf hwf₂.2.2.1
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
  have hdomj₁ : ∀ e ∈ g₁, TShape.NamedO Δ none
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) (Shape.T e.inp) :=
    fun e he =>
    TShape.NamedO.mono_r hΔ (hdom₁ e he) hled₁ hdjty
  have hdomj₂ : ∀ e ∈ g₂, TShape.NamedO Δ none
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) (Shape.T e.inp) :=
    fun e he =>
    TShape.NamedO.mono_r hΔ (hdom₂ e he) hled₂ hdjty
  -- **the cross pairs**
  have hcross : ShapeFun.Compat Shape.Compat Δ (A.subst σ)
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁)
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂) := by
    intro e he e' he' Θ τ hΘ Wτ hlab hin
    obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
    obtain ⟨b, hb, rfl⟩ := ShapeFun.mem_lift.1 he'
    have hwa := hwf₁.2.2.2.1.1 a ha
    have hwb := hwf₂.2.2.2.1.1 b hb
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
    have heq : Θ ⊢ b.tm.subst τ ≡ a.tm.subst τ : (A.subst σ).subst τ := hlab.2.symm
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
    hwSJ, .sigma hdj' hdjty hwSJ ?_ ?_ hwSJ (TShape.LE.refl hwSJ) ⟨u, hAty⟩ ⟨v, hB⟩,
    (TShape.LE.def hΔ (Nat.succ_le_succ k₁) (Nat.le_refl _)).2 ?_,
    (TShape.LE.def hΔ (Nat.succ_le_succ k₂) (Nat.le_refl _)).2 ?_⟩
  · -- inputs typed at the joined domain, with their names
    intro e he
    match List.mem_append.1 he with
    | .inl he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact .of_dom (TShape.NamedO.lift_subject hΔ (hdomj₁ a ha) (by omega))
        ((Shape.ValCanon.lift hΔ k₁).2 (hcan₁ a ha))
    | .inr he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact .of_dom (TShape.NamedO.lift_subject hΔ (hdomj₂ a ha) (by omega))
        ((Shape.ValCanon.lift hΔ k₂).2 (hcan₂ a ha))
  · -- bodies
    intro e he
    match List.mem_append.1 he with
    | .inl he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact Interp.lift hΔ k₁ (Interp.mono_val hΔ (Valuation.LE.push.2
        ⟨Valuation.LE.refl hwρ,
          TShape.LE.le_lift hΔ (m := Shape.T a.inp) k₁ (hwf₁.2.2.2.1.1 a ha).2.2.1⟩)
        (hbody₁ a ha))
    | .inr he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact Interp.lift hΔ k₂ (Interp.mono_val hΔ (Valuation.LE.push.2
        ⟨Valuation.LE.refl hwρ,
          TShape.LE.le_lift hΔ (m := Shape.T a.inp) k₂ (hwf₂.2.2.2.1.1 a ha).2.2.1⟩)
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
  | sigma hA₁ hd₁ hwf₁ hNV hbody₁ hw₁ hle₁ hAt hBt =>
    have hdom₁ := fun e he => (hNV e he).dom
    have hcan₁ := fun e he => (hNV e he).val
    cases h₂ with
    | bot =>
      refine ⟨_, ?_, ?_, hle₁, TShape.bot_le' rfl⟩
      · exact hwf₁
      · exact .sigma hA₁ hd₁  hwf₁ (fun e he => .of_dom (hdom₁ e he) (hcan₁ e he)) hbody₁ hwf₁ (TShape.LE.refl hwf₁) hAt hBt
    | sigma hA₂ hd₂ hwf₂ hNV hbody₂ hw₂ hle₂ _ _ =>
      have hdom₂ := fun e he => (hNV e he).dom
      have hcan₂ := fun e he => (hNV e he).val
      obtain ⟨s, hws, hs, hs₁, hs₂⟩ := sound_sigma_ub hΓ hAty hB ihAdir ihBdir
        hΔ W hwρ hA₁ hd₁ hwf₁ (fun e he => .of_dom (hdom₁ e he) (hcan₁ e he)) hbody₁ hA₂ hd₂ hwf₂ (fun e he => .of_dom (hdom₂ e he) (hcan₂ e he)) hbody₂
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
    (hNV₁ : ∀ e ∈ g₁, TShape.Named Δ d₁ e.tm e.inp.T)
    (hbody₁ : ∀ e ∈ g₁, Interp Δ (A :: Γ) b (σ.cons e.tm) (ρ.push e.inp.T) e.out.T)
    (hA₂ : Interp Δ Γ A σ ρ d₂)
    (hd₂ : TShape.HasType Δ d₂ TShape.type)
    (hwf₂ : Shape.WF (n := n₂+1) Δ (.lam (A.subst σ) g₂))
    (hNV₂ : ∀ e ∈ g₂, TShape.Named Δ d₂ e.tm e.inp.T)
    (hbody₂ : ∀ e ∈ g₂, Interp Δ (A :: Γ) b (σ.cons e.tm) (ρ.push e.inp.T) e.out.T) :
    ∃ s, TShape.WF Δ s ∧ Interp Δ Γ (.lam A b) σ ρ s ∧
      TShape.LE Δ (Shape.T (n := n₁+1) (.lam (A.subst σ) g₁)) s ∧
      TShape.LE Δ (Shape.T (n := n₂+1) (.lam (A.subst σ) g₂)) s := by
  have hdom₁ := fun e he => (hNV₁ e he).dom
  have hcan₁ := fun e he => (hNV₁ e he).val
  have hdom₂ := fun e he => (hNV₂ e he).dom
  have hcan₂ := fun e he => (hNV₂ e he).val
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hAty⟩
  have k₁ : n₁ ≤ max n₁ n₂ := Nat.le_max_left ..
  have k₂ : n₂ ≤ max n₁ n₂ := Nat.le_max_right ..
  -- the joined domain shape, from `A`'s own directedness
  have ⟨hcd, hdj⟩ := (ihAdir hΔ W hwρ).join hΔ hA₁ hA₂
  have hdjty : TShape.HasType Δ (d₁.join d₂) TShape.type :=
    TShape.HasType.join_sort' hΔ rfl hd₁ hd₂ hcd
  have ⟨hled₁, hled₂⟩ := TShape.le_join hΔ hA₁.wf hA₂.wf hcd
  have hdomj₁ : ∀ e ∈ g₁, TShape.NamedO Δ none (d₁.join d₂) e.inp.T := fun e he =>
    TShape.NamedO.mono_r hΔ (hdom₁ e he) hled₁ hdjty
  have hdomj₂ : ∀ e ∈ g₂, TShape.NamedO Δ none (d₁.join d₂) e.inp.T := fun e he =>
    TShape.NamedO.mono_r hΔ (hdom₂ e he) hled₂ hdjty
  -- **the cross pairs**: the body at the join of two entries' inputs, a
  -- valuation that is well formed but not admissible
  have hcross : ShapeFun.Compat Shape.Compat Δ (A.subst σ)
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
    -- the label equation, which puts the two bodies at one stage.  It is
    -- read at the domain label, the graph's type: this is what the
    -- λ-shape's label buys, and it holds at this non-admissible stage
    have heq : Θ ⊢ c.tm.subst τ ≡ a.tm.subst τ : (A.subst σ).subst τ := hlab.2.symm
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
    hwSJ, .lam hdj hdjty hwSJ ?_ ?_ hwSJ (TShape.LE.refl hwSJ) ⟨u, hAty⟩,
    (TShape.LE.def hΔ (Nat.succ_le_succ k₁) (Nat.le_refl _)).2 ?_,
    (TShape.LE.def hΔ (Nat.succ_le_succ k₂) (Nat.le_refl _)).2 ?_⟩
  · -- inputs typed at the joined domain, with their names
    intro e he
    match List.mem_append.1 he with
    | .inl he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact .of_dom (TShape.NamedO.lift_subject hΔ (hdomj₁ a ha) (by omega))
        ((Shape.ValCanon.lift hΔ k₁).2 (hcan₁ a ha))
    | .inr he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact .of_dom (TShape.NamedO.lift_subject hΔ (hdomj₂ a ha) (by omega))
        ((Shape.ValCanon.lift hΔ k₂).2 (hcan₂ a ha))
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
  | lam hA₁ hd₁ hwf₁ hNV hbody₁ hw₁ hle₁ hAt =>
    have hdom₁ := fun e he => (hNV e he).dom
    have hcan₁ := fun e he => (hNV e he).val
    cases h₂ with
    | bot =>
      refine ⟨_, ?_, ?_, hle₁, TShape.bot_le' rfl⟩
      · exact hwf₁
      · exact .lam hA₁ hd₁ hwf₁ (fun e he => .of_dom (hdom₁ e he) (hcan₁ e he)) hbody₁ hwf₁ (TShape.LE.refl hwf₁) hAt
    | lam hA₂ hd₂ hwf₂ hNV hbody₂ hw₂ hle₂ _ =>
      have hdom₂ := fun e he => (hNV e he).dom
      have hcan₂ := fun e he => (hNV e he).val
      obtain ⟨s, hws, hs, hs₁, hs₂⟩ := sound_lam_ub hΓ hAty hb ihAdir ihbdir
        hΔ W hwρ hA₁ hd₁ hwf₁ (fun e he => .of_dom (hdom₁ e he) (hcan₁ e he)) hbody₁ hA₂ hd₂ hwf₂ (fun e he => .of_dom (hdom₂ e he) (hcan₂ e he)) hbody₂
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
theorem graph_coherent {Γ Δ : List Term} {A C t : Term} {σ ρ} {u : Bool}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ t : C) (W : Ctx.SubstEq Δ σ σ Γ) (hwρ : Valuation.WF Δ ρ)
    (ihBdir : SoundDir (A :: Γ) t) {k} {f : ShapeFun k}
    (hent : ∀ e ∈ f, Shape.WF Δ e.inp)
    (hbody : ∀ e ∈ f, Interp Δ (A :: Γ) t (σ.cons e.tm) (ρ.push e.inp.T) e.out.T) :
    ShapeFun.Compat Shape.Compat Δ (A.subst σ) f f := by
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
  have heq : Θ ⊢ e'.tm.subst τ ≡ e.tm.subst τ : (A.subst σ).subst τ := hlabq.2.symm
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

/-- Each entry of a λ-approximant is an admissible stage: its label is
typed at the domain, and the slot it opens is hereditarily typed there
because `Interp.lam` demands that. -/
theorem lam_stage {Γ Γ₀ Δ : List Term} {A : Term} {u : Bool} {σ ρ}
    (hAty : Γ ⊢ A : .sort u) (ihAd : SoundDom Γ A (.sort u))
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {n} {g : ShapeFun n} {d : TShape} (hA : Interp Δ Γ A σ ρ d)
    (hwf : Shape.WF (n := n+1) Δ (.lam (A.subst σ) g))
    (hNV : ∀ e ∈ g, TShape.Named Δ d e.tm e.inp.T) :
    ∀ e ∈ g, Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A :: Γ) ∧
      Adm Δ Γ₀ (A :: Γ) (σ.cons e.tm) (ρ.push e.inp.T) := by
  intro e he
  have hwe := hwf.2.2.1.1 e he
  exact ⟨.cons W hAty hwe.2.1,
    .cons hAdm W.wf hA (TShape.WF.T.2 hwe.2.2.1)
      (hNV e he) (ihAd.codeAt hΔ W hAdm hA)⟩

/-- **The Π-approximant read off a λ-approximant.**  Given a code for
every entry's body, this is the Π-shape whose domain is the λ's own
domain slot and whose codomain graph has one entry per code: it
interprets `Π A B`, it types the λ-shape, and its graph looks up each
entry's code.  `sound_lam_dom` instantiates the codes with the body's
own saturation. -/
theorem lam_pi_code {Γ Γ₀ Δ : List Term} {A B : Term} {u v : Bool} {σ ρ}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) (ihAd : SoundDom Γ A (.sort u))
    (ihBty : SoundTy (A :: Γ) B (.sort v)) (ihBc : CodeAt (A :: Γ) B)
    (ihBdir : SoundDir (A :: Γ) B)
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {n} {g : ShapeFun n} {d : TShape}
    (hA : Interp Δ Γ A σ ρ d) (hd : TShape.HasType Δ d TShape.type)
    (hwf : Shape.WF (n := n+1) Δ (.lam (A.subst σ) g))
    (hNV : ∀ e ∈ g, TShape.Named Δ d e.tm e.inp.T)
    {Q : Entry (Shape n) → TShape → Prop}
    (hQmono : ∀ {e : Entry (Shape n)} {c c' : TShape}, TShape.LE Δ c c' →
      TShape.HasType Δ c' TShape.type → Q e c → Q e c')
    (hcodes : ∀ e ∈ g, ∃ c, Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push e.inp.T) c ∧
      TShape.HasType Δ e.out.T c ∧ Q e c) :
    ∃ (k : Nat) (dk : Shape k) (f : ShapeFun k),
      Interp Δ Γ (.forallE A B) σ ρ
        (Shape.T (n := k+1) (.forallE (A.subst σ) (B.subst σ.lift) dk f)) ∧
      TShape.HasType Δ (Shape.T (n := n+1) (.lam (A.subst σ) g))
        (Shape.T (n := k+1) (.forallE (A.subst σ) (B.subst σ.lift) dk f)) ∧
      TShape.HasType Δ (Shape.T dk) TShape.type ∧
      (∀ e ∈ g, TShape.NamedO Δ none (Shape.T dk) e.inp.T) ∧
      (∀ e ∈ g, ∃ c, TEvaluates Δ f (A.subst σ) e.tm e.inp.T c ∧
        TShape.HasType Δ c TShape.type ∧ Q e c) ∧
      TShape.CodeCanonS Δ ((Term.forallE A B).subst σ)
        (Shape.T (n := k+1) (.forallE (A.subst σ) (B.subst σ.lift) dk f)) := by
  have hdom := fun e he => (hNV e he).dom
  have hcan := fun e he => (hNV e he).val
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hAty⟩
  have hwρ := hAdm.wf
  have hstage := lam_stage hAty ihAd hΔ W hAdm hA hwf (fun e he => .of_dom (hdom e he) (hcan e he))
  -- the codes, collected and brought to one level
  obtain ⟨g₀, hmap, hall⟩ := List.exists_pairs (β := TShape) hcodes
  obtain ⟨k, hkn, hkd, hkc⟩ : ∃ k, n ≤ k ∧ d.1 ≤ k ∧ ∀ p ∈ g₀, (Prod.snd p : TShape).1 ≤ k :=
    ⟨levelMax (fun p => (Prod.snd p : TShape).1) (max n d.1) g₀,
      Nat.le_trans (Nat.le_max_left ..) le_levelMax,
      Nat.le_trans (Nat.le_max_right ..) le_levelMax,
      fun p hp => mem_le_levelMax (f := fun p => (Prod.snd p : TShape).1) hp⟩
  -- the codomain graph, one entry per entry of the λ's
  obtain ⟨f, hf⟩ : ∃ f : ShapeFun k, ∀ e, e ∈ f ↔ ∃ p ∈ g₀,
      e = ⟨p.1.tm, p.1.inp.lift k, (Prod.snd p : TShape).2.lift k⟩ :=
    ⟨g₀.map fun p => ⟨p.1.tm, p.1.inp.lift k, (Prod.snd p : TShape).2.lift k⟩,
      fun e => by simp [List.mem_map, eq_comm]⟩
  have hg₀g : ∀ p ∈ g₀, p.1 ∈ g := fun p hp => hmap ▸ List.mem_map.2 ⟨p, hp, rfl⟩
  have hpwf : ∀ p ∈ g₀, TShape.WF Δ (Prod.snd p : TShape) := fun p hp => (hall p hp).1.wf
  have hdty : TShape.HasType Δ (Shape.T (d.2.lift k)) TShape.type :=
    hd.lift_subject hΔ hkd
  have hdle : TShape.LE Δ d (Shape.T (d.2.lift k)) :=
    TShape.LE.le_lift hΔ (m := d) hkd hd.wf.1
  -- the Π-shape's premises, entry by entry
  have hfent : ∀ e ∈ f, (∃ u, Δ ⊢ A.subst σ : .sort u) ∧ Δ ⊢ e.tm : A.subst σ ∧
      Shape.WF Δ e.inp ∧ Shape.WF Δ e.out := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := (hf e).1 he
    have hwe := hwf.2.2.1.1 p.1 (hg₀g p hp)
    exact ⟨hwe.1, hwe.2.1, (Shape.lift_wf hkn).2 hwe.2.2.1,
      (Shape.lift_wf (hkc p hp)).2 (hpwf p hp)⟩
  have hfdom : ∀ e ∈ f, TShape.NamedO Δ none (Shape.T (d.2.lift k)) e.inp.T := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := (hf e).1 he
    exact TShape.NamedO.mono_r hΔ
      (TShape.NamedO.lift_subject hΔ (hdom p.1 (hg₀g p hp)) hkn) hdle hdty
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
  have hcdPi : Shape.CodeCanonS Δ (A.subst σ) (d.2.lift k) :=
    (Shape.CodeCanonS.lift_iff hkd).2 (ihAd.codeAt hΔ W hAdm hA)
  have hcfPi : ∀ e ∈ f, Shape.CodeCanonS Δ ((B.subst σ.lift).inst e.tm) e.out := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := (hf e).1 he
    have hc := ihBc hΔ (hstage p.1 (hg₀g p hp)).1 (hstage p.1 (hg₀g p hp)).2 (hall p hp).1
    rw [← inst_lift_cons] at hc
    exact (Shape.CodeCanonS.lift_iff (hkc p hp)).2 hc
  have hwfPi : Shape.WF (n := k+1) Δ
      (.forallE (A.subst σ) (B.subst σ.lift) (d.2.lift k) f) :=
    ⟨⟨u, hAσ⟩, ⟨v, hB.subst hΔA (W.lift hAty hAσ)⟩,
      Shape.WF.name ((Shape.lift_wf hkd).2 hd.wf.1) hcdPi,
      ShapeFun.WF.name
        ⟨fun e he => hfent e he,
          graph_coherent hΓ hAty hB W hwρ ihBdir (fun e he => (hfent e he).2.2.1)
            hfbody⟩ hcfPi, trivial⟩
  have hPi : Interp Δ Γ (.forallE A B) σ ρ
      (Shape.T (n := k+1) (.forallE (A.subst σ) (B.subst σ.lift) (d.2.lift k) f)) :=
    .forallE (Interp.mono hΔ ((Shape.lift_wf hkd).2 hd.wf.1)
        (TShape.LE.lift_le hΔ (m := d) hkd hd.wf.1) hA)
      hdty hwfPi
      (fun e he => by
        obtain ⟨p, hp, rfl⟩ := (hf e).1 he
        exact .of_dom (hfdom _ he) ((Shape.ValCanon.lift hΔ hkn).2 (hcan p.1 (hg₀g p hp))))
      hfbody hwfPi (TShape.LE.refl hwfPi) ⟨u, hAty⟩ ⟨v, hB⟩
  -- the typing codes are the Π-entries, so the λ-shape is typed by it
  have hcty : ∀ p ∈ g₀, TShape.HasType Δ (Shape.T ((Prod.snd p : TShape).2.lift k))
      TShape.type := by
    intro p hp
    exact (ihBty.isType hΔ (hstage p.1 (hg₀g p hp)).1 (hstage p.1 (hg₀g p hp)).2
      (hall p hp).1).lift_subject hΔ (hkc p hp)
  -- each code is looked up in the Π's graph at its own entry
  have hlook : ∀ p ∈ g₀, TEvaluates Δ f (A.subst σ) p.1.tm p.1.inp.T
      (Shape.T ((Prod.snd p : TShape).2.lift k)) := by
    intro p hp
    refine TEvaluates.entry _ ((hf _).2 ⟨p, hp, rfl⟩)
      ⟨hwf.2.2.2, (hwf.2.2.1.1 p.1 (hg₀g p hp)).2.1⟩ ?_
    exact TShape.LE.lift_le hΔ (m := p.1.inp.T) hkn (hwf.2.2.1.1 p.1 (hg₀g p hp)).2.2.1
  refine ⟨k, d.2.lift k, f, hPi, TShape.HasType.lam (g₀ := g₀)
    hdty (fun e he => ?_) hwf hwfPi (fun e he => ?_) (fun e he => ?_)
    (fun p hp => ?_) (fun p hp => (hall p hp).2.1) (TyEq.refl hAσ),
    hdty, fun e he => ?_, fun e he => ?_, ?_⟩
  · -- the Π-entries are types
    obtain ⟨p, hp, rfl⟩ := (hf e).1 he
    exact hcty p hp
  · -- the generator's entries are well formed
    rw [hmap] at he
    exact ⟨(hwf.2.2.1.1 e he).2.2.1, (hwf.2.2.1.1 e he).2.2.2⟩
  · -- every entry of `g` is covered by the generator, namely by itself
    rw [hmap]
    exact TEvaluates.refl hwf.2.2.1 e he
  · -- and each generator code is the Π-entry built from it
    exact TEvaluates.lower
      (TShape.LE.le_lift hΔ (m := (Prod.snd p : TShape)) (hkc p hp) (hpwf p hp))
      (hlook p hp)
  · -- the inputs are hereditarily typed at the lifted domain
    exact TShape.NamedO.mono_r hΔ (hdom e he) hdle hdty
  · -- and the code of each entry is looked up at it
    obtain ⟨p, hp, rfl⟩ : ∃ p ∈ g₀, p.1 = e := by
      rw [← hmap, List.mem_map] at he
      obtain ⟨p, hp, heq⟩ := he
      exact ⟨p, hp, heq⟩
    exact ⟨_, hlook p hp, hcty p hp,
      hQmono (TShape.LE.le_lift hΔ (m := (Prod.snd p : TShape)) (hkc p hp) (hpwf p hp))
        (hcty p hp) (hall p hp).2.2⟩
  · -- the Π-code names `Π A B`: its labels are the type's, its domain is
    -- an approximant of `A`, and its codomain entries approximate `B`
    exact ⟨v, (IsDefEq.forallEDF hAty hB hB).subst hΔ W⟩

/-- **Saturation at a λ.**  The body's own saturation enlarges every
entry's output to a hereditarily typed one -- the enlarged graph is
still a λ-approximant, by the same coherence argument (`graph_coherent`)
that `Interp.lam` wanted in the first place -- and then the codomain
codes of `lam_pi_code` are exactly codes `Dom` asks for. -/
theorem sound_lam_dom {Γ : List Term} {A B b : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v)
    (hb : A :: Γ ⊢ b : B) (ihAd : SoundDom Γ A (.sort u))
    (ihBty : SoundTy (A :: Γ) B (.sort v)) (ihBc : CodeAt (A :: Γ) B)
    (ihbdom : SoundDom (A :: Γ) b B) (ihbdir : SoundDir (A :: Γ) b)
    (ihBdir : SoundDir (A :: Γ) B) :
    SoundDom Γ (.lam A b) (.forallE A B) := by
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hAty⟩
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  have hwρ := hAdm.wf
  cases hm with
  | bot => exact ⟨TShape.bot, TShape.bot, .bot, TShape.bot_le' rfl, .bot, (.of_dom (TShape.NamedO.bot (.bot (.bot .sort))) (TShape.ValCanon.of_bot rfl)), TShape.CodeCanonS.bot⟩
  | @lam _ _ _ _ n g d _ _ hA hd hwf hNV hbody hw hle hAt =>
    have hdom := fun e he => (hNV e he).dom
    have hcan := fun e he => (hNV e he).val
    have hstage := lam_stage hAty ihAd hΔ W hAdm hA hwf (fun e he => .of_dom (hdom e he) (hcan e he))
    -- saturate every body, and bring the enlarged outputs to one level
    obtain ⟨gs, hmap, hall⟩ := List.exists_pairs (β := TShape × TShape)
      (P := fun (e : Entry (Shape n)) (p : TShape × TShape) =>
        Interp Δ (A :: Γ) b (σ.cons e.tm) (ρ.push e.inp.T) p.1 ∧
        TShape.LE Δ e.out.T p.1 ∧
        Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push e.inp.T) p.2 ∧ TShape.NamedO Δ none p.2 p.1 ∧
        TShape.CodeCanonS Δ (B.subst (σ.cons e.tm)) p.2 ∧
        TShape.ValCanon Δ (b.subst (σ.cons e.tm)) p.1)
      (fun e he => by
        obtain ⟨m', c, hm', hle', hc, hNV, hcc⟩ :=
          ihbdom hΔ (hstage e he).1 (hstage e he).2 (hbody e he)
        exact ⟨(m', c), hm', hle', hc, hNV.dom, hcc, hNV.val⟩)
    -- the enlarged graph, at one level
    obtain ⟨k, hkn, hkc⟩ : ∃ k, n ≤ k ∧ ∀ p ∈ gs, ((Prod.snd p).1 : TShape).1 ≤ k :=
      ⟨levelMax (fun p => ((Prod.snd p).1 : TShape).1) n gs, le_levelMax,
        fun p hp => mem_le_levelMax (f := fun p => ((Prod.snd p).1 : TShape).1) hp⟩
    obtain ⟨g', hg'⟩ : ∃ g' : ShapeFun k, ∀ e, e ∈ g' ↔ ∃ p ∈ gs,
        e = ⟨p.1.tm, p.1.inp.lift k, ((Prod.snd p).1 : TShape).2.lift k⟩ :=
      ⟨gs.map fun p => ⟨p.1.tm, p.1.inp.lift k, ((Prod.snd p).1 : TShape).2.lift k⟩,
        fun e => by simp [List.mem_map, eq_comm]⟩
    have hgsg : ∀ p ∈ gs, p.1 ∈ g := fun p hp => hmap ▸ List.mem_map.2 ⟨p, hp, rfl⟩
    have hswf : ∀ p ∈ gs, TShape.WF Δ ((Prod.snd p).1 : TShape) :=
      fun p hp => (hall p hp).1.wf
    -- its entries are well formed, and still carry information
    have hent' : ∀ e ∈ g', (∃ u, Δ ⊢ A.subst σ : .sort u) ∧ Δ ⊢ e.tm : A.subst σ ∧
        Shape.WF Δ e.inp ∧ Shape.WF Δ e.out := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := (hg' e).1 he
      have hwe := hwf.2.2.1.1 p.1 (hgsg p hp)
      exact ⟨hwe.1, hwe.2.1, (Shape.lift_wf hkn).2 hwe.2.2.1,
        (Shape.lift_wf (hkc p hp)).2 (hswf p hp)⟩
    have hbody' : ∀ e ∈ g',
        Interp Δ (A :: Γ) b (σ.cons e.tm) (ρ.push e.inp.T) e.out.T := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := (hg' e).1 he
      have hwe := hwf.2.2.1.1 p.1 (hgsg p hp)
      refine Interp.mono hΔ ((Shape.lift_wf (hkc p hp)).2 (hswf p hp))
        (TShape.LE.lift_le hΔ (m := ((Prod.snd p).1 : TShape)) (hkc p hp) (hswf p hp)) ?_
      exact Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
        TShape.LE.le_lift hΔ (m := p.1.inp.T) hkn hwe.2.2.1⟩) (hall p hp).1
    have hnotbot : ∀ e ∈ g', ¬ e.out.IsBot := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := (hg' e).1 he
      intro hbot
      refine hwf.2.1 p.1 (hgsg p hp) ?_
      have : ((Prod.snd p).1 : TShape).2 = Shape.bot :=
        (hswf p hp).eq_bot_of_isBot ((Shape.lift_isBot (hkc p hp)).1 hbot)
      have hbb : p.1.out = Shape.bot := TShape.le_bot hΔ this (hall p hp).2.1
      exact hbb ▸ Shape.isBot_bot
    have hwf' : Shape.WF (n := k+1) Δ (.lam (A.subst σ) g') := by
      refine ⟨?_, hnotbot, ⟨hent', graph_coherent hΓ hAty hb W hwρ ihbdir
        (fun e he => (hent' e he).2.2.1) hbody'⟩, hwf.2.2.2⟩
      intro hnil
      refine hwf.1 ?_
      rw [← hmap]
      have : gs = [] := by
        cases hgs : gs with
        | nil => rfl
        | cons q qs =>
          exact absurd ((hg' _).2 ⟨q, by simp [hgs], rfl⟩) (by simp [hnil])
      simp [this]
    -- the enlarged λ-shape is still an approximant of the λ
    have hlamI : Interp Δ Γ (.lam A b) σ ρ (Shape.T (n := k+1) (.lam (A.subst σ) g')) := by
      refine .lam hA hd hwf' (fun e he => ?_) hbody' (TShape.WF.T.2 hwf')
        (TShape.LE.refl (TShape.WF.T.2 hwf')) hAt
      · obtain ⟨p, hp, rfl⟩ := (hg' e).1 he
        exact .of_dom (TShape.NamedO.lift_subject hΔ (hdom p.1 (hgsg p hp)) hkn)
          ((Shape.ValCanon.lift hΔ hkn).2 (hcan p.1 (hgsg p hp)))
    -- and it dominates the given one: same entries, bigger outputs
    have hlamle : TShape.LE Δ (Shape.T (n := n+1) (.lam (A.subst σ) g))
        (Shape.T (n := k+1) (.lam (A.subst σ) g')) := by
      refine (TShape.LE.def hΔ (k := k+1) (Nat.succ_le_succ hkn) (Nat.le_refl _)).2 ?_
      show Shape.LE Δ (.lam (A.subst σ) (ShapeFun.lift (Shape.lift k) g))
        (.lam (A.subst σ) (ShapeFun.lift (Shape.lift k) g'))
      rw [show ShapeFun.lift (Shape.lift k) g' = g' from by
        simp [ShapeFun.lift, Shape.lift_self]]
      have hwfl : Shape.WF (n := k+1) Δ
          (.lam (A.subst σ) (ShapeFun.lift (Shape.lift k) g)) :=
        (Shape.lift_wf (Nat.succ_le_succ hkn)).2 hwf
      refine ⟨⟨fun e he => ?_, hwfl.2.2.1, hwf'.2.2.1⟩, hwfl.1, hwfl.2.1,
        ⟨u, hAty.subst hΔ W⟩, hwfl.2.2.2⟩
      -- every lifted entry is covered by its enlarged copy
      obtain ⟨q, hq, rfl⟩ := ShapeFun.mem_lift.1 he
      obtain ⟨p, hp, rfl⟩ : ∃ p ∈ gs, p.1 = q := by
        rw [← hmap, List.mem_map] at hq
        obtain ⟨p, hp, heq⟩ := hq
        exact ⟨p, hp, heq⟩
      refine ShapeFun.Eval.lower
        (TShape.LE.def_mp (a := p.1.out.T) (b := ((Prod.snd p).1 : TShape))
          hkn (hkc p hp) (hall p hp).2.1) ?_
      exact ShapeFun.Eval.entry _ ((hg' _).2 ⟨p, hp, rfl⟩)
        ⟨hwf.2.2.2, (hwf.2.2.1.1 p.1 (hgsg p hp)).2.1⟩
        (Shape.LE.refl ((Shape.lift_wf hkn).2 (hwf.2.2.1.1 p.1 (hgsg p hp)).2.2.1))
    -- the Π-approximant, with the saturation's codes
    obtain ⟨kP, dP, f, hPi, hty, hdtyP, hinP, hcodes, hcanPi⟩ :=
      lam_pi_code (Q := fun e c => TShape.NamedO Δ none c e.out.T)
        hΓ hAty hB ihAd ihBty ihBc ihBdir hΔ W hAdm hA hd hwf'
        (fun e he => by
          obtain ⟨p, hp, rfl⟩ := (hg' e).1 he
          exact .of_dom (TShape.NamedO.lift_subject hΔ (hdom p.1 (hgsg p hp)) hkn)
            ((Shape.ValCanon.lift hΔ hkn).2 (hcan p.1 (hgsg p hp))))
        (fun hle' hty' hQ => TShape.NamedO.mono_r hΔ hQ hle' hty')
        (fun e he => by
          obtain ⟨p, hp, rfl⟩ := (hg' e).1 he
          refine ⟨(Prod.snd p).2, ?_, ?_, ?_⟩
          · exact Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
              TShape.LE.le_lift hΔ (m := p.1.inp.T) hkn
                (hwf.2.2.1.1 p.1 (hgsg p hp)).2.2.1⟩) (hall p hp).2.2.1
          · exact TShape.HasType.mono_l hΔ (hall p hp).2.2.2.1.hasType
              (TShape.LE.lift_le hΔ (m := ((Prod.snd p).1 : TShape)) (hkc p hp)
                (hswf p hp))
          · exact TShape.NamedO.lift_subject hΔ (hall p hp).2.2.2.1 (hkc p hp))
    -- and the codes, entry by entry, are what `Dom` asks for
    obtain ⟨cs₀, hcsmap, hcsall⟩ := List.exists_pairs (β := TShape)
      (P := fun (e : Entry (Shape k)) (c : TShape) =>
        TEvaluates Δ f (A.subst σ) e.tm e.inp.T c ∧ TShape.NamedO Δ none c e.out.T)
      (fun e he => by
        obtain ⟨c, hc, _, hdc⟩ := hcodes e he
        exact ⟨c, hc, hdc⟩)
    have hcsg : ∀ p ∈ cs₀, p.1 ∈ g' := fun p hp => hcsmap ▸ List.mem_map.2 ⟨p, hp, rfl⟩
    refine ⟨Shape.T (n := k+1) (.lam (A.subst σ) g'), _, hlamI,
      TShape.LE.trans hΔ hle hlamle, hPi,
      .of_dom (.pi (cs := cs₀.map (fun p => ((⟨p.1.tm, p.1.inp.T, p.1.out.T⟩ : Entry TShape),
        p.2))) hty ?_ (fun p hp => ?_) (fun p hp => ?_) (fun p hp => ?_)) ?_, hcanPi⟩
    · show g'.map (fun e => (⟨e.tm, e.inp.T, e.out.T⟩ : Entry TShape)) = _
      rw [← hcsmap]
      simp [List.map_map, Function.comp_def]
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact hinP q.1 (hcsg q hq)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact (hcsall q hq).1
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact (hcsall q hq).2
    · -- each output names the application, by β at its own label
      have hAσ : Δ ⊢ A.subst σ : .sort u := hAty.subst hΔ W
      have hbσ : A.subst σ :: Δ ⊢ b.subst σ.lift : B.subst σ.lift :=
        hb.subst ⟨hΔ, _, hAσ⟩ (W.lift hAty hAσ)
      intro e he
      obtain ⟨p, hp, rfl⟩ := (hg' e).1 he
      have hq := hgsg p hp
      refine ⟨(Shape.ValCanon.lift hΔ hkn).2 (hcan p.1 hq), ?_⟩
      have htm : Δ ⊢ p.1.tm : A.subst σ :=
        (hwf.2.2.1.1 p.1 hq).2.1
      have hβ := IsDefEq.beta₀ hΔ hbσ htm
      rw [inst_lift_cons, inst_lift_cons] at hβ
      exact (Shape.ValCanon.lift hΔ (hkc p hp)).2
        (TShape.ValCanon.defeq hΔ (hall p hp).2.2.2.1 (hall p hp).2.2.2.2.1
          (hall p hp).2.2.2.2.2 hβ.symm)

/-- One direction of the `SoundEq` half of `lamDF`.

A λ-shape carries only its *domain* label, so the two sides differ in
that one term — and `Shape.LE` compares it up to definitional equality,
so one λ-shape is below the other with the same graph.  The bodies move
by their own `SoundEq` at each entry's stage (which is unchanged: the
stage term is the entry's label, not the binder's annotation) and then
`Interp.ctx` for the context whose head changed. -/
theorem sound_lam_eq_of {Γ : List Term} {A A' b b' : Term} {u : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u)
    (ihA : SoundEq Γ A A') (ihAd : SoundDom Γ A (.sort u))
    (ihb : SoundEq (A :: Γ) b b')
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {m : TShape} (H : Interp Δ Γ (.lam A b) σ ρ m) :
    Interp Δ Γ (.lam A' b') σ ρ m := by
  have hAσ : TyEq Δ (A.subst σ) (A'.subst σ) := ⟨u, hAA'.subst hΔ W⟩
  cases H with
  | @lam _ _ _ _ _ _ _ _ _ hA hd hwf hNV hbody hw hle hAt =>
    have hdom := fun e he => (hNV e he).dom
    have hcan := fun e he => (hNV e he).val
    have hwf' : Shape.WF Δ (Shape.lam (A'.subst σ) _) :=
      ⟨hwf.1, hwf.2.1, hwf.2.2.1.retype hAσ, hAσ.refl_r⟩
    refine .lam ((ihA hΔ W hAdm).1 hA) hd hwf' (fun e he => .of_dom (hdom e he) (hcan e he)) (fun e he => ?_) hw
      (hle.trans hΔ (TShape.LE.T.2
        ⟨ShapeFun.LE.refl hwf.2.2.1, hwf.1, hwf.2.1, hAσ, hwf.2.2.2⟩))
      ⟨u, hAA'.hasType.2⟩
    -- the body, at the stage extended by the entry's label
    have hwe := hwf.2.2.1.1 e he
    have W' : Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A :: Γ) :=
      .cons W hAA'.hasType.1 hwe.2.1
    have hAdm' : Adm Δ Γ₀ (A :: Γ) (σ.cons e.tm) (ρ.push (Shape.T e.inp)) :=
      .cons hAdm W.wf hA hwe.2.2.1 (hNV e he)
        (ihAd.codeAt hΔ W hAdm hA)
    exact Interp.ctx ((ihb hΔ W' hAdm').1 (hbody e he)) ⟨W.wf, _, hAA'.hasType.2⟩
      (Ctx.SubstEq.defeqHead W.wf hAA')
  | bot => exact .bot

/-- The `SoundEq` half of `lamDF`, both directions on the mirrored data —
which is why the rule carries its body premise twice, once over each
domain. -/
theorem sound_lam_eq {Γ : List Term} {A A' b b' : Term} {u : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u)
    (ihA : SoundEq Γ A A') (ihAd : SoundDom Γ A (.sort u))
    (ihb : SoundEq (A :: Γ) b b') (ihb' : SoundEq (A' :: Γ) b b') :
    SoundEq Γ (.lam A b) (.lam A' b') := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  exact ⟨sound_lam_eq_of hAA' ihA ihAd ihb hΔ W hAdm,
    sound_lam_eq_of hAA'.symm ihA.symm
      (SoundDom.of_eq hAA' ihA ihAd) ihb'.symm hΔ W hAdm⟩

/-! ## Pairs

A pair shape's components are the two arguments' own, so the common upper
bound is componentwise: the labels agree (both come from the same term at
the same stage), and each component joins by its argument's directedness.
The non-degeneracy conjunct of `WF` comes for free from `Shape.WF.join`,
which is why the bound is taken as the *join of the two lifted shapes*
rather than assembled from the two component bounds. -/

/-- The common upper bound of two pair shapes: the components joined by
their own directedness, the name shared (the clause reads it off the
term), and the codomain code joined by the body's.  With the graph gone
this is shorter than the λ case: there are no entries to merge and no
stage to move. -/
theorem dir_pair_ub {Γ : List Term} {A B a b : Term}
    (hAt : ∃ u, Γ ⊢ A : .sort u) (hat : Γ ⊢ a : A)
    (ihA : SoundDir Γ A) (ihB : SoundDir (A :: Γ) B)
    (iha : SoundDir Γ a) (ihb : SoundDir Γ b)
    {Δ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hwρ : Valuation.WF Δ ρ)
    {n₁ n₂} {x₁ y₁ : Shape n₁} {x₂ y₂ : Shape n₂} {d₁ d₂ c₁ c₂ : TShape}
    (ha₁ : Interp Δ Γ a σ ρ (Shape.T x₁)) (hb₁ : Interp Δ Γ b σ ρ (Shape.T y₁))
    (hA₁ : Interp Δ Γ A σ ρ d₁) (hd₁ : TShape.HasType Δ d₁ TShape.type)
    (hNV₁ : TShape.Named Δ d₁ (a.subst σ) (Shape.T x₁))
    (hdc₁ : TShape.CodeCanonS Δ (A.subst σ) d₁)
    (hwf₁ : Shape.WF (n := n₁+1) Δ (.pair (A.subst σ) (a.subst σ) x₁ y₁))
    (hcode₁ : Interp Δ (A :: Γ) B (σ.cons (a.subst σ)) (ρ.push (Shape.T x₁)) c₁)
    (hcty₁ : TShape.NamedO Δ none c₁ (Shape.T y₁))
    (ha₂ : Interp Δ Γ a σ ρ (Shape.T x₂)) (hb₂ : Interp Δ Γ b σ ρ (Shape.T y₂))
    (hA₂ : Interp Δ Γ A σ ρ d₂) (hd₂ : TShape.HasType Δ d₂ TShape.type)
    (hNV₂ : TShape.Named Δ d₂ (a.subst σ) (Shape.T x₂))
    (hdc₂ : TShape.CodeCanonS Δ (A.subst σ) d₂)
    (hwf₂ : Shape.WF (n := n₂+1) Δ (.pair (A.subst σ) (a.subst σ) x₂ y₂))
    (hcode₂ : Interp Δ (A :: Γ) B (σ.cons (a.subst σ)) (ρ.push (Shape.T x₂)) c₂)
    (hcty₂ : TShape.NamedO Δ none c₂ (Shape.T y₂)) :
    ∃ s, TShape.WF Δ s ∧ Interp Δ Γ (.pair A B a b) σ ρ s ∧
      TShape.LE Δ (Shape.T (n := n₁+1) (.pair (A.subst σ) (a.subst σ) x₁ y₁)) s ∧
      TShape.LE Δ (Shape.T (n := n₂+1) (.pair (A.subst σ) (a.subst σ) x₂ y₂)) s := by
  have hdx₁ := hNV₁.dom; have hxc₁ := hNV₁.val
  have hdx₂ := hNV₂.dom; have hxc₂ := hNV₂.val
  have k₁ : n₁ ≤ max n₁ n₂ := Nat.le_max_left ..
  have k₂ : n₂ ≤ max n₁ n₂ := Nat.le_max_right ..
  -- the components and the domain join, by their own directedness
  obtain ⟨hcx, hjx⟩ := (iha hΔ W hwρ).join hΔ ha₁ ha₂
  obtain ⟨hcy, hjy⟩ := (ihb hΔ W hwρ).join hΔ hb₁ hb₂
  obtain ⟨hcd, hjd⟩ := (ihA hΔ W hwρ).join hΔ hA₁ hA₂
  have hdjty : TShape.HasType Δ (d₁.join d₂) TShape.type :=
    TShape.HasType.join_sort' hΔ rfl hd₁ hd₂ hcd
  have ⟨hled₁, hled₂⟩ := TShape.le_join hΔ hA₁.wf hA₂.wf hcd
  obtain ⟨uA, hAσ⟩ := hwf₁.2.2.1
  -- the first components, lifted to the common level and joined
  have hcxl : TShape.Compat Δ (Shape.T (x₁.lift (max n₁ n₂)))
      (Shape.T (x₂.lift (max n₁ n₂))) :=
    TShape.Compat.T.2 ((TShape.Compat.def k₁ k₂).1 hcx)
  have hcyl : TShape.Compat Δ (Shape.T (y₁.lift (max n₁ n₂)))
      (Shape.T (y₂.lift (max n₁ n₂))) :=
    TShape.Compat.T.2 ((TShape.Compat.def k₁ k₂).1 hcy)
  have hwx₁ : TShape.WF Δ (Shape.T x₁) := TShape.WF.T.2 hwf₁.2.2.2.1
  have hwx₂ : TShape.WF Δ (Shape.T x₂) := TShape.WF.T.2 hwf₂.2.2.2.1
  -- the codes, read at the joined slot and joined there
  have hle₁ : Valuation.LE Δ (ρ.push (Shape.T x₁)) (ρ.push (Shape.T x₁ |>.join (Shape.T x₂))) :=
    Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, (TShape.le_join hΔ hwx₁ hwx₂ hcx).1⟩
  have hle₂ : Valuation.LE Δ (ρ.push (Shape.T x₂)) (ρ.push (Shape.T x₁ |>.join (Shape.T x₂))) :=
    Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, (TShape.le_join hΔ hwx₁ hwx₂ hcx).2⟩
  have hcode₁' := Interp.mono_val hΔ hle₁ hcode₁
  have hcode₂' := Interp.mono_val hΔ hle₂ hcode₂
  have Wcons : Ctx.SubstEq Δ (σ.cons (a.subst σ)) (σ.cons (a.subst σ)) (A :: Γ) :=
    .cons W hAt.choose_spec (IsDefEq.subst hΔ W hat)
  obtain ⟨hcc, hjc⟩ :=
    (ihB hΔ Wcons (Valuation.WF.push hwρ (TShape.WF.join hΔ hcx hwx₁ hwx₂))).join hΔ
      hcode₁' hcode₂'
  have hwS : Shape.WF (n := max n₁ n₂ + 1) Δ
      (.pair (A.subst σ) (a.subst σ) (x₁.lift (max n₁ n₂) |>.join (x₂.lift (max n₁ n₂)))
        (y₁.lift (max n₁ n₂) |>.join (y₂.lift (max n₁ n₂)))) := by
    refine ⟨?_, hwf₁.2.1, hwf₁.2.2.1, ?_, ?_⟩
    · intro hb
      exact hwf₁.1 ⟨(Shape.lift_isBot k₁).1 (Shape.IsBot.of_join_left hb.1),
        (Shape.lift_isBot k₁).1 (Shape.IsBot.of_join_left hb.2)⟩
    · exact Shape.WF.join hΔ ((TShape.Compat.def k₁ k₂).1 hcx)
        ((Shape.lift_wf k₁).2 hwf₁.2.2.2.1) ((Shape.lift_wf k₂).2 hwf₂.2.2.2.1)
    · exact Shape.WF.join hΔ ((TShape.Compat.def k₁ k₂).1 hcy)
        ((Shape.lift_wf k₁).2 hwf₁.2.2.2.2) ((Shape.lift_wf k₂).2 hwf₂.2.2.2.2)
  have hwS' : TShape.WF Δ (Shape.T (n := max n₁ n₂ + 1) _) := TShape.WF.T.2 hwS
  refine ⟨_, hwS', ?_, ?_, ?_⟩
  · have hjx' : Interp Δ Γ a σ ρ
        (Shape.T ((x₁.lift (max n₁ n₂)).join (x₂.lift (max n₁ n₂)))) := by
      simpa [TShape.join_T] using hjx
    have hjy' : Interp Δ Γ b σ ρ
        (Shape.T ((y₁.lift (max n₁ n₂)).join (y₂.lift (max n₁ n₂)))) := by
      simpa [TShape.join_T] using hjy
    have hdomj : TShape.NamedO Δ none (d₁.join d₂)
        (Shape.T ((x₁.lift (max n₁ n₂)).join (x₂.lift (max n₁ n₂)))) := by
      have hj := TShape.NamedO.join hΔ hcxl
        (TShape.NamedO.mono_r hΔ (TShape.NamedO.lift_subject hΔ hdx₁ k₁) hled₁ hdjty)
        (TShape.NamedO.mono_r hΔ (TShape.NamedO.lift_subject hΔ hdx₂ k₂) hled₂ hdjty)
      simpa [TShape.join_T] using hj
    have hjc' : Interp Δ (A :: Γ) B (σ.cons (a.subst σ))
        (ρ.push (Shape.T ((x₁.lift (max n₁ n₂)).join (x₂.lift (max n₁ n₂))))) (c₁.join c₂) := by
      have heq : Shape.T ((x₁.lift (max n₁ n₂)).join (x₂.lift (max n₁ n₂)))
          = (Shape.T x₁).join (Shape.T x₂) := rfl
      rw [heq]; exact hjc
    have hctyj : TShape.NamedO Δ none (c₁.join c₂)
        (Shape.T ((y₁.lift (max n₁ n₂)).join (y₂.lift (max n₁ n₂)))) := by
      have hjcc := TShape.le_join hΔ hcode₁'.wf hcode₂'.wf hcc
      have hcj : TShape.HasType Δ (c₁.join c₂) TShape.type :=
        TShape.HasType.join_sort' hΔ rfl (TShape.NamedO.hasType hcty₁).isType
          (TShape.NamedO.hasType hcty₂).isType hcc
      have hj := TShape.NamedO.join hΔ hcyl
        (TShape.NamedO.mono_r hΔ (TShape.NamedO.lift_subject hΔ hcty₁ k₁) hjcc.1 hcj)
        (TShape.NamedO.mono_r hΔ (TShape.NamedO.lift_subject hΔ hcty₂ k₂) hjcc.2 hcj)
      simpa [TShape.join_T] using hj
    -- the code and the first component keep their names through the join
    have hdcj : TShape.CodeCanonS Δ (A.subst σ) (d₁.join d₂) :=
      TShape.CodeCanonS.join hΔ    hdc₁ hdc₂
    have hxcj : Shape.ValCanon Δ (a.subst σ)
        ((x₁.lift (max n₁ n₂)).join (x₂.lift (max n₁ n₂))) :=
      Shape.ValCanon.join hΔ ((Shape.lift_wf k₁).2 hwf₁.2.2.2.1)
        ((Shape.lift_wf k₂).2 hwf₂.2.2.2.1) ((TShape.Compat.def k₁ k₂).1 hcx)
        ((Shape.ValCanon.lift hΔ k₁).2 hxc₁) ((Shape.ValCanon.lift hΔ k₂).2 hxc₂)
    exact Interp.pair hjx' hjy' hjd hdjty (.of_dom hdomj hxcj) hdcj hwS hjc' hctyj hwS'
      (TShape.LE.refl hwS') hAt hat
  · refine (TShape.LE.def hΔ (Nat.succ_le_succ k₁) (Nat.le_refl _)).2 ?_
    rw [Shape.lift_self]
    exact ⟨(Shape.le_join hΔ ((Shape.lift_wf k₁).2 hwf₁.2.2.2.1)
        ((Shape.lift_wf k₂).2 hwf₂.2.2.2.1) ((TShape.Compat.def k₁ k₂).1 hcx)).1,
      (Shape.le_join hΔ ((Shape.lift_wf k₁).2 hwf₁.2.2.2.2)
        ((Shape.lift_wf k₂).2 hwf₂.2.2.2.2) ((TShape.Compat.def k₁ k₂).1 hcy)).1,
      (Shape.lift_wf (s := ShapeS.pair ..) (Nat.succ_le_succ k₁)).2 hwf₁ |>.1,
      ((Shape.lift_wf (s := ShapeS.pair ..) (Nat.succ_le_succ k₁)).2 hwf₁).2.2.1,
      ((Shape.lift_wf (s := ShapeS.pair ..) (Nat.succ_le_succ k₁)).2 hwf₁).2.1⟩
  · refine (TShape.LE.def hΔ (Nat.succ_le_succ k₂) (Nat.le_refl _)).2 ?_
    rw [Shape.lift_self]
    exact ⟨(Shape.le_join hΔ ((Shape.lift_wf k₁).2 hwf₁.2.2.2.1)
        ((Shape.lift_wf k₂).2 hwf₂.2.2.2.1) ((TShape.Compat.def k₁ k₂).1 hcx)).2,
      (Shape.le_join hΔ ((Shape.lift_wf k₁).2 hwf₁.2.2.2.2)
        ((Shape.lift_wf k₂).2 hwf₂.2.2.2.2) ((TShape.Compat.def k₁ k₂).1 hcy)).2,
      ((Shape.lift_wf (s := ShapeS.pair ..) (Nat.succ_le_succ k₂)).2 hwf₂).1,
      ((Shape.lift_wf (s := ShapeS.pair ..) (Nat.succ_le_succ k₂)).2 hwf₂).2.2.1,
      ((Shape.lift_wf (s := ShapeS.pair ..) (Nat.succ_le_succ k₂)).2 hwf₂).2.1⟩

/-- Directedness of a pair: the `pairDF` case of `IsDefEq.dir`. -/
theorem dir_pair {Γ : List Term} {A B a b : Term}
    (ihA : SoundDir Γ A) (ihB : SoundDir (A :: Γ) B)
    (iha : SoundDir Γ a) (ihb : SoundDir Γ b) :
    SoundDir Γ (.pair A B a b) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | pair ha₁ hb₁ hA₁ hd₁ hNV hdc₁ hwf₁ hcode₁ hcty₁ hw₁ hle₁ hAt hat =>
    have hdx₁ := hNV.dom
    have hxc₁ := hNV.val
    cases h₂ with
    | bot =>
      exact ⟨_, hw₁, .pair ha₁ hb₁ hA₁ hd₁ (.of_dom hdx₁ hxc₁) hdc₁ hwf₁ hcode₁ hcty₁ hw₁ hle₁ hAt hat,
        TShape.LE.refl hw₁, TShape.bot_le' rfl⟩
    | pair ha₂ hb₂ hA₂ hd₂ hNV hdc₂ hwf₂ hcode₂ hcty₂ hw₂ hle₂ _ _ =>
      have hdx₂ := hNV.dom
      have hxc₂ := hNV.val
      obtain ⟨s, hws, hs, hs₁, hs₂⟩ :=
        dir_pair_ub hAt hat ihA ihB iha ihb hΔ W hwρ ha₁ hb₁ hA₁ hd₁ (.of_dom hdx₁ hxc₁) hdc₁ hwf₁
          hcode₁ hcty₁ ha₂ hb₂ hA₂ hd₂ (.of_dom hdx₂ hxc₂) hdc₂ hwf₂ hcode₂ hcty₂
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
    ∃ (k : Nat) (A' : Term) (g' : ShapeFun k),
      z = Shape.T (n := k+1) (ShapeS.lam A' g') := by
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
  | app hF₁ ha₁ hev₁ hw₁ hle₁ hty₁ =>
    cases h₂ with
    | bot =>
      exact ⟨_, hw₁, .app hF₁ ha₁ hev₁ hw₁ hle₁ hty₁, TShape.LE.refl hw₁, TShape.bot_le' rfl⟩
    | app hF₂ ha₂ hev₂ hw₂ hle₂ _ =>
      -- one λ-shape above both, and one shape above both arguments
      obtain ⟨z, hwz, hz, hz₁, hz₂⟩ := ihF hΔ W hwρ hF₁ hF₂
      obtain ⟨k, A, g, rfl⟩ := TShape.LE.lam_ub hz₁
      obtain ⟨x, hwx, hx, hx₁, hx₂⟩ := iha hΔ W hwρ ha₁ ha₂
      have hwg := ShapeFun.WF.forget hwz.2.2.1
      have hout : ∀ e ∈ g, TShape.WF Δ e.out.T := fun e he => (hwg.1 e he).2.2.2
      -- both lookups move into the big graph, at its label and its input
      have hmove {n'} {A' : Term} {g' : ShapeFun n'} {x' y' : TShape}
          (hF' : Interp Δ Γ F σ ρ (Shape.T (n := n'+1) (ShapeS.lam A' g')))
          (hz' : TShape.LE Δ (Shape.T (n := n'+1) (ShapeS.lam A' g'))
            (Shape.T (n := k+1) (ShapeS.lam A g)))
          (hx' : TShape.LE Δ x' x)
          (hev : TEvaluates Δ g' A' (a.subst σ) x' y') :
          TEvaluates Δ g A (a.subst σ) x y' :=
        TEvaluates.mono_inp hΔ hx' <| (TEvaluates.trans hΔ
          (TShape.LE.lam_decomp hΔ hz' hF'.wf hwz (TEvaluates.refl hwg)) hev).retype
          (TShape.LE.lam_dom hz')
      have hev₁' := hmove hF₁ hz₁ hx₁ hev₁
      have hev₂' := hmove hF₂ hz₂ hx₂ hev₂
      have hc := TEvaluates.compat hΔ hwg.2 hwx hev₁' hev₂'
      have hwy := TShape.WF.join hΔ hc (TEvaluates.wf hΔ hout hev₁')
        (TEvaluates.wf hΔ hout hev₂')
      refine ⟨_, hwy, .app hz hx (.join hc hev₁' hev₂') hwy (TShape.LE.refl hwy)
          (hty₁.retype (TShape.LE.lam_dom hz₁)),
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
theorem TShape.LE.pair_ub {Δ : List Term} {n} {A a : Term} {x y : Shape n}
    {z : TShape} (h : TShape.LE Δ (Shape.T (n := n+1) (ShapeS.pair A a x y)) z) :
    ∃ (k : Nat) (A' a' : Term) (x' y' : Shape k),
      z = Shape.T (n := k+1) (ShapeS.pair A' a' x' y') := by
  obtain ⟨j, t⟩ := z
  obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ h
  cases j with
  | zero => cases t <;> exact absurd h2 (fun x => x)
  | succ j =>
    cases t with
    | pair A' a' x' y' => exact ⟨j, A', a', x', y', rfl⟩
    | _ => exact absurd h2 (fun x => x)

/-- And its domain label is the same one. -/
theorem TShape.LE.pair_dom {Δ : List Term} {n k} {A A' a a' : Term} {x y : Shape n}
    {x' y' : Shape k}
    (h : TShape.LE Δ (Shape.T (n := n+1) (ShapeS.pair A a x y))
      (Shape.T (n := k+1) (ShapeS.pair A' a' x' y'))) : TyEq Δ A A' := by
  obtain ⟨M, _, _, h2⟩ := TShape.LE.at_succ h
  exact h2.2.2.2.1

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
      obtain ⟨k, A', a', x', y', rfl⟩ := TShape.LE.pair_ub hz₁
      obtain ⟨_, _, hx₁, _⟩ := TShape.LE.pair_decomp hΔ hz₁
      obtain ⟨_, _, hx₂, _⟩ := TShape.LE.pair_decomp hΔ hz₂
      exact ⟨Shape.T x', TShape.WF.T.2 hwz.2.2.2.1,
        .fst hz (TShape.WF.T.2 hwz.2.2.2.1) (TShape.LE.refl (TShape.WF.T.2 hwz.2.2.2.1)),
        hle₁.trans hΔ hx₁, hle₂.trans hΔ hx₂⟩

/-- Directedness for `.snd`: with the second component unconditional
this is `dir_fst`'s twin — the upper bound's own second component, with
the name moved to it by the order. -/
theorem dir_snd {Γ : List Term} {p : Term} (h : SoundDir Γ p) : SoundDir Γ (.snd p) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | snd hp₁ hlab₁ hw₁ hle₁ hty₁ =>
    cases h₂ with
    | bot =>
      exact ⟨_, hw₁, .snd hp₁ hlab₁ hw₁ hle₁ hty₁, TShape.LE.refl hw₁, TShape.bot_le' rfl⟩
    | snd hp₂ hlab₂ _ hle₂ _ =>
      obtain ⟨z, hwz, hz, hz₁, hz₂⟩ := h hΔ W hwρ hp₁ hp₂
      obtain ⟨k, A', a', x', y', rfl⟩ := TShape.LE.pair_ub hz₁
      obtain ⟨hA₁, ha₁, _, hy₁⟩ := TShape.LE.pair_decomp hΔ hz₁
      obtain ⟨_, _, _, hy₂⟩ := TShape.LE.pair_decomp hΔ hz₂
      have hwy : TShape.WF Δ (Shape.T y') := TShape.WF.T.2 hwz.2.2.2.2
      refine ⟨Shape.T y', hwy, .snd hz ?_ hwy (TShape.LE.refl hwy)
          (hty₁.retype (TShape.LE.pair_dom hz₁)),
        hle₁.trans hΔ hy₁, hle₂.trans hΔ hy₂⟩
      exact hA₁.choose_spec.defeqDF (ha₁.symm.trans hlab₁)

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
    (hA : Γ ⊢ A : .sort u) (ha : Γ ⊢ a : A)
    (ihAty : SoundTy Γ A (.sort u)) (ihadom : SoundDom Γ a A) :
    SoundEq Γ (.fst (.pair A B a b)) a := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  obtain ⟨n, s⟩ := m
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  constructor
  · intro h
    cases h with
    | bot => exact .bot
    | fst hp hw hle =>
      cases hp with
      | pair ha _ _ _ _ _ hwf' _ _ _ hle' =>
        exact ha.mono hΔ hw (hle.trans hΔ (TShape.LE.pair_decomp hΔ hle').2.2.1)
  · intro h
    -- the first component has to be hereditarily typed, so saturate it
    obtain ⟨⟨k, s'⟩, d, hs', hle', hd, hNV, hdc'⟩ := ihadom hΔ W hAdm h
    have hdom' := hNV.dom
    have hsc' := hNV.val
    by_cases hb : s'.IsBot
    · rw [show s = Shape.bot from
        TShape.le_bot hΔ (Shape.WF.eq_bot_of_isBot hs'.wf hb) hle']
      exact .bot
    · have hwf : Shape.WF (n := k+1) Δ
          (ShapeS.pair (A.subst σ) (a.subst σ) s' Shape.bot) :=
        ⟨fun hbb => hb hbb.1, IsDefEq.subst hΔ W ha, TyEq.refl hAσ, hs'.wf, Shape.WF.bot⟩
      exact .fst (.pair (c := TShape.bot) hs' .bot hd (ihAty.isType hΔ W hAdm hd) (.of_dom hdom' hsc') hdc'
        hwf
        .bot (TShape.NamedO.bot (TShape.HasType.bot_bot rfl)) hwf (TShape.LE.refl hwf) ⟨u, hA⟩ ha)
        h.wf hle'

/-- The second projection of a pair: the `pair_snd` case. -/
theorem sound_pair_snd {Γ : List Term} {A B a b : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) (ha : Γ ⊢ a : A)
    (hPB : B.Pinned (A :: Γ))
    (hfst : Γ ⊢ .fst (.pair A B a b) ≡ a : A)
    (ihAty : SoundTy Γ A (.sort u)) (ihadom : SoundDom Γ a A)
    (ihbdom : SoundDom Γ b (B.inst a))
    (ihadir : SoundDir Γ a) :
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
    | snd hp _ hw hle =>
      -- the second component *is* an approximant of `b`
      cases hp with
      | pair _ hb _ _ _ _ _ _ _ _ hle' =>
        exact hb.mono hΔ hw (hle.trans hΔ (TShape.LE.pair_decomp hΔ hle').2.2.2)
  · intro h
    by_cases hb : s.IsBot
    · rw [Shape.WF.eq_bot_of_isBot (s := s) h.wf hb]; exact .bot
    · -- the first component is enlarged until it is hereditarily typed,
      -- which is what the clause's slot asks of it, and the second
      -- component comes with the code that types it
      obtain ⟨⟨nb, sb⟩, c, hmb, hmle, hc, hNV, _⟩ := ihbdom hΔ W hAdm h
      have hdc := hNV.dom
      obtain ⟨x₀, hbody₀, hx₀⟩ :=
        (Interp.inst (A := A) (b := B) hΔ hΓ hA ha hB hPB W hAdm
          (Subst.Saturates.one hΔ hΓ W hAdm ihadom)
          (ihadir hΔ W hwρ) hwρ).1 hc
      obtain ⟨x, d, hx, hlex, hd, hNV, hdcx⟩ := ihadom hΔ W hAdm hx₀
      have hxd := hNV.dom
      have hxcx := hNV.val
      have hbody : Interp Δ (A :: Γ) B ((Subst.one a).comp σ) (ρ.push x) c :=
        Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hlex⟩) hbody₀
      obtain ⟨k, hkx, hkn⟩ : ∃ k, x.1 ≤ k ∧ nb ≤ k :=
        ⟨max x.1 nb, Nat.le_max_left .., Nat.le_max_right ..⟩
      have hwx : Shape.WF Δ (x.2.lift k) := (Shape.lift_wf hkx).2 hx.wf
      have hws : Shape.WF Δ (sb.lift k) := (Shape.lift_wf hkn).2 hmb.wf
      have hnb : ¬ (sb.lift k).IsBot := fun hbb => hb (by
        rw [show s = Shape.bot from TShape.le_bot hΔ
          (Shape.WF.eq_bot_of_isBot hmb.wf ((Shape.lift_isBot hkn).1 hbb)) hmle]
        exact Shape.isBot_bot)
      have hwf : Shape.WF (n := k+1) Δ (ShapeS.pair (A.subst σ)
          (a.subst σ) (x.2.lift k) (sb.lift k)) :=
        ⟨fun hbb => hnb hbb.2, haσ, TyEq.refl hAσ, hwx, hws⟩
      have hbody' : Interp Δ (A :: Γ) B (σ.cons (a.subst σ))
          (ρ.push (Shape.T (x.2.lift k))) c := by
        refine Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
          TShape.LE.le_lift hΔ hkx hx.wf⟩) ?_
        rw [← Subst.one_comp]; exact hbody
      exact .snd (.pair (c := c) (Interp.lift hΔ hkx hx)
          (Interp.lift (m := ⟨nb, sb⟩) hΔ hkn hmb) hd (ihAty.isType hΔ W hAdm hd)
          (.of_dom (TShape.NamedO.lift_subject hΔ hxd hkx)
            ((Shape.ValCanon.lift hΔ hkx).2 hxcx)) hdcx
          hwf hbody'
          (TShape.NamedO.lift_subject hΔ hdc hkn) hwf (TShape.LE.refl hwf) ⟨u, hA⟩ ha)
        (IsDefEq.subst hΔ W hfst.symm) h.wf
        (TShape.LE.trans hΔ hmle (TShape.LE.le_lift (m := ⟨nb, sb⟩) hΔ hkn hmb.wf))
        (Stable.of_typed hfst.hasType.1 (TyEq.refl hAσ))

/-- **Saturation at a first projection.**  The pair's own saturation
puts its first component in `Dom`'s Σ clause, and the projection reads
exactly that component. -/
theorem sound_fst_dom {Γ : List Term} {A B p : Term}
    (hpdom : SoundDom Γ p (.sigma A B)) : SoundDom Γ (.fst p) A := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  cases hm with
  | bot =>
    exact ⟨TShape.bot, TShape.bot, .bot, TShape.bot_le' rfl, .bot, (.of_dom (TShape.NamedO.bot (.bot (.bot .sort))) (TShape.ValCanon.of_bot rfl)), TShape.CodeCanonS.bot⟩
  | fst hp hw hle =>
    obtain ⟨P', S, hP', hPle, hS, hNV, hScan⟩ := hpdom hΔ W hAdm hp
    have hPdom := hNV.dom
    have hPcan := hNV.val
    -- the code is a Σ-shape, since `P'` dominates a pair
    have hSsg : S.IsSigma := by
      rcases (show S.2 = Shape.bot ∨ S.IsSigma from by
          cases hS with
          | bot => exact .inl rfl
          | sigma _ _ _ _ _ _ hles _ _ => exact TShape.isSigma_or_bot_of_le hles trivial)
        with hb | h
      · exact absurd (TShape.le_bot hΔ (TShape.HasType.bot_r hΔ hb hPdom.hasType) hPle)
          (by simp [Shape.bot])
      · exact h
    cases hPdom with
    | base hnb _ => exact absurd hSsg.isBinder hnb
    | pi _ _ _ _ => exact absurd hSsg (TShape.IsPi.not_sigma trivial)
    | @sg _ nS A' B' dS fS _ ps cc hty hps _ hxd' hevc hout =>
      -- `P'` is a pair-shape; its first component is the projection's
      -- value, and `Dom`'s Σ clause has it
      cases hty with
      | bot hb => exact absurd (TShape.le_bot hΔ rfl hPle) (by simp [Shape.bot])
      | refl hleid hAty' =>
        exact absurd hleid (by
          intro h
          obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ h
          exact absurd h2 (fun x => x))
      | @pair nP _ A₀' a₀' x' y' _ _ _ _ _ _ hd hfo hwP hwSg hxd hxle' hev' hyty hlabP =>
        obtain ⟨_, _, hxle, _⟩ := TShape.LE.pair_decomp hΔ hPle
        refine ⟨Shape.T x', dS.T, .fst hP' (TShape.WF.T.2 hwP.2.2.2.1)
            (TShape.LE.refl (TShape.WF.T.2 hwP.2.2.2.1)),
          TShape.LE.trans hΔ hle hxle, ?_, .of_dom ?_ hPcan.2.1, ?_⟩
        · -- the domain is an approximant of `A`
          cases hS with
          | @sigma _ _ _ _ nc gc dc _ _ hAint hdty hwfc _ hbodyc hwmc hleSg =>
            obtain ⟨_, hdle, _⟩ :=
              TShape.LE.sigma_decomp hΔ hleSg hwSg hwfc (TEvaluates.refl hwfc.2.2.2.1)
            exact Interp.mono hΔ (TShape.HasType.wf hd).1 hdle hAint
        · exact hxd' _ (by rw [← hps]; rfl)
        · -- and names `A`: the code names its own domain label, which the
          -- order identifies with the syntactic one
          cases hS with
          | @sigma _ _ _ _ nc gc dc _ _ hAint hdty hwfc _ hbodyc hwmc hleSg =>
            obtain ⟨hPL, _, _⟩ :=
              TShape.LE.sigma_decomp hΔ hleSg hwSg hwfc (TEvaluates.refl hwfc.2.2.2.1)
            exact Shape.CodeCanonS.conv (Shape.WFO.canon hwSg.2.2.1) (TyEq.symm hPL.1)

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
        | sigma hA hd₀ hwf _ _ _ hleS =>
          obtain ⟨_, hdd, _⟩ :=
            TShape.LE.sigma_decomp hΔ hleS hwSg hwf (TEvaluates.refl hwf.2.2.2.1)
          exact ⟨_, hA, TShape.HasType.mono_r hΔ
            (TShape.HasType.mono_l hΔ hxd hle) _ hdd hd₀⟩

/-- **The Σ-approximant read off a pair-approximant.**  Unlike the λ
case there is no graph to rebuild: `Interp.pair` already carries a code
for every entry.  This is the Σ-shape whose domain is the clause's own
domain slot joined with a code for `a`, and whose graph has one entry
per code; `sound_pair_ty` reads the typing off it, `sound_pair_dom` the
hereditary typing. -/
theorem pair_sigma_code {Γ Γ₀ Δ : List Term} {A B a : Term} {u v : Bool} {σ ρ}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v)
    (ihAty : SoundTy Γ A (.sort u)) (ihAc : CodeAt Γ A) (ihAdir : SoundDir Γ A)
    (ihaty : SoundTy Γ a A)
    (ihBty : SoundTy (A :: Γ) B (.sort v)) (ihBc : CodeAt (A :: Γ) B)
    (ihBdir : SoundDir (A :: Γ) B)
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {n} {x y : Shape n} {d c : TShape} 
    (ha : Interp Δ Γ a σ ρ (Shape.T x)) (hA : Interp Δ Γ A σ ρ d)
    (hd : TShape.HasType Δ d TShape.type)
    (hNV : TShape.Named Δ d (a.subst σ) (Shape.T x))
    (hdc : TShape.CodeCanonS Δ (A.subst σ) d)
    (hwp : Shape.WF (n := n+1) Δ (.pair (A.subst σ) (a.subst σ) x y))
    (hcode : Interp Δ (A :: Γ) B (σ.cons (a.subst σ)) (ρ.push (Shape.T x)) c)
    (hcty : TShape.NamedO Δ none c (Shape.T y)) :
    ∃ (k : Nat) (dk : Shape k) (f : ShapeFun k),
      Interp Δ Γ (.sigma A B) σ ρ
        (Shape.T (n := k+1) (.sigma (A.subst σ) (B.subst σ.lift) dk f)) ∧
      TShape.HasType Δ (Shape.T (n := n+1) (.pair (A.subst σ) (a.subst σ) x y))
        (Shape.T (n := k+1) (.sigma (A.subst σ) (B.subst σ.lift) dk f)) ∧
      TShape.HasType Δ (Shape.T dk) TShape.type ∧
      TShape.NamedO Δ none (Shape.T dk) (Shape.T x) ∧
      (∃ cc, TEvaluates Δ f (A.subst σ) (a.subst σ) (Shape.T x) cc ∧
        TShape.HasType Δ cc TShape.type ∧ TShape.NamedO Δ none cc (Shape.T y)) ∧
      TShape.CodeCanonS Δ ((Term.sigma A B).subst σ)
        (Shape.T (n := k+1) (.sigma (A.subst σ) (B.subst σ.lift) dk f)) := by
  have hdx := hNV.dom
  have hxc := hNV.val
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hAty⟩
  have hwρ := hAdm.wf
  have hAσ : Δ ⊢ A.subst σ : .sort u := hAty.subst hΔ W
  have hΔA : ⊢ (A.subst σ :: Δ) := ⟨hΔ, _, hAσ⟩
  -- the pair's own stage is admissible
  have hstage : Ctx.SubstEq Δ (σ.cons (a.subst σ)) (σ.cons (a.subst σ)) (A :: Γ) ∧
      Adm Δ Γ₀ (A :: Γ) (σ.cons (a.subst σ)) (ρ.push (Shape.T x)) :=
    ⟨.cons W hAty hwp.2.1,
      .cons hAdm W.wf hA
        (TShape.WF.T.2 hwp.2.2.2.1) (.of_dom hdx hxc) hdc⟩
  -- the first component, typed at a domain shape joined with the clause's
  obtain ⟨c₀, hc₀, hxc₀⟩ := ihaty.approx hΔ W hAdm ha
  obtain ⟨hcd, hdj⟩ := (ihAdir hΔ W hwρ).join hΔ hA hc₀
  have hdjty : TShape.HasType Δ (d.join c₀) TShape.type :=
    TShape.HasType.join_sort' hΔ rfl hd (ihAty.isType hΔ W hAdm hc₀) hcd
  obtain ⟨hled, hlec⟩ := TShape.le_join hΔ hA.wf hc₀.wf hcd
  -- one level for the code, the joined domain and the single entry
  obtain ⟨k, hkn, hkd, hkc⟩ : ∃ k, n ≤ k ∧ (d.join c₀).1 ≤ k ∧ c.1 ≤ k :=
    ⟨max n (max (d.join c₀).1 c.1), Nat.le_max_left .., 
      Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..),
      Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..)⟩
  have hcwf : Shape.WF Δ c.2 := hcode.wf
  -- the Σ-code's graph: the pair's own name, first component and code
  let f : ShapeFun k := [⟨a.subst σ, x.lift k, c.2.lift k⟩]
  have hfmem : ∀ e ∈ f, e = (⟨a.subst σ, x.lift k, c.2.lift k⟩ :
      Entry (Shape k)) := by
    intro e he
    simpa [f] using he
  have hdty : TShape.HasType Δ (Shape.T ((d.join c₀).2.lift k)) TShape.type :=
    hdjty.lift_subject hΔ hkd
  have hdle : TShape.LE Δ (d.join c₀) (Shape.T ((d.join c₀).2.lift k)) :=
    TShape.LE.le_lift hΔ (m := d.join c₀) hkd hdjty.wf.1
  have hcodety : TShape.HasType Δ c TShape.type :=
    ihBty.isType hΔ hstage.1 hstage.2 hcode
  have hcodety' : TShape.HasType Δ (Shape.T (c.2.lift k)) TShape.type :=
    hcodety.lift_subject hΔ hkc
  have hfent : ∀ e ∈ f, (∃ u, Δ ⊢ A.subst σ : .sort u) ∧ Δ ⊢ e.tm : A.subst σ ∧
      Shape.WF Δ e.inp ∧ Shape.WF Δ e.out := by
    intro e he
    rw [hfmem e he]
    exact ⟨⟨u, hAσ⟩, hwp.2.1, (Shape.lift_wf hkn).2 hwp.2.2.2.1,
      (Shape.lift_wf hkc).2 hcwf⟩
  have hfdom : ∀ e ∈ f, TShape.NamedO Δ none (Shape.T ((d.join c₀).2.lift k)) e.inp.T := by
    intro e he
    rw [hfmem e he]
    exact TShape.NamedO.mono_r hΔ
      (TShape.NamedO.lift_subject hΔ (TShape.NamedO.mono_r hΔ hdx hled hdjty) hkn) hdle hdty
  have hfbody : ∀ e ∈ f,
      Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push e.inp.T) e.out.T := by
    intro e he
    rw [hfmem e he]
    refine Interp.mono hΔ ((Shape.lift_wf hkc).2 hcwf)
      (TShape.LE.lift_le hΔ (m := c) hkc hcwf) ?_
    exact Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
      TShape.LE.le_lift hΔ (m := Shape.T x) hkn (TShape.WF.T.2 hwp.2.2.2.1)⟩) hcode
  have hcdSg : Shape.CodeCanonS Δ (A.subst σ) ((d.join c₀).2.lift k) :=
    (Shape.CodeCanonS.lift_iff hkd).2
      (TShape.CodeCanonS.join hΔ    hdc (ihAc hΔ W hAdm hc₀))
  have hcfSg : ∀ e ∈ f, Shape.CodeCanonS Δ ((B.subst σ.lift).inst e.tm) e.out := by
    intro e he
    rw [hfmem e he]
    have hcc := ihBc hΔ hstage.1 hstage.2 hcode
    rw [← inst_lift_cons] at hcc
    exact (Shape.CodeCanonS.lift_iff hkc).2 hcc
  have hwfSg : Shape.WF (n := k+1) Δ
      (.sigma (A.subst σ) (B.subst σ.lift) ((d.join c₀).2.lift k) f) :=
    ⟨⟨u, hAσ⟩, ⟨v, hB.subst hΔA (W.lift hAty hAσ)⟩,
      Shape.WF.name ((Shape.lift_wf hkd).2 hdjty.wf.1) hcdSg,
      ShapeFun.WF.name
        ⟨fun e he => hfent e he,
         graph_coherent hΓ hAty hB W hwρ ihBdir (fun e he => (hfent e he).2.2.1)
           hfbody⟩ hcfSg, trivial⟩
  have hSg : Interp Δ Γ (.sigma A B) σ ρ
      (Shape.T (n := k+1) (.sigma (A.subst σ) (B.subst σ.lift) ((d.join c₀).2.lift k) f)) :=
    .sigma (Interp.mono hΔ ((Shape.lift_wf hkd).2 hdjty.wf.1)
        (TShape.LE.lift_le hΔ (m := d.join c₀) hkd hdjty.wf.1) hdj)
      hdty hwfSg
      (fun e he => by
        exact .of_dom (hfdom _ he) (by rw [hfmem e he]; exact (Shape.ValCanon.lift hΔ hkn).2 hxc))
      hfbody hwfSg (TShape.LE.refl hwfSg) ⟨u, hAty⟩ ⟨v, hB⟩
  -- the code is the lookup at the pair's own name and first component
  have hlook : TEvaluates Δ f (A.subst σ) (a.subst σ) (Shape.T x)
      (Shape.T (c.2.lift k)) :=
    TEvaluates.entry _ (List.mem_cons_self) ⟨TyEq.refl hAσ, hwp.2.1⟩
      (TShape.LE.lift_le hΔ (m := Shape.T x) hkn (TShape.WF.T.2 hwp.2.2.2.1))
  refine ⟨k, (d.join c₀).2.lift k, f, hSg,
    TShape.HasType.pair hdty (fun e he => by rw [hfmem e he]; exact hcodety') hwp hwfSg
      (TShape.HasType.mono_r hΔ (TShape.HasType.mono_r hΔ hxc₀ _ hlec hdjty) _ hdle hdty)
      (TShape.LE.refl (TShape.WF.T.2 hwp.2.2.2.1)) hlook
      (TShape.HasType.mono_r hΔ (TShape.NamedO.hasType hcty) _
        (TShape.LE.le_lift hΔ (m := c) hkc hcwf) hcodety')
      (TyEq.refl hAσ),
    hdty,
    TShape.NamedO.mono_r hΔ (TShape.NamedO.mono_r hΔ hdx hled hdjty) hdle hdty,
    ⟨_, hlook, hcodety',
      TShape.NamedO.mono_r hΔ hcty (TShape.LE.le_lift hΔ (m := c) hkc hcwf) hcodety'⟩, ?_⟩
  -- the Σ-code names `Σ A B`: its domain joins two approximants of `A`,
  -- and its one entry is an approximant of `B` at the pair's own name
  exact ⟨true, (IsDefEq.sigmaDF hAty hB hB).subst hΔ W⟩

/-- **The type of a pair**, and shorter than the λ's,
because `Interp.pair` already carries the codes: a pair's graph is
certified by a generator whose codes are approximants of `B` at each
entry's slot, so the Σ-shape's graph is that generator, lifted to one
level.  The only thing the clause does not carry is a typing of the
first component at the *same* domain shape its entries are typed at, and
that is one call each to `SoundTy a A` and `A`'s directedness. -/
theorem sound_pair_ty {Γ : List Term} {A B a b : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v)
    (hpair : Γ ⊢ .pair A B a b : .sigma A B)
    (ihAty : SoundTy Γ A (.sort u)) (ihAc : CodeAt Γ A) (ihAdir : SoundDir Γ A)
    (ihaty : SoundTy Γ a A)
    (ihBty : SoundTy (A :: Γ) B (.sort v)) (ihBc : CodeAt (A :: Γ) B)
    (ihBdir : SoundDir (A :: Γ) B) :
    SoundTy Γ (.pair A B a b) (.sigma A B) := by
  refine ⟨hpair, ?_⟩
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  cases hm with
  | bot => exact ⟨TShape.bot, .bot, .bot (.bot .sort)⟩
  | pair ha hb hA hd hNV hdc hwp hcode hcty hw hle =>
    have hdx := hNV.dom
    have hxc := hNV.val
    obtain ⟨k, dk, f, hSg, hty, _⟩ :=
      pair_sigma_code hΓ hAty hB ihAty ihAc ihAdir ihaty ihBty ihBc ihBdir hΔ W hAdm
        ha hA hd (.of_dom hdx hxc) hdc hwp hcode hcty
    exact ⟨_, hSg, TShape.HasType.mono_l hΔ hty hle⟩

/-- Building a `TShape.LE` between two pair shapes at different levels. -/
theorem TShape.LE.pair_mk {Δ : List Term} {n k} {A a A' a' : Term}
    {x y : Shape n} {x' y' : Shape k} (hΔ : ⊢ Δ)
    (hx : TShape.LE Δ (Shape.T x) (Shape.T x')) (hy : TShape.LE Δ (Shape.T y) (Shape.T y'))
    (hnd : ¬ (x.IsBot ∧ y.IsBot)) (hA : TyEq Δ A A') (ha : Δ ⊢ a ≡ a' : A) :
    TShape.LE Δ (Shape.T (n := n+1) (ShapeS.pair A a x y))
      (Shape.T (n := k+1) (ShapeS.pair A' a' x' y')) := by
  refine (TShape.LE.def hΔ (Nat.succ_le_succ (Nat.le_max_left n k))
    (Nat.succ_le_succ (Nat.le_max_right n k))).2 ?_
  refine ⟨(TShape.LE.def hΔ (Nat.le_max_left n k) (Nat.le_max_right n k)).1 hx,
    (TShape.LE.def hΔ (Nat.le_max_left n k) (Nat.le_max_right n k)).1 hy, ?_, hA, ha⟩
  exact fun hb => hnd ⟨(Shape.lift_isBot (Nat.le_max_left n k)).1 hb.1,
    (Shape.lift_isBot (Nat.le_max_left n k)).1 hb.2⟩

/-- **Saturation at a pair.**  A pair-approximant's second component is
an arbitrary approximant of `b`, so the dominator is rebuilt: `b`'s own
saturation enlarges it, `Interp.inst` reads its code as `B` at a slot
approximating `a`, that slot is joined with the given first component,
and `a`'s saturation enlarges the join.  The rebuilt pair names its own
projections because both components do, moved along `pair_fst`/`pair_snd`;
its code is `pair_sigma_code`'s. -/
theorem sound_pair_dom {Γ : List Term} {A B a b : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v)
    (hat : Γ ⊢ a : A) (hbt : Γ ⊢ b : B.inst a) (hPB : B.Pinned (A :: Γ))
    (ihAty : SoundTy Γ A (.sort u)) (ihAd : SoundDom Γ A (.sort u)) (ihAdir : SoundDir Γ A)
    (ihaty : SoundTy Γ a A) (ihadom : SoundDom Γ a A) (ihadir : SoundDir Γ a)
    (ihbdom : SoundDom Γ b (B.inst a))
    (ihBty : SoundTy (A :: Γ) B (.sort v)) (ihBc : CodeAt (A :: Γ) B)
    (ihBdir : SoundDir (A :: Γ) B) :
    SoundDom Γ (.pair A B a b) (.sigma A B) := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  have hwρ := hAdm.wf
  have hAσ : Δ ⊢ A.subst σ : .sort u := hAty.subst hΔ W
  cases hm with
  | bot => exact ⟨TShape.bot, TShape.bot, .bot, TShape.bot_le' rfl, .bot, (.of_dom (TShape.NamedO.bot (.bot (.bot .sort))) (TShape.ValCanon.of_bot rfl)), TShape.CodeCanonS.bot⟩
  | @pair _ _ _ _ n x y d c _ _ _ _ ha hb hA hd _ hdc hwp hcode hcty hw hle hAt hat' =>
    -- the second component, saturated, with its code
    obtain ⟨y', cb, hy', hyle, hcb, hNV, hcbc⟩ := ihbdom hΔ W hAdm hb
    have hdy' := hNV.dom
    have hy'c := hNV.val
    -- that code is `B` read at a slot approximating `a`
    obtain ⟨x₀, hbody₀, hx₀⟩ :=
      (Interp.inst (A := A) (b := B) hΔ hΓ hAty hat hB hPB W hAdm
        (Subst.Saturates.one hΔ hΓ W hAdm ihadom)
        (ihadir hΔ W hwρ) hwρ).1 hcb
    -- joined with the given first component, then saturated
    obtain ⟨x₁, _, hx₁, hxx₁, hx₀x₁⟩ := ihadir hΔ W hwρ ha hx₀
    obtain ⟨x', d', hx', hx₁x', hd', hNV, hd'c⟩ := ihadom hΔ W hAdm hx₁
    have hdx' := hNV.dom
    have hx'c := hNV.val
    have hd'ty : TShape.HasType Δ d' TShape.type := ihAty.isType hΔ W hAdm hd'
    -- one level for both components
    obtain ⟨k, hkx, hky⟩ : ∃ k, x'.1 ≤ k ∧ y'.1 ≤ k :=
      ⟨max x'.1 y'.1, Nat.le_max_left .., Nat.le_max_right ..⟩
    have hwx' : Shape.WF Δ (x'.2.lift k) := (Shape.lift_wf hkx).2 hx'.wf
    have hwy' : Shape.WF Δ (y'.2.lift k) := (Shape.lift_wf hky).2 hy'.wf
    have hxle : TShape.LE Δ (Shape.T x) (Shape.T (x'.2.lift k)) :=
      (hxx₁.trans hΔ hx₁x').trans hΔ (TShape.LE.le_lift hΔ hkx hx'.wf)
    have hyle' : TShape.LE Δ (Shape.T y) (Shape.T (y'.2.lift k)) :=
      hyle.trans hΔ (TShape.LE.le_lift hΔ hky hy'.wf)
    -- the rebuilt pair is not information-free, since the given one is not
    have hnb : ¬ ((x'.2.lift k).IsBot ∧ (y'.2.lift k).IsBot) := by
      rintro ⟨hbx, hby⟩
      refine hwp.1 ⟨?_, ?_⟩
      · have hx0 : x = Shape.bot := TShape.le_bot hΔ (Shape.WF.eq_bot_of_isBot hwx' hbx) hxle
        rw [hx0]; exact Shape.isBot_bot
      · have hy0 : y = Shape.bot := TShape.le_bot hΔ (Shape.WF.eq_bot_of_isBot hwy' hby) hyle'
        rw [hy0]; exact Shape.isBot_bot
    have hwP : Shape.WF (n := k+1) Δ
        (ShapeS.pair (A.subst σ) (a.subst σ) (x'.2.lift k) (y'.2.lift k)) :=
      ⟨hnb, hwp.2.1, hwp.2.2.1, hwx', hwy'⟩
    have hcodeL : Interp Δ (A :: Γ) B (σ.cons (a.subst σ))
        (ρ.push (Shape.T (x'.2.lift k))) cb := by
      have h := Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
        (hx₀x₁.trans hΔ hx₁x').trans hΔ (TShape.LE.le_lift hΔ hkx hx'.wf)⟩) hbody₀
      rwa [Subst.one_comp] at h
    have hdxL : TShape.NamedO Δ none d' (Shape.T (x'.2.lift k)) := TShape.NamedO.lift_subject hΔ hdx' hkx
    have hdyL : TShape.NamedO Δ none cb (Shape.T (y'.2.lift k)) := TShape.NamedO.lift_subject hΔ hdy' hky
    have hxcL : Shape.ValCanon Δ (a.subst σ) (x'.2.lift k) := (Shape.ValCanon.lift hΔ hkx).2 hx'c
    have hP : Interp Δ Γ (.pair A B a b) σ ρ
        (Shape.T (n := k+1) (ShapeS.pair (A.subst σ) (a.subst σ) (x'.2.lift k) (y'.2.lift k))) :=
      .pair (Interp.lift hΔ hkx hx') (Interp.lift hΔ hky hy') hd' hd'ty (.of_dom hdxL hxcL) hd'c hwP
        hcodeL hdyL (TShape.WF.T.2 hwP) (TShape.LE.refl (TShape.WF.T.2 hwP)) hAt hat'
    have hPle := TShape.LE.pair_mk hΔ hxle hyle' hwp.1 (TyEq.refl hAσ) hwp.2.1
    obtain ⟨kS, dS, fS, hSg, hty, _, hdfst, ⟨cc, hlook, _, hccdom⟩, hScan⟩ :=
      pair_sigma_code hΓ hAty hB ihAty ihAd.codeAt ihAdir ihaty ihBty ihBc ihBdir hΔ W hAdm
        (Interp.lift hΔ hkx hx') hd' hd'ty (.of_dom hdxL hxcL) hd'c hwP hcodeL hdyL
    -- the two β-rules, at the stage
    have hfst : Δ ⊢ (Term.fst (.pair A B a b)).subst σ ≡ a.subst σ : A.subst σ :=
      (IsDefEq.pair_fst₀ hΓ hB hat hbt).subst hΔ W
    have hsnd : Δ ⊢ (Term.snd (.pair A B a b)).subst σ ≡ b.subst σ : (B.inst a).subst σ :=
      (IsDefEq.pair_snd₀ hΓ hB hat hbt).subst hΔ W
    exact ⟨_, _, hP, hle.trans hΔ hPle, hSg, (.of_dom (.sg (ps := some (a.subst σ, Shape.T (x'.2.lift k), Shape.T (y'.2.lift k))) (c := cc) hty rfl (fun _ _ => nofun)
        (fun p hp => by cases hp; exact hdfst)
        (fun p hp => by cases hp; exact hlook)
        (fun p hp => by cases hp; exact hccdom)) (⟨hfst.symm, Shape.ValCanon.defeq hΔ hdxL hd'c hxcL hfst.symm,
        Shape.ValCanon.defeq hΔ hdyL hcbc ((Shape.ValCanon.lift hΔ hky).2 hy'c) hsnd.symm⟩)),
      hScan⟩

/-- One direction of the `SoundEq` half of `pairDF`.  A pair-shape's only
label is its domain, and its entries' label terms name the *first
component*, so the two things that move are that label (up to `TyEq`, as
at λ) and those terms (along `a ≡ a'`, at the entry's own type).  The
codomain's values do not move at all: their stage is the entry's label
term, which is unchanged. -/
theorem sound_pair_eq_of {Γ : List Term} {A A' B B' a a' b b' : Term} {u v : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (haa' : Γ ⊢ a ≡ a' : A)
    (hB'ty : A' :: Γ ⊢ B' ≡ B' : .sort v)
    (ihA : SoundEq Γ A A')
    (iha : SoundEq Γ a a') (ihb : SoundEq Γ b b') (ihB : SoundEq (A :: Γ) B B')
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {m : TShape} (H : Interp Δ Γ (.pair A B a b) σ ρ m) :
    Interp Δ Γ (.pair A' B' a' b') σ ρ m := by
  have hAσ : TyEq Δ (A.subst σ) (A'.subst σ) := ⟨u, hAA'.subst hΔ W⟩
  have haσ : Δ ⊢ a.subst σ ≡ a'.subst σ : A.subst σ := haa'.subst hΔ W
  cases H with
  | bot => exact .bot
  | @pair _ _ _ _ n x y d c _ _ _ _ ha hb hA hd hNV hdc hwp hcode hcty hw hle hAt hat =>
    have hdx := hNV.dom
    have hxc := hNV.val
    have hwp' : Shape.WF (n := n+1) Δ
        (ShapeS.pair (A'.subst σ) (a'.subst σ) x y) :=
      ⟨hwp.1, hAσ.choose_spec.defeqDF (haσ.symm.trans haσ), TyEq.refl_r hAσ,
        hwp.2.2.2.1, hwp.2.2.2.2⟩
    have W' : Ctx.SubstEq Δ (σ.cons (a.subst σ)) (σ.cons (a.subst σ)) (A :: Γ) :=
      .cons W hAA'.hasType.1 hwp.2.1
    have hAdm' : Adm Δ Γ₀ (A :: Γ) (σ.cons (a.subst σ)) (ρ.push (Shape.T x)) :=
      .cons hAdm W.wf hA
        (TShape.WF.T.2 hwp.2.2.2.1) (.of_dom hdx hxc) hdc
    -- the codomain's value, at the pair's own name moved along `a ≡ a'`
    have hcode' : Interp Δ (A' :: Γ) B' (σ.cons (a.subst σ)) (ρ.push (Shape.T x)) c :=
      Interp.ctx ((ihB hΔ W' hAdm').1 hcode)
        (show ⊢ (A' :: Γ) from ⟨W.wf, _, hAA'.hasType.2⟩)
        (Ctx.SubstEq.defeqHead W.wf hAA')
    have hcode'' : Interp Δ (A' :: Γ) B' (σ.cons (a'.subst σ)) (ρ.push (Shape.T x)) c :=
      IsDefEq.stage (show ⊢ (A' :: Γ) from ⟨W.wf, _, hAA'.hasType.2⟩) hB'ty hΔ
        (Ctx.SubstEq.cons (σ := σ.cons (a.subst σ)) (σ' := σ.cons (a'.subst σ)) W
          hAA'.hasType.2 (hAσ.choose_spec.defeqDF haσ)) hcode'
    exact .pair ((iha hΔ W hAdm).1 ha) ((ihb hΔ W hAdm).1 hb) ((ihA hΔ W hAdm).1 hA)
      hd ((TShape.Named.of_dom hdx hxc).defeq hΔ hdc haσ)
      (TShape.CodeCanonS.conv hdc (TyEq.symm hAσ)) hwp' hcode'' hcty hw
      (hle.trans hΔ (TShape.LE.T.2 (show Shape.LE (n := n+1) Δ (ShapeS.pair ..)
        (ShapeS.pair ..) from
        ⟨Shape.LE.refl hwp.2.2.2.1, Shape.LE.refl hwp.2.2.2.2, hwp.1, hAσ, haσ⟩)))
      ⟨u, hAA'.hasType.2⟩ (hAA'.defeqDF (haa'.hasType.2))

/-- The `SoundEq` half of `pairDF`. -/
theorem sound_pair_eq {Γ : List Term} {A A' B B' a a' b b' : Term} {u v : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (haa' : Γ ⊢ a ≡ a' : A)
    (hBty : A :: Γ ⊢ B ≡ B : .sort v) (hB'ty : A' :: Γ ⊢ B' ≡ B' : .sort v)
    (ihA : SoundEq Γ A A')
    (iha : SoundEq Γ a a') (ihb : SoundEq Γ b b')
    (ihB : SoundEq (A :: Γ) B B') (ihB' : SoundEq (A' :: Γ) B B') :
    SoundEq Γ (.pair A B a b) (.pair A' B' a' b') := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  exact ⟨sound_pair_eq_of hAA' haa' hB'ty ihA iha ihb ihB hΔ W hAdm,
    sound_pair_eq_of hAA'.symm (hAA'.defeqDF haa'.symm)
      hBty
      ihA.symm iha.symm ihb.symm ihB'.symm hΔ W hAdm⟩

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
    obtain ⟨_, htmj⟩ := hlabj
    have Wcons : Ctx.SubstEq Δ (σ.cons ej.tm) (σ.cons tm) (A :: Γ) :=
      .cons W hA (hty.choose_spec.defeqDF htmj)
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
theorem dir_inst {Γ Γ₀ Δ : List Term} {A a b B : Term} {u : Bool} {σ ρ}
    (hA : Γ ⊢ A : .sort u) (ha : Γ ⊢ a : A) (hb : A :: Γ ⊢ b : B)
    (hPb : b.Pinned (A :: Γ)) (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ)
    (hAdm : Adm Δ Γ₀ Γ σ ρ) (hΓ : ⊢ Γ) (hadom : SoundDom Γ a A)
    (iha : SoundDir Γ a) (ihb : SoundDir (A :: Γ) b) :
    Interp.Dir Δ Γ (b.inst a) σ ρ := by
  have hwρ : Valuation.WF Δ ρ := hAdm.wf
  intro m₁ m₂ h₁ h₂
  have hinst : ∀ {m : TShape}, Interp Δ Γ (b.inst a) σ ρ m ↔
      ∃ x, Interp Δ (A :: Γ) b ((Subst.one a).comp σ) (ρ.push x) m ∧
        Interp Δ Γ a σ ρ x := fun {_} =>
    Interp.inst hΔ W.wf hA ha hb hPb W hAdm
      (Subst.Saturates.one hΔ hΓ W hAdm hadom) (iha hΔ W hwρ) hwρ
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
    | forallE _ _ hwf _ _ _ hle =>
      obtain ⟨hPi, _, _⟩ :=
        TShape.LE.forallE_decomp hΔ hle hwPi hwf (TEvaluates.refl hwf.2.2.2.1)
      exact TyEq.trans hdom hPi.1

/-- `Term.Pinned`'s `app` condition, from the function's own typing: the
λ-shape's label is the Π's domain, and the argument is typed there. -/
theorem PinApp.of_sound {Γ : List Term} {A B f a : Term}
    (hf : SoundTy Γ f (.forallE A B)) (ha : Γ ⊢ a : A) : PinApp Γ f a := by
  intro Δ Γ₀ σ ρ n A' g hΔ W hAdm hF
  exact Stable.of_typed ha (Interp.lam_label_ty hΔ W hAdm hf hF)

/-- **Saturation at an application.**  The function's own saturation
gives a λ-approximant whose entries' *outputs* are hereditarily typed at
the codomain read there — `Dom`'s second Π condition, and the reason it
is there — so the lookup's value is below one that is, the `lower` rule
being why this is up to the order and the `join` rule why the codes have
to join (`SoundJoin`, `dir_inst`). -/
theorem sound_app_dom {Γ : List Term} {A B f a : Term} {u v : Bool}
    (hPB : B.Pinned (A :: Γ))
    (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) (ha : Γ ⊢ a : A) (hadom : SoundDom Γ a A)
    (hfty : SoundTy Γ f (.forallE A B)) (hfdom : SoundDom Γ f (.forallE A B))
    (hBaty : SoundTy Γ (B.inst a) (.sort v)) (hBad : SoundDom Γ (B.inst a) (.sort v))
    (hadir : SoundDir Γ a) (hBdir : SoundDir (A :: Γ) B) :
    SoundDom Γ (.app f a) (B.inst a) := by
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  have hwρ := hAdm.wf
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  have haσ : Δ ⊢ a.subst σ : A.subst σ := ha.subst hΔ W
  cases hm with
  | bot => exact ⟨TShape.bot, TShape.bot, .bot, TShape.bot_le' rfl, .bot, (.of_dom (TShape.NamedO.bot (.bot (.bot .sort))) (TShape.ValCanon.of_bot rfl)), TShape.CodeCanonS.bot⟩
  | @app _ _ _ _ _ _ n g x y A₁ hF hx hev hw hle hst =>
    -- saturate the function
    obtain ⟨F', P, hF', hFle, hP, hNV, hPc⟩ := hfdom hΔ W hAdm hF
    have hFdom := hNV.dom
    have hF'c := hNV.val
    -- its code is a Π-shape: `F'` dominates a λ-shape, so neither is `⊥`
    have hPpi : P.IsPi := by
      rcases (show P.2 = Shape.bot ∨ P.IsPi from by
          cases hP with
          | bot => exact .inl rfl
          | forallE _ _ _ _ _ _ hlep _ _ => exact TShape.isPi_or_bot_of_le hlep trivial)
        with hb | h
      · exact absurd (TShape.le_bot hΔ (TShape.HasType.bot_r hΔ hb hFdom.hasType) hFle)
          (by simp [Shape.bot])
      · exact h
    cases hFdom with
    | base hnb _ => exact absurd hPpi.isBinder hnb
    | sg _ _ _ _ _ => exact absurd trivial hPpi.not_sigma
    | @pi _ nP A' B' dP fP _ cs hty hent hin hevc hout =>
      -- the saturated function is a λ-shape, and the code's codomain
      -- graph is covered by the canonical one
      cases hty with
      | bot hb =>
        exact absurd (TShape.le_bot hΔ rfl hFle) (by simp [Shape.bot])
      | refl hleid hAty' =>
        exact absurd hleid (by
          intro h
          obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ h
          exact absurd h2 (fun x => x))
      | @lam nF _ _ A'' G _ _ _ _ G₀ hd hfo hwG hwPi hwG₀ hgG hG₀ev hG₀ty hlabG =>
        cases hP with
        | @forallE _ _ _ _ nc gc dc _ _ hAint hdty hwfc _ hbodyc hwmc hlePi =>
          obtain ⟨hPiLab, _, hcovc⟩ :=
            TShape.LE.forallE_decomp hΔ hlePi hwPi hwfc (TEvaluates.refl hwfc.2.2.2.1)
          -- the λ-shape's label is the domain
          have hA₁ : TyEq Δ A₁ (A.subst σ) :=
            Interp.lam_label_ty hΔ W hAdm hfty hF
          -- a lookup in the code's codomain graph, at the canonical query,
          -- is an approximant of `B[a]`
          have toI : ∀ {c : TShape},
              TEvaluates Δ fP (A.subst σ) (a.subst σ) x c →
              Interp Δ Γ (B.inst a) σ ρ c := by
            intro c hc
            refine (Interp.inst (A := A) (b := B) hΔ hΓ hA ha hB hPB W hAdm
              (Subst.Saturates.one hΔ hΓ W hAdm hadom)
              (hadir hΔ W hwρ) hwρ).2 ⟨x, ?_, hx⟩
            rw [Subst.one_comp]
            exact sound_graph_lookup hΓA hA hB hΔ W hbodyc hx.wf hBdir hwρ haσ
              (TyEq.refl hAσ) (TEvaluates.trans hΔ (fun e he => (hcovc e he).retype hPiLab.1) hc)
          -- the λ-shape's own lookup is covered by the saturated one
          have hcovG : ∀ e ∈ g, TEvaluates Δ G A₁ e.tm e.inp.T e.out.T :=
            TShape.LE.lam_decomp hΔ hFle hF.wf hwG (TEvaluates.refl hwG.2.2.1)
          have hevG : TEvaluates Δ G A₁ (a.subst σ) x y :=
            TEvaluates.trans hΔ hcovG hev
          -- every value of that lookup is below one that is hereditarily
          -- typed, and still a value of it
          have hwout : ∀ e ∈ G, TShape.WF Δ e.out.T := fun e he =>
            TShape.WF.T.2 (hwG.2.2.1.1 e he).2.2.2
          -- the code's labels are the type's, by the order
          have hfσ : Δ ⊢ f.subst σ : (Term.forallE A B).subst σ := hfty.typed.subst hΔ W
          have hA'ty : Δ ⊢ A' : .sort hwPi.1.choose := hwPi.1.choose_spec
          have key : ∀ {w : TShape}, TEvaluates Δ G A₁ (a.subst σ) x w →
              ∃ w' c, TEvaluates Δ G A₁ (a.subst σ) x w' ∧ TShape.LE Δ w w' ∧
                Interp Δ Γ (B.inst a) σ ρ c ∧ TShape.NamedO Δ none c w' ∧
                TShape.ValCanon Δ ((Term.app f a).subst σ) w' := by
            intro w hw'
            induction hw' with
            | bot =>
              exact ⟨TShape.bot, TShape.bot, .bot, TShape.LE.refl trivial, .bot,
                TShape.NamedO.bot (.bot (.bot .sort)), TShape.ValCanon.of_bot rfl⟩
            | @entry q hq hlabq hinq =>
              -- the entry's output is `Dom` at its code, which is an
              -- approximant of `B[a]` once moved to the canonical query
              obtain ⟨pc, hpc, hpceq⟩ : ∃ pc ∈ cs,
                  pc.1 = ⟨q.tm, q.inp.T, q.out.T⟩ := by
                have : (⟨q.tm, q.inp.T, q.out.T⟩ : Entry TShape) ∈
                    (Shape.T (n := nF+1) (ShapeS.lam A'' G)).entries :=
                  List.mem_map_of_mem
                    (f := fun e => (⟨e.tm, e.inp.T, e.out.T⟩ : Entry TShape)) hq
                rw [hent, List.mem_map] at this
                obtain ⟨pc, hpc, heq⟩ := this
                exact ⟨pc, hpc, heq⟩
              have hcode := hevc pc hpc
              have hdomq := hout pc hpc
              rw [hpceq] at hcode hdomq
              have hqA' : TyEq Δ A₁ A' := hA₁.trans (TyEq.symm hPiLab.1)
              refine ⟨q.out.T, pc.2, .entry q hq hlabq hinq, TShape.LE.refl
                (TShape.WF.T.2 (hwG.2.2.1.1 q hq).2.2.2), ?_, hdomq, ?_⟩
              · refine toI (TEvaluates.mono hΔ ?_ hinq hcode)
                exact ⟨hPiLab.1, hqA'.choose_spec.defeqDF hlabq.2⟩
              · -- the entry's output names `app f q.tm`, which the label
                -- equation moves to `app f a`, through the entry's own code
                have hwq := (hwG.2.2.1.1 q hq)
                have hqtm : Δ ⊢ q.tm : A' := hlabG.choose_spec.defeqDF hwq.2.1
                have hcc : TShape.CodeCanonS Δ (B'.inst q.tm) pc.2 :=
                  TShape.CodeCanonS.lookup hΔ hwPi.2.2.2.1 (ShapeFun.WF.canon hwPi.2.2.2.1) hA'ty hwPi.2.1.choose_spec
                    hcode
                have hcc' : TShape.CodeCanonS Δ ((B.subst σ.lift).inst q.tm) pc.2 :=
                  hcc.conv (TyEq.inst hΔ hA'ty hPiLab.2.choose_spec
                    (hqtm.symm.trans hqtm)).symm
                have hqa : Δ ⊢ q.tm ≡ a.subst σ : A.subst σ :=
                  hA₁.choose_spec.defeqDF hlabq.2
                have happ := IsDefEq.appDF₀ hΔ hfσ hqa
                exact TShape.ValCanon.defeq hΔ hdomq hcc' (hF'c q hq).2 happ
            | lower hle' _ ih =>
              obtain ⟨w', c, hw'', hlew, hIc, hdc, hwc⟩ := ih
              exact ⟨w', c, hw'', TShape.LE.trans hΔ hle' hlew, hIc, hdc, hwc⟩
            | @join w₁ w₂ hcj hv₁ hv₂ ih₁ ih₂ =>
              obtain ⟨w₁', c₁, hv₁', hle₁, hI₁, hd₁, hc₁⟩ := ih₁
              obtain ⟨w₂', c₂, hv₂', hle₂, hI₂, hd₂, hc₂⟩ := ih₂
              -- the two values join, being lookups in one coherent graph
              have hcw : TShape.Compat Δ w₁' w₂' :=
                TEvaluates.compat hΔ (hwG.2.2.1.2.retype (TyEq.symm (TShape.LE.lam_dom hFle)))
                  hx.wf hv₁' hv₂'
              -- and so do their codes, inside `B[a]`'s extension
              obtain ⟨c, hwc, hIc, hlc₁, hlc₂⟩ :=
                dir_inst (b := B) hA ha hB hPB hΔ W hAdm hΓ hadom
                  hadir hBdir hI₁ hI₂
              have hcty := hBaty.isType hΔ W hAdm hIc
              refine ⟨w₁'.join w₂', c, .join hcw hv₁' hv₂',
                TShape.join_le hΔ (TShape.LE.trans hΔ hle₁
                  (TShape.le_join hΔ (TEvaluates.wf hΔ hwout hv₁')
                    (TEvaluates.wf hΔ hwout hv₂') hcw).1) ?_, hIc, ?_, ?_⟩
              · exact TShape.LE.trans hΔ hle₂
                  (TShape.le_join hΔ (TEvaluates.wf hΔ hwout hv₁')
                    (TEvaluates.wf hΔ hwout hv₂') hcw).2
              · exact TShape.NamedO.join hΔ hcw (TShape.NamedO.mono_r hΔ hd₁ hlc₁ hcty)
                  (TShape.NamedO.mono_r hΔ hd₂ hlc₂ hcty)
              · exact TShape.ValCanon.join hΔ (TEvaluates.wf hΔ hwout hv₁')
                  (TEvaluates.wf hΔ hwout hv₂') hcw hc₁ hc₂
          obtain ⟨y', c, hy', hyle, hIc, hdc, hyc⟩ := key hevG
          -- the saturated function's own label, which the clause reads at
          have hA'' : TyEq Δ A₁ A'' :=
            hA₁.trans (Interp.lam_label_ty hΔ W hAdm hfty hF').symm
          have hwy' := TEvaluates.wf hΔ hwout hy'
          exact ⟨y', c,
            .app hF' hx
              (TEvaluates.label ⟨hA'', hA₁.symm.choose_spec.defeqDF haσ⟩ hy') hwy'
              (TShape.LE.refl hwy') (hst.retype hA''),
            TShape.LE.trans hΔ hle hyle, hIc, .of_dom hdc hyc,
            hBad.codeAt hΔ W hAdm hIc⟩

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
  | app hF hx hev hw hle hty =>
    have hA₁ := Interp.lam_label_ty hΔ W hAdm hfty hF
    refine .app ((ihf hΔ W hAdm).1 hF) ((iha hΔ W hAdm).1 hx) ?_ hw hle
      (Stable.of_typed haa'.hasType.2 hA₁)
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

/-- The Σ analogue of `Interp.lam_label_ty`: a typed approximant of a
Σ-typed term is labelled by the syntactic domain. -/
theorem Interp.pair_label_ty {Γ Γ₀ Δ : List Term} {p A B : Term} {σ ρ}
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    (hty : SoundTy Γ p (.sigma A B))
    {n} {A₀ a₀ : Term} {x y : Shape n}
    (hp : Interp Δ Γ p σ ρ (Shape.T (n := n+1) (ShapeS.pair A₀ a₀ x y))) :
    TyEq Δ A₀ (A.subst σ) := by
  obtain ⟨s, hs, hsty⟩ := hty.approx hΔ W hAdm hp
  cases hsty with
  | pair _ _ _ hwSg _ _ _ _ hdom =>
    cases hs with
    | sigma _ _ hwf _ _ _ hle =>
      obtain ⟨hSg, _, _⟩ :=
        TShape.LE.sigma_decomp hΔ hle hwSg hwf (TEvaluates.refl hwf.2.2.2.1)
      exact hdom.trans hSg.1

/-- **Saturation at a second projection.**  The Σ twin of
`sound_app_dom`: the pair's own saturation pair-approximant
whose entries' outputs are hereditarily typed at the codomain read
there, and the projection is a lookup in that graph. -/
theorem sound_snd_dom {Γ : List Term} {A B p : Term} {u v : Bool}
    (hPB : B.Pinned (A :: Γ))
    (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v)
    (hfst : Γ ⊢ .fst p : A)
    (hfdom : SoundDom Γ (.fst p) A)
    (hpty : SoundTy Γ p (.sigma A B)) (hpdom : SoundDom Γ p (.sigma A B)) (hBfd : SoundDom Γ (B.inst (.fst p)) (.sort v))
    (hfdir : SoundDir Γ (.fst p)) (hBdir : SoundDir (A :: Γ) B) :
    SoundDom Γ (.snd p) (B.inst (.fst p)) := by
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  have hwρ := hAdm.wf
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  have hfσ : Δ ⊢ (Term.fst p).subst σ : A.subst σ := hfst.subst hΔ W
  cases hm with
  | bot => exact ⟨TShape.bot, TShape.bot, .bot, TShape.bot_le' rfl, .bot, (.of_dom (TShape.NamedO.bot (.bot (.bot .sort))) (TShape.ValCanon.of_bot rfl)), TShape.CodeCanonS.bot⟩
  | @snd _ _ _ _ _ n A₀ a₀ x y hp hlab hw hle hst =>
    -- saturate the pair; its second component is the projection's
    obtain ⟨P', S, hP', hPle, hS, hNV, _⟩ := hpdom hΔ W hAdm hp
    have hPdom := hNV.dom
    have hPcan := hNV.val
    have hSsg : S.IsSigma := by
      rcases (show S.2 = Shape.bot ∨ S.IsSigma from by
          cases hS with
          | bot => exact .inl rfl
          | sigma _ _ _ _ _ _ hles _ _ => exact TShape.isSigma_or_bot_of_le hles trivial)
        with hb | h
      · exact absurd (TShape.le_bot hΔ (TShape.HasType.bot_r hΔ hb hPdom.hasType) hPle)
          (by simp [Shape.bot])
      · exact h
    cases hPdom with
    | base hnb _ => exact absurd hSsg.isBinder hnb
    | pi _ _ _ _ => exact absurd hSsg (TShape.IsPi.not_sigma trivial)
    | @sg _ nS A' B' dS fS _ ps cc hty hps _ hxd' hevc hout =>
      cases hty with
      | bot hb => exact absurd (TShape.le_bot hΔ rfl hPle) (by simp [Shape.bot])
      | refl hleid hAty' =>
        exact absurd hleid (by
          intro h
          obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ h
          exact absurd h2 (fun x => x))
      | @pair nP _ A₀' a₀' x' y' _ _ _ _ _ _ hd hfo hwP hwSg hxd hxle' hev' hyty hlabP =>
        cases hS with
        | @sigma _ _ _ _ nc gc dc _ _ hAint hdty hwfc _ hbodyc hwmc hleSg =>
          obtain ⟨hSgLab, _, hcovc⟩ :=
            TShape.LE.sigma_decomp hΔ hleSg hwSg hwfc (TEvaluates.refl hwfc.2.2.2.1)
          -- the saturated pair's first component is an approximant of `fst p`
          have hx'w : TShape.WF Δ (Shape.T x') := TShape.WF.T.2 hwP.2.2.2.1
          have hx'I : Interp Δ Γ (.fst p) σ ρ (Shape.T x') :=
            .fst hP' hx'w (TShape.LE.refl hx'w)
          -- the two names, and the dominator's own equation to `fst p`
          have hA₀ : TyEq Δ A₀ (A.subst σ) := Interp.pair_label_ty hΔ W hAdm hpty hp
          have hA₀' : TyEq Δ A₀' (A.subst σ) := Interp.pair_label_ty hΔ W hAdm hpty hP'
          obtain ⟨hAle, hale, hxle, hyle⟩ := TShape.LE.pair_decomp hΔ hPle
          have hlab' : Δ ⊢ a₀' ≡ (Term.fst p).subst σ : A₀' :=
            hAle.choose_spec.defeqDF (hale.symm.trans hlab)
          -- the code that types the dominator's second component is a
          -- lookup at that name, hence an approximant of `B[fst p]`
          have hcode : TEvaluates Δ fS A' a₀' (Shape.T x') cc := hevc _ (by rw [← hps]; rfl)
          have hdomy : TShape.NamedO Δ none cc (Shape.T y') := by
            simpa using hout _ (show _ ∈ _ by rw [← hps]; rfl)
          have hIc : Interp Δ Γ (B.inst (.fst p)) σ ρ cc := by
            refine (Interp.inst (A := A) (b := B) hΔ hΓ hA hfst hB hPB W hAdm
              (Subst.Saturates.one hΔ hΓ W hAdm hfdom)
              (hfdir hΔ W hwρ) hwρ).2 ⟨Shape.T x', ?_, hx'I⟩
            rw [Subst.one_comp]
            refine sound_graph_lookup hΓA hA hB hΔ W hbodyc hx'w hBdir hwρ
              ((TyEq.symm hSgLab.1).choose_spec.defeqDF hfσ) hSgLab.1 ?_
            refine TEvaluates.label (A := A') (a := a₀')
              ⟨TyEq.refl_l hSgLab.1,
                (TyEq.trans hA₀' (TyEq.symm hSgLab.1)).choose_spec.defeqDF hlab'⟩ ?_
            exact TEvaluates.trans hΔ hcovc hcode
          exact ⟨Shape.T y', cc,
            .snd hP' hlab' (TShape.WF.T.2 hwP.2.2.2.2)
              (TShape.LE.refl (TShape.WF.T.2 hwP.2.2.2.2))
              (hst.retype (hA₀.trans hA₀'.symm)),
            TShape.LE.trans hΔ hle hyle, hIc, (.of_dom (hdomy) (hPcan.2.2)), hBfd.codeAt hΔ W hAdm hIc⟩

/-- The Σ twin: `Term.Pinned`'s `snd` condition, from the pair's typing. -/
theorem PinSnd.of_sound {Γ : List Term} {A B p : Term}
    (hp : SoundTy Γ p (.sigma A B)) (hfst : Γ ⊢ Term.fst p : A) : PinSnd Γ p := by
  intro Δ Γ₀ σ ρ n A' a₀ x y hΔ W hAdm hP
  exact Stable.of_typed hfst (Interp.pair_label_ty hΔ W hAdm hp hP)

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
  | snd hp hlab hw hle hty =>
    have hA₀ := Interp.pair_label_ty hΔ W hAdm hpty hp
    refine .snd ((ihp hΔ W hAdm).1 hp) ?_ hw hle
      (Stable.of_typed (IsDefEq.fstDF hA hB hpp').hasType.2 hA₀)
    -- the name now points at `fst p'`, along `fst p ≡ fst p'`
    exact hlab.trans (hA₀.choose_spec.symm.defeqDF
      ((IsDefEq.fstDF hA hB hpp').subst hΔ W))

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
  ⟨⟨u, hA.subst hΔ W⟩, ha.subst hΔ W, hb.subst hΔ W, trivial⟩

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
      | id hw hle hAt hat hbt =>
        exact .id hw (hle.trans hΔ (TShape.LE.id_of hΔ W hAA' haa' hbb'))
          ⟨u, hAA'.hasType.2⟩ (hAA'.defeqDF haa'.hasType.2) (hAA'.defeqDF hbb'.hasType.2)
    · intro h
      cases h with
      | bot => exact .bot
      | id hw hle hAt hat hbt =>
        exact .id hw (hle.trans hΔ (TShape.LE.id_of hΔ W hAA'' haa'' hbb''))
          ⟨u, hAA'.hasType.1⟩ haa'.hasType.1 hbb'.hasType.1
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
  refine ⟨_, hw, .id hw (TShape.LE.refl hw) ⟨u, hA⟩ ha hb, ?_, ?_⟩
  · cases h₁ with
    | bot => exact TShape.bot_le' rfl
    | id _ hle => exact hle
  · cases h₂ with
    | bot => exact TShape.bot_le' rfl
    | id _ hle => exact hle

/-! ## The two unary formers

`.succ N` wraps its argument's shape, so directedness is its argument's:
the bound is the wrapper applied to the argument's bound, and
`TShape.LE.succ_of` carries the order through.  `.refl a` carries nothing,
so its approximants are `⊥` and the one `refl`-shape. -/

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
    (hid : Γ ⊢ Term.id r A a a : .sort r) :
    SoundEq Γ (.refl r a) (.refl r a') ∧ SoundTy Γ (.refl r a) (.id r A a a) := by
  constructor
  · intro Δ Γ₀ σ ρ hΔ W hAdm m
    constructor
    · intro h
      cases h with
      | bot => exact .bot
      | refl hw hle => exact .refl hw hle
    · intro h
      cases h with
      | bot => exact .bot
      | refl hw hle => exact .refl hw hle
  · refine ⟨.reflDF hA haa'.hasType.1 hid, ?_⟩
    intro Δ Γ₀ σ ρ hΔ W hAdm m hm
    have hwid : TShape.WF Δ
        (Shape.T (n := 1) (ShapeS.id r (A.subst σ) (a.subst σ) (a.subst σ))) :=
      Shape.WF.id_of hΔ W hA haa'.hasType.1 haa'.hasType.1
    have hidty : TShape.HasType Δ
        (Shape.T (n := 1) (ShapeS.id r (A.subst σ) (a.subst σ) (a.subst σ))) TShape.type :=
      .id (Bool.le_true' r) hwid
    refine ⟨_, .id hwid (TShape.LE.refl hwid) ⟨u, hA⟩ haa'.hasType.1 haa'.hasType.1, ?_⟩
    cases hm with
    | bot => exact .bot hidty
    | refl hw hle =>
      exact TShape.HasType.mono_l hΔ (.refl (TShape.LE.refl hwid) hidty) hle

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
  | natCase_zero hM₁ hz₁ ha₁ hMt =>
    cases h₂ with
    | bot => exact ⟨_, ha₁.wf, .natCase_zero hM₁ hz₁ ha₁ hMt, TShape.LE.refl ha₁.wf,
        TShape.bot_le' rfl⟩
    | natCase_zero _ _ ha₂ _ =>
      obtain ⟨s, hws, hs, hs₁, hs₂⟩ := iha hΔ W hwρ ha₁ ha₂
      exact ⟨s, hws, .natCase_zero hM₁ hz₁ hs hMt, hs₁, hs₂⟩
    | natCase_succ hM₂ _ _ _ _ =>
      obtain ⟨_, hwz, _, hz₁, hz₂⟩ := ihM hΔ W hwρ hM₁ hM₂
      exact absurd (TShape.LE.zero_succ_absurd hz₁ hz₂) not_false
  | @natCase_succ _ _ _ _ _ _ _ _ n₁ v₁ t₁ hM₁ hwv₁ heq₁ hbody₁ hMt =>
    cases h₂ with
    | bot => exact ⟨_, hbody₁.wf, .natCase_succ hM₁ hwv₁ heq₁ hbody₁ hMt,
        TShape.LE.refl hbody₁.wf, TShape.bot_le' rfl⟩
    | natCase_zero hM₂ _ _ _ =>
      obtain ⟨_, hwz, _, hz₁, hz₂⟩ := ihM hΔ W hwρ hM₁ hM₂
      exact absurd (TShape.LE.zero_succ_absurd hz₂ hz₁) not_false
    | @natCase_succ _ _ _ _ _ _ _ _ n₂ v₂ t₂ hM₂ hwv₂ heq₂ hbody₂ _ =>
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
      exact ⟨s, hws, .natCase_succ hz hww heq₁ hs hMt, hs₁, hs₂⟩

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
    ∀ {A b : Term}, t = .Y A b → Valuation.WF Δ ρ → Ctx.SubstEq Δ σ σ Γ →
      Ctx.SubstEq Δ (σ.cons ((A.Y b).subst σ)) (σ.cons ((A.Y b).subst σ)) (A :: Γ) →
      SoundDir Γ A → SoundDir (A :: Γ) b → ∀ {m₂}, Interp Δ Γ t σ ρ m₂ →
        ∃ s, TShape.WF Δ s ∧ Interp Δ Γ t σ ρ s ∧ TShape.LE Δ m₁ s ∧ TShape.LE Δ m₂ s := by
  induction h₁ with
  | @Y _ _ _ _ _ _ _ _ hx₁ hwx₁ hA₁ hdty₁ hNVY hcc₁ hbody₁ hAt hYt ihx₁ ihA₁ _ =>
    have hD₁ := hNVY.dom
    have hvc₁ := hNVY.val
    rintro A b ⟨⟩ hwρ WΓ WY ihA ihb m₂ h₂
    cases h₂ with
    | bot =>
      exact ⟨_, hbody₁.wf, .Y hx₁ hwx₁ hA₁ hdty₁ (.of_dom hD₁ hvc₁) hcc₁ hbody₁ hAt hYt,
        TShape.LE.refl hbody₁.wf, TShape.bot_le' rfl⟩
    | @Y _ _ _ _ _ _ x₂ d₂ hx₂ hwx₂ hA₂ hdty₂ hNVY₂ hcc₂ hbody₂ _ _ =>
      have hD₂ := hNVY₂.dom
      have hvc₂ := hNVY₂.val
      -- one tower above both, by the first derivation's own induction
      obtain ⟨z, hwz, hz, hz₁, hz₂⟩ := ihx₁ rfl hwρ WΓ WY ihA ihb hx₂
      -- the slot is their *join*: it is below that bound, so it is an
      -- approximant too, and `Dom` is closed under the join — which the
      -- clause needs, since `Adm` reads the slot hereditarily
      have hcj := TShape.Compat.of_common_upper hΔ hwz hz₁ hz₂
      have hwj := TShape.WF.join hΔ hcj hwx₁ hwx₂
      have hjx := Interp.mono hΔ hwj (TShape.join_le hΔ hz₁ hz₂) hz
      -- and their *codes* join too, by the annotation's own directedness
      obtain ⟨dc, hwdc, hdc, hdc₁, hdc₂⟩ := ihA hΔ WΓ hwρ hA₁ hA₂
      have hcd := TShape.Compat.of_common_upper hΔ hwdc hdc₁ hdc₂
      have hdcty := TShape.HasType.join_sort' hΔ rfl hdty₁ hdty₂ hcd
      have hdcI := Interp.mono hΔ (TShape.WF.join hΔ hcd hdty₁.wf.1 hdty₂.wf.1)
        (TShape.join_le hΔ hdc₁ hdc₂) hdc
      obtain ⟨c₁, c₂⟩ := TShape.le_join hΔ hdty₁.wf.1 hdty₂.wf.1 hcd
      have hjd := TShape.NamedO.join hΔ hcj (TShape.NamedO.mono_r hΔ hD₁ c₁ hdcty)
        (TShape.NamedO.mono_r hΔ hD₂ c₂ hdcty)
      obtain ⟨j₁, j₂⟩ := TShape.le_join hΔ hwx₁ hwx₂ hcj
      obtain ⟨s, hws, hs, hs₁, hs₂⟩ := ihb hΔ WY (Valuation.WF.push hwρ hwj)
        (Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, j₁⟩) hbody₁)
        (Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, j₂⟩) hbody₂)
      -- the slot and the code keep their names through the join
      have hjc := TShape.CodeCanonS.join hΔ    hcc₁ hcc₂
      have hjv := TShape.ValCanon.join hΔ hwx₁ hwx₂ hcj hvc₁ hvc₂
      exact ⟨s, hws, .Y hjx hwj hdcI hdcty (.of_dom hjd hjv) hjc hs hAt hYt, hs₁, hs₂⟩
  | bot =>
    exact fun _ _ _ _ _ _ _ h₂ =>
      ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | _ => intro A b hne; cases hne

theorem dir_Y {Γ : List Term} {A b : Term} {u : Bool} (hA : Γ ⊢ A : .sort u)
    (hY : Γ ⊢ .Y A b : A) (ihA : SoundDir Γ A) (ihb : SoundDir (A :: Γ) b) :
    SoundDir Γ (.Y A b) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  exact dir_Y_aux hΔ h₁ rfl hwρ W (.cons W hA (hY.subst hΔ W)) ihA ihb h₂

/-- Directedness for `.refl`: every `refl`-approximant is below the one
`refl`-shape.  At `r = false` there is no `refl` rule and `cases` leaves
only `bot`. -/
theorem dir_refl {Γ : List Term} {a : Term} {r : Bool} : SoundDir Γ (.refl r a) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  have hwz : TShape.WF Δ (Shape.T (n := 1) ShapeS.refl) := TShape.WF.T.2 trivial
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | refl hw₁ hle₁ =>
    cases h₂ with
    | bot => exact ⟨_, hw₁, .refl hw₁ hle₁, TShape.LE.refl hw₁, TShape.bot_le' rfl⟩
    | refl _ hle₂ =>
      exact ⟨_, hwz, .refl hwz (TShape.LE.refl hwz),
        hle₁.trans hΔ (TShape.LE.refl_of hΔ), hle₂.trans hΔ (TShape.LE.refl_of hΔ)⟩

/-- **Directedness for `.tr`** — the case the plan called open, and the
case `SoundJoin` was meant for.  In the event it goes through
`TShape.HasType.join` directly, which is `SoundJoin`'s own ingredient, so
join-closure of a type's *extension* is never needed.

Everything in the `tr` clause is joined slotwise: the witness shape `v`
(which interprets both endpoints, so it is the *join*, not an upper
bound, taken twice), the type `vA`, the motive's value `cb` at the joined
slot, and the transported shape `m'`.  Three of the clause's premises are
typings, and each is a subject join at one type: `v` at `vA₁ ⊔ vA₂`, `cb`
at `type`, `m'` at `cb₁ ⊔ cb₂` — `TShape.HasType.join`, which is why this
case waited for it.  The proof premise is moved by `H`'s own
directedness: a shape above two `refl`s is a `refl`, above both
witnesses. -/
theorem dir_tr {Γ : List Term} {r : Bool} {A a b C X H : Term} {u : Bool}
    (hA : Γ ⊢ A : .sort u) (hb : Γ ⊢ b : A)
    (ihA : SoundDir Γ A) (iha : SoundDir Γ a) (ihb : SoundDir Γ b)
    (ihC : SoundDir (A :: Γ) C) (ihX : SoundDir Γ X) :
    SoundDir Γ (.tr r A a b C X H) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | tr hw₁ hle₁ hX₁ ha₁ hb₁ hA₁ hwv₁ hNV hvc₁ hC₁ hcb₁ hNV2 hcbc₁ hH₁ heq₁ hAt hat 
      hbt =>
    have hvA₁ := hNV.dom
    have hbc₁ := hNV.val
    have hm'₁ := hNV2.dom
    have hmc₁ := hNV2.val
    cases h₂ with
    | bot =>
      exact ⟨_, hX₁.wf, .tr hX₁.wf (TShape.LE.refl hX₁.wf) hX₁ ha₁ hb₁ hA₁ hwv₁ (.of_dom hvA₁ hbc₁)
        hvc₁ hC₁ hcb₁ (.of_dom hm'₁ hmc₁) hcbc₁ hH₁ heq₁ hAt hat hbt, hle₁, TShape.bot_le' rfl⟩
    | tr hw₂ hle₂ hX₂ ha₂ hb₂ hA₂ hwv₂ hNV hvc₂ hC₂ hcb₂ hNV2 hcbc₂ hH₂ _ _ _ _ =>
      have hvA₂ := hNV.dom
      have hbc₂ := hNV.val
      have hm'₂ := hNV2.dom
      have hmc₂ := hNV2.val
      -- the witness: the join interprets both endpoints
      have ⟨hcv, hav⟩ := Interp.Dir.join hΔ (iha hΔ W hwρ) ha₁ ha₂
      have ⟨_, hbv⟩ := Interp.Dir.join hΔ (ihb hΔ W hwρ) hb₁ hb₂
      have hwv := TShape.WF.join hΔ hcv hwv₁ hwv₂
      have hvle := TShape.le_join hΔ hwv₁ hwv₂ hcv
      -- its type
      have ⟨hcA, hAv⟩ := Interp.Dir.join hΔ (ihA hΔ W hwρ) hA₁ hA₂
      have hvAty := TShape.HasType.join hΔ hcA (TShape.NamedO.of_isType hvA₁.hasType.isType)
        (TShape.NamedO.of_isType hvA₂.hasType.isType)
      have hvAle := TShape.le_join hΔ hvA₁.hasType.isType.wf.1 hvA₂.hasType.isType.wf.1 hcA
      have hty : TShape.NamedO Δ none _ _ := TShape.NamedO.join hΔ hcv
        (TShape.NamedO.mono_r hΔ hvA₁ hvAle.1 hvAty) (TShape.NamedO.mono_r hΔ hvA₂ hvAle.2 hvAty)
      -- the motive, at the joined slot
      have WA : Ctx.SubstEq Δ (σ.cons (b.subst σ)) (σ.cons (b.subst σ)) (A :: Γ) :=
        .cons W hA (hb.subst hΔ W)
      have hC₁' := Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hvle.1⟩) hC₁
      have hC₂' := Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hvle.2⟩) hC₂
      have ⟨hccb, hcbv⟩ :=
        Interp.Dir.join hΔ (ihC hΔ WA (Valuation.WF.push hwρ hwv)) hC₁' hC₂'
      have hcbty := TShape.HasType.join hΔ hccb (TShape.NamedO.of_isType hcb₁)
        (TShape.NamedO.of_isType hcb₂)
      have hcble := TShape.le_join hΔ hcb₁.wf.1 hcb₂.wf.1 hccb
      -- the transported shape
      have ⟨hcm, hXv⟩ := Interp.Dir.join hΔ (ihX hΔ W hwρ) hX₁ hX₂
      have hm'ty := TShape.NamedO.join hΔ hcm
        (TShape.NamedO.mono_r hΔ hm'₁ hcble.1 hcbty) (TShape.NamedO.mono_r hΔ hm'₂ hcble.2 hcbty)
      have hm'le := TShape.le_join hΔ hm'₁.hasType.wf.1 hm'₂.hasType.wf.1 hcm
      -- and the proof premise, by `H`'s own directedness
      have hwm' := TShape.WF.join hΔ hcm hm'₁.hasType.wf.1 hm'₂.hasType.wf.1
      -- the slot and its type keep their names through the joins
      have hvcj := TShape.CodeCanonS.join hΔ 
          hvc₁ hvc₂
      have hbcj := TShape.ValCanon.join hΔ hwv₁ hwv₂ hcv hbc₁ hbc₂
      have hcbcj := TShape.CodeCanonS.join hΔ    hcbc₁ hcbc₂
      have hmcj := TShape.ValCanon.join hΔ hm'₁.hasType.wf.1 hm'₂.hasType.wf.1 hcm hmc₁ hmc₂
      exact ⟨_, hwm', .tr hwm' (TShape.LE.refl hwm')
          hXv hav hbv hAv hwv (.of_dom hty hbcj) hvcj hcbv hcbty (.of_dom hm'ty hmcj) hcbcj hH₁ heq₁ hAt hat hbt,
        hle₁.trans hΔ hm'le.1, hle₂.trans hΔ hm'le.2⟩

/-! ## β

The rule is padded with typings of both sides, so only `SoundEq` has
content (the other repo's `of_typings` observation).

`→` is the graph lookup unfolded: the function's λ-shape is covered by the
rule's own graph, each of whose entries carries the body at the entry's
label and input, and the entry's label is definitionally the argument, so
`IsDefEq.stage` puts the body at the argument's stage and `Interp.inst`
reads it as an approximant of `e[e']`.  The lookup's `join` rule lands on
two of those, which is why `dir_inst` is needed.  No typing of the input the body is evaluated at the entry's own input.

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
    (hPe : e.Pinned (A :: Γ))
    (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u) (hbe : A :: Γ ⊢ e : B) (he' : Γ ⊢ e' : A)
    (ihA : SoundTy Γ A (.sort u)) (ihe'dom : SoundDom Γ e' A)
    (ihe'dir : SoundDir Γ e') (ihedir : SoundDir (A :: Γ) e) :
    SoundEq Γ (.app (.lam A e) e') (e.inst e') := by
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  have hwρ : Valuation.WF Δ ρ := hAdm.wf
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  have he'σ : Δ ⊢ e'.subst σ : A.subst σ := he'.subst hΔ W
  have hinst : ∀ {m : TShape}, Interp Δ Γ (e.inst e') σ ρ m ↔
      ∃ x, Interp Δ (A :: Γ) e ((Subst.one e').comp σ) (ρ.push x) m ∧
        Interp Δ Γ e' σ ρ x := fun {_} =>
    Interp.inst hΔ hΓ hA he' hbe hPe W hAdm
      (Subst.Saturates.one hΔ hΓ W hAdm ihe'dom) (ihe'dir hΔ W hwρ) hwρ
  have hdir := dir_inst (b := e) hA he' hbe hPe hΔ W hAdm hΓ ihe'dom
    ihe'dir ihedir
  constructor
  · intro h
    cases h with
    | bot => exact .bot
    | app hF hx hev hw hle =>
      cases hF with
      | lam hAint hd hwf _ hbody hwlam hlelam _ =>
        -- the function's λ-shape is covered by the rule's own graph, and
        -- the order makes its label the domain, so the lookup moves there
        have hev' := (TEvaluates.trans hΔ
          (TShape.LE.lam_decomp hΔ hlelam hwlam hwf (TEvaluates.refl hwf.2.2.1)) hev).retype
          (TShape.LE.lam_dom hlelam)
        exact (sound_beta_lookup hΓA hA hbe hΔ W hwf hbody hx hdir hinst hev').mono hΔ hw hle
  · intro h
    obtain ⟨n, s⟩ := m
    by_cases hb : s.IsBot
    · rw [Shape.WF.eq_bot_of_isBot (s := s) h.wf hb]; exact .bot
    · obtain ⟨x₀, hbody₀, hx₀⟩ := hinst.1 h
      -- the argument's approximant, enlarged until hereditarily typed:
      -- that is what the λ-clause's slot asks of it
      obtain ⟨x, d, hx, hlex, hd, hNV, _⟩ := ihe'dom hΔ W hAdm hx₀
      have hxd := hNV.dom
      have hxc := hNV.val
      have hbody : Interp Δ (A :: Γ) e ((Subst.one e').comp σ) (ρ.push x) ⟨n, s⟩ :=
        Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hlex⟩) hbody₀
      -- one entry, at a level above both the argument's shape and the value
      obtain ⟨k, hkx, hkn⟩ : ∃ k, x.1 ≤ k ∧ n ≤ k :=
        ⟨max x.1 n, Nat.le_max_left .., Nat.le_max_right ..⟩
      have hwx : Shape.WF Δ (x.2.lift k) := (Shape.lift_wf hkx).2 hx.wf
      have hws : Shape.WF Δ (s.lift k) := (Shape.lift_wf hkn).2 h.wf
      have hnb : ¬ (s.lift k).IsBot := fun hbb => hb ((Shape.lift_isBot hkn).1 hbb)
      have hwg : Shape.WF (n := k+1) Δ (.lam (A.subst σ)
          [⟨e'.subst σ, x.2.lift k, s.lift k⟩]) := by
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
        · exact TyEq.refl hAσ
      have hlam : Interp Δ Γ (.lam A e) σ ρ (Shape.T (n := k+1)
          (.lam (A.subst σ)
            [⟨e'.subst σ, x.2.lift k, s.lift k⟩])) := by
        refine .lam hd (ihA.isType hΔ W hAdm hd) hwg ?_ ?_ hwg (TShape.LE.refl hwg) ⟨u, hA⟩
        · intro e₀ he₀
          cases he₀ with
          | head =>
            exact .of_dom (TShape.NamedO.lift_subject hΔ hxd hkx)
              ((Shape.ValCanon.lift hΔ hkx).2 hxc)
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
        (.entry ⟨e'.subst σ, x.2.lift k, s.lift k⟩ (.head _)
          (LabelEq.refl hAσ he'σ) (TShape.LE.refl hwx)) h.wf
        (TShape.LE.le_lift (m := ⟨n, s⟩) hΔ hkn h.wf)
        (Stable.of_typed he' (TyEq.refl hAσ))

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
    | natCase_zero _ _ ha _ => exact ha
    | natCase_succ hM _ _ _ _ =>
      cases hM with
      | zero _ hle => exact absurd (TShape.LE.succ_zero_absurd hle) not_false
  · have hz : TShape.WF Δ TShape.zero := trivial
    exact .natCase_zero (.zero hz (TShape.LE.refl hz)) .zero h .zero

/-- `natCase C (succ n) a b` and `b[n]`. -/
theorem sound_natCase_succ {Γ : List Term} {C a b n : Term}
    (hPb : b.Pinned (Term.nat :: Γ))
    (hΓ : ⊢ Γ) (hn : Γ ⊢ n : .nat) (hb : Term.nat :: Γ ⊢ b : B) (ihndom : SoundDom Γ n .nat) (ihndir : SoundDir Γ n) : SoundEq Γ (.natCase C (.succ n) a b) (b.inst n) := by
  have hΓN : ⊢ (Term.nat :: Γ) := ⟨hΓ, _, .nat⟩
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  have hwρ : Valuation.WF Δ ρ := hAdm.wf
  have hnσ : Δ ⊢ n.subst σ : Term.nat := hn.subst hΔ W
  have hinst : ∀ {m : TShape}, Interp Δ Γ (b.inst n) σ ρ m ↔
      ∃ x, Interp Δ (Term.nat :: Γ) b ((Subst.one n).comp σ) (ρ.push x) m ∧
        Interp Δ Γ n σ ρ x := fun {_} =>
    Interp.inst hΔ hΓ .nat hn hb hPb W hAdm
      (Subst.Saturates.one hΔ hΓ W hAdm ihndom) (ihndir hΔ W hwρ) hwρ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h with
    | bot => exact .bot
    | natCase_zero hM _ _ _ =>
      cases hM with
      | succ _ _ hle => exact absurd (TShape.LE.zero_succ_absurd' hle) not_false
    | natCase_succ hM hwv heq hbody _ =>
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
      hx.wf (.succDF hnσ) ?_ (.succDF hn)
    rw [← Subst.one_comp]; exact hbody

/-- `Y A b` and its unfolding `b[Y A b]`: the fixed point's rule *is* the
instantiation, so both directions are `Interp.inst` at the tower below. -/
theorem sound_Y_unfold {Γ : List Term} {A b : Term} {u : Bool} (hΓ : ⊢ Γ)
    (hPb : b.Pinned (A :: Γ))
    (hA : Γ ⊢ A : .sort u) (hb : A :: Γ ⊢ b : A.lift)
    (hY : Γ ⊢ .Y A b : A) (ihAty : SoundTy Γ A (.sort u)) (ihYdom : SoundDom Γ (.Y A b) A)
    (ihYdir : SoundDir Γ (.Y A b)) :
    SoundEq Γ (.Y A b) (b.inst (.Y A b)) := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  have hwρ : Valuation.WF Δ ρ := hAdm.wf
  have hinst : ∀ {m : TShape}, Interp Δ Γ (b.inst (.Y A b)) σ ρ m ↔
      ∃ x, Interp Δ (A :: Γ) b ((Subst.one (.Y A b)).comp σ) (ρ.push x) m ∧
        Interp Δ Γ (.Y A b) σ ρ x := fun {_} =>
    Interp.inst hΔ hΓ hA hY hb hPb W hAdm
      (Subst.Saturates.one hΔ hΓ W hAdm ihYdom)
      (ihYdir hΔ W hwρ) hwρ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h with
    | Y hx hwx hA' hdty _ _ hbody hAt hYt =>
      refine hinst.2 ⟨_, ?_, hx⟩
      rw [Subst.one_comp]; exact hbody
    | bot => exact .bot
  · obtain ⟨x₀, hbody₀, hx₀⟩ := hinst.1 h
    -- the tower's slot is enlarged until hereditarily typed
    obtain ⟨x, d, hx, hlex, hd, hNV, hdc⟩ := ihYdom hΔ W hAdm hx₀
    have hxd := hNV.dom
    have hxc := hNV.val
    refine .Y hx hx.wf hd (ihAty.isType hΔ W hAdm hd) (.of_dom hxd hxc) hdc ?_ ⟨u, hA⟩ hY
    rw [← Subst.one_comp]
    exact Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hlex⟩) hbody₀

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
  | natCase_zero hM hz ha hMt =>
    exact .natCase_zero ((ihM hΔ W hAdm).1 hM) (((hMM'.subst hΔ W).symm).trans hz)
      ((iha hΔ W hAdm).1 ha) hMM'.hasType.2
  | @natCase_succ _ _ _ _ _ _ _ _ n v t hM hwv heq hbody hMt =>
    -- the label term is a numeral's argument, so it is typed
    have ht : Δ ⊢ t : Term.nat := heq.succ_regular (.inr rfl)
    -- and the slot is typed at `nat`, because `M`'s shape is
    obtain ⟨c, hc, hty⟩ := ihMty.approx hΔ W hAdm hM
    have hvnat : TShape.HasType Δ v.T TShape.nat :=
      (TShape.HasType.isNumeral hΔ (Interp.le_nat hc) hty).pred.hasType
    have Wcons : Ctx.SubstEq Δ (σ.cons t) (σ.cons t) (Term.nat :: Γ) := .cons W .nat ht
    have hAdm' : Adm Δ Γ₀ (Term.nat :: Γ) (σ.cons t) (ρ.push v.T) :=
      .cons hAdm W.wf
        Interp.nat' (TShape.WF.T.2 hwv) (.of_dom (TShape.NamedO.of_not_binder (fun h => h) hvnat)
          (TShape.ValCanon.of_nat hΔ hvnat))
        (TyEq.refl .nat)
    exact .natCase_succ ((ihM hΔ W hAdm).1 hM) hwv
      (((hMM'.subst hΔ W).symm).trans heq)
      ((ihb hΔ Wcons hAdm').1 hbody) hMM'.hasType.2

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

/-- A `natCase` computes at a stage where its scrutinee is `zero`: the
congruence moves the scrutinee, and `natCase_zero` fires. -/
theorem IsDefEq.natCase_zero_stage {Γ Δ : List Term} {C M a b : Term} {v : Bool} {σ : Subst}
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hC : Term.nat :: Γ ⊢ C : .sort v)
    (ha : Γ ⊢ a : C.inst .zero)
    (hb : Term.nat :: Γ ⊢ b : (C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0)))
    (hz : Δ ⊢ M.subst σ ≡ .zero : .nat) :
    Δ ⊢ (Term.natCase C M a b).subst σ ≡ a.subst σ : (C.inst M).subst σ := by
  have hΔN : ⊢ (Term.nat :: Δ) := ⟨hΔ, _, .nat⟩
  have WN : Ctx.SubstEq (Term.nat :: Δ) σ.lift σ.lift (Term.nat :: Γ) := W.lift .nat .nat
  have hC1 : Term.nat :: Δ ⊢ C.subst σ.lift : .sort v := hC.subst hΔN WN
  have ha1 : Δ ⊢ a.subst σ : (C.subst σ.lift).inst .zero := by
    have h := ha.subst hΔ W; rwa [subst_inst] at h
  have hb1 := hb.subst hΔN WN
  rw [subst_succ_branch_swap] at hb1
  have h1 := hC1.natCaseDF₀ hΔ hz ha1 hb1
  have h2 := IsDefEq.natCase_zero₀ hΔ hC1 ha1 hb1
  rw [subst_inst]
  exact h1.trans ((IsDefEq.instDF hΔ .nat .sort hC1 hz.symm).defeqDF h2)

/-- And where it is a successor, `natCase_succ`. -/
theorem IsDefEq.natCase_succ_stage {Γ Δ : List Term} {C M a b t : Term} {v : Bool} {σ : Subst}
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hC : Term.nat :: Γ ⊢ C : .sort v)
    (ha : Γ ⊢ a : C.inst .zero)
    (hb : Term.nat :: Γ ⊢ b : (C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0)))
    (hs : Δ ⊢ M.subst σ ≡ .succ t : .nat) :
    Δ ⊢ (Term.natCase C M a b).subst σ ≡ b.subst (σ.cons t) : (C.inst M).subst σ := by
  have hΔN : ⊢ (Term.nat :: Δ) := ⟨hΔ, _, .nat⟩
  have WN : Ctx.SubstEq (Term.nat :: Δ) σ.lift σ.lift (Term.nat :: Γ) := W.lift .nat .nat
  have hC1 : Term.nat :: Δ ⊢ C.subst σ.lift : .sort v := hC.subst hΔN WN
  have ha1 : Δ ⊢ a.subst σ : (C.subst σ.lift).inst .zero := by
    have h := ha.subst hΔ W; rwa [subst_inst] at h
  have hb1 := hb.subst hΔN WN
  rw [subst_succ_branch_swap] at hb1
  have ht : Δ ⊢ t : .nat := hs.succ_regular (.inr rfl)
  have h1 := hC1.natCaseDF₀ hΔ hs ha1 hb1
  have h2 := IsDefEq.natCase_succ₀ hΔ hC1 ht ha1 hb1
  rw [inst_lift_cons] at h2
  rw [subst_inst]
  exact h1.trans ((IsDefEq.instDF hΔ .nat .sort hC1 hs.symm).defeqDF h2)

/-- **Saturation at a `natCase`.**  A `natCase`'s approximant is its
branch's, so the branch's own saturation is the whole content; the code
moves from the branch's type to `C[M]` because `M[σ]` is the branch's
index at the stage. -/
theorem sound_natCase_dom {Γ : List Term} {C M a b : Term} {v : Bool} (hΓ : ⊢ Γ)
    (hPC : C.Pinned (Term.nat :: Γ))
    (hC : Term.nat :: Γ ⊢ C : .sort v)
    (hat : Γ ⊢ a : C.inst .zero)
    (hbt : Term.nat :: Γ ⊢ b : (C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0)))
    (hCMd : SoundDom Γ (C.inst M) (.sort v))
    (ihadom : SoundDom Γ a (C.inst .zero))
    (ihbdom : SoundDom (Term.nat :: Γ) b
      ((C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0))))
    (ihMty : SoundTy Γ M Term.nat) (ihMdom : SoundDom Γ M Term.nat)
    (ihMdir : SoundDir Γ M) :
    SoundDom Γ (.natCase C M a b) (C.inst M) := by
  have hΓN : ⊢ (Term.nat :: Γ) := ⟨hΓ, _, .nat⟩
  have hzdir : SoundDir Γ (Term.zero) :=
    dir_atom Interp.le_zero (fun hw h => .zero hw h) trivial
  have hClift : Term.nat :: Term.nat :: Γ ⊢ C.lift' (.cons (.skip .refl)) : .sort v :=
    IsDefEq.weak' (.cons (.skip .refl)) hC
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  have hwρ := hAdm.wf
  cases hm with
  | bot => exact ⟨TShape.bot, TShape.bot, .bot, TShape.bot_le' rfl, .bot, (.of_dom (TShape.NamedO.bot (.bot (.bot .sort))) (TShape.ValCanon.of_bot rfl)), TShape.CodeCanonS.bot⟩
  | natCase_zero hMz hz hma hMt =>
    obtain ⟨ma, c, hma', hmle, hc, hNV, _⟩ := ihadom hΔ W hAdm hma
    have hdc := hNV.dom
    have hmac := hNV.val
    obtain ⟨x, hCx, hxz⟩ :=
      (Interp.inst (A := Term.nat) (b := C) hΔ hΓ .nat .zero hC hPC W hAdm
        (Subst.Saturates.one hΔ hΓ W hAdm (SoundDom.nat TypedAt.zero))
        (hzdir hΔ W hwρ) hwρ).1 hc
    rw [Subst.one_comp] at hCx
    have W0 : Ctx.SubstEq Δ (σ.cons (Term.zero.subst σ)) (σ.cons (M.subst σ))
        (Term.nat :: Γ) := .cons W .nat hz.symm
    have hIc : Interp Δ Γ (C.inst M) σ ρ c :=
      (Interp.inst (A := Term.nat) (b := C) hΔ hΓ .nat hMt hC hPC W hAdm
        (Subst.Saturates.one hΔ hΓ W hAdm ihMdom)
        (ihMdir hΔ W hwρ) hwρ).2
        ⟨x, by rw [Subst.one_comp]; exact IsDefEq.stage hΓN hC hΔ W0 hCx,
          Interp.mono hΔ hxz.wf (Interp.le_zero hxz) hMz⟩
    have hcc := hCMd.codeAt hΔ W hAdm hIc
    exact ⟨ma, c, .natCase_zero hMz hz hma' hMt, hmle, hIc,
      .of_dom hdc (TShape.ValCanon.defeq hΔ hdc hcc hmac
        (IsDefEq.natCase_zero_stage hΔ W hC hat hbt hz).symm), hcc⟩
  | @natCase_succ _ _ _ _ _ _ _ _ n w t hMs hwv heq hmb hMt =>
    have ht : Δ ⊢ t : Term.nat := heq.succ_regular (.inr rfl)
    have Wcons : Ctx.SubstEq Δ (σ.cons t) (σ.cons t) (Term.nat :: Γ) := .cons W .nat ht
    obtain ⟨cM, hcM, htyM⟩ := ihMty.approx hΔ W hAdm hMs
    have hvnat : TShape.HasType Δ w.T TShape.nat :=
      (TShape.HasType.isNumeral hΔ (Interp.le_nat hcM) htyM).pred.hasType
    have hwv' : TShape.WF Δ w.T := TShape.WF.T.2 hwv
    have hAdm' : Adm Δ Γ₀ (Term.nat :: Γ) (σ.cons t) (ρ.push w.T) :=
      .cons hAdm W.wf
        Interp.nat' hwv' (.of_dom (TShape.NamedO.of_not_binder (fun h => h) hvnat)
          (TShape.ValCanon.of_nat hΔ hvnat))
        (TyEq.refl .nat)
    obtain ⟨mb, c, hmb', hmle, hc, hNV, _⟩ := ihbdom hΔ Wcons hAdm' hmb
    have hdc := hNV.dom
    have hmbc := hNV.val
    obtain ⟨y, hCy, hsy⟩ := (Interp.inst (A := Term.nat) (b := C.lift' (.cons (.skip .refl)))
      hΔ hΓN .nat (.succDF (.bvar .zero .nat)) hClift
      (Term.Pinned.weak' hΓN hC.annot.1 (.cons (.skip .refl)) hPC) Wcons hAdm'
      (Subst.Saturates.one hΔ hΓN Wcons hAdm' (SoundDom.nat TypedAt.succ_bvar0))
      (dir_succ (dir_bvar (Γ := Term.nat :: Γ)) hΔ Wcons (Valuation.WF.push hwρ hwv'))
      (Valuation.WF.push hwρ hwv')).1 hc
    rw [Subst.one_comp] at hCy
    have hCy' : Interp Δ (Term.nat :: Γ) C (σ.cons ((Term.succ (.bvar 0)).subst (σ.cons t)))
        (ρ.push y) c := by
      have h := Interp.unweak (Δ := Δ) hΔ hΓN hC.annot.1 (Γ' := Term.nat :: Term.nat :: Γ)
        (l := .cons (.skip .refl)) (ρ := ρ.push y)
        (.cons (.skip .refl))
        (show Ctx.SubstEq Δ ((σ.cons t).cons ((Term.succ (.bvar 0)).subst (σ.cons t)))
            ((σ.cons t).cons ((Term.succ (.bvar 0)).subst (σ.cons t)))
            (Term.nat :: Term.nat :: Γ) from
          .cons Wcons .nat
            (by simpa using IsDefEq.subst hΔ Wcons (IsDefEq.succDF (.bvar .zero .nat))))
        (fun i => by cases i <;> rfl) hCy
      rwa [← Subst.lift_l_cons, ← Subst.tail_eq_lift_l] at h
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
    have hIc : Interp Δ Γ (C.inst M) σ ρ c :=
      (Interp.inst (A := Term.nat) (b := C) hΔ hΓ .nat hMt hC hPC W hAdm
        (Subst.Saturates.one hΔ hΓ W hAdm ihMdom)
        (ihMdir hΔ W hwρ) hwρ).2
        ⟨y, by rw [Subst.one_comp]; exact IsDefEq.stage hΓN hC hΔ W1 hCy',
          Interp.mono hΔ hsy.wf hyle hMs⟩
    have hcc := hCMd.codeAt hΔ W hAdm hIc
    exact ⟨mb, c, .natCase_succ hMs hwv heq hmb' hMt, hmle, hIc,
      .of_dom hdc (TShape.ValCanon.defeq hΔ hdc hcc hmbc
        (IsDefEq.natCase_succ_stage hΔ W hC hat hbt heq).symm), hcc⟩

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
    ∀ {A b : Term} {u : Bool}, t = .Y A b → ⊢ Γ →
      Γ ⊢ A : .sort u → Γ ⊢ .Y A b : A →
      Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ₀ Γ σ ρ →
      SoundTy Γ A (.sort u) → SoundTy (A :: Γ) b A.lift →
      ∃ c, Interp Δ Γ A σ ρ c ∧ TShape.HasType Δ m c := by
  induction H with
  | @Y Γ' σ' ρ' m' A b x d hx hwx hd hdty hNV hdcY hbody hAt hYt ihx _ _ =>
    have hDom := hNV.dom
    have hxcY := hNV.val
    rintro A' b' u ⟨⟩ hΓ hA hY W hAdm ihA ihb
    have WY : Ctx.SubstEq Δ (σ'.cons ((Term.Y A b).subst σ'))
        (σ'.cons ((Term.Y A b).subst σ')) (A :: Γ') := .cons W hA (hY.subst hΔ W)
    have hAdm' : Adm Δ Γ₀ (A :: Γ') (σ'.cons ((Term.Y A b).subst σ')) (ρ'.push _) :=
      .cons hAdm W.wf hd hwx (.of_dom hDom hxcY) hdcY
    obtain ⟨c, hc, hct⟩ := ihb.approx hΔ WY hAdm' hbody
    exact ⟨c, Interp.unweak (Δ := Δ) hΔ hΓ hA.annot.1 (Γ' := A :: Γ') (l := .skip .refl)
      (.skip .refl) WY (fun i => rfl) hc, hct⟩
  | bot => exact fun _ _ _ _ _ _ _ _ => ⟨TShape.bot, .bot, .bot (.bot .sort)⟩
  | _ => intro A b u hne; cases hne

theorem sound_Y_ty {Γ : List Term} {A b : Term} {u : Bool} (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A : .sort u) (hY : Γ ⊢ .Y A b : A)
    (ihA : SoundTy Γ A (.sort u)) (ihb : SoundTy (A :: Γ) b A.lift) :
    SoundTy Γ (.Y A b) A := by
  refine ⟨hY, ?_⟩
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  exact sound_Y_ty_aux hΔ hm rfl hΓ hA hY W hAdm ihA ihb

/-- **Saturation at a fixed point.**  An unfolding's approximant is the
body's at the slot, so the body's own saturation is the whole content:
the enlarged value is still an unfolding at the same slot, and its code
unweakens from `A↑` to `A`. -/
theorem sound_Y_dom_aux {Δ : List Term} (hΔ : ⊢ Δ) {Γ₀ Γ : List Term} {t : Term} {σ ρ}
    {m : TShape} (H : Interp Δ Γ t σ ρ m) :
    ∀ {A b : Term} {u : Bool}, t = .Y A b → ⊢ Γ →
      Γ ⊢ A : .sort u → Γ ⊢ .Y A b : A →
      Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ₀ Γ σ ρ →
      SoundTy Γ A (.sort u) → A :: Γ ⊢ b : A.lift → SoundDom (A :: Γ) b A.lift →
      ∃ m' c, Interp Δ Γ (.Y A b) σ ρ m' ∧ TShape.LE Δ m m' ∧
        Interp Δ Γ A σ ρ c ∧
        TShape.Slot Δ (A.subst σ) c ((Term.Y A b).subst σ) m' := by
  induction H with
  | @Y Γ' σ' ρ' m' A b x d hx hwx hd hdty hNV hdcY hbody hAt hYt _ _ _ =>
    have hDom := hNV.dom
    have hxcY := hNV.val
    rintro A' b' u ⟨⟩ hΓ hA hY W hAdm ihA hbt ihbdom
    have WY : Ctx.SubstEq Δ (σ'.cons ((Term.Y A b).subst σ'))
        (σ'.cons ((Term.Y A b).subst σ')) (A :: Γ') := .cons W hA (hY.subst hΔ W)
    have hAdm' : Adm Δ Γ₀ (A :: Γ') (σ'.cons ((Term.Y A b).subst σ')) (ρ'.push _) :=
      .cons hAdm W.wf hd hwx (.of_dom hDom hxcY) hdcY
    obtain ⟨mb, c, hmb, hmle, hc, hNV, hcc⟩ := ihbdom hΔ WY hAdm' hbody
    have hdc := hNV.dom
    have hmbc := hNV.val
    rw [lift_subst_cons] at hcc
    -- the body's value names `b[Y A b]`, which is `Y A b` by unfolding
    have hunf := (IsDefEq.Y_unfold₀ hΓ hA hbt).subst hΔ W
    rw [subst_inst, inst_lift_cons] at hunf
    exact ⟨mb, c, .Y hx hwx hd hdty (.of_dom hDom hxcY) hdcY hmb hAt hYt, hmle,
      Interp.unweak (Δ := Δ) hΔ hΓ hA.annot.1 (Γ' := A :: Γ') (l := .skip .refl)
        (.skip .refl) WY (fun i => rfl) hc,
      .of_dom hdc (TShape.ValCanon.defeq hΔ hdc hcc hmbc hunf.symm), hcc⟩
  | bot =>
    exact fun _ _ _ _ _ _ _ _ _ => ⟨TShape.bot, TShape.bot, .bot, TShape.bot_le' rfl, .bot,
      .of_dom (TShape.NamedO.bot (.bot (.bot .sort))) (TShape.ValCanon.of_bot rfl),
      Shape.CodeCanonS.bot⟩
  | _ => intro A b u hne; cases hne

theorem sound_Y_dom {Γ : List Term} {A b : Term} {u : Bool} (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A : .sort u) (hY : Γ ⊢ .Y A b : A)
    (ihA : SoundTy Γ A (.sort u)) (hbt : A :: Γ ⊢ b : A.lift)
    (ihbdom : SoundDom (A :: Γ) b A.lift) :
    SoundDom Γ (.Y A b) A := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  exact sound_Y_dom_aux hΔ hm rfl hΓ hA hY W hAdm ihA hbt ihbdom

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
      Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ₀ Γ σ ρ → SoundEq Γ A A' →
      SoundTy Γ A (.sort u) → SoundTy (A :: Γ) b A.lift → SoundEq (A :: Γ) b b' →
      Interp Δ Γ (.Y A' b') σ ρ m := by
  induction H with
  | @Y Γ' σ' ρ' m' A b x d hx hwx hd hdty hNV hdcY hbody hAt hYt ihx _ _ =>
    have hDom := hNV.dom
    have hxcY := hNV.val
    rintro A₁ A' b₁ b' u ⟨⟩ hΓ hAA' hY hYY' hb' W hAdm ihAeq ihA ihbty ihbeq
    -- the inner tower, already moved
    have hx' := ihx rfl hΓ hAA' hY hYY' hb' W hAdm ihAeq ihA ihbty ihbeq
    have WY : Ctx.SubstEq Δ (σ'.cons ((Term.Y A b).subst σ'))
        (σ'.cons ((Term.Y A b).subst σ')) (A :: Γ') :=
      .cons W hAA'.hasType.1 (hY.subst hΔ W)
    have hAdm' : Adm Δ Γ₀ (A :: Γ') (σ'.cons ((Term.Y A b).subst σ')) (ρ'.push _) :=
      .cons hAdm W.wf hd hwx (.of_dom hDom hxcY) hdcY
    -- the body, at the other side and at the other stage
    have hbody' := (ihbeq hΔ WY hAdm').1 hbody
    have W' : Ctx.SubstEq Δ (σ'.cons ((Term.Y A b).subst σ'))
        (σ'.cons ((Term.Y A' b').subst σ')) (A' :: Γ') :=
      .cons W hAA'.hasType.2 ((hAA'.subst hΔ W).defeqDF (hYY'.subst hΔ W))
    have hΓA' : ⊢ (A' :: Γ') := ⟨hΓ, _, hAA'.hasType.2⟩
    exact .Y hx' hwx ((ihAeq hΔ W hAdm).1 hd) hdty
      ((TShape.Named.of_dom hDom hxcY).defeq hΔ hdcY (hYY'.subst hΔ W))
      (TShape.CodeCanonS.conv hdcY (TyEq.symm ⟨u, hAA'.subst hΔ W⟩)) (IsDefEq.stage hΓA' hb' hΔ W'
        (hbody'.ctx hΓA' (Ctx.SubstEq.defeqHead hΓ hAA')))
      ⟨u, hAA'.hasType.2⟩ (hAA'.defeqDF hYY'.hasType.2)
  | bot => exact fun _ _ _ _ _ _ _ _ _ _ _ _ => .bot
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
      W hAdm ihAeq ihA ihbty ihbeq, fun h => ?_⟩
  have hY' : Γ ⊢ .Y A' b' : A' := hAA'.defeqDF hYY'.hasType.2
  exact sound_Y_eq_aux hΔ h rfl hΓ hAA'.symm hY'
    (hAA'.defeqDF hYY'.symm) hb.hasType.1 W hAdm ihAeq.symm
    (SoundTy.of_eq hAA' ihAeq ihA) ihbty' ihbeq'

/-! ## Transport

`Interp.tr` carries its motive's value at the stage extended by `b` —
the term the motive's binder is instantiated with — and the whole of
`SoundTy` is that this *is* `Interp.inst`'s decomposition of `C[b]`, with
the clause's own `v` as the slot.  `SoundEq` moves each premise with its
own induction hypothesis; the motive takes three steps (its `SoundEq`,
then `Interp.ctx` for the domain that changed, then `IsDefEq.stage` for
the stage term that changed), which is the pattern `YDF` already uses. -/

/-- The `refl` equation the `tr` clause carries, moved along congruences
of its proof, endpoints and type. -/
theorem IsDefEq.refl_eq_move {Δ : List Term} {r : Bool} {A A' a a' b b' H H' : Term}
    {u : Bool} (hAA : Δ ⊢ A ≡ A' : .sort u) (haa : Δ ⊢ a ≡ a' : A) (hbb : Δ ⊢ b ≡ b' : A)
    (hHH : Δ ⊢ H ≡ H' : .id r A a b) (heq : Δ ⊢ a ≡ b : A)
    (hH : Δ ⊢ H ≡ .refl r a : .id r A a b) : Δ ⊢ H' ≡ .refl r a' : .id r A' a' b' := by
  have hA := hAA.hasType.1; have ha := haa.hasType.1
  have hrefl : Δ ⊢ Term.refl r a ≡ Term.refl r a' : Term.id r A a b :=
    (IsDefEq.idDF hA ha heq).defeqDF (IsDefEq.reflDF hA haa (IsDefEq.idDF hA ha ha))
  exact (IsDefEq.idDF hAA haa hbb).defeqDF ((hHH.symm.trans hH).trans hrefl)

/-- **A transport computes at a stage where its endpoints agree**: its
proof is `refl` there (as a clause premise at `r = true`, by proof
irrelevance at `r = false`), so `trDF` moves it to `tr_refl`. -/
theorem IsDefEq.tr_stage {Γ Δ : List Term} {r : Bool} {A a b C X H : Term} {u v : Bool}
    {σ : Subst} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hA : Γ ⊢ A : .sort u)
    (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : A) (hC : A :: Γ ⊢ C : .sort v) (hX : Γ ⊢ X : C.inst a)
    (hH : Γ ⊢ H : .id r A a b) (heq : Δ ⊢ a.subst σ ≡ b.subst σ : A.subst σ)
    (hHr : r = true → Δ ⊢ H.subst σ ≡ .refl true (a.subst σ) :
      .id true (A.subst σ) (a.subst σ) (b.subst σ)) :
    Δ ⊢ (Term.tr r A a b C X H).subst σ ≡ X.subst σ : (C.inst b).subst σ := by
  have hA1 : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  have ha1 : Δ ⊢ a.subst σ : A.subst σ := ha.subst hΔ W
  have hb1 : Δ ⊢ b.subst σ : A.subst σ := hb.subst hΔ W
  have hC1 : A.subst σ :: Δ ⊢ C.subst σ.lift : .sort v :=
    hC.subst (Γ₀ := A.subst σ :: Δ) ⟨hΔ, _, hA1⟩ (W.lift hA hA1)
  have hX1 : Δ ⊢ X.subst σ : (C.subst σ.lift).inst (a.subst σ) := by
    have h := hX.subst hΔ W; rwa [subst_inst] at h
  have hH1 : Δ ⊢ H.subst σ : .id r (A.subst σ) (a.subst σ) (b.subst σ) := hH.subst hΔ W
  have hid : Δ ⊢ Term.id r (A.subst σ) (a.subst σ) (b.subst σ) : .sort r :=
    IsDefEq.idDF hA1 ha1 hb1
  have href : Δ ⊢ H.subst σ ≡ .refl r (a.subst σ) :
      .id r (A.subst σ) (a.subst σ) (b.subst σ) := by
    cases r with
    | true => exact hHr rfl
    | false =>
      refine IsDefEq.proofIrrel hid hH1 ?_
      exact (IsDefEq.idDF hA1 ha1 heq).defeqDF
        (IsDefEq.reflDF hA1 ha1 (IsDefEq.idDF hA1 ha1 ha1))
  have htr := IsDefEq.trDF hA1 ha1 heq.symm hC1 hC1 hX1 href
    (IsDefEq.instDF hΔ hA1 .sort hC1 heq.symm) hid
  have h2 := IsDefEq.tr_refl₀ (r := r) hΔ ha1 hC1 hX1
  rw [subst_inst]
  exact htr.trans ((IsDefEq.instDF hΔ hA1 .sort hC1 heq).defeqDF h2)

theorem sound_tr_eq_of {Γ : List Term} {A A' a a' b b' C C' X X' H H' : Term}
    {u v : Bool} {r : Bool} (hΓ : ⊢ Γ)
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (haa' : Γ ⊢ a ≡ a' : A) (hbb' : Γ ⊢ b ≡ b' : A)
    (hCC : A :: Γ ⊢ C ≡ C' : .sort v) (hCC' : A' :: Γ ⊢ C ≡ C' : .sort v)
    (hXX' : Γ ⊢ X ≡ X' : C.inst a) (hHH' : Γ ⊢ H ≡ H' : .id r A a b)
    (ihAeq : SoundEq Γ A A') (ihaeq : SoundEq Γ a a') (ihbeq : SoundEq Γ b b')
    (ihCeq : SoundEq (A :: Γ) C C') (ihXeq : SoundEq Γ X X')
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {m : TShape} (hm : Interp Δ Γ (.tr r A a b C X H) σ ρ m) :
    Interp Δ Γ (.tr r A' a' b' C' X' H') σ ρ m := by
  cases hm with
  | bot => exact .bot
  | tr hw hle hX ha hb hA hwv hNV hvc hC hcb hNV2 hcbc hH heq hAt hat hbt =>
    have hvA := hNV.dom
    have hbc := hNV.val
    have hm' := hNV2.dom
    have hmc := hNV2.val
    have hΓA' : ⊢ (A' :: Γ) := ⟨hΓ, _, hAA'.hasType.2⟩
    have WC : Ctx.SubstEq Δ (σ.cons (b.subst σ)) (σ.cons (b.subst σ)) (A :: Γ) :=
      .cons W hAA'.hasType.1 (hbb'.hasType.1.subst hΔ W)
    have hAdm' : Adm Δ Γ₀ (A :: Γ) (σ.cons (b.subst σ)) (ρ.push _) :=
      .cons hAdm W.wf hA hwv (.of_dom hvA hbc) hvc
    have WC' : Ctx.SubstEq Δ (σ.cons (b.subst σ)) (σ.cons (b'.subst σ)) (A' :: Γ) :=
      .cons W hAA'.hasType.2 ((hAA'.subst hΔ W).defeqDF (hbb'.subst hΔ W))
    have hAσ : Δ ⊢ A.subst σ ≡ A'.subst σ : .sort u := hAA'.subst hΔ W
    -- the transported value's code names the motive at `b`, hence at `a`
    have hcX :=
      hcbc.conv (TyEq.tr_motive hΔ W hAA'.hasType.1 haa'.hasType.1 hCC.hasType.1 heq)
    refine .tr hw hle ((ihXeq hΔ W hAdm).1 hX) ((ihaeq hΔ W hAdm).1 ha)
      ((ihbeq hΔ W hAdm).1 hb) ((ihAeq hΔ W hAdm).1 hA) hwv
      ((TShape.Named.of_dom hvA hbc).defeq hΔ hvc (hbb'.subst hΔ W))
      (TShape.CodeCanonS.conv hvc (TyEq.symm ⟨u, hAσ⟩))
      (IsDefEq.stage hΓA' hCC'.hasType.2 hΔ WC'
        (((ihCeq hΔ WC hAdm').1 hC).ctx hΓA' (Ctx.SubstEq.defeqHead hΓ hAA')))
      hcb ((TShape.Named.of_dom hm' hmc).defeq hΔ hcX (hXX'.subst hΔ W))
      (TShape.CodeCanonS.conv hcbc (TyEq.symm ⟨v, IsDefEq.subst' hΔ WC' hCC'⟩))
      (fun hr => by
        cases hr
        exact IsDefEq.refl_eq_move hAσ (haa'.subst hΔ W) (hbb'.subst hΔ W) (hHH'.subst hΔ W)
          heq (hH rfl))
      -- the endpoints' equation moves along the congruences
      (((hAA'.subst hΔ W).defeqDF
        (((haa'.subst hΔ W).symm.trans heq).trans (hbb'.subst hΔ W))))
      ⟨u, hAA'.hasType.2⟩ (hAA'.defeqDF haa'.hasType.2) (hAA'.defeqDF hbb'.hasType.2)

/-- The `SoundEq` half of `trDF`. -/
theorem sound_tr_eq {Γ : List Term} {A A' a a' b b' C C' X X' H H' : Term}
    {u v : Bool} {r : Bool} (hΓ : ⊢ Γ)
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (haa' : Γ ⊢ a ≡ a' : A) (hbb' : Γ ⊢ b ≡ b' : A)
    (hC : A :: Γ ⊢ C ≡ C' : .sort v) (hC' : A' :: Γ ⊢ C ≡ C' : .sort v)
    (hXX' : Γ ⊢ X ≡ X' : C.inst a) (hHH' : Γ ⊢ H ≡ H' : .id r A a b)
    (ihAeq : SoundEq Γ A A') (ihaeq : SoundEq Γ a a') (ihbeq : SoundEq Γ b b')
    (ihCeq : SoundEq (A :: Γ) C C') (ihCeq' : SoundEq (A' :: Γ) C C')
    (ihXeq : SoundEq Γ X X') :
    SoundEq Γ (.tr r A a b C X H) (.tr r A' a' b' C' X' H') := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  refine ⟨sound_tr_eq_of hΓ hAA' haa' hbb' hC hC' hXX' hHH' ihAeq ihaeq ihbeq ihCeq
      ihXeq hΔ W hAdm, ?_⟩
  have hΓA' : ⊢ (A' :: Γ) := ⟨hΓ, _, hAA'.hasType.2⟩
  have hCs : A' :: Γ ⊢ C' ≡ C : .sort v := hC'.symm
  have hCs' : A :: Γ ⊢ C' ≡ C : .sort v := hC.symm
  have hXs : Γ ⊢ X' ≡ X : C'.inst a' :=
    (IsDefEq.instDF hΓ hAA'.hasType.1 .sort hC haa').defeqDF hXX'.symm
  have hHs : Γ ⊢ H' ≡ H : .id r A' a' b' := (IsDefEq.idDF hAA' haa' hbb').defeqDF hHH'.symm
  exact sound_tr_eq_of hΓ hAA'.symm (hAA'.defeqDF haa'.symm) (hAA'.defeqDF hbb'.symm)
    hCs hCs' hXs hHs
    ihAeq.symm ihaeq.symm ihbeq.symm ihCeq'.symm ihXeq.symm hΔ W hAdm

/-- **Saturation at a transport.**  The clause already says the
transported value is hereditarily typed at the motive read at the slot,
and that it names `X` there; the transport computes to `X` at the stage
(`IsDefEq.tr_stage`), so it names the transport too. -/
theorem sound_tr_dom {Γ : List Term} {A a b C X H : Term} {r u v : Bool} (hΓ : ⊢ Γ)
    (hPC : C.Pinned (A :: Γ))
    (hA : Γ ⊢ A : .sort u) (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : A) (hC : A :: Γ ⊢ C : .sort v)
    (hX : Γ ⊢ X : C.inst a) (hHt : Γ ⊢ H : .id r A a b) (ihbdom : SoundDom Γ b A)
    (ihbdir : SoundDir Γ b) :
    SoundDom Γ (.tr r A a b C X H) (C.inst b) := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  have hwρ := hAdm.wf
  cases hm with
  | bot => exact ⟨TShape.bot, TShape.bot, .bot, TShape.bot_le' rfl, .bot, (.of_dom (TShape.NamedO.bot (.bot (.bot .sort))) (TShape.ValCanon.of_bot rfl)), TShape.CodeCanonS.bot⟩
  | tr hw hle hX' ha' hbv hAv hwv hNV hvc hCv hcb hNV2 hcbc hH heq hAt hat hbt =>
    have hvA := hNV.dom
    have hbc := hNV.val
    have hm' := hNV2.dom
    have hmc := hNV2.val
    have hcb' := hcbc
    rw [← inst_lift_cons, ← subst_inst] at hcb'
    refine ⟨_, _, .tr hm'.hasType.wf.1 (TShape.LE.refl hm'.hasType.wf.1) hX' ha' hbv hAv
        hwv (.of_dom hvA hbc) hvc hCv hcb (.of_dom hm' hmc) hcbc hH heq hAt hat hbt, hle,
      (Interp.inst (A := A) (b := C) hΔ hΓ hA hb hC hPC W hAdm
        (Subst.Saturates.one hΔ hΓ W hAdm ihbdom)
        (ihbdir hΔ W hwρ) hwρ).2 ⟨_, ?_, hbv⟩,
      .of_dom hm' (TShape.ValCanon.defeq hΔ hm' hcb' hmc
        (IsDefEq.tr_stage hΔ W hA ha hb hC hX hHt heq hH).symm), hcb'⟩
    rw [Subst.one_comp]
    exact hCv

/-- **`tr` at `refl` is the transported value.**  Forward is one `mono`:
the clause's `m'` is an approximant of `X`.  Backward is the clause
rebuilt around the value's own saturation: it gives a canonical code,
`Interp.inst` splits it into the motive at a slot approximating `a`, and
that slot serves as the witness `v`. -/
theorem sound_tr_refl_eq {Γ : List Term} {A a C X : Term} {u v : Bool} {r : Bool}
    (hPC : C.Pinned (A :: Γ))
    (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u) (ha : Γ ⊢ a : A) (hC : A :: Γ ⊢ C : .sort v) (ihadom : SoundDom Γ a A)
    (ihadir : SoundDir Γ a)
    (ihC : SoundTy (A :: Γ) C (.sort v)) (ihxdom : SoundDom Γ X (C.inst a)) :
    SoundEq Γ (.tr r A a a C X (.refl r a)) X := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  have hwρ := hAdm.wf
  constructor
  · intro h
    cases h with
    | bot => exact .bot
    | tr hw hle hX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact Interp.mono hΔ hw hle hX
  · intro h
    obtain ⟨mX, c, hmX, hmle, hc, hNV, hcc⟩ := ihxdom hΔ W hAdm h
    have hdc := hNV.dom
    have hmXc := hNV.val
    obtain ⟨x₀, hC₀, ha₀⟩ :=
      (Interp.inst (A := A) (b := C) hΔ hΓ hA ha hC hPC W hAdm
        (Subst.Saturates.one hΔ hΓ W hAdm ihadom)
        (ihadir hΔ W hwρ) hwρ).1 hc
    rw [Subst.one_comp] at hC₀
    -- the slot is the argument's approximant, hereditarily typed
    obtain ⟨x, vA, ha', hlex, hvA, hNV, hvAc⟩ := ihadom hΔ W hAdm ha₀
    have hdom := hNV.dom
    have hxc := hNV.val
    have hC : Interp Δ (A :: Γ) C ((Subst.one a).comp σ) (ρ.push x) c :=
      Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hlex⟩)
        (by rw [Subst.one_comp]; exact hC₀)
    rw [Subst.one_comp] at hC
    have Wa : Ctx.SubstEq Δ (σ.cons (a.subst σ)) (σ.cons (a.subst σ)) (A :: Γ) :=
      .cons W hA (ha.subst hΔ W)
    have hAdm' : Adm Δ Γ₀ (A :: Γ) (σ.cons (a.subst σ)) (ρ.push x) :=
      .cons hAdm W.wf hvA ha'.wf (.of_dom hdom hxc) hvAc
    have hcc' : TShape.CodeCanonS Δ (C.subst (σ.cons (a.subst σ))) c := by
      rw [subst_inst, inst_lift_cons] at hcc; exact hcc
    have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
    have haσ : Δ ⊢ a.subst σ : A.subst σ := ha.subst hΔ W
    refine .tr h.wf hmle hmX ha' ha' hvA ha'.wf (.of_dom hdom hxc) hvAc hC
      (ihC.isType hΔ Wa hAdm' hC) (.of_dom hdc hmXc) hcc' ?_ haσ ⟨u, hA⟩ ha ha
    rintro rfl
    exact IsDefEq.reflDF hAσ haσ (IsDefEq.idDF hAσ haσ haσ)

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
    (hxd : TShape.NamedO Δ none d x) (hxc : TShape.ValCanon Δ t x)
    (hdc : TShape.CodeCanonS Δ (A.subst σ) d)
    (hcc : TShape.CodeCanonS Δ ((B.subst σ.lift).inst t) c)
    (hc : Interp Δ (A :: Γ) B (σ.cons t) (ρ.push x) c) :
    ∃ (k : Nat) (dk xk ck : Shape k),
      Interp Δ Γ (.forallE A B) σ ρ (Shape.T (n := k+1)
        (.forallE (A.subst σ) (B.subst σ.lift) dk [⟨t, xk, ck⟩])) ∧
      TShape.LE Δ c (Shape.T ck) ∧ TShape.LE Δ (Shape.T xk) x := by
  obtain ⟨k, hkd, hkx, hkc⟩ : ∃ k, d.1 ≤ k ∧ x.1 ≤ k ∧ c.1 ≤ k :=
    ⟨max (max d.1 x.1) c.1, Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..),
      Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..), Nat.le_max_right ..⟩
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  have hΔA : ⊢ (A.subst σ :: Δ) := ⟨hΔ, _, hAσ⟩
  have hwd : Shape.WF Δ (d.2.lift k) := (Shape.lift_wf hkd).2 hdty.wf.1
  have hwx : Shape.WF Δ (x.2.lift k) := (Shape.lift_wf hkx).2 hxd.hasType.wf.1
  have hwc : Shape.WF Δ (c.2.lift k) := (Shape.lift_wf hkc).2 hc.wf
  have hwf : Shape.WF (n := k+1) Δ
      (.forallE (A.subst σ) (B.subst σ.lift) (d.2.lift k)
        [⟨t, x.2.lift k, c.2.lift k⟩]) := by
    refine ⟨⟨u, hAσ⟩, ⟨v, hB.subst hΔA (W.lift hA hAσ)⟩,
      Shape.WF.name hwd ((Shape.CodeCanonS.lift_iff hkd).2 hdc),
      ShapeFun.WF.name ⟨?_, ?_⟩ ?_, trivial⟩
    · intro e he
      cases List.mem_singleton.1 he
      exact ⟨⟨u, hAσ⟩, ht, hwx, hwc⟩
    · intro e he e' he' Θ τ hΘ Wτ _ _
      cases List.mem_singleton.1 he
      cases List.mem_singleton.1 he'
      exact Shape.WF.coherent (Shape.WF.subst hΘ Wτ hwc)
    · intro e he
      cases List.mem_singleton.1 he
      exact (Shape.CodeCanonS.lift_iff hkc).2 hcc
  refine ⟨k, _, _, _, .forallE ?_ ?_ hwf ?_ ?_ hwf (TShape.LE.refl hwf)
      ⟨u, hA⟩ ⟨v, hB⟩,
    TShape.LE.le_lift hΔ (m := c) hkc hc.wf,
    TShape.LE.lift_le hΔ (m := x) hkx hxd.hasType.wf.1⟩
  · exact Interp.mono hΔ hwd (TShape.LE.lift_le hΔ (m := d) hkd hdty.wf.1) hdint
  · exact hdty.lift_subject hΔ hkd
  · intro e he
    cases List.mem_singleton.1 he
    exact .of_dom (TShape.NamedO.mono_r hΔ (TShape.NamedO.lift_subject hΔ hxd hkx)
        (TShape.LE.le_lift hΔ (m := d) hkd hdty.wf.1) (hdty.lift_subject hΔ hkd))
      ((TShape.ValCanon.lift_iff hΔ hkx).1 hxc)
  · intro e he
    cases List.mem_singleton.1 he
    refine Interp.mono hΔ hwc (TShape.LE.lift_le hΔ (m := c) hkc hc.wf) ?_
    exact Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
      TShape.LE.le_lift hΔ (m := x) hkx hxd.hasType.wf.1⟩) hc

/-- The Σ twin of `Interp.forallE_single`. -/
theorem Interp.sigma_single {Γ Δ : List Term} {A B t : Term} {σ ρ} {u v : Bool}
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hwρ : Valuation.WF Δ ρ)
    (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) (ht : Δ ⊢ t : A.subst σ)
    {d x c : TShape} (hdint : Interp Δ Γ A σ ρ d) (hdty : TShape.HasType Δ d TShape.type)
    (hxd : TShape.NamedO Δ none d x) (hxc : TShape.ValCanon Δ t x)
    (hdc : TShape.CodeCanonS Δ (A.subst σ) d)
    (hcc : TShape.CodeCanonS Δ ((B.subst σ.lift).inst t) c)
    (hc : Interp Δ (A :: Γ) B (σ.cons t) (ρ.push x) c) :
    ∃ (k : Nat) (dk xk ck : Shape k),
      Interp Δ Γ (.sigma A B) σ ρ (Shape.T (n := k+1)
        (.sigma (A.subst σ) (B.subst σ.lift) dk [⟨t, xk, ck⟩])) ∧
      TShape.LE Δ c (Shape.T ck) ∧ TShape.LE Δ (Shape.T xk) x := by
  obtain ⟨k, hkd, hkx, hkc⟩ : ∃ k, d.1 ≤ k ∧ x.1 ≤ k ∧ c.1 ≤ k :=
    ⟨max (max d.1 x.1) c.1, Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..),
      Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..), Nat.le_max_right ..⟩
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  have hΔA : ⊢ (A.subst σ :: Δ) := ⟨hΔ, _, hAσ⟩
  have hwd : Shape.WF Δ (d.2.lift k) := (Shape.lift_wf hkd).2 hdty.wf.1
  have hwx : Shape.WF Δ (x.2.lift k) := (Shape.lift_wf hkx).2 hxd.hasType.wf.1
  have hwc : Shape.WF Δ (c.2.lift k) := (Shape.lift_wf hkc).2 hc.wf
  have hwf : Shape.WF (n := k+1) Δ
      (.sigma (A.subst σ) (B.subst σ.lift) (d.2.lift k)
        [⟨t, x.2.lift k, c.2.lift k⟩]) := by
    refine ⟨⟨u, hAσ⟩, ⟨v, hB.subst hΔA (W.lift hA hAσ)⟩,
      Shape.WF.name hwd ((Shape.CodeCanonS.lift_iff hkd).2 hdc),
      ShapeFun.WF.name ⟨?_, ?_⟩ ?_, trivial⟩
    · intro e he
      cases List.mem_singleton.1 he
      exact ⟨⟨u, hAσ⟩, ht, hwx, hwc⟩
    · intro e he e' he' Θ τ hΘ Wτ _ _
      cases List.mem_singleton.1 he
      cases List.mem_singleton.1 he'
      exact Shape.WF.coherent (Shape.WF.subst hΘ Wτ hwc)
    · intro e he
      cases List.mem_singleton.1 he
      exact (Shape.CodeCanonS.lift_iff hkc).2 hcc
  refine ⟨k, _, _, _, .sigma ?_ ?_ hwf ?_ ?_ hwf (TShape.LE.refl hwf) ⟨u, hA⟩ ⟨v, hB⟩,
    TShape.LE.le_lift hΔ (m := c) hkc hc.wf,
    TShape.LE.lift_le hΔ (m := x) hkx hxd.hasType.wf.1⟩
  · exact Interp.mono hΔ hwd (TShape.LE.lift_le hΔ (m := d) hkd hdty.wf.1) hdint
  · exact hdty.lift_subject hΔ hkd
  · intro e he
    cases List.mem_singleton.1 he
    exact .of_dom (TShape.NamedO.mono_r hΔ (TShape.NamedO.lift_subject hΔ hxd hkx)
        (TShape.LE.le_lift hΔ (m := d) hkd hdty.wf.1) (hdty.lift_subject hΔ hkd))
      ((TShape.ValCanon.lift_iff hΔ hkx).1 hxc)
  · intro e he
    cases List.mem_singleton.1 he
    refine Interp.mono hΔ hwc (TShape.LE.lift_le hΔ (m := c) hkc hc.wf) ?_
    exact Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
      TShape.LE.le_lift hΔ (m := x) hkx hxd.hasType.wf.1⟩) hc

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
    (hxd : TShape.NamedO Δ none d x) (hxc : TShape.ValCanon Δ t x)
    (hdc : TShape.CodeCanonS Δ (A₀.subst σ) d)
    (hcc : TShape.CodeCanonS Δ ((B₀.subst σ.lift).inst t) c)
    (hc : Interp Δ (A₀ :: Γ) B₀ (σ.cons t) (ρ.push x) c) :
    Interp Δ (A₁ :: Γ) B₁ (σ.cons t) (ρ.push x) c := by
  have hwρ := hAdm.wf
  obtain ⟨k, dk, xk, ck, hprobe, hcle, hxle⟩ :=
    Interp.forallE_single hΔ W hwρ hA₀ hB₀ ht hdint hdty hxd hxc hdc hcc hc
  have hpr := (H hΔ W hAdm).1 hprobe
  cases hpr with
  | forallE hA₁int hd₁ hwf₁ _ hbody₁ hw₁ hle₁ =>
    obtain ⟨hPi, _, hcov⟩ :=
      TShape.LE.forallE_decomp hΔ hle₁ hprobe.wf hwf₁ (TEvaluates.refl hwf₁.2.2.2.1)
    have hev := hcov ⟨t, xk, ck⟩ (by simp)
    have hB := sound_graph_lookup (B := B₁) ⟨hΓ, _, hA₁⟩ hA₁ hB₁ hΔ W hbody₁
      (TShape.WF.T.2 (hprobe.wf.2.2.2.1.1 _ (by simp)).2.2.1) hB₁dir hwρ ht hPi.1 hev
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
    (hxd : TShape.NamedO Δ none d x) (hxc : TShape.ValCanon Δ t x)
    (hdc : TShape.CodeCanonS Δ (A₀.subst σ) d)
    (hcc : TShape.CodeCanonS Δ ((B₀.subst σ.lift).inst t) c)
    (hc : Interp Δ (A₀ :: Γ) B₀ (σ.cons t) (ρ.push x) c) :
    Interp Δ (A₁ :: Γ) B₁ (σ.cons t) (ρ.push x) c := by
  have hwρ := hAdm.wf
  obtain ⟨k, dk, xk, ck, hprobe, hcle, hxle⟩ :=
    Interp.sigma_single hΔ W hwρ hA₀ hB₀ ht hdint hdty hxd hxc hdc hcc hc
  have hpr := (H hΔ W hAdm).1 hprobe
  cases hpr with
  | sigma hA₁int hd₁ hwf₁ _ hbody₁ hw₁ hle₁ =>
    obtain ⟨hSg, _, hcov⟩ :=
      TShape.LE.sigma_decomp hΔ hle₁ hprobe.wf hwf₁ (TEvaluates.refl hwf₁.2.2.2.1)
    have hev := hcov ⟨t, xk, ck⟩ (by simp)
    have hB := sound_graph_lookup (B := B₁) ⟨hΓ, _, hA₁⟩ hA₁ hB₁ hΔ W hbody₁
      (TShape.WF.T.2 (hprobe.wf.2.2.2.1.1 _ (by simp)).2.2.1) hB₁dir hwρ ht hSg.1 hev
    exact Interp.mono hΔ hc.wf hcle (Interp.mono_val hΔ (Valuation.LE.push.2
      ⟨Valuation.LE.refl hwρ, hxle⟩) hB)

/-- **Instantiating two semantically equal codomains at one argument.**
`Interp.inst` splits an approximant of `B[a]` into the codomain at a slot
approximating `a`; `SoundTy a A` types that slot, which is what the
one-entry probe needs; and `forallE_cod` moves it across.  This is the
semantic half of type uniqueness at `app` — the half that was waiting for
`Interp.inst`. -/
theorem SoundEq.inst_cod {Γ : List Term} {A₀ A₁ B₀ B₁ a : Term} {u v u' v' : Bool}
    (hPB₀ : B₀.Pinned (A₀ :: Γ)) (hPB₁ : B₁.Pinned (A₁ :: Γ))
    (hΓ : ⊢ Γ) (hA₀ : Γ ⊢ A₀ : .sort u) (hB₀ : A₀ :: Γ ⊢ B₀ : .sort v)
    (hA₁ : Γ ⊢ A₁ : .sort u') (hB₁ : A₁ :: Γ ⊢ B₁ : .sort v')
    (hB₀dir : SoundDir (A₀ :: Γ) B₀) (hB₁dir : SoundDir (A₁ :: Γ) B₁)
    (ha₀ : SoundTy Γ a A₀) (ha₁ : SoundTy Γ a A₁)
    (hdom₀ : SoundDom Γ a A₀) (hdom₁ : SoundDom Γ a A₁) (hadir : SoundDir Γ a)
    (ihA₀ : SoundTy Γ A₀ (.sort u)) (ihA₁ : SoundTy Γ A₁ (.sort u'))
    (ihB₀c : CodeAt (A₀ :: Γ) B₀) (ihB₁c : CodeAt (A₁ :: Γ) B₁)
    (H : SoundEq Γ (.forallE A₀ B₀) (.forallE A₁ B₁)) :
    SoundEq Γ (B₀.inst a) (B₁.inst a) := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  have hwρ := hAdm.wf
  constructor
  · intro h
    obtain ⟨x₀, hb₀, hx₀⟩ := (Interp.inst (A := A₀) (b := B₀) hΔ hΓ hA₀ ha₀.typed hB₀
      hPB₀ W hAdm (Subst.Saturates.one hΔ hΓ W hAdm hdom₀)
      (hadir hΔ W hwρ) hwρ).1 h
    rw [Subst.one_comp] at hb₀
    obtain ⟨x, d, hx, hlex, hd, hNV, hdc⟩ := hdom₀ hΔ W hAdm hx₀
    have hxd := hNV.dom
    have hxc := hNV.val
    have hb : Interp Δ (A₀ :: Γ) B₀ (σ.cons (a.subst σ)) (ρ.push x) m :=
      Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hlex⟩) hb₀
    refine (Interp.inst (A := A₁) (b := B₁) hΔ hΓ hA₁ ha₁.typed hB₁ hPB₁ W hAdm
      (Subst.Saturates.one hΔ hΓ W hAdm hdom₁)
      (hadir hΔ W hwρ) hwρ).2 ⟨x, ?_, hx⟩
    rw [Subst.one_comp]
    have Wc : Ctx.SubstEq Δ (σ.cons (a.subst σ)) (σ.cons (a.subst σ)) (A₀ :: Γ) :=
      .cons W hA₀ (ha₀.typed.subst hΔ W)
    have hcc : TShape.CodeCanonS Δ ((B₀.subst σ.lift).inst (a.subst σ)) m := by
      have h' := ihB₀c hΔ Wc (Adm.cons hAdm hΓ hd hx.wf (.of_dom hxd hxc) hdc) hb
      rwa [← inst_lift_cons] at h'
    exact SoundEq.forallE_cod hΓ hA₀ hB₀ hA₁ hB₁ hB₁dir H hΔ W hAdm
      (ha₀.typed.subst hΔ W) hd (ihA₀.isType hΔ W hAdm hd) hxd hxc hdc hcc hb
  · intro h
    obtain ⟨x₀, hb₀, hx₀⟩ := (Interp.inst (A := A₁) (b := B₁) hΔ hΓ hA₁ ha₁.typed hB₁
      hPB₁ W hAdm (Subst.Saturates.one hΔ hΓ W hAdm hdom₁)
      (hadir hΔ W hwρ) hwρ).1 h
    rw [Subst.one_comp] at hb₀
    obtain ⟨x, d, hx, hlex, hd, hNV, hdc⟩ := hdom₁ hΔ W hAdm hx₀
    have hxd := hNV.dom
    have hxc := hNV.val
    have hb : Interp Δ (A₁ :: Γ) B₁ (σ.cons (a.subst σ)) (ρ.push x) m :=
      Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hlex⟩) hb₀
    refine (Interp.inst (A := A₀) (b := B₀) hΔ hΓ hA₀ ha₀.typed hB₀ hPB₀ W hAdm
      (Subst.Saturates.one hΔ hΓ W hAdm hdom₀)
      (hadir hΔ W hwρ) hwρ).2 ⟨x, ?_, hx⟩
    rw [Subst.one_comp]
    have Wc : Ctx.SubstEq Δ (σ.cons (a.subst σ)) (σ.cons (a.subst σ)) (A₁ :: Γ) :=
      .cons W hA₁ (ha₁.typed.subst hΔ W)
    have hcc : TShape.CodeCanonS Δ ((B₁.subst σ.lift).inst (a.subst σ)) m := by
      have h' := ihB₁c hΔ Wc (Adm.cons hAdm hΓ hd hx.wf (.of_dom hxd hxc) hdc) hb
      rwa [← inst_lift_cons] at h'
    exact SoundEq.forallE_cod hΓ hA₁ hB₁ hA₀ hB₀ hB₀dir H.symm hΔ W hAdm
      (ha₁.typed.subst hΔ W) hd (ihA₁.isType hΔ W hAdm hd) hxd hxc hdc hcc hb

/-- The Σ twin, for `snd`. -/
theorem SoundEq.inst_cod_sigma {Γ : List Term} {A₀ A₁ B₀ B₁ a : Term} {u v u' v' : Bool}
    (hPB₀ : B₀.Pinned (A₀ :: Γ)) (hPB₁ : B₁.Pinned (A₁ :: Γ))
    (hΓ : ⊢ Γ) (hA₀ : Γ ⊢ A₀ : .sort u) (hB₀ : A₀ :: Γ ⊢ B₀ : .sort v)
    (hA₁ : Γ ⊢ A₁ : .sort u') (hB₁ : A₁ :: Γ ⊢ B₁ : .sort v')
    (hB₀dir : SoundDir (A₀ :: Γ) B₀) (hB₁dir : SoundDir (A₁ :: Γ) B₁)
    (ha₀ : SoundTy Γ a A₀) (ha₁ : SoundTy Γ a A₁)
    (hdom₀ : SoundDom Γ a A₀) (hdom₁ : SoundDom Γ a A₁) (hadir : SoundDir Γ a)
    (ihA₀ : SoundTy Γ A₀ (.sort u)) (ihA₁ : SoundTy Γ A₁ (.sort u'))
    (ihB₀c : CodeAt (A₀ :: Γ) B₀) (ihB₁c : CodeAt (A₁ :: Γ) B₁)
    (H : SoundEq Γ (.sigma A₀ B₀) (.sigma A₁ B₁)) :
    SoundEq Γ (B₀.inst a) (B₁.inst a) := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m
  have hwρ := hAdm.wf
  constructor
  · intro h
    obtain ⟨x₀, hb₀, hx₀⟩ := (Interp.inst (A := A₀) (b := B₀) hΔ hΓ hA₀ ha₀.typed hB₀
      hPB₀ W hAdm (Subst.Saturates.one hΔ hΓ W hAdm hdom₀)
      (hadir hΔ W hwρ) hwρ).1 h
    rw [Subst.one_comp] at hb₀
    obtain ⟨x, d, hx, hlex, hd, hNV, hdc⟩ := hdom₀ hΔ W hAdm hx₀
    have hxd := hNV.dom
    have hxc := hNV.val
    have hb : Interp Δ (A₀ :: Γ) B₀ (σ.cons (a.subst σ)) (ρ.push x) m :=
      Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hlex⟩) hb₀
    refine (Interp.inst (A := A₁) (b := B₁) hΔ hΓ hA₁ ha₁.typed hB₁ hPB₁ W hAdm
      (Subst.Saturates.one hΔ hΓ W hAdm hdom₁)
      (hadir hΔ W hwρ) hwρ).2 ⟨x, ?_, hx⟩
    rw [Subst.one_comp]
    have Wc : Ctx.SubstEq Δ (σ.cons (a.subst σ)) (σ.cons (a.subst σ)) (A₀ :: Γ) :=
      .cons W hA₀ (ha₀.typed.subst hΔ W)
    have hcc : TShape.CodeCanonS Δ ((B₀.subst σ.lift).inst (a.subst σ)) m := by
      have h' := ihB₀c hΔ Wc (Adm.cons hAdm hΓ hd hx.wf (.of_dom hxd hxc) hdc) hb
      rwa [← inst_lift_cons] at h'
    exact SoundEq.sigma_cod hΓ hA₀ hB₀ hA₁ hB₁ hB₁dir H hΔ W hAdm
      (ha₀.typed.subst hΔ W) hd (ihA₀.isType hΔ W hAdm hd) hxd hxc hdc hcc hb
  · intro h
    obtain ⟨x₀, hb₀, hx₀⟩ := (Interp.inst (A := A₁) (b := B₁) hΔ hΓ hA₁ ha₁.typed hB₁
      hPB₁ W hAdm (Subst.Saturates.one hΔ hΓ W hAdm hdom₁)
      (hadir hΔ W hwρ) hwρ).1 h
    rw [Subst.one_comp] at hb₀
    obtain ⟨x, d, hx, hlex, hd, hNV, hdc⟩ := hdom₁ hΔ W hAdm hx₀
    have hxd := hNV.dom
    have hxc := hNV.val
    have hb : Interp Δ (A₁ :: Γ) B₁ (σ.cons (a.subst σ)) (ρ.push x) m :=
      Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hlex⟩) hb₀
    refine (Interp.inst (A := A₀) (b := B₀) hΔ hΓ hA₀ ha₀.typed hB₀ hPB₀ W hAdm
      (Subst.Saturates.one hΔ hΓ W hAdm hdom₀)
      (hadir hΔ W hwρ) hwρ).2 ⟨x, ?_, hx⟩
    rw [Subst.one_comp]
    have Wc : Ctx.SubstEq Δ (σ.cons (a.subst σ)) (σ.cons (a.subst σ)) (A₁ :: Γ) :=
      .cons W hA₁ (ha₁.typed.subst hΔ W)
    have hcc : TShape.CodeCanonS Δ ((B₁.subst σ.lift).inst (a.subst σ)) m := by
      have h' := ihB₁c hΔ Wc (Adm.cons hAdm hΓ hd hx.wf (.of_dom hxd hxc) hdc) hb
      rwa [← inst_lift_cons] at h'
    exact SoundEq.sigma_cod hΓ hA₁ hB₁ hA₀ hB₀ hB₀dir H.symm hΔ W hAdm
      (ha₁.typed.subst hΔ W) hd (ihA₁.isType hΔ W hAdm hd) hxd hxc hdc hcc hb

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
    refine Interp.piAtom (u := u) (v := v) ?_ ?_ hA₀ hB₀
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
    refine Interp.sigmaAtom (u := u) (v := v) ?_ ?_ hA₀ hB₀
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
    (hA : SoundTy Γ A (.sort u)) (hB : A :: Γ ⊢ B : .sort v) (hAc : CodeAt Γ A)
    (hA' : SoundTy Γ A' (.sort u')) (hB' : A' :: Γ ⊢ B' : .sort v') (hA'c : CodeAt Γ A')
    (H : SoundEq Γ (.sigma A B) (.sigma A' B')) : SoundEq Γ A A' := by
  suffices key : ∀ {A B A' B' : Term} {u v : Bool}, SoundTy Γ A (.sort u) →
      A :: Γ ⊢ B : .sort v → CodeAt Γ A → SoundEq Γ (.sigma A B) (.sigma A' B') →
      ∀ {Δ Γ₀ σ ρ}, ⊢ Δ → Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ₀ Γ σ ρ →
      ∀ {m}, Interp Δ Γ A σ ρ m → Interp Δ Γ A' σ ρ m by
    intro Δ Γ₀ σ ρ hΔ W hAdm m
    exact ⟨key hA hB hAc H hΔ W hAdm, key hA' hB' hA'c H.symm hΔ W hAdm⟩
  intro A B A' B' u v hA hB hAc H Δ Γ₀ σ ρ hΔ W hAdm m hm
  have ⟨⟨_, hAσ⟩, _, hBσ⟩ := PiLabelEq.subst hΔ W ⟨⟨u, hA.typed⟩, v, hB⟩
  have hw : Shape.WF (n := m.1+1) Δ (ShapeS.sigma (A.subst σ) (B.subst σ.lift) m.2 []) :=
    ⟨⟨_, hAσ.hasType.1⟩, ⟨_, hBσ.hasType.1⟩,
      Shape.WF.name hm.wf (hAc hΔ W hAdm hm),
      ShapeFun.WF.name
        ⟨fun _ he => absurd he List.not_mem_nil, fun _ he => absurd he List.not_mem_nil⟩
        nofun, trivial⟩
  have hprobe : Interp Δ Γ (.sigma A B) σ ρ
      (Shape.T (n := m.1+1) (ShapeS.sigma (A.subst σ) (B.subst σ.lift) m.2 [])) :=
    .sigma hm (hA.isType hΔ W hAdm hm) hw nofun nofun hw (TShape.LE.refl hw)
      ⟨u, hA.typed⟩ ⟨v, hB⟩
  have hmove := (H hΔ W hAdm).1 hprobe
  cases hmove with
  | sigma hA'' _ hwf _ _ _ hle _ _ =>
    obtain ⟨_, hdd, _⟩ := TShape.LE.sigma_decomp hΔ hle hw hwf (TEvaluates.refl hwf.2.2.2.1)
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
  have hmove := (H hΓ (Ctx.SubstEq.id hΓ) Adm.bot).1
    (.id hw (TShape.LE.refl hw) ⟨u, hA₀⟩ ha₀ hb₀)
  cases hmove with
  | id _ hle _ _ _ =>
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
  | pairDF hAA' hB hB' _ _ _ _ ihA ihB ihB' iha ihb _ _ =>
    exact ⟨dir_pair (ihA hΓ).1 (ihB ⟨hΓ, _, hAA'.hasType.1⟩).1 (iha hΓ).1 (ihb hΓ).1,
      dir_pair (ihA hΓ).2 (ihB' ⟨hΓ, _, hAA'.hasType.2⟩).2 (iha hΓ).2 (ihb hΓ).2⟩
  | fstDF _ _ _ _ _ ih => exact ⟨dir_fst (ih hΓ).1, dir_fst (ih hΓ).2⟩
  | sndDF _ _ _ _ _ _ ih _ => exact ⟨dir_snd (ih hΓ).1, dir_snd (ih hΓ).2⟩
  | succDF _ ih => exact ⟨dir_succ (ih hΓ).1, dir_succ (ih hΓ).2⟩
  | natCaseDF _ _ _ hbb' _ _ ihM iha ihb _ =>
    exact ⟨dir_natCase hΓ hbb'.hasType.1 (ihM hΓ).1 (iha hΓ).1 (ihb ⟨hΓ, _, .nat⟩).1,
      dir_natCase hΓ hbb'.hasType.2 (ihM hΓ).2 (iha hΓ).2 (ihb ⟨hΓ, _, .nat⟩).2⟩
  | idDF hAA' haa' hbb' ihA iha ihb =>
    exact ⟨dir_id hAA'.hasType.1 haa'.hasType.1 hbb'.hasType.1,
      dir_id hAA'.hasType.2 (hAA'.defeqDF haa'.hasType.2) (hAA'.defeqDF hbb'.hasType.2)⟩
  | reflDF => exact ⟨dir_refl, dir_refl⟩
  -- the case `SoundJoin` was meant for: two transports are typed at two
  -- approximants of the motive, and the witness above both has to be
  -- typed at the motive above both (`dir_tr does this with the subject
  -- join).  Every other case is an upper bound
  -- with no typing to preserve, which is why they run under
  -- `Valuation.WF` with no admissibility in sight
  | trDF hAA' haa' hbb' hC hC' hxx' hhh' _ _ ihA iha ihb ihC ihC' ihx ihh =>
    exact ⟨dir_tr hAA'.hasType.1 hbb'.hasType.1 (ihA hΓ).1 (iha hΓ).1 (ihb hΓ).1
        (ihC ⟨hΓ, _, hAA'.hasType.1⟩).1 (ihx hΓ).1,
      dir_tr hAA'.hasType.2 (hAA'.defeqDF hbb'.hasType.2) (ihA hΓ).2 (iha hΓ).2 (ihb hΓ).2
        (ihC' ⟨hΓ, _, hAA'.hasType.2⟩).2 (ihx hΓ).2⟩
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
    exact ⟨dir_Y h1.hasType.1 hY.hasType.1 (ihA hΓ).1 (ihb ⟨hΓ, _, h1.hasType.1⟩).1,
      dir_Y h1.hasType.2 (h1.defeqDF hY.hasType.2) (ihA hΓ).2
        (ihb' ⟨hΓ, _, h1.hasType.2⟩).2⟩

/-! ## The soundness theorem

Two conclusions, as master's: the terms have the same approximants
(`SoundEq`, his `HasEquality`) and every approximant of the left one is
below a typed one (`SoundTy`, his `HasFixedness`).  Directedness is
`IsDefEq.dir` above; his `HasSubstitution`/`HasRenaming` are
`Interp.substTerm`/`Interp.weak'`; his `PiReady` dissolves into
`IsDefEq.dir` of the domain and the codomain; his `regular` is never
used, here or there. -/

/-- What one derivation yields.  A record rather than a tuple: the
conclusions have grown from two to six, and each addition would
otherwise renumber every projection in the file. -/
structure Sound (Γ : List Term) (t t' A : Term) : Prop where
  /-- The two sides have the same approximants. -/
  eq : SoundEq Γ t t'
  /-- Every approximant is typed at one of `A`. -/
  ty : SoundTy Γ t A
  /-- The clause conditions `Interp.to_substTerm` reads (§3.1d). -/
  pin : t.Pinned Γ
  /-- And for the right-hand side, which `symm` needs. -/
  pin' : t'.Pinned Γ
  /-- Saturation: every approximant is below a hereditarily typed one.
  The right-hand side needs no field of its own: `SoundDom.of_eq` moves
  this one across `eq`. -/
  dom : SoundDom Γ t A

/-- Attach the two `Pinned` conclusions to a lemma that proves the other
two, so the atoms and the purely structural rules stay one-liners. -/
theorem and_pinned {Γ : List Term} {t t' A : Term}
    (h : SoundEq Γ t t' ∧ SoundTy Γ t A) (hp : t.Pinned Γ) (hp' : t'.Pinned Γ)
    (hd : SoundDom Γ t A) : Sound Γ t t' A :=
  ⟨h.1, h.2, hp, hp', hd⟩

/-- The same, when the type only *filters* -- its approximants are never
binders, so the typing is already hereditary and saturation is free.
This is every atom and every type former. -/
theorem and_pinned_filter {Γ : List Term} {t t' A : Term}
    (h : SoundEq Γ t t' ∧ SoundTy Γ t A) (hp : t.Pinned Γ) (hp' : t'.Pinned Γ)
    (hnb : ∀ {Δ : List Term} {σ ρ : _} {a : TShape}, Interp Δ Γ A σ ρ a → ¬ a.IsBinder)
    (hct : CodeAt Γ t) (hcA : CodeAt Γ A) :
    Sound Γ t t' A :=
  ⟨h.1, h.2, hp, hp', SoundDom.of_typedAt hnb h.2.typedAt hct hcA⟩

/-- The unit type names itself. -/
theorem CodeAt.unit {Γ : List Term} {r : Bool} : CodeAt Γ (Term.unit r) :=
  CodeAt.of_top Interp.le_unit (s := TShape.unit r)
    (fun _ _ => show TyEq _ _ _ from TyEq.refl .unit)

/-- So does an identity type, its label being the stage's instance. -/
theorem CodeAt.id {Γ : List Term} {r u : Bool} {A a b : Term} (hA : Γ ⊢ A : .sort u)
    (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : A) : CodeAt Γ (.id r A a b) := by
  intro Δ Γ₀ σ ρ hΔ W _ m hm
  exact TShape.CodeCanonS.mono hΔ (Interp.le_id hm) 
    (show TyEq _ _ _ from ⟨_, (IsDefEq.idDF (r := r) hA ha hb).subst hΔ W⟩)

/-- A `refl` carries no names. -/
theorem CodeAt.refl {Γ : List Term} {r : Bool} {a : Term} : CodeAt Γ (.refl r a) := by
  intro Δ Γ₀ σ ρ hΔ W _ m hm
  cases hm with
  | bot => exact TShape.CodeCanonS.bot
  | refl _ hle => exact TShape.CodeCanonS.mono hΔ hle  trivial

/-! ## η

An approximant of `e` is one of its expansion, and that is where the
slot discipline pays: saturation (`SoundDom`) gives a λ-approximant above
it whose entry inputs are *hereditarily* typed, which is exactly what
`Interp.lam`'s slot asks, and the expansion's bodies are then that
approximant's own lookups (`TEvaluates.refl`).  The original gets the
same effect from its λ clause, which reads the body at the input
normalised at the domain (§4.5g). -/

theorem sound_eta_of {Γ : List Term} {A B e : Term} {u : Bool} (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A : .sort u) (ihedom : SoundDom Γ e (.forallE A B))
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {m : TShape} (hm : Interp Δ Γ e σ ρ m) :
    Interp Δ Γ (.lam A (.app e.lift (.bvar 0))) σ ρ m := by
  obtain ⟨m', p, hm', hle, hp, hNV, _⟩ := ihedom hΔ W hAdm hm
  have hdom := hNV.dom
  have hcanm := hNV.val
  have hmbot : m.2 = Shape.bot → Interp Δ Γ (.lam A (.app e.lift (.bvar 0))) σ ρ m := by
    intro hb
    obtain ⟨k, s⟩ := m
    cases k with
    | zero => cases s with
      | bot => exact .bot
      | sort r => exact absurd hb (by simp [Shape.bot])
    | succ k =>
      cases s <;> first | exact .bot | exact absurd hb (by simp [Shape.bot])
  -- the code is an approximant of a Π, so it is `⊥` or a Π-shape
  have hpi : p.2 = Shape.bot ∨ p.IsPi := by
    cases hp with
    | bot => exact .inl rfl
    | forallE _ _ _ _ _ _ hlep _ _ => exact TShape.isPi_or_bot_of_le hlep trivial
  cases hdom with
  | base hnb hty =>
    -- not a Π-shape, so `⊥` — and then so is the subject
    have hb : p.2 = Shape.bot := hpi.resolve_right (fun h => hnb h.isBinder)
    exact hmbot (TShape.le_bot hΔ (TShape.HasType.bot_r hΔ hb hty) hle)
  | @pi _ n A' B' d f _ cs hty hent hin hev hout =>
    -- the dominating approximant is a λ-shape, and its entries' inputs
    -- are hereditarily typed at the Π's domain
    cases hty with
    | bot hb => exact hmbot (TShape.le_bot hΔ rfl hle)
    | refl hleid hAty =>
      -- a `refl`-shape is never typed at a Π code
      exact absurd hleid (by
        intro h
        obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ h
        exact absurd h2 (fun x => x))
    | @lam nm n₀ _ A₀ g _ _ _ _ g₀ hd hfo hwg hwPi hwg₀ hg hg₀ev hg₀ty hlab =>
      -- the Π-code's own label and domain, read off `hp`
      cases hp with
      | @forallE _ _ _ _ k g₁ d₁ _ _ hAint hdty₁ hwf₁ _ hbody₁ hw₁ hle₁ _ _ =>
        obtain ⟨hPiLab, hdle, _⟩ := TShape.LE.forallE_decomp hΔ hle₁
          hwPi hwf₁
          (TEvaluates.refl hwf₁.2.2.2.1)
        have hAσ : TyEq Δ A₀ (A.subst σ) := TyEq.trans hlab hPiLab.1
        have hdA : Interp Δ Γ A σ ρ d.T :=
          Interp.mono hΔ (TShape.HasType.wf hd).1 hdle hAint
        -- the λ-shape, relabelled at the syntactic domain
        have hwg' : Shape.WF Δ (Shape.lam (A.subst σ) g) :=
          ⟨hwg.1, hwg.2.1, hwg.2.2.1.retype hAσ, hAσ.refl_r⟩
        refine .lam hdA hd hwg' (fun q hq => .of_dom ?_ ((hcanm q hq).1)) (fun q hq => ?_)
          hm.wf ?_ ⟨u, hA⟩
        · -- the inputs: saturation put them there
          obtain ⟨pc, hpc, hpceq⟩ : ∃ pc ∈ cs, pc.1 = ⟨q.tm, q.inp.T, q.out.T⟩ := by
            have : (⟨q.tm, q.inp.T, q.out.T⟩ : Entry TShape) ∈
                (Shape.T (n := nm+1) (ShapeS.lam A₀ g)).entries :=
              List.mem_map_of_mem (f := fun e => (⟨e.tm, e.inp.T, e.out.T⟩ : Entry TShape)) hq
            rw [hent, List.mem_map] at this
            obtain ⟨pc, hpc, heq⟩ := this
            exact ⟨pc, hpc, heq⟩
          have := hin pc hpc
          rw [hpceq] at this
          exact this
        · -- the body: a lookup in the same λ-shape, at that entry
          have hwe := hwg.2.2.1.1 q hq
          have hm'' : Interp Δ Γ e (Subst.lift_l Lift.refl.skip (σ.cons q.tm)) ρ
              (Shape.T (n := nm+1) (ShapeS.lam A₀ g)) := hm'
          have hfun : Interp Δ (A :: Γ) e.lift (σ.cons q.tm) (ρ.push q.inp.T)
              (Shape.T (n := nm+1) (ShapeS.lam A₀ g)) :=
            Interp.weak' (Γ' := A :: Γ) (ρ' := ρ.push q.inp.T) hΓ hm'' (.skip .refl)
              (fun _ => rfl)
          have hstable : Stable Δ (A :: Γ) (σ.cons q.tm) (Term.bvar 0) A₀ := by
            refine Stable.of_typed (IsDefEq.bvar₀ ⟨hΓ, _, hA⟩ Lookup.zero) ?_
            show TyEq Δ A₀ ((A.lift).subst (σ.cons q.tm))
            rw [show (A.lift).subst (σ.cons q.tm) = A.subst σ from by
              rw [Term.lift, subst_lift']
              rfl]
            exact hAσ
          exact .app hfun
            (.bvar (TShape.WF.T.2 hwe.2.2.1) (TShape.LE.refl (TShape.WF.T.2 hwe.2.2.1)))
            (.entry q hq ⟨hwg.2.2.2, hwe.2.1⟩
              (TShape.LE.refl (TShape.WF.T.2 hwe.2.2.1)))
            (TShape.WF.T.2 hwe.2.2.2) (TShape.LE.refl (TShape.WF.T.2 hwe.2.2.2)) hstable
        · -- and it dominates `m`, the labels being definitionally equal
          refine TShape.LE.trans hΔ hle ?_
          exact TShape.LE.T.2 ⟨ShapeFun.LE.refl hwg.2.2.1, hwg.1, hwg.2.1, hAσ, hwg.2.2.2⟩
  | @sg _ n A' B' d f _ cs hty hent hfst hin hev hout =>
    -- an approximant of a Π is never typed at a Σ code
    rcases hpi with hb | hpi'
    · exact absurd hb (TShape.IsSigma.not_bot
        (p := Shape.T (n := n+1) (ShapeS.sigma A' B' d f)) trivial)
    · exact absurd trivial (TShape.IsPi.not_sigma hpi')

/-- **η**, the easy direction: an approximant of the expansion is one of
`e`.  Each entry's body is a lookup in a λ-approximant of `e` one binder
up, `Interp.unweak` brings it down, directedness puts one approximant
above them all, and the lookup-coverage order (§5.2) is what lets the
expansion's graph be covered by it — an entry's output is a *join* of
outputs, which entry-by-entry coverage could not reach. -/
theorem sound_eta_to {Γ : List Term} {A B e : Term} {u : Bool} (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A : .sort u) (he : Γ ⊢ e : .forallE A B)
    (ihety : SoundTy Γ e (.forallE A B)) (ihedir : SoundDir Γ e)
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {m : TShape} (hm : Interp Δ Γ (.lam A (.app e.lift (.bvar 0))) σ ρ m) :
    Interp Δ Γ e σ ρ m := by
  have hwρ := hAdm.wf
  cases hm with
  | bot => exact .bot
  | @lam _ _ _ _ n g d _ _ hdA hdty hwf _ hbody hw hle hAt =>
    -- each entry's body is an application of `e` one binder up
    have hent : ∀ q ∈ g, ∃ (k : Nat) (Aq : Term) (gq : ShapeFun k) (xq : TShape),
        Interp Δ Γ e σ ρ (Shape.T (n := k+1) (ShapeS.lam Aq gq)) ∧
        TShape.LE Δ xq q.inp.T ∧
        TEvaluates Δ gq Aq q.tm xq q.out.T := by
      intro q hq
      have hb := hbody q hq
      generalize hqo : (q.out.T : TShape) = mo at hb
      cases hb with
      | bot =>
        -- a well-formed λ-shape has no `⊥` output
        refine absurd (hwf.2.1 q hq) (fun h => h ?_)
        obtain ⟨qtm, qinp, qout⟩ := q
        cases n with
        | zero => cases qout <;> first | trivial | cases hqo
        | succ n => cases qout <;> first | trivial | cases hqo
      | @app _ _ _ _ _ _ k gq xq y Aq hF hx hev hwy hley hst =>
        refine ⟨k, Aq, gq, xq, ?_, ?_, ?_⟩
        · -- the function, one binder down
          exact Interp.unweak_slot hΔ hΓ (.skip .refl) he.annot.1
            (.cons W hA (hwf.2.2.1.1 q hq).2.1) hF
        · exact Interp.le_bvar (i := 0) (ρ := ρ.push q.inp.T) hx
        · subst hqo
          exact .lower hley (by simpa using hev)
    -- per entry, a λ-approximant of `e` whose lookup covers that entry
    have hent' : ∀ q ∈ g, ∃ E : TShape, Interp Δ Γ e σ ρ E ∧ E.IsLam ∧
        ∀ {k : Nat} {A' : Term} {G : ShapeFun k},
          TShape.LE Δ E (Shape.T (n := k+1) (ShapeS.lam A' G)) →
          Shape.WF (n := k+1) Δ (ShapeS.lam A' G) →
          TEvaluates Δ G (A.subst σ) q.tm q.inp.T q.out.T := by
      intro q hq
      obtain ⟨k, Aq, gq, xq, hEq, hxle, hev⟩ := hent q hq
      refine ⟨_, hEq, trivial, ?_⟩
      intro k' A' G hEle hwG
      have hcov := TShape.LE.lam_decomp hΔ hEle hEq.wf hwG (TEvaluates.refl hwG.2.2.1)
      have h2 := TEvaluates.mono_inp hΔ hxle (TEvaluates.trans hΔ hcov hev)
      refine TEvaluates.label ?_ h2
      have hAq : TyEq Δ Aq (A.subst σ) := Interp.lam_label_ty hΔ W hAdm ihety hEq
      exact ⟨hAq, hAq.symm.choose_spec.defeqDF (hwf.2.2.1.1 q hq).2.1⟩
    -- one approximant of `e` above all of them
    obtain ⟨g₀, hmap, hall⟩ := List.exists_pairs hent'
    obtain ⟨E, hwE, hE, hleE⟩ :=
      Interp.Dir.list hΔ (ihedir hΔ W hwρ) (ms := Prod.snd) g₀ (fun p hp => (hall p hp).1)
    -- it is a λ-shape, dominating one
    obtain ⟨q₀, hq₀⟩ : ∃ q, q ∈ g := by
      cases g with
      | nil => exact absurd rfl hwf.1
      | cons q g' => exact ⟨q, .head _⟩
    obtain ⟨p₀, hp₀, hp₀eq⟩ : ∃ p ∈ g₀, p.1 = q₀ := by
      have : q₀ ∈ g₀.map Prod.fst := by rw [hmap]; exact hq₀
      obtain ⟨p, hp, heq⟩ := List.mem_map.1 this
      exact ⟨p, hp, heq⟩
    have hLam : E.IsLam := TShape.isLam_of_le (hleE p₀ hp₀) (hall p₀ hp₀).2.1
    -- so it is `lam A' G`, and every entry of `g` is a lookup in `G`
    obtain ⟨kE, sE⟩ := E
    match kE, sE, hLam with
    | kE+1, .lam A' G, _ =>
      have hwE' : Shape.WF (n := kE+1) Δ (ShapeS.lam A' G) := hwE
      have hcov : ∀ q ∈ g, TEvaluates Δ G (A.subst σ) q.tm q.inp.T q.out.T := by
        intro q hq
        obtain ⟨p, hp, hpeq⟩ : ∃ p ∈ g₀, p.1 = q := by
          have : q ∈ g₀.map Prod.fst := by rw [hmap]; exact hq
          obtain ⟨p, hp, heq⟩ := List.mem_map.1 this
          exact ⟨p, hp, heq⟩
        have := (hall p hp).2.2 (hleE p hp) hwE'
        rw [hpeq] at this
        exact this
      refine Interp.mono hΔ hw (TShape.LE.trans hΔ hle ?_) hE
      -- the comparison, at a level above both graphs
      have hkn : n ≤ max n kE := Nat.le_max_left ..
      have hkE : kE ≤ max n kE := Nat.le_max_right ..
      have hlabE : TyEq Δ A' (A.subst σ) :=
        Interp.lam_label_ty hΔ W hAdm ihety hE
      refine (TShape.LE.def hΔ (Nat.succ_le_succ hkn) (Nat.succ_le_succ hkE)).2 ?_
      refine ⟨⟨?_, (ShapeFun.lift_wf hkn).2 hwf.2.2.1,
          ((ShapeFun.lift_wf hkE).2 hwE'.2.2.1).retype hlabE⟩, ?_, ?_, hlabE.symm, hwf.2.2.2⟩
      · -- the coverage: each entry's output is a lookup in `G`
        intro e he
        obtain ⟨q, hq, rfl⟩ := ShapeFun.mem_lift.1 he
        have h1 := TEvaluates.lift_graph hΔ hkE
          (fun e he => ⟨(hwE'.2.2.1.1 e he).2.2.1, (hwE'.2.2.1.1 e he).2.2.2⟩) (hcov q hq)
        have h2 : TEvaluates Δ (ShapeFun.lift (Shape.lift (max n kE)) G) (A.subst σ) q.tm
            (Shape.T (q.inp.lift (max n kE))) q.out.T :=
          TEvaluates.mono_inp hΔ
            (TShape.LE.le_lift hΔ (m := q.inp.T) hkn (hwf.2.2.1.1 q hq).2.2.1) h1
        obtain ⟨c', hc', hev'⟩ := TEvaluates.toEval hΔ
          (((ShapeFun.lift_wf hkE).2 hwE'.2.2.1).retype hlabE)
          ((Shape.lift_wf hkn).2 (hwf.2.2.1.1 q hq).2.2.1) h2
        refine .lower ?_ hev'
        exact TShape.LE.T.1 (TShape.LE.trans hΔ
          (TShape.LE.lift_le hΔ (m := q.out.T) hkn (hwf.2.2.1.1 q hq).2.2.2) hc')
      · exact fun h => hwf.1 (by
          cases g with
          | nil => rfl
          | cons q g' => exact absurd h (by simp [ShapeFun.lift]))
      · intro e he
        obtain ⟨q, hq, rfl⟩ := ShapeFun.mem_lift.1 he
        exact fun hb => hwf.2.1 q hq ((Shape.lift_isBot hkn).1 hb)

/-- **The §4.7a label invariant.**  Every pair-approximant of `p` is
named by `p`'s *own* first projection.  It is what Σ's η needs, and it
is false for an admissibility that does not ask slots to name their
terms (§4.7i); with `Adm` asking that, it follows from saturation
(`PairCanon.of_dom`). -/
def PairCanon (Δ Γ : List Term) (σ : Subst) (ρ : Valuation) (p : Term) : Prop :=
  ∀ {n} {A₀ a₀ : Term} {x y : Shape n},
    Interp Δ Γ p σ ρ (Shape.T (n := n+1) (ShapeS.pair A₀ a₀ x y)) →
    Δ ⊢ a₀ ≡ (Term.fst p).subst σ : A₀

/-- **Pair names come from saturation**: a pair-approximant sits below
the saturated one, which names `fst p`, and the order compares names. -/
theorem PairCanon.of_dom {Γ : List Term} {A B p : Term} (h : SoundDom Γ p (.sigma A B))
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ) :
    PairCanon Δ Γ σ ρ p := by
  intro n A₀ a₀ x y hP
  obtain ⟨P', _, _, hle, _, hNV, _⟩ := h hΔ W hAdm hP
  have hcan := hNV.val
  obtain ⟨k, A', a', x', y', rfl⟩ := TShape.LE.pair_ub hle
  obtain ⟨hAA, haa, _, _⟩ := TShape.LE.pair_decomp hΔ hle
  exact haa.trans (hAA.choose_spec.symm.defeqDF hcan.1)

/-- **Σ's η, the hard direction**: an approximant of `p` is one of
`⟨fst p, snd p⟩`.  Saturation hands a pair-approximant `P` above it; its
first component is an approximant of `fst p` by the `fst` clause, and its
second is one of `snd p` by the `snd` clause — which fires exactly
because `P`'s *name* is `fst p`.  So the expansion's pair is rebuilt on
`P`'s own components, and it dominates what `P` dominated. -/
theorem sound_fst_snd_of {Γ : List Term} {A B p : Term} {u v : Bool} (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) (hp : Γ ⊢ p : .sigma A B)
    (ihpty : SoundTy Γ p (.sigma A B)) (ihpdom : SoundDom Γ p (.sigma A B))
    (ihBdir : SoundDir (A :: Γ) B)
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    {m : TShape} (hm : Interp Δ Γ p σ ρ m) :
    Interp Δ Γ (.pair A B (.fst p) (.snd p)) σ ρ m := by
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
  have hwρ := hAdm.wf
  have hfst : Γ ⊢ .fst p : A := .fstDF hA hB hp
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  have hfσ : Δ ⊢ (Term.fst p).subst σ : A.subst σ := hfst.subst hΔ W
  obtain ⟨P, S, hP, hle, hS, hNV, hScan⟩ := ihpdom hΔ W hAdm hm
  have hPdom := hNV.dom
  have hPcan := hNV.val
  -- `⊥` is an approximant of anything
  have hbot : m.2 = Shape.bot → Interp Δ Γ (.pair A B (.fst p) (.snd p)) σ ρ m := by
    intro hb
    obtain ⟨k, s⟩ := m
    cases k with
    | zero => cases s with
      | bot => exact .bot
      | sort r => exact absurd hb (by simp [Shape.bot])
    | succ k => cases s <;> first | exact .bot | exact absurd hb (by simp [Shape.bot])
  have hSsg : S.2 = Shape.bot ∨ S.IsSigma := by
    cases hS with
    | bot => exact .inl rfl
    | sigma _ _ _ _ _ _ hles _ _ => exact TShape.isSigma_or_bot_of_le hles trivial
  cases hPdom with
  | base hnb hty =>
    rcases hSsg with hb | hsg
    · exact hbot (TShape.le_bot hΔ (TShape.HasType.bot_r hΔ hb hty) hle)
    · exact absurd hsg.isBinder hnb
  | pi _ _ _ _ =>
    rcases hSsg with hb | hsg
    · exact absurd hb (TShape.IsPi.not_bot (p := Shape.T _) trivial)
    · exact absurd hsg (TShape.IsPi.not_sigma trivial)
  | @sg _ nS A' B' dS fS _ ps cc hty hps _ hxd' hevc hout =>
    cases hty with
    | bot hb => exact hbot (TShape.le_bot hΔ rfl hle)
    | refl hleid hAty' =>
      exact absurd hleid (by
        intro h
        obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ h
        exact absurd h2 (fun x => x))
    | @pair nP _ A₀ a₀ x y _ _ _ _ _ _ hd hfo hwP hwSg hxd hxle hev hyty hlabP =>
      -- the Σ-code, decomposed
      cases hS with
      | @sigma _ _ _ _ nc gc dc _ _ hAint hdty hwfc _ hbodyc hwmc hleSg =>
        obtain ⟨hSgLab, hdle, hcov⟩ :=
          TShape.LE.sigma_decomp hΔ hleSg hwSg hwfc (TEvaluates.refl hwfc.2.2.2.1)
        have hxw : TShape.WF Δ (Shape.T x) := TShape.WF.T.2 hwP.2.2.2.1
        have hyw : TShape.WF Δ (Shape.T y) := TShape.WF.T.2 hwP.2.2.2.2
        have hAlab : TyEq Δ A₀ (A.subst σ) := Interp.pair_label_ty hΔ W hAdm ihpty hP
        -- the name is the subject's own first projection
        have hname : Δ ⊢ a₀ ≡ (Term.fst p).subst σ : A₀ := hPcan.1
        -- the two components are the projections' approximants
        have hxI : Interp Δ Γ (.fst p) σ ρ (Shape.T x) := .fst hP hxw (TShape.LE.refl hxw)
        have hyI : Interp Δ Γ (.snd p) σ ρ (Shape.T y) :=
          .snd hP hname hyw (TShape.LE.refl hyw) (Stable.of_typed hfst hAlab)
        -- the code for `B[fst p]`, read at the pair's own name
        have hIc : Interp Δ (A :: Γ) B (σ.cons ((Term.fst p).subst σ))
            (ρ.push (Shape.T x)) cc := by
          refine Interp.stage hΔ hΓA hB.annot.1
            (Ctx.SubstEq.cons (σ := σ.cons a₀) W hA ?_) ?_
          · exact hAlab.choose_spec.defeqDF hname
          · refine sound_graph_lookup hΓA hA hB hΔ W hbodyc hxw ihBdir hwρ
              (show Δ ⊢ a₀ : A' from hlabP.choose_spec.defeqDF hwP.2.1)
              hSgLab.1 (TEvaluates.trans hΔ hcov (hevc _ (by rw [← hps]; rfl)))
        -- the expansion's pair, on the dominator's own components
        have hwf : Shape.WF (n := nP+1) Δ
            (ShapeS.pair (A.subst σ) ((Term.fst p).subst σ) x y) :=
          ⟨hwP.1, hfσ, TyEq.refl hAσ, hwP.2.2.2.1, hwP.2.2.2.2⟩
        have hwf' : TShape.WF Δ (Shape.T (n := nP+1) _) := TShape.WF.T.2 hwf
        refine Interp.pair (c := cc) hxI hyI
          (Interp.mono hΔ (TShape.HasType.wf hd).1 hdle hAint)
          (TShape.HasType.mono_l hΔ hdty hdle)
          (.of_dom (by simpa using hxd' _ (show _ ∈ _ by rw [← hps]; rfl)) hPcan.2.1)
          (Shape.CodeCanonS.conv (Shape.WFO.canon hwSg.2.2.1) (TyEq.symm hSgLab.1))
          hwf hIc (by simpa using hout _ (show _ ∈ _ by rw [← hps]; rfl))
          hm.wf ?_ ⟨u, hA⟩ hfst
        · -- and it dominates `m`, the name moved to `fst p`
          refine TShape.LE.trans hΔ hle (TShape.LE.T.2
            (show Shape.LE (n := nP+1) Δ (ShapeS.pair ..) (ShapeS.pair ..) from
              ⟨Shape.LE.refl hwP.2.2.2.1, Shape.LE.refl hwP.2.2.2.2, hwP.1, hAlab, hname⟩))

/-- **Σ's η, the easy direction**: an approximant of `⟨fst p, snd p⟩` is
one of `p`.  With the graph gone this is true, where with it it was not
(§4.7e): the expansion's pair has no inputs to promise a second
component at, so its two components are approximants of the projections
and nothing more.  Each comes from a pair-approximant of `p`; one
directedness step puts both under a single one, whose name is `fst p`
by canonicity, and the order then compares. -/
theorem sound_fst_snd_to {Γ : List Term} {A B p : Term} {u v : Bool}
    (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) (hp : Γ ⊢ p : .sigma A B)
    (ihpty : SoundTy Γ p (.sigma A B)) (ihpdir : SoundDir Γ p)
    {Δ Γ₀ : List Term} {σ ρ} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    (hcanon : PairCanon Δ Γ σ ρ p)
    {m : TShape} (hm : Interp Δ Γ (.pair A B (.fst p) (.snd p)) σ ρ m) :
    Interp Δ Γ p σ ρ m := by
  have hwρ := hAdm.wf
  have hfst : Γ ⊢ .fst p : A := .fstDF hA hB hp
  cases hm with
  | bot => exact .bot
  | @pair _ _ _ _ n x y _ _ _ _ _ _ hx hy _ _ _ _ hwf _ _ hw hle _ _ =>
    -- the two components come from two pair-approximants of `p`
    cases hx with
    | bot =>
      cases hy with
      | bot => exact absurd ⟨Shape.isBot_bot, Shape.isBot_bot⟩ hwf.1
      | snd hP₂ hlab₂ hw₂ hle₂ hst₂ =>
        refine Interp.mono hΔ hw (TShape.LE.trans hΔ hle ?_) hP₂
        have hAP := Interp.pair_label_ty hΔ W hAdm ihpty hP₂
        exact TShape.LE.pair_mk hΔ (TShape.bot_le' rfl) hle₂ hwf.1 (TyEq.symm hAP)
          (hAP.choose_spec.defeqDF (hcanon hP₂).symm)
    | fst hP₁ hwx hlex =>
      cases hy with
      | bot =>
        refine Interp.mono hΔ hw (TShape.LE.trans hΔ hle ?_) hP₁
        have hAP := Interp.pair_label_ty hΔ W hAdm ihpty hP₁
        exact TShape.LE.pair_mk hΔ hlex (TShape.bot_le' rfl) hwf.1 (TyEq.symm hAP)
          (hAP.choose_spec.defeqDF (hcanon hP₁).symm)
      | snd hP₂ hlab₂ hwy hley hst₂ =>
        -- one pair-approximant above both
        obtain ⟨P, hwP, hP, hleP₁, hleP₂⟩ := ihpdir hΔ W hwρ hP₁ hP₂
        obtain ⟨k, A', a', x', y', rfl⟩ := TShape.LE.pair_ub hleP₁
        obtain ⟨_, _, hx₁, _⟩ := TShape.LE.pair_decomp hΔ hleP₁
        obtain ⟨_, _, _, hy₂⟩ := TShape.LE.pair_decomp hΔ hleP₂
        refine Interp.mono hΔ hw (TShape.LE.trans hΔ hle ?_) hP
        have hAP := Interp.pair_label_ty hΔ W hAdm ihpty hP
        exact TShape.LE.pair_mk hΔ (TShape.LE.trans hΔ hlex hx₁)
          (TShape.LE.trans hΔ hley hy₂) hwf.1 (TyEq.symm hAP)
          (hAP.choose_spec.defeqDF (hcanon hP).symm)

/-- The four conclusions proved by the induction itself.  `Sound` adds
saturation on top, which is where the remaining work is (§4.5g). -/
theorem IsDefEq.sound {Γ : List Term} {t t' A : Term}
    (hΓ : ⊢ Γ) (H : Γ ⊢ t ≡ t' : A) : Sound Γ t t' A := by
  induction H with
  -- structural rules: no stage or valuation changes, so these are pure
  -- bookkeeping on the two conclusions
  | @symm _ _ _ _ hs ih =>
    have ⟨he, hty, hpL, hpR, hd⟩ := ih hΓ
    exact ⟨he.symm, SoundTy.of_eq hs he hty, hpR, hpL, SoundDom.of_eq hs he hd⟩
  | trans _ _ ih₁ ih₂ =>
    have ⟨he₁, hty₁, hp₁, _, hd₁⟩ := ih₁ hΓ
    have ⟨he₂, _, _, hp₂, _⟩ := ih₂ hΓ
    exact ⟨he₁.trans he₂, hty₁, hp₁, hp₂, hd₁⟩
  | trans' _ _ ih₁ ih₂ =>
    have ⟨he₁, hty₁, hp₁, _, hd₁⟩ := ih₁ hΓ
    have ⟨he₂, _, _, hp₂, _⟩ := ih₂ hΓ
    exact ⟨he₁.trans he₂, hty₁, hp₁, hp₂, hd₁⟩
  -- conversion: only the *type*'s interpretation moves, and `SoundEq` of
  -- the two types is exactly what moves it
  | @defeqDF _ _ _ _ _ _ hAB _ ihAB ih =>
    have ⟨heAB, _, _, _, _⟩ := ihAB hΓ
    have ⟨he, hty, hpL, hpR, hd⟩ := ih hΓ
    refine ⟨he, ⟨hAB.defeqDF hty.typed, ?_⟩, hpL, hpR, SoundDom.of_tyEq hAB heAB hd⟩
    intro Δ Γ₀ σ ρ hΔ W hA m hm
    have ⟨a, ha, hht⟩ := hty.approx hΔ W hA hm
    exact ⟨a, (heAB hΔ W hA).1 ha, hht⟩
  -- everything below is one rule of the induction, each an independent
  -- obligation; see §4 of `presheaf-proof-strategy.md` for what each needs
  -- the slot's typing is `Adm`'s own, read off at the index by `Adm.lookup`
  | @bvar _ _ _ _ hl hA _ =>
    refine ⟨SoundEq.refl, ⟨.bvar hl hA, ?_⟩, trivial, trivial, SoundDom.bvar hl⟩
    intro Δ Γ₀ σ ρ hΔ W hAdm m hm
    obtain ⟨a, ha, hty⟩ := hAdm.lookup hΓ hl
    refine ⟨a, ha, TShape.HasType.mono_l hΔ hty ?_⟩
    cases hm with
    | bot => exact TShape.bot_le' rfl
    | bvar _ hle => exact hle
  | sort =>
    exact and_pinned_filter (sound_atom .sort Interp.le_sort Interp.sort' .sort)
      trivial trivial (fun ha => TShape.not_binder_of_le (Interp.le_sort ha) (fun h => h))
      CodeAt.sort CodeAt.sort
  | @unit _ r =>
    exact and_pinned_filter
      (sound_atom .unit Interp.le_unit Interp.sort' (.unit (fun x => x)))
      trivial trivial (fun ha => TShape.not_binder_of_le (Interp.le_sort ha) (fun h => h))
      CodeAt.unit CodeAt.sort
  | star =>
    exact and_pinned (sound_of_bot .star (fun .bot => rfl) (fun .bot => rfl))
      trivial trivial (SoundDom.of_bot (by intro _ _ _ _ _ _ _ _ h; cases h; rfl))
  -- the lookup, typed: `SoundEq` moves the query's term along `a ≡ a'`,
  -- and `SoundTy` walks the generator chain of `HasType.lam`
  | @appDF _ A u B v f f' a a' hA hB hff' haa' hBinst ihA ihB ihf iha ihBinst =>
    have hΓA : ⊢ (A :: _) := ⟨hΓ, _, hA.hasType.1⟩
    have ⟨hef, htyf, hpf, hpf', hd_ihf⟩ := ihf hΓ
    have ⟨hea, htya, hpa, hpa', hd_iha⟩ := iha hΓ
    exact ⟨sound_app_eq hff' haa' htyf hef hea,
      SoundTy.of_dom (.appDF hA hB hff'.hasType.1 haa'.hasType.1 hBinst.hasType.1)
        (sound_app_dom (ihB hΓA).pin hΓ hA.hasType.1 hB.hasType.1 haa'.hasType.1 hd_iha htyf hd_ihf (ihBinst hΓ).ty (ihBinst hΓ).dom
          (IsDefEq.dir hΓ haa').1 (IsDefEq.dir hΓA hB).1),
      ⟨PinApp.of_sound htyf haa'.hasType.1, hpf, hpa⟩,
      ⟨PinApp.of_sound (SoundTy.of_eq hff' hef htyf) haa'.hasType.2, hpf', hpa'⟩,
      sound_app_dom (ihB hΓA).pin hΓ hA.hasType.1 hB.hasType.1 haa'.hasType.1 hd_iha htyf hd_ihf (ihBinst hΓ).ty (ihBinst hΓ).dom
        (IsDefEq.dir hΓ haa').1 (IsDefEq.dir hΓA hB).1⟩
  | @lamDF _ A A' u B v body body' hAA' hB hbody hbody' hPi ihA ihB ihbody ihbody' ihPi =>
    have hΓA : ⊢ (A :: _) := ⟨hΓ, _, hAA'.hasType.1⟩
    have hΓA' : ⊢ (A' :: _) := ⟨hΓ, _, hAA'.hasType.2⟩
    have ⟨heA, htyA, hpA, hpA', hd_ihA⟩ := ihA hΓ
    exact ⟨sound_lam_eq hAA' heA hd_ihA (ihbody hΓA).eq (ihbody' hΓA').eq,
      SoundTy.of_dom (IsDefEq.lamDF hAA' hB hbody hbody' hPi).hasType.1
        (sound_lam_dom hΓ hAA'.hasType.1 hB hbody.hasType.1 hd_ihA (ihB hΓA).ty
          (ihB hΓA).dom.codeAt (ihbody hΓA).dom (IsDefEq.dir hΓA hbody).1
          (IsDefEq.dir hΓA hB).1),
      ⟨htyA.isTypeAt hd_ihA, hpA, (ihbody hΓA).pin⟩,
      ⟨(SoundTy.of_eq hAA' heA htyA).isTypeAt (SoundDom.of_eq hAA' heA hd_ihA), hpA',
        (ihbody' hΓA').pin'⟩,
      sound_lam_dom hΓ hAA'.hasType.1 hB hbody.hasType.1 hd_ihA (ihB hΓA).ty
        (ihB hΓA).dom.codeAt (ihbody hΓA).dom (IsDefEq.dir hΓA hbody).1
        (IsDefEq.dir hΓA hB).1⟩
  -- the two halves proved above
  | forallEDF hAA' hB hB' ihA ihB ihB' =>
    have ⟨heA, htyA, hpA, hpA', hd_ihA⟩ := ihA hΓ
    have ⟨heB, htyB, hpB, _, hd_ihB⟩ := ihB ⟨hΓ, _, hAA'.hasType.1⟩
    have ⟨heB', _, _, hpB', hd_ihB'⟩ := ihB' ⟨hΓ, _, hAA'.hasType.2⟩
    exact ⟨sound_forallE_eq hAA' hB hB' heA hd_ihA heB heB',
      sound_forallE_ty hd_ihA htyB hAA'.hasType.1,
      ⟨htyA.isTypeAt hd_ihA, hpA, hpB⟩,
      ⟨(SoundTy.of_eq hAA' heA htyA).isTypeAt (SoundDom.of_eq hAA' heA hd_ihA), hpA', hpB'⟩,
      SoundDom.of_sort (sound_forallE_ty hd_ihA htyB hAA'.hasType.1).typedAt
        (CodeAt.forallE hAA'.hasType.1 hB.hasType.1)⟩
  -- Σ now has real rules, mirroring Π, so these are no longer vacuous
  | sigmaDF hAA' hB hB' ihA ihB ihB' =>
    have ⟨heA, htyA, hpA, hpA', hd_ihA⟩ := ihA hΓ
    have ⟨heB, htyB, hpB, _, hd_ihB⟩ := ihB ⟨hΓ, _, hAA'.hasType.1⟩
    have ⟨heB', _, _, hpB', hd_ihB'⟩ := ihB' ⟨hΓ, _, hAA'.hasType.2⟩
    exact ⟨sound_sigma_eq hAA' hB hB' heA hd_ihA heB heB',
      sound_sigma_ty hd_ihA htyB hAA'.hasType.1,
      ⟨htyA.isTypeAt hd_ihA, hpA, hpB⟩,
      ⟨(SoundTy.of_eq hAA' heA htyA).isTypeAt (SoundDom.of_eq hAA' heA hd_ihA), hpA', hpB'⟩,
      SoundDom.of_sort (sound_sigma_ty hd_ihA htyB hAA'.hasType.1).typedAt
        (CodeAt.sigma hAA'.hasType.1 hB.hasType.1)⟩
  | @pairDF _ A A' u B v B' a a' b b' hAA' hB hB' haa' hbb' hBa hSg
      ihA ihB ihB' iha ihb ihBa ihSg =>
    have hΓA : ⊢ (A :: _) := ⟨hΓ, _, hAA'.hasType.1⟩
    have hΓA' : ⊢ (A' :: _) := ⟨hΓ, _, hAA'.hasType.2⟩
    have ⟨heA, htyA, hpA, hpA', hd_ihA⟩ := ihA hΓ
    have ⟨_, _, hpB, _, hd_ihB⟩ := ihB hΓA
    have ⟨_, _, _, hpB', hd_ihB'⟩ := ihB' hΓA'
    have ⟨hea, htya, hpa, hpa', hd_iha⟩ := iha hΓ
    have ⟨_, _, hpb, hpb', hd_ihb⟩ := ihb hΓ
    exact ⟨sound_pair_eq hAA' haa' hB.hasType.1 hB'.hasType.2 heA hea (ihb hΓ).eq
        (ihB hΓA).eq (ihB' hΓA').eq,
      sound_pair_ty hΓ hAA'.hasType.1 hB.hasType.1
        (IsDefEq.pairDF hAA' hB hB' haa' hbb' hBa hSg).hasType.1
        htyA hd_ihA.codeAt (IsDefEq.dir hΓ hAA').1 htya (ihB hΓA).ty hd_ihB.codeAt
        (IsDefEq.dir hΓA hB).1,
      ⟨htyA.isTypeAt hd_ihA, hpA, hpB, hpa, hpb⟩,
      ⟨(SoundTy.of_eq hAA' heA htyA).isTypeAt (SoundDom.of_eq hAA' heA hd_ihA), hpA', hpB',
        hpa', hpb'⟩,
      sound_pair_dom hΓ hAA'.hasType.1 hB.hasType.1 haa'.hasType.1 hbb'.hasType.1 hpB
        htyA hd_ihA (IsDefEq.dir hΓ hAA').1 htya hd_iha (IsDefEq.dir hΓ haa').1 hd_ihb
        (ihB hΓA).ty hd_ihB.codeAt (IsDefEq.dir hΓA hB).1⟩
  | fstDF hA hB _ _ _ ih =>
    have ⟨he, hty, hp, hp', hd⟩ := ih hΓ
    exact and_pinned (sound_fst hA hB he hty) hp hp' (sound_fst_dom hd)
  | @sndDF _ A u B v p p' hA hB hpp' hBfst ihA ihB ihp ihBfst =>
    have hΓA : ⊢ (A :: _) := ⟨hΓ, _, hA.hasType.1⟩
    have hfst := IsDefEq.fstDF hA hB hpp'.hasType.1
    have ⟨hep, htyp, hpp, hpp2, hd_ihp⟩ := ihp hΓ
    exact ⟨sound_snd_eq hA hB hpp' htyp hep,
      SoundTy.of_dom (.sndDF hA hB hpp'.hasType.1 hBfst.hasType.1)
        (sound_snd_dom (ihB hΓA).pin hΓ hA hB hfst
          (sound_fst_dom hd_ihp) htyp hd_ihp (ihBfst hΓ).dom
          (IsDefEq.dir hΓ hfst).1 (IsDefEq.dir hΓA hB).1),
      ⟨PinSnd.of_sound htyp hfst, hpp⟩,
      ⟨PinSnd.of_sound (SoundTy.of_eq hpp' hep htyp)
        (IsDefEq.fstDF hA hB hpp'.hasType.2), hpp2⟩,
      sound_snd_dom (ihB hΓA).pin hΓ hA hB hfst
        (sound_fst_dom hd_ihp) htyp hd_ihp (ihBfst hΓ).dom
        (IsDefEq.dir hΓ hfst).1 (IsDefEq.dir hΓA hB).1⟩
  -- padded with typings of both sides, so `SoundTy` is the IH for the
  -- left-hand side and only `SoundEq` has content
  | @beta _ A u e B e' hA hbe he' hredex _ ihA ihe ihe' ihredex ihrhs =>
    have hΓA : ⊢ (A :: _) := ⟨hΓ, _, hA.hasType.1⟩
    exact ⟨sound_beta (ihe hΓA).pin hΓ hA.hasType.1 hbe.hasType.1
        he'.hasType.1 (ihA hΓ).ty (ihe' hΓ).dom
        (IsDefEq.dir hΓ he').1 (IsDefEq.dir hΓA hbe).1,
      (ihredex hΓ).ty, (ihredex hΓ).pin, (ihrhs hΓ).pin, (ihredex hΓ).dom⟩
  | @eta _ A B e he hexp ihe ihexp =>
    obtain ⟨v, hPi⟩ := IsDefEq.isType hΓ he
    obtain ⟨u, hA⟩ := hPi.forallE_dom
    refine ⟨fun Δ Γ₀ σ ρ hΔ W hAdm m => ⟨fun h => ?_, fun h => ?_⟩,
      (ihexp hΓ).ty, (ihexp hΓ).pin, (ihe hΓ).pin, (ihexp hΓ).dom⟩
    · exact sound_eta_to hΓ hA he.hasType.1 (ihe hΓ).ty (IsDefEq.dir hΓ he).1
        hΔ W hAdm h
    · exact sound_eta_of hΓ hA (ihe hΓ).dom hΔ W hAdm h
  | @unit_eta _ _ r _ ih =>
    refine and_pinned (sound_of_bot_at
      (sound_of_bot (t := .star r) (t' := .star r) (A := .unit r) .star
        (fun .bot => rfl) (fun .bot => rfl)).2
      (by intro _ _ _ _ _ _ _ _ h; cases h; rfl)
      (by intro _ _ _ _ hΔ W hAdm _ h; exact Interp.eq_bot_of_unit (ih hΓ).ty hΔ W hAdm h))
      trivial (ih hΓ).pin (SoundDom.of_bot (by intro _ _ _ _ _ _ _ _ h; cases h; rfl))
  -- unblocked by the Σ rules: `fst` now reads the first component off a
  -- pair shape, so the two sides really can have the same approximants
  -- the β-rules of Σ: the projection's approximants are the component's,
  -- and the typing then comes from the component's by `SoundTy.of_eq`
  | @pair_fst _ A u B v a b hA hB ha hb hfst ihA _ iha _ ihlhs =>
    have he := sound_pair_fst (B := B) (b := b) hA.hasType.1 ha.hasType.1
      (ihA hΓ).ty (iha hΓ).dom
    exact ⟨he, SoundTy.of_eq (.symm (.pair_fst hA hB ha hb hfst)) he.symm (iha hΓ).ty,
      (ihlhs hΓ).pin, (iha hΓ).pin, (ihlhs hΓ).dom⟩
  | @pair_snd _ A u B v a b hA hB ha hb hsnd ihA ihB iha ihb ihlhs =>
    -- `snd`'s rule is a query at `fst`, so this case needs the β-rule for
    -- `fst` as well, which its own premises give
    have hpair := IsDefEq.pairDF hA hB hB ha hb
      (IsDefEq.inst_cod hΓ hA.hasType.1 ha.hasType.1 hB) (IsDefEq.sigmaDF hA hB hB)
    have hfst := IsDefEq.pair_fst hA.hasType.1 hB.hasType.1 ha.hasType.1 hb.hasType.1
      (IsDefEq.fstDF hA.hasType.1 hB.hasType.1 hpair)
    have he := sound_pair_snd (B := B) (v := v) hΓ hA.hasType.1 hB.hasType.1
      ha.hasType.1 (ihB ⟨hΓ, _, hA.hasType.1⟩).pin
      hfst
      (ihA hΓ).ty (iha hΓ).dom (ihb hΓ).dom
      (IsDefEq.dir hΓ ha).1
    exact ⟨he, SoundTy.of_eq (.symm (.pair_snd hA hB ha hb hsnd)) he.symm (ihb hΓ).ty,
      (ihlhs hΓ).pin, (ihb hΓ).pin, (ihlhs hΓ).dom⟩
  | @fst_snd Γ p A B hp hpair ihp ihpair =>
    -- both directions of Σ's η, against the one condition the model does
    -- not yet give: a pair-approximant's name is the subject's own first
    -- projection (§4.7a, `PairCanon`)
    obtain ⟨hAty, hpA, hpB, hpa, hpb⟩ := (ihpair hΓ).pin
    have hSg := (hp.isType hΓ).choose_spec
    obtain ⟨u, hA⟩ := IsDefEq.sigma_dom hSg
    obtain ⟨v, hB⟩ := IsDefEq.sigma_cod hSg
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
    have he : SoundEq Γ (.pair A B (.fst p) (.snd p)) p := by
      intro Δ Γ₀ σ ρ hΔ W hAdm m
      -- a pair-approximant's name is the subject's own first projection,
      -- because the saturated one names it (§4.7i)
      exact ⟨sound_fst_snd_to hA hB hp (ihp hΓ).ty (IsDefEq.dir hΓ hp).1 hΔ W hAdm
          (PairCanon.of_dom (ihp hΓ).dom hΔ W hAdm),
        sound_fst_snd_of hΓ hA hB hp (ihp hΓ).ty (ihp hΓ).dom
          (IsDefEq.dir hΓA hB).1 hΔ W hAdm⟩
    exact ⟨he, (ihpair hΓ).ty, (ihpair hΓ).pin, (ihp hΓ).pin, (ihpair hΓ).dom⟩
  | nat =>
    exact and_pinned_filter (sound_atom .nat Interp.le_nat Interp.sort' .nat)
      trivial trivial (fun ha => TShape.not_binder_of_le (Interp.le_sort ha) (fun h => h))
      CodeAt.nat CodeAt.sort
  | zero =>
    exact and_pinned_filter (sound_atom .zero Interp.le_zero Interp.nat' .zero)
      trivial trivial (fun ha => TShape.not_binder_of_le (Interp.le_nat ha) (fun h => h))
      (CodeAt.of_nat TypedAt.zero) CodeAt.nat
  | succDF _ ih =>
    have ⟨he, hty, hp, hp', _⟩ := ih hΓ
    exact and_pinned_filter (sound_succ he hty) hp hp'
      (fun ha => TShape.not_binder_of_le (Interp.le_nat ha) (fun h => h))
      (CodeAt.of_nat (sound_succ he hty).2.typedAt) CodeAt.nat
  | @natCaseDF _ v C C' M M' a a' b b' hCC' hMM' haa' hbb' hCM ihC ihM iha ihb ihCM =>
    have hΓN : ⊢ (Term.nat :: _) := ⟨hΓ, _, .nat⟩
    have ⟨heM, htyM, hpM, hpM', hd_ihM⟩ := ihM hΓ
    have ⟨_, _, hpC, hpC', hd_ihC⟩ := ihC hΓN
    have ⟨_, _, hpa, hpa', hd_iha⟩ := iha hΓ
    have ⟨_, _, hpb, hpb', hd_ihb⟩ := ihb hΓN
    exact ⟨sound_natCase hMM' heM htyM (iha hΓ).eq (ihb hΓN).eq,
      SoundTy.of_dom (IsDefEq.natCaseDF hCC' hMM' haa' hbb' hCM).hasType.1
        (sound_natCase_dom hΓ (ihC hΓN).pin hCC'.hasType.1 haa'.hasType.1 hbb'.hasType.1
          (ihCM hΓ).dom (iha hΓ).dom (ihb hΓN).dom
          htyM hd_ihM (IsDefEq.dir hΓ hMM').1),
      ⟨htyM.typedAt, hpC, hpM, hpa, hpb⟩,
      ⟨(SoundTy.of_eq hMM' heM htyM).typedAt, hpC', hpM', hpa', hpb'⟩,
      sound_natCase_dom hΓ (ihC hΓN).pin hCC'.hasType.1 haa'.hasType.1 hbb'.hasType.1
        (ihCM hΓ).dom (iha hΓ).dom (ihb hΓN).dom
        htyM hd_ihM (IsDefEq.dir hΓ hMM').1⟩
  -- the computation rules again: padded, so `SoundTy` is an IH
  | natCase_zero _ _ _ _ _ iha _ ihredex =>
    exact ⟨sound_natCase_zero, (ihredex hΓ).ty,
      (ihredex hΓ).pin, (iha hΓ).pin, (ihredex hΓ).dom⟩
  | @natCase_succ _ C v n a b _ hn _ hb _ _ _ ihn _ ihb ihredex ihrhs =>
    exact ⟨sound_natCase_succ (ihb ⟨hΓ, _, .nat⟩).pin hΓ hn.hasType.1 hb.hasType.1 (ihn hΓ).dom (IsDefEq.dir hΓ hn).1,
      (ihredex hΓ).ty, (ihredex hΓ).pin, (ihrhs hΓ).pin, (ihredex hΓ).dom⟩
  | @YDF _ A A' u b b' hAA' hb hb' ihA ihb ihb' =>
    have hΓA : ⊢ (A :: _) := ⟨hΓ, _, hAA'.hasType.1⟩
    have hΓA' : ⊢ (A' :: _) := ⟨hΓ, _, hAA'.hasType.2⟩
    have hYY' : _ ⊢ Term.Y A b ≡ Term.Y A' b' : A := .YDF hAA' hb hb'
    have ⟨heA, htyA, hpA, hpA', hd_ihA⟩ := ihA hΓ
    have htyA' := SoundTy.of_eq hAA' heA htyA
    have htyb' := SoundTy.of_eq hb' (ihb' hΓA').eq (ihb' hΓA').ty
    have hYty := sound_Y_ty hΓ hAA'.hasType.1 hYY'.hasType.1 htyA (ihb hΓA).ty
    have hYty' := sound_Y_ty hΓ hAA'.hasType.2
      (IsDefEq.YDF hAA'.hasType.2 hb'.hasType.2 hb'.hasType.2) htyA' htyb'
    exact ⟨sound_Y_eq hΓ hAA' hYY' hb hb' heA htyA
        (ihb hΓA).ty (ihb hΓA).eq htyb' (ihb' hΓA').eq.symm,
      hYty,
      ⟨htyA.isTypeAt hd_ihA, hYty.typedAt, hpA, (ihb hΓA).pin⟩,
      ⟨htyA'.isTypeAt (SoundDom.of_eq hAA' heA hd_ihA), hYty'.typedAt, hpA', (ihb' hΓA').pin'⟩,
      sound_Y_dom hΓ hAA'.hasType.1 hYY'.hasType.1 htyA hb.hasType.1 (ihb hΓA).dom⟩
  | @Y_unfold _ A u b hA hb hY hunf ihA ihb ihY ihrhs =>
    exact ⟨sound_Y_unfold hΓ (ihb ⟨hΓ, _, hA.hasType.1⟩).pin
        hA.hasType.1 hb.hasType.1 hY.hasType.1 (ihA hΓ).ty
        (ihY hΓ).dom (IsDefEq.dir hΓ hY).1,
      (ihY hΓ).ty, (ihY hΓ).pin, (ihrhs hΓ).pin, (ihY hΓ).dom⟩
  | idDF hAA' haa' hbb' ihA iha ihb =>
    exact and_pinned_filter (sound_id hAA' haa' hbb')
      ⟨(ihA hΓ).pin, (iha hΓ).pin, (ihb hΓ).pin⟩
      ⟨(ihA hΓ).pin', (iha hΓ).pin', (ihb hΓ).pin'⟩
      (fun ha => TShape.not_binder_of_le (Interp.le_sort ha) (fun h => h))
      (CodeAt.id hAA'.hasType.1 haa'.hasType.1 hbb'.hasType.1) CodeAt.sort
  | reflDF hA haa' hid _ iha _ =>
    exact and_pinned_filter (sound_refl hA haa' hid) (iha hΓ).pin
      (iha hΓ).pin' (fun ha => TShape.not_binder_of_le (Interp.le_id ha) (fun h => h))
      CodeAt.refl (CodeAt.id hA haa'.hasType.1 haa'.hasType.1)
  | @trDF _ A A' u a a' b b' v C C' X X' r H H' hAA' haa' hbb' hC hC' hXX' hHH' hCb hid
      ihA iha ihb ihC ihC' ihX ihH =>
    have hΓA : ⊢ (A :: _) := ⟨hΓ, _, hAA'.hasType.1⟩
    have hΓA' : ⊢ (A' :: _) := ⟨hΓ, _, hAA'.hasType.2⟩
    have ⟨heA, htyA, hpA, hpA', hd_ihA⟩ := ihA hΓ
    have ⟨_, _, hpa, hpa', hd_iha⟩ := iha hΓ
    have ⟨_, _, hpb, hpb', hd_ihb⟩ := ihb hΓ
    have ⟨_, _, hpC, _, hd_ihC⟩ := ihC hΓA
    have ⟨_, _, _, hpC', hd_ihC'⟩ := ihC' hΓA'
    have ⟨_, _, hpX, hpX', hd_ihX⟩ := ihX hΓ
    have ⟨_, _, hpH, hpH', hd_ihH⟩ := ihH hΓ
    exact ⟨sound_tr_eq hΓ hAA' haa' hbb' hC hC' hXX' hHH' heA (iha hΓ).eq
        (ihb hΓ).eq (ihC hΓA).eq (ihC' hΓA').eq (ihX hΓ).eq,
      SoundTy.of_dom
        (IsDefEq.trDF hAA' haa' hbb' hC hC' hXX' hHH' hCb hid).hasType.1
        (sound_tr_dom hΓ hpC hAA'.hasType.1 haa'.hasType.1 hbb'.hasType.1 hC.hasType.1
          hXX'.hasType.1 hHH'.hasType.1 (ihb hΓ).dom (IsDefEq.dir hΓ hbb').1),
      ⟨htyA.isTypeAt hd_ihA, hpA, hpa, hpb, hpC, hpX, hpH⟩,
      ⟨(SoundTy.of_eq hAA' heA htyA).isTypeAt (SoundDom.of_eq hAA' heA hd_ihA), hpA', hpa',
        hpb', hpC', hpX', hpH'⟩,
      sound_tr_dom hΓ hpC hAA'.hasType.1 haa'.hasType.1 hbb'.hasType.1 hC.hasType.1
        hXX'.hasType.1 hHH'.hasType.1 (ihb hΓ).dom
        (IsDefEq.dir hΓ hbb').1⟩
  | @tr_refl _ A u a v C X r hA ha hC hx htr ihA iha ihC ihx ihtr =>
    exact ⟨sound_tr_refl_eq (ihC ⟨hΓ, _, hA⟩).pin hΓ hA ha hC (iha hΓ).dom (IsDefEq.dir hΓ ha).1
        (ihC ⟨hΓ, _, hA⟩).ty (ihx hΓ).dom,
      (ihtr hΓ).ty, (ihtr hΓ).pin, (ihx hΓ).pin, (ihtr hΓ).dom⟩
  -- both sides are typed at a proposition, so both collapse to `⊥`
  | proofIrrel _ _ _ ih₁ ih₂ ih₃ =>
    refine and_pinned (sound_of_bot_at (ih₂ hΓ).ty
      (by intro _ _ _ _ hΔ W hAdm _ h
          exact Interp.eq_bot_of_prop (ih₁ hΓ).ty (ih₂ hΓ).ty hΔ W hAdm h)
      (by intro _ _ _ _ hΔ W hAdm _ h
          exact Interp.eq_bot_of_prop (ih₁ hΓ).ty (ih₃ hΓ).ty hΔ W hAdm h))
      (ih₂ hΓ).pin (ih₃ hΓ).pin
      (SoundDom.of_bot (by
        intro _ _ _ _ hΔ W hAdm _ h
        exact Interp.eq_bot_of_prop (ih₁ hΓ).ty (ih₂ hΓ).ty hΔ W hAdm h))

/-- **Saturation.**  Every approximant of a well-typed term is below one
that is hereditarily typed: the original's `HasFixedness`
(`rawExtend ⟦A⟧ ⟦t⟧ = ⟦t⟧`), read through "ideal = set of approximants".
It is the fifth conclusion of the induction above, and it has to be
*that* -- not a theorem of its own -- because the slot discipline makes
the other four depend on it: η needs it at the function, `Interp.lam`'s
slot needs it at the argument, and `Adm` needs it at every variable. -/
theorem IsDefEq.soundDom {Γ : List Term} {t A : Term} (hΓ : ⊢ Γ) (ht : Γ ⊢ t : A) :
    SoundDom Γ t A := (IsDefEq.sound hΓ ht).dom

/-- **Every well-typed term is pinned.**  This was the development's last
assumption before saturation; it is the third conclusion of the induction
above, which is where the original proves its `HasFixedness` too -- a
field of `RawTermProperties`, alongside substitution. -/
theorem IsDefEq.pinned {Γ : List Term} {t T : Term} (hΓ : ⊢ Γ) (ht : Γ ⊢ t : T) :
    t.Pinned Γ := (IsDefEq.sound hΓ ht).pin
