import DomainSemantics.Presheaf

/-! # The `fst_snd` case is false as the model stands

`IsDefEq.sound`'s one `sorry` is `PairCanon`: a pair-approximant of `p`
is named by `p`'s own first projection.  This file shows that the
condition — and with it the `fst_snd` case itself — is **false** for the
current `Adm`, not merely unproved.

The witness is §4.7a's, in the form the graph-free Σ-value leaves it: in
`Γ = [Σ nat nat]` the valuation whose only slot is

    pair nat nat (succ zero) zero zero

is well formed and hereditarily typed at a Σ-code, hence *admissible* —
nothing in `Adm` relates a pair's **name** to the variable it stands
for.  It is an approximant of `#0`; it is not an approximant of
`⟨fst #0, snd #0⟩`, whose approximants are all named by `fst #0`.  So
the two terms have different approximant sets, which is what `SoundEq`
denies.

The moral: `fst_snd` needs a change to `Adm` (slots must name their own
projections), not more proof effort.  Everything below is checked; the
only input is the evident non-equation `succ zero ≢ fst #0`, which no
consistent model can validate (`fst #0` is neutral). -/

namespace DomainSemantics

/-- The context: one variable of type `Σ nat nat`. -/
abbrev ceΓ : List Term := [Term.sigma .nat .nat]

/-- The misnamed slot: components `zero` and `zero`, but named
`succ zero` rather than `fst #0`. -/
abbrev ceSlot : TShape :=
  Shape.T (n := 2) (ShapeS.pair .nat .nat (.succ .zero) (Shape.zero) (Shape.zero))

/-- The Σ-code it is typed at: domain `nat`, and a codomain graph with a
single entry at the slot's own name. -/
abbrev ceCode : TShape :=
  Shape.T (n := 2) (ShapeS.sigma .nat .nat (Shape.nat)
    [⟨.nat, .succ .zero, Shape.zero, Shape.nat⟩])

/-- The valuation: the misnamed slot, and `⊥` elsewhere. -/
abbrev ceρ : Valuation := Valuation.nil.push ceSlot

/-! ## The slot is admissible -/

theorem ce_wfΓ : ⊢ ceΓ := ⟨trivial, _, .sigmaDF .nat .nat .nat⟩

theorem ce_wf_slot : TShape.WF ceΓ ceSlot := by
  refine TShape.WF.T.2 ⟨?_, ?_, ?_, trivial, trivial⟩
  · rintro ⟨h, -⟩; exact h
  · exact .succDF (.zero)
  · exact ⟨true, .nat⟩

theorem ce_wfρ : Valuation.WF ceΓ ceρ := by
  intro i
  cases i with
  | zero => exact ce_wf_slot
  | succ i => exact trivial

/-- The Σ-code is an approximant of the type, at the identity stage. -/
theorem ce_code_interp :
    Interp ceΓ ceΓ (Term.sigma .nat .nat) Subst.id ceρ ceCode := by
  have hwg : ShapeFun.WF ceΓ (Shape.WF ceΓ) (n := 1)
      [⟨.nat, .succ .zero, Shape.zero, Shape.nat⟩] := by
    refine ⟨?_, ?_⟩
    · intro e he
      cases he with
      | head => exact ⟨⟨true, .nat⟩, .succDF .zero, trivial, trivial⟩
      | tail _ h => nomatch h
    · intro e he e' he' Θ τ hΘ W _ _
      cases he with
      | tail _ h => nomatch h
      | head =>
        cases he' with
        | tail _ h => nomatch h
        | head => trivial
  have hwSg : Shape.WF (n := 2) ceΓ
      (ShapeS.sigma .nat .nat Shape.nat [⟨.nat, .succ .zero, Shape.zero, Shape.nat⟩]) :=
    ⟨⟨true, .nat⟩, ⟨true, .nat⟩, trivial, hwg⟩
  refine Interp.sigma (d := Shape.nat) (.nat trivial (TShape.LE.refl trivial)) .nat hwSg
    ?_ ?_ ?_ (TShape.WF.T.2 hwSg) (TShape.LE.refl (TShape.WF.T.2 hwSg))
    ⟨true, .nat⟩ ⟨true, .nat⟩
  · intro e he
    cases he with
    | head => exact ⟨true, .nat⟩
    | tail _ h => nomatch h
  · intro e he
    cases he with
    | head => exact TShape.Dom.of_not_binder (fun h => h) (.zero)
    | tail _ h => nomatch h
  · intro e he
    cases he with
    | head => exact .nat trivial (TShape.LE.refl trivial)
    | tail _ h => nomatch h

/-- The graph of the Σ-code, and its well-formedness, reused below. -/
abbrev ceGraph : ShapeFun 1 := [⟨.nat, .succ .zero, Shape.zero, Shape.nat⟩]

theorem ce_wg : ShapeFun.WF ceΓ (Shape.WF ceΓ) ceGraph := by
  refine ⟨?_, ?_⟩
  · intro e he
    cases he with
    | head => exact ⟨⟨true, .nat⟩, .succDF .zero, trivial, trivial⟩
    | tail _ h => nomatch h
  · intro e he e' he' Θ τ hΘ W _ _
    cases he with
    | tail _ h => nomatch h
    | head => cases he' with
      | tail _ h => nomatch h
      | head => trivial

theorem ce_wSg : Shape.WF (n := 2) ceΓ
    (ShapeS.sigma .nat .nat Shape.nat ceGraph) :=
  ⟨⟨true, .nat⟩, ⟨true, .nat⟩, trivial, ce_wg⟩

/-- The lookup that types the second component: at the slot's own name. -/
theorem ce_lookup : TEvaluates ceΓ ceGraph .nat (.succ .zero)
    (Shape.T (n := 1) Shape.zero) (Shape.T (n := 1) Shape.nat) :=
  TEvaluates.entry ⟨.nat, .succ .zero, Shape.zero, Shape.nat⟩ List.mem_cons_self
    ⟨⟨true, .nat⟩, .succDF .zero⟩ (TShape.LE.refl trivial)

/-- The misnamed slot is typed at the Σ-code. -/
theorem ce_hasType : TShape.HasType ceΓ ceSlot ceCode :=
  .pair (d := Shape.nat) (f := ceGraph) .nat
    (fun e he => by cases he with
      | head => exact .nat
      | tail _ h => nomatch h)
    (TShape.WF.T.1 ce_wf_slot) ce_wSg .zero (TShape.LE.refl trivial) ce_lookup .zero
    ⟨true, .nat⟩

/-- And hereditarily so: `Dom` sees nothing wrong with the name either. -/
theorem ce_dom : TShape.Dom ceΓ ceCode ceSlot :=
  .sg (ps := some (.succ .zero, Shape.T (n := 1) Shape.zero,
      Shape.T (n := 1) Shape.zero))
    (c := Shape.T (n := 1) Shape.nat) ce_hasType rfl
    (fun p hp => by cases hp; exact TShape.Dom.of_not_binder (fun h => h) .zero)
    (fun p hp => by cases hp; exact ce_lookup)
    (fun p hp => by cases hp; exact TShape.Dom.of_not_binder (fun h => h) .zero)

/-! ## …and therefore the valuation is admissible -/

theorem ce_adm : Adm ceΓ ceΓ ceΓ Subst.id ceρ := by
  refine ⟨ce_wfρ, ?_⟩
  intro i A hl
  cases hl with
  | zero =>
    refine ⟨ceCode, ?_, ce_dom⟩
    show Interp ceΓ ceΓ ((Term.sigma .nat .nat).lift) Subst.id ceρ ceCode
    simpa [Term.lift, Term.subst] using ce_code_interp
  | succ hl => nomatch hl

/-- The slot is an approximant of the variable: the `bvar` clause asks
only for well-formedness and the order. -/
theorem ce_interp_bvar : Interp ceΓ ceΓ (.bvar 0) Subst.id ceρ ceSlot :=
  .bvar ce_wf_slot (TShape.LE.refl ce_wf_slot)

/-! ## The conclusion: `fst_snd`'s `SoundEq` is false here

Nothing above mentions `fst p` at all — that is the point.  `Adm` asks a
slot to be well formed and hereditarily typed, and this one is; it says
nothing about the slot's *name*, so the name may be any term of the
domain, here `succ zero`.  Every approximant of `⟨fst #0, snd #0⟩`, on
the other hand, is named `fst #0`, because `Interp.pair` puts the
component's own term there.  So the slot separates the two terms. -/
theorem ce_fst_snd_unsound
    (hne : ¬ (ceΓ ⊢ Term.succ .zero ≡ Term.fst (.bvar 0) : .nat)) :
    ¬ SoundEq ceΓ (.pair .nat .nat (.fst (.bvar 0)) (.snd (.bvar 0))) (.bvar 0) := by
  intro hsound
  have h := (hsound ce_wfΓ (Ctx.SubstEq.id ce_wfΓ) ce_adm).2 ce_interp_bvar
  cases h with
  | pair _ _ _ _ _ _ _ _ _ hle _ _ =>
    obtain ⟨_, hname, _, _⟩ := TShape.LE.pair_decomp ce_wfΓ hle
    exact hne (by simpa using hname)

/-- And so the `sorry` it rests on is not merely unproved: `PairCanon`
fails for this valuation. -/
theorem ce_pairCanon_false
    (hne : ¬ (ceΓ ⊢ Term.succ .zero ≡ Term.fst (.bvar 0) : .nat)) :
    ¬ PairCanon ceΓ ceΓ Subst.id ceρ (.bvar 0) := by
  intro h
  exact hne (by simpa using h ce_interp_bvar)

/-! ## The non-equation, from soundness itself

`succ zero ≢ fst #0` needs no appeal to the other model: if soundness
held, the two terms would have the same approximants at the all-`⊥`
valuation, where `#0` has only `⊥`, so `fst #0` has only `⊥`, while
`succ zero` has `succ zero`. -/
theorem ce_ne_of_sound
    (hsound : ∀ {Γ : List Term} {t t' A : Term}, ⊢ Γ → (Γ ⊢ t ≡ t' : A) → SoundEq Γ t t') :
    ¬ (ceΓ ⊢ Term.succ .zero ≡ Term.fst (.bvar 0) : .nat) := by
  intro hD
  -- `succ zero`'s own shape is an approximant of it
  have hwz : TShape.WF ceΓ (Shape.T (n := 1) Shape.zero) := TShape.WF.T.2 trivial
  have hws : TShape.WF ceΓ (Shape.T (n := 2) (Shape.succ (Shape.zero))) :=
    TShape.WF.T.2 trivial
  have hs : Interp ceΓ ceΓ (.succ .zero) Subst.id Valuation.nil
      (Shape.T (n := 2) (Shape.succ (Shape.zero))) :=
    .succ (.zero hwz (TShape.LE.refl hwz)) hws (TShape.LE.refl hws)
  -- so it is one of `fst #0`, at the `⊥` valuation
  have h := (hsound ce_wfΓ hD ce_wfΓ (Ctx.SubstEq.id ce_wfΓ) Adm.bot).1 hs
  -- but `#0` has only `⊥` there, so `fst #0` has only `⊥`
  cases h with
  | fst hp _ hle =>
    cases hp with
    | bvar _ hlep =>
      exact absurd (TShape.le_bot ce_wfΓ rfl hlep) (by simp [Shape.bot])

/-- **The `fst_snd` case of soundness is false**, for the `Adm` the
development has: assuming it, the η-equation and the non-equation it
implies contradict each other at one admissible valuation. -/
theorem ce_sound_false :
    ¬ (∀ {Γ : List Term} {t t' A : Term}, ⊢ Γ → (Γ ⊢ t ≡ t' : A) → SoundEq Γ t t') := by
  intro hsound
  have hp : ceΓ ⊢ Term.bvar 0 : Term.sigma .nat .nat := by
    have := IsDefEq.bvar₀ (Γ := ceΓ) (i := 0) ce_wfΓ Lookup.zero
    simpa [Term.lift, Term.subst] using this
  have hfst : ceΓ ⊢ Term.fst (.bvar 0) : .nat := .fstDF .nat .nat hp
  have hsnd : ceΓ ⊢ Term.snd (.bvar 0) : .nat := by
    have := IsDefEq.sndDF (A := .nat) (B := .nat) .nat .nat hp (by simpa using IsDefEq.nat)
    simpa [Term.inst, Term.subst] using this
  have hpair : ceΓ ⊢ Term.pair .nat .nat (.fst (.bvar 0)) (.snd (.bvar 0)) :
      Term.sigma .nat .nat := by
    refine IsDefEq.pairDF .nat .nat .nat hfst ?_ ?_ ?_
    · simpa [Term.inst, Term.subst] using hsnd
    · simpa [Term.inst, Term.subst] using IsDefEq.nat
    · exact .sigmaDF .nat .nat .nat
  exact ce_fst_snd_unsound (ce_ne_of_sound hsound)
    (hsound ce_wfΓ (IsDefEq.fst_snd hp hpair))

end DomainSemantics
