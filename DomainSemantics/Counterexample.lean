import DomainSemantics.Presheaf

/-! # The slot that refuted the old admissibility

Before §4.7i, `Adm` asked a slot to be well formed and hereditarily
typed, and nothing more.  That made Σ's η false: in `Γ = [Σ nat nat]`
the valuation whose only slot is

    pair nat nat (succ zero) zero zero

was admissible (nothing related a pair's **name** to the variable it
stands for), it was an approximant of `#0`, and it was not one of
`⟨fst #0, snd #0⟩`, whose approximants are all named `fst #0`.  The
machine-checked refutation is commit `248147c`.

`Adm` now also asks every slot to name the term it stands for
(`TShape.ValCanon`), and soundness holds, Σ's η included.  This file
keeps the witness and shows where it stands now: it is still well formed
and hereditarily typed at a Σ-code (`ce_dom`), but it is **not
admissible** (`ce_not_adm`), and the conjunct it fails is exactly the
name.  The non-equation `succ zero ≢ fst #0` that the old refutation took
as a hypothesis is now a corollary of soundness (`ce_ne`). -/

namespace DomainSemantics

/-- The context: one variable of type `Σ nat nat`. -/
abbrev ceΓ : List Term := [Term.sigma .nat .nat]

/-- The misnamed slot: components `zero` and `zero`, but named
`succ zero` rather than `fst #0`. -/
abbrev ceSlot : TShape :=
  Shape.T (n := 2) (ShapeS.pair .nat (.succ .zero) (Shape.zero) (Shape.zero))

/-- The Σ-code it is typed at: domain `nat`, and a codomain graph with a
single entry at the slot's own name. -/
abbrev ceCode : TShape :=
  Shape.T (n := 2) (ShapeS.sigma .nat .nat (Shape.nat)
    [⟨.nat, .succ .zero, Shape.zero, Shape.nat⟩])

/-- The valuation: the misnamed slot, and `⊥` elsewhere. -/
abbrev ceρ : Valuation := Valuation.nil.push ceSlot

/-! ## The slot is well formed and hereditarily typed -/

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
    ?_ ?_ ?_ ?_ (TShape.WF.T.2 hwSg) (TShape.LE.refl (TShape.WF.T.2 hwSg))
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
    | head => trivial
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

/-- The slot is an approximant of the variable: the `bvar` clause asks
only for well-formedness and the order. -/
theorem ce_interp_bvar : Interp ceΓ ceΓ (.bvar 0) Subst.id ceρ ceSlot :=
  .bvar ce_wf_slot (TShape.LE.refl ce_wf_slot)

/-! ## The name is what it gets wrong -/

/-- `succ zero ≢ fst #0`: if they were equal they would have the same
approximants at the all-`⊥` valuation, where `#0`, hence `fst #0`, has
only `⊥` while `succ zero` has its own shape. -/
theorem ce_ne : ¬ (ceΓ ⊢ Term.succ .zero ≡ Term.fst (.bvar 0) : .nat) := by
  intro hD
  have hwz : TShape.WF ceΓ (Shape.T (n := 1) Shape.zero) := TShape.WF.T.2 trivial
  have hws : TShape.WF ceΓ (Shape.T (n := 2) (Shape.succ (Shape.zero))) :=
    TShape.WF.T.2 trivial
  have hs : Interp ceΓ ceΓ (.succ .zero) Subst.id Valuation.nil
      (Shape.T (n := 2) (Shape.succ (Shape.zero))) :=
    .succ (.zero hwz (TShape.LE.refl hwz)) hws (TShape.LE.refl hws)
  have h := ((IsDefEq.sound ce_wfΓ hD).eq ce_wfΓ (Ctx.SubstEq.id ce_wfΓ) Adm.bot).1 hs
  cases h with
  | fst hp _ hle =>
    cases hp with
    | bvar _ hlep =>
      exact absurd (TShape.le_bot ce_wfΓ rfl hlep) (by simp [Shape.bot])

/-- **The old witness is not admissible**: its slot would have to name
`#0`, i.e. be named `fst #0`, and it is named `succ zero`. -/
theorem ce_not_adm : ¬ Adm ceΓ ceΓ ceΓ Subst.id ceρ := by
  intro h
  obtain ⟨_, _, _, _, hname⟩ := h.lookupCanon (i := 0) Lookup.zero
  exact ce_ne hname.1
