import DomainSemantics.Interp

/-! # The third conclusion of soundness, assumed

`Interp.to_substTerm` needs two semantic facts that the term does not
say: `IsTypeAt` at a binder and `PinApp`/`PinSnd` at an eliminator, both
gathered by `Term.Pinned`.  In the original they are fields of
`RawTermProperties` (`HasIdeality`, `HasFixedness`), proved in the same
induction as soundness, and `HasSubstitution.app` consumes them there.

Here they are assumed, as one statement: **every well-typed term is
pinned.**  That is exactly the third conclusion `IsDefEq.sound` is
missing, and discharging it is the remaining translation step (§3.1d of
`presheaf-proof-strategy.md`).  It replaces the earlier assumption of
uniqueness of types, which was a detour: with `Pinned` threaded, the
`app` and `snd` cases of `to_substTerm` read their label link off the
hypothesis instead of reconstructing it syntactically.

What proving it inside the induction still needs, over and above the
present machinery: the valuation `to_substTerm` *builds* has to be
admissible whenever the source one is, since `SoundTy` is stated at
admissible stages and the transport of a subterm's `SoundTy` across `θ`
reads it there.  That is the original's `SourceAdmissible`/
`SingleSubstitution` pair (`Soundness/Admissible.lean`,
`Soundness/SingleSubstitution.lean`), and it is the next piece to
translate.  The two places it bites are the `natCase_succ` and `Y`
clauses, whose binder slot is not an entry input and so is typed only
through the scrutinee's — resp. the tower's — own `SoundTy`.
-/

namespace DomainSemantics

/-- **Every well-typed term is pinned**; see the file header. -/
theorem IsDefEq.pinned {Γ : List Term} {t T : Term} (hΓ : ⊢ Γ) (ht : Γ ⊢ t : T) :
    t.Pinned Γ := by
  sorry
