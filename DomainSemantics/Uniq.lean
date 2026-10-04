import DomainSemantics.Label

/-! # Uniqueness of types, assumed here

The labelled model needs one syntactic fact that this root cannot yet
prove: **a term has at most one type, up to definitional equality.**

It is needed in exactly one place, `Stable.transfers`
(`Interp.lean`): an `app` or `snd` clause's label types the query, and
`Interp.to_substTerm` has to recognise that label as the image of the
*argument's own type* in the smaller context.  Those are two types of one
term, so the link is uniqueness and nothing else.

Why it is true, and why it is a `sorry` here:

* It is the standard meta-theorem for this judgement, and it is proved in
  this repository — `HasType.uniq` in `Consequences.lean`, by induction
  on a bundled structural typing judgement whose only external inputs are
  the `sort` and Π inversions.
* That proof lives on the **other root**: its inversions come from
  `Adequacy.lean`, the context-free model, which `LE_Interp.tr_stuck`
  shows is wrong at a stuck transport.  So it cannot be imported here,
  and re-deriving the inversions is what this root exists for.
* Here the inversions come from soundness (`Inversion.lean`), soundness
  needs `Interp.inst`, and `inst` needs `to_substTerm`.  So assuming
  uniqueness at this point is circular *as a proof*, not as a statement:
  nothing below depends on the labelled model, and the model is not being
  used to prove it.

Discharging it means either re-proving `HasType.uniq`'s inversions
syntactically, or annotating `Term.app` with its domain, after which the
`app` clause's label is pinned by the syntax and `Stable.transfers` needs
no uniqueness at all (§3.1c of `presheaf-proof-strategy.md`).
-/

namespace DomainSemantics

/-- **Uniqueness of types up to definitional equality.**  The one
syntactic fact assumed on this root; see the file header. -/
theorem IsDefEq.uniq {Γ : List Term} {a T₁ T₂ : Term} (hΓ : ⊢ Γ)
    (h₁ : Γ ⊢ a : T₁) (h₂ : Γ ⊢ a : T₂) : TyEq Γ T₁ T₂ := by
  sorry
