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

**It should not be assumed at all**, and the original proof does not.
There (`/project/presheaf-semantics-lean`) substitution is a field of
`RawTermProperties`, proved inside the soundness induction, and its `app`
case consumes `HasFixedness Γ f (Π A B)`: the function's *value* is a
value of the Π-type, which forces every non-`⊥` response of its graph to
sit at a genuine point of the domain (`outputAtom_rawPi_fixed_support`).
That is the link, and it is semantic, not syntactic.  Here the same
ingredient is `Interp.lam_label_ty`, which needs `SoundTy Γ f (Π A B)` —
available only inside `IsDefEq.sound`.  Hoisting `to_substTerm` out of
that induction is what made this assumption necessary; putting it back
removes it.  §3.1d of `presheaf-proof-strategy.md`.
-/

namespace DomainSemantics

/-- **Uniqueness of types up to definitional equality.**  The one
syntactic fact assumed on this root; see the file header. -/
theorem IsDefEq.uniq {Γ : List Term} {a T₁ T₂ : Term} (hΓ : ⊢ Γ)
    (h₁ : Γ ⊢ a : T₁) (h₂ : Γ ⊢ a : T₂) : TyEq Γ T₁ T₂ := by
  sorry
