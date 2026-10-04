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
`Soundness/SingleSubstitution.lean`).

**And translating that pair is not mechanical**, which is worth knowing
before trying.  There the `Γ`-side valuation *is* the interpretation of
`θ` — an ideal, hence a single object, and admissible by construction.
Here it is an approximant the `∃` picks, and **admissibility is not
upward closed**: enlarging a valuation breaks its slots' typings, since
typing is a lower set.  So the obvious repair — enlarge the reconstructed
valuation until it hosts the type-approximants `Adm` asks for — does not
terminate: each enlargement needs the new slots typed, whose types are
read at a bigger valuation again.  `Adm` being a predicate on slots
(rather than the old inductive) is what makes joins and enlargements
expressible at all, so it is the right base to try from; what is missing
is a reason for the process to close.

Where it is tractable: at `Interp.inst`, the one use that matters, the
`Γ`-side valuation is `ρ.push x` with `ρ` already admissible, and `x` can
be chosen typed among `a`'s approximants (`SoundTy Γ a A` and
directedness).  So a form of the substitution lemma specialised to
`one a` — the original's `SingleSubstitution`, which is also only ever
used there — may well close where the general one does not.
-/

namespace DomainSemantics

/-- **Every well-typed term is pinned**; see the file header. -/
theorem IsDefEq.pinned {Γ : List Term} {t T : Term} (hΓ : ⊢ Γ) (ht : Γ ⊢ t : T) :
    t.Pinned Γ := by
  sorry
