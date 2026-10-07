import DomainSemantics.Consequences
import DomainSemantics.Strong
import DomainSemantics.Inversion

/-! # The axiom board

Every claim the library makes, axiom-checked at build time via
`#guard_msgs`. Any `sorryAx` or project-specific axiom in a dependency
would change a printed axiom list and fail the build, so a successful
`lake build` *is* the validation step. There are no `sorry`s and no
project axioms.

The headline theorems are stated for `IsDefEq₀` (`⊢₀`), the judgment of
`Term.lean`'s rule list, rather than for the instrumented `IsDefEq` (`⊢`)
the proof runs on; `IsDefEq.iff` is what licenses that, and is guarded
here too. The internals below are the model's own machinery.

What is **not** claimed is consistency: `Y` inhabits every type at every
sort, which with `Type : Type` is deliberate. The non-triviality claim is
about the *equational* theory, and `zero_ne_succ_zero` and `not_UIP` are
its witnesses. -/

open DomainSemantics

/-! ## The headline theorems -/

-- **Soundness**: the labelled domain interpretation respects definitional
-- equality.  Five conclusions in one induction (equality, typing, both
-- `Pinned`s, saturation), every rule, Σ's η included.
/-- info: 'DomainSemantics.IsDefEq.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsDefEq.sound

-- **Equivalence of judgments**: the instrumented `IsDefEq` and the standard
-- `IsDefEq₀` prove the same equalities, so everything below transfers.
/-- info: 'DomainSemantics.IsDefEq.iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsDefEq.iff

-- **Π-injectivity**: defeq function types have defeq domains and codomains.
/-- info: 'DomainSemantics.forallE_inv'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms forallE_inv'

-- **Sort injectivity**: definitionally equal sorts sit at the same level.
/-- info: 'DomainSemantics.sort_inv'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sort_inv'

-- **No confusion**, one of fifteen: a sort is never a function type.
/-- info: 'DomainSemantics.sort_forallE_inv'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sort_forallE_inv'

-- **Type uniqueness**: any two types of a term are definitionally equal.
/-- info: 'DomainSemantics.IsDefEq.uniq'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsDefEq.uniq'

-- **Sort uniqueness**: the middle sort levels of a `trans'` step coincide.
/-- info: 'DomainSemantics.IsDefEq.uniq_sort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsDefEq.uniq_sort

-- **Subject reduction**: a weak-head step preserves the term's type.
/-- info: 'DomainSemantics.WHRed.subject_red'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WHRed.subject_red'

-- **Progress**: a closed well-typed term is a value or takes a weak-head step.
/-- info: 'DomainSemantics.progress'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progress'

-- **Non-degeneracy**: two closed terms of one type that are *not* equal,
-- so the equational theory is not the total relation.
/-- info: 'DomainSemantics.zero_ne_succ_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zero_ne_succ_zero

-- **Definitional UIP is false**: not all proofs of a (proof-relevant) identity are equal.
/-- info: 'DomainSemantics.not_UIP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms not_UIP

/-! ## The model's internals -/

-- **The subject join**: two compatible shapes at one type join there.
/-- info: 'DomainSemantics.TShape.HasType.join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms TShape.HasType.join

-- **Join-closure of a type's extension** (`SoundJoin`), once and for all.
-- Nothing applies it: the proof reaches `TShape.HasType.join` directly at
-- every point where the plan expected to need join-closure, so this is the
-- §5.1 milestone standing on its own, not a load-bearing lemma.
/-- info: 'DomainSemantics.sound_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sound_join

-- **Strengthening**: an interpretation moves into a smaller context, the
-- clauses' premises coming back from the term's annotations.  This was
-- choice-free until the clauses started carrying `TShape.Named`:
-- building one at a Σ moves the name along the pair label's `TyEq`,
-- whose witness is a `choose_spec`.
/-- info: 'DomainSemantics.Interp.unweak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Interp.unweak

-- **Stage invariance**: the labels move with the stage, each clause
-- carrying what its own need.
/-- info: 'DomainSemantics.Interp.stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Interp.stage

-- **Substitution in the term**, both directions, and **clean**: the
-- semantic side conditions are hypotheses (`Term.Pinned`), as the
-- original's are.
/-- info: 'DomainSemantics.Interp.substTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Interp.substTerm

/-- info: 'DomainSemantics.Interp.inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Interp.inst

-- **The third conclusion of soundness**: every well-typed term is
-- pinned, so `to_substTerm`'s clause conditions are a theorem.
/-- info: 'DomainSemantics.IsDefEq.pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsDefEq.pinned

-- **The proof-irrelevant transport**: it computes by K, so a transport
-- whose endpoints differ at the stage has no information.
/-- info: 'DomainSemantics.Interp.tr_bot_of_ne' depends on axioms: [propext] -/
#guard_msgs in #print axioms Interp.tr_bot_of_ne

-- **Saturation**, what the slot discipline runs on, with names: a
-- conclusion of the soundness induction.
/-- info: 'DomainSemantics.IsDefEq.soundDom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsDefEq.soundDom

-- **Directedness** — every case proved, and nothing left under it: `dir`
-- never instantiates, and the joined slot it builds is hereditarily
-- typed by `TShape.Dom.join`, so it needs no saturation.
/-- info: 'DomainSemantics.IsDefEq.dir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsDefEq.dir

-- **Σ's η**: a pair-approximant is named by the subject's first
-- projection, because the saturated one is.
/-- info: 'DomainSemantics.PairCanon.of_dom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PairCanon.of_dom

-- **Type uniqueness** from the labelled model, syntactic and semantic halves.
/-- info: 'DomainSemantics.StrongSound.uniq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms StrongSound.uniq

-- **A stuck transport has no information**: `tr false nat zero (succ zero)
-- nat zero h` computes by no rule, because its endpoints are not equal,
-- and the `tr` clause asks for them to be equal at the stage.  This used
-- to assume `zero ≢ succ zero`; `zero_ne_succ` is now a theorem.
/-- info: 'DomainSemantics.Interp.tr_stuck_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Interp.tr_stuck_bot

-- **The two merges are faithful.**  `Named` is hereditary typing and
-- naming in one induction, and it is exactly their conjunction; `Slot`
-- is that together with the code's own naming, and is exactly the three
-- facts a valuation slot was always asked for.
/-- info: 'DomainSemantics.TShape.Named.iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms TShape.Named.iff

/-- info: 'DomainSemantics.TShape.Slot.iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms TShape.Slot.iff
