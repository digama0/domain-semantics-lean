import DomainSemantics.Strong
import DomainSemantics.Inversion
import DomainSemantics.Counterexample

/-! # Where the labelled model stands

The axiom board for the presheaf line, checked at build time, as
`DomainSemantics.lean` is for the old one.  The two cannot be one file:
`Shape` and `ShapeOld` both define `DomainSemantics.Shape`, so the two
models are separate roots.
-/

open DomainSemantics

/-!
**No `sorry` remains in the labelled model.**  Soundness
(`IsDefEq.sound`) is proved for every rule, Σ's η (`fst_snd`) included.

What closed `fst_snd` (§4.7i) is a change to admissibility, not a proof
trick: `Adm` now asks every slot to **name the term it stands for**
(`TShape.ValCanon`: a pair is named by the term's first projection, its
components name the projections, a λ's outputs name the applications),
and its code to name the slot's type (`TShape.CodeCanon`).  Without it
the η-equation is false (`Counterexample.lean`: the old witness is now
excluded, `ce_not_adm`).  The names propagate as a sixth piece of
saturation: `SoundDom` concludes that the dominator names the term and
its code names the type.  The transport that made this look impossible
(§4.7d) is `ValCanon.defeq`, which moves a name along a definitional
equality of the subject *through the code the value is typed at*, so no
inversion is needed.  Two clauses changed with it: the binders, pair, `Y`
and `tr` clauses carry their slots' names, and `tr` at `r = true` asks
for its proof to *be* `refl` at the stage (a `refl`-shaped slot under a
stuck transport would pass on names of the wrong term).

**η is proved** (`sound_eta_of`, `sound_eta_to`), and so is Σ's η
(`sound_fst_snd_of`, `sound_fst_snd_to`, with `PairCanon.of_dom`).

**Saturation is proved** (`IsDefEq.soundDom`), as a conclusion of the
soundness induction -- the original's `HasFixedness` read through
"ideal = set of approximants", now with names.

**Stage invariance and strengthening are theorems** (`Interp.stage`,
`Interp.unweak`), `IsDefEq.dir` is clean, and so is the substitution
half (`Interp.to_substTerm`, `Interp.substTerm`).

The one remaining `sorry` of the repository is in the *old* model:
`LR.adequacy`'s `r = false` transport (`Adequacy.lean`), false for that
model with `LE_Interp.tr_stuck` as the witness; it is guarded on the
other root, since the two models cannot be imported together. -/

-- **The subject join**: two compatible shapes at one type join there.
/-- info: 'DomainSemantics.TShape.HasType.join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms TShape.HasType.join

-- **Join-closure of a type's extension** (`SoundJoin`), once and for all.
/-- info: 'DomainSemantics.sound_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sound_join

-- **Strengthening**: an interpretation moves into a smaller context, the
-- clauses' premises coming back from the term's annotations.
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

-- **Soundness** of the labelled model, five conclusions in one
-- induction (equality, typing, both `Pinned`s, saturation), every rule.
/-- info: 'DomainSemantics.IsDefEq.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsDefEq.sound

-- **Σ's η**: a pair-approximant is named by the subject's first
-- projection, because the saturated one is.
/-- info: 'DomainSemantics.PairCanon.of_dom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PairCanon.of_dom

-- **Type uniqueness** from the labelled model, syntactic and semantic halves.
/-- info: 'DomainSemantics.StrongSound.uniq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms StrongSound.uniq

-- **The old admissibility's witness is excluded**: well formed and
-- hereditarily typed, but not named by the variable it stands for.
/-- info: 'DomainSemantics.ce_not_adm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ce_not_adm
