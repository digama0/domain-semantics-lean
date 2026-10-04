import DomainSemantics.Strong
import DomainSemantics.Inversion

/-! # Where the labelled model stands

The axiom board for the presheaf line, checked at build time, as
`DomainSemantics.lean` is for the old one.  The two cannot be one file:
`Shape` and `ShapeOld` both define `DomainSemantics.Shape`, so the two
models are separate roots.
-/

open DomainSemantics

/-!
Three `sorry`s remain in the whole development, and this board says
which theorems they reach:

* `Interp.to_substTerm` (`Interp.lean`) — the analytic half of
  substitution in the term, and the one place a clause premise has to be
  rebuilt in a *smaller* context.  Every premise but one comes back from
  `Term.Annot`; the exception is `app`'s and `snd`'s label link, which
  says the shape's label types the query.  Rebuilding it at `Γ` from its
  `Γ'` form needs the two to be types of the same term, i.e. uniqueness
  of types — which is downstream of soundness, which needs this lemma.
  It is what `Interp.inst` reaches, and `inst` is what the computation
  rules of `IsDefEq.sound` reach.
* `eta`, `fst_snd` (`IsDefEq.sound`) — the §5.3 decision.
* `LR.adequacy`'s `r = false` transport (`Adequacy.lean`, the old
  model) — false for that model, and `LE_Interp.tr_stuck` is the
  witness; it is guarded on the other root, since the two models cannot
  be imported together.

**Stage invariance and strengthening are theorems** (`Interp.stage`,
`Interp.unweak`), and `IsDefEq.dir` is clean. -/

-- **The subject join**: two compatible shapes at one type join there.
/-- info: 'DomainSemantics.TShape.HasType.join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms TShape.HasType.join

-- **Join-closure of a type's extension** (`SoundJoin`), once and for all.
/-- info: 'DomainSemantics.sound_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sound_join

-- **Strengthening**: an interpretation moves into a smaller context, the
-- clauses' premises coming back from the term's annotations.
/-- info: 'DomainSemantics.Interp.unweak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Interp.unweak

-- **Stage invariance**: the labels move with the stage, each clause
-- carrying what its own need.
/-- info: 'DomainSemantics.Interp.stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Interp.stage

-- **Substitution in the term**, both directions.  `to_substTerm` is the
-- half still open, so both reach it.
/-- info: 'DomainSemantics.Interp.substTerm' depends on axioms: [propext, sorryAx, Quot.sound] -/
#guard_msgs in #print axioms Interp.substTerm

/-- info: 'DomainSemantics.Interp.inst' depends on axioms: [propext, sorryAx, Quot.sound] -/
#guard_msgs in #print axioms Interp.inst

-- **The proof-irrelevant transport**: it computes by K, so a transport
-- whose endpoints differ at the stage has no information.
/-- info: 'DomainSemantics.Interp.tr_bot_of_ne' depends on axioms: [propext] -/
#guard_msgs in #print axioms Interp.tr_bot_of_ne

-- **Directedness** — every case proved, and nothing left under it.
/-- info: 'DomainSemantics.IsDefEq.dir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsDefEq.dir

-- **Soundness** of the labelled model: `to_substTerm`, `eta`, `fst_snd`.
/-- info: 'DomainSemantics.IsDefEq.sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsDefEq.sound

-- **Type uniqueness** from the labelled model, syntactic and semantic halves.
/-- info: 'DomainSemantics.StrongSound.uniq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms StrongSound.uniq
