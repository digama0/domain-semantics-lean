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
Two `sorry`s remain in the whole development, and this board says
which theorems they reach:

* `IsDefEq.soundDom` — **saturation**: every approximant of a well-typed
  term is below a *hereditarily* typed one.  This is the original's
  `HasFixedness` (`rawExtend ⟦A⟧ ⟦t⟧ = ⟦t⟧`) read through "ideal = set of
  approximants", and it is what the slot discipline runs on: `Adm` and
  the six clauses that create a slot now ask for `TShape.Dom`, their
  `SourceAdmissible`.  §4.5g.
* `fst_snd` (`IsDefEq.sound`) — the Σ twin of η, still to do.

**η is proved** (`sound_eta_of`, `sound_eta_to`), which is what the slot
discipline was for: ← reads its typed inputs off the dominating
approximant saturation supplies, and → collects the bodies' function
approximants, bounds them by one (`Interp.Dir.list`) and compares by
lookup coverage (§5.2), `TEvaluates.toEval` bridging back to the
level-indexed order.
* `LR.adequacy`'s `r = false` transport (`Adequacy.lean`, the old
  model) — false for that model, and `LE_Interp.tr_stuck` is the
  witness; it is guarded on the other root, since the two models cannot
  be imported together.

**Stage invariance and strengthening are theorems** (`Interp.stage`,
`Interp.unweak`), `IsDefEq.dir` is clean, and so is the substitution
half: `Interp.to_substTerm` reads its clause conditions off `Term.Pinned`
and the saturation hypothesis, both of which the soundness induction now
supplies (`Subst.Saturates.one`, `IsDefEq.pinned`). -/

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

-- **Substitution in the term**, both directions, and **clean**: the
-- semantic side conditions are hypotheses (`Term.Pinned`), as the
-- original's are.
/-- info: 'DomainSemantics.Interp.substTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Interp.substTerm

/-- info: 'DomainSemantics.Interp.inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Interp.inst

-- **The third conclusion of soundness**: every well-typed term is
-- pinned, so `to_substTerm`'s clause conditions are a theorem.  What it
-- still reaches is only `eta` and `fst_snd`, through the induction it
-- now shares with the other two conclusions.
/--
info: 'DomainSemantics.IsDefEq.pinned' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsDefEq.pinned

-- **The proof-irrelevant transport**: it computes by K, so a transport
-- whose endpoints differ at the stage has no information.
/-- info: 'DomainSemantics.Interp.tr_bot_of_ne' depends on axioms: [propext] -/
#guard_msgs in #print axioms Interp.tr_bot_of_ne

-- **Saturation**, the assumption the slot discipline runs on.
/-- info: 'DomainSemantics.IsDefEq.soundDom' depends on axioms: [propext, sorryAx] -/
#guard_msgs in #print axioms IsDefEq.soundDom

-- **Directedness** — every case proved, and nothing left under it: `dir`
-- never instantiates, and the joined slot it builds is hereditarily
-- typed by `TShape.Dom.join`, so it needs no saturation.
/-- info: 'DomainSemantics.IsDefEq.dir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsDefEq.dir

-- **Soundness** of the labelled model: `to_substTerm`, `eta`, `fst_snd`.
/-- info: 'DomainSemantics.IsDefEq.sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsDefEq.sound

-- **Type uniqueness** from the labelled model, syntactic and semantic halves.
/-- info: 'DomainSemantics.StrongSound.uniq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms StrongSound.uniq
