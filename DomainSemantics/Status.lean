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
Five `sorry`s remain in the whole development, and this board says
which theorems they reach:

* `IsDefEq.stage` (`Presheaf.lean`) — stage invariance.  **Everything
  below that is not clean is clean but for this**: `dir` uses it at the
  graphs' cross pairs, and `sound` through `dir` and
  `sound_graph_lookup`.
* `Interp.unweak` and `Interp.to_substTerm` (`Interp.lean`) — the two
  typing-indexed inductions the stage-invariant clauses ask for.  Each
  clause now carries the premises that make it stage-invariant, so
  these two can be proved by induction on the *typing*; until they are,
  they are what `substTerm` and `inst` reach.
* `eta`, `fst_snd` (`IsDefEq.sound`) — the §5.3 decision.
* `LR.adequacy`'s `r = false` transport (`Adequacy.lean`, the old
  model) — false for that model, and `LE_Interp.tr_stuck` is the
  witness; it is guarded on the other root, since the two models cannot
  be imported together. -/

-- **The subject join**: two compatible shapes at one type join there.
/-- info: 'DomainSemantics.TShape.HasType.join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms TShape.HasType.join

-- **Join-closure of a type's extension** (`SoundJoin`), once and for all.
/-- info: 'DomainSemantics.sound_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sound_join

-- **Substitution in the term**, both directions.  `to_substTerm` is the
-- induction still open, so both reach it.
/-- info: 'DomainSemantics.Interp.substTerm' depends on axioms: [propext, sorryAx, Quot.sound] -/
#guard_msgs in #print axioms Interp.substTerm

/-- info: 'DomainSemantics.Interp.inst' depends on axioms: [propext, sorryAx, Quot.sound] -/
#guard_msgs in #print axioms Interp.inst

-- **The proof-irrelevant transport**: it computes by K, so a transport
-- whose endpoints differ at the stage has no information.
/-- info: 'DomainSemantics.Interp.tr_bot_of_ne' depends on axioms: [propext] -/
#guard_msgs in #print axioms Interp.tr_bot_of_ne

-- **Directedness** — every case proved, `stage` the only axiom reached.
/-- info: 'DomainSemantics.IsDefEq.dir' depends on axioms: [propext, sorryAx, Quot.sound] -/
#guard_msgs in #print axioms IsDefEq.dir

-- **Soundness** of the labelled model: `stage`, `eta`, `fst_snd`.
/-- info: 'DomainSemantics.IsDefEq.sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsDefEq.sound

-- **Type uniqueness** from the labelled model, syntactic and semantic halves.
/-- info: 'DomainSemantics.StrongSound.uniq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms StrongSound.uniq
