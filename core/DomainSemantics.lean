import DomainSemantics.Consequences

/-! The headline theorems of the library, axiom-checked at build time
via `#guard_msgs`. Any `sorryAx` or project-specific axiom in a
dependency would change the printed axiom list and fail the build. -/

open DomainSemantics

-- **Soundness**: the domain interpretation respects definitional equality.
/-- info: 'DomainSemantics.LE_Interp.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LE_Interp.sound

-- **Adequacy**: every well-typed term is realised by the logical relation.
/-- info: 'DomainSemantics.LR.adequacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LR.adequacy

-- **Π-injectivity**: defeq function types have defeq domains and codomains.
/-- info: 'DomainSemantics.forallE_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms forallE_inv

-- **Sort injectivity**: definitionally equal sorts sit at the same level.
/-- info: 'DomainSemantics.sort_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sort_inv

-- **Type uniqueness**: any two types of a term are definitionally equal.
/-- info: 'DomainSemantics.HasType.uniq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HasType.uniq

-- **Sort uniqueness**: the middle sort levels of a `trans'` step coincide.
/-- info: 'DomainSemantics.IsDefEq.uniq_sort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsDefEq.uniq_sort

-- **Equivalence of judgments**: the instrumented `IsDefEq` and the standard `IsDefEq₀` prove the same equalities.
/-- info: 'DomainSemantics.IsDefEq.iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsDefEq.iff

-- **Subject reduction**: a weak-head step preserves the term's type.
/-- info: 'DomainSemantics.WHRed.subject_red' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WHRed.subject_red

-- **Progress**: a closed well-typed term is a value or takes a weak-head step.
/-- info: 'DomainSemantics.progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progress
