import DomainSemantics.UniqueTyping

/-! The headline theorems of the library, axiom-checked at build time
via `#guard_msgs`. Any `sorryAx` or project-specific axiom in a
dependency would change the printed axiom list and fail the build. -/

open DomainSemantics

/-- info: 'DomainSemantics.LE_Interp.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LE_Interp.sound
/-- info: 'DomainSemantics.LR.adequacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LR.adequacy
/-- info: 'DomainSemantics.forallE_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms forallE_inv
/-- info: 'DomainSemantics.sort_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sort_inv
/-- info: 'DomainSemantics.HasType.uniq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HasType.uniq
/-- info: 'DomainSemantics.IsDefEq.uniq_sort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsDefEq.uniq_sort
/-- info: 'DomainSemantics.IsDefEq.iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsDefEq.iff
