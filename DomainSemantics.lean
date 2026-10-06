import DomainSemantics.Consequences
import DomainSemantics.Status

/-! The headline theorems of the library, axiom-checked at build time
via `#guard_msgs`. Any `sorryAx` or project-specific axiom in a
dependency would change the printed axiom list and fail the build.

These are stated for `IsDefEq₀` (`⊢₀`), the judgment of `Term.lean`'s
rule list, rather than for the instrumented `IsDefEq` (`⊢`) the proof
runs on; `IsDefEq.iff` is what licenses that, and is guarded here too.
`DomainSemantics/Status.lean` is the board for the model's internals. -/

open DomainSemantics

-- **Soundness**: the labelled domain interpretation respects definitional equality.
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
