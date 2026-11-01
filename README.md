# DomainSemantics

A Lean 4 formalisation of a denotational semantics for a dependently
typed λ-calculus with Π, Σ, `Nat`, `Unit`, a proof-relevant identity
type, a fixpoint `Y`, and `Type : Type`. From it come Π-, Σ- and
Id-injectivity, fifteen no-confusion principles, type uniqueness, subject
reduction and progress.

The semantic domain is a level-graded family of "shape" structures,
finite approximations of values, each carrying the **syntactic labels**
of the type or term it approximates. The labels are what glue syntax
into the domain: a function shape's graph is looked up at the label of
the argument, and Π-injectivity is then a projection out of a Π-shape's
label. There is no logical relation and no adequacy theorem; every
syntactic consequence is read off soundness directly.

Admissibility of a valuation asks each slot to **name the term it stands
for**. That is what makes Σ's η true (`TShape.Named` in
`DomainSemantics/HasType.lean`; `design.md` §6 has the witness that
refutes the weaker admissibility).

## Compilation

```sh
lake build
```

Build dependencies — [Lean 4](https://lean-lang.org/) (toolchain pinned
via `lean-toolchain`) and [batteries](https://github.com/leanprover-community/batteries).

To rebuild a single file:

```sh
lake build DomainSemantics.Consequences
```

## Validation

Axiom checks for the eleven headline theorems are baked into the umbrella
file `DomainSemantics.lean` using `#guard_msgs`. They are stated for
`IsDefEq₀` (notation `⊢₀`), the judgment of `DefEq.lean`'s rule list:

* `IsDefEq.sound` — soundness of the interpretation
* `IsDefEq.iff` — the instrumented `IsDefEq` and the standard `IsDefEq₀` agree
* `forallE_inv'` — Π-injectivity
* `sort_inv'` — sort injectivity
* `sort_forallE_inv'` — no confusion (one of fifteen)
* `IsDefEq.uniq'` — type uniqueness
* `IsDefEq.uniq_sort` — sort uniqueness
* `WHRed.subject_red'` — subject reduction for weak-head reduction
* `progress'` — closed well-typed terms are values or step
* `zero_ne_succ_zero` — the equational theory is not the total relation
* `not_UIP` — definitional UIP fails (the identity type is proof-relevant)

Each line pins the expected axiom list to exactly `[propext, Quot.sound]`.
**The development is choice-free**: nothing in it uses `Classical.choice`.
The two places that would have — the sort level hidden inside
`TyEq Δ A A' := ∃ u, Δ ⊢ A ≡ A' : .sort u`, and a case split on whether a
shape is `⊥` — are handled by destructuring the witness instead of
`Exists.choose`, and by splitting on the decidable `Shape.IsBot`.

Any `sorryAx` or project-specific axiom that leaks into a dependency
changes the printed output and fails the build, so a successful
`lake build` is the validation step. There are no `sorry`s and no project
axioms.

What is **not** claimed: consistency. `Y` inhabits every type at every
sort, which with `Type : Type` is deliberate. The non-triviality claim is
about the *equational* theory, and `zero_ne_succ_zero` and `not_UIP` are
its witnesses.

## File map

Files in dependency order. `Label.lean` and `Regular.lean` both branch off
`DefEq.lean` — the first rejoins at `Shape.lean`, the second at
`HasType.lean` — and from there the chain is linear. Lines are of Lean
source.

| File | Lines | Role |
|---|---:|---|
| [`Basic.lean`](DomainSemantics/Basic.lean) | 13 | The batteries `simp` attributes the project wants on by default. |
| [`Lift.lean`](DomainSemantics/Lift.lean) | 67 | `Lift`: a term-level representation of de Bruijn weakening, used by every later weakening lemma. |
| [`Term.lean`](DomainSemantics/Term.lean) | 335 | Syntax (`Term`), the substitution monoid (`Subst`) and its laws, and contexts (`Lookup`, `Ctx.Lift'`). |
| [`DefEq.lean`](DomainSemantics/DefEq.lean) | 1513 | The standard judgment `IsDefEq₀` (`⊢₀`), the instrumented `IsDefEq` (`⊢`), context well-formedness `Ctx.WF`, the two-sided `Ctx.SubstEq`, and the substitution theorem `IsDefEq.subst'` every later file runs on. |
| [`Label.lean`](DomainSemantics/Label.lean) | 255 | Equality of the syntactic labels a shape carries, up to definitional equality in a context, and `Stable`, the form of it an `app` or `snd` clause carries. |
| [`Regular.lean`](DomainSemantics/Regular.lean) | 229 | Regularity: the subterms of a well-typed term are well typed, read off the judgment's own premises, one shallow inversion per former. |
| [`Shape.lean`](DomainSemantics/Shape.lean) | 2400 | The domain: level-graded `Shape n`, graphs as labelled `Entry` lists, the total `TShape`, and the order, compatibility, join, lift, substitution and graph lookup (`ShapeFun.Eval`).  `Shape.WF` carries an optional name as its last argument, defaulting to `none`, so canonicity rides the recursion rather than being a predicate of its own; `Shape.LE` carries well-formedness of a Π/Σ shape's dominator and of each entry's output as conjuncts. |
| [`HasType.lean`](DomainSemantics/HasType.lean) | 2278 | `TShape.HasType`, typing of shapes, one inductive over `TShape`; the total-level lookup `TEvaluates`; `TShape.Named`, hereditary typing indexed by an optional name, with its transport `Named.defeq`; `TShape.Slot`; the subject join. |
| [`Interp.lean`](DomainSemantics/Interp.lean) | 1737 | `Interp`, the interpretation relation, with one clause per former; the valuation relations and admissibility `Adm`; stage invariance, strengthening and substitution; and the semantic clause conditions `Term.Pinned` collects. |
| [`Directed.lean`](DomainSemantics/Directed.lean) | 1130 | Directedness (`SoundDir`): two approximants of a well-typed term have a common upper bound that is again an approximant. Its own induction on typing, before soundness and independent of it, which is why nothing downstream carries a directedness premise. |
| [`Sound.lean`](DomainSemantics/Sound.lean) | 3986 | `IsDefEq.sound`: four conclusions (equality, saturating semantic typing, both `Pinned`s) in one induction over every rule. |
| [`Inversion.lean`](DomainSemantics/Inversion.lean) | 236 | Π-, Σ- and Id-injectivity, fifteen no-confusion principles, and `zero_ne_succ_zero`, all four steps from soundness and none from adequacy. |
| [`Consequences.lean`](DomainSemantics/Consequences.lean) | 991 | Type uniqueness, sort uniqueness, `IsDefEq.iff`, canonical forms, weak-head reduction `WHRed` with subject reduction, progress, `not_UIP`. |
| [`DomainSemantics.lean`](DomainSemantics.lean) | 72 | Umbrella: the axiom board for the headline theorems. |

`design.md` is the map of the proof: what each definition is, why it has
the shape it has, and how each piece corresponds to the presheaf-over-syntax
development this one was boiled down from. The module docstrings carry the
local detail and point there for the reasons.
