# DomainSemantics

A Lean 4 formalisation of a denotational semantics for a dependently
typed λ-calculus with Π, Σ, `Nat`, `Unit`, a proof-relevant identity
type, a fixpoint `Y`, and `Type : Type`. From it come Π- and Σ-injectivity,
fifteen no-confusion principles, type uniqueness, subject reduction and
progress.

The semantic domain is a level-graded family of "shape" structures,
finite approximations of values, each carrying the **syntactic labels**
of the type or term it approximates. The labels are what glue syntax
into the domain: a function shape's graph is looked up at the label of
the argument, and Π-injectivity is then a projection out of a Π-shape's
label. There is no logical relation and no adequacy theorem; every
syntactic consequence is read off soundness directly.

Admissibility of a valuation asks each slot to **name the term it stands
for**. That is what makes Σ's η true (see `DomainSemantics/Canon.lean`,
and `design.md` for the witness that refutes the weaker admissibility).

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
`IsDefEq₀` (notation `⊢₀`), the judgment of `Term.lean`'s rule list:

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

A second section of the same file is the board for the model's own
internals — the subject join, stage invariance, strengthening,
substitution, saturation, directedness, Σ's η, and the two statements
that say the `Named` and `Slot` merges are faithful. Each line pins the
expected axiom list to exactly `[propext, Classical.choice, Quot.sound]`
(one is tighter). Any `sorryAx` or project-specific axiom that leaks into
a dependency changes the printed output and fails the build, so a
successful `lake build` is the validation step. There are no `sorry`s and
no project axioms.

What is **not** claimed: consistency. `Y` inhabits every type at every
sort, which with `Type : Type` is deliberate. The non-triviality claim is
about the *equational* theory, and `zero_ne_succ_zero` and `not_UIP` are
its witnesses.

## File map

The library is a strict dependency chain. Lines are of Lean source.

| File | Lines | Role |
|---|---:|---|
| [`Basic.lean`](DomainSemantics/Basic.lean) | 13 | The batteries `simp` attributes the project wants on by default. |
| [`Lift.lean`](DomainSemantics/Lift.lean) | 67 | `Lift`: a term-level representation of de Bruijn weakening, used by every later weakening lemma. |
| [`Term.lean`](DomainSemantics/Term.lean) | 1963 | Syntax (`Term`), substitution (`Subst`), contexts (`Lookup`, `Ctx.Lift'`, `Ctx.WF`), the standard judgment `IsDefEq₀` (`⊢₀`), the instrumented `IsDefEq` (`⊢`), the two-sided `Ctx.SubstEq`, and one-step weak-head reduction `WHRed`. |
| [`Regular.lean`](DomainSemantics/Regular.lean) | 165 | Regularity: the subterms of a well-typed term are well typed, read off the judgment's own premises. |
| [`Annot.lean`](DomainSemantics/Annot.lean) | 171 | `Term.Annot`: the typing data a term's own annotations carry, which strengthening needs and which `IsDefEq.annot` supplies. |
| [`Label.lean`](DomainSemantics/Label.lean) | 220 | Equality of the syntactic labels a shape carries, and `Stable`. |
| [`Shape.lean`](DomainSemantics/Shape.lean) | 2719 | The domain: level-graded `Shape n`, graphs as labelled `Entry` lists, the total `TShape`, and the order, compatibility, join, lift, substitution and graph lookup (`ShapeFun.Eval`).  `Shape.WF` and `Shape.LE` carry `CodeCanonS`, the shallow half of canonicity, at every Π and Σ node. |
| [`HasType.lean`](DomainSemantics/HasType.lean) | 2436 | `TShape.HasType`, typing of shapes, one inductive over `TShape`; the total-level lookup `TEvaluates`; `TShape.Dom`, hereditary typing; the subject join. |
| [`Canon.lean`](DomainSemantics/Canon.lean) | 613 | Canonicity: `ValCanon` (a value names its projections), its merge with hereditary typing as `TShape.Named` with `Named.defeq`, and `Slot`, the three facts a valuation slot carries.  A code's naming is `Shape.CodeCanonS`, which lives in `Shape.lean` because `Shape.WF` carries it. |
| [`Interp.lean`](DomainSemantics/Interp.lean) | 2796 | `Interp`, the interpretation relation, with one clause per former; admissibility `Adm`; stage invariance, strengthening and substitution. |
| [`Presheaf.lean`](DomainSemantics/Presheaf.lean) | 5485 | `IsDefEq.sound`: five conclusions (equality, typing, both `Pinned`s, saturation) in one induction, every rule, Σ's η included. |
| [`Strong.lean`](DomainSemantics/Strong.lean) | 241 | `StrongSound.uniq`, the semantic half of type uniqueness. |
| [`Inversion.lean`](DomainSemantics/Inversion.lean) | 272 | Π-, Σ- and Id-injectivity, fifteen no-confusion principles, and `zero_ne_succ_zero`, all four steps from soundness and none from adequacy. |
| [`Consequences.lean`](DomainSemantics/Consequences.lean) | 980 | Type uniqueness, sort uniqueness, `IsDefEq.iff`, canonical forms, subject reduction, progress, `not_UIP`. |
| [`DomainSemantics.lean`](DomainSemantics.lean) | 155 | Umbrella: the axiom board, headline theorems and internals. |

`presheaf-proof-strategy.md` is the design record, including what the
labels buy (§4.7) and what the domain no longer carries (§6).
