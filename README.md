# DomainSemantics

A Lean 4 formalisation of a denotational semantics for a dependently-typed
λ-calculus, including soundness, adequacy, and type uniqueness theorems.

The semantic domain is a level-graded family of "shape" structures —
finite approximations of values that interpret terms via a step-indexed
logical relation. From the resulting Adequacy theorem we recover Pi-type
and sort injectivity, and from those we prove uniqueness of typing for
the syntactic definitional-equality judgment.

## Compilation

```sh
lake build
```

Build dependencies — [Lean 4](https://lean-lang.org/) (toolchain pinned
via `lean-toolchain` to
[`leanprover/lean4:v4.29.0`](https://github.com/leanprover/lean4/releases/tag/v4.29.0))
and [Batteries](https://github.com/leanprover-community/batteries)
(pinned in `lake-manifest.json`). A first build downloads `batteries`
and compiles 40 jobs; the heaviest file (`Shape.lean`) takes about
30 s on a modern machine.

To rebuild a single file:

```sh
lake build DomainSemantics.UniqueTyping
```

## Validation

Axiom checks for the seven headline theorems are baked into the umbrella
file `DomainSemantics.lean` using `#guard_msgs`:

* `LE_Interp.sound` — soundness
* `LR.adequacy` — fundamental theorem
* `forallE_inv` — Pi injectivity
* `sort_inv` — sort injectivity
* `HasType.uniq` — type uniqueness
* `IsDefEq.uniq_sort` — sort uniqueness
* `IsDefEq.iff` — equivalence of `IsDefEq` and `IsDefEq'`

Each line pins the expected axiom list to exactly
`[propext, Classical.choice, Quot.sound]`. Any `sorryAx` or
project-specific axiom that leaks into a dependency changes the printed
output and fails the build, so a successful `lake build` is the
validation step.

## File map

The library is organised as a strict dependency chain
`Basic → Lift → Term → Shape → Sound → LogRel → Adequacy → UniqueTyping`,
plus the umbrella file `DomainSemantics.lean` that just re-exports the
top of the chain.

| File | Lines | Role |
|---|---:|---|
| [`DomainSemantics/Basic.lean`](DomainSemantics/Basic.lean) | 79 | Prelude. `List`/`Option` lemmas plus `ReflTransGen`, the reflexive-transitive closure used to build multi-step reduction. |
| [`DomainSemantics/Lift.lean`](DomainSemantics/Lift.lean) | 71 | `Lift`: term-level representation of de Bruijn weakening/extension. Used uniformly by every later weakening lemma. |
| [`DomainSemantics/Term.lean`](DomainSemantics/Term.lean) | 902 | Core syntax (`Term`), substitution (`Subst`), context machinery (`Lookup`, `Ctx.Lift'`, `Ctx.WF`), the standard definitional-equality judgment `IsDefEq₀` (notation `⊢₀`), the instrumented `IsDefEq` (notation `⊢`), the two-sided substitution judgment `Ctx.SubstEq`, and weak-head reduction `WHRed`/`WHNF`/`WHRedS`. |
| [`DomainSemantics/Shape.lean`](DomainSemantics/Shape.lean) | 2289 | The semantic domain. Level-graded `Shape n`, well-formed restrictions `WShape n` / `WShapeFun n`, the total domain `TShape := Σ n, WShape n`, plus order, compatibility, join, application, and a decidable typing relation `HasType`. |
| [`DomainSemantics/Sound.lean`](DomainSemantics/Sound.lean) | 1138 | The interpretation relation `LE_Interp` and its saturated form `InterpTyped`; mutual scaffolding `StrongSound` / `StrongSoundCore`; main theorem `LE_Interp.sound`. |
| [`DomainSemantics/LogRel.lean`](DomainSemantics/LogRel.lean) | 790 | The level-graded logical relation. `LogRelBase` (data) / `LogRel` (data + closure properties), `LR0` (base level), `LRS IH` (successor), and the recursive combinator `LR : LogRel Γ n`. |
| [`DomainSemantics/Adequacy.lean`](DomainSemantics/Adequacy.lean) | 567 | The fundamental theorem. `LR.SubstWF` (two-sided substitution well-formedness), `LR.Adequate`, and the headline theorem `LR.adequacy`. Concludes with the inversion lemmas `forallE_inv`, `sort_inv`, `sort_forallE_inv`. |
| [`DomainSemantics/UniqueTyping.lean`](DomainSemantics/UniqueTyping.lean) | 266 | Discharges the `IsDefEq` scaffolding. Bundled typing judgment `HasType`, type uniqueness `HasType.uniq`, sort uniqueness `IsDefEq.uniq_sort`, and the bridge theorem `IsDefEq.iff` that equates the working `IsDefEq` with the standard `IsDefEq'` on well-formed contexts. |
| [`DomainSemantics.lean`](DomainSemantics.lean) | 1 | Umbrella: just `import DomainSemantics.UniqueTyping`. |
