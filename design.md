# The labelled model: what the definitions are

A map of the finished proof — what each definition is and why it has the
shape it has. `presheaf-proof-strategy.md` is the design record and keeps
the history; this file describes only the settled architecture.

Throughout, **intgrah** means `/project/presheaf-semantics-lean`, Jeremy
Chen's presheaf-over-syntax development. The organising difference from it
is that his hypotheses are our constructions. He builds objects in a
category whose morphisms are typed by construction, so directedness,
idempotence and functoriality come free with the object. We build raw
data: a value is one shape, a stage is a raw substitution, a type is a
relation on shapes. Every fact that is free for him is here a lemma, a
hypothesis, or a premise on a clause. That accounts for most of the
definitions below that have no counterpart on his side.

Four groups: the domain, its typing, the interpretation, and the
syntactic bookkeeping that stands in for his quotient.

## 1. The domain

**`Entry α`** (`Shape.lean`). One row of a function graph: a syntactic
argument `tm` and two shapes, `inp` and `out`. Read it as "applied to the
argument `tm`, on input at least `inp` the result is at least `out`". The
argument's *type* is not stored per row; it is the domain label of the
shape the graph belongs to.

**`Shape n`** (`Shape0` at level 0, `ShapeS` above). A finite
approximation of a value, graded by level. `⊥`, the numerals, `refl`,
sorts, `unit`, `nat`, `id`; the type formers `forallE A B d f` and
`sigma A B d f`, each carrying syntactic labels `A B`, a domain code `d`
and a graph `f`; and the value formers `lam A f` and `pair A a x y`. The
labels are what glue syntax into the domain: Π-injectivity is a
projection out of a Π-shape's label.

**`TShape = Σ n, Shape n`**, the total domain. Everything downstream is
stated here; `Shape n` exists so the recursions terminate.

**`Shape.LE Δ`, `Shape.Compat Δ`, `Shape.join`.** The order compares
labels up to definitional equality in `Δ`, so it lives in `Prop` and is
indexed by a context; `Compat` is the compatibility that makes the join
an upper bound; `join` is total and context-free. A well-formed λ-shape
is never information-free, so `IsBot` collapses to `= ⊥` and the
collapse clauses the order would otherwise need disappear.

**`Shape.WF Γ s o`**, well-formedness, with an `Option Term` index: every
label in `s` is well typed in `Γ`, and at a name the head's own labels
name it. The index is the last argument and defaults to `none`, so
`Shape.WF Γ s` is the structural notion written exactly as if there were
no index; `Option`'s coercion then lets the named form be written
`Shape.WF Γ s T` rather than `Shape.WF Γ s (some T)`.

The index is read in one place, `TyEqO Γ o T'` — `True` at `none`,
`TyEq Γ T T'` at a name — so at `none` every clause reduces to the
structural one. It carries down the recursion rather than being restated:
a Π node asks for its domain code at `A` and, through `ShapeFun.WF`, each
entry's output at `B.inst e.tm`. There is no
separate canonicity predicate; hereditary naming *is* `WF` at an index.

`WF` also carries the two conditions that are not about labels:
non-degeneracy (a λ-shape has an entry with a non-`⊥` output, a pair has
an informative component), and **internal coherence** — entries whose
labels become definitionally equal at some later stage, with compatible
inputs there, have compatible outputs there. Coherence is what makes the
graph lookup's joins exist, and it belongs here because `WF` is the
single "good shape" predicate the interpretation carries anyway.

**`ShapeFun.Eval Δ R f A a x y`**, the graph lookup. `y` is reached from
the graph `f` at argument `a` and input `x`: `bot`, or an `entry` whose
label is definitionally equal to `a`, or `lower`, or a `join` of two
lookups. `TEvaluates` is the total-level version. A code's codomain is
never stored; it is looked up, which is why an entry that is dead at one
stage can be live at a later one.

**Coverage, not entry-matching.** `ShapeFun.LE` says every entry of the
smaller graph is *reached by a lookup* in the bigger one, not that it
occurs there. Entry-matching is not transitive once labels are compared
up to definitional equality.

## 2. Typing of the domain

**`TShape.HasType Δ m a`** (`HasType.lean`). One inductive over `TShape`,
not a recursion: at a Π the codomain code is a lookup in the Π's graph,
and a premise may not existentially quantify the inductive being defined.
A code *filters* (the shape has the right head) and, at a binder, types
the parts. The `pair` clause reads the second component's code at a
**dominator** of the first rather than at the first itself, which is what
keeps typing lower-closed.

**`TShape.Named Δ d x o`**, hereditary typing with a name. An inductive
over the code, with an `Option Term` index that is the name, last and
defaulting to `none`, so `Named Δ d x` is hereditary typing alone and
`Named Δ d x t` is that together with "`x` names `t`". Three
clauses:

- at a code that only filters, `HasType` together with `TShape.WF Δ x o`
  — the subject well formed at the index;
- at a Π, every entry's input is hereditarily typed at the domain and
  every output at the codomain read there (intgrah's
  `arrow Q P F = λX. Q (F (P X))`), the index becoming `e.tm` on the
  input and `app t e.tm` on the output;
- at a Σ, the first component at the domain and the second at the
  codomain read at the pair's own name, the index becoming `fst t` and
  `snd t`, and the pair's label equated with `fst t`.

Making the name an index rather than an argument is what lets one
inductive and one copy of each closure lemma (`subst`, `lift_subject`,
`mono_r`, `join`, `sg_inv`, `defeq`) serve both readings. The extraction
`Named.wf : Named Δ d x o → TShape.WF Δ x o` has premise and conclusion
the same proposition.

`Named` is only ever used upward, so it is closed under joins and needs
no lower-closure.

**`Named.defeq`** is the lemma the whole thing turns on: it moves a name
along a definitional equality of the subject, **through the code the
shape is hereditarily typed at**. Stating it relative to the code is what
avoids needing Σ-injectivity or type uniqueness, both of which are
derived *from* soundness here and so unavailable. It is one induction on
`Named`, legal because the index is a variable: the conclusion maps it to
the constant `t'`, so `none` goes to `none` and a name `t` to `t'`.

**`TShape.Slot Δ T d t x`** is `Named Δ d x t ∧ TShape.WF Δ d T` — the
shape names the term, and its code names the type. Two
conjuncts, not three and not a bundle, because the naming already travels
inside the hereditary typing.

## 3. The interpretation

**`Valuation = Nat → TShape`**, with `push`/`tail`, pointwise `WF` and
`LE`. intgrah's environment of ideals.

**`Interp Δ Γ t σ ρ m`** (`Interp.lean`): at ambient context `Δ`, the
shape `m` approximates the term `t` of source context `Γ`, read at the
**stage** `σ` (a raw substitution `Γ → Δ`) and the valuation `ρ`. One
clause per former. The stage is what lets a clause state an equation
between terms, which is what the transport rule needs and what forces the
naming discipline. The binder clauses interpret the body at the stage
extended by the entry's label term (intgrah's `normalizedBodyAction`,
evaluated at `rawExtend ⟦A⟧ x`).

Several clause premises are syntactic typings of the clause's own labels
at the source context. Nothing downstream reads them; they are what let
`Interp.ctx`, `Interp.weak'` and `Interp.of_substTerm` rebuild the
extended context's well-formedness without taking an annotation
hypothesis.

**`Adm Δ Γ₀ Γ σ ρ`**, admissibility: the valuation is well formed, and
every variable's slot is an approximant of its type and a `Slot` at it —
hereditarily typed there, named by the variable it stands for, at a code
that names the type. intgrah's `SourceAdmissible`, plus the naming his
quotient makes unnecessary. `Adm.bot` holds for free at the all-`⊥`
valuation, which is the stage every inversion theorem runs at.

**`Interp.Dir`** and **`SoundDir`**: directedness, that two approximants
have a common upper bound that is still an approximant. This is intgrah's
`HasIdeality`. He proves it inside the main induction because his `app`
case needs the function's fixedness; ours is a *separate* induction on
typing, proved before soundness and running under the weaker
`Valuation.WF` rather than `Adm`, which works only because `IsDefEq.dir`
never instantiates a binder.

## 4. Bookkeeping that replaces the quotient

intgrah's `Ty`/`Tm` are quotients by definitional equality and his
contexts are objects of a category, so a term comes with its typing. Our
syntax is raw and extrinsic, so four predicates carry what the quotient
would:

- **`LabelEq` / `TyEq` / `PiLabelEq` / `IdLabelEq`** (`Label.lean`):
  equality of labels up to definitional equality. Partial equivalences,
  not reflexive on arbitrary terms, which is why every reflexivity lemma
  downstream takes a context.
- **`Term.Annot t Γ`** (`Annot.lean`): every annotation inside `t` is
  typed where it occurs. Syntax-directed, and free from the instrumented
  judgment (`IsDefEq.annot`), because that judgment carries subterm sort
  proofs. The extrinsic stand-in for intrinsically typed syntax.
- **`Term.Pinned t Γ`** (`Interp.lean`), built from `IsTypeAt`,
  `TypedAt`, `PinApp`, `PinSnd`: the *semantic* counterpart of `Annot`,
  being the clause conditions that `Interp.to_substTerm` consumes. It is
  a conclusion of soundness, not a hypothesis, and is quantified over
  later stages *and* over ambient substitutions. The `app` and `snd`
  clauses need this rather than a typing, because a typing cannot be
  strengthened out of a larger context while a stage can be extended into
  one.
- **`Subst.Saturates`** and **`Valuation.Approx`**: every valuation that
  approximates a substitution lies below an *admissible* one. intgrah's
  `SourceAdmissible` together with his `SingleSubstitution`, and what
  lets the `Pinned` conditions be read at the source stage.

## 5. What soundness says

`IsDefEq.sound` takes `⊢ Γ` and `Γ ⊢ t ≡ t' : A` and returns a record
with five fields, proved in one induction over every rule:

| field | meaning | intgrah |
|---|---|---|
| `eq : SoundEq Γ t t'` | the two sides have the same approximants at every admissible stage | `HasEquality` |
| `ty : SoundTy Γ t A` | the syntactic typing, and: every approximant of `t` is typed at one of `A` | `HasFixedness` |
| `pin`, `pin'` | both sides are `Pinned` | fields of `RawTermProperties` |
| `dom : SoundDom Γ t A` | **saturation**: every approximant sits below one that is a `Slot` at an approximant of `A` | `HasFixedness` read through "ideal = set of approximants", now with names |

`SoundEq` is type-agnostic, which is what lets the instrumented
judgment's heterogeneous `trans'` rule go through without sort
uniqueness, and so breaks the circularity: soundness comes first, type
uniqueness is derived from it.

### Why they are one induction

They cannot be separated. The five are one strongly connected component,
and the tightest cycle needs only two of them:

- **`pin` needs `ty`.** `Term.Pinned` at a binder is `IsTypeAt Γ A`
  together with the subterms' own, and `IsTypeAt` is half of
  `SoundTy Γ A (.sort u)` (`SoundTy.isTypeAt`).
- **`ty` needs `pin`.** `sound_tr_ty` and `sound_natCase_ty` take the
  motive's `Pinned`, because typing the result means instantiating the
  motive and `Interp.inst` is what consumes `Pinned`.

Both edges are at subterms, which is exactly what a simultaneous
induction is for. Three further cycles run through the other two fields:
`ty` needs `dom` (at `app` and `snd`, through `SoundTy.of_dom`: an
approximant sits below a hereditarily typed one and typing is
lower-closed); `dom` needs `pin` (every `sound_*_dom` takes the
codomain's or motive's `Pinned`); and `eq` needs all three while `ty` and
`dom` need `eq`, because `symm` rebuilds them for the other side with
`SoundTy.of_eq` and `SoundDom.of_eq`.

`SoundTy` is **implied by** `SoundDom` plus the syntactic typing
(`SoundTy.of_dom`), so wherever `dom` is proved on its own the `ty`
conclusion is a corollary. At `lam`, `natCase` and `tr` the cases read
`ty` off their own `dom`. The implication runs the other way at the type
formers, where `dom` comes from `SoundDom.of_sort` applied to `ty`.

Two derived notions sit on top. **`CodeAt Γ t`** says every approximant
of `t`, read as a code, names `t`; it follows from any `SoundDom` at a
sort. **`PairCanon`** says every pair-approximant of `p` is named by
`p`'s own first projection, and `PairCanon.of_dom` derives it from
saturation. That is the last step of Σ's η.

## 6. Why the naming is there

The naming discipline has no counterpart in intgrah, and it is what makes
Σ's η true. In a value-driven model a pair's second component is typed at
a *shape*; here the model is stage-driven, so the second component is
typed at the code read at a **term**, and that term has to be the pair's
own first projection or η fails.

The witness, for `Γ = [Σ nat nat]`: the slot
`pair nat nat (succ zero) zero zero` is well formed and hereditarily
typed at a Σ-code, so admissibility without the naming accepts it; it is
an approximant of `#0`; and it is *not* one of `⟨fst #0, snd #0⟩`, whose
approximants are all named `fst #0`. With the naming it is not
admissible.

## 7. Above soundness

**`StrongSound` / `StrongSoundCore`** (`Strong.lean`): a bundled typing
carrying `SoundTy` for the subterms at the types the corresponding rule
gives them, with `StrongSound.uniq` the semantic half of type uniqueness.

**`Inversion.lean`**: Π-, Σ- and Id-injectivity, fifteen no-confusion
principles, and `zero_ne_succ`. Each is four steps and none uses
adequacy: the type is regular, so it has a label-only approximant
(`Interp.piAtom`); soundness moves that approximant to the other side at
the identity stage and the `⊥` valuation; and reading the label back off
is a projection out of the order. There is no logical relation and no
adequacy theorem anywhere in the development.

**`Consequences.lean`**: type uniqueness, sort uniqueness, the
equivalence of the instrumented and standard judgments, canonical forms,
subject reduction, progress, and the refutation of definitional UIP.

## 8. Axioms

The development is **choice-free**: every one of the 25 guards in
`DomainSemantics.lean` pins `[propext, Quot.sound]`, and one is tighter
still. The two places `Classical.choice` would enter are handled
structurally rather than classically — the sort level hidden inside
`TyEq Δ A A' := ∃ u, Δ ⊢ A ≡ A' : .sort u` is destructured rather than
chosen, and the one case split on whether a shape is `⊥` goes through the
decidable `Shape.IsBot` rather than equality with `⊥`. There are no
`sorry`s and no project axioms.

## What is not claimed

Consistency. `Y` inhabits every type at every sort, which with
`Type : Type` is deliberate. The non-triviality claim is about the
*equational* theory, and `zero_ne_succ_zero` and `not_UIP` are its two
witnesses.
