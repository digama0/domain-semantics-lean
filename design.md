# The labelled model: what the definitions are

A map of the finished proof. `presheaf-plan.md` is the original plan,
`presheaf-proof-strategy.md` the running design record (including the
decisions that were reversed); this file is the settled architecture.

Throughout, **intgrah** means `/project/presheaf-semantics-lean`, Jeremy
Chen's presheaf-over-syntax development, and **master** means the
label-free logical-relation proof this branch replaced.

The organising difference from intgrah is that his hypotheses are our
constructions. He builds objects in a category whose morphisms are typed
by construction, so directedness, idempotence and functoriality come free
with the object. We build raw data: a value is one shape, a stage is a
raw substitution, a type is a relation on shapes. Every fact that is free
for him is, here, either a lemma, a hypothesis, or a premise on a clause.
That accounts for most of the definitions below that have no counterpart
on his side.

Master had five moving parts (`Shape`, `HasType`, `LE_Interp`, `Fits`,
`SubstWF`). This has more, in four groups: the domain, the typing of the
domain, the naming discipline (new, and what makes Σ's η true), and the
syntactic bookkeeping that stands in for intgrah's quotient.

## 1. The domain

**`Entry α`** (`Shape.lean`). One row of a function graph: a syntactic
argument `tm` and two shapes, `inp` and `out`. Read it as "applied to the
argument `tm`, on input at least `inp` the result is at least `out`". The
argument's *type* is not stored per row; it is the domain label of the
shape the graph sits in, and every judgment about a graph takes it as a
parameter. intgrah has no entries: his function values are ideals closed
under every graph valid for their action.

**`Shape n`** (`Shape0` at level 0, `ShapeS` above). A finite
approximation of a value, graded by level so the recursion is structural.
`ShapeFun n = List (Entry (Shape n))`. The constructors are the term
formers plus `bot`, and **the type formers carry syntactic labels**:
`forallE (A B : Term)`, `sigma (A B : Term)`, `id (r) (A a b : Term)`,
`lam (A : Term)`, `pair (A a : Term)`. This is the whole gluing trick.
Π-injectivity is a projection out of a Π-shape's label rather than a
consequence of adequacy. `refl` carries nothing, and neither λ nor pair
carries a codomain label, because nothing reads them.

**`TShape = Σ n, Shape n`**, the total domain. Everything downstream is
stated here; the level is bookkeeping, and `Shape.lift` moves a shape up
it.

**`Shape.LE Δ`, `Shape.Compat Δ`, `Shape.join`, `Shape.WF Δ`.** The
approximation order, compatibility, the (total, context-free) join, and
well-formedness. The order is context-indexed and `Prop`-valued because
labels are compared up to definitional equality in `Δ`; master's were
`Bool`-valued. `Shape.WF` says every label occurring in a shape is
well-typed, and it also carries the graph's **internal coherence**:
entries whose labels become definitionally equal at some later stage,
with compatible inputs there, have compatible outputs there. That last
conjunct is intgrah's `Graph.IsCoherent`, and the quantification over
later stages is what makes it survive substitution.

**`ShapeFun.Eval Δ R f A a x y`** (`Shape.lean`), the graph lookup. `y`
is reachable by looking `f` up at the argument `a` of type `A` on input
`x`: `⊥`, the outputs of matching entries, closed downwards and under
compatible joins. It is parameterised by the order one level down, which
is what closes the recursion. `TEvaluates` is the same at the total
level. intgrah's lookup is function application of an ideal-valued map;
the join closure here is what replaces his ideals being closed under sups.

**Coverage, not entry-matching.** `ShapeFun.LE` says every entry of the
smaller graph is *reached by a lookup* in the bigger one. Master and
intgrah both use single-entry coverage (`Graph.LE`), which is too fine
here: η needs an entry whose output is a join of several outputs of the
covering graph, and no single entry dominates that.

## 2. Typing of the domain

**`TShape.HasType Δ m a`** (`HasType.lean`). One inductive over `TShape`,
every clause pinning its subject's shape. The shape `m` is a well-typed
inhabitant of the code `a`. Master's was recursive on the level and
false at `lam`; this is the redesign. Corresponds to intgrah's
`HasFixedness`, read through "ideal = set of approximants", and to his
`decode` in the sense that a code determines which shapes it admits.

Lower-closed: a smaller shape is still typed. That is what the `pair`
clause pays for by reading the second component's code at a **dominator**
of the first rather than at the first itself.

**`TShape.Dom Δ d x`** (`HasType.lean`), hereditary typing. An inductive,
not a recursion on the code, because at Π the codomain code is a *lookup*
in the Π's graph and a premise may not existentially quantify the
inductive being defined. Three clauses:

- at a code that only filters, it is just `HasType`;
- at a Π, additionally every entry's input is `Dom` at the domain and
  every output is `Dom` at the codomain read there (intgrah's
  `arrow Q P F = λX. Q (F (P X))`);
- at a Σ, the first component is `Dom` at the domain and the second at
  the codomain read at the pair's own name.

`Dom` is only ever used upward, so it is closed under joins and needs no
lower-closure. On a slot this is intgrah's `SourceAdmissible.cons`
condition `rawExtend ⟦A⟧ (ρ 0) = ρ 0`: the slot is a fixed point of the
type's idempotent projection. He gets idempotence free from the object;
we have to say what being fixed means, clause by clause on the code.

## 3. Naming (the new part)

This group has no counterpart in master or in intgrah, and it is what
makes Σ's η true. In a value-driven model a pair's second component is
typed at a *shape*; here the model is stage-driven, so the second
component is typed at the code read at a **term**, and that term has to
be the pair's own first projection or η fails. The witness, for
`Γ = [Σ nat nat]`: the slot `pair nat nat (succ zero) zero zero` is well
formed and hereditarily typed at a Σ-code, so the old admissibility
accepted it; it is an approximant of `#0`; and it is *not* one of
`⟨fst #0, snd #0⟩`, whose approximants are all named `fst #0`. With the
naming conjunct it is no longer admissible. (Machine-checked at commit
`248147c`, and again as `ce_not_adm` before that file was dropped as
documentation rather than a deliverable.)

**`Shape.CodeCanon Δ T s`**: the code `s` names its type `T`. Entry-based
on graphs, with `⊥`-outputs exempt, because a dead entry can come alive
after substitution. Closed under conversion, lift, join, downward
inclusion and substitution, and needing no injectivity, since codes
compare both their labels.

**`Shape.ValCanon Δ t s`**: the value `s` names its own projections. A
pair is named by `fst t` and its components name `fst t` and `snd t`; a
λ's entries name `e.tm` on the input and `app t e.tm` on the output.

**`ValCanon.defeq`** is the lemma the whole thing turns on: it moves a
name along a definitional equality of the subject **through the code the
value is `Dom`-typed at**. Stating it relative to the code is what avoids
needing Σ-injectivity or type uniqueness, both of which are derived
*from* soundness here and so unavailable.

## 4. The interpretation

**`Valuation = Nat → TShape`**, with `push`/`tail`, pointwise `WF` and
`LE`. intgrah's environment of ideals.

**`Interp Δ Γ t σ ρ m`** (`Interp.lean`): at ambient context `Δ`, the
shape `m` approximates the term `t` of source context `Γ`, read at the
**stage** `σ` (a raw substitution `Γ → Δ`) and the valuation `ρ`.
Master's `LE_Interp` had neither a context nor a stage. The stage is what
lets a clause state an equation between terms, which is exactly what the
transport rule needs, and it is also what forces the naming discipline.
One clause per former. The binder clauses interpret the body at the
stage extended by the entry's label term (intgrah's
`normalizedBodyAction`, evaluated at `rawExtend ⟦A⟧ x`).

Thirteen clause premises are syntactic typings of the clause's own labels
at the source context. Nothing downstream reads them; they are what lets
`Interp.ctx`, `Interp.weak'` and `Interp.of_substTerm` rebuild the
extended context's well-formedness without taking an annotation
hypothesis (see §6 of the strategy record).

**`Adm Δ Γ₀ Γ σ ρ`**, admissibility. The valuation is well formed and
every slot is (a) an approximant of its type, (b) hereditarily typed
there, (c) at a code that names the type, and (d) **named by the variable
it stands for**. (c) and (d) are the §4.7i addition. intgrah's
`SourceAdmissible`, plus the naming his quotient makes unnecessary.

`Adm.bot` holds for free at the all-`⊥` valuation, which is the stage
every inversion theorem runs at; `Adm.cons` is the extension used inside
the induction.

**`Interp.Dir`** and **`SoundDir`**: directedness, that two approximants
have a common upper bound that is still an approximant. This is
intgrah's `HasIdeality`, which says the raw interpretation is directed at
every admissible stage and so can be made into an ideal. He bundles it
into `RawTermProperties` and proves it in the main induction, because his
`app` case needs the function's fixedness. Ours is a *separate*
induction on typing, proved before soundness and running under the
weaker `Valuation.WF` rather than `Adm`, which works only because
`IsDefEq.dir` never instantiates a binder.

## 5. Bookkeeping that replaces the quotient

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
  a conclusion of soundness, not a hypothesis. Stating these on the `Γ`
  side rather than the stage side was the move that made the substitution
  lemma go through: each is then exactly one half of a subterm's own
  `SoundTy`.
- **`Stable Δ Γ σ a A`** (`Label.lean`): "the label is `A` at the stage",
  quantified over later stages *and* over ambient substitutions. The
  `app` and `snd` clauses need this rather than a typing, because a
  typing cannot be strengthened out of a larger context while a stage can
  be extended into one.

**`Subst.Saturates`** and **`Valuation.Approx`**: every valuation that
approximates a substitution lies below an *admissible* one. This is
intgrah's `SourceAdmissible` together with his `SingleSubstitution`, and
it is what lets the `Pinned` conditions be read at the source stage.

## 6. What soundness says

`IsDefEq.sound` takes `⊢ Γ` and `Γ ⊢ t ≡ t' : A` and returns a record
with five fields, proved in one induction over every rule:

| field | meaning | intgrah |
|---|---|---|
| `eq : SoundEq Γ t t'` | the two sides have the same approximants at every admissible stage | `HasEquality` |
| `ty : SoundTy Γ t A` | the syntactic typing, and: every approximant of `t` is typed at one of `A` | `HasFixedness` |
| `pin`, `pin'` | both sides are `Pinned` | fields of `RawTermProperties` |
| `dom : SoundDom Γ t A` | **saturation**: every approximant sits below one that is hereditarily typed at an approximant of `A`, whose code names `A` and which names `t` | `HasFixedness` read through "ideal = set of approximants", now with names |

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

### What can be merged

`SoundTy` is **implied by** `SoundDom` plus the syntactic typing
(`SoundTy.of_dom`), so wherever `dom` is proved on its own the `ty`
conclusion is a corollary rather than an obligation. At `lam`,
`natCase` and `tr` it was being proved twice, and those cases now read
`ty` off their own `dom`. The implication runs the other way at the type
formers, where `dom` comes from `SoundDom.of_sort` applied to `ty`, so
nothing is saved there; and at `pair` and `Y` the `SoundTy` is also read
for its `typedAt` inside the `Pinned` components.

`CodeCanon` and `ValCanon` look like the obvious candidate for
intermingling, since they are two recursions on the same shape with
complementary heads: `ValCanon` at a type-former shape *is* `CodeCanon`,
and `CodeCanon` at a value-former shape is `True`. That merge does not
work, and the reason is the §4.7 obstruction. `CodeCanon.mono`, downward
closure, is consumed; the merged predicate would have to have it; and
`ValCanon` is not downward closed at `lam`. A smaller λ-shape's entry is
reached by a lookup at a *definitionally equal* label, so its output
names `app t e'.tm` where the bigger one names `app t e.tm`, and moving
a value's name along that equality is `ValCanon.defeq`, which needs the
code the value is `Dom`-typed at. `mono` does not have one. That is why
`ValCanon` has `defeq`, `subst`, `lift`, `join` and `toCode` but no
`mono`.

**`ValCanon` merges with `Dom` instead** (`TShape.Named`, and
`Named.iff` for the equivalence). The two are the same induction: `Dom`
recurses on the code and `ValCanon` on the shape, but a shape typed at a
code has its head determined by that code, so the recursions line up
clause for clause. Folding the naming in needs three observations. At a
code that only filters, a typed shape is never a `lam` or a `pair`
(`ValCanon.of_code`), so the only naming left is a code naming its type,
and `CodeCanon` is `True` on the numerals and on `refl`. At a Π, an
entry's input names the entry's own label term and its output names the
application, which is exactly `ValCanon`'s `lam` clause. At a Σ, the
components name the projections, with the equation read at the Σ's
domain label rather than the pair shape's, the two being definitionally
equal because `HasType.pair` says so.

What is left over, `CodeCanon`, does not merge in, and the reason is not
an obstruction but a type error: `Named` is a statement about the value
`x`, `CodeCanon` one about the *code* `d`. Different subjects, so no
single induction carries both. The slot condition is therefore exactly
two notions (`Slot.iff`), and `Slot` itself is their conjunction.

**And `CodeCanon` folds into `Shape.WF`.** Not as a conjunction and not
as a second recursion: the hereditary half moves into well-formedness,
which was already walking the same shapes, and what is left at the head
is a *shallow* predicate `Shape.CodeCanonS Γ T s` saying only that `s`'s
own labels name `T`. `Shape.WF` asks for one of these at every Π and Σ
node it descends through — the domain's, and one per entry output at the
instantiated codomain — and then for a well-formed shape the deep
condition adds nothing: `CodeCanon.iff_shallow`.

`Shape.LE` needs the same two conjuncts, and that is the only subtle
part. `LE` already carries `WF` of both sides by fiat (the label
equalities, the graph's `WF`, the λ clause's non-degeneracy), which is
why `Shape.LE.wf` can produce a `WF` from an order fact alone. Making
`WF` stronger would falsify that lemma, since the order cannot know what
type a code names; giving `LE` the same conjuncts repairs it with no
signature change, because `LE.wf` then reads them straight off.

The price is that `Shape.WF` is no longer purely structural. A lemma
that *fabricates* a shape out of an arbitrary approximant now has to
know that the approximant names its type. Three do: the single-entry
probes (`Interp.forallE_single`, `sigma_single`) and `SoundEq.sigma_dom`
take the canonicity as a hypothesis, which `SoundEq.forallE_cod`,
`sigma_cod` and `inst_cod` thread up to `Strong.lean`, where soundness
supplies it. `lam_pi_code` and `pair_sigma_code` needed nothing new —
they already proved the Π/Σ code canonical further down, so the
ingredients are hoisted above the `WF` and used twice.

Note what this does *not* buy. Indexing the naming by the code does not
make `defeq` free on its own: moving a pair's name along `t ≡ t'` needs
the Σ labels to be the type of `t`, which is `CodeCanon`. The transport
needs the bundle, not the indexing, which is why `Slot.defeq` is the
form it takes. And the fold is not free: `Dom`'s term argument has to be
supplied at every one of its ~170 sites, and `Dom.of_isType` and
`Dom.of_not_binder` would each gain a `CodeCanon` hypothesis. `Named`
is proved and unused; the propagation is a separate job.

Two things are known to be separable, and both were separated. **`dir`**
is its own induction, proved before soundness and under the weaker
`Valuation.WF`; that works because `IsDefEq.dir` never instantiates a
binder, so it never needs an admissible stage. And the record needs no
`dom'` field: `SoundDom.of_eq` moves saturation across `eq`, so only
`pin` had to be doubled, and that only because `symm` swaps the sides.

Of the four remaining edges, exactly one looks removable. `SoundTy.of_dom`
replaced the former `sound_app_ty` and `sound_snd_ty`; restoring those
would break `ty → dom`. It would not buy a separation, because `ty ↔ pin`
survives on its own.

Two derived notions sit on top. **`CodeAt Γ t`** says every approximant
of `t`, read as a code, names `t`; it follows from any `SoundDom` at a
sort. **`PairCanon`** says every pair-approximant of `p` is named by
`p`'s own first projection, and `PairCanon.of_dom` derives it from
saturation. That is the last step of Σ's η.

## 7. Above soundness

**`StrongSound` / `StrongSoundCore`** (`Strong.lean`): a bundled typing
carrying `SoundTy` for the subterms at the types the corresponding rule
gives them, with `StrongSound.uniq` the semantic half of type uniqueness.

**`Inversion.lean`**: Π-, Σ- and Id-injectivity, fifteen no-confusion
principles, and `zero_ne_succ`. Each is four steps and none uses
adequacy: the type is regular, so it has a label-only approximant
(`Interp.piAtom`); soundness moves that approximant to the other side at
the identity stage and the `⊥` valuation; and reading the label back off
is a projection out of the order. Master needed about 4,900 lines of
logical relation and adequacy for the same results.

**`Consequences.lean`**: type uniqueness, sort uniqueness, the
equivalence of the instrumented and standard judgments, canonical forms,
subject reduction, progress, and the refutation of definitional UIP.

## What is not claimed

Consistency. `Y` inhabits every type at every sort, which with
`Type : Type` is deliberate. The non-triviality claim is about the
*equational* theory, and `zero_ne_succ_zero` and `not_UIP` are its two
witnesses.
