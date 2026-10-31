# The labelled model: what the definitions are

A map of the proof — what each definition is and why it has the shape it
has. This is the only design document: the module docstrings carry the
local detail and point here for the reasons.

Throughout, **intgrah** means Jeremy Chen's presheaf-over-syntax
development,
[`intgrah/domain-semantics-lean`](https://github.com/intgrah/domain-semantics-lean).
The organising difference from it is that his hypotheses are our
constructions. He builds objects in a category whose morphisms are typed
by construction, so directedness, idempotence and functoriality come free
with the object. We build raw data: a value is one shape, a stage is a raw
substitution, a type is a relation on shapes. Every fact that is free for
him is here a lemma, a hypothesis, or a premise on a clause. That accounts
for most of the definitions below that have no counterpart on his side,
and the appendix lists the correspondence.

Five groups: the syntax and its judgments, the domain, its typing, the
interpretation, and the syntactic bookkeeping that stands in for his
quotient.

The files, in dependency order: `Term`/`Label`/`Regular` are the
syntax and its judgments, `Shape` and `HasType` the domain and its
typing, `Interp` the interpretation, `Directed` the directedness
induction, `Sound` soundness, and `Inversion`/`Consequences` what follows
from it.

## 0. The syntax and its judgments

**`IsDefEq`** (`DefEq.lean`) exists twice: the raw judgment `Γ ⊢₀ t ≡ t' : A`
and the **instrumented** one `Γ ⊢ t ≡ t' : A`, whose congruence rules carry
their subterms' sort proofs and whose computation rules carry both sides as
typings. `Γ ⊢ t : A` is notation for `Γ ⊢ t ≡ t : A`, so there is no separate
typing judgment anywhere. The instrumentation is what makes each shallow
inversion (§4) a single induction, and `Consequences.lean` proves the two
judgments equivalent — after soundness, since the instrumented `trans'` is
what avoids needing sort uniqueness first.

**`Ctx.WF Γ`** (`⊢ Γ`), by recursion on the context: every entry has a sort
typing in the entries before it. `Ctx.WF' Γ` (`⊢₀ Γ`) is the same against the
raw judgment, and `Ctx.WF.iff` bridges them.

**`Lookup Γ i A`**, de Bruijn lookup: the `i`th entry is `A`, already weakened
over the binders crossed to reach it, which is what the `.lift` in each
constructor accounts for. It is also the *bound* on valuations (§3) — a context
says where its variables stop by what it can look up.

**`Ctx.Lift' l Γ Γ'`**, context weakening as a relation between a `Lift` and
two contexts: `skip` inserts a fresh entry, `cons` keeps one and applies `l` to
it. It is the source of truth for `IsDefEq.weak'`, and `Lookup.weak'`
transports a lookup along it — which is why `Lookup`, and not `i < Γ.length`,
is what the valuation relations quantify over.

**`Ctx.SubstEq Γ₀ σ σ' Γ`** — a **stage**, and the word means this throughout:
a two-sided typed substitution from `Γ` into `Γ₀`, each `.cons` carrying the
entry's sort proof in the source and its head's equality in the target. `.nil`
admits any `σ`, `σ'`, which is what leaves a substitution's junk slots past the
end of `Γ` unconstrained (§3).

**`Stable Δ Γ σ a A`** (`Label.lean`): reading `a` at the stage and at any
later stage out of `Γ` gives two terms equal *at the label* `A`, and this
survives any substitution of the ambient context — the same device
`Shape.Compat` uses, for the same reason. This is what an `app` or `snd` clause
carries in place of "`a` has type `A₀` in `Γ`, and the label is `A₀` here". The
two are interderivable where the argument's typing is at hand
(`Stable.of_typed`, its only producer), but only this form survives
`Stable.unweak`, the move to a *smaller* context: the existential "there is a
type the term has, and the label is it" would have to re-match the clause's
label against a strengthened typing, which is type uniqueness and so circular
here. It carries one transport per `Interp` transport — nine in all.

**`WHRed`** (`⤳`), weak-head reduction: β, the two projections, `natCase`,
`Y`, and recursion on the head. It appears only above soundness, in subject
reduction and progress, and is defined there, in `Consequences.lean`.

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

**Why a label and not a shape.** A λ-shape carries the Π's domain *label*
`A`, not an approximant of the domain. A label is exact syntax up to
definitional equality, so a λ-shape cut into single-entry pieces and
rebuilt (which is what η does) carries the same `A[σ]` throughout, whereas
an approximant is graded by stage and the slot a variable reads would
carry an arbitrary smaller one. `Shape.WF` asks every entry's label type
to be `TyEq` to the shape's own, `LE` and `Compat` ask two λ-shapes'
labels to agree, `join` keeps the left one, and `Interp.app` looks the
argument up at the λ-shape's own label instead of at an existentially
quantified type. That last point is what makes directedness at `app` need
no typing input: two λ-approximants of one term have a common upper bound
whose order clause forces their labels definitionally equal, so one lookup
sits above both. `HasType.lam`'s `TyEq Δ A₀ A` (the label is the Π's
domain) is intgrah's `Section` condition, stored rather than derived.
A pair carries its first component's label for the same reason (§6).

**`Shape.LE Δ`, `Shape.Compat Δ`, `Shape.join`.** The order compares
labels up to definitional equality in `Δ`, so it lives in `Prop` and is
indexed by a context; `Compat` is the compatibility that makes the join
an upper bound; `join` is total and context-free. A well-formed λ-shape
is never information-free, so `IsBot` collapses to `= ⊥` and the
collapse clauses the order would otherwise need disappear.

**`ShapeFun.Compat`** is the graph-level compatibility that `Shape.Compat` is
defined against: two graphs are compatible when any two of their entries whose
labels become definitionally equal at some later stage, with compatible inputs
there, have compatible outputs there. **`TShape.Compat`** lifts both shapes to
their common level and compares there, which is how every total-level order
fact is stated.

**`ShapeFun.WFE`** is the entrywise half of `ShapeFun.WF` — a predicate holds
of both components of every entry — split out so the recursion can hand itself
down without mentioning labels. It is also what two generators certifying
*compatible* values share, coherence being exactly what they need not have.

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
stage can be live at a later one. The lookup is parameterised by the order
one level down and lives in `Shape.lean`, because the dependency descends
a level: `Shape.LE` at `n+1` needs the lookup at `n`, which needs
`Shape.LE` at `n`.

**Coverage, not entry-matching.** `ShapeFun.LE` says every entry of the
smaller graph is *reached by a lookup* in the bigger one, not that it
occurs there. Entry-matching is not transitive once labels are compared
up to definitional equality, and it cannot state η: an entry of an
η-expansion's graph has as its output a *join* of several outputs of the
function's graph, and no single entry need dominate a join. (Saturated
graphs escape by having that join as an entry, and ideals by being closed
under every graph valid for their action; a level index with
non-saturated graphs has neither escape.) Three things the lookup order
asks for, each of them earning its keep:

- the `join` rule carries `Compat`, which is what makes the join of two
  reflected lookups an upper bound of them (`le_join`, through
  `Eval.compat` and `Eval.wf`);
- `ShapeFun.LE` carries well-formedness of both graphs, which is what
  `ShapeFun.Eval.lift_of` needs of the covering graph and cannot take as
  a hypothesis. It is not decoration: an entry whose output is `⊥` says
  nothing, `Eval.bot` discharging it;
- the order demands `WF` only of graphs and of its *lower* bound
  (`Shape.LE.wf`). It cannot be had for the upper one: `⊥` is below
  everything, well formed or not, and has to be, or `Interp.le_id` could
  not invert the `bot` rule without knowing the label is typed.

**Preservation and reflection are separate lemmas.** `Shape.lift_le`
(preservation) is hypothesis-free; `Shape.lift_le_lift` (the iff) needs
`⊢ Δ`, through `Eval.compat` and `le_join`, and so does `TShape.LE.def`
beside `TShape.LE.def_mp`. Reflection is the minority use — an order fact
is read at a higher level far more often than it is built from one — and
keeping preservation free is what stops `⊢ Δ` from spreading to every
site that mentions the order. At the canonical level `max a.1 b.1` a
`TShape.LE` *is* the shape order definitionally, so `LE.refl`, `bot_le`
and `LE.T` are a `show` and a rewrite.

**Normalising the level.** A shape and its lift are equivalent in the
order, so any shape may be moved up without changing what it
approximates (`TShape.lift`, and `Interp.mono` to come back down). That
is what lets a proof put every shape in sight at one level before
touching typing, where the level bookkeeping is done once and for all by
`TShape.HasType.lift_subject` and `lower_subject`.

## 2. Typing of the domain

**`TShape.HasType Δ m a`** (`HasType.lean`). One inductive over `TShape`,
not a recursion on the level. A code *filters* (the shape has the right
head) and, at a binder, types the parts: at a Π the codomain code is a
lookup in the Π's graph. It is what intgrah builds as a decoder — a
retraction operator per code, with a fixed point (`piStep`, `piStage`,
`rank`, `piLimit`) over stages, because his codes are domain elements.
Ours are finite shapes, and the level index already stratifies what that
fixed point constructs, so the whole of that layer is one inductive here.

**Pinning, and the generators.** Every clause **pins the head of its
subject and leaves the contents free**: `.succ v'` below `.succ v` is the
`succ` clause again at `v'`, a λ below `.lam A g` is the `lam` clause
again at its own graph, a pair below `.pair A a x y` is the `pair` clause
again at its own first component. Everything strictly below a shape and
not of its head is `⊥`, and the `bot` clause takes that. The *type* is
pinned too at `lam` and `pair`: the clause names the Π, resp. the Σ,
outright, and `mono_r` moves to a bigger one. `id`, `refl`, `pair`,
`lam`, `forallE` and `sigma` pay for pinning with a `Shape.WF` premise;
`succ` does not, `IsNumeral` implying it. Being above a named type does
not by itself make a type a type (a `forallE` above a `forallE` may have
an untyped codomain graph), so the clauses whose type is not a sort carry
`HasType Δ a .type` outright, which is also what `isType` reads off them;
the sort-typed clauses must not, or `sort` would regress, and they need
not, a sort being rigid (`TShape.LE.sort_symm`).

Only `lam` and `pair` name a **generator** — for `lam` the codomain
witnesses `g₀`, a list of pairs — and ask the subject to be below it. That
is what makes `mono_l` and `mono_r` transitivity of the order rather than
rules of the relation, and it is what gives `proofIrrel` and `subst`
their recursive calls: a dominating witness supplies no induction
hypothesis at the codomain.

**Why an inductive, not a recursion on the level.** Three facts meet. A
level-indexed relation must reflect along `lift`, since the total-level
one is it at the canonical level. Reflection goes clause by clause only
if every object a clause mentions is itself a lift, which forces the λ
clause to be stated per entry. And per entry the clause is *not* closed
under the order, because an entry of a smaller graph has a join of
outputs, and typing a join at an arbitrary type is false — the pair
counterexample below. A generator closes the clause but is not the lift
of anything, so no level-indexed form has both. Over `TShape` there is no
per-level definition to walk back: the generator may live at any level,
`TShape.LE` being level-independent already, and lift-invariance of the
subject becomes a lemma (`lift_subject`, `lower_subject`) instead of a
constraint on the clauses. Two kernel restrictions shape the spelling:

- a premise may not existentially quantify the witness — an `∃` nests the
  inductive inside `Exists`, whose type parameters may not mention
  locals — so the generator is a parameter of the clause. A *list of
  pairs* rather than a function, because a list is reindexed by
  `List.map`, which is the whole of `HasType.subst`;
- `ShapeFun.THasPi` is spelled out in the constructors, the kernel
  refusing the inductive being declared as an argument to a definition.

A third thing to know when reading the file: `Shape.sort` at a variable
level is a stuck `match`, so it does not unify with itself. Any `cases`
on a derivation whose type index is a sort needs that index to be a
variable, which is the `a.2 = Shape.sort j` idiom of `sort_level` and
`cumul`, and why `forallE_inv`/`sigma_inv` are stated as they are.

**The dominator, and what joins two subjects.** The `pair` clause reads
the second component's code at the Σ's codomain graph, looked up at the
pair's own name `a` and at a **dominator** `xd ≥ x` of the first
component. The dominator is what keeps typing lower-closed: shrinking
either component keeps the same `xd`, and so the same code. What it costs
is a join:

> let `f` be a Σ codomain graph with entries at `.zero` and at `.succ ⊥`,
> and let `y` and `z` be pairs with first component `⊥` whose second
> components are typed at those two codes, non-`⊥` and compatible. Both
> are typed at the Σ, with those two dominators, and they are compatible,
> their first components being equal. Their join is typed only if a
> single input serves both, and no numeral is above both `.zero` and
> `.succ ⊥`.

A pair shape records only *one* conditional fact ("at this much of the
first component, the second is at least that"), because it has one second
component and therefore one dominator; a join needs two such facts at
once. So join-closure of typing is not a shape-level fact, and neither is
lower-closure in the per-entry form: both hold of approximants *of a
term*, and for the same reason — a dominating existential is compatible
with another only through the term both dominate. What supplies the join
where it is needed is `TShape.HasType.join`, whose hypotheses are
`TShape.Named` rather than `HasType`: `Named`'s Σ clause reads the code
at the first component *itself*, so joining the first components turns
the two codes into lookups at one query (`TEvaluates.mono_inp` moves each
up to the join), and the codes then join too. A dominator cannot be moved
like that, which is the whole of the counterexample above, and `Named`
can afford to read the component because it is only ever used upward and
so needs no lower-closure. The configuration the counterexample needs
cannot arise in the image of `Interp` either, two compatible pairs having
definitionally equal labels and so approximating one term; the shape
level simply cannot see that, `HasType` not reading labels.

**A Σ-value is two components, not a graph.** The symmetric design —
mirror the λ-value, a first component and a graph from first-component
approximants to second-component approximants — makes the join work
outright (append the graphs, each entry keeping its own code) and breaks
η. A λ-entry's input *is* the slot its body reads, so an entry's output
is justified at exactly that input, and the η-expansion, whose body is a
lookup at the pushed slot, lands on the same one. A pair-entry's input is
never read: it only picks the code that types the output. The order,
though, honours an entry only by a lookup *at that same input*, so a
graph lets a value promise its second component conditionally where the
η-expansion promises it outright, and the expansion is then not below the
value.

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
  `snd t`, and the pair's label equated with `fst t`. This clause reads
  the code at the first component *itself* rather than at a dominator,
  which is what makes the subject join available.

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

**The head probes.** `TShape.IsBinder` is the two codes whose decoder does
more than filter; `TShape.IsPi` and `TShape.IsSigma` are those two separately,
and `TShape.IsLam` the value-side λ. Each is a recursion returning `False` at
level 0, so a probe on a shape of unknown level is decided rather than
inverted. They exist because the order pins heads upward — a shape dominating a
λ-shape is one — which is how `fst`, `snd` and `app` recover a head from a
bound. **`Shape.IsNumeral`** is the same kind of probe for `natCase`'s
scrutinee: `⊥`, `zero`, or a successor of one, with `⊥` included because the
interpretation is downward closed.

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

**`Valuation`, and the three relations on one.** A `Valuation` is
`Nat → TShape`, a shape per variable. `Valuation.WF Δ Γ ρ`, `Valuation.LE Δ Γ ρ ρ'`
and `Valuation.Approx Δ Γ' Γ θ σ ρ ρ'` are its well-formedness, order and
approximation, each quantified over `Γ`'s variables only — see *Where a
substitution ends* below for why the bound is there and why it is a `Lookup`.

**`Adm Δ Γ σ ρ`**, admissibility: every variable's slot is an
approximant of its type and a `Slot` at it — hereditarily typed there,
named by the variable it stands for, at a code that names the type.
intgrah's `SourceAdmissible`, plus the naming his quotient makes
unnecessary. Slotwise well-formedness is not part of it: hereditary
typing is well-formedness at the name, so forgetting the name gives it
(`Adm.wf`). `Adm.bot` holds for free at the all-`⊥` valuation, which is
the stage every inversion theorem runs at. It is a predicate on *slots*
rather than an inductive indexed by a base context, which is what makes
enlargements and joins expressible and keeps a context index off every
signature; `Adm.unlift`, its restriction along a context lift, is what
the weakening lemmas run on.

**`SoundDir Γ t`** (`Directed.lean`): directedness, that two approximants
of `t` have a common upper bound that is still an approximant, at every
stage the context admits. This is intgrah's `HasIdeality`. He proves it
inside the main induction because his `app` case needs the function's
fixedness — his query is the *set* of all typings of the argument, and
collapsing that sup to the canonical label is what the function's typing
pays for. Ours is `IsDefEq.dir`, a *separate* induction on typing,
running under the weaker `Valuation.WF` rather than `Adm`, which works
because a λ-shape carries its own domain label (§1) and because
`IsDefEq.dir` never instantiates a binder.

That induction is its own file, and what makes it one is that it needs
none of `Interp`'s substitution or merging machinery — only the
interpretation, its order lemmas and `Interp.lift`. So `Directed.lean`
imports `Interp` and nothing else. It holds one theorem per typing
rule (`sound_forallE_dir`, `dir_pair`, `dir_app` and so on, each the whole
of its rule's argument, the upper bound's construction included),
`IsDefEq.stage`, and the order-inversion lemmas (`TShape.LE.lam_ub` and
friends) that read a head back off a bound.

Standing alone has a consequence worth stating: **nothing outside this
file mentions `SoundDir` at all**, and nothing anywhere carries a
directedness premise. Directedness holds of every well-typed term, so a
premise asking for it is never information — it is the typing the caller
already has. Each lemma derives what it needs from a typing in its own
signature, which is why `Interp.inst` takes no directedness of its
argument and the `sound_*` lemmas take none of their subterms'.

For a substitution the same fact is `Ctx.SubstEq.dir`: the stage types
the slot, so `IsDefEq.dir` applies. There is no second case, because
nothing ever asks about a slot the stage does not type — see
*Where a substitution ends* below. The substitution lemmas carry the
stage anyway, so the merges (`to_substTerm`, `body_merge`,
`Subst.Saturates.lift`, the `Valuation.Approx` joins) have no
directedness hypothesis either.

The merging lemmas — `to_substTerm`, `inst`, `body_merge` —
are about `Interp` alone but each needs a slot's two approximants joined,
so they sit after `IsDefEq.dir` rather than beside the rest of `Interp`'s
theory.

### Where a substitution ends

A `Subst` is `Nat → Term` and a `Valuation` is `Nat → TShape`: both are
total, so both have slots past the end of the context they belong to.
`Subst.one a` is the example — slot `0` is the argument and slot `i+1` is
`.bvar i`, for every `i`, in range or not. Those slots are junk, and
every relation on valuations is quantified so as not to mention them:

    Valuation.LE Δ Γ ρ ρ'        ∀ {{i A}}, Lookup Γ i A → TShape.LE Δ (ρ i) (ρ' i)
    Valuation.WF Δ Γ ρ           ∀ {{i A}}, Lookup Γ i A → TShape.WF Δ (ρ i)
    Valuation.Approx Δ Γ' Γ θ σ ρ ρ'
                                 ∀ {{i A}}, Lookup Γ i A → Interp Δ Γ' (θ i) σ ρ (ρ' i)

`Approx` names two contexts because a substitution has two: `Γ` is its
source, which is what says where it ends, and `Γ'` its target, where the
approximants live. `Ctx.SubstEq Γ' θ θ Γ` types exactly the slots these
quantifiers reach, which is why it is the only premise the merges need —
it is both the typing and the bound.

Two definitions supply the bound rather than consume it. `Interp.bvar`
carries the variable's `Lookup`, which is what `Interp.mono_val` applies
the order at, and `IsDefEq.bvar_regular` reads it off the variable's own
typing, which is what `Interp.unweak` needs to know an index survives the
descent. The bound is
a `Lookup` rather than `i < Γ.length` because `Lookup.weak'` already
transports it across a context lift; a numeric bound would need a new
transport lemma at every index-moving step.

This is also why no predicate says that a substitution's junk is
harmless. The alternative is one bounded by the context — "every slot is
typed in the target or is a variable", carried by every merge and read
for both strengthening and directedness — and bounding the valuation
relations instead is exactly what makes it unnecessary.

## 4. Bookkeeping that replaces the quotient

intgrah's `Ty`/`Tm` are quotients by definitional equality and his
contexts are objects of a category, so a term comes with its typing. Our
syntax is raw and extrinsic, so four predicates carry what the quotient
would:

- **`LabelEq` / `TyEq` / `PiLabelEq` / `IdLabelEq`** (`Label.lean`):
  equality of labels up to definitional equality. Partial equivalences,
  not reflexive on arbitrary terms, which is why every reflexivity lemma
  downstream takes a context. They are his `Tm.presheaf` — an element of
  which is a type and a term of it, both quotiented by definitional
  equality — spelled as a relation.
- **The shallow inversions** (`Regular.lean`), one per former: from a
  definitional equality mentioning `.lam A b` (on either side — `symm` and
  `trans` force that), the annotation's own typing and a typing for each
  subterm in the context it lives in. The instrumented judgment carries
  subterm sort proofs, so each is one induction whose only case with
  content is the former's congruence rule. The strengthening lemmas take
  the subject's typing and invert it a layer at a time.
- **`Term.Pinned t Γ`** (`Interp.lean`), built from `IsTypeAt`
  (itself `TypedAt` at the top sort together with `CodeAt`), `TypedAt`,
  `PinApp`, `PinSnd`: the *semantic* counterpart of those,
  being the clause conditions that `Interp.to_substTerm` consumes. It is
  a conclusion of soundness, not a hypothesis, and is quantified over
  later stages *and* over ambient substitutions. It mentions a subterm
  only where a clause interprets one, that consumer recursing exactly
  where the clauses do: `id` and `refl` are `True`, a `natCase`'s motive
  and a `tr`'s proof do not appear, and `Y` asks only that its annotation
  be a type. The `app` and `snd`
  clauses need this rather than a typing, because a typing cannot be
  strengthened out of a larger context while a stage can be extended into
  one. Each conjunct is one half of a subterm's own `SoundTy`, which is
  what lets the induction discharge it: `IsTypeAt` at a binder is
  `SoundTy` at a sort, and `PinApp`/`PinSnd` are what intgrah gets from
  `HasFixedness` together with `outputAtom_rawPi_fixed_support`.
- **`Subst.Saturates`** and **`Valuation.Approx`**: every valuation that
  approximates a substitution lies below an *admissible* one. intgrah's
  `SourceAdmissible` together with his `SingleSubstitution`, and what
  lets the `Pinned` conditions be read at the source stage.

**Admissibility is not upward closed**, and that is what decides where
the `Pinned` conditions live. Enlarging a valuation breaks its slots'
typings, typing being a lower set. So the conditions cannot be stated at
the stage `to_substTerm` reconstructs: transporting a subterm's `SoundTy`
across `θ` would read it under the valuation that lemma *builds*, which
need not be admissible, and "enlarge it until it hosts the
type-approximants `Adm` wants" does not close, each enlargement needing
its new slots typed at a bigger valuation again. Stating them on the `Γ`
side and carrying `Subst.Saturates` is what closes it, and the only `θ`
that arises is `one a` lifted, which is why saturation is available. This
is the ideal-versus-approximant gap in its third place (§2 has the other
two, join-closure and lower-closure of typing): on his side the
`Γ`-valuation *is* `⟦θ⟧`, one object, admissible by construction.

Two ways of pinning a label that the model does not take. **Annotating
`Term.app`** with its domain would pin it, at the price of changing the
object language, and the model does not need it. **Indexing `Interp` by a
type** would not pin it at all: the `app` clause's index is `B₀.inst a`,
in which the domain does not occur, so the function's Π-type stays
existential and `to_substTerm` still has to invent `Γ`-level data.

## 5. What soundness says

`IsDefEq.sound` takes `⊢ Γ` and `Γ ⊢ t ≡ t' : A` and returns a record
with four fields — three notions, `pin` once per side — proved in one
induction over every rule:

| field | meaning | intgrah |
|---|---|---|
| `eq : SoundEq Γ t t'` | the two sides have the same approximants at every admissible stage | `HasEquality` |
| `ty : SoundTy Γ t A` | **semantic typing**: every approximant sits below one that is a `Slot` at an approximant of `A` | `HasFixedness` read through "ideal = set of approximants", with the names added |
| `pin`, `pin'` | both sides are `Pinned` | fields of `RawTermProperties` |

Four fields, three notions, and nothing syntactic: the record says only
what the model adds. `SoundTy` is the *saturating* form and the only
semantic typing notion. The weaker reading — every approximant is itself
typed at one of `A` — is `SoundTy.approx`, a consequence: typing is
lower-closed (`TShape.HasType.mono_l`), so the saturating witness can be
dropped.

The syntactic typing is *not* here. It is `H.hasType.1`, which every
consumer of soundness already holds, so carrying it would be carrying the
input back out.

**What the saturation is for** is η. The expansion's graph has to have
*typed* inputs, `Interp.lam` demanding them, and nothing types the inputs
of an arbitrary approximant of the function; what the saturating form
gives is an approximant above it all of whose entry inputs are typed at
the domain, and that one's own lookups are the expansion's bodies. An
entry at an untyped input carries no more than the value at its typed
part, which is why dropping to that approximant loses nothing. intgrah
needs no such step: his λ clause reads the body at the input *normalised
at the domain* (`rawExtend ⟦A⟧ I`, never `I`), so what we saturate for is
in his clause. His `application_piOperator_fixed` is what makes that
work, and `Interp.lam_label_ty` is the half of it we have outright.

There is **no notion of join-closure** here, although the `join` rule of
the graph lookup asks for it wherever a lookup's value has to be typed:
`tr` in `IsDefEq.dir` is the case with the most to maintain, two
approximants typed at two approximants of the motive needing the joined
witness typed at the joined motive. Every such point reaches the subject
join `TShape.Named.join` (§2) directly, so the property of a *type* that
would package them has no consumer and is not stated.

`SoundEq` is type-agnostic, which is what lets the instrumented
judgment's heterogeneous `trans'` rule go through without sort
uniqueness, and so breaks the circularity: soundness comes first, type
uniqueness is derived from it.

### Why they are one induction

They cannot be separated: the three semantic notions, plus `Pinned`, are
one strongly connected component. Reading `X ← Y` as "the proof of `X` consumes `Y` at a
subterm", five of the six possible edges are there.

| | ← `eq` | ← `ty` | ← `pin` |
|---|---|---|---|
| **`eq`** | — | yes | yes |
| **`ty`** | yes | — | yes |
| **`pin`** | *no* | yes | — |

Every edge is at a subterm, which is what a simultaneous induction is
for. The ones that carry the argument:

- **`pin` ← `ty`.** `Term.Pinned` at a binder is `IsTypeAt Γ A` together
  with the subterms' own, and `IsTypeAt` comes from `SoundTy` at a sort
  (`SoundTy.isTypeAt`). It is not a notion of its own: it is `TypedAt Γ A
  (.sort true) ∧ CodeAt Γ A`, and `IsTypeAt.apply` reads the pair off at a
  stage, the `⊥` witness `TypedAt` allows being no weaker because typing
  is monotone in the type. `PinApp.of_sound` and `PinSnd.of_sound` are the
  others.
- **`ty` ← `pin`.** Every `sound_*_dom` takes the codomain's or motive's
  `Pinned`, because saturating the result means instantiating, and
  `Interp.inst` is what consumes `Pinned`.
- **`ty` ← `eq`.** `symm` rebuilds it for the other side
  (`SoundTy.of_eq`).
- **`eq` ← both others**, at the computation rules: `sound_beta`,
  `sound_Y_unfold` and `SoundEq.inst_cod` each take some of them.

So the tightest cycles are two long: `eq ↔ ty`, and — the one that pins
`pin` into the component — `pin ↔ ty`.

The one absent edge is worth naming: **`pin` does not need `eq`**. The
right-hand side's `pin'` is built from the *other* side's `ty`, not from
the equation.

At the type formers the saturation comes from `SoundTy.of_sort` applied to
a `TypedAt`, which is what `sound_forallE_typedAt` and friends produce.
The computation and congruence rules are *padded* — `appDF` carries
`Γ ⊢ B.inst a ≡ B.inst a' : sort v`, `trDF` carries
`Γ ⊢ C.inst b ≡ C'.inst b' : sort v` — so the typing of a rule's own
result type is an induction hypothesis wherever a case needs one, and at
`beta` and `eta` only `SoundEq` has content at all (intgrah's
`of_typings` is the same observation).

One derived notion sits on top: **`CodeAt Γ t`** says every approximant of
`t`, read as a code, names `t`. It is the same shape as `SoundTy` with a
different conclusion, and at a *sort* the two are interderivable:
`SoundTy.codeAt` goes one way (the approximants of a type are codes, and
naming is downward closed on codes, so the name comes down off the
saturated witness), `SoundTy.of_sort` and `SoundTy.of_typedAt` the other.
`CodeAt` is the half that survives going down the order, which is why it
can be an input to `SoundTy.of_typedAt` without circularity — and that is
the only place a `CodeAt` on a *type* is asked for. It has to be: the
atoms' own `SoundTy`s (`soundTy_sort`, `soundTy_nat`, `soundTy_unit`,
`soundTy_zero`, hypothesis-free theorems rather than cases of the
induction) are proved *through* `of_typedAt`, so asking it for a `SoundTy`
of the type would make `soundTy_sort` refer to itself. Everywhere else the
type's `CodeAt` is a `SoundTy … (.sort u)`. `CodeAt` has no relation
to `SoundEq` or `SoundDir` — `Directed.lean` never reads a name.

## 6. Why the naming is there

The naming discipline has no counterpart in intgrah — he has no Σ-types
at all — and it is what makes Σ's η true. In a value-driven model a
pair's second component is typed at a *shape*; here the model is
stage-driven, so the second component is typed at the code read at a
**term**, and that term has to be the pair's own first projection or η
fails.

The witness, for `Γ = [Σ nat nat]`: the slot
`pair nat nat (succ zero) zero zero` is well formed and hereditarily
typed at a Σ-code, so admissibility without the naming accepts it; it is
an approximant of `#0`; and it is *not* one of `⟨fst #0, snd #0⟩`, whose
approximants are all named `fst #0`. With the naming it is not
admissible.

**The label invariant** is the same fact about approximants rather than
about slots: every pair-approximant of `p` carries, as its first
component's label, a term definitionally equal at the stage to `p`'s own
first projection. It is `SoundTy.pair_name`, read off the saturated
approximant above it, and Σ's β at `snd` and Σ's η need it in the same
place — the second component of an approximant is typed at the codomain
looked up *at that label*, while what is wanted is an approximant of
`B.inst (fst p)`. For a literal pair the label is `a[σ]` and `pair_fst`
gives it; for a slot (`p` a variable, the shape handed over by `Adm`)
nothing else does. Like join-closure and lower-closure of typing (§2) it
is a property of approximants of a term and not of shapes: a shape
records the term it approximates only in its labels, and `HasType` does
not read them.

`Interp.snd` reads its query at `fst p` for the same reason, and that is
what the `tr` clause's equation is for: without it `fst (tr … X h)` is
not a name the pair clause can be read at, and Σ's η breaks.

## 7. Above soundness

**`Inversion.lean`**: Π-, Σ- and Id-injectivity, fifteen no-confusion
principles, and `zero_ne_succ`. Each is four steps and none uses
adequacy: the type is regular, so it has a label-only approximant
(`Interp.piAtom`); soundness moves that approximant to the other side at
the identity stage and the `⊥` valuation; and reading the label back off
is a projection out of the order. There is no logical relation and no
adequacy theorem anywhere in the development. These theorems are what the
labels are for, and the reason the values carry syntax at all.

**`Consequences.lean`**: type uniqueness, sort uniqueness, the
equivalence of the instrumented and standard judgments (`Ctx.WF'` is the
context well-formedness of the raw one), canonical forms — `Value`, the closed
weak-head normal forms — subject reduction and progress for `WHRed`, and the
refutation of definitional UIP.

## 8. Axioms

The development is **choice-free**: every one of the eleven guards in
`DomainSemantics.lean` pins `[propext, Quot.sound]`. The two places
`Classical.choice` would enter are handled
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

## Appendix. Correspondence with intgrah

His hypotheses are our constructions, and this is that sentence in full.
A dash means the notion has no counterpart on that side.

| intgrah | here |
|---|---|
| `Ctx := Quotient RawCtx.homRel`; a stage is a morphism, a typed substitution modulo defeq | a stage is a raw `Subst`; invariance under `Ctx.SubstEq` is the theorem `Interp.stage` |
| equality of morphisms mod defeq, and functoriality in the stage, both free | `Interp.stage` and `Interp.subst`, structural in the term, each clause carrying what moves its own label |
| `rawInterpret`, a *function* on raw terms, each clause supping over the typings it needs | `Interp`, a relation, those typings being clause premises |
| `RawValue = ΩLower`, a Kripke lower set; `ΩIdeal` adds directedness | one shape; directedness is `SoundDir`, an induction of its own (§3) |
| `IsDirected`, a field of the ideal | `SoundDir Γ t`, with `sound_dir_of_ub` as his form of the conclusion |
| `Compatible.of_common_upper` | `TShape.Compat.of_common_upper` |
| `cSup`, `CondSemilatticeSup` | `Shape.join` with `Shape.Compat` |
| `Graph.IsCoherent`, `InternallyCompatible` | the coherence conjunct of `Shape.WF`, hereditary and label-sensitive |
| `Graph.LE`, single-entry coverage | `ShapeFun.LE`, lookup coverage (§1) |
| the decoder: `CodeAssignment`, `extend`, `piOperator`, and the `piStep`/`piStage`/`rank`/`piLimit` fixed point | `TShape.HasType` (§2); the level index stratifies what the fixed point constructs |
| `IsCode r`, separate from inhabitation | `HasType · (.sort r)`, cumulative |
| `Section`: a value responds only at labels of the right type | `HasType.lam`'s `TyEq Δ A₀ A`, stored in the shape (§1) |
| `sourceQuery`, the set of all typings of the argument, transported as the image of a set | the λ-shape's own domain label, and one lookup (§1) |
| `normalizedBodyAction`: the body read at `rawExtend ⟦A⟧ x` | the binder clauses read it at the entry's own input, and demand that input typed at the domain (§5) |
| `application_piOperator_fixed` | `Interp.lam_label_ty` for the support half, `SoundTy`'s saturation for the normalisation half |
| `HasEquality`, `HasFixedness` | `SoundEq`, `SoundTy` |
| `HasSubstitution`, `HasRenaming`, fields of `RawTermProperties` proved inside the main induction | `Interp.to_substTerm`, `Interp.weak'`/`unweak`, standalone lemmas taking `Term.Pinned` and `Subst.Saturates` instead |
| `SingleSubstitution.variable_eq` | `Interp.bvar_iff` |
| `SourceAdmissible` | `Adm`, plus the naming his quotient makes unnecessary (§6) |
| `SourceAdmissible` with `SingleSubstitution` | `Subst.Saturates` |
| `Ctx.extension` unquotiented, hence `contextConversion` and `HasRenaming` | nothing: `Interp`'s context index is phantom (`Interp.ctx`) |
| `rawExtend ⟦C[b/]⟧ ⟦x⟧` as the value of `tr` | the `tr` clause's two typing premises |
| `IsIdealValued`: the body action directed at every input | `SoundDir (A::Γ) B` at every well-formed slot |
| `regular`, a field of `RawJudgment` | — (he never uses it) |
| an ideal is closed under every graph valid for its action | — (a value is one shape; lookup coverage is the replacement) |
| — | the naming discipline, `TShape.Named` and `Slot`: he has no Σ |
| — | the inversion theorems, which is what the labels buy (§7) |
