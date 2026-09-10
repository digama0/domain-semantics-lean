# Boiling down the presheaf model (intgrah/domain-semantics-lean)

Analysis of how `intgrah/domain-semantics-lean` (Jeremy Chen, 2026-09-10, ~14k
lines, Mathlib + lean-autosubst, local clone at `/project/presheaf-semantics-lean`)
proves definitional inversion *from soundness alone*, and a plan for an
elementary reimplementation on the `presheaf` branch of this repo, over the
`master` syntax (`Term.lean`), without Mathlib or autosubst.

Notation below: `Δ ⊢ σ : Γ` means `Ctx.SubstEq Δ σ σ Γ` (our `Term.lean`).
"His" = intgrah's development; file names in `code` refer to his tree unless
said otherwise.

---

## 1. What is proved, and the shape of the argument

Headline (`Inversion.lean`, `Unique.lean`):

* `IsDefEq.forallE_inv : ⊢Γ → Γ ⊢ ΠAB ≡ ΠA'B' : T → Γ ⊢ A ≡ A' ∧ A::Γ ⊢ B ≡ B' ∧ A'::Γ ⊢ B ≡ B'`
* `IsDefEq.sort_inv`, plus no-confusion sort/Π/nat/id.
* `IsDefEq.type_unique`, `sort_unique` (the usual canonical-type induction,
  same as our `Consequences.lean`).

The argument has **one** semantic theorem, soundness
(`IsDefEq.rawSoundness : ⊢Γ → Γ ⊢ t ≡ t' : A → RawJudgment Γ t t' A`), and
no logical relation, no adequacy, no reduction relation. This is possible
because **the syntax is embedded in the semantic domain**:

* function graphs are labelled by *syntactic arguments* (defeq classes of
  typed terms of the current context), and
* Π-shapes carry the *syntactic pair* `(A, B)` as a label (again a defeq
  class), so the *only* Π-atom in `⟦Π A B⟧` is `piAtom (A,B)`.

Then `⟦ΠAB⟧ = ⟦ΠA'B'⟧` (an instance of soundness at the identity stage and
the bottom valuation) forces `(A,B) = (A',B')` as classes, i.e. defeq.

Everything else — the domain-theoretic machinery — exists to make soundness
true: the `β`, `η`, `proofIrrel`, `tr_K` rules and the congruence rules
must hold *as equations* between the interpretations, and the interpretation
must commute with substitution.

## 2. The categorical scaffolding, and what it is really for

### 2.1 `Ctx`, `Ty`, `Tm` (`Syntax/Intrinsic.lean`, 750 lines)

* `RawCtx` = `{terms : List Term // ⊢ terms}`; morphisms `Raw.Hom Γ₁ Γ₂` =
  substitutions `σ` with `Γ₁ ⊢ σ : Γ₂`. `Ctx := Quotient` of this category by
  `Γ₁ ⊢ σ ≡ σ' ⊣ Γ₂` (two-sided `SubstEq`).
* `Ty Γ` = defeq classes of types in `Γ` (as a presheaf, via Yoneda);
  `Tm Γ A` = defeq classes of terms of type `A`; `Tm.typing : Tm → Ty`.
* Context extension `Γ.extend A` is proved to be the *representing object*
  of the pullback of `Tm.typing` along `A` (a comprehension category,
  `Presheaf/Comprehension.lean`, 290 lines). What is used downstream:
  - `Ctx.rawDisplay hA` / `Ctx.extension hA = A :: Γ`,
  - **sections**: `Raw.ContextSection hA σ label` — a morphism
    `s.hom : Δ ⟶ A::Γ` over `σ : Δ ⟶ Γ` whose generic term is `label`.
    Concretely `s.hom` is the substitution `σ.cons t` where the label is
    `(A[σ], t)` with `Δ ⊢ t : A[σ]`. Sections are a *subsingleton*
    (`Section.hom_eq`), which is what makes "`∃ s : Section, …`" harmless.
  - `pairOfTyping_eq_iff` (labels equal ⇔ components defeq) — the payload of
    the inversion theorem.

**Why the quotient.** Two reasons only: (i) `Ty`/`Tm` must be honest
presheaves (functoriality on the nose) to use Mathlib's functor-hom
machinery; (ii) graph lookup (`Entry.mem : g.names j = name`) is *equality*
of labels, and soundness of `appDF` (`a ≡ a'` ⇒ same lookup) needs labels
to be identified up to defeq.

**Boil-down.** Keep raw `List Term` contexts and raw substitutions; make the
*order on shapes* compare labels up to defeq in a context (`LabelEq Δ`),
and put `⊢ Θ`, `Θ ⊢ τ : Δ` as hypotheses on every reindexing lemma. The
category laws we need (`(t[σ])[τ] = t[σ.comp τ]`, identity) hold on the
nose for raw substitutions; invariance under `σ ≡ σ'` is only needed where
labels are compared, which the order now handles. (Alternative kept in
reserve: labels as `Quotient` of raw pairs by defeq — `Quot` is in core
Lean; costs typing witnesses inside *definitions* such as `Shape.reindex`.
See §7.)

### 2.2 `ΩLower`, `ΩIdeal` (`Presheaf/Lower/Basic.lean`, `Presheaf/Ideal.lean`)

`ΩLower R X` for a presheaf of pointed posets `R` on `C` is the *internal
lower set*: a value at stage `X` assigns to every `f : Y ⟶ X` a lower set of
`R(Y)`, naturally. Inlined for our situation (`R` = coherent shapes,
`C` = contexts):

```
structure Val where
  mem     : (Θ : List Term) → Subst → Shape → Prop         -- mem Θ τ x, "x ∈ V at stage (Θ, τ)"
  natural : ⊢Θ' → Θ' ⊢ τ' : Θ → mem Θ τ x → mem Θ' (τ.comp τ') (x.subst τ')
  bottom  : mem Θ τ ⊥
  lower   : LE Θ x y → mem Θ τ y → mem Θ τ x
```

Note `Val` needs **no home context index**: `mem Θ τ x` is meaningful when
`Θ ⊢ τ : Γ` for the intended home `Γ`, but nothing in the structure
mentions `Γ`. Operations: `pullback σ V` (`mem Θ τ x := V.mem Θ (σ.comp τ) x`),
`principal a` (`mem Θ τ x := LE Θ x (a.subst τ)`), `⊥`, arbitrary unions
(`iSup`, with the `x ≤ ⊥ ∨ …` guard so the union is never empty), `bind`
(`mem f b := ∃ a, I.mem f a ∧ (F a).mem id b`, i.e. Kleisli extension of
a basis-defined map).

`ΩIdeal` = `ΩLower` + `IsDirected` (any two members at the same stage have
an upper bound at that stage). `Domain Γ := ΩIdeal`. His interpretation
lands in `RawValue = ΩLower`; *directedness is a proved property*
(`HasIdeality`) of interpretations of well-typed terms.

The **presheaf/functor-hom layer** (`Functor.HomObj`, `parameterizedHom`,
`Subfunctor`, `Preord`/`CondSemilatSup` categories, ~2.5k lines) exists to
say "natural family of monotone maps" for: valuations → values
(`RawFamily`), (label, shape) → value (`BasisAction`), (label, value) →
value (`IdealAction`), value → value (`IdealOperator`), etc. In the
boil-down each of these is a plain function together with a *naturality
lemma stated with typing hypotheses*; no structures needed except `Val`.

### 2.3 Shapes, coherence, joins (`Basis/*.lean`, ~1.6k lines)

```
Shape Γ ::= bot | sort r | forallE (label : (A : Ty Γ) × Ty (Γ.A)) (dom : Shape) (graph)
          | lam (graph) | nat | zero | succ (label) (pred) | id (A a b : Shape)
graph   ::= k entries (names : Fin k → (A : Ty Γ) × Tm Γ A) (ins outs : Fin k → Shape)
```

* Order `LE` (`Basis/Order.lean`): `collapse` (`IsBottom a → a ≤ b`, where
  `IsBottom` = `⊥` or a graph with all-bottom outputs), structural
  congruences, and graph order = every entry of `f` is *covered* by an entry
  of `g` with the *same* label, smaller input, larger output (`Entry.mem`),
  or has bottom output. Only a **preorder** (graphs are lists).
* `IsCoherent` (`Basis/Coherent.lean`, `InternalCoherence.lean`): every
  graph inside a shape is *internally directed*: any two entries whose
  labels agree and whose inputs are compatible **at every future stage**
  have compatible outputs there. `CoherentShape Γ` is the subtype; the
  domain is built over coherent shapes so that:
  - outputs of one function at compatible inputs are compatible
    (`Evaluates.compatible`) ⇒ `application` of an ideal is directed,
  - two valid graphs of an ideal-valued action are jointly coherent
    (`GraphValid.internallyCompatible`) ⇒ `abstraction` is directed,
  - `sup a b h` exists for compatible `a b` (`Basis/Join.lean`), giving a
    `CondSemilatticeSup`; `universeIdeal` and `pi` directedness use it.
* `rank` (`Basis/Rank.lean`) — only for the decoder's fixed point (§2.5).
* `IsCode r a` (`Basis/UniverseShape.lean`): which shapes are codes of
  types in universe `r`: `sort`, `forallE` (in `type`; in `prop` iff all
  graph outputs are prop-codes), `nat`, `id` (both), bottoms.

**Boil-down.** Shapes become *context-free* trees with raw terms as labels
(`DomainSemantics/Presheaf/Basis.lean`, started): `pi (A B : Term) dom g`,
`id (A a b : Term)`, `lam g`, `sort`, `unit`; graphs as a mutual inductive
list of `(A, a, x, y)`. `LE Δ` compares labels with `LabelEq Δ` (= syntactic
equality ∨ typed defeq; the first disjunct keeps `LE Δ` reflexive on
ill-typed labels). Coherence and compatibility become predicates
`Coherent Δ x` (hereditary: quantified over typed `τ`) and `Compat Δ a b :=
∃ c, a ≤ c ∧ b ≤ c`; the join is a total structural function `Shape.join`
proved to be a lub on compatible pairs. Whether coherence is a subtype or a
property carried by "ideal" is open (§7).

### 2.4 Application, abstraction, Π (`Domain/Evaluation.lean`, `Domain/Action*.lean`, `Domain/Pi.lean`)

* `OutputAtom I label x y`: some graph `f ∈ I` (at the current stage) has
  an entry with label `= label`, input `≤ x`, output `= y`.
  `Evaluates I label x y`: closure of `OutputAtom` under `⊥`, lowering,
  and *binary joins of compatible outputs* (needed for directedness).
  `application I label X := {y | ∃ x ∈ X, Evaluates (I∣stage) label x y}`
  (stage-wise; naturality by reindexing entries).
* `BasisAction` = natural family `(stage, label, shape) ↦ value`.
  `GraphValid F σ f := ∀ entries (ℓ, x, y) of f, y ∈ F(σ, ℓ, x)` at the
  current stage; `abstraction F := {q | ∃ valid f, q ≤ lam f}` stage-wise.
  `IdealAction` = same with ideal inputs, and `onBasis` restricts it.
* `pi label A B := {q | ∃ a ∈ A, valid f for B, q ≤ piGenerator label a f}`;
  `piAtom label := piGenerator label ⊥ nil`, and
  `mem_piAtom_pi_iff : piAtom l' ∈ pi l A B ↔ l' = l[σ]` — the inversion
  payload. `pi_isDirected` needs `A` directed and `B` ideal-valued.

All of these are *basis-defined*: their value on an arbitrary lower set is
determined by the finite elements. This is what will let us drop
finitarity (§3).

### 2.5 The decoder = typing as retraction (`Domain/Decoder/*.lean`, `Domain/Universe.lean`, ~2.3k lines)

The universe is modelled à la Scott: a **code** (any shape) denotes an
idempotent operator ("retraction") on the domain, and "`t : A`" means
`⟦t⟧` is a fixed point of the operator denoted by `⟦A⟧`.

* `IdealOperator Γ` = natural family of monotone *finitary* maps
  `Domain Γ₁ → Domain Γ₁` over stages `σ : Γ₁ ⟶ Γ`.
* `CodeAssignment := order ⟶ IdealOperator.presheaf`: a monotone natural
  assignment of an operator to every *basis* code. Derived:
  - `eval F c X := (F c) X` at the identity stage,
  - `rawExtend F T X := bind₂ T X (fun (c,x) ↦ eval F c (principal x))`,
    i.e. `{y | ∃ c ∈ T, x ∈ X, y ∈ F c ⟨x⟩}` — decoding a *set* of codes
    applied to a *set* of payloads via finite approximants (`extend` is the
    ideal version). `decode F T` is the operator `X ↦ extend F T X`.
  - `IsIdempotent F` (`F c ∘ F c = F c` pointwise) ⇒ `extend F T` idempotent.
* The operators used: `universeOperator r` (restrict to `IsCode r` shapes);
  `natOperator` (project to nat-shapes); the **Π retraction**
  `piOperator F A B := (resultOperator F B).arrow (decode F A)` where
  - `P := decode F A` decodes the domain,
  - `Q(ℓ)(X, Y) := extend F (B(ℓ)(X)) Y` decodes the result at label `ℓ`
    with the family's code `B(ℓ)(X)`,
  - `arrow Q P G := abstraction (ℓ, x ↦ Q(ℓ)(P x, application G ℓ (P x)))`
    (`FunctionRetraction.lean`): re-abstract `G` after retracting input
    and output. Key equation (`application_piOperator`):
    `app (R G) ℓ X = Q(ℓ)(P X, app G ℓ (P X))` — this is where
    finitarity of `Q` and `P` and directedness of `X` are used
    (RHS ⊆ LHS needs one finite `x ∈ X` witnessing both `P`-approximant
    and application entry).
  - for a *code* `pi label a f` the family action is
    `graphAction f := (ℓ, X) ↦ application ⟨lam f⟩ ℓ X` (`PiDecoder.lean`):
    the codes for `B(x)` are the outputs of the graph `f`.
* The fixed point: `piStep F` maps each code to its operator using `F` for
  sub-codes; `piStage 0 = ⊥`, `piStage (n+1) = piStep (piStage n)`;
  `piLimit c := piStage (rank c + 1) c`, well-defined by rank stability
  (`PiStages.lean`, `RankLocality.lean`: outputs of `application ⟨lam f⟩`
  have rank ≤ rank f), and `piLimit_fixedPoint : piLimit.piStep = piLimit`
  (`PiFixedPoint.lean`), giving the decoding equations
  `decode ⟨sort r⟩ = universeOperator r`, `decode (pi l A B) = piOperator A B`.
* Strictness (`DecoderStrictness.lean`): every operator sends `⊥` to `⊥`
  (`IsPayloadStrict`), hence `rawExtend T ⊥ = ⊥` — this is why the bottom
  valuation is admissible (`Raw.WF.bottom_admissible`) and the inversion
  theorem can be run at `ρ = ⊥`.
* `Prop`: prop-codes decode to the `⊥` operator (`piStage_eval_prop`), so
  any two proofs of a prop have interpretation `⊥`: `proofIrrel` is free.
  (`Interpretation/Prop.lean`.)

### 2.6 The interpretation (`Interpretation/*.lean`, ~3k lines)

`rawInterpret D Γ : Term → RawFamily Γ`, i.e. `⟦t⟧ σ ρ : RawValue Γ₁` for a
stage `σ : Γ₁ ⟶ Γ` and a **semantic valuation** `ρ : ℕ → RawValue Γ₁`.
Note `σ` and `ρ` are independent data: `σ` only feeds the labels, `ρ` the
variables. Defined on *raw* terms; typing derivations occur only as
`Prop`-indices of a `⨆` (so derivation-independence is free):

* `bvar i ↦ ρ i`; `sort u ↦ ⟨sortAtom u⟩`; `nat`, `zero`, `id A a b` similar
  (`identity` builds `.id`-shapes from members of `⟦A⟧ ⟦a⟧ ⟦b⟧`); `refl ↦ ⊥`.
* `app f a ↦ application ⟦f⟧ ⟦a⟧ (sourceQuery Γ a)` where
  `sourceQuery Γ a = {(A, a) | Γ ⊢ A : sort u, Γ ⊢ a : A}` reindexed along
  `σ`: look the graph up at *every typing* of the argument.
* `lam A b ↦ ⨆_{hA} abstraction D (rawDisplay hA) ⟦A⟧ ⟦b⟧` with the
  **normalized body action** (`Binder.lean`, `Abstraction.lean`):
  `(σ₁, ℓ, I) ↦ sectionValue …` = "`⊥`-guarded: if there is a section `s`
  over `σ₁ ≫ σ` with label `ℓ` then `⟦b⟧ s.hom (ρ.push I')`, where
  `I' := rawExtend D ⟦A⟧ I` is the input *retracted to the domain*".
  Concretely: entry `((A[σ], t), x, y)` is valid iff `Δ ⊢ t : A[σ]` and
  `y ∈ ⟦b⟧ (σ.cons t) (ρ.push (decode ⟦A⟧ ⟨x⟩))`. **Substituting the label
  term for the bound variable in the syntactic stage** is the coupling of
  syntax and semantics.
* `forallE A B ↦ ⨆_{hA,hB} pi D (rawDisplay hA) (A,B) ⟦A⟧ ⟦B⟧` with the same
  normalized body action for `B`.
* `tr A a b C x h ↦ ⨆ decode D (⟦C⟧ instantiated along the section of b) ⟦x⟧`
  (transport = retract `x` to the target type; `K` holds by fixedness).
* `natRec` via an explicit iteration `Nat/Iteration.lean` (450 lines).

`rawInterpret_isFinitary`: every `⟦t⟧` is finitary (continuous) in each
valuation slot — used for `toIdealAction` and `arrow`.

### 2.7 Admissibility and the soundness invariant (`Soundness/*.lean`, ~2.6k lines)

`SourceAdmissible σ ρ` (for `σ : Γ₁ ⟶ Γ`): by recursion on `Γ`; for
`A :: Γ`: tail admissible, `⟦A⟧ (σ ≫ proj) ρ.tail` directed, `ρ 0`
directed, and `rawExtend ⟦A⟧ (ρ 0) = ρ 0` (**`ρ 0` is a fixed point of the
decoder of its type**). No relation between `ρ i` and `σ i`.

Properties of a raw term `t` at `Γ` (all "∀ stage σ, ∀ admissible ρ, …"):

| property | statement | used for |
|---|---|---|
| `HasIdeality Γ t` | `⟦t⟧ σ ρ` directed | β-equation, abstraction directed, `push` admissible |
| `HasRenaming Γ t` | `⟦t[r]⟧ σ ρ = ⟦t⟧ (σ ≫ r) (ρ ∘ r)` for variable maps `r` | η (weakening `e↑`), building `ContextRen` |
| `HasSubstitution Γ t` | `⟦t[θ]⟧ σ ρt = ⟦t⟧ (σ ≫ θ) ρs` for `SingleSubstitution θ σ ρs ρt` (θ = one/oneAlong/ren/lift) | β, `appDF` result type, `tr_K` |
| `HasFixedness Γ t A` | `rawExtend ⟦A⟧ ⟦t⟧ = ⟦t⟧` | typing; proof-irrelevance; η; app lookups |
| `HasEquality Γ t t'` | `⟦t⟧ σ ρ = ⟦t'⟧ σ ρ` | the actual defeq |
| `PiReady Γ A B` | body action of `B` over `A` is ideal-valued | `app` cases |

`RawJudgment Γ t t' A` = `regular` (`A` is a fixed point of its sort) +
`type`, `left`, `right : RawTermProperties` (ideality, substitution,
readiness) + `equal` + `fixed`. `rawSemantics` is one induction on
`IsDefEq` (plus `ContextRen Γ` carried along), each case a lemma in
`BasicJudgments`/`BinderRules`/`EliminationRules`/`ComputationRules`.

Rule by rule, what carries the case:

* `bvar`: admissibility gives directedness and fixedness of `ρ i` (via
  `ContextRen.lookup`, which needs `HasRenaming` of the context types to
  move `⟦A⟧` across the projection).
* `appDF`: `application_piOperator_fixed`: since `⟦f⟧` is a fixed point of
  the Π-retraction, `app ⟦f⟧ ℓ X = Q(ℓ)(P X, app ⟦f⟧ ℓ (P X))`; with `X = ⟦a⟧`
  already `P`-fixed, the lookup only sees labels whose *type is defeq to
  `A[σ]`* (the section exists), so `sourceQuery a` and `sourceQuery a'`
  agree (`SourceQuery.lean`) — this is how the argument avoids needing
  type uniqueness. Result fixed under `⟦B[a]⟧` by `HasSubstitution B` along
  the section (`HasSubstitution.instantiate`).
* `lamDF`/`forallEDF`: body actions agree (`section_contextConversion`
  handles `A::Γ` vs `A'::Γ`); ideality from `HasIdeality.bodyAction`;
  fixedness of `lam` under `pi` = `LambdaFixed.lean`
  (`normalizedAbstraction_fixed`: re-abstracting a normalized abstraction
  is the identity), fixedness of `pi` under `sort` = `IsCode`.
* `beta`: `rawInterpret_beta` (`Computation.lean`): `app (abstraction act) ℓ X`
  with `ℓ ∈ sourceQuery a` equals `act ℓ X` = `⟦b⟧ (σ.cons a) (ρ.push ⟦a⟧)`
  (needs `X` directed, `act` ideal-valued, `rawExtend ⟦A⟧ ⟦a⟧ = ⟦a⟧`), then
  `HasSubstitution b` turns that into `⟦b[a]⟧ σ ρ`.
* `eta`: `HasEquality.eta` (`EliminationRules.lean`, 200 lines): both sides
  are abstractions of body actions once `⟦e⟧` is rewritten as `R ⟦e⟧`;
  `HasRenaming e` moves `e↑` back; `eta_query_eq_of_section` shows the
  `bvar 0` query picks exactly the section's label.
* `defeqDF`: `HasFixedness.convert` (equality of types gives equal decoders).
* `proofIrrel`: `rawInterpret_proofIrrel` from strictness on prop codes.
* `trans'`: `RawJudgment.trans` ignores the middle type — heterogeneous
  transitivity is free semantically.

### 2.8 Inversion (`Inversion.lean`, 130 lines)

`forallE_inv`: `p := rawSoundness`; `p.equal id ⊥ (bottom_admissible)` gives
`⟦ΠAB⟧ id ⊥ = ⟦ΠA'B'⟧ id ⊥`; `piAtom (A,B) ∈ LHS` trivially, hence
`∈ RHS`, hence `(A,B) = (A',B')` as labels, hence
`pairOfTyping_eq_iff`. `sort_inv`: `sortAtom u ≤ sortAtom v`.
No-confusion: constructor mismatch in `LE`. The typing side conditions
(`hA hB hA' hB'`) come from `p.left.ready`/`p.right.ready` (that is the
only reason `PiReady` records the derivations).

## 3. Where continuity is used, and why we can drop it

His `IsFinitary` (for `ΩLower`: `f I ∋ y ⇒ ∃ finite s ⊆ I, f ⟨s⟩ ∋ y`;
`Presheaf/Approximation.lean` uses a `Filter` of approximations) appears
in: `IdealOperator`/`IdealAction`/`DependentOperator` (as a *field*),
`toIdealAction`, `abstraction_finitary`, `arrowAction.property`,
`rawInterpret_isFinitary` and all `IsFinitary.*` lemmas of `Interpretation/*`.
Its real consumer is the retraction equation `app (R G) ℓ X = Q(P X, app G ℓ (P X))`
(RHS ⊆ LHS needs finite witnesses), and `Nat/Iteration`.

If every operator is **defined on basis elements and extended by `bind`**
(as `CodeAssignment`, `rawExtend`, `application`, `abstraction` already
are), continuity is automatic and the retraction equation only needs the
*argument* `X` to be directed. So the boil-down defines all operators as
`Shape → Val` (per stage) and never states finitarity. The price: `Y` (see
§5) needs continuity of `⟦t⟧` *in the valuation*, which we would then prove
as one lemma by induction on terms when we get there.

## 4. The boiled-down design

Files (new; nothing existing is modified):

* `DomainSemantics/Presheaf/Basis.lean` — shapes with term labels,
  substitution action, `LabelEq`/`PiLabelEq`/`IdLabelEq`, `IsBottom`,
  `LE Δ`/`GraphLE Δ`/`Entry Δ`, preorder, `LE.subst`, `rank`, `join`,
  `Compat`, `Coherent`, `IsCode`. (Started; order defined, proofs pending.)
* `DomainSemantics/Presheaf.lean` (next to `Sound.lean`) — `Val` (inlined
  `ΩLower`), `IsIdeal`, valuations, the semantic operations, the decoder,
  `interp`, `Adm`, the properties and `RawJudgment`. Split later if it
  grows.
* `DomainSemantics/PresheafSound.lean`, `PresheafInversion.lean` — the
  soundness induction and the inversion theorems in the interface
  `Consequences.lean` expects (`forallE_inv`, `sort_inv`, `id_inv`,
  no-confusion).

### 4.1 Values

`Val` as in §2.2, unindexed. Derived: `pullback`, `principal`, `⊥`,
`iSup`, `IsIdeal V := ∀ Θ τ, directed (V.mem Θ τ) ∧ (coherence, see §7)`.
Convenience: "local families". Most values are of the form
`mem Θ τ y := L Θ τ y` for a predicate `L` on (stage, shape) that is
hereditary under typed substitution; a constructor `Val.ofLocal` packages
naturality/bottom/lower once.

### 4.2 Operations (all per stage, all basis-defined)

```
Evaluates Θ (F : Val) (ℓ : Term × Term) : Shape → Shape → Prop     -- at stage τ inside F
app  (F : Val) (ℓ : Term × Term) (X : Val) : Val   -- mem Θ τ y := ∃ x, X.mem Θ τ x ∧ Evaluates Θ (F∣τ) (ℓ[τ]) x y
GraphValid Θ τ (act : List Term → Subst → Term×Term → Shape → Val) (g : Graph) : Prop
abs  (act) : Val                                   -- mem Θ τ q := ∃ g, GraphValid Θ τ act g ∧ LE Θ q (lam g)
piVal (A B : Term) (D : Val) (act) : Val           -- mem Θ τ q := ∃ a g, D.mem Θ τ a ∧ GraphValid … g ∧ LE Θ q (pi (A[τ]) (B[τ.lift]) a g)
sortVal u := principal (sort u);  idVal A a b := principal (id A a b);  unitVal r
restrict (r : Bool) (X : Val) : Val                -- members that are r-codes
```

Actions are raw functions `(Θ, τ, ℓ, x) ↦ Val` plus a naturality lemma;
no `Act` structure.

### 4.3 Decoder

`decodeN : ℕ → (Θ : List Term) → (code x : Shape) → Shape → Prop` by
recursion on the fuel (his `piStage`), where

* `sort r ↦ fun x y => LE Θ y x ∧ IsCode r y`,
* `pi _ _ a g ↦` the arrow retraction, with `P := decodeN n Θ a`,
  `Q(ℓ)(X,Y) := ⋃_{c ∈ app ⟨lam g⟩ ℓ X, y ∈ Y} decodeN n Θ c y` (all made
  into `Val`s via the local-family constructor),
* everything else (`bot`, `lam`, `unit`, `id`, prop-codes) `↦ ⊥`.

`decodeAt Θ c := decodeN (rank c + 1) Θ c`; `decodeVal c x : Val` with
`mem Θ τ y := decodeAt Θ (c[τ]) (x[τ]) y`; `extend (C X : Val) : Val` =
`bind₂`: `mem Θ τ y := ∃ c x, C.mem Θ τ c ∧ X.mem Θ τ x ∧ decodeAt Θ c x y`.
Needed lemmas: hereditary (naturality), rank stability, idempotence,
strictness (`extend C ⊥ = ⊥`), prop-codes decode to `⊥`, and the decoding
equations for `sort`/`pi`.

### 4.4 Interpretation

`interp (Γ : List Term) : Term → (Δ : List Term) → Subst → (ℕ → Val) → Val`
following §2.6 verbatim, with sections replaced by the typing side
condition `∃ u, Θ ⊢ A'[τ] ≡ A[σ∘τ] : sort u` ∧ `Θ ⊢ t[τ] : A'[τ]` and the
stage `σ.cons t`. Constructs not yet modelled (`sigma`, `pair`, `fst`,
`snd`, `nat`, `zero`, `succ`, `natCase`, `Y`) interpret to `⊥` for now.

### 4.5 Admissibility, properties, `RawJudgment`

Verbatim from §2.7 with raw data: `Adm : (Γ : List Term) → (Δ : List Term)
→ Subst → (ℕ → Val) → Prop` by recursion on `Γ` (tail = `σ.tail`,
`ρ.tail`); the five properties as `∀ Δ σ ρ, ⊢Δ → Δ ⊢ σ : Γ → Adm Γ Δ σ ρ → …`;
`RawJudgment` as a structure of Props.

## 5. Language coverage (master `Term.lean`)

| construct | model | status in plan |
|---|---|---|
| `sort`, `forallE`, `lam`, `app`, `proofIrrel` | as his | core of the work |
| `id A a b` (`type`-valued, proof-relevant on master) | label atom `id A a b`; `refl ↦ ⊥`; `tr ↦ extend ⟦C[b]⟧ ⟦x⟧`; id-codes decode to `⊥` | cheap; `tr_refl` is fixedness of `x`; gives `id_inv` from labels; the model validates UIP semantically, which is harmless for inversion |
| `unit r`, `star r`, `unit_eta` | atom `unit r` (an `r`-code), `star ↦ ⊥`, decodes to `⊥` | cheap |
| `sigma`, `pair`, `fst`, `snd` | Σ-shape with `(A,B)` label + dom + graph, pair shapes; retraction = componentwise | later; mirrors Π |
| `nat`, `zero`, `succ`, `natCase` | his `Nat/*` (1.3k lines) | later |
| `Y A b`, `Y_unfold` | `⨆ₙ Fⁿ ⊥` with `F X := ⟦b⟧ (ρ.push X)`; unfolding needs continuity of `⟦b⟧` in `ρ` | later; the one place continuity is genuinely needed |

## 6. Obligations, roughly ordered

1. Basis: `LE` preorder (mutual recursion on the *middle* shape, since
   `induction` does not support mutual inductives), `LE.subst`,
   `IsBottom` lemmas, `join` is a lub on compatible pairs, `rank` and
   `rank_join`, `Coherent` hereditary, `IsCode` closure. (~his 1.6k lines,
   expect ~800.)
2. `Val` and operations with naturality; `app`/`abs`/`piVal` directedness
   under coherence; `mem_piAtom_piVal_iff`, `sortAtom_le_iff`. (~600.)
3. Decoder: fuel recursion, hereditary, rank stability, idempotence,
   strictness, decoding equations, retraction equation
   `app (R G) ℓ X = Q(P X, app G ℓ (P X))` for directed `X`. (~1000.)
4. `interp`, `Adm`, `bottom_admissible`, `Adm.pullback`/`push`. (~300.)
5. Soundness cases: structural (`bvar`, `sort`, `defeqDF`, `symm/trans`),
   `HasSubstitution`/`HasRenaming` for each constructor, binders
   (`lamDF`, `forallEDF`, `LambdaFixed`), `appDF`, `beta`, `eta`,
   `proofIrrel`, id/unit rules. (~his 2.6k + parts of Interpretation; the
   bulk of the work.)
6. Inversion + hooking into `Consequences.lean` (parametrise it over the
   inversion lemmas, or duplicate the small bridge). (~100.)

The inversion theorem (6) can be proved against the *statement* of
soundness first, so the branch is useful before (5) is complete.

## 7. Open choices (for discussion)

1. **Labels: defeq-aware order vs `Quot`.** Chosen: order compares labels
   up to defeq in `Δ`; every reindexing lemma takes `⊢Θ`, `Θ ⊢ τ : Δ`.
   `LE Δ` is then only a preorder, but so is his. The alternative
   (`Quotient` of raw pairs by defeq, core-Lean `Quot`) makes `Entry` a
   plain equality but forces typing witnesses into `Shape.subst`.
2. **Coherence: subtype vs property.** His `CoherentShape` subtype makes
   every element coherent by construction. With context-dependent
   coherence a subtype would re-index shapes by `Δ`; the alternative is
   `IsIdeal := directed ∧ coherent members`, and prove coherence of
   outputs where needed. Leaning towards the property.
3. **Directedness at all?** Needed only for the retraction equation
   (argument side) and hence for β; η goes through "both sides are
   abstractions of the same action". Could not find a way to drop it.
4. **Stage `σ` vs valuation `ρ`.** Kept independent (as his). The
   inversion argument runs at `σ = id`, `ρ = ⊥`; no "syntactic valuation"
   is ever needed.
5. **Id semantics.** `⊥`-inhabited, label-only shape (§5). If we later
   want the model to refute UIP semantically, `refl` would need a real
   shape and `tr` a case split — not needed for inversion.
