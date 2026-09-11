# Boiling down the presheaf model (intgrah/domain-semantics-lean)

Appendix A is a three-way comparison table (other repo / master / this
branch) and is the quickest way in.  The body below analyses how
`intgrah/domain-semantics-lean` (Jeremy Chen, 2026-09-10, ~14k
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
*order on shapes* compare labels up to defeq in a context (`LabelEq Δ`,
`DomainSemantics/Label.lean`), and put `⊢ Θ`, `Θ ⊢ τ : Δ` as hypotheses on
every reindexing lemma. The category laws we need (`(t[σ])[τ] =
t[σ.comp τ]`, identity) hold on the nose for raw substitutions; invariance
under `σ ≡ σ'` is only needed where labels are compared, which the order
handles. This is the "preservation lemmas instead of a quotient" policy of
§4.

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

(This structure is *not* used in the boil-down, see §4: the only lower sets
in the proof are principal ones from the valuation and the interpretation
itself, so `mem` is replaced by the single relation `Interp`. The box above
is what `ΩLower` amounts to.) Operations: `pullback σ V` (`mem Θ τ x := V.mem Θ (σ.comp τ) x`),
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
boil-down each of these becomes a lemma about the relation `Interp`
(naturality along typed substitutions); no structures at all.

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

**Boil-down.** Superseded by §4.1: we keep our stratified `Shape.lean`
and add labels; coherence and joins are our existing `WF`/`Compat`/`join`
with `LabelEq Δ` in the entry order.

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
relations on shapes (per stage) and never states finitarity. The price: `Y` (see
§5) needs continuity of `⟦t⟧` *in the valuation*, which we would then prove
as one lemma by induction on terms when we get there.

## 4. The boiled-down design (revised after discussion)

Decisions so far:

* **No quotients, preservation lemmas instead.** Contexts are `List Term`,
  substitutions are `Subst`, labels are raw terms. Wherever his
  construction relies on `Ctx`/`Ty`/`Tm` being quotients by defeq, we
  instead prove that the notion in question is preserved by the defeq
  relation, with WF side conditions — the same policy `Term.lean` already
  follows for contexts and terms modulo defeq (`IsDefEq.subst`,
  `defeqDF_l`, `SubstEq`). Concretely the relation enters in exactly one
  definition, the order on shapes (`LabelEq Δ` inside `LE Δ`), and the
  preservation lemmas are `LabelEq.subst`, `LE.subst`, and the naturality
  lemma for the interpretation, all along *typed* substitutions
  (`⊢ Θ`, `Θ ⊢ τ : Δ`), because defeq is only stable under those.
* **Keep our `Shape.lean`**, with its level stratification
  (`Shape (n+1) = ShapeS (Shape n)`, `WShape`, `TShape`), and add the
  gluing data: graph entries of `lam`/`forallE`/`sigma` carry a syntactic
  label `(A, a) : Term × Term`; `forallE`/`sigma` carry the syntactic pair
  `(A, B)`; `id` carries the syntactic triple `(A, a, b)` (plus the
  relevance flag, see §5); `unit r` is an atom. The old file is kept as
  `Shape.old.lean` for reference; `Sound`/`LogRel`/`Adequacy` will break
  and are to be deleted on this branch. The level index replaces his
  `rank` and makes the decoder's fixed point a recursion on `n` (no
  `piStage`/`piLimit`/rank-stability).
* **No `Val`/`ΩLower` structure.** The only sources of lower sets in his
  proof are the valuation and compositional constructions; nothing
  quantifies over arbitrary natural assignments. So, as in `Sound.lean`,
  valuations are single shapes `ρ : Nat → TShape` (principal ideals) and
  the whole model is **one inductively defined relation**

  ```
  Interp Γ : Term → (Δ : List Term) → Subst → (Nat → TShape) → TShape → Prop
  --  Interp Γ t Δ σ ρ x : "x is an approximant of ⟦t⟧ at stage σ : Δ → Γ under ρ"
  ```

  plus the shape-level typing relation `HasType` (§4.2). Directedness (`join`),
  monotonicity in `ρ`, naturality along typed `τ`, and the substitution
  lemma (with its `∃ ρ'` + join trick, which is the finitarity argument
  done once) become lemmas by induction on derivations, exactly as
  `LE_Interp.mono/join/subst` today.
* **Inductive, not recursive, `Interp`.** `Y` (and later `natCase`) is
  not structural; an inductive definition gives the least fixed point for
  free — a shape is in `⟦Y A b⟧` iff finitely many unfoldings produce it —
  and every lemma about `Y` is just another case of the derivation
  induction. A recursive definition would need `⋃ₙ Fⁿ ⊥` plus continuity
  of `⟦b⟧` in `ρ` and an inner induction on `n` in every lemma. Positivity
  holds: all occurrences of `Interp` in premises are positive (`app`,
  `tr` are `∃`/`∧`; binder validity is `∀ e ∈ g.entries` over a finite
  graph, i.e. over data); `HasType` is defined on shapes alone and never
  mentions `Interp`.

### 4.1 Shapes (modifications to `Shape.lean`)

```
ShapeS X ::= bot | sort r | unit r
           | forallE (A B : Term) (dom : X) (f : LFun X)      -- label (A,B)
           | sigma   (A B : Term) (dom : X) (f : LFun X)
           | lam  (f : LFun X) | pair (a b : X)
           | id (r : Bool) (A a b : Term)                      -- label only
           | refl (w : X)                                      -- kept (proof-relevant Id)
           | nat | zero | succ (label) (w : X)
LFun X := List ((Term × Term) × X × X)                         -- entries ((A,a), in, out)
```

Order: as now, plus `LabelEq Δ` on labels, so `Shape.LE` becomes
`Shape.LE Δ` (context-indexed). The `Bool`-valued `ble`/`Compat` become
`Prop`s (label defeq is not decidable); `lift`/`olift` carry labels
through unchanged.

**Graph semantics: per-entry, not saturated.** Our `ShapeFun.WF`
(`⊥`-input entry, closure of inputs under compatible joins, monotone
samples) makes a graph a saturated sample so that `app` is a `find?` of
the maximal entry below the input. Saturation is per label class and
label classes merge under substitution, so it is not preserved by
reindexing and cannot be kept. Replace by his `Evaluates`: the output at
`(ℓ, a)` is the join of all outputs of entries with label `≡_Δ ℓ` and input
`≤ a`, closed under `⊥` and lowering (an inductive relation
`Evaluates Δ f ℓ a y`, which is the premise of the `app` constructor).
Consequences: graph join is list append; no `⊥` entry, no stored joins,
no monotonicity of samples; `maxBelow`/`trunc`/`ShapeFun.app`/
`ShapeFun.join`/`NonZero`/`lam'` are deleted; a λ with only `⊥` outputs is
handled by the `IsBottom`/`collapse` rule of `LE`. Coherence is the only
invariant, and it is what makes the computed join a lub. Coherence (his `IsCoherent`, our `WF` +
`Compat`) becomes the hereditary condition on graphs: entries with defeq
labels and compatible inputs, at every typed later stage, have compatible
outputs. `IsCode r` as in his `UniverseShape.lean`.

### 4.2 The decoder, implemented by `HasType`

The other repo's decoder is **not** optional: `HasFixedness Γ t A`
(`rawExtend ⟦A⟧ ⟦t⟧ = ⟦t⟧`) is one of the six components of
`RawJudgment` and carries the typing content of soundness (§2.7).  What is
optional is *how* it is built.  He constructs a retraction operator per
code (`CodeAssignment`, `extend`, `piOperator`), and needs the
`piStep`/`piStage`/`rank`/`piLimit` fixed point because his shapes have no
typing relation at all.  Ours do, so we implement the same notion with
`HasType`, in master's style, and the fixed-point construction disappears
(the level index of `Shape n` already stratifies it).

Note the argument of the retraction is an **ideal**, not a shape:
`extend T X` takes the type-ideal `T = ⟦A⟧` and the term-ideal `X = ⟦t⟧`.
Bounding by a single shape would under-approximate, because master's
`{z ≤ x ∣ z : c}` had a maximum only thanks to graph saturation, which is
gone (§4.1); with the ideal formulation the joins come from directedness
of the interpretation instead.

| other repo | role | ours | master |
|---|---|---|---|
| `extend T X` | retract the term ideal to the type ideal | `{m ∣ ∃ m' a, m ≤ m' ∧ m' ∈ X ∧ a ∈ T ∧ m'.HasType a}` | `InterpTyped` (`Sound.lean:530`) |
| `HasFixedness Γ t A` | "`t : A`", semantically | every `m ∈ ⟦t⟧` is such an `m'`-approximant | `SoundTy` (`Sound.lean:813`) |
| `IsIdempotent` | `extend T ∘ extend T = extend T` | immediate: the typed set is lower-closed and contains its witnesses | — |
| `IsPayloadStrict`, `extend T ⊥ = ⊥` | admissibility of the `⊥` valuation | `⊥` is typed at everything | `WShape.HasType.bot` |
| `piStage_eval_prop` (prop codes ↦ `⊥`) | `proofIrrel` | prop-typed shapes collapse | `WShape.HasType.proofIrrel`, `TShape.HasType.proofIrrel` |
| `universeOperator r` | sort codes | `IsCode r` := `HasType · (sort r)` | — |
| `piOperator`, `arrow`, `application_piOperator` | β | the `∀ x, x.HasType a → …` premise of the `lam`/`forallE` clauses, plus `sound_app`/`sound_lam` | `LE_Interp` |
| `piStep`/`piStage`/`rank`/`piLimit` | the fixed point | not needed — recursion on the level | — |

So the obligation is to define `HasType` on **labelled** shapes so that it
still supports the behaviour the decoder needs.  What has to be checked:

1. `⊥` is typed at every type shape, and the typed set is lower-closed
   (strictness, idempotence).
2. Two typed shapes at compatible types have a typed join (directedness of
   the retraction; this is where coherence is consumed).
3. Prop-typed shapes are `⊥` (proof irrelevance).
4. Preservation under typed substitution — new, since labels move.
5. The Π/λ clause restated with the **relational** lookup: `HasType`
   for Π and λ used `ShapeFun.app` (search for the maximal entry below the
   input), which relied on saturation.  The output of an entry must instead
   be typed at *some* code in the directed set of codes the family graph
   yields at that label and input.

Item 5 is the only real work; 1–3 are master's lemmas, 4 is routine given
`LabelEq.subst`.

### 4.3 `Interp` (one constructor per term former, as `LE_Interp`)

Stage `(Δ, σ)`; `ρ` a single-shape valuation at `Δ`; labels are the
current-stage terms `A[σ]`, `a[σ]`.

* `bot`, `bvar` (`x ≤ ρ i`), `sort`, `unit`, `star ↦ ⊥`, `nat`, `zero`.
* `app f a`: `Interp f … F`, `Interp a … x`, `Γ ⊢ A : sort u`,
  `Γ ⊢ a : A`, `m ≤ F.app ((A[σ], a[σ])) x` (graph lookup at the label
  with `LabelEq Δ`, our `ShapeFun.app` with label matching).
* `lam A b`: `Interp A … d`, `m ≤ lam' g`, and every entry
  `((A', t), x, y)` of `g` is valid: `∃ u, Δ ⊢ A' ≡ A[σ] : sort u`,
  `Δ ⊢ t : A'`, and for every `x'` with `x'.HasType d`,
  `Interp b Δ (σ.cons t) (ρ.push x') y` — master's binder rule, with the
  stage extended by the label term.
  The label term `t` is substituted for the bound variable *in the
  stage*; the decoded approximant `x'` is pushed on the valuation (his
  normalized body action, with a single approximant instead of the
  retracted ideal — fine since the decoded set is directed and `Interp`
  is monotone in `ρ`).
* `forallE A B`: `m ≤ forallE (A[σ], B[σ.lift]) d g` with `d ∈ ⟦A⟧` and
  `g` valid for `B` as above (its outputs are codes for `B(t)`).
* `sigma`/`pair`/`fst`/`snd`: as Π/λ/app, with the label of the pair.
* `id r A a b ↦ id r (A[σ]) (a[σ]) (b[σ])` (label only, no sub-shapes);
  `refl true a`: `m ≤ refl v` with `v ∈ ⟦a⟧`; `refl false a ↦ ⊥`.
* `tr r A a b C x h` (master's constructor unchanged, except that `C` is
  evaluated at the stage `σ.cons b`):
  `m' ∈ ⟦x⟧`, `v ∈ ⟦a⟧ ∩ ⟦b⟧`, `c ∈ ⟦C⟧ Δ (σ.cons b) (ρ.push v)`,
  `m'.HasType c`, and `(r = true → refl v ∈ ⟦h⟧)`. Sound for `tr_refl`
  exactly as today (`Sound.lean:2734`); `r = false` ignores the proof, as
  intgrah does.
* `natCase`, `Y`: `Y` as `Interp (Y A b) … x' → Interp b Δ (σ.cons (Y A b)) (ρ.push x') y → Interp (Y A b) … y`.
* `proofIrrel` needs nothing: prop-typed approximants are `⊥` because
  nothing non-`⊥` is typed at a `prop` code.

### 4.4 Admissibility, properties, soundness

`Adm Γ Δ σ ρ` by recursion on `Γ` (master's `Valuation.Fits`):
for `A :: Γ`, `Adm Γ Δ σ.tail ρ.tail` and `ρ 0` typed at `A` at stage
`σ.tail`. The properties of §2.7 restated over the relation (all
"`∀ Δ σ ρ, ⊢Δ → Δ ⊢ σ : Γ → Adm Γ Δ σ ρ → …`"): equality of the
approximant sets (`HasEquality`), typedness of every approximant
(`HasFixedness`), the substitution lemma (`HasSubstitution`), and
`PiReady` collapses into the join/directedness lemmas. `RawJudgment` as a
structure of these Props, in `DomainSemantics/Presheaf.lean` next to
`Sound.lean`; the induction on `IsDefEq` in `PresheafSound.lean`;
inversion in `PresheafInversion.lean`, feeding `Consequences.lean`.

## 5. Language coverage (master `Term.lean` + the flagged equality)

| construct | model | status |
|---|---|---|
| `sort`, `forallE`, `lam`, `app`, `proofIrrel` | as his, on our shapes | core of the work |
| `id r A a b`, `refl r a`, `tr r …` (the `eq` worktree's syntax: one `Bool` flag, `id r A a b : sort r`) | label-only `id r` shape; `refl` shape kept for `r = true`; `tr` inspects the proof only when `r = true` | both equalities at once; syntactic side (Term.lean, substitution lemmas) to be taken from the `eq` worktree's uncommitted diff (`/home/mario/claude-test/domain-semantics-lean-2`, 141 changed lines in `Term.lean`); keeps `not_UIP` for `r = true` |
| `unit r`, `star r`, `unit_eta` | atom, `star ↦ ⊥`, decodes to `⊥` | cheap |
| `sigma`, `pair`, `fst`, `snd` | Σ-shape with `(A,B)` label, componentwise retraction | mirrors Π |
| `nat`, `zero`, `succ`, `natCase` | our shapes; `natCase` inductive like `Y` | after Π |
| `Y A b`, `Y_unfold` | inductive constructor, least fixed point for free | after Π |

## 6. Obligations, roughly ordered

1. ~~Syntax: port the flagged equality from the `eq` worktree into
   `Term.lean`.~~ **Done** (commit `a4a5f60`). The whole `eq` diff was
   applied, semantic side included, so the old proof keeps building; it
   carries one `sorry` in `Adequacy.lean` (the `r = false` transport
   case), which is precisely what this branch replaces. `not_UIP` is
   unaffected and stays axiom-clean. `Shape.lean` is now `ShapeOld.lean`.
2. `Shape.lean`: **mostly done** (`4a4c007`, `87736ee`, `55f6a68`).  Labels
   on entries/`forallE`/`sigma`/`id`; `WF`; `LE Δ` with `LabelEq`, proved
   reflexive (under `WF`) and transitive; `le_bot_iff` and the collapse
   lemma; `Compat` carrying the coherence implication; the `Join` relation
   and a `join` witness; `Shape.subst` and `LE.subst`; `join_le`,
   `le_join` and `exists_join`; `WF.subst`, `IsBot.subst`, `join_subst`,
   `subst_subst`, hereditary `Compat` with `Compat.subst`; `IsBot`
   decidable and `isBot_subst_iff`.  Plus `Ctx.SubstEq.comp` in
   `Term.lean`.  **Done**, modulo the Σ label (§5).

   Final shape of the collapse story: rather than carrying
   information-free λ-shapes around and giving `LE`, `Compat` and `join`
   collapse clauses for them, `Shape.WF` now excludes them — a λ-graph
   must be non-empty with no bottom output.  This is master's `NonZero`,
   strengthened from "some entry is non-bottom" to "every entry is",
   which is what lets the bottom escape disappear from `ShapeFun.LE` as
   well.  Legitimate where saturation was not: being information-free is
   structural, never inspects a label, and so is invariant under
   substitution in both directions (`isBot_subst_iff`) and decidable.
   Net effect: the escape clause, the `LE` collapse clause, both mixed-`lam`
   clauses of `Compat`, both of `join`, and the lemmas `IsBot.le` and
   `ShapeFun.LE.append_bot` are all gone, and `le_bot_iff` strengthens to
   `s ≤ ⊥ ↔ s = ⊥`.

   A bug found and fixed while proving `le_join`: the first `join` returned
   `⊥` whenever the heads differed, which is wrong when one side is an
   information-free λ-shape — that is compatible with anything, so the lub
   is the *other* side.  The other repo's `cSup` has exactly the two
   clauses for it (`| .lam _, b => b`, `| a, .lam _ => a`), and no test for
   information-freeness is needed: `Compat` already forces a λ-shape facing
   a different head to be `IsBot`.  Adopting those clauses also let the
   `if r = r'` guards on `sort`/`unit` go, since `Compat` supplies the
   equality; the definition is now a faithful copy of `cSup` and `join_le`
   got shorter.

3. `HasType` on labelled shapes: **defined**, with `Evaluates` as the
   relational graph lookup and `HasDom`.  Proved: `HasType.bot` (master's
   conditional form), `HasType.cumul`, `HasType.isType`, `Evaluates.subst`,
   `HasDom.subst`, `HasType.subst`, `Evaluates.compat`, `Evaluates.wf`,
   `Evaluates.mono_graph`, `HasType.mono_r`, `HasType.join`,
   `Evaluates.bounded`, `HasType.bot_r`, `HasType.proofIrrel`.  **Left:**
   the Σ label (§5).

   **`mono_r` and typed joins are mutually recursive on the level** and so
   are proved together, as `HasType.mono_r_join`.  Master proves them
   separately: there, `mono_r`'s λ case moves an entry's code from the
   smaller graph to the larger one through the *function* `ShapeFun.app`,
   which is monotone outright.  Here that step is `Evaluates.mono_graph`,
   and its `join` case must show the joined witness is still a type — that
   is the typed-join lemma, one level down.  Typed joins in turn need
   `mono_r` one level down, to retype an entry's domain check from one of
   the two domain shapes at their join.  Both descend, so a single
   induction on the level with a conjoined motive does it; `mono_graph`
   therefore takes the typed-join property as a hypothesis rather than
   proving it.

   `Shape.WF.coherent` (a well-formed shape is compatible with itself) was
   added to `Shape.lean` for the λ case, which has to supply
   `mono_graph`'s `Shape.Compat Δ x x` for the entry input `x`.  It is
   immediate now that internal coherence is a conjunct of `WF`.

   **Prop collapse** (`HasType Δ a .prop → HasType Δ x a → x = ⊥`) is
   proved as `HasType.proofIrrel`, with `WF` on both arguments.  Every
   case but Π is a head clash; the Π case is where saturation is missed a
   third time.  Master reads the codomain off the graph with the function
   `ShapeFun.app` and recurses on its value.  Here the codomain comes out
   of `Evaluates`, which may hand back a *lowering* of an entry output,
   and `HasType · (.sort r)` is **not** downward closed — master's
   `mono_l` is an equivalence (`m ≤ m'` together with `m' ≤ m`), not
   monotonicity, so it is no help.  The way round is `Evaluates.bounded`:
   every witness is below a witness that is a type, which is just
   `mono_graph` instantiated at `f' = f` (hence the new
   `ShapeFun.LE.refl_aux`), and `mono_r` retypes the entry output there.
   The contradiction is then master's, with non-degeneracy standing in for
   `lam'`: a well-formed λ has a non-`⊥` output, but the recursion says
   that output is `⊥`.

   Corrections made along the way.

   (a) **`HasType` is not monotone on the left** (in the subject), and no
   attempt should be made to make it so.  Where downward closure is
   needed, close downwards *explicitly at the use site* — which is exactly
   what `InterpTyped`'s `∃ m' a, m ≤ m' ∧ …` does.  So the obligation
   "the typed set is lower-closed" was misstated: `InterpTyped` is lower
   closed by construction, `HasType` is not.

   (b) There is **no separate `IsCode`**: a shape is a code exactly when
   it is a type, `HasType a .type`, because the two universes are
   cumulative in the model.  `HasType.cumul` is proved.  (I briefly added
   an `IsCode` copied from the other repo, which needs one because it has
   no typing relation on shapes at all; with `HasType` available master's
   route is right.)

   (c) `HasType`'s `succ` clause uses a nested match on the level, as
   master's does; splitting the outer level pattern stops the final
   catch-all from reducing.

   (d) **`isType` forced two further corrections**, both restoring
   master's shape: the `⊥` clauses are given per type former rather than
   blanket, and the `lam`/`pair` clauses carry the well-formedness of the
   Π/Σ type they inhabit.  Without these, `HasType ⊥ a` holds for shapes
   `a` that are not types at all, and `isType` — hence `mono_r`, hence
   prop collapse — cannot even be stated.

   (e) `Evaluates` closes under the `join` **function** rather than the
   `Join` relation.  That was impossible while the function was wrong, and
   is what makes `Evaluates.subst`, hence `HasType.subst`, go through:
   `join` commutes with substitution on the nose, whereas `Join Θ`
   quantifies over more shapes than the image of the substitution.

   **The two obstructions in `mono_r`: both now discharged.**

   * ~~`HasType Δ d' .type` for the larger Π's domain.~~ **Done.**  Master
     derives it from `HasDom.isType`, which works there only because
     saturation makes every graph contain a `⊥`-input entry, so the domain
     has an inhabitant.  With saturation gone it is stated: `HasType Δ d
     .type` is a conjunct of the Π/Σ type clauses.
   * ~~`Evaluates.mono_graph`, whose `join` case needs the two witnesses to
     be compatible.~~ **Done** (`d9339ac`), via `Evaluates.compat`: every
     pair of shapes one lookup returns is compatible, given the graph and
     the query shape are coherent.  Coherence asks for the two entries'
     *inputs* to be compatible, and the query supplies exactly that, both
     lying below the query shape, so `Compat.of_common_upper` applies.
     Supporting lemmas proved along the way: `Compat.symm`,
     `Compat.anti_right` (one-sided on purpose — a two-sided induction
     would need reflexivity of `LE`, which holds only on well-formed
     shapes and would drag `WF` into every use), `Compat.anti`,
     `Compat.of_common_upper`, `Shape.join_compat` (the other repo's
     `cSup_compatible`), and `Shape.subst_id`.

   **`Evaluates.lower` carries a `WF` premise.**  The lookup is a lower
   set, as in the other repo, but lowering is constrained to well-formed
   shapes.  Unconstrained lowering makes `Evaluates y → WF y` false, `WF`
   not being downward closed (a smaller λ-shape may have a bottom output),
   and then `mono_graph` has to take the `⊔`-upper-bound property as a
   bare hypothesis.  With the premise, `Evaluates.wf` is structural — `⊥`,
   an entry output, a join of those (`Shape.WF.join`), or an explicitly
   well-formed lowering — and `mono_graph` takes only
   `∀ e ∈ f', WF e.out` and discharges `le_join` itself.

   Master avoids both because its saturated `ShapeFun.app` is a
   *function*, monotone by `app_mono_l`, so there is no existential to
   re-join.  That is the real price of dropping saturation, and it is
   payable.

4. Prerequisites **done**: `Shape.lift` / `ShapeFun.lift` / `lift_self`, the
   total shape domain `TShape := Σ n, Shape n` with `TShape.LE`, `WF`,
   `bot`, `sort` (master's, labels carried through; lifting *down*
   collapses to `⊥`).

   The **lifting layer** is now complete, since `Interp` quantifies over
   `TShape` and so every notion it mentions has to transport along
   `Shape.lift`: `lift_lift`, `lift_le_lift`, `lift_subst`, `lift_isBot`,
   `lift_compat` (with `ShapeFun.lift_compat`), `lift_wf`, `lift_join`,
   `Evaluates.lift`, `HasType.lift_mono`.  On top of them the total level
   gets `subst`, `Compat`, `join`, `HasType`, the four `def` lemmas that
   replace the canonical level by any level above both arguments, the
   same-level forms (`LE.T`, `WF.T`, `Compat.T`, `join.T`, `HasType.T`),
   and the order itself (`LE.refl`, `LE.trans`, `bot_le`, `le_bot_iff`).

   Two differences from master, both consequences of earlier decisions.

   * `lift_compat` has to **generalise the context** in its induction,
     because `Compat`'s graph clause is hereditary and moves to a later
     stage `Θ`.  Master's `Compat` is context-free.
   * `HasType.lift_mono` is **one-directional**, where master's
     `HasType.lift` is an equivalence.  Lifting up preserves typing; the
     converse fails because `Evaluates.lower` can produce a witness at the
     higher level that is not the lift of anything — the order on graphs
     is contravariant in the input, so a shape below a lifted shape need
     not itself be a lift.  Master has the equivalence only because its
     lookup is a function.  One direction suffices: `TShape.HasType` is
     defined at the canonical level and read off at any higher one
     (`TShape.HasType.def`), and constructed at a common level
     (`TShape.HasType.T`).  For the same reason `join.T` is stated through
     `lift` rather than as an equation of `TShape`s, `max n n` being only
     propositionally `n`.

   **Positivity verified** by a spike
   (`scratchpad/spike-interp.lean`): the inductive `Interp` over
   `Term → (Δ : List Term) → Subst → Valuation → TShape → Prop`
   elaborates, including the `lam` premise quantified over graph entries
   and the self-referential `Y` constructor, and `induction` works on it.

   The technique that makes it go through: **split every conjunction into
   separate premises**.  The kernel rejects a nested inductive occurrence
   under `And`, `Or` or `Exists` (as it did for `LE`, appendix B.3), so the
   `lam` clause is written as several `∀ e ∈ g, …` premises in a row
   rather than one premise with a conjunction inside, leaving the `Interp`
   occurrences under `∀` and `→` only.

   Then `Interp`, `Adm`, and the structural lemmas: `mono` (in the
   shape and in `ρ`), `join`, naturality along typed `τ`, `weak`, `subst`
   (the `∃ ρ'` form), `inst`.
5. `RawJudgment` and the soundness induction: structural rules, binders
   (`lamDF`, `forallEDF`, λ fixed under Π), `appDF`, `beta`, `eta`,
   `proofIrrel`, id/unit rules, then Σ, Nat, `Y`.
6. Inversion (`forallE_inv`, `sort_inv`, `id_inv`, `sigma_inv`,
   no-confusion) against the *statement* of soundness first, then hook up
   `Consequences.lean`; delete `Sound`/`LogRel`/`Adequacy`.

## 7. Remaining open points

1. **Coherence (decided).** Typed functions are genuinely label-sensitive
   (`λx:type. Πy:x.y` must output Π-shapes labelled by the argument, or
   Π-inversion through β fails), so whether two entries may have
   incompatible outputs depends on whether their labels can ever be
   identified by a typed substitution. Hence no context-free WF works and
   "prove it from typing" would make `join`/`compat` typed-only. The
   invariant is hereditary coherence relative to a context:
   `Coherent Δ x := ∀ Θ τ, ⊢Θ → Θ ⊢ τ : Δ → LocallyCoherent Θ (x[τ])`, with
   `LocallyCoherent Θ y` = for entries `(a₁,u₁,v₁)`, `(a₂,u₂,v₂)` of any
   graph inside `y` (and, for joins, of two graphs approximating the same
   function): `a₁ ≡_Θ a₂ → Compat Θ u₁ u₂ → Compat Θ v₁ v₂`, recursively.
   Needed lemmas: downward closed under `LE Δ`, closed under compatible
   joins, preserved by typed substitution. It is imposed **as a premise
   `Coherent Δ m` on every constructor of `Interp`** and on admissible
   valuations, so shapes stay context-free and the structural lemmas
   hold for all raw terms as in `Sound.lean`; the alternative is his
   context-indexed subtype `WShape Δ n`. The old `WShape.WF` (graph WF,
   `HasDom`, `NonZero`) goes away.
2. **Directedness.** Needed for the retraction equation (argument side)
   and hence β; η goes through "both sides are abstractions of the same
   body action". No way found to drop it; it is the `join` lemma.
3. **`Bool` vs `Prop` in `Shape.lean`.** `ble`/`Compat` are decidable
   today; with defeq in labels they become `Prop`s. Small mechanical
   change, but it touches most of the file.

## Appendix A. Three-way comparison

Every definition, across the three developments: the **other repo**
(`intgrah/domain-semantics-lean`), **master** (this repo's logical-relation
proof, now `ShapeOld.lean` / `Sound.lean` / `LogRel.lean` / `Adequacy.lean`),
and **this branch**.  A dash means the notion does not exist there.  Rows
marked ✱ are where this branch differs from master, and are the ones worth
reading.

### A.0 Shapes

| notion | other repo | master | this branch |
|---|---|---|---|
| shape type | `Shape Γ`, context-indexed, unstratified | `Shape n`, level-graded | `Shape n`, level-graded ✱ labels added |
| graph | `k` + `names`/`ins`/`outs` families, `names : Σ A : Ty Γ, Tm Γ A` | `List (Shape n × Shape n)` | ✱ `List (Entry (Shape n))`, `Entry` = `(ty, tm, inp, out)` |
| argument label | intrinsic: a typed term in the quotient | — | ✱ raw `(ty, tm)`, compared by `LabelEq Δ` |
| Π label | `Σ A : Ty Γ, Ty (Γ.extend A)` | — | ✱ raw `(A, B)`, compared by `PiLabelEq Δ` |
| Id shape | `id (ty lhs rhs : Shape Γ)`, no relevance flag — its Id is proof-*irrelevant* | `id (rel) (A a b : Shape n)` | ✱ `id (rel) (A a b : Term)` — labels only |
| `refl` | **none**: no such constructor, `⟦refl a⟧ = ⊥`, forced by proof irrelevance | `refl (w : Shape n)` | master's `refl (w : Shape n)`, used only at `rel = true`; at `rel = false` the interpretation is `⊥`, as in the other repo |
| depth device | `rank` + `piStage`/`piLimit` fixed point | the level index | the level index (so no fixed point) |
| substitution on shapes | reindexing along `σ : Γ₁ ⟶ Γ` (functorial) | — (shapes are context-free) | ✱ `Shape.subst`, structural, no typing hypotheses |

### A.1 Order, bottom, compatibility, join

| notion | other repo | master | this branch |
|---|---|---|---|
| order | `LE` judgement, `Prop` | `ble`, `Bool`, decidable | ✱ `Shape.LE Δ`, `Prop`, context-indexed |
| entry coverage | `Entry` judgement, `bottom` + `mem` | inside `ble`, no bottom escape | `ShapeFun.LE` with the `out ≤ ⊥` escape |
| information-free λ | `IsBottom` + `LE.collapse` | normalised away: `NonZero` / `lam'` | excluded by `WF`: a λ-graph is non-empty with no bottom output |
| graph well-formedness | coherence only | saturation: `⊥`-input entry, join-closed inputs, monotone samples | ✱ non-degeneracy only (master's `NonZero`, per entry); saturation dropped, since label classes merge under substitution |
| compatibility | `Compatible σ`, hereditary *inside the graph clause* | `Compat`, `Bool`, structural, local | ✱ `Compat Δ`, `Prop`, hereditary inside the graph clause (copied from the other repo) |
| coherence | `IsCoherent` / `InternallyCompatible` (separate) | part of `Compat`/`WF` | part of `Compat Δ` |
| join | `cSup` + `sup` for compatible pairs | `join` re-applying both graphs (needs saturation) | ✱ append on graphs; no mixed-`lam` clauses, since a well-formed λ is never information-free |
| join as relation | `CondSemilatticeSup` instance | `WShape.Join` | `Shape.Join Δ`, with `exists_join` |
| preservation under substitution | functoriality, free | — | ✱ `LE.subst`, `WF.subst`, `IsBot.subst`, `Compat.subst`, `join_subst` |

### A.2 Typing of shapes

| notion | other repo | master | this branch |
|---|---|---|---|
| typing relation | **none** — typing *is* being a fixed point of a code's retraction | `hasType` (`Bool`) → `HasType` → `HasTypeU` → `unfold_iff` | ✱ `HasType Δ`, `Prop`, defined directly and context-indexed |
| the decoder | `CodeAssignment`, `eval`, `rawExtend`, `extend`, `decode`, `IsIdempotent`, `IsPayloadStrict` | — | `InterpTyped` / `SoundTy` over `HasType` (§4.2) |
| Π retraction | `resultOperator`, `arrow`, `piOperator`, `graphAction` | in the `lam`/`forallE` clauses of `LE_Interp` | as master |
| fixed point | `piStep` / `piStage` / `piLimit` + rank stability | — | — (recursion on the level) |
| graph lookup | `Evaluates` (relation, closed under `⊥`, lowering, joins) | `ShapeFun.app` = `maxBelow (trunc f a)` (needs saturation) | ✱ `Evaluates` (relation), closing under `Join Δ` |
| "is a type" | `IsCode r`, separate and downward closed | `HasType a .type`, universes cumulative | `HasType a .type` (master's), with `HasType.cumul` |
| universe | `universeIdeal`/`universeOperator` restrict to codes | `⟦sort l⟧` is the principal ideal `↓(.sort l)` | as master |
| monotonicity | — | `mono_r` (on the *type*, with the larger type a type) | as master; **not** monotone on the left |
| downward closure | built into the ideals | explicit: `InterpTyped`'s `∃ m', m ≤ m' ∧ …` | as master, explicit at each use site |
| proof irrelevance | prop codes decode to `⊥` | `HasType.proofIrrel` | as master |

### A.3 Values and the interpretation

| notion | other repo | master | this branch |
|---|---|---|---|
| a value | `RawValue = ΩLower`, a Kripke lower set | a single shape `TShape` | a single shape (master's) |
| an ideal | `ΩIdeal` = lower set + directed | directedness is the `join` lemma | as master |
| valuation | `ℕ → RawValue` | `ℕ → TShape` | `ℕ → TShape` (master's) |
| denotation of a term | `RawFamily`: stage-indexed map from valuations to values | `LE_Interp ρ m M`, inductive | ✱ inductive, with a **stage** `(Δ, σ)` added |
| stage | `σ : Γ₁ ⟶ Γ`, feeds labels only | — | ✱ a substitution, feeds labels only |
| continuity | `IsFinitary` everywhere, `Filter` of approximations | the `∃ ρ'` + join trick in `subst` | as master (operations are basis-defined) |
| binder rule | section + normalised body action | `∀ x, x.HasType a → …` | ✱ master's, with the stage extended by the label term (`σ.cons t`) |
| admissibility | `SourceAdmissible` | `Valuation.Fits` | master's |
| soundness bundle | `RawJudgment` (6 components) | `StrongSound` / `SoundEq` / `SoundTy` | `RawJudgment` expressed over master's notions |
| adequacy | none needed | `LR` + `LR.adequacy` (2.2k + 2.7k lines) | none needed ✱ |
| inversion | from labels, out of soundness | from adequacy + weak-head reduction | ✱ from labels, out of soundness |

### A.4 What each development spends its lines on

| | other repo | master | this branch (projected) |
|---|---|---|---|
| category/presheaf scaffolding | ~5k | — | — |
| shapes, order, join | ~1.6k | ~4.4k | ~0.9k so far |
| typing / decoder | ~2.3k | in `ShapeOld` | `HasType.lean`, small |
| interpretation | ~3k | `Sound.lean` ~2.9k | item 4 |
| logical relation + adequacy | — | ~4.9k | — |
| soundness | ~2.6k | in `Sound.lean` | item 5 |

## Appendix B. Two experiments on the shape order

Both run on the branch; the first settled a question, the second is a
design option that is still open.

### B.1 Type-free entry labels: rejected

`Entry` was first written with a bare `tm : Term` and label equality
`TmEq Δ a a' := ∃ A, Δ ⊢ a ≡ a' : A` (`Label.lean`). Everything works
except **transitivity**: chaining `Δ ⊢ a ≡ a' : A` with `Δ ⊢ a' ≡ a'' : B`
needs `Δ ⊢ A ≡ B`, i.e. uniqueness of the type of `a'` — the theorem the
model exists to prove. `IsDefEq.trans'` does not help, being heterogeneous
only for *sort*-typed equations. Transitivity of the shape order reduces
to exactly this (`ShapeFun.LE.trans_of`), so the label must carry its
type: `Entry` has `ty` and `tm`, and `LabelEq` is used. `TmEq` is kept in
`Label.lean` with its `trans` sorry'd, as the record of the obstruction.

Note the same problem does *not* affect Π/Σ or Id labels: their type
components are types, whose "type" is a sort, so `trans'` applies. That is
why `PiLabelEq`/`IdLabelEq` need no stored type.

### B.2 Plain defeq, no syntactic escape clause

The label relations originally had a syntactic-equality disjunct
(`(A = A' ∧ a = a') ∨ …`) to stay reflexive on ill-typed labels. Dropped:
they are now plain definitional equality, hence partial equivalence
relations, and reflexivity of the order holds exactly on **well-formed**
shapes. `Shape.WF Δ` (every label well-typed in `Δ`) is the new
side condition of `Shape.LE.refl`. Unlike the old `ShapeFun.WF`, this is a
real invariant of the model: interpretations only ever produce well-typed
labels.

### B.3 One inductive relation instead of the recursive order

`Shape.LE` is currently defined by recursion on the level, with the label
relations named (`LabelEq`, `PiLabelEq`, `IdLabelEq`). The alternative is
a single inductive relation with the defeq premises inlined, which would
give inversion by `cases` for free.

The naive version is **rejected by the kernel**: the graph-coverage
premise nests the relation under `Or`/`Exists`
(`∀ e ∈ f, LE e.out ⊥ ∨ ∃ e' ∈ f', …`), and Lean reports
`invalid nested inductive datatype 'Or'`.

It does work with the standard sum-index trick — one inductive family over
`(Shape n × Shape n) ⊕ (ShapeFun n × Entry (Shape n))`, so that the
disjunction and the existential become *extra constructors* rather than
nested types, with `abbrev`s recovering the two readable names. Verified
by a spike (kept at
`scratchpad/spike-inductive-le.lean`): the kernel accepts it and
`induction` works on it.

Open: whether to switch. In favour, one relation and free inversion.
Against, `refl`/`trans` need reworking, and the named label relations are
wanted anyway downstream (graph lookup in `Evaluates`, the coherence
condition, the `app` rule of `Interp` all compare labels), so inlining
them into the order does not actually remove them from the development.
