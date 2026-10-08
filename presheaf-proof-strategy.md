# Proof strategy for elementary soundness (presheaf branch)

Companion to `presheaf-plan.md`.  That document records the design and its
history; this one is a *proof strategy*: for each key lemma and for a
selection of cases of soundness it says what the statement should be, what
the proof does move by move, and where that move comes from in the two
originals.  "His" is intgrah's `presheaf-semantics-lean`; "master" is this
repo's `master` branch (`Sound.lean`, `Shape.lean`).  Nothing here assumes
the statements currently in the tree are right; §2 proposes corrections.

The organising principle, and the one that decides where directedness
lives (§2.3): **his hypotheses are our constructions.**  Every field of his
`RawTermProperties` and every side condition of his `SourceAdmissible` is a
fact that comes for free from the *type* of the object he builds — an
`ΩIdeal` is directed, a morphism of `Ctx` is typed, `rawExtend T X` is a
`bind₂` of ideals and so directed and idempotent.  We build no such
objects: a value is one shape, a stage is a raw substitution, a type is a
relation on shapes.  So each of those free facts becomes either a lemma
about our constructions, a hypothesis on a lemma, or an extra premise on a
constructor.  The table in §1 says which, for each.  The rest of the
document follows those decisions through.

Notation: `Δ ⊢ σ : Γ` is `Ctx.SubstEq Δ σ σ Γ`; `x ⊔ y` is `TShape.join`;
`⟦t⟧` is the approximant set `{m ∣ Interp Δ Γ t σ ρ m}`.

---

## 1. What his hypotheses become

Read down the middle column: that is the list of things we have to prove
or state, and it is the whole difference between the two developments.

| his | ours | status |
|---|---|---|
| `IsDirected` of an `ΩIdeal` (a field) | `SoundDir Γ t` (§2.3), a lemma by induction on typing | **to restructure**: currently a conclusion of `IsDefEq.sound` |
| `IsDirected` conclusion `∃ c ∈ L, a ≤ c ∧ b ≤ c` | `sound_dir_of_ub`: common WF upper bound in `⟦t⟧` | done; it is *his* statement, `Compat ∧ join` is master's derived form |
| `Compatible.of_common_upper` | `TShape.Compat.of_common_upper` | done |
| morphism `σ : Γ₁ ⟶ Γ` of the quotient category | `⊢ Δ` and `Δ ⊢ σ : Γ` carried as hypotheses | done (the `Stage`) |
| equality of morphisms mod defeq (free) | `Interp.stage` | **done** (§3.1b–c): structural in the term, each clause carrying what moves its own label; `IsDefEq.stage` is it, fed `H.annot.1` |
| functoriality in the stage (free) | `Interp.subst` | done (naturality) |
| `Ty`/`Tm` quotients: labels equal mod defeq | `LabelEq`, `PiLabelEq`, `IdLabelEq` in `LE`/`Compat` | done |
| `Ctx.extension` is *not* quotiented: `A::Γ` vs `A'::Γ` need `contextConversion` + `HasRenaming` | `Interp.ctx` (the context index is phantom) | done, free |
| `SourceAdmissible`: slot directed, `rawExtend ⟦A⟧ (ρ 0) = ρ 0` | `Adm.cons`: slot WF, typed at an approximant, `⟦A⟧` saturated | done |
| `SourceAdmissible.pullback` | `Adm.subst` | stated, sorried; **probably not needed** (§3.5).  What *was* needed is `Subst.Saturates` (§3.1e), the original's `SourceAdmissible`+`SingleSubstitution` |
| `SourceAdmissible.push` at `rawExtend ⟦A⟧ X` | `Adm.cons` at a *typed* slot; the binder rules' `hdom` premise supplies it | done for the binder congruences |
| `rawExtend_isDirected` + idempotent (free) | `SoundJoin` | **avoidable for Π/λ** (§2.3), **needed for `tr`** (§4.7) |
| `normalizedBodyAction`: body evaluated at `rawExtend ⟦A⟧ x` | binder rules evaluate the body at the entry input `e.inp`, and demand `HasType e.inp d` | see η, §4.5: this is where the choice bites |
| `application_piOperator_fixed`: a Π-fixed function's lookup depends only on the normalised argument | its *support* half is `Interp.lam_label_ty` (§3.1d); the *normalisation* half has no counterpart | the support half is used; normalisation is **still needed by η** (§4.5) |
| `IsIdealValued` (body action directed at *every* input) | `SoundDir (A::Γ) B` at every WF slot | follows once `SoundDir` takes `Valuation.WF` |
| `PiReady Γ A B` stored in the *type's* `RawTermProperties` | `SoundDir Γ A`, `SoundDir (A::Γ) B` from the typing of the binder | see η: recovering `A`'s typing from `Γ ⊢ e : Π A B` is the issue |
| `HasFixedness Γ t A` | `SoundTy Γ t A` (`InterpTyped`) | as master |
| `HasEquality` | `SoundEq` | as master |
| `HasSubstitution` / `HasRenaming`, **fields of `RawTermProperties` proved inside the main induction** | `Interp.substTerm` (∃ρ' form), `Interp.weak'`/`unweak`, as *standalone* lemmas taking the induction's own conclusions (`Term.Pinned`, `Subst.Saturates`) as hypotheses | **done** (§3.1d–f); the data the original keeps in the induction is passed in instead |
| `SingleSubstitution.variable_eq` | `Interp.bvar_iff` | done |
| `sourceQuery a` (sup over all typings of the argument), transported as the **image of a set** | the `app` rule names the type `A` in `Δ`, one lookup | **wrong as stated** (§5.5b): naming `A` does not remove the obstruction, it relocates it — and §3.1d is where the relocated one surfaced |
| `rawExtend ⟦C[b/]⟧ ⟦x⟧` as the value of `tr` | master's `tr` constructor with two `HasType` premises | as master; §4.7 |
| `regular` field of `RawJudgment` | — | he never uses it; drop |
| `IsCode r` separate from inhabitation | `HasType · (sort r)` | done, cumulative |
| conditional sup `cSup`, `CondSemilatticeSup` | `Shape.join` + `Compat` | done |
| `Graph.IsCoherent`, `InternallyCompatible` | the coherence conjunct of `Shape.WF` (hereditary, label-sensitive) | done |
| `Graph.LE` = single-entry coverage (`Entry.mem`) | `ShapeFun.LE`, same | stays; lookup coverage is **impossible** here (§5.2), so η needs another route |
| an ideal is closed under every graph valid for its action | — (a value is one shape) | the previous row is the replacement |

Three of these rows are design decisions rather than lemmas, and the
document is organised around them:

1. **Directedness is a separate lemma**, `IsDefEq.dir`, proved *before*
   `IsDefEq.sound` by its own induction on typing, with `Valuation.WF` in
   place of `Adm` (§2.3).  **This is the one row that does not survive
   contact with `app`** — see §5.5b.  His `HasIdeality` is bundled into
   `RawTermProperties` because `HasIdeality.app` takes
   `HasFixedness Γ f (.forallE A B)`, and ours needs the same thing for the
   same reason; naming the type in the clause does not avoid it.  What is
   *also* typing-dependent, and genuinely is the residue of his quotient,
   is the *stage*: under a binder the label term extends the stage, and the
   extended stage is typed only if the binder annotation is.  That is why
   `IsDefEq.stage` is an induction on typing and not on the raw term.
2. **The graph order cannot be lookup coverage** (§5.2), though η wants
   it to be.  An order defined through the lookup does not reflect along
   `lift`, and `lift_le_lift` is what makes the level index invisible.
   Master escapes by saturation, the other repo by having no levels; we
   have neither escape, so η is the open case.
3. **Two things stay open**, both about `Σ`: join-closure of a type's
   extension, needed by `tr` (§4.7), and nothing else once (1) is done.

---

## 2. Statement architecture

### 2.1 Order of lemmas

```
Shape.lean / HasType.lean      shape-level facts, all context-relative        [done]
Interp.lean
  Interp.mono, mono_val, ctx   structural                                      [done]
  Interp.subst                 naturality in the stage                         [done]
  Interp.weak', unweak         renaming in the term                            [weak' done]
Presheaf.lean
  IsDefEq.stage                stage invariance under defeq, by ind. on typing [§3.1]
  IsDefEq.dir                  directedness, by ind. on typing                 [§3.2]
  Interp.substTerm, inst       ∃ρ' substitution, parameterised by directedness [§3.3]
  IsDefEq.sound                SoundEq ∧ SoundTy, by ind. on defeq             [§4]
Inversion.lean                                                                  [done modulo Σ]
```

Each line uses only the lines above it.  In particular `IsDefEq.sound`'s
cases call `IsDefEq.dir` and `Interp.inst` as lemmas, at the typing
derivations the rule's premises supply; they never re-prove directedness.

**This layering is what the clause conditions pay for** (§3.1d).  The
original layers `dir` this way too — `HasIdeality` is a field of its
bundle, but its `app` case takes the function's fixedness — and it does
*not* layer substitution: `HasSubstitution` is a field of
`RawTermProperties`, proved in the same induction, and its `app` case
consumes that fixedness.  Putting `Interp.substTerm` below `sound`
deprives its `app` case of the only thing that pins the label; rather
than move the lemma up, the data is passed down, as `Term.Pinned` and
`Subst.Saturates` hypotheses that the soundness induction supplies
(§3.1e–f).  `IsDefEq.dir` needs neither, so it stays independent.

### 2.2 Definitions to keep

`Interp` as is, with one addition (§2.4).  `Adm` as is.  `InterpTyped`,
`SoundEq`, `SoundTy` as is.  `sound_dir_of_ub` as is.

### 2.3 `SoundDir`, restated

Current:

```lean
def SoundDir (Γ t) := ∀ {{Δ Γ₀ σ ρ}}, ⊢ Δ → Δ ⊢ σ : Γ → Adm Δ Γ₀ Γ σ ρ →
  ∀ {m₁ m₂}, Interp Δ Γ t σ ρ m₁ → Interp Δ Γ t σ ρ m₂ →
    TShape.Compat Δ m₁ m₂ ∧ Interp Δ Γ t σ ρ (m₁ ⊔ m₂)
```

Proposed:

```lean
def SoundDir (Γ t) := ∀ {{Δ σ ρ}}, ⊢ Δ → Δ ⊢ σ : Γ → Valuation.WF Δ ρ →
  ∀ {m₁ m₂}, Interp Δ Γ t σ ρ m₁ → Interp Δ Γ t σ ρ m₂ →
    ∃ s, TShape.WF Δ s ∧ Interp Δ Γ t σ ρ s ∧ TShape.LE Δ m₁ s ∧ TShape.LE Δ m₂ s

theorem IsDefEq.dir (hΓ : ⊢ Γ) (H : Γ ⊢ t ≡ t' : A) : SoundDir Γ t ∧ SoundDir Γ t'
```

Three changes, each with a reason.

*`Adm` → `Valuation.WF`.*  This is what makes the lemma separable, and it
is what both originals do: master's `compat_join` takes no `Fits`, his
`IsIdealValued` is directedness at *every* shape.  The recursive call
under a binder is then at `ρ.push (x₁ ⊔ x₂)`, which is WF because both
are; nothing has to be typed.  With `Adm` the same call needs the joined
slot typed at an approximant of `⟦A⟧`, which is `rawExtend_isDirected`'s
content and, for us, the `pair`-clause obstruction (§4.7).  Weakening the
hypothesis deletes the obligation.  The price: nothing inside `IsDefEq.dir`
may appeal to `SoundTy`, since `SoundTy` needs `Adm`.  §2.4 is what that
costs, and it is one premise on three constructors.

*Upper-bound conclusion.*  His `IsDirected`; `Compat` and the join follow
by `sound_dir_of_ub`.  It is also what every case naturally produces.

*Induction on typing, not on the raw term.*  The one place a typing fact
is needed is the cross pair of an appended graph (§3.2, Π/λ cases): the
two bodies live at stages `(σ∘τ).cons (a.tm[τ])` and `(σ∘τ).cons (b.tm[τ])`,
which are defeq but not equal, and `IsDefEq.stage` needs
`Δ ⊢ (σ∘τ).cons _ : A :: Γ`, hence `Γ ⊢ A : sort u`.  A raw term does not
carry that.  His quotient carries it in the morphism; master has no labels
and no stage.  So the induction is on `Γ ⊢ t ≡ t' : A` used as a typing
judgment, and every case takes `SoundDir` of the subterms from the IHs
and the binder annotation's typing from the rule.  Note this induction is
*cheap*: `symm`, `trans`, `defeqDF` are identities on the two conclusions,
and the computation rules are padded with typings of both sides, so
`beta`, `eta`, `natCase_*`, `Y_unfold`, `tr_refl` are also identities.
Only the congruence rules have content, one per term former.

Why not fold `dir` into `sound` after all?  Because `sound` needs
`Interp.inst` (β, `appDF`, `tr`), whose `→` direction merges the
valuations two subderivations return and so needs directedness of the
substituted term; and `dir` for Π would need `SoundTy` to type the joined
domain.  Inside one induction the cycle closes; as two lemmas it does not,
provided §2.4.

### 2.4 The one new constructor premise

`Interp.forallE`, `Interp.sigma` and `Interp.lam` gain

```lean
    TShape.HasType Δ (Shape.T d) TShape.type →
```

the domain shape is a type.  It is free to establish: every place that
builds one of these has `SoundTy Γ A (sort u)` (the binder rule's
annotation typing) and so `HasType d (sort u)` by `SoundTy.hasType`,
cumulated.  It is exactly what `dir` needs and must not get from `SoundTy`:
the appended graph's `hdom` field types each input at the *joined* domain
`d₁ ⊔ d₂` by `mono_r`, which asks for `HasType (d₁ ⊔ d₂) type`, and that is
`HasType.join` **at a sort** — the typed-join lemma we have — from the two
premises.  Master gets this from `HasDom.isType`, which works only because
its saturated graphs have a `⊥`-input entry; his `piGenerator` is built
over `a ∈ ⟦A⟧` and `⟦A⟧` is a type by fixedness.

It also removes `SoundTy` from `sound_forallE_ub`'s other use, the
`isType` field of `Adm.cons` — which disappears with `Adm` (§2.3).

### 2.5 `SoundJoin`

Stays as a definition, in upper-bound form, but is no longer a hypothesis
of the Π case.  It is what `tr` needs (§4.7).  Where it should be proved is
open (§5.1).

---

## 3. Key lemmas

### 3.1 `IsDefEq.stage`

```lean
theorem IsDefEq.stage (hΓ : ⊢ Γ) (H : Γ ⊢ t ≡ t' : A) :
    ∀ {Δ σ σ' ρ m}, ⊢ Δ → Ctx.SubstEq Δ σ σ' Γ →
      (Interp Δ Γ t σ ρ m → Interp Δ Γ t σ' ρ m) ∧
      (Interp Δ Γ t' σ ρ m → Interp Δ Γ t' σ' ρ m)
```

`Interp.stage` as stated in the tree — for a raw `t` — is not provable:
take `t = forallE A B` with `A` ill-typed in `Γ` but `A[σ]` typed in `Δ`;
`Interp` holds with label `A[σ]`, and `A[σ']` need not even be a term of
the right sort.  Nothing in an `Interp` derivation types its labels in
`Γ`; `hlab` types them in `Δ`.  So the lemma is indexed by a typing
derivation of `t`, and its proof is an induction on that derivation with
an inner `cases` on `Interp` per congruence rule.

Per rule, what moves:

* labels `A[σ]` in `forallE`/`sigma`/`pair`/`id`/`app`: by `IsDefEq.subst'`
  from the rule's typing of `A`, `a`, etc. and `W : SubstEq Δ σ σ' Γ`,
  giving `Δ ⊢ A[σ] ≡ A[σ'] : sort u`; the label-comparing premises
  (`hlab`, `Evaluates`' `LabelEq`, the `WF` of the shape) are transported
  by `LabelEq.trans` and by rebuilding the shape with the new label and
  showing the old one is `≈` it (`PiLabelEq`, `LE.refl` on the components);
* bodies under binders: the IH at `SubstEq Δ (σ.cons e.tm) (σ'.cons e.tm)
  (A :: Γ)`, which is `.cons W hA (Δ ⊢ e.tm : A[σ])`, the last from the
  entry's own typing converted along `hlab`;
* `natCase_succ`: the premise `Δ ⊢ M[σ] ≡ succ t : nat` moves by
  `IsDefEq.subst'` on `M`;
* `Y`, `tr`: as binders, the label term being `(Y A b)[σ]` resp. `b[σ]`,
  moved by `subst'`.

`symm`/`trans`/`defeqDF` and every padded computation rule are identities.
The lemma is used by `dir` (cross pairs) and by `sound` wherever a label
equation from a graph entry has to be turned into an equation of stages.

**Where it actually stops (2026-10-01).**  Every case of that plan goes
through *except `app`*, and the obstruction is structural, not clerical.
`Interp.app` looks the argument up at the **λ-shape's own label** `A₀`:

```lean
TEvaluates Δ g A₀ (a.subst σ) x y
```

Moving the stage means moving the query's *term* from `a[σ]` to `a[σ']`
**at the type `A₀`**.  The typing of `a` and `W` give that equation at
`A₁[σ]`, where `A₁` is `a`'s type in `Γ`; transporting it to `A₀` needs
`Δ ⊢ A₀ ≡ A₁[σ]`, and for an arbitrary λ-shape — one that came out of a
valuation slot, not out of a `lam` term — nothing says so.  Both types do
type `a[σ]` (the entry's label equation says the first, the typing the
second), so *uniqueness of types* would close it; but uniqueness is
`HasType.uniq`, which comes from `StrongSound.uniq`, which comes after
soundness, which uses `stage`.  A real cycle.

**The cycle, precisely.**  Transporting a definitional equation to
another type of the same two terms is *uniqueness of types*: from
`Δ ⊢ x ≡ y : T` and `Δ ⊢ x : T'` one gets `Δ ⊢ x ≡ y : T'` only through
`Δ ⊢ T ≡ T'`.  Uniqueness here is `StrongSound.uniq`, which rests on the
`SoundEq`-level inversions, which rest on `IsDefEq.sound`, which rests on
`IsDefEq.dir`, which uses `stage` at the graphs' cross pairs.  Four
steps, and back to the start.

It is not broken by making the induction simultaneous.  In the `app`
case the two typings of `a[σ]` are *not* subderivations: one is the
rule's premise substituted, the other comes from a graph entry's label
and is an arbitrary derivation at the stage.

What *does* break it is the `appDF` rule's own shape: there the
argument's type **is** the domain of the function's type.  With
admissibility and the subterm's `SoundTy f (Π A₀ B)` in hand,
`Interp.lam_label_ty` gives `TyEq Δ A (A₀[σ])` and the transport is one
`defeqDF` — no uniqueness.  So `stage` *at admissible stages* is a
conclusion of the soundness induction, as §5.3's `HasDom` would be.

**But that version does not serve `dir`**, which is where `stage` is
actually used: the cross pairs of `sound_lam_ub` and `graph_coherent`
live at a *later* stage `Θ`, under `Valuation.WF`, and there is no
`Adm.subst` — `Adm.cons`'s "every approximant of `A` is a type" field
quantifies over the approximants of its own stage, and a later stage has
more of them.  `dir` needs `stage` at every well-formed stage.

So the choice is between three repairs, and it is a design decision:

  (a) **Put the connection in the clause.**  `Interp.app` carries
      `Γ ⊢ a : A₀` and `TyEq Δ A (A₀[σ])`: the λ-shape's label is the
      argument's type at the stage.  Then `app` is one `defeqDF` at
      *every* stage, so `dir` is served and no typing theory is invoked.
      The cost is that `Interp` becomes a relation on *typed* terms: a
      clause mentioning `Γ` breaks `Interp.ctx` (context irrelevance,
      used by `lamDF`, `trDF`, `YDF` to move a body from `A :: Γ` to
      `A' :: Γ`), and reinstating it for defeq contexts needs the
      binders' annotations typed — i.e. the same premise on `lam`,
      `forallE`, `sigma`, `pair`.  `Interp.substTerm` would likewise
      need `θ` typed, which every call site has.
  (b) **Rework the coherence condition** so that `dir` no longer needs
      `stage` at later stages, and take the admissible-stage version as
      a conclusion of `sound`.  `Shape.Compat`'s quantification over
      later stages is what forces it.
  (c) **Quotient the labels**, as the other repo does: its `Ctx` is
      literally `Quotient RawCtx.homRel`, with typed substitutions
      *modulo defeq* as morphisms, so two definitionally equal stages are
      one morphism and stage invariance is not a theorem at all.  Its
      *syntax* is raw and extrinsic, like ours (§3.1d); what is
      quotiented is the ambient category, and the typing data its
      interpretation needs is taken as a supremum over typing
      derivations, clause by clause.

(a) is the smallest step that unblocks everything.  **Taken** (§3.1b),
and §3.1c–d say what it cost.

#### 3.1a What "the other repo's path without the quotient" costs

Both (a) and (c) were tried on paper, and the measurement is this.

**The quotient is not the obstacle; where the substitution lemma sits
is.**  (The heading this paragraph used to carry — "the intrinsic typing
is" — was wrong twice over: that development's syntax is extrinsic, and
the thing doing the work is the bundle, not the syntax.  See the end of
this section and §3.1d.)  Two repairs suggest themselves, and each dies
on a different lemma:

* **Close `Interp` under stage equality**, i.e. add the constructor

  ```lean
  | stage : Ctx.SubstEq Δ σ σ' Γ → Interp Δ Γ t σ' ρ m → Interp Δ Γ t σ ρ m
  ```

  — a function on a quotient is a function on the carrier that respects
  the equivalence, built in rather than proved.  `stage` then costs one
  constructor.  Each inversion grows a case, which is always "recurse at
  `σ'`, move the conclusion back", and `dir` survives because the
  constructor moves derivations *both* ways, so two derivations can
  always be brought to one stage.  It dies at `Interp.weak'`,
  `Interp.unweak` and `Interp.substTerm`, which pattern-match the
  stage's *shape* (`lift_l l σ'`, `θ.comp σ`): the stage case hands them
  an arbitrary `σ''` with no such shape.  `lift_l` can be inverted
  (`liftVar` is injective), `θ.comp` cannot.

* **Type the clauses** — `lam` carries `∃ u, Γ ⊢ A : .sort u`, `app`
  carries `Γ ⊢ a : A₀` and `TyEq Δ A (A₀[σ])`, and so on.  `stage`'s
  `app` case is then one `defeqDF`.  Measured: one clause (`lam`) costs
  ≈15 sites, so all twelve label-forming clauses cost ≈200, which is
  affordable.  What is not affordable is what the premises break:
  `Interp.ctx` (context irrelevance) needs the annotations typed, which
  the typing itself supplies — fine — but **`Interp.unweak` needs
  *strengthening*** of a typing, and this syntax has only `IsDefEq.weak'`.
  Strengthening is exactly the kind of lemma this development exists to
  avoid assuming.

**Why the other repo has neither problem** — and the answer is not
intrinsic typing, which an earlier draft of this paragraph claimed.  Its
terms are raw (`Syntax/Extrinsic.lean`), and the typings its clauses need
appear as `⨆ h : {u // Γ ⊢ A : sort u}, …` inside the defining equations
of `rawInterpret`, which is our clause premises by another route.  The
two real differences are:

* its interpretation is a **function**, so renaming and substitution are
  *equations* (`⟦t[θ]⟧ = ⟦t⟧ ∘ θ`) rather than two inversions of a
  relation.  `HasRenaming` is literally `HasSubstitution` specialised
  (`HasRenaming.of_substitution`), and there is no `unweak` to state
  because an equation runs both ways;
* those equations are **fields of `RawTermProperties`**, proved in the
  soundness induction, so their `app` case can consume `HasFixedness`.

So the strengthening problem is an artefact of stating substitution as a
relation-inversion *below* the induction, not of extrinsic syntax.
`Interp.unweak` is nevertheless provable, indexed by `Term.Annot`
(§3.1c); what is not is the label link, §3.1d.

#### 3.1b The plan: stage-invariant clauses, and typed inductions

*Decided.*  Extrinsic terms with a context around them and a typing
assumed wherever one is needed — no quotient, no stage constructor
(which is not the right analogue: it adds a *rule*, where what is wanted
is that each existing rule respect the equivalence).  Each clause
instead carries what makes it stage-invariant:

| clause | assumption |
|---|---|
| `app` | `∃ A₀, (Γ ⊢ a : A₀) ∧ TyEq Δ A (A₀[σ])` — the λ-label *is* the argument's type |
| `lam` | `∃ u, Γ ⊢ A : sort u` |
| `forallE`, `sigma` | `∃ u, Γ ⊢ A : sort u`, `∃ v, A :: Γ ⊢ B : sort v` |
| `pair` | `∃ u, Γ ⊢ A : sort u`, `Γ ⊢ a : A` |
| `snd` | `∃ A₁, (Γ ⊢ fst p : A₁) ∧ TyEq Δ A₀ (A₁[σ])` |
| `natCase_zero`, `natCase_succ` | `Γ ⊢ M : nat` |
| `Y` | `∃ u, Γ ⊢ A : sort u`, `Γ ⊢ Y A b : A` |
| `id`, `tr` | `∃ u, Γ ⊢ A : sort u`, `Γ ⊢ a : A`, `Γ ⊢ b : A` |

`bvar`, the atoms, `succ`, `fst`, `refl` need nothing: no `σ` in sight.
With these, every case of `stage` is the clause rebuilt at `σ'`, with
`IsDefEq.subst` on the assumption for each label and `Ctx.SubstEq.cons`
for each body — and `app`, the case that defeated every other repair, is
one `defeqDF`, because in `appDF` the argument's type *is* the domain of
the function's type.

Three lemmas then have to be re-proved **by induction on a typing**
rather than on the term, which is the same move and for the same reason:

* `Interp.ctx` — now "any *definitionally equal* context"; the
  annotations' typings are exactly what rebuilds the `Ctx.SubstEq`
  under a binder.  (Done, in the work-in-progress patch.)
* `Interp.unweak` — strengthening is not syntactically available, so the
  lemma is indexed by a typing of the term in the *small* context and
  the induction runs on that.
* `Interp.slots` (new) — "an interpretation reads only the slots its
  context has".  Needed because `Valuation.Approx` quantifies over *all*
  slots, and a merge under a binder has nothing to say about the ones
  past the end of `Γ`: `θ i` is not typed there, so it cannot be
  unweakened.  A typed term only reads in-range slots, and that is again
  an induction on the typing.

`Interp.slots` turned out to be avoidable.  What the merges need is only
that a slot *past the end of `Γ`* can be strengthened, and there every
`θ` in sight is a variable: `Subst.one a` has the argument at slot `0`
and variables after it, and lifting preserves that.  So the hypothesis
is `Subst.Good Γ' θ` — "every slot is typed in `Γ'` or is a `bvar`" —
and `Interp.unweak_slot` splits on it: typed slots go by `unweak`,
variables by hand, since both sides of `Interp.bvar` say `m ≤ ρ j`.

**Status: done.**  The clauses carry their premises, `Presheaf.lean` is
repaired throughout, and `Interp.stage` is the theorem behind
`IsDefEq.stage`.  §3.1c records what the premises are and what is left.

### 3.1c What the stage-invariant clauses cost, and the one link left

**Done, and the shape of the answer.**  The clause premises are what make
each clause stage-invariant, and they come in two kinds:

* a *typing in `Γ`* for every annotation and subject — `∃ u, Γ ⊢ A : sort
  u` at `lam`/`forallE`/`sigma`/`pair`/`Y`/`id`/`tr`, `Γ ⊢ a : A` at
  `pair`, `Γ ⊢ M : nat` at `natCase`, `Γ ⊢ Y A b : A` at `Y`;
* `Stable Δ Γ σ a A` at `app` and `snd`, which says the shape's *label*
  types the query, stably: reading the query at the stage and at any
  later stage out of `Γ` gives two terms equal **at the label**, and that
  survives any substitution of the ambient context (`Label.lean`).

`Stable` is there because the label is a term of `Δ`, and no typing in
`Γ` relates it to the argument's type without uniqueness.  It is also
what makes the premise survive a move to a *smaller* context: the stages
a smaller context admits extend to ones the larger one admits
(`Ctx.SubstEq.extend`), where a typing does not strengthen.

With those premises in place:

* **`Interp.stage` is a theorem** — structural induction on the term,
  `Term.Annot` supplying the annotations' typings, each clause's own
  premise moving its own label, and `Y` (whose premise is the tower one
  level down) running on the derivation.  `IsDefEq.stage` is that lemma
  fed `H.annot.1`, so no call site changed.  **`IsDefEq.dir` is now
  clean**: no `sorry` under it.
* **`Interp.unweak` is a theorem** — the strengthening that §3.4 called
  impossible.  Indexed by `Term.Annot` rather than by a typing, since a
  typing is exactly what does not strengthen; `Annot` is syntax-directed,
  so it decomposes without inversion, and `IsDefEq.annot` establishes it
  for every term in a derivation (the instrumented judgement carries its
  subterms' sort proofs, and both sides of every computation rule).
* **`Interp.to_substTerm` is proved for every term former**, down to one
  lemma.

**The one link.**  `to_substTerm` rebuilds a `Γ`-level clause from its
`Γ'`-level form, and all but one premise comes back from `Annot`.  The
exception is `app`'s and `snd`'s: at `Γ'` the premise is `Stable Δ Γ' σ
(a[θ]) A` and at `Γ` it is `Stable Δ Γ (θ∘σ) a A`.  These differ only in
which context the later stages come out of, and `Γ`'s are strictly more —
`Γ'` sees only the stages that factor through `θ`.  To bridge them one
needs `A` and the image of `a`'s own `Γ`-type to be the same type, i.e.
**uniqueness of types at the stage**, which this development proves *from*
soundness, which needs `inst`, which needs this lemma.

`Stable.transfers` is now a *theorem*, proved from that: the clause's own
premise at the identity stage says the label types the query in `Δ`, the
argument's typing in `Γ` pushed along `θ` and `σ` says its own type does
too, uniqueness identifies them, and the equation transports.  `Annot`
records what an `app`'s argument and a `snd`'s first projection are typed
at, which `IsDefEq.annot` gets from `appDF`'s and `sndDF`'s own premises.

So the whole assumption was once `IsDefEq.uniq`: **a term has at most
one type, up to definitional equality.**  (It is no longer assumed; the
rest of this section records why it looked unavoidable and §4.7 what
removed it.)

**And that is circular, which is the finding.**  Uniqueness is true of
this theory, and its proof is formalised here — `HasType.uniq` in
`Consequences.lean`, over a bundled structural typing judgement.  But
that proof's only external inputs are the `sort` and Π inversions, and Π
inversion is what the labelled model exists to prove.  On this root the
chain is

    uniq → Stable.transfers → to_substTerm → inst → sound → inversions → uniq

so assuming uniqueness here assumes a consequence of what is being
proved.  As scaffolding it is fine — nothing below the model depends on
it, and every other lemma is now unconditional — but it cannot stay.

### 3.1d What the original does here, and where we left it

Read against `/project/presheaf-semantics-lean`.  The object language
there is **extrinsic too** — raw `Term`s and a typing judgement
(`Syntax/Extrinsic.lean`, `Syntax/Typing.lean`), the same as ours; what
is categorical is the *ambient*, not the syntax.  (An earlier note in
this file said "intrinsically typed syntax".  That was wrong.)  Lining
the two up:

| there | here |
|---|---|
| `Ctx := Quotient RawCtx.homRel` (`Syntax/Intrinsic.lean`): a stage is a morphism, i.e. a typed substitution **modulo defeq** | a stage is a raw `Subst`; invariance under `Ctx.SubstEq` is the theorem `Interp.stage` |
| `rawInterpret` is a **function** on raw terms, each clause taking `⨆ h : {u // Γ ⊢ A : sort u}, …` over the typings it needs | `Interp` is a relation, and those typings are clause *premises*; `Term.Annot` is the bookkeeping that recovers them structurally |
| an application's query is `sourceQuery Γ a` — the **set of all typings of `a`** — and `application F X Q` looks up at `Tm.presheaf.map σ '' Q`, so the query transports as the image of a set | the query is the λ-shape's own label, plus a premise tying it to `a`'s type |
| `HasSubstitution Γ t` is a **field of `RawTermProperties`**, proved inside the main induction alongside `HasIdeality` (our `SoundDir`), `HasEquality` (our `SoundEq`) and `HasFixedness` | `Interp.substTerm`/`inst` are standalone lemmas, proved before soundness |
| `HasSubstitution.app` (`Soundness/StructuralRules.lean`) takes **`HasFixedness Γ f (Π A B)`** — ⟦f⟧ is a value of the Π-type — and `outputAtom_rawPi_fixed_support` turns it into: a non-`⊥` output responds only at a label that is a genuine point of the domain, so the two query sets agree (`rawApplication_subst_query_eq`) | nothing semantic is available, so the label had to be tied syntactically — and that is the step that needs uniqueness |
| `Unique.lean` derives `IsDefEq.type_unique` **from** `Inversion.lean` | we assume it *upstream* of inversion |

**So the hole is one divergence, and it is ours: we hoisted the
substitution lemma out of the soundness induction.**  The original never
has to recognise a shape's label syntactically, because at every use of
substitution it already knows the function's value is Π-fixed.  We have
that ingredient — `Interp.lam_label_ty` is exactly
`outputAtom_rawPi_fixed_support`, and it gives `TyEq Δ A' (A[σ])` — but
only from `SoundTy Γ f (Π A B)`, which lives in the soundness induction.

**The fix, in their shape:** give `IsDefEq.sound` a third component, a
`SoundSubst Γ t` (their `HasSubstitution`), proved in the same induction
as `SoundEq`/`SoundTy`; the `app` and `snd` cases of its proof get the
label link from `lam_label_ty`/`pair_label_ty` applied to the IH's
`SoundTy`, and the computation rules use the *subterms'* `SoundSubst`
instead of a global `Interp.inst`.  Then `IsDefEq.uniq` is not needed at
all, and uniqueness comes out downstream, where their `Unique.lean` has
it.

**That is now what is there.**  `IsDefEq.sound` proves `SoundEq`,
`SoundTy` *and* `Term.Pinned` of both sides in one induction (§3.1f), and
`Interp.to_substTerm` is the standalone lemma that consumes the last of
these.  `Term.Pinned` (`Interp.lean`) gathers the conditions
structurally:

| conjunct | what it is | the original |
|---|---|---|
| `IsTypeAt Γ A` at every binder | every approximant of the annotation, at an admissible stage, is a type | what rebuilds the extended stage's admissibility |
| `TypedAt Γ M .nat`, `TypedAt Γ (Y A b) A` | the two binder slots that are not entry inputs | `natCase`'s and `Y`'s own fixedness |
| `PinApp Γ F a`, `PinSnd Γ p` | a λ- (resp. pair-) shape approximating the subject has its label defeq to the argument's type at the stage | `HasFixedness` + `outputAtom_rawPi_fixed_support` |

Each is one half of a subterm's own `SoundTy`, which is why the induction
can discharge it; `Stable.transfers` and `IsDefEq.uniq` are deleted, and
so is the `IsDefEq.pinned` assumption.

**Getting there went through one real obstacle**, found by trying
(twice): stated at the *source* stage, as `to_substTerm` consumes them,
the conditions are unprovable, because transporting a subterm's
`SoundTy` across `θ` reads it under the valuation `to_substTerm`
**builds**, and that valuation need not be admissible.  **Admissibility
is not upward closed**: enlarging a valuation breaks its slots' typings,
typing being a lower set.  So "enlarge the reconstructed valuation until
it hosts the type-approximants `Adm` wants" does not close — each
enlargement needs its new slots typed, and their types are read at a
bigger valuation again.  That is the same ideal-versus-approximant gap as
§5.1's join-closure and §5.5's lower-closure, in a third place: there the
`Γ`-side valuation *is* `⟦θ⟧`, an ideal, one object, admissible by
construction.

What closes it is to state the conditions on the `Γ` side and carry
`Subst.Saturates` — "every θ-approximating valuation is below an
admissible one" — which is the original's `SourceAdmissible` /
`SingleSubstitution` pair, true for the same reason: the only `θ` that
arises is `one a` lifted.  §3.1e has it.

Two things came out of the attempt and stayed.  `Adm` is a **predicate on
slots** — every slot well formed, and the slot a variable reads typed at
an approximant of its type — rather than an inductive indexed by a base
context.  It says the same of every valuation the inductive admitted
(`Adm.lookup` *was* that statement), it makes enlargements and joins
expressible, and it drops a context index from every signature.  And
`Adm.unlift`, its restriction along a context lift, is what gives the
weakening lemmas back.

Two things that would *not* work, recorded so they are not retried:

* **Annotating `Term.app`** with its domain.  It would pin the label, but
  it changes the object language, and the original shows it is
  unnecessary.
* **Indexing `Interp` by a type.**  The app clause's index would be
  `B₀.inst a`, in which the domain does not occur, so the function's
  Π-type stays existential and `to_substTerm` still has to invent
  `Γ`-level data.

#### 3.1e Saturation: how the clause conditions got discharged — **closed**

The obstacle was that `Term.Pinned`'s conditions were stated on the
*source* side of the substitution, where `to_substTerm` consumes them —
"every approximant of `A[θ]` at the source stage is a type" — and nothing
can prove them there.  Proving one means transporting an approximant back
to `Γ` and reading the subterm's `SoundTy`, and `SoundTy` is only
readable at an **admissible** stage, which the transported valuation need
not be: `Adm` is not upward closed, because typing is a lower set, so
enlarging a valuation to host the type-approximants `Adm` asks for breaks
the slots that were already there.

The resolution is to state the conditions where they are *provable* and
pay for the move once:

* `IsTypeAt`, `TypedAt`, `PinApp`, `PinSnd` now quantify over stages out
  of `Γ` alone.  Each is then one half of a subterm's own `SoundTy`:
  `SoundTy.isTypeAt`, `SoundTy.typedAt`, and (for the two eliminators)
  `Interp.lam_label_ty` / `Interp.pair_label_ty` followed by
  `Stable.of_typed` — `PinApp.of_sound`, `PinSnd.of_sound`.
* What pays for it is

  ```lean
  def Subst.Saturates (Δ Γ₀ Γ Γ' : List Term) (θ σ : Subst) (ρ : Valuation) : Prop :=
    ∀ {ρ'}, Valuation.Approx Δ Γ' θ σ ρ ρ' →
      ∃ ρ'', Valuation.LE Δ ρ' ρ'' ∧ Valuation.Approx Δ Γ' θ σ ρ ρ'' ∧
        Adm Δ Γ₀ Γ (θ.comp σ) ρ''
  ```

  — every valuation approximating `θ` is below an admissible one that
  still approximates it.  `to_substTerm` carries it and applies it at
  each site where it reads a condition.

`Saturates` is the original's `SourceAdmissible`/`SingleSubstitution`
pair, and it holds for the same reason: the only `θ` that ever arises is
`one a` lifted `k` times, since `Interp.inst` is the substitution
lemma's only consumer and `to_substTerm`'s recursion lifts.  So it is
proved in two pieces, and the class never has to be named:

* **Base, `Subst.Saturates.one`** (`= Valuation.Approx.canon_one`): at
  `one a` the canonical valuation is `ρ` with the argument's approximant
  pushed on.  No join and no growth — slot `0` is already an approximant
  of `a`, so `TypedAt a A` types it where it stands, and `A` lives
  *below* the substituted variable, so its own approximant does not move.
* **Step, `Subst.Saturates.lift`**: under a binder the slot `y` stays put
  and the tail is saturated by the hypothesis.  The one obligation the
  binder adds is that the annotation have an approximant typing `y` on
  the `Γ` side; that witness is another θ-approximating valuation, so it
  is absorbed by one join and one further saturation, and *that* does not
  cascade — enlarging those slots leaves `y` alone.

Two consequences worth recording.  `IsDefEq.dir` never instantiates, so
it never needs `Saturates` and stays independent of soundness.  And the
weakening lemmas (`Term.Pinned.weak'` and friends), which the `Γ`-side
statement broke, come back through `Adm.unlift`: admissibility restricts
along a context lift, since a variable of the smaller context is one of
the bigger (`Lookup.weak'`) with the same type lifted, so `Interp.unweak`
moves that type's approximant down.

#### 3.1f `Term.Pinned` is a theorem — **closed**

With the conditions on the `Γ` side, `IsDefEq.sound`'s induction proves
them.  Its conclusion is now

```lean
SoundEq Γ t t' ∧ SoundTy Γ t A ∧ t.Pinned Γ ∧ t'.Pinned Γ
```

and `IsDefEq.pinned` is a projection; `Pinned.lean` is gone.  Both sides,
because `symm` needs the right-hand one, and both are cheap: at a
congruence rule every semantic condition is a subterm's `SoundTy` read
through the bridges above, and at a computation rule nothing is built at
all — those rules are padded with typings of both sides, so both
`Pinned`s are IHs.  The primed side goes through `SoundTy.of_eq`, exactly
as `SoundTy` itself does.

This is the architecture §3.1d describes as the original's: substitution
and its prerequisites proved in the same induction as soundness, rather
than hoisted out of it.  The only difference left is bookkeeping — there
they are fields of one `RawTermProperties`, here three conclusions of one
theorem plus the standalone `to_substTerm` that consumes them.

### 3.2 `IsDefEq.dir`, per former

**Status: complete and axiom-clean** — every case including `tr`, and
nothing under it (the axiom board in `DomainSemantics.lean`).  What follows is the original sketch,
annotated where the proof went differently.

The proof is `sound_dir_of_ub` in every case; what varies is the upper
bound.  Throughout, `hρ : Valuation.WF Δ ρ`.

*`bvar`.* `m₁, m₂ ≤ ρ i`; upper bound `ρ i`, WF by `hρ`.  His `ContextRen`
machinery does not arise: it exists to move `⟦A⟧` across the projection
for the *fixedness* half of `bvar`, which is `SoundTy`'s business.

*atoms.* the canonical shape.

*`succ`.* invert both to `succ v₁`, `succ v₂` with `Interp N v₁`, `v₂`;
IH on `N` gives `v ≥ v₁, v₂`; upper bound `succ v`.  His
`succ_isDirected`.

*`forallE`, `sigma`.* `sound_forallE_ub` as written, with the changes of
§2.3–2.4: the domain bound comes from the IH on `A` (now an upper bound
`d` rather than the join — take `d`), typed by the new premise plus
`HasType.join`-at-a-sort if one prefers the join; the graphs appended; the
cross pairs by the argument already in the tree (`Interp.subst` to
`(Θ,τ)`, `IsDefEq.stage` along the label equation, `Interp.mono_val` to
the WF slot `x₁ ⊔ x₂`, IH on `B` there, `Compat.of_common_upper`); and
`Shape.WF.join` for the merged shape's well-formedness.  No `Adm`, no
`SoundJoin`, no `Adm.subst`.  This is his `pi_isDirected` +
`GraphValid.internallyCompatible`, with `IsDefEq.stage` in place of the
quotient.

*`lam`.* identical, with no domain component to join.  His
`abstraction_isDirected`.

*`app`.* invert both: `Interp F (lam g₁)`, `Interp a x₁`, `Evaluates g₁ A
a[σ] x₁ y₁`, `m₁ ≤ y₁`; same with 2.  IH on `F` gives an approximant
`lam g ≥ lam g₁, lam g₂` (so `g₁ ≤ g`, `g₂ ≤ g` in the graph order), IH on
`a` gives `x ≥ x₁, x₂`.  `Evaluates.mono_graph'` moves each lookup to
`(g, x)`: `y₁ ≤ y₁'`, `Evaluates g A a[σ] x y₁'`, likewise `y₂'`.  The two
results of one lookup are compatible (`Evaluates.compat`, from `g`'s
coherence, which `WF (lam g)` carries) and `Evaluates.join` gives
`Evaluates g … x (y₁' ⊔ y₂')`.  Upper bound: `.app` at that.

**This sketch was wrong** (§5.5b).  Only the *term* halves of the two
labels agree on the nose; the clause's type `A` was existential, so the
two lookups were at `(A₁, a[σ])` and `(A₂, a[σ])`, and neither
`Evaluates.join` nor `Evaluates.compat` — both stated at one query —
applied across them.

**Fixed, and `dir_app` is proved.**  The λ-shape now carries its domain
label, so `A₁` and `A₂` are the two shapes' labels, and the upper bound's
own label is definitionally equal to both (`TShape.LE.lam_dom`).
`TEvaluates.retype` moves each lookup to that one query — free, because
`entry`'s label equation is stated at the *entry's* type, so the query's
type is not what the argument is typed at — and `TEvaluates.compat` then
joins the two outputs.  `Interp.app`'s lookup is `TEvaluates` over
`TShape`s rather than the level-indexed `Evaluates`, since a lookup in the
bigger graph lands at that graph's level and does not reflect back down.

*`pair`, `fst`, `snd`.* as `app`/`succ`: components from the IHs, pair
shapes joined componentwise; a projection's approximants are below a
component of a pair approximant of `p`, and the IH on `p` bounds those.

*`natCase`.* `natCase_zero` approximants are approximants of `a`; IH on
`a`.  `natCase_succ`: both push `v₁`, `v₂` with `Interp M (succ vᵢ)`; IH
on `M` gives `succ v ≥` both, `v` WF by `Interp.wf`; `mono_val` both
bodies to `ρ.push v`; IH on `b` there.  Mixed zero/succ: `Interp M zero`
and `Interp M (succ v)` are compatible by the IH on `M`, and `zero`,
`succ v` are not, so one is `⊥`; then that side's approximant is bounded
by the other's by `Interp.mono`.  (Check: `Interp M (succ ⊥)` and `Interp
M zero` — `succ ⊥` is not `⊥`, so this really is a contradiction from
the IH, as in master.)

As built, the mixed case is outright absurd (`TShape.LE.zero_succ_absurd`:
nothing is above both), and the two-`succ` case needs one thing the sketch
missed: the two derivations carry two *label terms* `t₁`, `t₂` for the
body's binder, each definitionally `M[σ]`'s predecessor, and the bodies
compare only at one stage.  `IsDefEq.succ_inj` (`Regular.lean`) supplies
`t₁ ≡ t₂`: with the constant motive `nat`, `natCase` is the predecessor,
and `natCase_succ` computes it on both sides of `succ t₁ ≡ succ t₂`.  It
is a syntactic theorem, not a consequence of soundness — `succ_regular`,
the `succ` row of `Regular.lean`, is what types its two arguments.

*`Y`.* both are `Interp b` at `ρ.push sᵢ` with `Interp (Y A b) sᵢ`;
the IH on the *inner* `Y` — this case is an inner induction on the
`Interp` derivation, since `Y` refers to itself; master's `compat_join`
does the same — gives `s ≥ s₁, s₂`, then `mono_val` and the IH on `b`.

*`id`.* label-only; the canonical shape.

*`refl`.* as `succ`.

*`tr`.* §4.7.  This is the one case with content beyond the IHs, and the
one still open: it is the only consumer of `SoundJoin` (§5.1), since two
transports are typed at two approximants of the motive and the witness
above both has to be typed at the motive above both.  Every other case is
an upper bound with no typing to preserve, which is what lets them run
under `Valuation.WF` with no admissibility anywhere.

### 3.3 `Interp.substTerm`, `Interp.inst` — **done**

Master's `LE_Interp.subst`, with the stage moving and the directedness of
the substituted terms as a hypothesis rather than a global lemma:

```lean
theorem Interp.substTerm (hΔ : ⊢ Δ) (hΓ : ⊢ Γ) (ht : Γ ⊢ t : T) (hPin : t.Pinned Γ)
    (hΓ' : ⊢ Γ') (hgood : Subst.Good Γ' θ) (Wθ : Ctx.SubstEq Γ' θ θ Γ)
    (Wσ : Ctx.SubstEq Δ σ σ Γ') (hAdm : Adm Δ Γ₀ Γ' σ ρ)
    (hSat : Subst.Saturates Δ Γ₀ Γ Γ' θ σ ρ)
    (hθ : ∀ i, Interp.Dir Δ Γ' (θ i) σ ρ) :
    Interp Δ Γ' (t.subst θ) σ ρ m ↔
      ∃ ρ', Interp Δ Γ t (θ.comp σ) ρ' m ∧ ∀ i, Interp Δ Γ' (θ i) σ ρ (ρ' i)
```

(`hPin` is §3.1d's clause conditions, `hSat` §3.1e's saturation; at
`inst`'s call sites both are discharged, the first by `IsDefEq.pinned`
and the second by `Subst.Saturates.one`.)

`←` is master's structural rebuild (`weak'` for the binder cases, since
`ρ'` gains a slot); it needs no `hθ`.  `→` is master's generalised
induction, merging the valuations two subderivations return: master uses
`compat`+`join'` on each slot, we use `hθ i` to get a common upper bound
per slot and `Valuation.LE` to move both subderivations there.  Labels:
`A.subst (θ.comp σ) = (A.subst θ).subst σ` is `subst_subst`, on the nose,
so no stage lemma is needed.  For `inst`:

```lean
theorem Interp.inst (hΔ : ⊢ Δ) (ha : SoundDir Γ a) (W : Δ ⊢ σ : Γ) (hρ : Valuation.WF Δ ρ) :
    Interp Δ Γ (b.inst a) σ ρ m ↔
      ∃ x, Interp Δ (A :: Γ) b ((Subst.one a).comp σ) (ρ.push x) m ∧ Interp Δ Γ a σ ρ x
```

`hθ` for `one a` is `ha` at `i = 0` and `Interp.bvar_iff` + `hρ` at
`i+1`; then master's `inst` proof verbatim (`ρ'` coerced to `ρ.push (ρ' 0)`
by `mono_val`).

**Both are proved** (`Interp.lean`) **except for one link**, §3.1d: the
analytic direction's `app` and `snd` cases cannot rebuild the clause's
label premise in the smaller context, and the stand-in is `IsDefEq.uniq`.
The plan above is what the proof does, with three refinements.  `→` is an induction on the **term**, not
on the derivation: `(bvar i)[θ]` is `θ i`, which has no head to invert,
and that case is where the valuation is built (slot `i` holds the
approximant, every other slot `⊥`).  The merge is factored out —
`Valuation.Approx` (every slot approximates its `θ i`), `Approx.join` /
`Approx.foldr`, and `Interp.body_merge` / `list_merge` for the clauses
with one subderivation per graph entry; under a binder the body's
valuation comes back with the binder's own slot in front, which
`Interp.weak_iff` strips off the tail.  And `Y` needs its own induction,
on the tower, since its clause is recursive in its own term.  `SoundDir Γ a` is available at every use site from
`IsDefEq.dir` on the rule's typing of `a`.

### 3.4 `Interp.unweak` — **done**

Master's `weak'_iff.1`: `generalize` the renamed term and case on the
original.  Nothing presheaf-specific: the stage is `σ'.lift_l l` on one
side and `σ'` on the other, and labels are `A[σ'.lift_l l] =
(A.lift' l)[σ']` by `subst_lift'`.  Used by η (§4.5) and both `Y` rules.

With the typed clauses this stopped being that, and §3.1a called it
impossible: the premises are typings, and typings do not strengthen.  The
way through is to index the induction by `Term.Annot` rather than by a
typing — the annotations' typings are what the clauses need, `Annot` is
syntax-directed so it decomposes without inversion, and `IsDefEq.annot`
supplies it for every term in a derivation.  The `app` and `snd` label
premises come back by `Stable.unweak`, which is where `Stable`'s
quantification over later stages earns its keep: the stages a smaller
context admits extend to the larger one's (`Ctx.SubstEq.extend`).

### 3.5 `Adm.subst`

Needed only if something moves an *admissible* valuation to a later
stage.  With `dir` taking `Valuation.WF`, the cross-pair argument moves
only a WF valuation, and `Valuation.WF` is preserved by `TShape.WF.subst`
slotwise.  `sound` never moves stage.  So `Adm.subst` can go, together
with its sorry.  (If it is ever wanted, it is an induction on `Adm` with
`Interp.subst` for the interpretation fields and `TShape.HasType.subst`
for the typing field, plus `Interp.subst` again inside the saturation
field — routine.)

---

## 4. Selected cases of `IsDefEq.sound`

With `dir` separate, `IsDefEq.sound` concludes `SoundEq Γ t t' ∧ SoundTy Γ
t A` — master's two conclusions, his `equal` and `fixed`.  His `left`,
`right`, `type` are `RawTermProperties`, i.e. `ideal`+`subst`+`ready`; the
first is `dir`, the second is `Interp.substTerm`, the third dissolves
(§4.5).  **His `subst` is a field of that bundle and ours is not**, which
is the divergence §3.1d traces: the fix is to make `SoundSubst` a third
conclusion here.  Each case below says what it needs from the IHs, from `dir`, and
from the lemmas of §3, and where the originals' moves land.

Conventions in the case proofs: the stage is `(Δ, σ)` with `hΔ`, `W`, and
`hAdm : Adm Δ Γ₀ Γ σ ρ`; the body stage under a binder with entry `e` is
`σ.cons e.tm`; `W' := W.cons hA (hty.defeqDF hwe)` where `hty` is the
entry's label equation and `hwe` its typing; `hAdm' := hAdm.cons (isType)
hA₀ hwx hdom` where `hA₀ : Interp A d` and `hdom : HasType e.inp d`.

### 4.1 `bvar`

`SoundEq` is reflexivity.  `SoundTy`: induction on `Adm` (master's
`SoundTy.bvar`).  `Adm.cons`'s third and fifth fields are literally the
witness: for slot `0`, `m ≤ ρ 0 = x`, `Interp A a`, `HasType x a` — but
`Interp A` is at stage `σ.tail` and context `Γ`, and the conclusion wants
`A.lift` at `σ` and `A :: Γ`: `Interp.weak'` with `l = skip refl` moves
it, and `Interp.ctx` fixes the context.  For slot `i+1`, the IH on the
tail after `Interp.bvar_iff`.  His version needs `ContextRen` (renaming
of every context type) for exactly this weakening; ours is `weak'`, once.

### 4.2 `forallEDF`

Premises: `Γ ⊢ A ≡ A' : sort u`, `A::Γ ⊢ B ≡ B' : sort v`, `A'::Γ ⊢ B ≡ B'
: sort v`.  IHs give `SoundEq`/`SoundTy` for `A`, `A'` at `Γ`, for `B`,
`B'` at `A::Γ` and at `A'::Γ`.

*`SoundEq`* — `sound_forallE_eq`, done.  One direction, applied twice on
mirrored data; the second codomain premise (over `A'`) is what the
backward direction runs on.  Content: the two Π-shapes differ only in the
label, `PiLabelEq` from the premises substituted, `LE.trans`.  Bodies move
context by `Interp.ctx`.  His `HasEquality.forallE` needs
`section_contextConversion` + `pB.right.ren` for the context change; ours
is free.

*`SoundTy`* — `sound_forallE_ty`, done.  Witness: the shape at hand,
typed at `sort v` by `HasTypeS.forallE ⟨domain, codomain⟩`, both halves
from `SoundTy.hasType` (i.e. `mono_r` up to the sort then `mono_l` down).
The codomain half runs the IH on `B` at `W'`, `hAdm'`.  Master instead
saturates to a *bigger* Π-shape (`sound_forallE`: domain `a' ≥ d` typed,
graph re-applied); that route needs no `mono_l` and is worth remembering
if lower-closure is ever given up (§5.3).  His `HasFixedness.forallE` is
`rawPi_type_fixed` (unconditional at `type`) and `rawPi_prop_fixed` at
`prop`; our clause inspects the codomain at both sorts, §4.5e of the plan.

*`SoundDir`* — no longer a conclusion here; `IsDefEq.dir` at the rule's
own derivation.

### 4.3 `lamDF`

Premises: `Γ ⊢ A ≡ A' : sort u`, `A::Γ ⊢ B : sort v`, `A::Γ ⊢ b ≡ b' : B`,
`A'::Γ ⊢ b ≡ b' : B`, `Γ ⊢ Π A B : sort v`.

*`SoundEq`* — as `forallEDF` with no codomain label: the λ-shape carries
no label at all, only its entries do, and those are unchanged.  Invert
`lam hA hwf hlab hdom hbody hw hle`; rebuild with `(ihA).1 hA`, `hlab`
converted along `A[σ] ≡ A'[σ]`, `hdom` unchanged, bodies by the IH on `b`
at `W'`, `hAdm'` then `Interp.ctx`, and the same `hle`.  His
`HasEquality.lam`.

*`SoundTy`* — witness the shape at hand, `lam g`, typed at an approximant
of `⟦Π A B⟧`.  Which approximant?  Build it: `forallE (A[σ]) (B[σ.lift])
d f` where `d` is `hA`'s domain and `f` is the graph with the *same
entries as `g`* but each output replaced by the `SoundTy B` witness's
*type*: for `e ∈ g`, the IH on `b` at `W'`, `hAdm'` gives `e.out ≤ y'`,
`Interp b y'`, `Interp B c`, `HasType y' c`; put `⟨e.ty, e.tm, e.inp,
c⟩` into `f`.  Then:

* `Interp (Π A B) (forallE … d f)`: `hA`, `WF` (labels from the premise
  typings substituted; `f`'s entries WF since `c` is `Interp.wf`;
  coherence of `f` — **this needs `dir` on `B`** at cross pairs of `f`
  with itself, exactly the argument of §3.2 with `f` in place of the
  appended graph, so `IsDefEq.dir` on `A::Γ ⊢ B : sort v`), `hlab`
  (same), `hdom` (same), bodies `Interp B (σ.cons e.tm) (ρ.push e.inp) c`
  (the IH's `Interp B c`), the new premise `HasType d type` from
  `SoundTy A`.
* `HasType (lam g) (forallE … d f)`: the λ clause, `∀ e ∈ g, ∃ c, WF c ∧
  Evaluates f e.ty e.tm e.inp c ∧ HasType e.out c`: `c` is `f`'s entry at
  `e`, `Evaluates.entry_self`, and `HasType e.out c` from `HasType y' c`
  by `mono_l` (`e.out ≤ y'`).  Plus `HasPi d f type` from `HasType d type`
  and each `c` a type (`SoundTy B` at a sort, `hasType`, cumul).

So `SoundTy` for λ costs one `dir` call (coherence of the codomain graph)
and nothing else new.  His `HasFixedness.lam` is `normalizedAbstraction_fixed`
(103 lines of re-abstraction); master's `sound_lam` needs `join'` at an
arbitrary type to merge two codomain graphs (`Sound.lean:701-704`), which
we avoid by building `f` from `g` directly rather than from a saturated
Π-approximant.  The premise `Γ ⊢ Π A B : sort v` of the rule is what makes
`SoundTy (Π A B) (sort v)` available for the *type* side of the
conclusion, i.e. master's `regular`/his `type` field, if it is wanted;
the case itself does not need it.

### 4.4 `appDF`

Premises: `Γ ⊢ A : sort u`, `A::Γ ⊢ B : sort v`, `Γ ⊢ f ≡ f' : Π A B`,
`Γ ⊢ a ≡ a' : A`, `Γ ⊢ B[a] ≡ B[a'] : sort v`.

*`SoundEq`* — invert `app hF hx hev hw hle`; rebuild with `(ihf).1 hF`,
`(iha).1 hx`, and `hev` **moved along `a[σ] ≡ a'[σ]`**: `Evaluates g A
a[σ] x y → Evaluates g A a'[σ] x y` is `LabelEq.trans` on the `entry`
rule's premise, by induction on `Evaluates` (four cases, trivial except
`entry`).  `Δ ⊢ a[σ] ≡ a'[σ] : A[σ]` from `IsDefEq.subst`; the `entry`
premise compares at type `e.ty` with `∃ u, Δ ⊢ A ≡ e.ty`, so convert.  His
`HasEquality.app` needs `sourceQuery a = sourceQuery a'` (`SourceQuery.lean`,
via `PiReady` and fixedness); ours is one `LabelEq.trans`.

*`SoundTy`* at `B[a]` — master's `sound_app`, step for step, with
`Interp.inst` where master has `forallE_inv`:

1. `m ≤ y`, `Evaluates g A a[σ] x y`, `Interp f (lam g)`, `Interp a x`.
2. `SoundTy f (Π A B)` (IH): `lam g ≤ m'`, `Interp f m'`, `Interp (Π A B)
   p`, `HasType m' p`.  Invert `p` to `forallE (A[σ]) (B[σ.lift]) d f₀`
   (or `⊥`, then `m' = ⊥`, `y = ⊥`, `InterpTyped.bot`), and `HasType m' p`
   to `m' = lam g'` with the λ clause on `g'`, and `g ≤ g'`.
3. `SoundTy a A` (IH): `x ≤ x'`, `Interp a x'`, `Interp A d'`, `HasType x'
   d'`.  Move to `d`: `d`, `d'` are both approximants of `A`, so `dir A`
   bounds them by `d'' ≥ d, d'` with `Interp A d''`; `HasType x' d''` by
   `mono_r` (`d''` a type: new premise on `p`, or `SoundTy A`).  Now `x'`
   is typed at a domain approximant, which is what the λ clause of `g'`
   needs.  (Master's `HasDom.iff` finds a typed `bx' ≤ x` inside the
   graph; we go up instead of down, which is why the λ clause is stated
   with `∃ c` over the *code* `f₀` and not over `g'`.)
4. Lookup: `Evaluates g A a[σ] x y`, `g ≤ g'`, `x ≤ x'` give `Evaluates
   g' A a[σ] x' y'` with `y ≤ y'` (`mono_graph'`, `mono_input`).  The λ
   clause at the entries this lookup uses gives codes `c_e` with
   `Evaluates f₀ e.ty e.tm e.inp c_e`, `HasType e.out c_e`; `y'` is a join
   of such outputs (`joins_iff`), so `HasType y' c` for `c := ⊔ c_e` by
   `mono_r` on each and `HasType.join` at `type` (the `c_e` are types:
   `HasPi`), and `Evaluates f₀ A a[σ] x' c` by `Evaluates.join` +
   `mono_input`.  This is master's `app_mono_l`/`app_mono_r` chain with the
   relational lookup.
5. Type it: `Interp (B[a]) c` is `Interp.inst.2 ⟨x', Interp B ((one
   a).comp σ) (ρ.push x') c, Interp a x'⟩`, and `Interp B` there is `hbody`
   of `p` at the entry `(A[σ], a[σ])`… except `p`'s graph `f₀` has entries
   at *its own* labels, defeq to `a[σ]` only through `Evaluates`' `entry`
   rule; the stage `(one a).comp σ = σ.cons a[σ]` differs from the entry's
   `σ.cons e.tm` by that label equation — `IsDefEq.stage` on `A::Γ ⊢ B :
   sort v`.  And `c` is a join of several entries' outputs at inputs
   `e.inp ≤ x'`: `mono_val` each to `ρ.push x'`, `dir B` to bound the
   join — the same move as the cross pairs.
6. Witness: `⟨y', c, m ≤ y', .app hF' hx' hev', Interp (B[a]) c, HasType
   y' c⟩`.

Master's `H2` (saturation of `B[a]`, the IH `ihResult`) is not needed on
this route: the type `c` is a type already.  His `HasFixedness.app` is
`HasSubstitution.instantiate` (six hypotheses) + `application_piOperator_fixed`.

The case is long but every piece is in the tree except `Interp.inst`
(§3.3) and `IsDefEq.stage` (§3.1).  It is the case that determines the
shape of the λ typing clause: step 3 is where `∃ c` over the code (not a
dominating graph) pays.

### 4.5 `beta` and `eta`

Both are padded: the rule carries typings of both sides, so `SoundTy` of
each side is an IH and only `SoundEq` has content.  His `of_typings` is
exactly this observation.

*`beta`*: `app (lam A e) e' ≡ e.inst e'`.

`→`: invert `app`, then `lam hA hwf hlab hdom hbody _ hle`: `lam g ≤ lam
g'` (so `g ≤ g'`), `Interp e' x`, `Evaluates g' A₀ e'[σ] x y`, `m ≤ y`.
Goal `Interp (e.inst e') σ ρ m`, by `Interp.inst.2 ⟨x', body, Interp e'
x'⟩`.  The lookup `y` is a join of outputs of entries `(t_j, x_j, y_j)` of
`g'` with `t_j ≡ e'[σ]` and `x_j ≤ x`; `hbody` gives `Interp e (σ.cons
t_j) (ρ.push x_j) y_j`; `IsDefEq.stage` (on `A::Γ ⊢ e : B`, at
`SubstEq Δ (σ.cons t_j) (σ.cons e'[σ]) (A::Γ)` from the label equation)
moves each to the stage `σ.cons e'[σ] = (one e').comp σ`; `mono_val` to
`ρ.push x`; `dir e` bounds the `y_j` by some `y' ≥ ⊔ y_j ≥ y ≥ m`, and
`Interp.mono` finishes.  Master does the same with `h6 bx' bx_ht` at the
`HasDom` witness; his `rawInterpret_beta` needs `HasFixedness a A` because
the abstraction normalises its argument.  We need no typing of `x` at all
— the body is evaluated at `x_j`, the entry's own input.

`←`: `Interp.inst.1` gives `x` with `Interp e ((one e').comp σ) (ρ.push x)
m` and `Interp e' x`.  Build the λ: a one-entry graph `[(A[σ], e'[σ], x₀,
m)]` with `x₀` a *typed* shape — `SoundTy e' A` gives `x ≤ x₀`, `Interp e'
x₀`, `HasType x₀ d` with `Interp A d` — and body `Interp e (σ.cons e'[σ])
(ρ.push x₀) m` by `mono_val`.  Then `.app` of that λ at `x₀` looks up
`m` by `entry_self`.  `WF` of the singleton λ: `m ≠ ⊥` (else trivial),
labels typed (`e'` typed, substituted), self-coherence at later stages
from `WF.coherent` of `m[τ]`.  Master's `WShapeFun.single`.

*`eta`*: `lam A (app e.lift (bvar 0)) ≡ e : Π A B`, premises `Γ ⊢ e : Π A
B` and the expansion typed.

`→` (expansion to `e`): invert `lam`: `m ≤ lam g`, and for each `(t, x, y)
∈ g`, `Interp (app e.lift (bvar 0)) (σ.cons t) (ρ.push x) y`; invert
`app`: `Interp e.lift … (lam g_t)`, `Interp (bvar 0) … x_t` with `x_t ≤
x`, `Evaluates g_t A_t t x_t y` (the argument `(bvar 0)[σ.cons t] = t`).
`Interp.unweak` gives `Interp e σ ρ (lam g_t)`.  `dir e` bounds all the
`lam g_t` by one approximant `lam G` of `e` (`g_t ≤ G` each).  Now `lam g
≤ lam G` is needed, and **it is false in the single-entry order**: `y` is
a join of several outputs of `g_t`, and no single entry of `G` need
dominate it.  With the lookup-coverage order (§5.2) it holds:
`Evaluates G A_t t x y'` with `y ≤ y'` by `mono_graph'` (from `Evaluates
g_t … x_t y`, `g_t ≤ G`, `x_t ≤ x`).  Then `m ≤ lam g ≤ lam G` and
`Interp.mono`.

This is master's `key`/`main` (`Sound.lean:2283-2316`), whose per-point
witnesses `single x y ≤ f'` hold there because `f'` is saturated; and it
is his `eta_formation`, where `⟦e⟧ = abstraction (arrowAction ⟦e⟧)` is an
equation of *ideals*, and an ideal is closed under every graph valid for
its action.  A single non-saturated shape is closed under neither, unless
the order says so.  Hence §5.2.

`←` (`e` to the expansion): `Interp e σ ρ m`; need `m ≤ lam g` for a `g`
satisfying the `lam` premises with body `app e.lift (bvar 0)`.  `SoundTy
e (Π A B)`: `m ≤ m'`, `Interp e m'`, `Interp (Π A B) p`, `HasType m' p`;
so `p = forallE (A[σ]) (B[σ.lift]) d f₀` and `m' = lam g'` with the λ
clause (or `⊥`).  Take `g := g'`.  Premises: `Interp A d` ✓ (from `p`);
`WF (lam g')` ✓ (`Interp.wf`); `hlab`: `Δ ⊢ e.ty ≡ A[σ]` for `e ∈ g'` —
from the λ clause: `Evaluates f₀ e.ty e.tm e.inp c` with `HasType e.out c`
and `e.out ≠ ⊥` (non-degeneracy) forces the `entry` rule, whose `LabelEq`
with `f₀`'s `hlab` gives it ✓; body: `Interp (app e.lift (bvar 0)) (σ.cons
e.tm) (ρ.push e.inp) e.out` by `.app (weak' hm') (.bvar' …) (entry_self)`
✓; `hle : m ≤ lam g'` ✓; **`hdom : HasType e.inp d` ✗** — nothing types
the inputs of an arbitrary approximant of `e`.

This is the point where the two originals differ from us and from each
other, and it decides the λ typing clause:

* Master: `HasDom f a` is a premise of `LE_Interp.lam` *and* a conjunct of
  the λ typing clause (`HasTypeLam`), so `ty_forallE_inv` on `HasType m'
  p` hands back `HasDom g' d`, and η ← rebuilds with it (`c1.2.1`,
  `Sound.lean:2323`).  Master can afford `HasDom` in the typing clause
  because its `HasType` is not lower-closed.
* His: the body action is evaluated at `rawExtend ⟦A⟧ x`, and
  `application_piOperator_fixed` says a Π-fixed function's lookup at `x`
  equals its lookup at `rawExtend ⟦A⟧ x`.  So an entry at an untyped
  input carries no information beyond the typed part below it, and the
  η-expansion's graph is valid without any typedness of inputs.
* Ours: `HasType` is lower-closed, so `HasDom` cannot be a conjunct of
  the λ clause (§4.5e' of the plan: a smaller graph has weaker lookups),
  and the `Interp.lam` premise `hdom` demands typed inputs outright.

Resolution (§5.3): keep the `Interp.lam` premise but let η ← *shrink the
inputs*.  The order is contravariant in inputs, so replacing `e.inp` by a
smaller `x₀` makes the shape *bigger*: `lam {(t, x₀, y)} ≥ lam {(t, x,
y)}`.  If for every entry of `g'` there is a typed `x₀ ≤ e.inp` with
`Evaluates g' … x₀ e.out`, then `g₀ := {(e.ty, e.tm, x₀, e.out)}` has
`lam g' ≤ lam g₀`, typed inputs, and bodies `.app (weak' hm') .bvar'
(that Evaluates)` — and `m ≤ lam g' ≤ lam g₀` closes the case.  The
required fact is `HasDom` in the *lookup* form of §4.5e', for the typed
approximant `g'` of `e`.  It is not a property of shapes (that is what was
removed) but of **approximants of Π-typed terms**, i.e. it belongs in
`SoundTy` for terms of Π type — his `application_piOperator_fixed`,
elementary.  Two ways to have it:

  (a) strengthen `InterpTyped` for Π types: the typed witness `m'` of a
      term of type `Π A B` is `lam g'` with `HasDom g' d` (lookup form).
      Then `SoundTy` for `lamDF` must produce it — from `hdom` of the
      `Interp.lam` premise, immediately (`x₀ := e.inp`, `entry_self`) —
      and `appDF`, `beta` ←, `eta` ← must preserve it;
  (b) prove it as a lemma about `⟦e⟧` for `Γ ⊢ e : Π A B`, by induction
      on typing like `dir`: "every approximant `lam g` of `e` has, at
      every entry, a typed input below it at which the lookup already
      gives the output".  The `lam` case is `hdom`; `app` and `bvar` are
      where it has content — for `bvar` it comes from `Adm`, so this
      lemma needs `Adm`, not just `WF`, and so is part of `sound`.

(a) is master's `HasDom` moved from the shape level to the semantic level,
which is precisely the "his hypothesis, our construction" pattern, and it
keeps `IsDefEq.sound` as one induction.  Recommended.

#### 4.5f Typed generators: tried, and why it is not the way out

With `Term.Pinned` discharged (§3.1f), η and `fst_snd` are the only
`sorry`s, and η ← is the one obstruction: `Interp.lam`'s `hdom` demands
*typed* entry inputs, and nothing types the inputs of an arbitrary
approximant of `e`.  §5.3 names two ways out; this section rules out a
third that looks cheaper, so it is not tried again.

**The idea.**  `HasType.lam` certifies a graph `g` by a generator `g₀`
(§5.5).  Lower closure forbids `HasDom` on `g` — `mono_l` shrinks `g` to
any graph it covers, whose inputs are arbitrary — but the generator is
existential and *fixed* under shrinking, so `HasDom` can be put on `g₀`:

```lean
(∀ e ∈ g₀, HasType Δ e.1.inp.T d.T) →
```

**It costs nothing.**  Implemented and built green: `mono_r` moves the
inputs along `forallE_decomp`'s `d ≤ d'` (the Π order is *covariant* in
the domain) by `mono_r` on the inputs; `lift_subject`, `lower_subject`
and `subst` carry it entrywise; `join` concatenates, both sides being
typed at the same `d` because the clause pins the Π (`join_gen_inp`,
three lines after `join_gen_ty`); and the one producer, `lam_pi_code`,
has it for free, since there the generator **is** the λ's own graph and
the typing is the `Interp.lam` clause's own `hdom`.

**And it does not help.**  η ← needs, for each entry `q` of the
approximant's graph `g`, a typed `x₀ ≤ q.inp` at which the lookup *in
`g`* already gives `q.out` — then `g'' := {(q.ty, q.tm, x₀, q.out)}` has
typed inputs, bodies by the `app` clause, and covers `g`.  The typed
generator gives the right `x₀` (the join of the generator entries that
fire at `q.inp`, typed by `HasType.join`), but it gives the lookup in
`g₀`, and `g₀` only *covers* `g` — the converse coverage is what would
transfer it.  Demanding mutual coverage forces `g₀ = g` (take the graph
as its own generator, `TEvaluates.refl`), and then the typed-input
premise is `HasDom` on the graph again, which `mono_l` breaks.

So the obstruction is stable: **under lower closure, typing cannot
deliver a typed input for an arbitrary λ-approximant.**  The remaining
routes are the two §5.3 already names — master's (give up lower closure,
`HasDom` in the clause) and intgrah's (a truncation `rawExtend ⟦A⟧ x` on
shapes, with the lookup invariant that makes an untyped input carry no
more than its typed part) — plus the option of removing η (and
`fst_snd`) from `IsDefEq`, since soundness is an induction over the rules
and cannot simply skip one.  The experiment is reverted; none of it is in
the tree.

#### 4.5g What the original actually does at η — read off the source

Read against `/project/presheaf-semantics-lean`, after §4.5f ruled out
the cheap route.  **The original has no typed-input condition at all**,
and the reason is one line of its λ clause:

```lean
-- Interpretation/Binder.lean
noncomputable def normalizedSectionValue (hA) (C B) (σ ρ label) (I : RawValue Γ₁) :=
  sectionValue hA B σ ρ label (D.rawExtend (C.app _ σ.op ρ) I)
```

`⟦λA.b⟧` is `abstraction (normalizedBody …)` (`Interpretation.lean`,
`Interpretation/Abstraction.lean`), so **the body is read at the input
*normalised at the domain*, `rawExtend ⟦A⟧ I`**, never at `I`.  An entry
at an arbitrary input therefore carries exactly the value at its
normalised part, and nothing has to produce a typed input.

Our `Interp.lam` does the opposite: it keeps the raw input and *demands*
`hdom : HasType Δ e.inp.T d`.  That premise is what makes the extended
stage admissible — and it is the η blocker.  **It is a mistranslation of
`normalizedBodyAction`**: the original normalises where we require.

Three further things the source settles:

* **Their typing is not ours.**  `HasFixedness Γ t A` is
  `rawExtend ⟦A⟧ ⟦t⟧ = ⟦t⟧` (`Soundness/Judgment.lean`): the *value* is
  closed under the type's decoder.  There is no per-point typing
  predicate, so the question §5.3 asks — lower-closed `HasType` or
  `HasDom` — does not arise there.  Our lower-closed `HasType` is a
  strengthening of master's per-point condition and is **not** in
  tension with η.  What it does not give is decode-closure, and that is
  what η consumes.
* **η, in their proof** (`Soundness/EliminationRules.lean`,
  `HasEquality.eta_formation`): the expansion's body value at an
  arbitrary argument `X` is, by the λ clause, the application of `⟦e⟧`
  at `Y = decode ⟦A⟧ X`; `HasFixedness` of `e` at `Π A B` makes `⟦e⟧` a
  fixed point of the Π-retraction, and
  `DependentOperator.application_fixed` then rewrites the application at
  `Y` back to the application at `X`.  So `abstraction (arrowAction ⟦e⟧)
  = ⟦e⟧`.  Both ingredients are used: the clause's normalisation and the
  value's fixedness.
* **The decoder is their big construction** — `Domain/Decoder/*`, ~1.5k
  lines, built as a fixed point over stages (`PiStages`,
  `PiFixedPoint`, `FunctionRetraction`), because *their* codes are
  domain elements.  Ours are finite shapes, so the analogue
  `decode : TShape → TShape → TShape` should be structural recursion on
  the code, which is much cheaper.

**Their typing is a projection, and that is the device we lack.**  There
is no `HasType` there because `x : a` is `p_a x = x`: each code names an
idempotent, **deflationary** operator on values (`natIdeal_le : natIdeal
X ≤ X` with `natIdeal_idempotent`; `universeIdeal r X` is `X` filtered by
`IsCode`; `decode (pi label A B) = piOperator A B`, the arrow retraction
`F ↦ λX. Q (F (P X))`).  For the base codes the projection is a *filter*
by a downward-closed condition on points — which is our lower-closed
`HasType`, so downward closure and η are not in tension.  At Π it does
more: it **renormalises**, replacing an entry's output by the value at
the projected input.

**Where the content sits.**  Deflationarity is the part that matters
here.  `p z ≤ z`, and an ideal is downward closed, so `p z` is
automatically a *member*: their "every member is below a fixed one"
silently means "below a fixed **member**".  Our `Interp` is downward
closed too, so the same reading is available — and at approximant level
the statement needs no projection at all:

```lean
SoundDom Γ e :  -- their `HasFixedness`, read through ideal = approximant set
  at every admissible stage, every λ-shape approximant of `e` is `≤` an
  approximant of `e` all of whose entry inputs are typed at the domain
```

An entry at an untyped input carries the value at its typed part, which
is exactly why dropping to the typed-input approximant loses nothing.

η ← is then three lines of bookkeeping: take that approximant `z ⊒ m`,
use **its** graph for the η-expansion — inputs typed, so `Interp.lam`'s
`hdom` holds; bodies are `z`'s own lookups by `TEvaluates.refl`, and `z`
*is* an approximant, so the `app` clause applies; and `m ≤ z` covers the
original.

**Taking the downward closure as the Π clause of `HasType`** (the
obvious thing to try) is fine as a *definition* — it stays downward
closed, so `mono_l` survives — but it is not the content: η needs the
witness to be an approximant, and an existential over shapes has no link
to `Interp`.  Definition and content are separate here.

**What is needed, then:**

1. `Shape.Dom Δ d x` — *hereditarily* typed: `x` is typed at the code
   `d`, and where `d` is a Π or Σ code, every entry input of `x` is again
   `Dom` at `d`'s domain.  Structural recursion on the code; no joins,
   since nothing is renormalised.
2. `SoundDom` as a fourth conclusion of `IsDefEq.sound`, beside
   `SoundEq`, `SoundTy` and `Term.Pinned`.  The `lam` case is free (`z :=
   m`, its inputs typed by `hdom`); the computation rules come from the
   padding IHs, as `Pinned`'s did.
3. `Interp.lam`'s `hdom` and `Adm`'s slot condition ask for `Dom` rather
   than `HasType` — otherwise the `bvar` case of (2) has nothing to say
   about a slot, since a slot is where an arbitrary approximant enters.
   Most producers just carry the premise; the one real obligation is
   `beta` ←, which picks its input from `SoundTy e' A` and will pick it
   from `SoundDom` instead.

Step 3 is the only part that touches existing proofs, and it is a
premise change rather than a reinterpretation of the clause.

### 4.6 `proofIrrel`, `unit_eta`, `star`

Done or routine: `sound_of_bot`, `sound_of_bot_at`, `Interp.eq_bot_of_prop`
(`HasType.proofIrrel` at a common level).  His `rawInterpret_proofIrrel`
from strictness on prop codes; same content.

### 4.7 `trDF`, `tr_refl`, and where Σ bites

The constructor is master's: `m ≤ m'`, `Interp X m'`, `Interp a v`,
`Interp b v`, `Interp A vA`, `HasType v vA`, `Interp C (σ.cons b[σ])
(ρ.push v) cb`, `HasType m' cb`, `r = true → Interp H (refl v)`.

*`SoundEq` (`trDF`)*: rebuild, moving `C` to `C'` by the IH on `C` at
`W.cons hA (b[σ] typed)`, `hAdm.cons … hvA`, and `Interp.ctx`; the type
`C.inst b` to `C'.inst b'` is `SoundEq.inst` (from `Interp.inst` both
ways and the IHs) — master `Sound.lean:2701`.  `SoundTy` at `C.inst b`:
`⟨m', cb, le, .tr …, Interp.inst.2 ⟨v, hC, hvb⟩, hty⟩` — the constructor
carries its own typing, master `:2721-2727`.  Both need only `Interp.inst`.

*`tr_refl`*: `→` is `hx.mono le`; `←` rebuilds from `Interp.inst.1` on
the motive and re-saturates `v` via `SoundTy a`; master `:2733-2745`.

*`dir` for `tr`* is where the arbitrary-type join lives.  Two
approximants: `m₁ ≤ m₁'` typed at `cb₁`, `m₂ ≤ m₂'` typed at `cb₂`, with
`m₁', m₂'` approximants of `X` and `cb₁, cb₂` approximants of `C` at
`ρ.push v₁`, `ρ.push v₂`.  The IHs give upper bounds `m'' ≥ m₁', m₂'`
(of `X`), `v ≥ v₁, v₂`, `cb ≥ cb₁, cb₂` (of `C` at `ρ.push v`); `HasType
m'' cb` is needed, and `mono_r` gives `HasType m₁' cb`, `HasType m₂' cb`
(`cb` a type by `SoundTy C` — **which `dir` does not have**; so the `tr`
constructor should carry `HasType cb type` as the binder rules carry
`HasType d type`, §2.4).  What is left is: two compatible shapes typed at
`cb`, find a typed shape above both — `SoundJoin` for `C.inst b`, in
upper-bound form.  Master: `TShape.HasType.join'` after retyping both up
to the joined type (`compat_join`, `Sound.lean:589-593`).  His: `⟦tr⟧ =
rawExtend ⟦C[b/]⟧ ⟦x⟧`, directed by `rawExtend_isDirected`, free.

This is the only consumer of join-closure of a type's extension once the
Π case takes `Valuation.WF`.  Its Σ instance is the `pair`-dominator
obstruction (`HasType.lean`, removal note; `SoundJoin`'s doc comment).

#### 4.7c The proof-irrelevant transport: what the clause must carry

**The case the redesign is for.**  All of the above is about `r = true`,
where the proof is informative.  At `r = false` the identity type is a
**Prop**, so every proof has shape `⊥` (`HasType.proofIrrel`) and the
`r = true → Interp H (refl v)` premise says nothing.  What then licenses
the transport's value?

The other repo answers: nothing about the proof ever does.  There the
identity type is proof-irrelevant throughout, the transport is a
**coercion**

```
⟦tr A a b C x h⟧ = rawExtend ⟦C[b/]⟧ ⟦x⟧
```

(`rawInterpret_transport_value`), and its computation rule is not
`tr_refl` but **K**:

```
Γ ⊢ A : sort u    Γ ⊢ a ≡ b : A    A :: Γ ⊢ C : sort v
Γ ⊢ x : C[a/]     Γ ⊢ h : id A a b
─────────────────────────────────────────── tr_K
Γ ⊢ tr A a b C x h ≡ x : C[b/]
```

— the transport computes as soon as the *endpoints* are definitionally
equal, whatever the proof is.  (In our syntax `tr_K` at `r = false` is
derivable: `proofIrrel` gives `h ≡ refl a` once `a ≡ b` makes
`refl a : id false A a b` typecheck, and then `tr_refl` fires.)

So the value is licensed by a **judgment about the endpoints**, and the
`tr` clause has to carry it.  `Interp.tr` now does:

```lean
Δ ⊢ a.subst σ ≡ b.subst σ : A.subst σ →
```

beside the motive's `Interp Δ (A :: Γ) C (σ.cons (b.subst σ)) (ρ.push v) cb`.
`Interp.tr_bot_of_ne` is the consequence: a transport whose endpoints are
not equal *at the stage* has only `⊥`.

**Why the old model cannot do this, and why that is the whole point.**
**The witness.**  `LE_Interp.tr_stuck` (`Adequacy.lean`, axiom-clean) is
the counterexample, in three lines:

```lean
theorem LE_Interp.tr_stuck {ρ : Valuation} {H : Term} :
    LE_Interp ρ (WShape.T (n := 1) .zero)
      (.tr false .nat .zero (.succ .zero) .nat .zero H)
```

The endpoints `zero` and `succ zero` are not definitionally equal, so no
rule computes this transport and it is stuck at every stage — yet the
model gives it the shape `zero`: take `v := ⊥` (the only shape below both
`zero` and `succ ⊥`), read the constant motive there, and the
transported value `zero` is typed at it.  Adequacy says a term of shape
`zero` reduces to `zero`; this one does not.  `Interp.tr_stuck_bot` is
the same example on the new side, where it is `⊥`; it used to assume
`zero ≢ succ zero` and now proves it (`zero_ne_succ`).

`LE_Interp ρ m M` has no context and no stage.  It cannot state `a ≡ b`;
and it reads the motive at a valuation *slot* (`LE_Interp (ρ.push v) cb C`),
so when `a` and `b` share the slot `v` — which `⊥` always is — it cannot
tell `C[a]` from `C[b]` either.  Its `tr` clause therefore hands a
**stuck** transport the transported value's shapes, and no reduction
justifies that: `LR.adequacy`'s `trDF` case at `r = false` is false for
that model, not merely unproved (`Adequacy.lean`, where the one remaining
`sorry` of the old line sits).  Labels and stages are exactly what buys
the missing premise.
Options in §5.1.  Everything else about `tr` is master's proof.

### 4.7a `sndDF` and `fst_snd`: the Σ analogue of §5.3

**Found while proving the Σ β-rules.**  A pair shape carries its *first
component's* label `(ty, tm)`, and `HasType.pair` types the second
component at `TEvaluates f ty tm x c` — the codomain family looked up **at
that label**.  So for

```lean
SoundTy Γ (.snd p) (B.inst (.fst p))
```

the value `y` of a pair approximant of `p` is typed at `B[tm]`, and what
is wanted is an approximant of `B[fst p]`.  The two agree only given

```lean
Δ ⊢ tm ≡ (Term.fst p).subst σ : ty
```

and nothing in the model forces it: for a *literal* pair the label is
`a[σ]` and `pair_fst` gives it, but for a slot — `p` a variable, the shape
handed over by `Adm` — the label is an arbitrary well-typed term.  The
same equation is what `fst_snd` (Σ's η) needs, in the same place and for
the same reason: to compare the rebuilt `pair A B (fst p) (snd p)` with
`p`'s own pair approximant, whose label is that arbitrary term.

This is exactly §5.3 with Π replaced by Σ: *a typed approximant of a
Σ-typed term must remember where its label came from*, as a typed
approximant of a Π-typed term must remember `HasDom`.  The Π resolution
recommended there — strengthen what `SoundTy` promises at a Π type — has
a Σ twin: **at a Σ type, the typed witness is a pair shape whose label is
the first projection**.  The two should be decided together, since both
are the same change to `InterpTyped`/`SoundTy`, and `app` is the model for
both: there the query *is* the argument, by construction of the rule, and
that is why `appDF` needs no such invariant.

Note this is not the λ-label problem of §5.5b in disguise.  That one was
about a *type* label and was fixed by storing it in the shape, because the
order and `WF` can compare it.  This one is about a *term* label that has
to match a term built from the subject, which the shape does not know.

**What intgrah does (checked).**  *He has no Σ-types at all* — his term
grammar (`Syntax/Extrinsic.lean`) is `sort, app, lam, forallE, nat, zero,
succ, natRec, id, refl, tr`, and the `pair` in his files is CwF context
comprehension, not a pair former.  So there is no precedent to copy, and
the Π machinery has to be read as the pattern.  Read that way it says
something sharp, and it is not what we do at `snd`:

* A label is an element of `Tm.presheaf = typedTerms Tm.typing`, i.e. a
  pair `⟨A, a⟩` of a type and a term of it, **both quotiented by
  definitional equality** (`Tm.pairOfTyping_eq_iff`).  Our `LabelEq` is
  this quotient, spelled as a relation.
* The eliminator's query is not one label but the **set of all typings of
  the subterm**: `sourceQuery Γ a = {pairOfTyping hA ha}` over all `A`,
  and `rawApplication F Q X = ⨆ label ∈ Q, …`.  The term component of a
  responding label is pinned *from the syntax of the eliminator*, never
  from the value.
* A value responds only at labels that are a `Section` of the display of
  the domain — and `Section` is a `Subsingleton`, equivalent to the bare
  **type** equation `label.1 = A[σ]`.  So a value's own structure
  constrains only the label's *type*.  It is our λ domain label exactly.
* The two are married by *theorems*, not definitions:
  `sourceQuery_eq_of_section` (in the query ⇒ the term is `a`; a section ⇒
  the type is `A`; hence the label is the canonical one) and
  `rawApplication_eq_of_support` (then the sup collapses to that label).
  The support hypothesis comes from Π-fixedness, through
  `application_piOperator_fixed`: a Π-fixed `F`'s lookup at any `X` equals
  its lookup at the decoder-normalised `X`.
* There is **no `HasDom`** anywhere, and no typing condition on a graph
  entry's label or input.  Fixedness plus "off-section is `⊥`" does that
  work.

Two conclusions for us.

1. `Interp.app` already follows his pattern: the query *is* `a[σ]`, from
   the syntax.  **`Interp.snd` does not** — it reads the second component
   at whatever label the pair shape happens to carry.  The faithful fix is
   to make `snd` query-driven like `app`: require
   `Δ ⊢ tm ≡ (fst p)[σ] : ty` in the rule, which is his "the label is in
   `sourceQuery (fst p)`" (we can demand a single label rather than a sup,
   because our labels are compared up to defeq in the order, so the sup
   over a defeq class is already collapsed).
2. That shifts the burden to where his `application_piOperator_fixed`
   sits, and there we have nothing: his decoder *normalises* a value to
   its Π-fixed part, which is what makes "the responding label is a
   section" hold for every typed value.  A shape is not an ideal and has
   no retraction, so for us the same fact has to be carried, not derived —
   i.e. §5.3(a) for Π and its Σ twin, by `SoundTy`.  This is the same
   missing retraction as `SoundJoin` (§5.1); it is worth deciding all
   three together.

**Done: `snd` is a query (1).**  `Interp.snd` now carries
`Δ ⊢ tm ≡ (fst p)[σ] : ty`, and `sound_sigma_lookup` (the Σ twin of
`sound_beta_lookup`) turns a lookup in the Σ-shape's graph at that label
into an approximant of the codomain there.  The `SoundEq` half of `sndDF`
and the `pair_snd` β-rule go through with it.

**Where it stands after η.**  η went through on the slot discipline
alone (§4.5g): saturation hands ← a λ-approximant with hereditarily
typed inputs, and → needs nothing new.  `fst_snd` does **not** follow the
same way, and the reason is this section's: to rebuild `pair A B (fst p)
(snd p)` above a pair-approximant `pair A₀ x g` of `p`, every entry of
`g` must be at the canonical label — `Interp.pair` demands
`Δ ⊢ e.tm ≡ (fst p)[σ] : e.ty` — and an off-label entry cannot be
dropped, since dropping it loses the coverage.  So Σ's η needs

> a pair-approximant of a Σ-typed term is below one all of whose entries
> are at the first projection

which is "off-section is `⊥`" (point 2 above) in approximant form: a
*third* conclusion of the same kind as `SoundDom`, about labels rather
than inputs.  `Shape.Dom`'s Σ clause cannot carry it, since a shape
cannot name `fst p`.

**And it cannot be a conclusion of soundness either: as the model
stands, `fst_snd` is false.**  Saturation is now a theorem, so the
obstruction can be stated exactly.  Take `Γ = [Σ nat nat]`, `p = #0`,
`σ = id`, and the slot

```
ρ 0  =  pair nat x [⟨nat, zero, inp, zero⟩]
```

— one entry, labelled by the *closed* term `zero` rather than by
`fst #0`.  This slot is well formed (its output is not `⊥`), it is typed
at the Σ-code `sigma nat nat d f` whose codomain graph answers `nat` at
the label `zero`, and it is hereditarily typed there, `nat` being a
filtering code.  So the valuation is admissible, and `pair nat x […]` is
an approximant of `p`.  But `Interp.snd` queries at `(fst p)[σ] = fst #0`,
and `Δ ⊢ zero ≡ fst #0 : nat` is false, so the entry never fires: every
approximant of `snd p` is `⊥`, every approximant of
`pair A B (fst p) (snd p)` has an empty graph (`Shape.WF` forbids a `⊥`
output), and the slot is below none of them — lookup coverage asks the
`zero`-entry to be answered, and an empty graph answers `⊥`.

So the missing content is not a further conclusion of the induction but
a further *condition on slots*, hereditary like `Dom` and in the same
six clauses: **a slot standing for the term `t`, if it is a pair-shape,
carries only entries labelled `fst t`** (and so on under the pair).
That is a third discipline of the size of this one.  The alternative,
and probably the better one, is to take the graph out of the Σ-value:
a pair's second component does not vary with the label the way a
function's output varies with its argument — the graph is there only to
record which label its *typing* was read at.  A Σ-value of the form
"first component `x`, second component `y`, label `tm`" would make Σ's η
the mirror of Π's, with the canonical label forced by the single
constructor, and it is a smaller change than carrying canonicity
hereditarily through `Adm`.  Either way this is a design decision, and
it is Mario's.

### 4.7c Σ's η: what the Π analogy actually says, and the design

**The analogy does not transpose, and the way it fails is the design.**
η for Π works because the expansion has a *binder*: `λx. e x` rebuilds a
λ-approximant of `e` entry by entry, and at the entry `⟨tm, inp⟩` the
body `app e.lift #0` is read at the stage `σ.cons tm` — so the
eliminator's query term is *whatever the entry's label says*.  A label
mismatch cannot arise, because the binder absorbs it.

`⟨fst p, snd p⟩` has no binder.  Its label is forced to `(fst p)[σ]` by
the `pair` clause, while `p`'s own pair-approximant carries whatever
label it was built with.  So where Π's η needs nothing of labels, Σ's η
needs exactly one thing: **a pair-approximant of `p` is labelled by
`p`'s own first projection**.  That is the whole content of §4.7a's
counterexample, and no change to the Σ-*value* removes it: relabelling
has to be justified, not avoided.

**The graph cannot go.**  Shape.lean's own comment is right.  Write
`f` for the Σ-code's codomain family and consider a pair `⟨x, y⟩` whose
second component is a single shape:

* typing `y` at the code read at `x` (`f(tm, x)`) is **join**-closed
  (`f` is monotone in the input, so both codes sit below `f(tm, x₁ ⊔ x₂)`)
  but not **lower**-closed: shrinking `x` to `x'` shrinks the code, and
  `y` is not typed at the smaller one.  With `B z` a `natCase` on `z`,
  `⟨succ zero, succ zero⟩` is typed and `⟨⊥, succ zero⟩`, which the order
  gives for free, is not;
* typing it at a *dominator* `x̄ ≥ x` is lower-closed (the witness
  survives) but not join-closed: the two dominators need not be
  compatible, so there is no code to join at.

The input-indexed family is what makes the second component's
information *conditional on the first*, which is what dependent typing
needs in a domain model.  What **can** go is the per-entry *label*: a
pair's entries may be indexed by input alone, with one label for the
whole pair (`WF` forcing every entry's label defeq to it).  That is a
simplification, not a fix — and it is optional, since the condition
below can be stated per entry.

**The fix: `Dom` relative to a term.**  Saturation (`SoundDom`) is the
Π pattern: η ← does not rebuild from the *given* approximant but from
the hereditarily typed one above it, and downward closure brings the
given one along.  Σ's η wants the same move, and needs the dominator to
be *canonically labelled*.  So `TShape.Dom Δ d x` becomes
`TShape.Dom Δ t d x` — "`x` is hereditarily typed at `d` **as a value of
the term `t`**" — with the clauses following the eliminators:

| `x` | conditions |
|---|---|
| filtering code | as now (`HasType`) |
| `lam`-shape | each entry's input `Dom` at *its own label* `e.tm`; each output `Dom` at `app t e.tm` |
| `pair`-shape | every entry's label `≡ fst t`; the first component `Dom` at `fst t`; each output `Dom` at `snd t` |

Every slot-creating clause already knows the term its slot stands for
(`Adm`: `σ i`; `Interp.lam`: the entry's label; `Y`: `(Y A b)[σ]`;
`tr`: `b[σ]` and `X[σ]`; `pair`: `a[σ]` and `b[σ]`), so the discipline
threads through unchanged in shape — only the terms are new.  The eight
saturation cases keep their proofs: at `app`, for instance, the firing
entries are at labels defeq to `a[σ]`, so their outputs are `Dom` at
`app f a[σ]`, which is the subject.

With that, `fst_snd` ← is three lines: saturate `p`, read `fst` and
`snd` off the dominator (the query fires, the label being canonical),
rebuild the pair, and bring the given approximant along by
`Interp.mono`.  → is `dir`, as `sound_eta_to` is.

**But canonicity cannot live in `Dom`** (tried, commit `8734b66`, and
reverted).  `Dom` is shape-level, and a term-indexed shape-level
predicate has no defeq transport.  The place it dies is `join_at`:
joining two hereditarily typed pairs identifies their first components,
so it must identify the *terms* they stand for — an equation at the
Σ-code's domain label `A` — and then push a sub-`Dom` along it.  Pushing
`Dom Δ s d y` along `s ≡ s' : A` means re-proving the clause's equations
at whatever head `d` has, so it needs `A ≡ Π A' B'` when `d` is a
Π-code; and nothing at shape level says `d` approximates `A`.  `WF` of a
`sigma` shape does not relate its domain *code* to its domain *label*,
and cannot: codes are shapes, labels are terms.  The same wall appears
at every producer (`sound_pair_dom` needs `a[σ] ≡ fst (⟨a,b⟩[σ])`
pushed into a sub-`Dom`), so it is not an artefact of `join_at`.

The type is recoverable one level up: `Interp Δ Γ t σ ρ x` *does* know
which term the shape approximates, and a derivation knows its type.  So
the condition belongs there — a second hereditary predicate, by
recursion on the shape and parameterised by the term,

```
Canon Δ Γ σ t x :
  pair ⟨A₀, x₁, g⟩ ↦ (∀ e ∈ g, Δ ⊢ e.tm ≡ (Term.fst t).subst σ : e.ty) ∧
                     Canon (.fst t) x₁ ∧ ∀ e ∈ g, Canon (.snd t) e.out
  lam ⟨A₀, g⟩      ↦ ∀ e ∈ g, Canon ?(e.tm) e.inp ∧ Canon (.app t ?) e.out
  _                ↦ True
```

demanded by `Adm` and the six slot-creating clauses beside `Dom`, and
produced by saturation alongside it.  Its transport *is* provable, by
the same shape recursion with the type as a hypothesis: at a pair the
sub-terms are `fst t` and `snd t`, whose types come from `T = Σ A B`.

That is a second discipline the size of the first (predicate, API,
`Adm` and six clauses, eight saturation cases, then `fst_snd`), and it
is what Σ's η costs.  Dropping the graph from Σ-values does not pay any
of it.

**The transport claim in the paragraph above is wrong**, and §4.7d is
what replaces it.

#### 4.7d Why canonicity does not transport: three locked doors

The labelled-shape surgery of this branch (`sigma-no-graph`) carried out
the premise of §4.7c: value shapes now carry their type labels
(`lam A B g`, `pair A B x g`), `Shape.tyOf` reads the type a value
names, and `Shape.Canon` is the hereditary condition "every entry label
names this value's own first projection".  `Canon.defeq`, `Canon.subst`
and `Canon.lift` are **proved** (`HasType.lean`).  The discipline then
fails at one specific place, and the failure is not an accident of the
formulation: every formulation fails at the same place, for one of three
reasons.

`Canon` must be closed under the join — saturation reads lookup values,
and a lookup value is a join of entry outputs.  Joining two canonical
values at one subject needs their *nested* label data related:

* **Type-indexed** (`Canon Δ T t x`, conditions read off `T = Σ A B`):
  joins are free (both sides read the same `A`, `B`), but the soundness
  induction's conversion rule needs `Canon Δ T t x → TyEq Δ T T' →
  Canon Δ T' t x`, which for `T = Σ A B`, `T' = Σ A' B'` **is Σ
  injectivity**.
* **Label-indexed** (conditions read off the value's own labels, this
  branch): conversion is free, but the join of two pair shapes needs
  `TyEq Δ (B.inst e.tm) (B'.inst e.tm)` for the right-hand entries, and
  `Compat` compares only the *domain* labels.  Comparing codomains too
  makes `HasType.mono_l` false (a smaller shape's codomain label is
  arbitrary), and tying them in `HasType` needs the comparison — the two
  requirements are each other's premise.  Deriving the equation from the
  two typings instead **is Σ injectivity** again.
* **Typing-quantified** (`Canon Δ t x` with `∀ A B, Δ ⊢ t : Σ A B → …`
  inside): joins and conversion are both free, but the transport along
  `Δ ⊢ t ≡ t' : T` must move the hypothesis `Δ ⊢ t' : Σ A B` back to
  `t`, i.e. relate `T` and `Σ A B` — **type uniqueness**.
* **Code-indexed** (the `Dom` pattern, conditions read off a Σ-*code*'s
  labels): joins and conversion are free (defeq types have the *same*
  approximants), and the nested equations need the code's label to agree
  with its sub-codes' labels.  That coherence is a sound `WF` conjunct
  for codes — `Shape.LE` already compares `PiLabelEq` there — but it
  cannot be *established*: a code for `app F x` (a type family) is a
  lookup in a λ-value's graph, and `Interp.lam`'s codomain label is
  free, because `Term.lam A e` does not carry the codomain.  Forcing it
  is impossible for the same reason; `Term.pair A B a b` *does* carry
  both, which is why the Σ half has no analogous problem.

So the three doors are **Σ/Π injectivity**, **type uniqueness**, and
**syntactic determinism of the codomain label**, and all three are
locked before soundness: `Inversion.lean` derives injectivity from
`IsDefEq.sound`, `Consequences.lean`'s `HasType.uniq` derives uniqueness
from injectivity, and the λ label is not in the term.  Inside the
soundness induction only the *subderivations*' soundness is available,
and the equations that need inverting are derived facts, not
subderivations.

What this costs is exactly `fst_snd`, and nothing else: η for Π,
saturation, and the other 40-odd rules are proved.  The ways out, in
the order I would try them:

1. **Prove injectivity (or uniqueness) syntactically**, by a
   parallel-reduction/Church-Rosser argument on the instrumented terms,
   as a standalone development.  Everything else here is then ready:
   with uniqueness, the typing-quantified `Canon` above closes
   `fst_snd` with no further model surgery.
2. **A second, coarser model** whose soundness is easy (no labels, so
   `fst_snd` is free), used only to derive injectivity, then cited by
   this one.  This is the usual stratification and is what the
   `logrel`/`total` work would give.
3. **Carry the codomain label on `Term.lam`** (a change to the object
   syntax, not to the model), which unlocks the code-indexed door: the
   `WF` coherence becomes establishable, and canonicity becomes a third
   discipline of the `Dom` kind with a transport that needs no
   inversion.

### 4.7b The dominator: resolved by (β)

*Superseded.*  This section recorded the obstruction as it stood with the
old Σ-value (a first component and a *single* second component, typed at
a code read at a **dominator** `x ≥ x'` of the first component).  The
dominator was there for lower-closure of typing, while `Interp.inst`
needs the code read at a slot that *approximates* `fst p` — the two pull
in opposite directions, and the note closed by listing three ways out,
all of them the §5.1/§5.3 decision.

(β) (§5.1b) removed the dominator: a Σ-value is now a first component
`x` and a *graph* `g`, and `HasType.pair` certifies that graph by a
**generator**, exactly as `HasType.lam` does.  A generator entry sits
*below* the graph entry it covers, whose input is below `x`, and `x` is
an approximant of `fst p` (the `fst` rule says so); so every code is read
at a slot approximating `fst p`, and `Interp.inst` applies.

`sound_snd_ty` is `sound_app_ty` transposed, line for line, and
`sound_snd_eq` is `sound_app_eq`'s twin with `Interp.pair_label_ty` for
the query's type.  `sndDF` is closed.  The remaining Σ hole is
`fst_snd` (η), which needs the §4.7a label invariant — that a Σ-typed
value's label names its *own* first projection — and that is still the
§5.3 decision.

#### 4.7e The other direction is false: a pair's input is not consulted

While proving `sound_fst_snd_of` (the ← direction, `Presheaf.lean`,
proved against `PairCanon`) I checked the ← /→ split and found that **→
is false as the model stands** — not blocked, false.  Compare the two
clauses:

    | lam  …  (∀ e ∈ g,  Interp Δ (A :: Γ) b (σ.cons e.tm) (ρ.push e.inp.T) e.out.T)
    | pair …  (∀ e ∈ g₀, Interp Δ Γ b σ ρ e.1.out.T)

A λ-entry's input *is* the slot its body reads, so an entry's output is
justified at exactly that input, and η's expansion — whose body is a
lookup at the pushed slot — lands on the same input.  A pair-entry's
input is never read: it only picks the code that types the output
(`Interp Δ (A :: Γ) B (σ.cons e.1.tm) (ρ.push e.1.inp.T) e.2`).  The
*order*, though, reads it as a genuine condition: `ShapeFun.LE` honours
an entry `(ty, tm, inp, out)` only by a lookup **at that same `inp`**.
So a value may promise a second component conditionally where the
η-expansion promises it outright.

Concretely, in `Γ = [Σ nat nat]` at the closed stage
`σ = one (pair nat nat zero zero)`, take the slot

    ρ 0 = pair nat nat zero [⟨nat, fst (pair nat nat zero zero), zero, zero⟩]

— WF (first component `zero`, output not `⊥`), hereditarily typed at the
Σ-code, and *canonically labelled* in the §4.7a sense, so admissible
under `Adm` and under any canonicity discipline.  `Adm` asks for nothing
else: a slot need not be an approximant of a term.  Then

    pair nat nat zero [⟨nat, fst (pair nat nat zero zero), ⊥, zero⟩]

is an approximant of `⟨fst #0, snd #0⟩`: its entry's label is `fst #0`
at the stage, its input `⊥` is an approximant of `fst #0`, its output
`zero` is an approximant of `snd #0` (the lookup in `ρ 0` at the pair's
own first component fires), and the code at `⊥` is `nat`, which types
`zero`.  It is **not** an approximant of `#0`: the lookup in `ρ 0` at
input `⊥` does not fire, because that entry wants `zero ≤ ⊥`.

Note what the counterexample does *not* use: no dependency (`B = nat`),
no exotic valuation, no failure of canonicity.  It is the encoding
itself.  The tension is exactly §5.5's, seen from the other side:

* the **graph** is what makes typing lower-closed *and* join-closed
  (§5.1b (β)), because an entry's input names the code that justifies
  its output;
* **η** says a pair is its two projections, so the second component's
  information must not depend on how much of the first you present —
  i.e. the input must be semantically inert.

The input cannot be both.  A Σ-value with no graph (Mario's "option 2")
makes η true and `HasType.join` false; the graph makes `HasType.join`
true and η false.  Ways to break the tie, none of them local:

1. **Input-saturated slots.**  `Adm` is a condition on *one* valuation,
   not on a downward-closed set, so it may demand that a slot promise
   each output at every input whose code types it.  Approximant sets
   stay downward closed (the `bvar` clause is unchanged), and → becomes
   provable.  The cost: `Subst.Saturates` must *build* such slots, which
   needs a least typable input to exist — i.e. that the typable inputs
   of an output are upward closed with a least element.  That is a real
   question about `HasType`'s behaviour in the code, worth checking
   before anything else, because it is the cheapest of the three.
2. **Make the input semantically live**, by interpreting the second
   component against the entry's input the way `lam` does.  There is no
   slot for it to read — `pair A B a b` has no binder — so this means
   changing what a Σ-value is.
3. **Give up lower-closure of typing** for Σ (master's `InterpTyped`,
   §5.1b's fallback (δ)): then the graph is unnecessary and η is Π's.

#### 4.7f Option 2, carried out: what it fixes and what is left

The branch `sigma-no-graph` now carries Mario's option 2.  A Σ-value is

    | pair (A B a : Term) : Shape → Shape → ShapeS Shape

its two components with the first's *term* as a name; `snd` reads the
second component at a pair whose name is `fst p`, as a clause premise
rather than a graph query.  The whole development is green, and both
directions of Σ's η are theorems against a single named condition.

**What the graph's departure fixes.**  §4.7e's counterexample is gone:
with no entries there is no input for a value to promise a second
component at, so `sound_fst_snd_to` (η's → direction, *false* with the
graph) is now proved — two components, each an approximant of a
projection, one directedness step, and the order compares.

**What pays for it.**  §5.5's objection to a graph-free Σ was that
typing cannot be both lower- and join-closed.  Both still hold, by
splitting them between the two predicates that need them:

* `HasType.pair` reads the second component's code at a **dominator** of
  the first, so shrinking either component keeps the same code — typing
  stays lower-closed, which `SoundTy` and `mono_l` need;
* `Dom`'s `sg` clause reads it at the **first component itself**, so two
  compatible values have compatible codes — `Dom` stays join-closed,
  which `dir` and saturation need, and `Dom` is never used downward.

`sound_join` is therefore stated on `Dom`, and the two lookup inductions
that consumed it — `sound_app_ty` and `sound_snd_ty` — are deleted in
favour of `SoundTy.of_dom`: an approximant sits below a hereditarily
typed one, and typing is lower-closed, so **saturation gives typing**.
That is a simplification the Π side should eventually share.

**What is left** is one line, inside the `fst_snd` case:

    have hcanon : PairCanon Δ Γ σ ρ p := sorry

`PairCanon` says: every pair-approximant of `p` is named by `p`'s own
first projection.  It is §4.7a's invariant in its smallest form — one
equation per pair, no graph, no hereditary shape predicate at the point
of use.

**Why it is still open.**  To carry it, the name must move when the
subject does: from `a₀ ≡ fst t : A₀` and `t ≡ t' : T` one needs
`fst t ≡ fst t' : A₀`, i.e. `fstDF`, i.e. the equation at a *syntactic*
Σ whose domain is `A₀`.  The value's own typing gives a Σ-*code* for
`T`, so what is missing is exactly

    Interp Δ Γ T σ ρ (sigma A' B' d f) → TyEq Δ (T.subst σ) (Σ A' B')

— "a code names its type".  That is provable as a further hereditary
invariant (through λ-graphs, since a type family's codes are read out of
one), and its own transports are *sort-level*, so they need no
inversion; but each step of it needs the subject's typing, which only
the soundness induction has.  So the two invariants have to be two more
conclusions of that induction, each the size of the `Dom` discipline.
Short of that, the name's transport reduces to Σ-injectivity (§4.7d),
which this model supplies only *after* soundness.

The state to resume from: `PairCanon` is the only hole, both η
directions are proved from it, and the next step is `SigOk` ("a code
names its type") as a sixth conclusion, then `NameOk` as a seventh.

#### 4.7g The name invariant's λ clause: mono or subst, not both

`Shape.Canon` (`Interp.lean`) is the invariant §4.7f asks for — a code
names its type, a pair names its first projection, hereditary through
λ-values — with `Canon.mono` proved.  Adding it to the six slot-creating
clauses and to `Adm` is where it dies, and the reason is worth keeping:

* read **query-based** (`∀ q, every lookup at q is `Canon` at `app t q`'),
  it is *downward closed* — the order's coverage is lookup-wise, so a
  smaller λ's lookups are the bigger one's — but it does **not survive a
  substitution**: `g.subst τ` is queried at Θ-terms outside the image of
  `τ`, and the entry that answers has label `e.tm.subst τ ≡ q'`, not
  `q'`;
* read **entry-based** (`∀ e ∈ g, Canon (app t e.tm) e.out`), it
  substitutes — entries map — but is **not downward closed**, since
  coverage answers a smaller entry with a *join* of outputs sitting at a
  definitionally equal label.

Both gaps are the same step: the query slides along a definitional
equality, and the pair conjunct then needs `fst q ≡ fst q'`, i.e.
`fstDF`, i.e. the subject's Σ-typing — which is exactly what the
invariant was introduced to supply.  Carrying the type in the invariant
closes that step and reopens the join (Σ-injectivity, §4.7d); carrying
the *typing* closes the join and reopens the conversion (type
uniqueness, which in this calculus reduces to injectivity, which the
model supplies only after soundness).

So the position is stable under all four readings, and `fst_snd` is
where the model's own inversion principles are needed before they
exist.  The ways out are unchanged (§4.7d): prove injectivity
separately, stratify through a coarser model, or put the codomain on
`Term.lam` so the labels are term-determined.  The attempt is in the
history (`05dcd81`, reverted in `be069e8`) with `Shape.Canon` and
`Canon.mono` kept, since any of those routes starts from them.

#### 4.7h The old model cannot lend its injectivity

The obvious shortcut — take `sigma_inv` from `Adequacy.lean`, which does
not import this model, and use it to discharge the name invariant's
transports — does not work, and the reason is instructive.

`LE_Interp.sound` (`Sound.lean`) is **sorry-free** (`propext`,
`Classical.choice`, `Quot.sound`).  But the old model's shapes carry no
syntax:

    | sigma : LE_Interp ρ b.T B → LE_Interp ρ b'.T B → WShape.HasDom f b' →
        (∀ x, x.HasType b' → LE_Interp (ρ.push x.T) (f.app x).T F) →
        m ≤ WShape.T (.sigma b f) → LE_Interp ρ m (.sigma B F)

so the probe argument has nothing to read back: from a Σ-shape
approximating `Σ A₁ B₁` one learns only that its domain part
approximates `A₁`, never that `A₀ ≡ A₁`.  That is exactly why the
labelled model was built.  The old file's `sigma_inv` therefore goes
through `sigma_whRed_l` — weak-head reduction, i.e. **adequacy** — and
`Adequacy.lean`'s single `sorry` is a case its own model makes *false*
(the `tr` clause reads the motive at a slot, so it cannot tell `C[a]`
from `C[b]`).  `#print axioms` confirms the taint: `sigma_inv` and
`HasType.uniq` both depend on `sorryAx`.

So the stratification route needs a *labelled* coarser model, not the
one already in the repo.

#### 4.7i The diagnosis, against master and intgrah; and the door that was open

**What is actually wrong.**  Read the two reference models side by side.

* *Master* is a **value-driven** model with label-free shapes.  A pair is
  `pair : Shape → Shape → ShapeS Shape`; `natCase` fires when the
  scrutinee's *shape* is `succ v`; a pair's second component is typed at
  the Σ-code's codomain read at the first component's *shape*
  (`y.HasType (b.app x)`).  Nothing in the model mentions a term, so a
  variable's slot is any pair of typed shapes, `⟨fst p, snd p⟩`
  approximates to `(x', y')` with `x' ≤ x`, `y' ≤ y`, and Σ's η is a
  one-liner (`Sound.lean`, `fst_snd`).  The price is paid elsewhere: with
  no syntax in the shapes, `⟦Σ A B⟧ = ⟦Σ A' B'⟧` says nothing about
  `A ≡ A'`, so injectivity needs weak-head normalisation — the adequacy
  proof, whose one `sorry` is the stuck `tr` that this model cannot
  express.
* *The presheaf model* (intgrah's pattern) is **stage-driven**: an
  interpretation is indexed by a substitution σ, reduction happens when
  the *term at the stage* is definitionally a redex (`natCase_succ`
  needs `Δ ⊢ M[σ] ≡ succ t`), and a binder's body is read at a stage
  extended by a **term**.  That is what the labels are for, and it is
  what makes injectivity fall out of soundness.  It also means the
  codomain `B` of a Σ is a family over *terms*: `B[σ, succ zero]` and
  `B[σ, fst #0]` have different codes (`natCase` on the variable
  computes in one and is stuck in the other), even at the same slot.  So
  the type of a pair's second component is a function of a *term*, and
  the pair must know which one.  There is no label-free Σ-value in a
  stage-driven model: the name is forced, and a label-free pair would be
  typed at nothing in particular.
* *intgrah* has no Σ, but his Π says what the right shape of the fix
  is.  A λ-value is a **family over labels**: it responds at every query,
  and `app f a` pins the query from the syntax of `a`.  Its η holds
  because the expansion `λx. f x` rebuilds the family label by label,
  with the binder absorbing the label.  A pair is not a family; it is a
  **point at one stage**.  `snd p` pins the query `fst p` from the
  syntax, and a point at the stage `succ zero` does not respond to it.
  A slot that is a point at the wrong stage is exactly the
  witness in §4.7h.

So nothing is wrong with the Σ-*shape* as it now stands (`pair A B a x
y`, §4.7f): it is the only possible Σ-value here.  What is wrong is
`Adm`: it admits a slot for `p` that is a value of some *other* term.  At
the generic stage the only term a variable's slot can stand for is the
variable, and the condition "the slot for `σ i` is named `fst (σ i)`,
hereditarily" is a missing conjunct of admissibility, of the same kind as
`Dom`.  That is the §4.7a conclusion; what was unresolved was whether the
conjunct could be *propagated* (§4.7d, §4.7g: three locked doors).

**The doors were locked by the formulation, not the model.**  All four
attempts (§4.7d) asked the *value* to know its own type — read off its
labels, off a quantified typing, or off a `WF` coherence of codes — and
then needed Σ-injectivity or type uniqueness to move the name along a
definitional equality of the subject.  But the type is never needed from
the value: the value is `Dom`-typed at a **code**, the code carries
labels, and whether a code names its type is a sort-level fact.  Stated
relative to the code, the transport is a theorem with no inversion in it.
`DomainSemantics/Canon.lean` (new) has it, machine-checked, with the
closure properties the two uses need:

```
Shape.CodeCanon Δ T d   -- a code names its type, hereditarily
  sigma A B d f ↦ T ≡ Σ A B ∧ CodeCanon A d ∧
                  ∀ e ∈ f, e.out = ⊥ ∨ (e.ty ≡ A ∧ CodeCanon (B[e.tm]) e.out)
  sort r        ↦ T ≡ sort r          (likewise nat, unit, Id, Π)
Shape.ValCanon Δ t x    -- a value names its own projections
  pair A₀ _ a x y ↦ a ≡ fst t : A₀ ∧ ValCanon (fst t) x ∧ ValCanon (snd t) y
  lam _ _ g       ↦ ∀ e ∈ g, ValCanon e.tm e.inp ∧ ValCanon (app t e.tm) e.out
  code-shaped     ↦ CodeCanon t x
```

* `ValCanon.defeq : Dom d x → CodeCanon T d → ValCanon t x → (Δ ⊢ t ≡ t' : T) → ValCanon t' x`.
  At a pair the code is `sigma A B d₁ f` with `T ≡ Σ A B`, so `fstDF₀`
  and `sndDF₀` apply at a *syntactic* Σ; the components recurse at
  `d₁` (canonical for `A`) and at the lookup `f(a, x)` (canonical for
  `B[a] ≡ B[fst t]`).  At a λ the code is a Π-code, `appDF₀` applies,
  and each output recurses at the entry's own code from `Dom.pi`.  This
  is the lemma §4.7c, §4.7d and §4.7g could not state.
* `CodeCanon.mono` (downward closed, needs `WF` of the bigger code) and
  `CodeCanon.join`: codes compare *both* labels (`PiLabelEq`), so no
  injectivity is needed; dead entries (output `⊥`) are exempt because
  the order can hand them to a smaller code under any label type.
  `CodeCanon.lookup` derives the query-based reading from the
  entry-based one through these two.
* `ValCanon.subst`, `CodeCanon.subst`: entry-based, so entries map and
  `(fst t)[τ] = fst (t[τ])` is syntactic.  No typing is consulted.

The two horns of §4.7g are split between the two predicates: **values
are entry-based** (substitutive; downward closure is never consumed,
since the consumers are saturation, which produces a canonical value
*above*, and the pair's name, which the order preserves), **codes are
query-based in effect** (downward closed, because their transports are
at sorts).  Door 3 — the λ-value's undetermined codomain label — is not
touched: the codomain code is read from the Π-code that `Dom`-types the
λ-value, which the induction supplies canonical for the *derivation's*
type, never from the λ-value's own `Bd` (now vestigial).

**What remains is propagation, and it is the `Dom` discipline again.**

1. `Adm`: `∃ a, Interp Γ_i σ ρ a ∧ Dom a (ρ i) ∧ CodeCanon (Γ_i[σ]) a ∧ ValCanon (σ i) (ρ i)`.
2. The slot-creating clauses add `ValCanon tm inp` for the slot they
   push (`lam`, `forallE`, `sigma`: `e.tm`/`e.inp`; `pair`: `a[σ]`/`x`;
   `Y`: `(Y A b)[σ]`/`x`; `tr`: its two; `natCase_succ`: nothing, the
   slot is a numeral).  `Interp.subst`/`weak`/`ctx` go through by the
   `.subst` lemmas.
3. A sixth `Sound` conclusion, `SoundCanon Γ t A`: every approximant of
   `t` is below one `m'` with a code `a` of `A[σ]`, `Dom a m'`,
   `CodeCanon (A[σ]) a` and `ValCanon (t[σ]) m'`.  `bvar` is `Adm`;
   `app` saturates `f`, transports each firing entry's output along
   `app f e.tm ≡ app f a[σ]` by `ValCanon.defeq` with that entry's code,
   and joins; `lam`/`forallE`/`sigma`/`pair` saturate their bodies at
   the extended (now admissible) valuation and transport along β /
   `pair_fst`; `fst`/`snd`/`Y`/`tr` read the saturated subject's
   components; the rest are `of_eq` across `SoundEq`, as `SoundDom` does
   it.  Every transport site has the derivation's syntactic type and a
   canonical code for it, which is all `ValCanon.defeq` asks.
4. `PairCanon` is then `SoundCanon` at `p` plus `Shape.le_pair`, and
   `fst_snd` closes (both directions are already proved against it).

The old `Shape.Canon` block in `Interp.lean` (type-indexed, query-based
λ clause) is superseded by `Canon.lean` and should be deleted when the
clauses are rewired; `PiLabelEq.sigmaEq`/`forallEEq` and `IsDefEq.ctx_id`
/`Ctx.SubstEq.defeqHead` have local copies there to be deduplicated
(`Canon` sits between `HasType` and `Interp`).

#### 4.7j Done: the propagation, and the two things it found

The plan of §4.7i is carried out, and **`IsDefEq.sound` has no `sorry`**
(axioms `propext`, `Classical.choice`, `Quot.sound`), Σ's η included.

* `Adm` asks, per slot, `CodeCanon (A[σ]) a ∧ ValCanon (σ i) (ρ i)`;
  `IsTypeAt` asks for code canonicity too, and `Saturates.lift` takes the
  pushed slot's name.
* The clauses carry the names of the slots they push: λ/Π/Σ entries'
  inputs, the pair's first component and its domain code, `Y`'s tower and
  its code, `tr`'s witness and its code.
* `SoundDom` concludes, besides the dominator and its `Dom` code, that
  the code names the type and the dominator names the term.  Most cases
  were pass-through; the ones with content are `app` (each firing
  entry's output is moved from `app f e.tm` to `app f a` by
  `ValCanon.defeq` through the entry's own code), `lam` (β per entry),
  `natCase` and `Y` (ι and unfolding, at the stage), `snd`/`fst` (read off
  the saturated pair), and **`pair`**, whose dominator has to be rebuilt:
  the second component is an arbitrary approximant of `b`, so `b`'s
  saturation enlarges it, `Interp.inst` reads its code as `B` at a slot
  for `a`, and that slot is joined with the given first component and
  saturated.
* `PairCanon` is then a lemma (`PairCanon.of_dom`): a pair-approximant
  sits below the saturated one, which names `fst p`.

Two things the propagation turned up, both fixed in the model:

1. **The `tr` clause at `r = true` was wrong for names.**  It accepted a
   `refl`-shaped approximant of the proof, so a stuck `tr A a a C X h`
   (with `h` a variable holding a `refl` slot; there is no UIP) received
   `X`'s values, whose pairs are named `fst X`, not `fst (tr … X h)`.
   The clause now asks for `H[σ] ≡ refl a[σ]` at the stage, as
   `natCase` asks for `M[σ] ≡ succ t`; then `tr … ≡ X` there by
   `tr_refl` (`IsDefEq.tr_stage`), and at `r = false` the equation is
   proof irrelevance.  For the same reason the clause carries that its
   transported value names `X[σ]` and its code names `C[σ, b[σ]]`;
   re-saturating `X` cannot supply this, because the code it gives is
   read at a slot for `a`, and the clause's slot must approximate `a`
   and `b` at once.
2. Moving those names along a stage needs `X`'s and `C`'s typings, so
   `tr`'s annotation records them, as a typing *up to equality*
   (`x : C₀[a₀]`, `a₀ ≡ a`, `C₀ ≡ C`), which `trDF` supplies without
   instantiating (`IsDefEq.annot` has no `⊢ Γ`).

The old witness is now excluded: well formed
and hereditarily typed, but not admissible, the failed
conjunct being its name; `succ zero ≢ fst #0` is a corollary of
soundness.

### 4.8 The remaining cases, in one line each

`sigmaDF`, `pairDF`, `fstDF`, `sndDF`: mirror Π/λ/app with the pair's
label `(A[σ], a[σ])`; `pair_fst`/`pair_snd`/`fst_snd` are the β/η of Σ
and go as §4.5, with `fst_snd` needing the lookup-coverage order for the
same reason as η.  `succDF`, `natCaseDF`, `natCase_zero/succ`: master's,
with the successor branch's label premise `Δ ⊢ M[σ] ≡ succ t : nat` moved
by `IsDefEq.subst`.  `YDF`, `Y_unfold`: master's `Y_iff` (one line) and
`sound_Y`/`Y_cong`, needing `unweak`.  `idDF`, `reflDF`: label-only.
`defeqDF`, `symm`, `trans`, `trans'`: done.

---

## 5. Open decisions

### 5.1 Join-closure of a type's extension (`SoundJoin`) — **closed**

**Resolved by (β) (§5.1b).**  `TShape.HasType.join` is proved
(`HasType.lean`): at one level, by induction on the level, with the
sort-typed shapes going to `join_sort`, numerals through
`IsNumeral.join`, and `lam`/`pair` appending their graphs and
concatenating their generators (lifted to a common level by
`join_gen_wf`/`_cover`/`_code`/`_ty`).  For the lift to carry the
lookups, both clauses now also carry their generator's entrywise
well-formedness, `ShapeFun.WFE` — the first half of `ShapeFun.WF`,
without the coherence, which two generators certifying *compatible*
values need not have.

`SoundJoin` is therefore `sound_join`: no `Interp`, no `Adm`, no
induction on the type.  Its consumers are discharged — `sound_app_ty`
lost its hypothesis, `dir_tr` is proved, and `IsDefEq.dir` has no holes
at all.  The analysis below is kept because it is what identified (β),
and because §5.5's counterexample remains the reason the *old* pair
could not be joined.

**Correction, from proving `appDF`: it is not needed by `tr` only.**  Every
consumer of a *relational* lookup needs it.  A lookup's `join` rule returns
`y₁ ⊔ y₂` with the two sides typed separately, and typing the join is the
only way to type what the lookup returned; `SoundJoin.hasType_join`
(`Presheaf.lean`) is the two-line bridge, using that typing is
lower-closed.  Master never meets this because its lookup is a saturated
max-below *function* — no `join` rule to discharge.  So the current
consumers are `tr`'s directedness, `appDF`'s `SoundTy` (`sound_app_ty`
takes it as a hypothesis and is otherwise complete), and whatever else
reads a lookup: `lamDF`, `fst_snd`, `eta`.

**And the obstruction is sharper than "incompatible dominators".**  The
pair order is *componentwise*: `pair ty tm x'' y ≤ pair ty tm x' y` as soon
as `x'' ≤ x'`, with the second component unmoved.  But the second
component's code is the codomain looked up *at the first component*.  So:

* read the code at the component and lower-closure fails — shrinking `x'`
  shrinks the available code while `y` stays;
* read it at a dominator and the join fails — two pairs can dominate
  incompatibly.

No choice is stable both ways, which is why `HasType.join` had to go when
typing became lower-closed.  λ escapes because its order is lookup
coverage: an entry's output is bounded by a lookup *at that entry's own
input*, so shrinking an entry shrinks what it must be typed at, and the
generator `g₀` composes downward (`TEvaluates.trans`).  In other words the
λ-order already has the fibrewise character the pair order lacks.

**Is `SoundJoin` dischargeable where it is used?**  Half of it, yes, and
that half is structural: the computation and congruence rules are *padded*
with a typing of their own result type — `appDF` carries
`Γ ⊢ B.inst a ≡ B.inst a' : sort v`, `trDF` carries
`Γ ⊢ C.inst b ≡ C'.inst b' : sort v` — so if `SoundJoin Γ t` were a third
conclusion of `IsDefEq.sound` for judgments at a sort, every consumer
would get it from a premise's induction hypothesis.  That is what the
padding is for, and it is why `sound_app_ty` taking it as a hypothesis is
the right *shape*.

The other half fails, and this is the reason the hypothesis cannot be
discharged today: **that third conclusion cannot be proved by induction on
the type's syntax.**  At the formers it goes through (`sort` is
`join_sort'`, `nat` is numerals, `unit` is `⊥`, `id` is `refl` of a join,
Π is graph append), but at a *neutral* type — a variable of sort type, or
`B[a]` with a neutral head — the type's approximant is an arbitrary type
*shape* and there is no syntax left to induct on.  The statement there is
exactly master's shape-level `HasType.join`, which is also what the Σ case
needs.  So `SoundJoin` is a stand-in: the real lemma is the shape-level
one, and the pair clause is the only place it fails.

#### 5.1b Which option works on paper

§5.5 already has the decisive example, and it is worth reading as a
*test* rather than as an obituary:

> `f` a Σ codomain graph with entries `.zero ↦ c₁` and `.succ ⊥ ↦ c₂`;
> `y = .pair ty tm ⊥ b₁` and `z = .pair ty tm ⊥ b₂` with `bᵢ : cᵢ`
> non-`⊥` and compatible.  Each is typed, with dominators `.zero` and
> `.succ ⊥`; the two are compatible; their join is typed only if one input
> serves both, and no numeral is above `.zero` and `.succ ⊥`.

What the example actually shows is **not** that dependent pairs cannot be
joined.  It shows that a pair shape can record only *one* conditional
fact — "at *this* much of the first component, the second is at least
that" — because it has one second component and therefore one input.  The
join needs two such facts at once.  Everything else follows from that.

Against that test:

* **(α) restrict the order.**  Dead.  The order cannot see types, and
  "the second component lies in the fibre over the first" is not a
  property of a shape.  Any attempt to write it collapses into (β).

* **(γ) strengthen `SoundTy`.**  Survives the test only by leaving the
  shape level: two pairs *of one term* have dominators that are
  approximants of `fst p`, hence compatible by `dir`, hence joinable.  So
  the join becomes conditional on provenance, and every consumer of a
  lookup has to carry "these two shapes come from one term" — which is
  true at `appDF` and `trDF`, but has to be re-established at each use,
  and the shape-level `HasType.join` stays false.  Minimal diff, maximal
  ongoing tax.

* **(β) second component as a graph.**  Passes the test outright, and
  this is the reason to prefer it.  Write a pair as `pair ty tm x g` with
  `g` a graph from first-component approximants to second-component
  approximants.  Then `y` and `z` above are
  `pair ty tm ⊥ [(zero, b₁)]` and `pair ty tm ⊥ [(succ ⊥, b₂)]`, their
  join is `pair ty tm ⊥ [(zero, b₁), (succ ⊥, b₂)]`, and it is typed —
  each entry keeps *its own* code.  No input has to serve both, because
  the shape now records both conditional facts.  Downward closure is free
  for the same reason: shrinking `x` cannot invalidate a fact that was
  always conditional on the input it names.

**(β) in its precise form: make a Σ-value mirror a λ-value.**  A pair is a
first component and a graph; `Shape.LE` at `pair` is label equality, `≤`
on the first component and *lookup coverage* on the graph; `join` appends;
and `HasType.pair` is `HasType.lam` verbatim, with the Σ's codomain graph
in place of the Π's — a generator `g₀` covering `g`, each generator entry's
code a lookup in `f` at that entry's own input, each generator output typed
at its code.  The consequences are exactly the ones the λ clause was
engineered for in §5.2 and §5.5:

* **`HasType.join` becomes provable**, for Π and Σ alike: two λ-shapes (or
  pair shapes) typed at one type join by appending graphs and
  concatenating generators, since both generators' codes are lookups in
  the *same* codomain graph.  That unblocks `SoundJoin`, hence `appDF`,
  `trDF` and every other lookup consumer.
* **`mono_l` stays provable**, by the generator argument that already
  works at `lam`; the dominator disappears.
* **Reflection along `lift` is preserved** — this is why the clause must
  use a generator *list* and not a dominating graph, as §5.5 records.
* **Σ's η becomes Π's η**: lookup coverage, the thing §5.2 bought and has
  already paid for.
* **`snd`'s type works**: the code sits at the entry's own input, which is
  an approximant of `fst p`, which is what `Interp.inst` wants.

What (β) does *not* remove is the label invariant of §4.7a — a Σ-typed
value's label has to name its own first projection — needed for `snd`'s
type and for η.  That is the Σ twin of §5.3's `HasDom` and is unavoidable
in any design (no type-level condition can pin a term-level name; §4.7a
checks this against intgrah).  The gain is that it is no longer entangled
with the join.

**Fallback, if (β) is too much surgery: (δ) master's typing.**  Master has
product pairs, reads the code at the component (`b.app x`), and proves
`HasType.join` — because its typing is *not* lower-closed, which is
exactly the hypothesis that forces our dominator.  Reverting to master's
`InterpTyped` (`∃ m' ≥ m`, typed) would restore the join at the price of
restating `SoundTy` and `Adm` and touching every consumer.  It is
known-good, since master is a complete proof, but it gives up what
lower-closure bought here (`Eval.lower` free, `LE.wf`, `SoundTy` typing
the approximant itself).

**Recommendation: (β).**  It is the only option that passes §5.5's test at
the shape level, it deletes machinery rather than adding it, and it makes
the Σ half of the development a second instance of the Π half instead of a
parallel one.  Estimated surgery: `ShapeS.pair`'s signature and the
order/`WF`/`Compat`/`join`/`subst`/`lift` clauses, `HasType.pair`,
`Interp.pair`/`fst`/`snd`, and the Σ proofs (`sound_fst`, the β-rules,
`dir_pair`/`fst`/`snd`, `pair_ub`/`pair_decomp`).

**Done**, and the estimate was right.  What it bought, beyond the join:
`sndDF`'s `SoundTy` (§4.7b — the dominator was the obstruction, and it is
gone), `appDF`'s `SoundTy`, and `trDF`'s directedness.  What it did not
buy: `fst_snd`, which needs §4.7a's label invariant, i.e. §5.3.

Three ways out, and the third is the one §5.3 was already heading for:

  (α) **restrict the pair order** so the second component lives in the
      fibre over the first;
  (β) **index the second component by the first**, i.e. make a pair's
      second half a one-entry graph and inherit λ's machinery verbatim;
  (γ) **strengthen `SoundTy` at Σ (and Π) types** — a typed approximant of
      a Σ-typed term is a pair whose label is the first projection and
      whose dominator is an approximant of it; then two such, being
      approximants of one term, have compatible dominators by `dir`.  This
      is §5.3(a) and §4.7a's Σ twin, and it is also what `sndDF` and both
      η rules need.  One decision covers `sndDF`, `SoundJoin`, `appDF`,
      `trDF` and η.

Original text follows.

Needed by `dir` for `tr` only.  In upper-bound form it is the elementary
shadow of `rawExtend_isDirected`.  Its Σ case fails at the shape level
because two compatible pairs can carry incompatible dominating first
components.  Options:

(a) prove `SoundJoin Γ A` alongside `sound`, one case per type former,
    using at the Σ case that the dominators are approximants of the *same*
    term (the pair's first component) and so compatible by `dir` — this
    needs the pair's *typing* to remember where its dominator came from,
    i.e. the same strengthening of `InterpTyped` as §4.5(a), for Σ;
(b) change `Interp.tr` to push a typed upper bound rather than demand
    `HasType m' cb` of the join — i.e. make `tr`'s value the *saturation*
    `{m ∣ ∃ m' ≥ m typed at some approximant cb}` outright, which is his
    `rawExtend`; then `dir` for `tr` needs only `dir X`, `dir C`, and the
    `HasType m'' cb` obligation becomes "there is a typed shape above" —
    still `SoundJoin`.  So (b) does not remove it, only relocates it;
(c) restate the `pair` typing clause so dominators are canonical.  No
    formulation found that is both downward closed and join-friendly
    (§ the `SoundJoin` doc comment records the attempts).

(a) is the honest one and fits the pattern; it makes the Σ half of the
development carry its own directedness, as his Π half does.

### 5.2 The graph order: lookup coverage, and what it cost

**Implemented; the order is lookup coverage.**  Entry coverage

```lean
def ShapeFun.LE Γ R f f' := ∀ e ∈ f, ∃ e' ∈ f', LabelEq Γ e'.ty e'.tm e.ty e.tm ∧
  R e'.inp e.inp ∧ R e.out e'.out
```

cannot express η →: an entry of an η-expansion's graph has as its output a
*join* of several outputs of the function's graph, and no single entry
need dominate a join.  Master escapes because its graphs are saturated, so
a join of matching outputs *is* an entry; the other repo because a λ-value
is an ideal, closed under every graph valid for its action.  Levels *and*
non-saturated graphs is our combination alone, and it needs the lookup.

**(a) It is spelled with `Evaluates`, moved.**  `Evaluates` was in
`HasType.lean` and defined using `Shape.LE`, but the dependency descends a
level — `Shape.LE` at `n+1` needs the lookup at `n`, which needs
`Shape.LE` at `n` — so the lookup is given in `Shape.lean`, parameterised
by the order one level down:

```lean
inductive ShapeFun.Eval (Δ) {n} (R : Shape n → Shape n → Prop)
    (f : ShapeFun n) (A a : Term) (x : Shape n) : Shape n → Prop
  | bot   : Eval .bot
  | entry (e) : e ∈ f → LabelEq Δ e.ty e.tm A a → R e.inp x → Eval e.out
  | lower {y z} : R y z → Eval z → Eval y
  | join  {y z} : Shape.Compat Δ y z → Eval y → Eval z → Eval (y.join z)
```

`HasType.lean`'s `Evaluates` is now this at `R := Shape.LE Δ`, a
`@[reducible] def` with `@[match_pattern]` constructor aliases, so every
existing `Evaluates` proof reads unchanged.  `Shape.join` moved above the
order section; `Compat` and `WF` do not depend on `LE`, so nothing else
moved.

**(b) The reflection along `lift` does go through.**  The earlier verdict
here was wrong.  `Shape.lift_le_lift` — `LE (s.lift m) (t.lift m) ↔ LE s
t`, the content of `TShape.LE.def` — is proved, by the motive `∃ c,
LE c' (c.lift k) ∧ Eval f A a x c` (`Eval.lift_of`).  Three things make it
work, and each is a change to a definition rather than to a proof:

1. **`join` carries `Compat`.**  The `join` case wants `c₁.lift ⊔ c₂.lift`
   to be an upper bound of the two reflected values, which is `le_join`,
   which needs `Compat` and `WF` of the two.  `Eval.compat` supplies the
   first (any two values of one lookup are compatible, given a coherent
   graph and a coherent query) and `Eval.wf` the second.  Both hold
   *because* of the side condition, which is why it is on the rule.
2. **`ShapeFun.LE` carries the well-formedness of both graphs.**  This is
   the move that was missing.  `Eval.lift_of` wants the covering graph
   well formed and coherent; those cannot be hypotheses of `lift_le_lift`
   (see 3), but they need not be, because the order on graphs asks for
   them outright and `lift_le_lift`'s own hypothesis then supplies them.
   The conjunct is not decoration elsewhere either: `∀ e ∈ f, Eval f'
   e.ty e.tm e.inp e.out` says nothing whatever about an entry whose
   output is `⊥`, since `Eval.bot` discharges it.  `ShapeFun.WF` absorbed
   the graph's self-coherence at the same time, so `Shape.WF`'s
   `forallE`/`sigma`/`lam` clauses lost their trailing `Compat` conjunct
   and every projection into them was unchanged.
3. **`WF` never lands on an upper bound.**  The old objection was that
   `Interp.mono` and the `Interp` constructors' `hle` premises apply the
   order to shapes with no `WF`.  That is true and harmless: the order
   demands `WF` only of graphs and of its *lower* bound.  `Shape.LE.wf`
   now states this outright — `LE Γ x y → WF Γ x` — and it is what lets
   `Eval`'s `lower` rule drop its own `WF` side condition.  It cannot be
   had for `y`: `⊥` is below everything, well formed or not, and has to
   be, or `Interp.le_id` could not invert the `bot` rule without knowing
   its label is typed.

**Preservation and reflection are separate lemmas.**  Only reflection
needs `⊢ Γ` (through `Eval.compat` and `le_join`), and reflection is the
minority use — a `TShape.LE` is read at a higher level far more often than
it is built from one.  So `Shape.lift_le` (preservation, hypothesis-free)
sits beside `Shape.lift_le_lift` (the iff, with `⊢ Γ`), and
`TShape.LE.def_mp` beside `TShape.LE.def`.  Of the 46 `LE.def` sites, 31
were preservation.  Keeping preservation free is what stops `⊢ Δ` from
spreading to every site that mentions the order, `Interp.sort'` among
them.  A further group needed neither: at the canonical level `max a.1
b.1` a `TShape.LE` *is* the shape order definitionally, so `LE.refl`,
`bot_le`, `LE.T` and `bot_le'` are a `show` and a rewrite.

**What it cost.**  A resequencing of `Shape.lean` (the substitution and
compatibility block, 613 lines, above `Shape.join_le`); `Compat.anti_right`
rewritten as an induction over the lookup, with its graph argument factored
out as `ShapeFun.Compat.anti_right_of` (it had been written out three
times); and `ShapeFun.Compat.of_common_upper` built from that rather than
by wrapping graphs in `.lam`, which the λ non-degeneracy conjunct no longer
permits.  `Shape.join_le` came out *without* a context hypothesis, as its
comment always claimed it should.

**What it buys.**  η → as described in §4.5, and with it `fst_snd`; and
`Evaluates.mono_graph'` became exact — the transport is `Eval.trans` on
the nose, so the dominating witness is the shape itself — losing two
hypotheses in the process.

### 5.3 Lower-closed `HasType` vs `HasDom` in the λ clause

Superseded in part by §5.5: lower closure is not available at the shape
level at all.  What follows is the reasoning as it stood.

Decided in favour of lower closure this session, and §4.5 shows the cost
is exactly one thing: typedness of inputs of approximants of Π-typed
terms, which master reads off the shape and we must carry semantically
(§4.5(a)).  Worth recording that the alternative — master's non-closed
`HasType`, closure by `InterpTyped` at use sites, `HasDom` in the clause,
`sound_forallE` by saturation rather than `mono_l` — is a coherent design
too, and `lift_iff` reflection is the thing it lacks (`Evaluates.lower`
producing witnesses outside the image of `lift`).  If (a) proves awkward
that is the fallback.

### 5.4 The Π typing clause at `type`

§4.5e of the plan: his `IsCode true (piGenerator …)` is unconditional;
ours inspects the codomain.  With `mono_r` now `lower`-based this weakening
is available and would make `SoundTy` for `forallEDF` at `type` free.  Not
needed for anything above; a simplification to take when convenient.

### 5.5 `mono_l` at `lam`: lower-closure of typing is semantic

The one thing lookup coverage breaks, and it is not a gap in a proof but a
false statement.

`Shape.HasType.mono_l` at `.lam` has to turn a typing of `.lam g` into one
of `.lam g'` for `g' ≤ g`.  The clause is stated per entry,

```lean
| lam : ShapeFun.HasPi T d f .type →
    (∀ e ∈ g, ∃ c, WF c ∧ Evaluates Δ f e.ty e.tm e.inp c ∧ T e.out c) → …
```

so for `e ∈ g'` one must walk the lookup derivation `Eval g e.ty e.tm
e.inp e.out`.  `bot` and `entry` are immediate and `lower` is the
induction hypothesis, but `join` asks for

```
T y c₁ → T z c₂ → Compat y z → T (y ⊔ z) (c₁ ⊔ c₂)
```

at an *arbitrary* type, and that is false — for the reason §5.1 gives for
`SoundJoin`, made concrete:

> Let `f` be a Σ codomain graph with entries at `.zero ↦ c₁` and
> `.succ ⊥ ↦ c₂`, and let `y = .pair ty tm ⊥ b₁`, `z = .pair ty tm ⊥ b₂`
> with `b₁ : c₁`, `b₂ : c₂` both non-`⊥` and compatible.  Each pair is
> typed at `.sigma A B .nat f`, with dominators `.zero` and `.succ ⊥`.
> They are compatible (their first components are both `⊥`).  Their join
> `.pair ty tm ⊥ (b₁ ⊔ b₂)` is typed at that Σ only if some single input
> `x₀` has `Eval f ty tm x₀ c` with `b₁ ⊔ b₂ : c`, and no numeral is above
> both `.zero` and `.succ ⊥`.

Put a `g` with two entries carrying those outputs at compatible inputs and
a `g'` with the single joined entry above them: `g' ≤ g`, both well
formed, `.lam g` typed, `.lam g'` not.  So `mono_l` is false as stated.

The three repairs that suggest themselves all fail:

* *Prove the element-level join.*  It is the statement just shown false.
* *Make `HasType` join-closed by a constructor.*  It would type
  `.pair ty tm ⊥ (b₁ ⊔ b₂)` at the Σ, which is not what the domain model
  says: the two pairs approximate different values and a shape does not
  record which.  `HasType` would over-approximate, and `proofIrrel` and
  adequacy are downstream of it being tight.
* *Drop the dominator from the `pair` clause* and type the second
  component at the lookup at the pair's own first component.  Then joins
  work (`mono_input` puts both codomain values at `a₁ ⊔ a₂`) but downward
  closure fails, which is what the dominator was for.  Downward closure
  and join closure are genuinely in conflict for dependent pairs at the
  shape level; that conflict is the content of §5.1.

**A dominating graph does not work either.**  The obvious repair is to
give the `lam` clause a dominating graph, as `pair` has a dominating first
component:

```lean
| lam : ShapeFun.HasPi T d f .type →
    (∃ g₀, ShapeFun.LE Δ (Shape.LE Δ) (Shape.WF Δ) g g₀ ∧
       ∀ e ∈ g₀, ∃ c, WF c ∧ Evaluates Δ f e.ty e.tm e.inp c ∧ T e.out c) → …
```

`mono_l` at `lam` is then transitivity of `ShapeFun.LE` and nothing else.
But the clause then does not **reflect along `lift`**, and this repo
already knows it — the note above `Evaluates.lift` in `HasType.lean`, left
from when `HasDom` was removed, says exactly this: *"the `lam` clause's
dominating graph at the level above need not be a lift."*

That is the dilemma, and it is sharp:

* **Reflection** (`Shape.HasType.lift_iff`'s `→`) works clause by clause
  because every object the per-entry clause mentions is a lift: the entry
  is `e.lift`, its output is `e.out.lift`, and `ihcode` reflects the
  codomain witness with `Evaluates.lift_of` and then reflects the typing
  with the level-`n` induction hypothesis, *both of whose sides are
  lifts*.  Any clause whose witness is an arbitrary object at the higher
  level — a dominating graph, or a list of pieces the output is below the
  join of — loses this, because there is nothing to pull the witness back
  along.
* **Downward closure** (`mono_l`) needs precisely such a witness, since
  the entry outputs of `g' ≤ g` are joins.

Per entry: reflects, does not close.  Dominating: closes, does not
reflect.  There is no third form.

Nor can the reflection be dodged by re-reading the level index.
`TShape.HasType` is `Shape.HasType` at the canonical level `max m.1 a.1`,
and reflection is what `TShape.HasType.mono_l` and `mono_r` are built on
(lift both sides to a common level, work there, come back).  Reading
`TShape.HasType` as "*at every* level above the canonical one" removes the
reflection from `.def` and from `.T`'s `←`, but not from `mono_l`: `m` may
sit at a higher level than both `m'` and `a`, so the hypothesis is
available only above `m.1` and the conclusion is wanted at `max m'.1 a.1`.
Reading it as "*at some* level" fixes `mono_l` and breaks `.T`'s `→`
instead.  (What is worth keeping from that exercise is `Shape.HasType.lift`
— preservation, hypothesis-free — which is now proved.)

**The counterexample is semantically spurious, and that is the point.**
`Shape.Compat` on pairs demands `LabelEq Δ ty tm ty' tm'`, so the two
pairs in it carry definitionally equal labels: they approximate *the same
term*.  Their dominating first components are therefore approximants of
the same first projection, and are compatible by `dir` — `.zero` and
`.succ ⊥` never both occur.  The configuration that breaks `mono_l` cannot
arise in the image of `Interp`; the shape level simply cannot see that,
because a shape records the term it approximates only in its labels and
`HasType` does not read them.

So the conclusion is the same one §5.1 reaches for `SoundJoin`, arrived at
from the other side:

> **Lower-closure of typing is not a shape-level fact.**  Like
> join-closure, it holds only of approximants of a term, and the reason is
> the same: a dominating existential is compatible with another only
> through the term both dominate.

§5.3 recorded lower closure as decided and named master's design as the
fallback "if (a) proves awkward".  It is not awkward, it is unavailable,
so the fallback is now the live option.  Three ways forward:

  (a) **Semantic lower-closure.**  Keep the per-entry `lam` clause; drop
      `Shape.HasType.mono_l` at `lam`; replace the uses of
      `TShape.HasType.mono_l` by a lemma proved alongside `sound`, where
      `dir` is available.  Its three uses are `SoundTy.hasType` — whose
      type is a *sort*, and `mono_l` at a sort never reaches the `lam`
      clause, so that one survives as a shape-level lemma — and two level
      adjustments in `sound_forallE_ub`.  This is the smallest change and
      it keeps §5.3's decision, semantically.
  (b) **Master's design.**  `HasType` not lower-closed, `HasDom` back in
      the `lam` clause, closure applied by `InterpTyped` at use sites.
      Coherent, and it is what master does; it gives up `Evaluates.lift_iff`
      reflection for `HasDom`, which is why it was dropped here.
  (c) **Drop joins from the order.**  `ShapeFun.LE` through a join-free
      lookup (`bot`/`entry`/`lower`) makes the per-entry clause downward
      closed outright — the offending case disappears — at the cost of η →,
      which is the whole reason for lookup coverage (§5.2).  Only worth it
      if η can be had another way.

  (d) **Define typing as one inductive over `TShape`.**  Obligation 2
      exists only because `Shape.HasType` is defined *by recursion on the
      level*, so a typing at level `k` has to be walked back to level `n`.
      An inductive over `TShape` has no per-level definition to walk back,
      and the dominating graph may then live at *any* level, because
      `TShape.LE Δ ⟨n+1, .lam g⟩ ⟨n₀+1, .lam g₀⟩` is already
      level-independent (§5.2).  Candidate (B)'s only defect vanishes and
      its virtue survives.

(d) is the way out, and two things about it have been checked in Lean
(`DomainSemantics/HasType.lean`):

* **Strict positivity holds.**  Every recursive occurrence is a premise
  under `∀`/`→`, never to the left of an arrow into itself.
* **A different kernel restriction bites, and is dodgeable.**  Writing the
  codomain witness as `∃ c, … ∧ THasType …` makes `THasType` a *nested*
  occurrence inside `Exists`, and the kernel refuses: *"invalid nested
  inductive datatype 'Exists', nested inductive datatypes parameters
  cannot contain local variables"* — `Exists`'s type parameter is
  `Shape n'`, which mentions a local.  Hoisting the witness into a
  function argument `cs : Entry (Shape n₀) → Shape n'` and splitting the
  conjunction into separate premises is accepted.  (The present
  `HasTypeS` gets away with `∃ c, …` because there the recursive slot is
  the *parameter* `T`, not the inductive being defined.)

It is now in the tree: `TShape.HasTypeOld` is the old definition, renamed
and untouched, and `TShape.HasType` is the inductive.  Every clause names
a **generator** and asks the shape to be below it, and a **co-generator**
and asks the type to be above it, so `mono_l` *and* `mono_r` are both
transitivity of `TShape.LE` and neither is a rule.  Being above the
co-generator does not by itself make the type a type — a `forallE` above a
`forallE` may have an untyped codomain graph — so the clauses whose type
is not a sort carry `HasType Δ a TShape.type` outright, which is also what
`isType` reads off them; the sort-typed clauses must not carry it, or
`sort` would regress, and they do not need to, because a sort is rigid
(`TShape.LE.sort_symm`).  Proved: `isType`, `mono_l`, `mono_r`, `wf`,
`bot_r`, `lift_subject`/`unlift_subject`.

The shape of `mono_l` at `lam`:

```lean
| lam cs hd hf hwc hev hty hg hc hA _ _ _ _ =>
  exact fun h => .lam cs hd hf hwc hev hty (h.trans hΔ hg) hc hA
```

What replaces obligation 2 is **lift-invariance of the relation**:
`⟨n, m⟩` and `⟨k, m.lift k⟩` are distinct `TShape`s denoting the same
value, so `THasType` must not separate them.  Preservation is an induction
on the derivation (re-apply the same constructor with the entries' TShapes
lifted); reflection should be too, since the dominating graph is reused
unchanged and `TShape.LE` is already lift-invariant — and if it is not, it
can be a constructor, which the kernel also accepts and which is
semantically valid, levels being bookkeeping and `lift` an embedding.

The shape of the refactor: the semantic layer moves to `TShape` wholesale.
Order, `WF`, `Compat` and `join` are level-independent already; the lookup
becomes an inductive `TEval` over `TShape` with the same four rules,
level-independent by construction instead of by `Evaluates.lift_iff`; and
typing becomes `THasType`.  `Shape n` is then only the carrier and the
`lift` lemmas are bridges used once.  `Shape.HasType.lift_iff` and the
whole `TShape.HasType.def`/`T`/`sort_T` wrapper layer go.  Not yet
checked: `proofIrrel`, `Inversion.lean`, and whether `ShapeFun.HasPi` stays
transparent enough for the positivity checker when it is not inlined.

Note `mono_r_join`'s induction on the level survives unchanged, because a
*type* is never a λ, so the clause whose premises escape the level never
arises there.  (a) remains the smaller change if (d) proves too large.

### 5.5a `TShape.HasType`, as built

The inductive is in `HasType.lean`; `TShape.HasTypeOld` is the old
definition, renamed and left for reference.  Every clause **pins the shape
of its subject and leaves the contents free**: `.succ v'` below `.succ v`
is the `succ` clause again at `v'`, a λ below `.lam g` is the `lam` clause
again at its own graph, a pair below `.pair ty tm x y` is the `pair` clause
again at its own first component `x'` with `x` kept as the dominator the
code is read at.  Everything strictly below a shape and not of its head is
`⊥`, and the `bot` clause takes that.  The **type** is pinned too, at
`lam` and `pair`: the clause names the Π, resp. the Σ, outright, and
`mono_r` moves to a bigger one rather than the clause carrying a bound.
`id`, `refl`, `pair`, `lam`, `forallE` and `sigma` pay for pinning with a
`Shape.WF` premise; `succ` does not, since `IsNumeral` implies it.  Only
`lam` and `pair` keep a generator, which is §5.5's point.

**Sorry-free**: `isType`, `mono_l`, `mono_r`, `wf` (subject *and* type),
`lift_subject` and `lower_subject`, `sort_level`, `cumul`, `subst`,
`join_sort`, `forallE_inv`/`sigma_inv`, `Eval.tHasType`, `mono_l_sort_T`
and `mono_l_sort`.

Three things the kernel or the level index forced, worth not rediscovering:

* a premise may not existentially quantify the witness: an `∃` nests the
  inductive inside `Exists`, whose parameters may not mention locals.  The
  witness therefore has to be a **parameter of the clause**.  Taking it as
  a *function* `cs : Entry (Shape n₀) → TShape` typechecks but does not
  substitute — reindexing along `τ` gives `cs (e.subst τ) |>.subst τ`
  where `(cs e).subst τ` is wanted.  Taking it as a **list of pairs**
  `g₀ : List (Entry (Shape n₀) × TShape)` does, because a list is
  reindexed by `List.map`.  That is the whole of `HasType.subst`.
* the constructors spell `ShapeFun.THasPi` out: the kernel will not take
  the inductive being declared as an argument to a definition.
* `Shape.sort` at a *variable* level is a stuck `match`, so it does not
  unify with itself.  Any `cases` on a derivation whose type index is a
  sort needs that index to be a variable — hence `forallE_inv`/`sigma_inv`
  and the `a.2 = Shape.sort j` idiom throughout (`sort_level`, `cumul`).

**How `mono_l` closed.**  The hard cases were `forallE` and `sigma`: a
smaller Π is `.forallE A' B' d' f'`, and typing its entry outputs is
`Eval.tHasType` over the lookup in `f`, whose `lower` case wants general
lowering at a sort — `mono_l` itself.  `mono_l_sort_T` already has it *at
one fixed level*, by induction on the level, and that induction is sound
precisely because at a sort the `lam` and `pair` clauses never arise, so
the existential `n₀` that motivated the inductive never appears.  What was
missing was only the bridge from one level to two:

```lean
lower_subject : HasType Δ (y.lift k).T a → HasType Δ y.T a
```

the reflection direction of `lift_subject`, and exactly what §5.5 shows
the *level-indexed* definition cannot have.  It holds here because every
object a clause quantifies over — `g₀`, the pair's `x` and `c` — is a
`TShape`, so `lift` touches none of them; what is left is entrywise, and
`TEvaluates.lower_cover` does it.  Then

```lean
mono_l_sort := lift_subject, then mono_l_sort_T, then lower_subject
```

and `mono_l` at `forallE`/`sigma` is one line each.  (The `Q'` plan in an
earlier draft of this section — generalising `mono_l_sort_T` to take the
smaller side as a `TShape` — is not needed: it is `mono_l_sort`, obtained
by transport rather than by redoing the induction.)

**The transport lemmas.**  Pinning the shapes moves work onto `TEvaluates`,
which is level-free and therefore where the level bookkeeping can be done
once:

| lemma | what it does |
|---|---|
| `mono_inp` | grow the input alone |
| `label` | move the query label along a defeq |
| `refl` | a graph covers itself |
| `trans` | a lookup in a covered graph is one in the coverer |
| `lift_cover` / `lower_cover` | coverage survives lifting the graph, and comes back |
| `of_cover_lift` | a graph whose *lift* is covered, covered at its own level |
| `subst` | transport along a typed substitution |
| `Eval.toT` | the level-indexed lookup is this one, at a fixed level |

`mono_l` at `lam` reads the order at a level above both and brings the
coverage down with `of_cover_lift`; `mono_r` at `lam`/`pair` moves the
codomain witnesses into the bigger Π/Σ's graph with `trans`.

**Migrated.**  `Interp`'s clauses, `Adm`, `InterpTyped`, `SoundTy` and
everything `IsDefEq.sound` runs through now use the inductive.  The old
`Shape.HasType` / `TShape.HasTypeOld` family stays in `HasType.lean` for
reference and is used by nothing else, so the false `mono_l` at `lam` is
out of the soundness chain; what `sorry`s remain there are the genuinely
open lemmas (`IsDefEq.stage`, `Interp.unweak`/`substTerm`/`inst`, the
open cases of `IsDefEq.dir`/`sound`, `Inversion.lean`).

Two proofs collapsed on the way.  `Interp.eq_bot_of_prop` read every
hypothesis at a common level, applied `Shape.HasType.proofIrrel` there and
transported the conclusion back down with `Shape.lift_eq_bot`; it is now
`le_prop_cases` and then `proofIrrel`, because both `mono_r` and the order
are level-free.  `sound_forallE_ub`'s joined domain needed two
lift-and-read steps and `Shape.HasType.join`; it is now `join_sort` on the
two premises.

`TShape.HasType.proofIrrel` itself is worth noting: the old proof inducted
on the *level*, since everything lived at one.  Over `TShape` it is an
induction on the **derivation**, and the `lam` clause's own hypothesis at
the codomain generator is the recursive call.  A dominating codomain
witness gives no such hypothesis, so this is the generator earning its
keep a second time (`subst` was the first).

**Deleted.**  The level-indexed relation is gone — `Shape.HasType0`,
`HasTypeS`, `HasType`, `TShape.HasTypeOld`, `ShapeFun.HasDom`/`HasPi` and
their 37 lemmas, 900 lines — and with it the only theorem in the file that
could not be proved.  §5.5's analysis stays as a short note in
`HasType.lean`, since the shape of the difficulty recurs: a level-indexed
relation must reflect along `lift`; reflection forces the `lam` clause to
be per entry; per entry it is not closed under the order.

**`InterpTyped` is gone too.**  `SoundTy` now says what it means — every
approximant of `t` is typed at an approximant of `A` — rather than "is
below one that is typed".  The saturating witness was forced by typing not
being a lower set; the two are equivalent once it is, so §2.3's
`InterpTyped` collapses into `SoundTy`'s body.  Every consumer got shorter
and two got stronger conclusions for free: `SoundTy.hasType` no longer
ends in a `mono_l`, and `Interp.eq_bot_of_prop` loses its `mono_r` as
well, since the type's typing lands on the approximant itself.  `Adm.cons`'s
saturation field went the same way and now reads "every approximant of `A`
is a type".

### 5.5b The `app` clause's label type: what the two other repos do

`Interp.app` names the argument's type as a free term of `Δ`:

```lean
| app {n} {g} {x y} {A : Term} :
  Interp Δ Γ F σ ρ (Shape.T (.lam g)) → Interp Δ Γ a σ ρ (Shape.T x) →
  Evaluates Δ g A (a.subst σ) x y → … → Interp Δ Γ (.app F a) σ ρ m
```

`A` has to be named, since `Term.app` does not record it, and nothing in
the clause pins it — it is existentially quantified per derivation.  So two
approximants of `.app F a` come from lookups at `(A₁, a[σ])` and
`(A₂, a[σ])`, and `IsDefEq.dir` has to produce *one* lookup above both.
`Evaluates.join` and `Evaluates.compat` are both stated at a single query,
so neither applies; relating `A₁` to `A₂` through the entries they matched
is uniqueness of the type of `a[σ]`.  §3.2's sketch overlooked this (it
says "the labels agree on the nose", which is true only of the term
halves), and §1's `sourceQuery` row drew the opposite conclusion.

**intgrah** (`/project/presheaf-semantics-lean`).  His query is not a
label but a *set* of them:

```lean
def sourceQuery (Γ : Ctx) (a : Term) : Set (Σ A : Ty Γ, Tm Γ A) :=
  {label | ∃ A u (hA : Γ ⊢ A : .sort u) (ha : Γ ⊢ a : A),
     Tm.pairOfTyping Γ.wf hA ha = label}

noncomputable def rawApplication (F : RawValue Γ) (Q : Set _) (X : RawValue Γ) :=
  ⨆ label ∈ Q, ΩLower.bind₂ F X (stepApplicationRaw label)
```

— all typings of `a`, supped over.  So the *definition* makes no choice.
But the sup is not directed on its own: `HasIdeality.app`
(`Soundness/EliminationRules.lean`) reads

```lean
theorem HasIdeality.app (hready : PiReady Γ A B) (ha : Γ ⊢ a : A)
    (hFI : HasIdeality Γ f) (hXI : HasIdeality Γ a)
    (hFF : HasFixedness Γ f (.forallE A B)) : HasIdeality Γ (.app f a)
```

and its proof first **collapses** the sup to the canonical label
(`PiReady.application_value`, via `rawApplication_eq_of_support`: every
other label's output atoms in `F` are `⊥`), and only then is ideality free.
`hFF` — the function's *typing* — is what supplies that.  `HasEquality.app`
does the same collapse on both sides and then observes the two labels are
the same element of the quotient `Tm Γ A`, by `Tm.pairOfTyping_eq` from
`Γ ⊢ a ≡ a' : A`.  This is why `HasIdeality` lives in `RawTermProperties`
next to `HasFixedness` and is proved in one induction: **his directedness
at `app` is not standalone either.**

**master** (`Sound.lean`).  `LE_Interp.app` carries no label at all —
`f.app a` is a *function* of the graph and the input, master's shapes
carrying no syntax — so this particular problem does not arise there, and
`StrongSoundCore` earns its keep elsewhere (`StrongSound.uniq`, semantic
uniqueness of types, used at `trans'`).

**Superseded (option 4 below, domain-only variant, is now built).**  The
first fix was a pinning lemma, `Interp.lam_entry_ty`: every entry of a
λ-shape approximating a term of type `Π A B` carries a label type
definitionally equal to `A[σ]`, so any `app` derivation could be
re-annotated at the canonical `A[σ]`.  It was proved (four
`TEvaluates.bot_or` links), but it needs `SoundTy` and `Adm`, and
directedness has to hold at the **non-admissible** valuations
`(ρ.subst τ).push (a.inp ⊔ b.inp)` of the λ/Π/Σ cross pairs, where typing
says nothing.  So pinning by typing cannot serve `dir`.

The fix is to store it: `Shape.lam A g` carries its **domain label** `A`,
`Shape.WF` requires `∀ e ∈ g, TyEq Γ e.ty A`, `LE`/`Compat` require the two
labels `TyEq`, `join` keeps the left one, `Interp.lam` emits `A[σ]` (and
lost its separate entry-type premise, now part of `WF`), and `Interp.app`
looks up at the λ-shape's own label instead of an existential `A`.  The
pinning then holds at every well-formed valuation.  `HasType.lam` gained
`TyEq Δ A₀ A` (label = Π's domain), which is intgrah's `Section`
condition stored rather than derived, and `Interp.lam_label_ty` is what is
left of the old lemma: at an admissible stage the label is the syntactic
domain `A[σ]` — a one-line projection.

Why a label and not master's domain *shape*: η.  Master proves η by
cutting `F`'s λ-shape into single-entry λs and rebuilding it; a domain
shape is an *approximant*, graded by stage, so the rebuilt λ would carry
`⟦A⟧σρ` where the slot `ρ(F)` carries an arbitrary smaller one.  A label
is not approximated — it is exact syntax up to defeq — so every piece
gets `A[σ]`, and typing the slot at `Π A B` forces its label to agree.
`pair` already works this way (it carries its first component's label).

**Why `uniq` does not do this job, and it is not the semantic/syntactic
gap.**  `StrongSound.uniq` yields `SoundEq Γ A B`.  In *this* design that
is not a weaker statement than the syntactic equation: `Inversion.lean`
extracts `Γ ⊢ A₀ ≡ A₁ : sort u` from `SoundEq` by probing with the type's
own label-only approximant and reading the label back off the order, which
is the point of carrying syntax in the shapes — so a `SoundEq`-level
inversion family is a restatement of what is already proved, and porting
master's `uniq` is *easier* here than on master, whose version needs
`SoundEq.forallE_inv`/`sigma_inv`/`id_inv` as separate semantic lemmas.

The obstruction is elsewhere: the clause's `A₁`, `A₂` are free terms of
`Δ`, not types of anything in a judgment the induction knows about.
Making them so — adding `Δ ⊢ a.subst σ : A` to the clause — needs
uniqueness of types for `a[σ]` *in `Δ`*, and that typing derivation is not
a sub-derivation of the one being inducted on.  Circular, for the third
time and by a third route.  `lam_entry_ty` does not reconcile `A₁` with
`A₂` at all; it re-annotates each to the canonical `A[σ]`, which is what
makes it non-circular.

So the score is: the only development in which `app`-directedness is free
is the one whose values carry no syntax, and it pays for that by having no
inversion principles (which is the whole reason for this branch).  Four
options, of which the last is ours alone:

1. **Make `dir` and `sound` mutual.**  What both other repos do, under
   different names (`RawTermProperties`+`RawJudgment`, `StrongSoundEq`).
   Costs §2.1's layering and a well-founded measure.
2. **Give `SoundDir` a typing hypothesis**, threading it from `sound`.
   Two inductions, but `SoundDir` stops being about `Interp` alone.
3. **Make the query a set**, as intgrah does: quantify `A` *inside* the
   `entry` rule (`Δ ⊢ e.tm ≡ a : e.ty`, the type supplied by the entry),
   so joins across entries with different types are fine.  This does not
   remove the typing obligation — intgrah's own `HasIdeality.app` shows it
   does not — but it *changes* it, from "reconcile two arbitrary choices"
   (uniqueness of types, unavailable) to "the other labels contribute `⊥`"
   (the Π's domain pins the graph, available from `SoundTy`).  Keep the
   labelled `Eval` for the *order*, where the type is needed for
   transitivity (`Label.lean`).
4. **[built, domain only: `.lam A g`]**
   **Carry the Π's label in the λ-shape**: `.lam A B g`, as `forallE` and
   `sigma` already do.  Then the query type is read off `F`'s own shape
   rather than guessed, and two λ-shapes of the same `F` have a common
   upper bound whose `LE` clause forces their labels definitionally equal —
   the `PiLabelEq` conjunct `forallE` already has.  `dir` at `app` then
   needs no typing input at all.  This option exists only because our
   values carry syntax, which is also what makes the inversion theorems of
   §6 corollaries of soundness; it is the only one that keeps §2.1 intact.

**How it turned out.**  (4) is built and it delivered what it promised:
`IsDefEq.dir` is complete and axiom-clean, `app` included, with no typing
input.  What it did not cover is `stage`, which needs the *term* half of
the query to move — and that took the clause premise of §3.1b, i.e. (a)
of §3.1, i.e. the obstruction relocated once more.  §3.1d is where it
came to rest: the premise is rebuildable in every direction but one, and
the original rebuilds nothing because it never hoisted the substitution
lemma out of the induction.  So of the four options here, (1) — make the
substitution half mutual with `sound`, which is what both originals do —
is the one still owed.

### 5.6 Summary of statement changes

| where | change | why | |
|---|---|---|---|
| `SoundDir` | `Adm` → `Valuation.WF`; upper-bound conclusion; separate lemma `IsDefEq.dir` by induction on typing | §2.3 | **done** |
| `IsDefEq.sound` | two conclusions, `SoundEq ∧ SoundTy` | §2.3 | **done** |
| `Interp.forallE/sigma/lam`, `Interp.tr` | `+ HasType d type` resp. `+ HasType cb type` | §2.4, §4.7 | **done** |
| `Interp.stage` → `IsDefEq.stage` | `Interp.stage`, structural in the term with `Term.Annot` | §3.1b–c | **done** (proved) |
| every label-forming clause | carries what makes it stage-invariant: the annotations' typings, and `Stable` at `app`/`snd` | §3.1b | **done** |
| `Term.Annot`, `IsDefEq.annot` | syntax-directed "the annotations are typed", for the inductions that cannot use a typing | §3.1c | **done** |
| `Interp.unweak` | indexed by `Term.Annot`, not by a typing | §3.4 | **done** (proved) |
| `Interp.subst_iff` → `Interp.substTerm` | directedness of the `θ i` as a hypothesis (`Interp.Dir`) | §3.3 | **done** modulo §3.1d |
| `Interp.inst` | takes `Interp.Dir` of the substituted term | §3.3 | **done** modulo §3.1d |
| `IsDefEq.uniq` | not assumed: `Stable.transfers` is gone, and uniqueness is a *corollary* of soundness (`Consequences.lean`) | §3.1d | **done** |
| `Adm.subst` | delete | §3.5 | **done** |
| `ShapeFun.LE` | lookup coverage, carrying `WF` of both graphs | §5.2 | **done** |
| `ShapeFun.Eval.lower` | drop the `WF` side condition (`Shape.LE.wf`) | §5.2 | **done** |
| `Shape.LE` | `WF` of the lower bound at `pair`/`lam`; `Shape.LE.wf` | §5.2 | **done** |
| `Shape.HasType.mono_l` | false at `lam` | §5.5 | superseded: the level-indexed relation is deleted |
| `TShape.HasType` | one inductive over `TShape`, every clause pinning its subject's shape | §5.5a | **done** (old kept as `HasTypeOld`) |
| `TShape.HasType.mono_l` | every clause, `forallE`/`sigma` by `mono_l_sort` | §5.5a | **done** |
| `Shape.HasType.lift` | preservation split off `lift_iff` | §5.5 | **done** |
| `InterpTyped` at Π (and Σ) types | witness carries lookup-form `HasDom` | §4.5(a), §5.1(a) | open |
| `SoundJoin` | `sound_join`, from the shape-level `TShape.HasType.join` | §5.1 | **done** (proved outright) |
| `IsDefEq.dir` | complete, `tr` included | §3.2 | **done**, axiom-clean |

`Interp.Dir Δ Γ t σ ρ` is the one-stage form of directedness, introduced
so that `substTerm`/`inst` can take it as a hypothesis; `SoundDir` is its
closure over well-formed stages and `Interp.Dir.join` is master's form.

The graph-order rows are done: §5.2 records how lookup coverage was made
to reflect along `lift`, which was the one thing standing between it and
η.  The `InterpTyped` row remains open and is a restructuring rather than
a restatement — it changes what `SoundTy` promises and so touches every
case that consumes it.


## 6. The shape domain, trimmed (2026-10-06)

With soundness closed, the question is whether the domain carries
anything the proof does not need.  Four pieces of data were removed, each
because no clause of `Interp`, `TShape.HasType`, `Shape.WF`, `Shape.LE`,
`Shape.Compat` or the canonicity predicates reads it.

(a) **The codomain label of `lam` and `pair`.**  A λ-shape carried
`(A, B)` and a pair carried `(A, B, a)`.  Every judgment mentioned the
domain `A` (a λ's entries are read at it, a pair's name is typed at it)
and none mentioned `B`: the `Interp` clauses took it as a free implicit,
and the Π that types a λ-shape carries its own codomain label anyway.
Deleted.

(b) **The witness of `refl`.**  `refl` wrapped a shape, read by nothing:
`HasType.refl` asked only that the witness be well formed, both
canonicity predicates are `True` on it, and no rule looks inside a proof
of an identity type.  The `tr` rule, which is the only consumer of such a
proof, asks for `H ≡ refl a` at the stage (§4.7j) rather than for a
`refl`-shaped approximant with a usable witness.  So `refl` is now
nullary, the `Interp` clause loses its premise on the subject, and
directedness for `refl` is the statement that two approximants of one
nullary shape have an upper bound.

(c) **The per-entry type.**  An `Entry` stored `(ty, tm)`, and every
place two entries were compared required `ty` to be the domain label of
the shape the graph sits in (`Shape.WF`'s last `lam` conjunct, and the
`Interp` premise `∀ e ∈ g, ∃ u, Δ ⊢ e.ty ≡ A[σ] : sort u` at `forallE`
and `sigma`).  The graph judgments now take that type as a parameter
(`ShapeFun.WF Δ T W f`, `ShapeFun.Compat R Δ T f f'`,
`ShapeFun.LE Δ R W T f f'`, `ShapeFun.Eval Δ R f A a x y` reading entries
at `A`), the per-entry conjuncts disappear, and moving a graph from one
label to a definitionally equal one is the `retype` family.  What this
costs is one `retype` at each point where two comparable shapes' labels
meet, which the order supplies; what it buys is that the "entry type
equals domain label" invariant is no longer something to carry, restate
and re-establish.  Note the type is still *stored* — one per graph rather
than one per entry — for the reason in `ShapeFun.LE.trans_of`:
composing coverage chains two label equalities, and a type-free label
would need uniqueness of types to do it.

Side effect: `Interp.unweak` is now `Classical.choice`-free, since the
`choose_spec` it used to type an entry's label is gone.

(d) Two lemmas with no remaining users, `TShape.LE.refl_ub` and
`TShape.LE.refl_decomp`, and one, `Interp.lam_entry_ty`, whose statement
no longer has a subject.  Deleted.

*How the rounds interact.*  Mostly they do not.  Of the hypotheses the
last round removed, exactly one died because of the trimming above
(`sound_refl`'s equation for the argument, which only ever moved the
witness inside a `refl`-shape, plus `dir_refl`'s own argument, dropped
with the clause at the time).  31 died in the `Adm.cons` cascade, and 21
were already slack before either round.  In the other direction the
`Interp` premises are unaffected: their blocker is the context lemmas'
need for `⊢ (A' :: Γ')`, which no amount of hypothesis pruning supplies.
The one real connection runs the other way, from §2 to the model:
`Interp.tr_stuck_bot` used to *assume* `zero ≢ succ zero`, with a comment
that this was soundness's business; `zero_ne_succ` now proves it, so the
lemma is unconditional and has moved downstream to `Inversion.lean`.

*Hypotheses.* 68 of them were declared and never used, and `lake build`
is now warning-free.  One was load-bearing in appearance only and paid
for the rest: `Adm.cons` asked that the type's approximants be types,
which admissibility has no clause to read, so it was a definitional
condition in lemma clothing supplied at 33 call sites.  Removing it
cascaded through four further waves, because most of those sites built
it out of a `SoundTy` that nothing else wanted.  The residue is one
pattern: a `sound_*` lemma taking a subterm's typing beside its
saturation and reading only the saturation, because the single uniform
call site in `IsDefEq.sound` has both to hand.  Singular cases worth
naming: `sound_refl` took an equation for the argument and proves its
conclusion without it, `dir_tr` took directedness of the transported
proof, Σ-η's forward direction took four, and `ShapeFun.WFE` took a
context its body never mentions.

Investigated and **kept**: thirteen premises of `Interp` are syntactic
typings of the clause's own labels at the *source* context
(`(∃ u, Γ ⊢ A : sort u)` on `lam`/`forallE`/`sigma`/`Y`/`id`/`tr`, and
the term typings on `id`/`tr`/`Y`).  Nothing downstream of `Interp` reads
them, and at first sight they are self-sustaining: their only consumers
are `Interp.ctx`, `Interp.weak'` and `Interp.of_substTerm`, each of which
destructures a premise and rebuilds it in the new context.  Removing them
does not work.  The rebuild is not the whole use: those three lemmas also
need `⊢ (A' :: Γ')` to apply the body's induction hypothesis, and this is
where it comes from.  `Shape.WF` carries the same typings at the *stage*
`Δ`, which is the wrong context, and the three lemmas deliberately take
no `Term.Annot` hypothesis (that is what makes them usable where no
annotation is in hand).  So the premises are the price of the context
lemmas being annotation-free.  The two analogous premises that *are* read
downstream, `pair`'s pair (by `dir_pair`) and `natCase`'s `Γ ⊢ M : nat`
(by `Interp.inst`), show the pattern was generalised one step past where
it was needed, but not more than that.

What is *not* removable, and why: the Π/Σ labels `(A, B)` and the `id`
label `(A, a, b)` are what the inversion theorems project out; the pair's
domain label types its name, which is what Σ's η reads; `unit`'s
relevance flag decides which sorts it inhabits; a λ's domain label is
read by `Interp.lam_label_ty` and pins the lookup at non-admissible
stages.

## 7. Canonicity folded into well-formedness (2026-10-07)

§4.7i above describes `CodeCanon` as a hereditary predicate of its own,
recursing through a Π- or Σ-code's domain and its codomain graph's
outputs. That recursion is gone. `Shape.WF` was already walking exactly
those shapes, so it now carries the *shallow* claim `Shape.CodeCanonS Γ T
s` — this head's own labels name `T` — at every Π and Σ node it descends
through: `CodeCanonS Γ A d` for the domain and one per entry output at
the instantiated codomain. For a well-formed shape the hereditary
reading is then `WF` plus the head equation and nothing more, so the deep
predicate was deleted and every use is the shallow one.

`Shape.LE` carries the same two conjuncts. It had to: `LE` already
carries `WF` of both sides by fiat (the label equalities, the graph's
`WF`, the λ clause's non-degeneracy), which is why `Shape.LE.wf` can
produce a `WF` from an order fact alone. Strengthening `WF` on its own
would make that lemma false, since the order cannot know what type a code
names; giving `LE` the conjuncts repairs it with no signature change.

What this bought, beyond deleting a recursion: the shallow theory is a
handful of lines (conversion, join, lift, downward inclusion,
substitution, two graph companions) because there is nothing to push
through, and the lemmas need less. `mono` no longer wants the bigger
shape's `WF`, `join` wants neither `WF` nor `Compat`, `CodeAt.of_top`
drops a `WF`, and `CodeAt.forallE`/`CodeAt.sigma` are one line each.

What it cost: `Shape.WF` is no longer purely structural, so a lemma that
*fabricates* a shape out of an arbitrary approximant must know that the
approximant names its type. Three do — `Interp.forallE_single`,
`Interp.sigma_single` and `SoundEq.sigma_dom` — and `SoundEq.forallE_cod`,
`sigma_cod` and `inst_cod` thread it up to `Strong.lean`, where soundness
supplies it.

Also in this round: `TShape.Dom` and `ValCanon` merged into
`TShape.Named` (hereditarily typed at a code *and* naming a term), whose
`Named.defeq` is the transport with the code's naming as its only extra
argument; and `CodeCanon`'s `⊥`-output exemption was dropped, having
always been implied by `CodeCanon` at `⊥` being `True`. §8 then removes
`TShape.Dom` itself.

## 8. Hereditary typing indexed by the name (2026-10-07)

§7 merged `ValCanon` into hereditary typing as `TShape.Named`, which left
two inductives over the same code recursion — `TShape.Dom` for the
index-free notion and `Named` for the named one — and a bridge between
them. This round collapses them into one.

The move is to make the name an **index** rather than an argument:

```
TShape.NamedO (Δ : List Term) : Option Term → TShape → TShape → Prop
TShape.Named Δ d t x := TShape.NamedO Δ (some t) d x
```

The `base` clause asks `∀ t ∈ o, Shape.CodeCanonS Δ t x.2`, which is
vacuous at `none`; the `pi` clause maps the index to `e.tm` on an entry's
input and `app t e.tm` on its output; the `sg` clause maps it to `fst t`
and `snd t` and asks the pair's label to be `fst t` only `∀ t ∈ o`. So at
`none` the relation is exactly the old `Dom`, at `some t` exactly the old
`Named`, and **one** inductive with **one** copy of each closure lemma
(`hasType`, `bot`, `subst`, `lift_subject`, `mono_r`, `sg_inv`, `join_at`,
`join`, `of_isType`, `of_not_binder`) serves both. `TShape.Dom` and its
eleven lemmas are deleted.

Three things had to be true for this to work, and each was a real step:

1. **`NamedO.reindex`** — weakening the index — must be proved by direct
   induction on `NamedO`, because `induction` refuses an inductive whose
   index is not a variable. This is also why the earlier attempt, defining
   `Dom := NamedO none` while keeping `Dom`'s own lemmas, could not be
   made to go: every one of them inducted at the fixed index `none`.
2. **`NamedO.shallow`**, the extraction `NamedO o d x → ∀ t ∈ o,
   CodeCanonS Δ t x.2`, has to live beside the inductive rather than in
   `Canon.lean`, because `join_at`'s `base` case needs the *other* side's
   shallow name in order to join the two with `CodeCanonS.join`.
3. **`mono_r` at a Σ** moves the name equation along the domain label:
   the target code's label is a different term, so the equation
   `p.1 ≡ fst t : A` has to be retyped at `A'` with the `LE`'s label
   equality. That is the only clause where the index does real work.

What it buys, beyond one inductive instead of two: `NamedO.of_isType` and
`NamedO.of_not_binder` land at `none` and so need no `CodeCanonS`
hypothesis, which was the cost §7 anticipated and which the indexing
avoids. `Interp` and `Presheaf` mention only `Named` and `Slot`; nothing
outside `HasType.lean` mentions the index-free case except through
`NamedO.dom`.

## 9. Well-formedness indexed by the name (2026-10-07)

§8 gave hereditary typing an `Option Term` index. `Shape.WF` gets the
same treatment, for the same reason: §7 folded canonicity into it by
bolting two conjuncts onto the Π and Σ clauses,

```
WF Γ (forallE A B d f) := … ∧ WF Γ d ∧ ShapeFun.WF Γ A (WF Γ) f ∧
  CodeCanonS Γ A d ∧ ∀ e ∈ f, CodeCanonS Γ (B.inst e.tm) e.out
```

and those two say exactly "the sub-shapes are well formed *at the labels
the node already names*". That is an index, not a conjunct:

```
WFO Γ o (forallE A B d f) := … ∧ WFO Γ (some A) d ∧
  ShapeFun.WF Γ A (some B) (WFO Γ) f ∧ TyEqO Γ o (forallE A B)
```

with `Shape.WF Γ s := Shape.WFO Γ none s`. `ShapeFun.WF` gains the
codomain as `oB : Option Term` and asks an entry's output to be well
formed at `oB.map (·.inst e.tm)` — `some (B.inst e.tm)` under a code,
`none` under a λ, whose outputs are values and name nothing.

Three things are worth recording.

**The index is read through `TyEqO`, not `∀ T ∈ o`.** `TyEqO Γ o T'`
matches on `o` and is `True` at `none`, so every clause *reduces* to the
structural one there and the hundreds of existing `trivial`s keep
working. With `∀ T ∈ o, …` they would all have become `nofun`. This is
the one place the `WF` refactor differs from the `NamedO` one, and it is
because `WF` is a definition that gets unfolded everywhere rather than an
inductive that gets `cases`d.

**`Shape.WFO.iff` is a `cases`, not an induction**, because the index is
read only at the head: `WFO Γ o s ↔ (∀ T ∈ o, CodeCanonS Γ T s) ∧ WF Γ s`.
It is choice-free, and it is what `WFO.wf`, `WFO.canon` and `WF.name`
(with the graph-level `ShapeFun.WF.forget`/`.canon`/`.name`) are built
from. Those six are the whole migration cost at the use sites.

**The order cannot be indexed, and that is not an oversight.** `Shape.LE`
relates shapes whose labels agree only up to definitional equality, so
`LE.trans` would need `ShapeFun.LE` at `some B₁` on the left and
`some B₃` on the right with `some B₂` in the middle — three different
terms. `ShapeFun.LE`'s well-formedness conjuncts therefore stay at
`none`, and `Shape.LE`'s Π/Σ clauses keep `CodeCanonS Γ A d` and
`∀ e ∈ f, CodeCanonS Γ (B.inst e.tm) e.out` written out. `LE.wf` is where
the two representations meet: it reads the conjuncts off the order and
hands them to `WF.name` and `ShapeFun.WF.name`.

`Shape.WFO.subst` replaces `Shape.WF.subst` as the real lemma (the index
substitutes with the shape, `TyEqO.subst`), `Shape.lift_wf` is now stated
at an arbitrary index, and `Shape.WF.subst` is the `none` instance of the
first, so no downstream call site changed.

### 9a. The index as a defaulted trailing argument

Both indices are the **last** argument and default to `none`:

```
Shape.WF (Γ : List Term) : ∀ {n}, Shape n → (o : Option Term := none) → Prop
TShape.Named (Δ : List Term) : TShape → TShape → (o : Option Term := none) → Prop
```

so `Shape.WF Δ s` and `Named Δ d x` *are* the index-free notions, written
exactly as before, and the named ones are `Shape.WF Δ s (some T)` and
`Named Δ d x (some t)`. The `Shape.WFO`/`Shape.WF` pair collapses to one
name and so does `NamedO`/`Named`; nothing is left standing in for a
`none` case, and the ~450 index-free `Shape.WF` sites did not change.

Lean accepts a defaulted trailing argument in an inductive's index
position as well as in a recursive `def`, which is what makes this work at
all. Two consequences are worth knowing:

* a partially applied `Shape.WF Γ` has the default *inserted*, so it
  elaborates at `Shape n → Prop`, not `Shape n → Option Term → Prop`.
  Where the predicate is passed to `ShapeFun.WF` the `@` form
  `(@Shape.WF Γ _)` is needed; where it is passed to the index-free
  `ShapeFun.WFE`, plain `Shape.WF Γ` is right.
* `Shape.WF.subst` now has conclusion index `o.map (·.subst τ)`, and its
  `none` instance needs no separate lemma: `o` is determined by the
  hypothesis, so `none.map _` is checked against `none` by reduction
  rather than by unification.

The last of the `Dom` vocabulary went with it: `Named.dom` is
`Named.forget` and `Named.of_dom` is `Named.name`, matching
`Shape.WF.forget`/`Shape.WF.name`. Those 270 references could not be
renamed textually, because `.dom` is also `Shape.WF.dom`,
`TShape.LE.pair_dom` and the `IsDefEq.*_dom` projections. They were
renamed by reading the resolved references out of Lake's `.ilean` files
(`references[<const>].usages` gives exact spans; the fifth field of a
usage is the *containing* declaration, not the referent) and rewriting
only those spans.

## 10. `CodeCanonS` removed (2026-10-07)

§7 made canonicity shallow, §9 made it `Shape.WF`'s index. This round
deletes the predicate.

The move is in two steps. First `Named`'s `base` clause: it asked
`∀ t ∈ o, CodeCanonS Δ t x.2` and now asks `Shape.WF Δ x.2 o`. That is
stronger, but the clause already carries `HasType Δ x d`, so the extra
content is free — and the bounded quantifier disappears from both the
premise and the extraction, which becomes

```
Named.wf : Named Δ d x o → Shape.WF Δ x.2 o
```

premise and conclusion the same proposition. Three proofs collapsed:
`subst`'s base case is `Shape.WF.subst hΘ W hc` where it was a `cases o`
with an `Option.map` normalisation, `lift_subject`'s is
`(Shape.lift_wf hk).2 hc`, and `join_at`'s is `Shape.WF.join_mem`.

Then every other statement: `CodeCanonS Δ T x` became `WF Δ x (some T)`
everywhere, including inside `Shape.LE`'s two canonicity conjuncts and
`Shape.ValCanon`'s code-shaped clauses. The sweep was scripted off the
resolved references in Lake's `.ilean` files, because the change is an
argument reorder rather than a rename and two textual attempts had
already gone wrong in ways a compiler check would not localise (one
rewrote the `def` header as an application, the other had the
`Shape.CodeCanonS` pass match the tail of `TShape.CodeCanonS`).

**What the splitting lemmas turn out to be.** `WF.iff`, `WF.canon`,
`WF.name` and `WF.named` existed to separate `WF`'s structural half from
its head half. Once the head half *is* a `WF` at an index, three of the
four are identities and the fourth, `iff`, is circular. Only
`WF.forget` — dropping the index — has content, and it is a `cases` on
the head. What replaces the others:

* `WF.mem` / `WF.named_of`, moving between an index and its `some` case,
  one `cases o` each;
* `WF.conv`, the name moving along a type equality, one `cases` on the
  head;
* `WF.mono_mem`, downward closure, which is `LE.wf` for every conjunct
  but the last and the label equalities for that one;
* `WF.join_of`, which takes the *structural* half of the join as a
  hypothesis because its two consumers reach it by different routes —
  `Shape.join_le` from `LE.wf` of the induction hypothesis, and
  `WF.join_mem` from the index-free `WF.join`. That asymmetry is the one
  place the old `CodeCanonS.join`, which needed no context and no
  compatibility, was doing real work.

`Shape.ValCanon` keeps its own recursion, but its code-shaped clauses now
read `Shape.WF Δ s (some t)`, so `ValCanon.toCode` gained a structural
`Shape.WF Δ s` hypothesis — at a `lam` or a `pair` the value's own
well-formedness does not follow from the naming, and that is what the
hypothesis supplies.

The axiom board loses `Shape.WF.iff`: the index is not a second notion,
so there is nothing for a faithfulness statement to say. `TShape.Named.iff`
stays, because `ValCanon` is still a notion of its own.


## 11. `ValCanon` removed, and `Canon.lean` with it (2026-10-07)

§8 made the name an index on hereditary typing and §10 made it an index on
well-formedness. `Shape.ValCanon` — "the value names its own projections"
— then had nothing left to say that `TShape.Named`'s index does not, and
this round removes it. `Canon.lean` is deleted: `TShape.WF.conv` moves to
`Shape.lean`, `TShape.Slot` and its two lemmas to `HasType.lean`, and the
build drops from 46 jobs to 45.

**The two lemmas that had to be reproved.** `Named.forget` and
`Named.defeq` went through `ValCanon`. `forget` is one induction dropping
the naming at every clause. `defeq` is stated with the index a *variable* —

```
Named Δ d x o → WF Δ d (some T) → (∀ t ∈ o, Δ ⊢ t ≡ t' : T)
  → Named Δ d x (o.map fun _ => t')
```

— which makes `induction h` legal, `none` going to `none` and `some t` to
`some t'`. Its three cases are the ones `ValCanon.defeq` had.

**What the call sites turned out to be.** Of the 137 `.name` sites, almost
all were a name forgotten and immediately re-added, sometimes ninety lines
apart or across a lemma boundary. The recurring shapes:

* `.name h.forget h.val` adjacent — 38 of them;
* a lemma that *receives* the named form and splits it on its first two
  lines (`sound_forallE_ub`, `sound_sigma_ub`, `sound_lam_ub`);
* a lemma that takes the two halves as separate parameters
  (`Interp.forallE_single`, `Interp.sigma_single`, `SoundEq.*_cod`,
  `Subst.Saturates.lift`);
* a bundle carrying them as separate conjuncts (`sound_lam_dom`'s
  `exists_pairs` predicate, `sound_app_dom`'s `key`);
* `cases h.forget` where `cases h` makes the clause's own premises arrive
  already named (`sound_app_dom`, `sound_fst_dom`, `sound_snd_dom`,
  `sound_eta_of`, `pair_eta`);
* a transport applied to the extracted half and then reglued, where the
  transport is index-general on `Named` itself (`lift_subject`, `join`,
  `mono_r`, `defeq`).

**Three things are worth recording.**

`Interp.unweak` is choice-free again. It had `Classical.choice` because
rebuilding a `Named` at a Σ moves the name along the pair label's `TyEq`,
whose witness is a `choose_spec`; carrying the named hypothesis through
instead of rebuilding it removes the `choose_spec`.

The collapses had to be **scoped to the branch**. The same names (`hxc`,
`hdx`, `hm'`) are rebound in sibling branches of one `cases`, while the
`hNV` they come from is rebound too, so a proof-level substitution silently
picks the wrong hypothesis. Eleven pairs sit in nested `cases` where the
inner pattern shadows the outer; those got their binders renamed apart.

`PairCanon.of_dom` is the one place the `ValCanon` formulation was
genuinely shorter. It stated the pair's name equation without reference to
a code; `Named` states it in the Σ clause, so getting it out means ruling
out the `base` and `pi` clauses from the subject being a pair, and moving
the equation from the code's domain label to the pair shape's.

**What was given up.** `TShape.Named.iff` — the faithfulness statement
that `Named` at `some t` is exactly hereditary typing together with
`ValCanon` — is gone, since one side of it no longer exists. It was on the
axiom board; the board is 25 guards now. The merge it certified is no
longer a merge of two notions, so there is nothing left for it to say, but
it did certify that the inductive neither strengthened nor weakened what it
replaced, and that certificate is not replaced by anything.

## 12. The development is choice-free (2026-10-07)

Every board entry now pins `[propext, Quot.sound]`; nothing in the library
uses `Classical.choice`. There were exactly two sources, and both were
avoidable rather than essential.

**`Exists.choose` on a hidden sort level.** `TyEq Δ A A' := ∃ u, Δ ⊢ A ≡ A'
: .sort u`, and 72 sites reached the equation as `h.choose_spec`. `choose`
*is* choice; `Exists.elim` into a `Prop` is not, and the existing `TyEq`
API was already written by pattern matching (`| ⟨u, h⟩ => …`) — the
`choose_spec` habit had simply spread alongside it. What the sites needed:

* 40 of them wanted `h.choose_spec.defeqDF`, whose conclusion does not
  mention the level, so one choice-free `TyEq.defeqDF` replaced all of
  them. For dot notation to find it, `PiLabelEq` and `IdLabelEq` now *say*
  `TyEq` where they spelled out `∃ u, …` longhand.
* 5 were `have hA := E.choose_spec`, i.e. `obtain ⟨_, hA⟩ := E`.
* 3 built a label equality back up (`IsDefEq.forallEDF₀ hΔ h.1.1.choose_spec
  h.1.2.choose_spec` wrapped in `⟨_, ·⟩`), which is `PiLabelEq.forallE`,
  `PiLabelEq.sigma` and `IdLabelEq.id` — each a one-line pattern match.
* 4 passed the pair `(hA, hAA', hBB')` to `ShapeFun.codeCanonS_append`,
  which now takes the `PiLabelEq` and destructures once.
* the rest were term-mode `let`/`.cons` applications, rewritten as `match`
  or a tactic `obtain`, plus a `TyEq.inst'` taking the codomain equation
  packaged.

**One classical case split.** `Named.mono_r` did `by_cases hb : d.2 =
Shape.bot`. Shapes carry `Term`s, so equality is not decidable and
`by_cases` fell back to `Classical.em`. `Shape.IsBot` *is* decidable
(`Shape.decIsBot`), and for a well-formed shape the two agree
(`Shape.WF.eq_bot_of_isBot`), so the split moves to `IsBot` — the other
four `by_cases` in the development were already on `IsBot`. That single
line was what kept soundness, `IsDefEq.iff`, Π-injectivity, type
uniqueness, subject reduction, progress and `not_UIP` all choice-dependent.

Worth noting what this does *not* mean. `Quot.sound` remains, and so does
`propext`; the claim is only that no choice principle is used. And the
result was free: nothing had to be reproved, only restated.

## 13. `Interp.Dir` eliminated; `Directed.lean` (2026-10-08)

There were two directedness notions: `SoundDir Γ t`, quantified over
stages, and `Interp.Dir Δ Γ t σ ρ`, its body at one stage, with `SoundDir`
defined as `∀ Δ σ ρ, … → Interp.Dir Δ Γ t σ ρ`. The second is gone.

`SoundDir` now spells the body out and lives in `Interp.lean` where
`Interp.Dir` was, with `SoundDir.join` taking it plus the stage data.

What made the split worth doing is a measurement rather than a
preference. The dependency closure of `IsDefEq.dir` contains 32
declarations of `Presheaf.lean` and, from the whole tail of `Interp.lean`,
only three: the definition, `.join`, and `Interp.lift`. So directedness
does not need the substitution machinery at all — the dependency ran the
other way. Those 32 now make `Directed.lean`, which imports `Interp` and
nothing else.

That inverts who owes whom. Ten theorems of `Interp.lean` took a
directedness premise (`Valuation.Approx.join`/`foldr`, `body_merge`,
`Saturates.lift`, `to_substTerm`, `substTerm`, `inst`, `Dir.list`, and the
two transport lemmas `Dir.bvar`/`Dir.weak_slot` that existed only to move
such a premise along a stage extension). None is needed by `IsDefEq.dir`,
so all ten move *after* it, into `Presheaf.lean`, and take a typing
instead:

* `Subst.Dir Γ' θ` is `∀ i, SoundDir Γ' (θ i)` — stage-free, so the
  recursion under a binder re-instantiates rather than transports.
  `Subst.Dir.one` builds it from `Γ ⊢ a : A` through `IsDefEq.dir`;
  `Subst.Dir.lift` carries it under a binder, and `SoundDir.weak` is what
  it rests on (the arbitrary stage on the extended context splits as a
  `cons`, and the slot's annotation moves the approximants down).
* `Interp.Dir.bvar` is subsumed by `dir_bvar`, which already states
  `SoundDir Γ (.bvar i)` with no hypothesis at all, the slot's
  well-formedness coming from `SoundDir`'s own `Valuation.WF`.
* `Interp.Dir.weak_slot` becomes `SoundDir.weak`, stated once on
  `SoundDir` instead of per stage extension. The seven `fun i => by cases
  i with | zero => Dir.bvar … | succ => Dir.weak_slot …` blocks inside
  `to_substTerm` collapse to `Subst.Dir.lift hΓ' (.skip .refl) hgood hθ`.
* `Interp.inst` loses its directedness premise outright: it already took
  `hat : Γ ⊢ a : A`, and `Γ ⊢ a : A` *is* `Γ ⊢ a ≡ a : A`, so
  `IsDefEq.dir` applies to it directly. Twenty call sites dropped an
  argument.
* `body_merge`'s `hθ'` — the lifted substitution's directedness at the
  extended stage, six lines — turned out to be dead already.

Two places keep a stage-specific statement, spelled out rather than named:
`dir_inst` and `sound_beta_lookup`'s premise. Both need `Interp.inst`,
which needs `Subst.Saturates`, which needs `Adm` at the stage, and
`SoundDir` offers only `Valuation.WF` at an arbitrary one. That is the
honest reason, and it is the whole residue.

### 13a. The `_ub`/`_dir` pairs merged

`sound_forallE_ub`, `sound_sigma_ub`, `sound_lam_ub` and `dir_pair_ub`
each had exactly one caller: their `_dir` partner. The split cost an
18-line hypothesis list and a 4-line conclusion apiece, and every one of
those hypotheses was a field the partner's `cases` had just produced,
restated under the same name. So the `_ub` statement carried no
information — it was the `cases` pattern written out twice.

Each body now sits in its `_dir`, with one change: the two `TShape.LE`
components of the `refine` are wrapped in `TShape.LE.trans hΔ hle₁/hle₂`,
which is exactly what the `exact` after the old call did. The levels and
graphs that were implicit binders of `_ub` are named in the `cases`
pattern instead (`| @forallE _ _ _ _ n₁ g₁ d₁ _ _ hA₁ …`, the four
leading holes being the inductive's auto-bound `Γ σ ρ m`).

One trap: `dir_pair_ub`'s body has its own `hle₁`/`hle₂`, a pair of
`Valuation.LE`s, so the bounds coming from the `cases` are `hlm₁`/`hlm₂`
there.

`TShape.LE.lam_ub`, `TShape.LE.pair_ub` and `TShape.LE.succ_ub` stay.
They are a different species — inversion of the order at a head, giving
back the upper bound's shape — and `pair_ub` has four callers across two
files.

### 13b. `SoundDir` sealed, and `Subst.Dir` dissolved

Directedness holds of every well-typed term, so a `SoundDir` premise is
never information: it is the typing the caller already has, pushed through
`IsDefEq.dir`. Twenty-four lemmas in `Presheaf.lean` carried one anyway,
and `IsDefEq.sound` discharged every one of them at the call site with
`(IsDefEq.dir hΓ h).1`. All twenty-four premises are gone; each lemma
derives it from a typing already in its signature (`hB`, `hat`, `he'`,
`ihMty.typed`, and for `sound_fst_snd_to`, which has no `⊢ Γ`, from
`W.wf`). Thirty call-site arguments, seventeen inner passes and four in
`Strong.lean` went with them.

`Subst.Dir Γ' θ` — every slot directed — survived one round as the last
directedness-shaped premise, on the merges. It is gone too, and the reason
is that `Subst.Good` had been *saying* the right thing all along: its
docstring reads "every slot is either typed in the target context or a
variable", while the definition said only `∀ i, (θ i).Annot Γ'`. Written
out as the disjunction it claimed, `Subst.Good` gives both halves —
`Subst.Good.annot` for strengthening, `Subst.Good.dir` for directedness
(typed slot ⇒ `IsDefEq.dir`, variable ⇒ `dir_bvar`) — and since every
merge already carries it, none needs a directedness premise. `Subst.Dir`,
`Subst.Dir.one`, `Subst.Dir.lift` and the stage-decomposing
`SoundDir.weak` all disappear, along with seven `Subst.Dir.lift` arguments
inside `to_substTerm`.

What is left: `SoundDir` occurs outside `Directed.lean` only in prose. The
two stage-specific statements (`dir_inst`, `sound_beta_lookup`) are
written out rather than named, both blocked by `Interp.inst` needing `Adm`
at the stage.

## 14. `SoundTy` and `SoundDom` merged (2026-10-08)

There were two semantic typing notions. `SoundTy` was a structure, the
syntactic typing paired with "every approximant of `t` is typed at an
approximant of `A`". `SoundDom` was the saturating form: every approximant
sits *below* one that is a `Slot` at an approximant of `A`. The second
implies the first's semantic half — that is `SoundTy.of_dom`, and it
became provable when typing became lower-closed (`TShape.HasType.mono_l`).
So the pair was one notion and a corollary, carried everywhere as two.

Now there is one. `SoundTy` *is* the saturating predicate, and the weaker
reading is `SoundTy.approx`, a theorem. The `Sound` record splits: the
induction proves `SoundCore` (`eq`, `ty`, `pin`, `pin'`) and
`IsDefEq.sound` attaches `typed := H.hasType.1` on top — the typing is the
same expression in every case, so it was never part of the induction, and
it stays a field only because `StrongSound` bundles both halves per
subterm.

What this removed, beyond the notion itself:

* Eleven premise *pairs* that had become literally identical —
  `sound_app_dom`'s `hfty`/`hfdom`, `sound_pair_dom`'s `ihAty`/`ihAd` and
  `ihaty`/`ihadom`, `SoundEq.inst_cod`'s `ha₀`/`hdom₀`, and so on. Each
  lemma now takes one.
* `SoundTy.of_dom`, which became the identity on its second argument, and
  the second `SoundTy.of_eq` (the old structure's).
* `sound_pair_ty`, duplicating `sound_pair_dom`.
* Every `⟨typing, approx⟩` construction. The lemmas that built one now
  conclude `TypedAt` and are named for it (`sound_forallE_typedAt`,
  `sound_sigma_typedAt`, `sound_Y_typedAt`); `and_pinned` and
  `and_pinned_filter` take that half and assemble the record.

`Strong.lean` is where the typing's bundling is real: `StrongSoundCore`'s
clauses need both halves per subterm, and with `SoundTy` no longer
carrying the typing they now carry `Sound Γ A A (.sort u)`, which does.
`StrongSound.sound` returns the `Sound` rather than the `SoundTy`.

The dependency graph shrinks with the merge: `dom` and `ty` were two nodes
of the strongly connected component and are now one, so the edge count
goes from ten of twelve to five of six, and `pin ↔ ty` is the cycle that
pins `Pinned` into the component.

### 14a. `Sound` is four fields and nothing syntactic

The `typed` field went in with §14 and came straight back out. It was
`H.hasType.1` in every case — the derivation the caller passed *in* — so
the record was handing the input back as an output. `Sound` is now the
four fields the induction proves (`eq`, `ty`, `pin`, `pin'`) and
`IsDefEq.sound` is the induction itself, with no wrapper.

The one place the bundling was load-bearing is `Strong.lean`, and there it
belongs: `StrongSound` is a *typing* judgment, so it carries the syntactic
typing as its own premise (`StrongSound.mk` gained it, `StrongSound.typed`
reads it) and `StrongSoundCore`'s annotation premises are typings rather
than `Sound`s. Where a clause needs the semantic half it goes through
`IsDefEq.soundTy hΓ`, which is a one-liner given the typing it already
has. Twelve clause premises got simpler for it.
