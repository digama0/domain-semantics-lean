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
| equality of morphisms mod defeq (free) | `Interp.stage` | **restate as `IsDefEq.stage`** (§3.1): needs the term typed |
| functoriality in the stage (free) | `Interp.subst` | done (naturality) |
| `Ty`/`Tm` quotients: labels equal mod defeq | `LabelEq`, `PiLabelEq`, `IdLabelEq` in `LE`/`Compat` | done |
| `Ctx.extension` is *not* quotiented: `A::Γ` vs `A'::Γ` need `contextConversion` + `HasRenaming` | `Interp.ctx` (the context index is phantom) | done, free |
| `SourceAdmissible`: slot directed, `rawExtend ⟦A⟧ (ρ 0) = ρ 0` | `Adm.cons`: slot WF, typed at an approximant, `⟦A⟧` saturated | done |
| `SourceAdmissible.pullback` | `Adm.subst` | stated, sorried; **probably not needed** (§3.5) |
| `SourceAdmissible.push` at `rawExtend ⟦A⟧ X` | `Adm.cons` at a *typed* slot; the binder rules' `hdom` premise supplies it | done for the binder congruences |
| `rawExtend_isDirected` + idempotent (free) | `SoundJoin` | **avoidable for Π/λ** (§2.3), **needed for `tr`** (§4.7) |
| `normalizedBodyAction`: body evaluated at `rawExtend ⟦A⟧ x` | binder rules evaluate the body at the entry input `e.inp`, and demand `HasType e.inp d` | see η, §4.5: this is where the choice bites |
| `application_piOperator_fixed`: a Π-fixed function's lookup depends only on the normalised argument | no counterpart yet | **needed by η** (§4.5) |
| `IsIdealValued` (body action directed at *every* input) | `SoundDir (A::Γ) B` at every WF slot | follows once `SoundDir` takes `Valuation.WF` |
| `PiReady Γ A B` stored in the *type's* `RawTermProperties` | `SoundDir Γ A`, `SoundDir (A::Γ) B` from the typing of the binder | see η: recovering `A`'s typing from `Γ ⊢ e : Π A B` is the issue |
| `HasFixedness Γ t A` | `SoundTy Γ t A` (`InterpTyped`) | as master |
| `HasEquality` | `SoundEq` | as master |
| `HasSubstitution` / `HasRenaming` | `Interp.substTerm` (∃ρ' form), `Interp.weak'`/`unweak` | `weak'` done; `substTerm`, `unweak` sorried (§3.3, §3.4) |
| `SingleSubstitution.variable_eq` | `Interp.bvar_iff` | done |
| `sourceQuery a` (sup over all typings of the argument) | the `app` rule names the type `A` in `Δ`, one lookup | **wrong as stated** (§5.5b): naming `A` does not remove the obstruction, it relocates it |
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

### 3.2 `IsDefEq.dir`, per former

**Status: every case is proved except `tr`.**  What follows is the
original sketch, annotated where the proof went differently.

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

### 3.3 `Interp.substTerm`, `Interp.inst`

Master's `LE_Interp.subst`, with the stage moving and the directedness of
the substituted terms as a hypothesis rather than a global lemma:

```lean
theorem Interp.substTerm (hΔ : ⊢ Δ) {θ : Subst}
    (hθ : ∀ i {m₁ m₂}, Interp Δ Γ' (θ i) σ ρ m₁ → Interp Δ Γ' (θ i) σ ρ m₂ →
      ∃ s, TShape.WF Δ s ∧ Interp Δ Γ' (θ i) σ ρ s ∧ TShape.LE Δ m₁ s ∧ TShape.LE Δ m₂ s) :
    Interp Δ Γ' (t.subst θ) σ ρ m ↔
      ∃ ρ', Interp Δ Γ t (θ.comp σ) ρ' m ∧ ∀ i, Interp Δ Γ' (θ i) σ ρ (ρ' i)
```

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
by `mono_val`).  `SoundDir Γ a` is available at every use site from
`IsDefEq.dir` on the rule's typing of `a`.

### 3.4 `Interp.unweak`

Master's `weak'_iff.1`: `generalize` the renamed term and case on the
original.  Nothing presheaf-specific: the stage is `σ'.lift_l l` on one
side and `σ'` on the other, and labels are `A[σ'.lift_l l] =
(A.lift' l)[σ']` by `subst_lift'`.  Used by η (§4.5) and both `Y` rules.

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
(§4.5).  Each case below says what it needs from the IHs, from `dir`, and
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
Options in §5.1.  Everything else about `tr` is master's proof.

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

### 5.1 Join-closure of a type's extension (`SoundJoin`)

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

### 5.6 Summary of statement changes

| where | change | why | |
|---|---|---|---|
| `SoundDir` | `Adm` → `Valuation.WF`; upper-bound conclusion; separate lemma `IsDefEq.dir` by induction on typing | §2.3 | **done** |
| `IsDefEq.sound` | two conclusions, `SoundEq ∧ SoundTy` | §2.3 | **done** |
| `Interp.forallE/sigma/lam`, `Interp.tr` | `+ HasType d type` resp. `+ HasType cb type` | §2.4, §4.7 | **done** |
| `Interp.stage` → `IsDefEq.stage` | indexed by a typing derivation | §3.1 | **done** (stated) |
| `Interp.subst_iff` → `Interp.substTerm` | directedness of the `θ i` as a hypothesis (`Interp.Dir`) | §3.3 | **done** (stated) |
| `Interp.inst` | takes `Interp.Dir` of the substituted term | §3.3 | **done** (stated) |
| `Adm.subst` | delete | §3.5 | **done** |
| `ShapeFun.LE` | lookup coverage, carrying `WF` of both graphs | §5.2 | **done** |
| `ShapeFun.Eval.lower` | drop the `WF` side condition (`Shape.LE.wf`) | §5.2 | **done** |
| `Shape.LE` | `WF` of the lower bound at `pair`/`lam`; `Shape.LE.wf` | §5.2 | **done** |
| `Shape.HasType.mono_l` | false at `lam` | §5.5 | open |
| `TShape.HasType` | one inductive over `TShape`, every clause pinning its subject's shape | §5.5a | **done** (old kept as `HasTypeOld`) |
| `TShape.HasType.mono_l` | all clauses but `forallE`/`sigma`; those need `Q'` | §5.5a | open, one step |
| `Shape.HasType.lift` | preservation split off `lift_iff` | §5.5 | **done** |
| `InterpTyped` at Π (and Σ) types | witness carries lookup-form `HasDom` | §4.5(a), §5.1(a) | open |
| `SoundJoin` | keep, upper-bound form; prove per former alongside `sound` | §5.1 | **done** (kept) |

`Interp.Dir Δ Γ t σ ρ` is the one-stage form of directedness, introduced
so that `substTerm`/`inst` can take it as a hypothesis; `SoundDir` is its
closure over well-formed stages and `Interp.Dir.join` is master's form.

The graph-order rows are done: §5.2 records how lookup coverage was made
to reflect along `lift`, which was the one thing standing between it and
η.  The `InterpTyped` row remains open and is a restructuring rather than
a restatement — it changes what `SoundTy` promises and so touches every
case that consumes it.

