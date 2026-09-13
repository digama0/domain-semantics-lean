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
| `sourceQuery a` (sup over all typings of the argument) | the `app` rule names the type `A` in `Δ`, one lookup | done; removes his `app` obstruction to standalone directedness |
| `rawExtend ⟦C[b/]⟧ ⟦x⟧` as the value of `tr` | master's `tr` constructor with two `HasType` premises | as master; §4.7 |
| `regular` field of `RawJudgment` | — | he never uses it; drop |
| `IsCode r` separate from inhabitation | `HasType · (sort r)` | done, cumulative |
| conditional sup `cSup`, `CondSemilatticeSup` | `Shape.join` + `Compat` | done |
| `Graph.IsCoherent`, `InternallyCompatible` | the coherence conjunct of `Shape.WF` (hereditary, label-sensitive) | done |
| `Graph.LE` = single-entry coverage (`Entry.mem`) | `ShapeFun.LE`, same | **must change to lookup coverage** (§4.5, §5.2) |
| an ideal is closed under every graph valid for its action | — (a value is one shape) | the previous row is the replacement |

Three of these rows are design decisions rather than lemmas, and the
document is organised around them:

1. **Directedness is a separate lemma**, `IsDefEq.dir`, proved *before*
   `IsDefEq.sound` by its own induction on typing, with `Valuation.WF` in
   place of `Adm` (§2.3).  His `HasIdeality` is bundled into
   `RawTermProperties` only because his `app` is a sup over `sourceQuery`
   and needs `PiReady`+`HasFixedness` to collapse; our `app` is one lookup,
   so the obstruction is gone.  What remains typing-dependent is only the
   *stage*: under a binder the label term extends the stage, and the
   extended stage is typed only if the binder annotation is.  That is why
   the induction is on typing and not on the raw term, and it is the entire
   residue of his quotient.
2. **The graph order is lookup coverage** (§5.2).  η forces it, for the
   same reason his η needs the λ-value to be an ideal closed under valid
   graphs.
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
`Evaluates g … x (y₁' ⊔ y₂')`.  Upper bound: `.app` at that.  Note the
labels agree on the nose — both sides are the same term at the same stage
— so no stage move.  This is the case his design cannot do standalone
(`sourceQuery` is a sup over labels, and the collapse needs `PiReady` and
`HasFixedness`); ours can because the label is named.

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

*`Y`.* both are `Interp b` at `ρ.push sᵢ` with `Interp (Y A b) sᵢ`;
the IH on the *inner* `Y` — this case is an inner induction on the
`Interp` derivation, since `Y` refers to itself; master's `compat_join`
does the same — gives `s ≥ s₁, s₂`, then `mono_val` and the IH on `b`.

*`id`.* label-only; the canonical shape.

*`refl`.* as `succ`.

*`tr`.* §4.7.  This is the one case with content beyond the IHs.

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

### 5.2 The graph order must be lookup coverage

Current `ShapeFun.LE`: every entry of `f` is covered by *one* entry of
`f'`.  Required (η →, `fst_snd`, and every place a join of lookups has to
sit below an approximant):

```lean
def ShapeFun.LE Δ R f f' := ∀ e ∈ f, ∃ y, Evaluates Δ f' e.ty e.tm e.inp y ∧ R e.out y
```

Single-entry coverage is master's order, right there because saturated
graphs store their joins; it is also his `Graph.LE` (`Entry.mem`), right
there because a value is an ideal closed under valid graphs.  Neither
reason survives here.  Consequences: `LE.refl` by `entry_self`; `LE.trans`
by `Evaluates.mono_graph'` (needs the larger graph's coherence — which
`WF` has, so transitivity holds on WF shapes, as reflexivity already
does); `lift_le_lift` by `Evaluates.lift_iff`; `LE.subst` by
`Evaluates.subst`; `Compat.anti` by `Evaluates.compat`; `join_le`/`le_join`
unchanged (append only adds entries: `mono_sub`); `le_bot_iff` unchanged.
The `Evaluates`-based `HasDom` of §4.5e' is this order's `HasDom`.  Cost:
a pass over `Shape.lean`'s order section; the lemmas it needs exist.

### 5.3 Lower-closed `HasType` vs `HasDom` in the λ clause

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

### 5.5 Summary of statement changes

| where | change | why |
|---|---|---|
| `SoundDir` | `Adm` → `Valuation.WF`; upper-bound conclusion; separate lemma `IsDefEq.dir` by induction on typing | §2.3 |
| `IsDefEq.sound` | two conclusions, `SoundEq ∧ SoundTy` | §2.3 |
| `Interp.forallE/sigma/lam`, `Interp.tr` | `+ HasType d type` resp. `+ HasType cb type` | §2.4, §4.7 |
| `Interp.stage` → `IsDefEq.stage` | indexed by a typing derivation | §3.1 |
| `Interp.subst_iff` → `Interp.substTerm` | directedness of the `θ i` as a hypothesis | §3.3 |
| `Interp.inst` | takes `SoundDir Γ a` | §3.3 |
| `Adm.subst` | delete | §3.5 |
| `ShapeFun.LE` | lookup coverage | §5.2 |
| `InterpTyped` at Π (and Σ) types | witness carries lookup-form `HasDom` | §4.5(a), §5.1(a) |
| `SoundJoin` | keep, upper-bound form; prove per former alongside `sound` | §5.1 |

