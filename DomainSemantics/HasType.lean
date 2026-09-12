import DomainSemantics.Shape

/-! # Typing of labelled shapes

`Shape.HasType Δ m a` says the shape `m` is a well-typed inhabitant of the
type-shape `a`.  This is `ShapeOld.lean`'s `HasType`, with three changes.

* It is `Prop`-valued and defined directly, not factored through a `Bool`
  function: labels are compared up to definitional equality, so nothing
  here is decidable and the `hasType` / `hasType.core` / `HasTypeU` /
  `unfold_iff` layering has no purpose.
* It is indexed by a context, for the same reason.
* The Π and λ clauses used `ShapeFun.app`, the search for the maximal
  graph entry below the input, which was only correct because graphs were
  saturated (`ShapeFun.WF`).  Saturation is gone, so the codomain type is
  obtained from the relational lookup `Evaluates` instead, and the output
  of an entry must be typed at *some* code the family graph yields — which
  is also how the other repo reads it (`rawExtend T X` quantifies
  `∃ c ∈ T`).

Together with `InterpTyped`/`SoundTy` this plays the role of the other
repo's decoder: see §4.2 of `presheaf-plan.md`.  Its fixed-point
construction (`piStep`/`piStage`/`rank`/`piLimit`) is unnecessary here
because the recursion is structural in the level. -/

namespace DomainSemantics

variable {Δ : List Term}

variable (Δ : List Term) {n} (f : ShapeFun n) (A a : Term) (x : Shape n) in
/-- Relational graph lookup: `Evaluates Δ f A a x y` says `y` approximates
the result of applying the graph `f`, at the argument label `(A, a)`, to an
input at least `x`.  It is the set of outputs of matching entries, closed
downwards and under compatible joins — the other repo's `Evaluates`.

Replacing `ShapeFun.app` (a function) by this (a relation) is what lets us
drop saturation: the join of several matching entries is available here
without having to be stored in the graph. -/
inductive Evaluates : Shape n → Prop where
  | bot : Evaluates .bot
  | entry (e : Entry (Shape n)) : e ∈ f → LabelEq Δ e.ty e.tm A a →
    Shape.LE Δ e.inp x → Evaluates e.out
  -- the lookup is a lower set, but **lowering is constrained to well-formed
  -- shapes**.  Unrestricted lowering would break `Evaluates.wf`, since `WF`
  -- is not downward closed: a smaller λ-shape may have a bottom output,
  -- which non-degeneracy forbids.  With the constraint the lookup stays an
  -- ideal and everything it returns is still well formed.
  | lower {y z} : Shape.WF Δ y → Shape.LE Δ y z → Evaluates z → Evaluates y
  -- Now that the `join` *function* is correct (no information-free λ-shapes),
  -- closing under it rather than under the `Join` relation is what makes
  -- `Evaluates` transport along a substitution: `join` commutes with
  -- substitution on the nose, whereas `Join Θ` quantifies over more shapes
  -- than the image of the substitution
  | join {y z} : Shape.Compat Δ y z → Evaluates y → Evaluates z → Evaluates (y.join z)

/-- The **β-law**, and it is nearly free here: looking a graph up at one of
its own entries returns that entry's output.

The other repo needs a real lemma for this
(`rawApplication_abstraction_eq_value`: applying an abstraction recovers
the action it was built from), because its λ-value is an abstraction
*operator* and recovering the action needs finitarity and
ideal-valuedness.  Our λ-shape carries the graph itself, and the graph is
a `List`, so finitarity is structural and β is one constructor. -/
theorem Evaluates.entry_self {Δ : List Term} {n} {f : ShapeFun n} {e : Entry (Shape n)}
    (hwf : ShapeFun.WF Δ (Shape.WF Δ) f) (he : e ∈ f) :
    Evaluates Δ f e.ty e.tm e.inp e.out :=
  have ⟨⟨_, hty⟩, htm, hin, _⟩ := hwf e he
  .entry e he (LabelEq.refl hty htm) (Shape.LE.refl hin)

/-- Every input of the graph is typed at the domain shape.

Master states this as "every entry is *dominated by* one whose input is
typed", which is a saturation-era formulation: with a saturated graph and
a lookup that searches for the maximal entry below the argument, you need
the entry the search lands on to be typed, and you find it by a finiteness
argument on the domination chain.  Nothing here searches, so the direct
form is both simpler and stronger, and it is exactly the premise
`Interp`'s binder rules carry. -/
def ShapeFun.HasDom (Δ : List Term) (T : Shape n → Shape n → Prop)
    (f : ShapeFun n) (d : Shape n) : Prop :=
  ∀ e ∈ f, T e.inp d

/-- `m` is a well-typed inhabitant of the type-shape `a`.  Structural
recursion on the level.

Following master, the `⊥` clauses are given **per type former** rather
than blanket, and the `lam`/`pair` clauses carry the well-formedness of
the Π/Σ type they inhabit.  Both are needed for `isType`
(`HasType m a → HasType a .type`), without which `mono_r` cannot be
stated, let alone proved: a blanket `HasType ⊥ a = True` would make `⊥`
an inhabitant of shapes that are not types at all. -/
def Shape.HasType (Δ : List Term) : ∀ {n}, Shape n → Shape n → Prop
  -- `⊥` inhabits every *type*
  | 0, .bot, .bot => True
  | 0, .bot, .sort _ => True
  | 0, .sort _, .sort j => j = true
  | 0, _, _ => False
  | _+1, .bot, .bot => True
  | _+1, .bot, .sort _ => True
  | _+1, .bot, .unit _ => True
  | _+1, .bot, .nat => True
  | _+1, .bot, .id _ _ _ _ => True
  | _+1, .bot, .forallE _ _ d f =>
      HasType Δ d .type ∧ ShapeFun.HasDom Δ (HasType Δ) f d ∧
        ∀ e ∈ f, HasType Δ e.out .type
  | _+1, .bot, .sigma _ _ d f =>
      HasType Δ d .type ∧ ShapeFun.HasDom Δ (HasType Δ) f d ∧
        ∀ e ∈ f, HasType Δ e.out .type
  | _+1, .bot, _ => False
  | _+1, .sort _, .sort j => j = true
  | _+1, .unit r, .sort j => r ≤ j
  | _+1, .nat, .sort j => j = true
  | _+1, .zero, .nat => True
  -- nested match, as in master: splitting the outer level pattern would stop
  -- the final catch-all from reducing for `succ` against a non-`nat` type
  | n+1, .succ v, .nat =>
      match n, v with
      | 0, w => w = .bot
      | _+1, w => HasType Δ w .nat
  | _+1, .id r _ _ _, .sort j => r ≤ j
  -- a Π-type is in `sort r` when its codomain family lands in `sort r`
  -- the domain is a type: master derives this from saturation (every graph
  -- has a `⊥`-input entry, so the domain has an inhabitant); with
  -- saturation gone it has to be stated
  | _+1, .forallE _ _ d f, .sort r =>
      HasType Δ d .type ∧ ShapeFun.HasDom Δ (HasType Δ) f d ∧
        ∀ e ∈ f, HasType Δ e.out (.sort r)
  | _+1, .sigma _ _ d f, .sort j =>
      j = true ∧ HasType Δ d .type ∧ ShapeFun.HasDom Δ (HasType Δ) f d ∧
        ∀ e ∈ f, HasType Δ e.out .type
  -- a λ-shape inhabits a Π-type when that Π-type is well-formed and every
  -- entry's output is typed at a code the codomain family yields at that
  -- entry's label and input
  | _+1, .lam g, .forallE _ _ d f =>
      (HasType Δ d .type ∧ ShapeFun.HasDom Δ (HasType Δ) f d ∧
          ∀ e ∈ f, HasType Δ e.out .type) ∧
        ShapeFun.HasDom Δ (HasType Δ) g d ∧
        ∀ e ∈ g, ∃ c, Evaluates Δ f e.ty e.tm e.inp c ∧ HasType Δ e.out c
  -- a pair inhabits a Σ-type when that Σ-type is well formed, the first
  -- component is in the domain, and the second is typed at a code the
  -- codomain family yields at the pair's own label and first component.
  -- Exactly the `lam` clause, with one entry instead of a graph
  | _+1, .pair ty tm x y, .sigma _ _ d f =>
      (HasType Δ d .type ∧ ShapeFun.HasDom Δ (HasType Δ) f d ∧
          ∀ e ∈ f, HasType Δ e.out .type) ∧
        HasType Δ x d ∧
        ∃ c, Evaluates Δ f ty tm x c ∧ HasType Δ y c
  -- with a label-only Id shape there is nothing semantic left to check
  | _+1, .refl _, .id r _ _ _ => r = true
  | _+1, _, _ => False

/-! ## Codes and cumulativity

There is no separate `IsCode` predicate: a shape is a code exactly when it
is a type, `HasType Δ a .type`, because the two universes are **cumulative
in the model** — a proof-irrelevant former is also a proof-relevant type.
Cumulativity is built into the clauses that compare sorts with `≤`
(`unit`, `id`) and is the lemma below for the rest.

(The other repo does keep a separate `IsCode`, because it has no typing
relation on shapes at all and needs a downward-closed predicate for its
universe retraction.  With `HasType` available, master's route is the
right one: the lemma that replaces downward closure is `mono_r`, which
carries the hypothesis that the *larger* type is itself a type, and so
never needs `HasType · (sort r)` to be downward closed.) -/

private theorem Bool.eq_true_of_le {r s : Bool} (h : r = true) (hrs : r ≤ s) : s = true := by
  subst h; revert hrs; cases s <;> decide

private theorem Bool.le_true' (r : Bool) : r ≤ true := by cases r <;> decide

private theorem Bool.le_tr {t r s : Bool} (h₁ : t ≤ r) (h₂ : r ≤ s) : t ≤ s := by
  revert h₁ h₂; cases t <;> cases r <;> cases s <;> decide

/-- The universes are cumulative: a `prop` is also a `type`. -/
theorem Shape.HasType.cumul : ∀ {n} {a : Shape n} {r s : Bool},
    Shape.HasType Δ a (.sort r) → r ≤ s → Shape.HasType Δ a (.sort s) := by
  intro n
  induction n with
  | zero =>
    intro a r s h hrs
    cases a with
    | bot => trivial
    | sort => exact Bool.eq_true_of_le h hrs
  | succ n ih =>
    intro a r s h hrs
    cases a with
    | bot => trivial
    | sort _ => exact Bool.eq_true_of_le h hrs
    | nat => exact Bool.eq_true_of_le h hrs
    | unit t => exact Bool.le_tr h hrs
    | id t A a' b' => exact Bool.le_tr h hrs
    | forallE A B d f => exact ⟨h.1, h.2.1, fun e he => ih (h.2.2 e he) hrs⟩
    | sigma A B d f => exact ⟨Bool.eq_true_of_le h.1 hrs, h.2⟩
    | _ => exact absurd h id

/-- `⊥` inhabits every type (master's form: the hypothesis is what the
blanket version silently assumed). -/
theorem Shape.HasType.bot : ∀ {n} {a : Shape n},
    Shape.HasType Δ a .type → Shape.HasType Δ .bot a := by
  intro n
  cases n with
  | zero => intro a _; cases a <;> trivial
  | succ n =>
    intro a h
    cases a with
    | bot | sort | unit | nat | id => trivial
    | forallE A B d f => exact h
    | sigma A B d f => exact h.2
    | _ => exact absurd h id

/-- Anything typed has a type that is itself a type.  This is the lemma the
per-former `⊥` clauses and the Π-well-formedness conjuncts exist for. -/
theorem Shape.HasType.isType : ∀ {n} {m a : Shape n},
    Shape.HasType Δ m a → Shape.HasType Δ a .type := by
  intro n
  induction n with
  | zero => intro m a h; cases m <;> cases a <;> simp_all [Shape.HasType]
  | succ n ih =>
    intro m a h
    cases m with
    | bot =>
      cases a with
      | bot | sort | nat => trivial
      | unit r => exact Bool.le_true' r
      | id r _ _ _ => exact Bool.le_true' r
      | forallE A B d f => exact h
      | sigma A B d f => exact ⟨rfl, h⟩
      | _ => exact absurd h id
    | sort s => cases a <;> first | exact absurd h id | trivial
    | unit s => cases a <;> first | exact absurd h id | trivial
    | nat => cases a <;> first | exact absurd h id | trivial
    | zero => cases a <;> first | exact absurd h id | trivial
    | succ v => cases a <;> first | exact absurd h id | trivial
    | id s A a' b' => cases a <;> first | exact absurd h id | trivial
    | refl w =>
      cases a with
      | id r _ _ _ => exact Bool.le_true' r
      | _ => exact absurd h id
    | forallE A B d f => cases a <;> first | exact absurd h id | trivial
    | sigma A B d f => cases a <;> first | exact absurd h id | trivial
    | lam g =>
      cases a with
      | forallE A B d f => exact h.1
      | _ => exact absurd h id
    | pair x y =>
      cases a with
      | sigma A B d f => exact ⟨rfl, h.1⟩
      | _ => exact absurd h id

/-! ## Substitution -/

theorem Evaluates.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ)
    {n} {f : ShapeFun n} {A a : Term} {x c : Shape n} :
    Evaluates Δ f A a x c →
    Evaluates Θ (ShapeFun.subst (Shape.subst · τ) τ f) (A.subst τ) (a.subst τ)
      (x.subst τ) (c.subst τ) := by
  intro h
  induction h with
  | bot => simp only [Shape.subst_bot]; exact .bot
  | entry e he hlab hin =>
    exact .entry _ (ShapeFun.mem_subst.2 ⟨e, he, rfl⟩) (hlab.subst hΘ W)
      (Shape.LE.subst hΘ W hin)
  | lower hw hle _ ih =>
    exact .lower (Shape.WF.subst hΘ W hw) (Shape.LE.subst hΘ W hle) ih
  | join hc _ _ ih₁ ih₂ =>
    exact Shape.join_subst ▸ .join (Shape.Compat.subst hΘ W hc) ih₁ ih₂

theorem ShapeFun.HasDom.subst_of {Δ Θ : List Term} {τ : Subst} {n} {f : ShapeFun n}
    {d : Shape n} (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ)
    (ih : ∀ {m a : Shape n}, Shape.HasType Δ m a → Shape.HasType Θ (m.subst τ) (a.subst τ))
    (h : ShapeFun.HasDom Δ (Shape.HasType Δ) f d) :
    ShapeFun.HasDom Θ (Shape.HasType Θ) (ShapeFun.subst (Shape.subst · τ) τ f)
      (d.subst τ) := by
  intro e' he'
  obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
  exact ih (h e he)

/-- Typing of shapes is stable along a typed substitution. -/
theorem Shape.HasType.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) : ∀ {n} {m a : Shape n},
    Shape.HasType Δ m a → Shape.HasType Θ (m.subst τ) (a.subst τ) := by
  intro n
  induction n with
  | zero => intro m a h; cases m <;> cases a <;> simp_all [Shape.HasType, Shape.subst]
  | succ n ih =>
    -- the "this Π/Σ type is well-formed" conjunct, substituted
    have hpi : ∀ {f : ShapeFun n} {d : Shape n},
        (Shape.HasType Δ d .type ∧ ShapeFun.HasDom Δ (Shape.HasType Δ) f d ∧
            ∀ e ∈ f, Shape.HasType Δ e.out .type) →
        (Shape.HasType Θ (d.subst τ) .type ∧
          ShapeFun.HasDom Θ (Shape.HasType Θ) (ShapeFun.subst (Shape.subst · τ) τ f)
            (d.subst τ) ∧
          ∀ e ∈ ShapeFun.subst (Shape.subst · τ) τ f, Shape.HasType Θ e.out .type) := by
      intro f d h
      refine ⟨by simpa using ih h.1, ShapeFun.HasDom.subst_of hΘ W ih h.2.1, fun e' he' => ?_⟩
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      simpa using ih (h.2.2 e he)
    intro m a h
    cases m with
    | bot =>
      cases a with
      | bot | sort | unit | nat | id => trivial
      | forallE A B d f => exact hpi h
      | sigma A B d f => exact hpi h
      | _ => exact absurd h id
    | sort s => cases a <;> first | exact absurd h id | exact h
    | unit s => cases a <;> first | exact absurd h id | exact h
    | nat => cases a <;> first | exact absurd h id | exact h
    | zero => cases a <;> first | exact absurd h id | exact h
    | id s A a' b' => cases a <;> first | exact absurd h id | exact h
    | refl w => cases a <;> first | exact absurd h id | exact h
    | succ v =>
      cases a with
      | nat =>
        cases n with
        | zero => cases (h : v = .bot); exact Shape.subst_bot
        | succ m => exact ih h
      | _ => exact absurd h id
    | forallE A B d f =>
      cases a with
      | sort r => exact ⟨by simpa using ih h.1,
          ShapeFun.HasDom.subst_of hΘ W ih h.2.1, fun e' he' => by
          obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
          simpa using ih (h.2.2 e he)⟩
      | _ => exact absurd h id
    | sigma A B d f =>
      cases a with
      | sort r => exact ⟨h.1, hpi h.2⟩
      | _ => exact absurd h id
    | lam g =>
      cases a with
      | forallE A B d f =>
        refine ⟨hpi h.1, ShapeFun.HasDom.subst_of hΘ W ih h.2.1, fun e' he' => ?_⟩
        obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
        have ⟨c, hev, hty⟩ := h.2.2 e he
        exact ⟨c.subst τ, Evaluates.subst hΘ W hev, ih hty⟩
      | _ => exact absurd h id
    | pair ty tm x y =>
      cases a with
      | sigma A B d f =>
        have ⟨c, hev, hcty⟩ := h.2.2
        exact ⟨hpi h.1, ih h.2.1, c.subst τ, Evaluates.subst hΘ W hev, ih hcty⟩
      | _ => exact absurd h id

/-! ## The lookup is coherent

What the relational lookup owes and master does not: master's lookup is a
saturated max-below *function*, single-valued, so there is nothing to
join and nothing to check. -/

/-- Everything a single lookup returns is pairwise compatible, given that
the graph is internally coherent and the query shape is.

Coherence asks for the two entries' *inputs* to be compatible, and that is
exactly what the query supplies: both inputs lie below the query shape, so
`of_common_upper` applies. -/
theorem Evaluates.compat {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a : Term}
    {x : Shape n} (hf : ShapeFun.Compat Shape.Compat Δ f f) (hx : Shape.Compat Δ x x) :
    ∀ {y z : Shape n}, Evaluates Δ f A a x y → Evaluates Δ f A a x z →
      Shape.Compat Δ y z := by
  -- an entry output selected by the query is compatible with anything the
  -- lookup returns
  have atom : ∀ {e : Entry (Shape n)}, e ∈ f → LabelEq Δ e.ty e.tm A a →
      Shape.LE Δ e.inp x → ∀ {z}, Evaluates Δ f A a x z →
      Shape.Compat Δ e.out z := by
    intro e he hlab hin z hz
    induction hz with
    | bot => exact Shape.Compat.bot_right
    | entry e' he' hlab' hin' =>
      have key := hf e he e' he' Δ .id hΔ (Ctx.SubstEq.id hΔ)
        (by simpa using hlab.trans (LabelEq.symm hlab'))
        (by simpa using Shape.Compat.of_common_upper hΔ hx hin hin')
      simpa using key
    | lower _ hle _ ih => exact Shape.Compat.anti_right hΔ ih hle
    | join _ _ _ ih₁ ih₂ =>
      exact Shape.Compat.symm hΔ
        (Shape.join_compat hΔ (Shape.Compat.symm hΔ ih₁) (Shape.Compat.symm hΔ ih₂))
  intro y z hy hz
  induction hy with
  | bot => exact Shape.Compat.bot_left
  | entry e he hlab hin => exact atom he hlab hin hz
  | lower _ hle _ ih =>
    exact Shape.Compat.symm hΔ (Shape.Compat.anti_right hΔ (Shape.Compat.symm hΔ ih) hle)
  | join _ _ _ ih₁ ih₂ => exact Shape.join_compat hΔ ih₁ ih₂

/-- Everything the lookup returns is well formed, structurally: it is `⊥`,
an entry output, a join of those, or an explicitly well-formed lowering.
The `WF` premise on `lower` is exactly what makes this hold — `WF` is not
downward closed, so unconstrained lowering would break it. -/
theorem Evaluates.wf {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a : Term}
    {x : Shape n} (hf : ∀ e ∈ f, Shape.WF Δ e.out) :
    ∀ {y : Shape n}, Evaluates Δ f A a x y → Shape.WF Δ y := by
  intro y h
  induction h with
  | bot => cases n <;> trivial
  | entry e he _ _ => exact hf e he
  | lower hw _ _ _ => exact hw
  | join hc _ _ ih₁ ih₂ => exact Shape.WF.join hΔ hc ih₁ ih₂

/-- The lookup is **monotone in the graph**, and what it returns is a type
whenever the graph's outputs are.  Master gets monotonicity from
`app_mono_l`, its lookup being a function; ours produces a witness, and
the `join` case needs the two witnesses to be compatible
(`Evaluates.compat`), bounded (`le_join`, via `Evaluates.wf`), and typed
(`hjoin`, which is `mono_r`'s companion at the level below). -/
theorem Evaluates.mono_graph {Δ : List Term} (hΔ : ⊢ Δ) {n} {f f' : ShapeFun n}
    {A a : Term} {x : Shape n} {r : Bool}
    (hf' : ShapeFun.Compat Shape.Compat Δ f' f') (hx : Shape.Compat Δ x x)
    (hwf : ∀ e ∈ f', Shape.WF Δ e.out)
    (hty : ∀ e ∈ f', Shape.HasType Δ e.out (.sort r))
    (hjoin : ∀ {y z : Shape n}, Shape.WF Δ y → Shape.WF Δ z → Shape.Compat Δ y z →
      Shape.HasType Δ y (.sort r) → Shape.HasType Δ z (.sort r) →
      Shape.HasType Δ (y.join z) (.sort r))
    (hff' : ShapeFun.LE Δ (Shape.LE Δ) f f') :
    ∀ {c : Shape n}, Evaluates Δ f A a x c →
      ∃ c', Evaluates Δ f' A a x c' ∧ Shape.LE Δ c c' ∧
        Shape.HasType Δ c' (.sort r) := by
  intro c h
  induction h with
  | bot => exact ⟨.bot, .bot, Shape.LE.bot, by cases n <;> trivial⟩
  | entry e he hlab hin =>
    have ⟨e', he', hlab', hin', hout'⟩ := hff' e he
    exact ⟨e'.out, .entry e' he' (hlab'.trans hlab)
      (hin'.trans hΔ hin), hout', hty e' he'⟩
  | lower _ hle _ ih =>
    have ⟨c', hc', hle', hty'⟩ := ih
    exact ⟨c', hc', hle.trans hΔ hle', hty'⟩
  | join _ _ _ ih₁ ih₂ =>
    have ⟨y', hy', hley, htyy⟩ := ih₁
    have ⟨z', hz', hlez, htyz⟩ := ih₂
    have hc : Shape.Compat Δ y' z' := Evaluates.compat hΔ hf' hx hy' hz'
    have hwy := Evaluates.wf hΔ hwf hy'
    have hwz := Evaluates.wf hΔ hwf hz'
    have ⟨hu₁, hu₂⟩ := Shape.le_join hΔ hwy hwz hc
    exact ⟨y'.join z', .join hc hy' hz',
      Shape.join_le (hley.trans hΔ hu₁) (hlez.trans hΔ hu₂),
      hjoin hwy hwz hc htyy htyz⟩

/-! ## Monotonicity on the right, and typed joins

These two are **mutually recursive on the level** and so are proved
together: `mono_r` at level `n+1` uses `mono_graph`, whose `join` case
needs typed joins at level `n`; and typed joins at level `n+1` need
`mono_r` at level `n` to move an entry's input from one domain shape up to
the joined one.  Both descend, so one induction on the level does it.

`mono_r` is monotone on the **right** only.  `HasType` is not monotone on
the left, and the hypothesis that the larger type is itself a type is what
lets it avoid needing that. -/
theorem Shape.HasType.mono_r_join (hΔ : ⊢ Δ) : ∀ {n},
    (∀ {m a a' : Shape n} {r : Bool}, Shape.WF Δ m → Shape.WF Δ a' →
      Shape.HasType Δ m a → Shape.LE Δ a a' → Shape.HasType Δ a' (.sort r) →
      Shape.HasType Δ m a') ∧
    (∀ {y z : Shape n} {r : Bool}, Shape.WF Δ y → Shape.WF Δ z → Shape.Compat Δ y z →
      Shape.HasType Δ y (.sort r) → Shape.HasType Δ z (.sort r) →
      Shape.HasType Δ (y.join z) (.sort r)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun {m a a' r} _ _ h hle hA => ?_, fun {y z r} _ _ _ hy hz => ?_⟩
    · cases m with | bot => cases a' <;> trivial | sort s
      cases a with | bot => cases h | sort j
      cases a' with | bot => cases hle | sort j'
      exact (hle : j = j').symm.trans h
    · cases y with | bot => exact hz | sort s
      cases z with | bot => exact hy | sort s'
      exact hy
  | succ n ih =>
    obtain ⟨ihm, ihj⟩ := ih
    refine ⟨?_, ?_⟩
    · -- mono_r
      intro m a a' r hwm hwa h hle hA
      cases m with
      | bot => exact .bot (.cumul hA (Bool.le_true' r))
      | sort s =>
        cases a with | sort j => ?_ | _ => cases h
        cases a' <;> cases hle; exact h
      | unit t =>
        cases a with | sort j => ?_ | _ => cases h
        cases a' <;> cases hle; exact h
      | nat =>
        cases a with | sort j => ?_ | _ => cases h
        cases a' <;> cases hle; exact h
      | id t A₀ a₀ b₀ =>
        cases a with | sort j => ?_ | _ => cases h
        cases a' <;> cases hle; exact h
      | zero => cases a <;> cases h; cases a' <;> cases hle; trivial
      | succ v => cases a <;> (try cases h); cases a' <;> cases hle; trivial
      | refl w =>
        cases a with | id t A₀ a₀ b₀ => ?_ | _ => cases h
        cases a' with | id t' A₁ a₁ b₁ => ?_ | _ => cases hle
        exact (hle.1 : t = t').symm.trans h
      | forallE A₀ B₀ d f =>
        cases a with | sort j => ?_ | _ => cases h
        cases a' with | sort j' => exact ((hle : j = j') ▸ h : _) | _ => cases hle
      | sigma A₀ B₀ d f =>
        cases a with | sort j => ?_ | _ => cases h
        cases a' with | sort j' => ?_ | _ => cases hle
        exact hle ▸ h
      | pair ty tm x y =>
        cases a with | sigma A₀ B₀ d g => ?_ | _ => cases h
        cases a' with | sigma A₁ B₁ d' g' => ?_ | _ => cases hle
        have ⟨c, hev, hcty⟩ := h.2.2
        have ⟨c', hev', hcle, hc'ty⟩ :=
          Evaluates.mono_graph hΔ hwa.2.2.2.2 (Shape.WF.coherent hwm.2.2.1)
            (fun e' he' => (hwa.2.2.2.1 e' he').2.2.2)
            (fun e' he' => hA.2.2.2 e' he') ihj hle.2.2 hev
        exact ⟨hA.2, ihm hwm.2.2.1 hwa.2.2.1 h.2.1 hle.2.1 hA.2.1,
          c', hev', ihm hwm.2.2.2.1 (Evaluates.wf hΔ
            (fun e' he' => (hwa.2.2.2.1 e' he').2.2.2) hev') hcty hcle hc'ty⟩
      | lam g =>
        cases a with | forallE A₀ B₀ d f => ?_ | _ => cases h
        cases a' with | forallE A₁ B₁ d' f' => ?_ | _ => cases hle
        refine ⟨⟨hA.1, hA.2.1, fun e he => .cumul (hA.2.2 e he) (Bool.le_true' r)⟩, ?_, ?_⟩
        · intro e he
          exact ihm (hwm.2.2.1 e he).2.2.1 hwa.2.2.1 (h.2.1 e he) hle.2.1 hA.1
        · intro e he
          have ⟨c, hev, hcty⟩ := h.2.2 e he
          have ⟨c', hev', hcle, hc'ty⟩ :=
            Evaluates.mono_graph hΔ hwa.2.2.2.2 (hwm.2.2.1 e he).2.2.1.coherent
              (fun e' he' => (hwa.2.2.2.1 e' he').2.2.2)
              (fun e' he' => hA.2.2 e' he') ihj hle.2.2 hev
          exact ⟨c', hev', ihm (hwm.2.2.1 e he).2.2.2 (Evaluates.wf hΔ
            (fun e' he' => (hwa.2.2.2.1 e' he').2.2.2) hev') hcty hcle hc'ty⟩
    · -- typed joins
      intro y z r hwy hwz hc hy hz
      cases y with
      | bot => exact hz
      | forallE A₀ B₀ d f =>
        cases z with | bot => exact hy | forallE A₁ B₁ d' g => ?_ | _ => cases hc
        have hdj := ihj hwy.2.2.1 hwz.2.2.1 hc.2.1 hy.1 hz.1
        have ⟨hu₁, hu₂⟩ := Shape.le_join hΔ hwy.2.2.1 hwz.2.2.1 hc.2.1
        refine ⟨hdj, fun e he => ?_, fun e he => ?_⟩
        · match List.mem_append.1 he with
          | .inl he =>
            exact ihm (hwy.2.2.2.1 e he).2.2.1
              (Shape.WF.join hΔ hc.2.1 hwy.2.2.1 hwz.2.2.1) (hy.2.1 e he) hu₁ hdj
          | .inr he =>
            exact ihm (hwz.2.2.2.1 e he).2.2.1
              (Shape.WF.join hΔ hc.2.1 hwy.2.2.1 hwz.2.2.1) (hz.2.1 e he) hu₂ hdj
        · match List.mem_append.1 he with
          | .inl he => exact hy.2.2 e he
          | .inr he => exact hz.2.2 e he
      | sigma A₀ B₀ d f =>
        cases z with | bot => exact hy | sigma A₁ B₁ d' g => ?_ | _ => cases hc
        have hdj := ihj hwy.2.2.1 hwz.2.2.1 hc.2.1 hy.2.1 hz.2.1
        have ⟨hu₁, hu₂⟩ := Shape.le_join hΔ hwy.2.2.1 hwz.2.2.1 hc.2.1
        refine ⟨hy.1, hdj, fun e he => ?_, fun e he => ?_⟩
        · match List.mem_append.1 he with
          | .inl he =>
            exact ihm (hwy.2.2.2.1 e he).2.2.1
              (Shape.WF.join hΔ hc.2.1 hwy.2.2.1 hwz.2.2.1) (hy.2.2.1 e he) hu₁ hdj
          | .inr he =>
            exact ihm (hwz.2.2.2.1 e he).2.2.1
              (Shape.WF.join hΔ hc.2.1 hwy.2.2.1 hwz.2.2.1) (hz.2.2.1 e he) hu₂ hdj
        · match List.mem_append.1 he with
          | .inl he => exact hy.2.2.2 e he
          | .inr he => exact hz.2.2.2 e he
      | _ => cases z <;> exact hy

/-- Typing is monotone on the right. -/
theorem Shape.HasType.mono_r (hΔ : ⊢ Δ) {n} {m a a' : Shape n} {r : Bool}
    (hwm : Shape.WF Δ m) (hwa : Shape.WF Δ a') (h : Shape.HasType Δ m a)
    (hle : Shape.LE Δ a a') (hA : Shape.HasType Δ a' (.sort r)) :
    Shape.HasType Δ m a' := (Shape.HasType.mono_r_join hΔ).1 hwm hwa h hle hA

/-- The join of two types is a type. -/
theorem Shape.HasType.join (hΔ : ⊢ Δ) {n} {y z : Shape n} {r : Bool}
    (hwy : Shape.WF Δ y) (hwz : Shape.WF Δ z) (hc : Shape.Compat Δ y z)
    (hy : Shape.HasType Δ y (.sort r)) (hz : Shape.HasType Δ z (.sort r)) :
    Shape.HasType Δ (y.join z) (.sort r) := (Shape.HasType.mono_r_join hΔ).2 hwy hwz hc hy hz

/-! ## Proof irrelevance

`HasType Δ a .prop → HasType Δ x a → x = ⊥`: a proposition has no
information in it.  This is master's `HasType.proofIrrel`, and it is the
shape-level content of the syntactic `proofIrrel` rule.

Only the Π case has anything to it, and it is where dropping saturation
bites once more.  Master reads the codomain off the graph with the
function `ShapeFun.app` and recurses on its value directly.  Here the
codomain comes out of `Evaluates`, which may hand back a *lowering* of an
entry output, and `HasType · (.sort r)` is not downward closed — master's
`mono_l` is an equivalence (`m ≤ m'` and `m' ≤ m`), not monotonicity, so
it does not help either.  `Evaluates.bounded` is the way round: every
witness is below a witness that is a type, and `mono_r` retypes at that
one. -/

/-- Everything the lookup returns is below something the lookup returns
that is a type, in whatever sort the graph's outputs live.  Immediate from
`mono_graph` at `f' = f`. -/
theorem Evaluates.bounded (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a : Term} {x : Shape n}
    {r : Bool} (hwf : ShapeFun.WF Δ (Shape.WF Δ) f)
    (hco : ShapeFun.Compat Shape.Compat Δ f f) (hx : Shape.Compat Δ x x)
    (hty : ∀ e ∈ f, Shape.HasType Δ e.out (.sort r))
    {c : Shape n} (h : Evaluates Δ f A a x c) :
    ∃ z, Shape.WF Δ z ∧ Shape.LE Δ c z ∧ Shape.HasType Δ z (.sort r) :=
  have hout : ∀ e ∈ f, Shape.WF Δ e.out := fun e he => (hwf e he).2.2.2
  have ⟨c', hc', hle, hc'ty⟩ :=
    Evaluates.mono_graph hΔ hco hx hout hty (Shape.HasType.join hΔ)
      (ShapeFun.LE.refl_aux hwf) h
  ⟨c', Evaluates.wf hΔ hout hc', hle, hc'ty⟩

/-- Nothing but `⊥` is typed at `⊥`. -/
theorem Shape.HasType.bot_r : ∀ {n} {x : Shape n}, Shape.HasType Δ x .bot → x = .bot := by
  intro n x h
  cases n <;> cases x <;> first | rfl | exact absurd h id

/-- A proposition is inhabited only by `⊥`. -/
theorem Shape.HasType.proofIrrel (hΔ : ⊢ Δ) : ∀ {n} {a x : Shape n},
    Shape.WF Δ a → Shape.WF Δ x →
    Shape.HasType Δ a .prop → Shape.HasType Δ x a → x = .bot := by
  intro n
  induction n with
  | zero =>
    intro a x _ _ ha h
    cases a with
    | bot => exact Shape.HasType.bot_r h
    | sort s => exact Bool.noConfusion (ha : false = true)
  | succ n ih =>
    intro a x hwa hwx ha h
    cases a with
    | bot => exact Shape.HasType.bot_r h
    | sort s => exact Bool.noConfusion (ha : false = true)
    | nat => exact Bool.noConfusion (ha : false = true)
    | sigma => exact Bool.noConfusion (ha.1 : false = true)
    | zero | succ | lam | pair | refl => exact absurd ha id
    | unit t =>
      -- nothing but `⊥` inhabits `unit` at all, so the flag never matters
      cases x <;> first | rfl | exact absurd h id
    | id t A₀ a₀ b₀ =>
      -- `HasType (.id t ..) .prop` forces `t = false`, and `refl` needs `t = true`
      have ht : t = false := by
        cases t with
        | false => rfl
        | true => exact Bool.noConfusion (Bool.eq_true_of_le (r := true) rfl ha)
      subst ht
      cases x with
      | bot => rfl
      | refl w => exact Bool.noConfusion (h : false = true)
      | _ => exact absurd h id
    | forallE A₀ B₀ d f =>
      cases x with
      | bot => rfl
      | lam g =>
        -- a well-formed λ carries real information, so it cannot inhabit a
        -- Π-type whose codomain family is propositional
        have ⟨hne, hnb, hwg, _⟩ := hwx
        have ⟨_, _, _, hwf, hco⟩ := hwa
        cases g with
        | nil => exact absurd rfl hne
        | cons e g' =>
          have he : e ∈ e :: g' := List.mem_cons_self ..
          have ⟨_, _, hwin, hwout⟩ := hwg e he
          have ⟨c, hev, hcty⟩ := h.2.2 e he
          have ⟨z, hwz, hcz, hzty⟩ :=
            Evaluates.bounded hΔ hwf hco (Shape.WF.coherent hwin) ha.2.2 hev
          have hbot : e.out = .bot :=
            ih hwz hwout hzty (Shape.HasType.mono_r hΔ hwout hwz hcty hcz hzty)
          have hb : Shape.IsBot (Shape.bot : Shape n) := by cases n <;> trivial
          exact absurd (hbot ▸ hb) (hnb e he)
      | _ => exact absurd h id

/-! ## Lifting

`Interp` quantifies over `TShape`, so every notion it mentions has to be
transportable along `Shape.lift`.  For the order, well-formedness,
compatibility and the join that transport is an equivalence
(`Shape.lift_le_lift` and friends).  For typing it is **one-directional**:
lifting *up* preserves `HasType`, but the converse fails, because
`Evaluates.lower` can produce a witness at the higher level that is not
the lift of anything — the order on graphs is contravariant in the input,
so a shape below a lifted shape need not itself be a lift.  Master has the
equivalence only because its lookup is a function.

One direction is enough: `TShape.HasType` is defined at the canonical
level and read off at any higher one. -/

theorem Evaluates.lift {Δ : List Term} {n k} (h : n ≤ k) {f : ShapeFun n} {A a : Term}
    {x c : Shape n} (H : Evaluates Δ f A a x c) :
    Evaluates Δ (ShapeFun.lift (Shape.lift k) f) A a (x.lift k) (c.lift k) := by
  induction H with
  | bot => rw [Shape.lift_bot]; exact .bot
  | entry e he hlab hin =>
    exact .entry ⟨e.ty, e.tm, e.inp.lift k, e.out.lift k⟩ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)
      hlab ((Shape.lift_le_lift h).2 hin)
  | lower hwf hle _ ih =>
    exact .lower ((Shape.lift_wf h).2 hwf) ((Shape.lift_le_lift h).2 hle) ih
  | join hc _ _ ih₁ ih₂ =>
    rw [← Shape.lift_join h]
    exact .join ((Shape.lift_compat h).2 hc) ih₁ ih₂

theorem Shape.HasType.lift_mono {Δ : List Term} : ∀ {n k}, n ≤ k → ∀ {m a : Shape n},
    Shape.HasType Δ m a → Shape.HasType Δ (m.lift k) (a.lift k) := by
  intro n
  induction n with
  | zero =>
    intro k _ m a
    cases k with
    | zero => rw [Shape.lift_self, Shape.lift_self]; exact id
    | succ k => cases m <;> cases a <;> exact id
  | succ n ih =>
    intro k h m a
    cases k with
    | zero => exact absurd h (Nat.not_succ_le_zero _)
    | succ k =>
      have h' := Nat.le_of_succ_le_succ h
      have ihs : ∀ {d : Shape n} {r : Bool},
          Shape.HasType Δ d (.sort r) → Shape.HasType Δ (d.lift k) (.sort r) := by
        intro d r hd
        have := ih h' (a := Shape.sort r) hd
        rwa [Shape.lift_sort] at this
      have ihdom : ∀ {f : ShapeFun n} {d : Shape n},
          ShapeFun.HasDom Δ (Shape.HasType Δ) f d →
          ShapeFun.HasDom Δ (Shape.HasType Δ)
            (ShapeFun.lift (Shape.lift k) f) (d.lift k) := by
        intro f d H e'' he''
        obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
        exact ih h' (H e he)
      have ihout : ∀ {f : ShapeFun n} {r : Bool},
          (∀ e ∈ f, Shape.HasType Δ e.out (.sort r)) →
          ∀ e ∈ ShapeFun.lift (Shape.lift k) f, Shape.HasType Δ e.out (.sort r) := by
        intro f r H e'' he''
        obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
        exact ihs (H e he)
      have ihpi : ∀ {d : Shape n} {f : ShapeFun n} {r : Bool},
          (Shape.HasType Δ d .type ∧ ShapeFun.HasDom Δ (Shape.HasType Δ) f d ∧
              ∀ e ∈ f, Shape.HasType Δ e.out (.sort r)) →
          (Shape.HasType Δ (d.lift k) .type ∧
            ShapeFun.HasDom Δ (Shape.HasType Δ) (ShapeFun.lift (Shape.lift k) f) (d.lift k) ∧
            ∀ e ∈ ShapeFun.lift (Shape.lift k) f, Shape.HasType Δ e.out (.sort r)) :=
        fun ⟨h1, h2, h3⟩ => ⟨ihs h1, ihdom h2, ihout h3⟩
      intro H
      cases m with
      | bot =>
        cases a with
        | forallE A B d f => exact ihpi H
        | sigma A B d f => exact ihpi H
        | _ => exact H
      | sort | unit | nat | zero => cases a <;> exact H
      | id t A₀ a₀ b₀ => cases a <;> exact H
      | refl w => cases a <;> exact H
      | succ v =>
        cases a with
        | nat =>
          cases n with
          | zero =>
            have hv : v = Shape.bot := H
            cases k with
            | zero =>
              show Shape.lift 0 v = Shape.bot
              rw [hv, Shape.lift_bot]
            | succ k =>
              show Shape.HasType Δ (v.lift (k+1)) Shape.nat
              rw [hv, Shape.lift_bot]
              trivial
          | succ n =>
            cases k with
            | zero => exact absurd h' (Nat.not_succ_le_zero _)
            | succ k =>
              show Shape.HasType Δ (v.lift (k+1)) Shape.nat
              exact ih h' (a := Shape.nat) H
        | _ => exact H
      | pair ty tm x y =>
        cases a with
        | sigma A B d f =>
          have ⟨c, hev, hcty⟩ := H.2.2
          exact ⟨ihpi H.1, ih h' H.2.1, c.lift k, Evaluates.lift h' hev, ih h' hcty⟩
        | _ => exact H
      | forallE A₀ B₀ d f =>
        cases a with
        | sort r => exact ihpi H
        | _ => exact H
      | sigma A₀ B₀ d f =>
        cases a with
        | sort j => exact ⟨H.1, ihpi H.2⟩
        | _ => exact H
      | lam g =>
        cases a with
        | forallE A₁ B₁ d f =>
          refine ⟨ihpi H.1, ihdom H.2.1, ?_⟩
          intro e'' he''
          obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
          have ⟨c, hev, hcty⟩ := H.2.2 e he
          exact ⟨c.lift k, Evaluates.lift h' hev, ih h' hcty⟩
        | _ => exact H

/-- Typing at the total level: at the canonical level, and (by
`lift_mono`) at every level above it. -/
def TShape.HasType (Δ : List Term) (m a : TShape) : Prop :=
  Shape.HasType Δ (m.2.lift (max m.1 a.1)) (a.2.lift (max m.1 a.1))

/-- One direction only, for the reason given above: a witness at the
canonical level can be read at any higher level. -/
theorem TShape.HasType.def {Δ : List Term} {m a : TShape} {k}
    (h1 : m.1 ≤ k) (h2 : a.1 ≤ k) (H : TShape.HasType Δ m a) :
    Shape.HasType Δ (m.2.lift k) (a.2.lift k) := by
  rw [show m.2.lift k = (m.2.lift (max m.1 a.1)).lift k from
        (Shape.lift_lift (Nat.le_max_left ..)).symm,
      show a.2.lift k = (a.2.lift (max m.1 a.1)).lift k from
        (Shape.lift_lift (Nat.le_max_right ..)).symm]
  exact Shape.HasType.lift_mono (Nat.max_le.2 ⟨h1, h2⟩) H

/-- At a common level the two agree. -/
theorem TShape.HasType.T {Δ : List Term} {n} {m a : Shape n} :
    TShape.HasType Δ (Shape.T m) (Shape.T a) ↔ Shape.HasType Δ m a := by
  show Shape.HasType Δ (m.lift (max n n)) (a.lift (max n n)) ↔ _
  rw [Nat.max_self, Shape.lift_self, Shape.lift_self]

/-- Typing at the total level transports along a typed substitution of the
context.  The level is untouched, so the canonical level is too, and the
statement is `Shape.HasType.subst` with `lift_subst` on each side. -/
theorem TShape.HasType.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {m a : TShape} (H : TShape.HasType Δ m a) :
    TShape.HasType Θ (m.subst τ) (a.subst τ) := by
  show Shape.HasType Θ (Shape.lift (max m.1 a.1) (m.2.subst τ))
    (Shape.lift (max m.1 a.1) (a.2.subst τ))
  rw [Shape.lift_subst, Shape.lift_subst]
  exact Shape.HasType.subst hΘ W H

/-- Cumulativity at the total level. -/
theorem TShape.HasType.cumul {Δ : List Term} {a : TShape} {r s : Bool}
    (h : TShape.HasType Δ a (TShape.sort r)) (hrs : r ≤ s) :
    TShape.HasType Δ a (TShape.sort s) := by
  show Shape.HasType Δ (Shape.lift (max a.1 0) a.2) (Shape.lift (max a.1 0) (Shape.sort s))
  rw [Shape.lift_sort]
  exact Shape.HasType.cumul (by rw [← Shape.lift_sort (m := max a.1 0)]; exact h) hrs
