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

/-- Relational graph lookup: `Evaluates Δ f A a x y` says `y` approximates
the result of applying the graph `f`, at the argument label `(A, a)`, to an
input at least `x`.  It is the set of outputs of matching entries, closed
downwards and under compatible joins — the other repo's `Evaluates`.

Replacing `ShapeFun.app` (a function) by this (a relation) is what lets us
drop saturation: the join of several matching entries is available here
without having to be stored in the graph. -/
inductive Evaluates (Δ : List Term) {n} (f : ShapeFun n) (A a : Term) (x : Shape n) :
    Shape n → Prop where
  | bot : Evaluates Δ f A a x .bot
  | entry (e : Entry (Shape n)) : e ∈ f → LabelEq Δ e.ty e.tm A a →
      Shape.LE Δ e.inp x → Evaluates Δ f A a x e.out
  | lower {y z} : Shape.LE Δ y z → Evaluates Δ f A a x z → Evaluates Δ f A a x y
  -- now that the `join` *function* is correct (no information-free λ-shapes),
  -- closing under it rather than under the `Join` relation is what makes
  -- `Evaluates` transport along a substitution: `join` commutes with
  -- substitution on the nose, whereas `Join Θ` quantifies over more shapes
  -- than the image of the substitution
  | join {y z} : Shape.Compat Δ y z → Evaluates Δ f A a x y → Evaluates Δ f A a x z →
      Evaluates Δ f A a x (y.join z)

/-- Every entry of a graph is dominated by one whose input is typed at the
domain shape (master's `HasDom`, with the label premise added). -/
def ShapeFun.HasDom (Δ : List Term) (T : Shape n → Shape n → Prop)
    (f : ShapeFun n) (d : Shape n) : Prop :=
  ∀ e ∈ f, ∃ e' ∈ f, LabelEq Δ e'.ty e'.tm e.ty e.tm ∧
    Shape.LE Δ e'.inp e.inp ∧ Shape.LE Δ e.out e'.out ∧ T e'.inp d

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
      ShapeFun.HasDom Δ (HasType Δ) f d ∧ ∀ e ∈ f, HasType Δ e.out .type
  | _+1, .bot, .sigma _ _ d f =>
      ShapeFun.HasDom Δ (HasType Δ) f d ∧ ∀ e ∈ f, HasType Δ e.out .type
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
  | _+1, .forallE _ _ d f, .sort r =>
      ShapeFun.HasDom Δ (HasType Δ) f d ∧ ∀ e ∈ f, HasType Δ e.out (.sort r)
  | _+1, .sigma _ _ d f, .sort j =>
      j = true ∧ ShapeFun.HasDom Δ (HasType Δ) f d ∧ ∀ e ∈ f, HasType Δ e.out .type
  -- a λ-shape inhabits a Π-type when that Π-type is well-formed and every
  -- entry's output is typed at a code the codomain family yields at that
  -- entry's label and input
  | _+1, .lam g, .forallE _ _ d f =>
      (ShapeFun.HasDom Δ (HasType Δ) f d ∧ ∀ e ∈ f, HasType Δ e.out .type) ∧
        ShapeFun.HasDom Δ (HasType Δ) g d ∧
        ∀ e ∈ g, ∃ c, Evaluates Δ f e.ty e.tm e.inp c ∧ HasType Δ e.out c
  -- TODO(Σ): the codomain family is a *labelled* graph, so a `pair` shape
  -- must carry the term label of its first component, exactly as `forallE`
  -- and `lam` do, before the second component can be typed at
  -- `Evaluates Δ f (label) x`.  Σ is deferred (§5), so only the first
  -- component is checked here.
  | _+1, .pair x _, .sigma _ _ d f =>
      (ShapeFun.HasDom Δ (HasType Δ) f d ∧ ∀ e ∈ f, HasType Δ e.out .type) ∧
        HasType Δ x d
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
    | forallE A B d f => exact ⟨h.1, fun e he => ih (h.2 e he) hrs⟩
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
  | lower hle _ ih => exact .lower (Shape.LE.subst hΘ W hle) ih
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
  have ⟨g, hg, hlab, hin, hout, hty⟩ := h e he
  exact ⟨_, ShapeFun.mem_subst.2 ⟨g, hg, rfl⟩, hlab.subst hΘ W,
    Shape.LE.subst hΘ W hin, Shape.LE.subst hΘ W hout, ih hty⟩

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
        (ShapeFun.HasDom Δ (Shape.HasType Δ) f d ∧ ∀ e ∈ f, Shape.HasType Δ e.out .type) →
        (ShapeFun.HasDom Θ (Shape.HasType Θ) (ShapeFun.subst (Shape.subst · τ) τ f)
            (d.subst τ) ∧
          ∀ e ∈ ShapeFun.subst (Shape.subst · τ) τ f, Shape.HasType Θ e.out .type) := by
      intro f d h
      refine ⟨ShapeFun.HasDom.subst_of hΘ W ih h.1, fun e' he' => ?_⟩
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      simpa using ih (h.2 e he)
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
      | sort r => exact ⟨ShapeFun.HasDom.subst_of hΘ W ih h.1, fun e' he' => by
          obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
          simpa using ih (h.2 e he)⟩
      | _ => exact absurd h id
    | sigma A B d f =>
      cases a with
      | sort r => exact ⟨h.1, ShapeFun.HasDom.subst_of hΘ W ih h.2.1, fun e' he' => by
          obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
          simpa using ih (h.2.2 e he)⟩
      | _ => exact absurd h id
    | lam g =>
      cases a with
      | forallE A B d f =>
        refine ⟨hpi h.1, ShapeFun.HasDom.subst_of hΘ W ih h.2.1, fun e' he' => ?_⟩
        obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
        have ⟨c, hev, hty⟩ := h.2.2 e he
        exact ⟨c.subst τ, Evaluates.subst hΘ W hev, ih hty⟩
      | _ => exact absurd h id
    | pair x y =>
      cases a with
      | sigma A B d f => exact ⟨hpi h.1, ih h.2⟩
      | _ => exact absurd h id

end DomainSemantics
