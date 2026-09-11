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
  | join {y z w} : Shape.Join Δ y z w → Evaluates Δ f A a x y → Evaluates Δ f A a x z →
      Evaluates Δ f A a x w

/-- Every entry of a graph is dominated by one whose input is typed at the
domain shape (master's `HasDom`, with the label premise added). -/
def ShapeFun.HasDom (Δ : List Term) (T : Shape n → Shape n → Prop)
    (f : ShapeFun n) (d : Shape n) : Prop :=
  ∀ e ∈ f, ∃ e' ∈ f, LabelEq Δ e'.ty e'.tm e.ty e.tm ∧
    Shape.LE Δ e'.inp e.inp ∧ Shape.LE Δ e.out e'.out ∧ T e'.inp d

/-- `m` is a well-typed inhabitant of the type-shape `a`.  Structural
recursion on the level. -/
def Shape.HasType (Δ : List Term) : ∀ {n}, Shape n → Shape n → Prop
  -- `⊥` inhabits every type; a type shape is a type when its parts are
  | 0, .bot, _ => True
  | 0, .sort _, .sort j => j = true
  | 0, _, _ => False
  | _+1, .bot, _ => True
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
  -- a λ-shape inhabits a Π-type when every entry's output is typed at a
  -- code the codomain family yields at that entry's label and input
  | _+1, .lam g, .forallE _ _ d f =>
      ShapeFun.HasDom Δ (HasType Δ) g d ∧
        ∀ e ∈ g, ∃ c, Evaluates Δ f e.ty e.tm e.inp c ∧ HasType Δ e.out c
  -- TODO(Σ): the codomain family is a *labelled* graph, so a `pair` shape
  -- must carry the term label of its first component, exactly as `forallE`
  -- and `lam` do, before the second component can be typed at
  -- `Evaluates Δ f (label) x`.  Σ is deferred (§5), so only the first
  -- component is checked here.
  | _+1, .pair x _, .sigma _ _ d _ => HasType Δ x d
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

/-- `⊥` inhabits every shape. -/
theorem Shape.HasType.bot {a : Shape n} : Shape.HasType Δ .bot a := by
  cases n <;> trivial

end DomainSemantics
