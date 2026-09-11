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
  | 1, .succ v, .nat => v = .bot
  | _+2, .succ v, .nat => HasType Δ v .nat
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

/-! ## Codes

`IsCode r a` says `a` is a code of universe `r`.  It is deliberately *not*
`HasType · (sort r)`: it omits the `HasDom` condition, and that is what
makes it **downward closed** (`IsCode.of_le`).  Downward closure is
essential, because `Evaluates` closes under `lower`, so anything read out
of a family graph has to stay a code.  The other repo splits these the
same way (`IsCode` in `Basis/UniverseShape.lean` versus its decoder).

Following master, the `Bool` order is used where a proof-irrelevant former
also counts as a proof-relevant code (`unit`, `id`). -/
def Shape.IsCode : ∀ {n}, Bool → Shape n → Prop
  | 0, _, .bot => True
  | 0, r, .sort _ => r = true
  | _+1, _, .bot => True
  | _+1, r, .sort _ => r = true
  | _+1, r, .unit s => s ≤ r
  | _+1, r, .nat => r = true
  | _+1, r, .id s _ _ _ => s ≤ r
  | _+1, r, .sigma _ _ _ _ => r = true
  | _+1, true, .forallE _ _ _ _ => True
  | _+1, false, .forallE _ _ _ f => ∀ e ∈ f, IsCode false e.out
  -- an information-free λ-shape is a code, as it is `⊥`
  | _+1, _, .lam f => ∀ e ∈ f, Shape.IsBot e.out
  | _+1, _, _ => False

theorem Shape.IsCode.bot {r : Bool} : Shape.IsCode (n := n) r .bot := by
  cases n <;> trivial

/-- Codes are downward closed.  This is the property `HasType · (sort r)`
would *not* have, since `HasDom` is a condition internal to a graph and so
is not inherited by a graph that merely sits below it. -/
theorem Shape.IsCode.of_le (hΔ : ⊢ Δ) : ∀ {n} {r : Bool} {a b : Shape n},
    Shape.LE Δ a b → Shape.IsCode r b → Shape.IsCode r a := by
  intro n
  induction n with
  | zero => intro r a b hab hb; cases a <;> cases b <;> simp_all [Shape.IsCode, Shape.LE]
  | succ n ih =>
    intro r a b hab hb
    cases a with
    | bot => trivial
    | lam f =>
      cases b with
      | lam g =>
        intro e he
        match hab e he with
        | .inl hbot => exact Shape.le_bot_iff.1 hbot
        | .inr ⟨e', he', _, _, hout⟩ =>
          exact Shape.le_bot_iff.1 (Shape.LE.trans_aux hΔ hout (Shape.le_bot_iff.2 (hb e' he')))
      | _ => exact fun e he => Shape.le_bot_iff.1 (hab e he)
    | forallE A B d f =>
      cases r with
      | true => trivial
      | false =>
        cases b with
        | forallE A' B' d' f' =>
          intro e he
          match hab.2.2 e he with
          | .inl hbot => exact ih hbot Shape.IsCode.bot
          | .inr ⟨e', he', _, _, hout⟩ => exact ih hout (hb e' he')
        | _ => exact absurd hab id
    | sort s => cases b <;> first | exact absurd hab id | exact hb
    | unit s =>
      cases b with
      | unit s' => exact (show s = s' from hab) ▸ hb
      | _ => exact absurd hab id
    | nat => cases b <;> first | exact absurd hab id | exact hb
    | zero => cases b <;> first | exact absurd hab id | exact hb
    | succ v => cases b <;> first | exact absurd hab id | exact hb
    | refl w => cases b <;> first | exact absurd hab id | exact hb
    | pair x y => cases b <;> first | exact absurd hab id | exact hb
    | sigma A B d f => cases b <;> first | exact absurd hab id | exact hb
    | id s A a' b' =>
      cases b with
      | id s' A'' a'' b'' => exact hab.1 ▸ hb
      | _ => exact absurd hab id

/-- `⊥` inhabits every shape. -/
theorem Shape.HasType.bot {a : Shape n} : Shape.HasType Δ .bot a := by
  cases n <;> trivial

end DomainSemantics
