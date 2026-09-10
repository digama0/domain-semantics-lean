import DomainSemantics.Label

/-! # Labelled shapes

The semantic domain of the gluing model. This is `ShapeOld.lean`'s
level-graded `Shape n` with two changes:

* a function graph is a `List (Entry (Shape n))` rather than a
  `List (Shape n × Shape n)`, where an `Entry` carries the **syntactic
  argument** `(ty, tm)` it is about alongside the input and output shapes; and
* `forallE`/`sigma` carry the syntactic pair `(A, B)` of the type they
  approximate, and `id` carries its syntactic triple.

The labels are what glue syntax into the domain: application looks a graph
up at the label of the argument, and Π-injectivity is then a projection out
of the Π-label. See `presheaf-plan.md`.

Because labels are compared up to definitional equality in a context, the
order `Shape.LE Δ` is context-indexed and `Prop`-valued (the old `ble` and
`Compat` were `Bool`-valued). The saturation conditions of the old
`ShapeFun.WF` (a `⊥`-input entry, closure under compatible joins, monotone
samples) are gone: graph lookup is now the join of *all* matching entries
(`Evaluates`, in a later file) rather than a search for a maximal one. -/

namespace DomainSemantics

/-- One entry of a function graph: applied to the syntactic argument `tm`
of type `ty`, on input at least `inp` the result is at least `out`.

The type `ty` is part of the label, not decoration: `Δ ⊢ tm ≡ tm' : ty` is
how two entries are seen to be about the same argument, and our definitional
equality is typed, so the type has to be stored for that judgment to be
stateable.  Dropping it (`TmEq` in `Label.lean`) makes label equality
`∃ A, Δ ⊢ a ≡ a' : A`, whose transitivity needs uniqueness of the type of
the middle term — the theorem this model exists to prove. -/
structure Entry (α : Type) where
  ty : Term
  tm : Term
  inp : α
  out : α
  deriving Inhabited

namespace Entry

/-- Map the shape components of an entry, keeping the label. -/
def map (f : α → β) (e : Entry α) : Entry β := ⟨e.ty, e.tm, f e.inp, f e.out⟩

@[simp] theorem map_ty (f : α → β) (e : Entry α) : (e.map f).ty = e.ty := rfl
@[simp] theorem map_tm (f : α → β) (e : Entry α) : (e.map f).tm = e.tm := rfl
@[simp] theorem map_inp (f : α → β) (e : Entry α) : (e.map f).inp = f e.inp := rfl
@[simp] theorem map_out (f : α → β) (e : Entry α) : (e.map f).out = f e.out := rfl

/-- Act on the label by a substitution, keeping the shapes. -/
def substTm (e : Entry α) (σ : Subst) : Entry α :=
  ⟨e.ty.subst σ, e.tm.subst σ, e.inp, e.out⟩

end Entry

/-- Ground (level-0) shapes: the bottom element and a sort indexed by
`rel : Bool`. All function-shape information lives at level ≥ 1. -/
inductive Shape0 : Type where
  | bot : Shape0
  | sort (rel : Bool) : Shape0

/-- One step of the level-graded shape constructor. Compared with
`ShapeOld.lean`: graphs are lists of `Entry`, and `forallE`/`sigma`/`id`
carry syntactic labels. `refl` keeps a shape argument, so the
proof-relevant identity type stays proof-relevant. -/
inductive ShapeS (Shape : Type) : Type where
  | bot : ShapeS Shape
  | sort (rel : Bool) : ShapeS Shape
  | unit (rel : Bool) : ShapeS Shape
  | forallE (A B : Term) : Shape → List (Entry Shape) → ShapeS Shape
  | lam : List (Entry Shape) → ShapeS Shape
  | sigma (A B : Term) : Shape → List (Entry Shape) → ShapeS Shape
  | pair : Shape → Shape → ShapeS Shape
  | nat : ShapeS Shape
  | zero : ShapeS Shape
  | succ (n : Shape) : ShapeS Shape
  | id (rel : Bool) (A a b : Term) : ShapeS Shape
  | refl : Shape → ShapeS Shape

/-- The graded shape domain: `Shape 0 = Shape0`, `Shape (n+1) = ShapeS (Shape n)`. -/
def Shape : Nat → Type
  | 0 => Shape0
  | n + 1 => ShapeS (Shape n)

/-- A function shape at level `n`: a finite labelled graph. -/
abbrev ShapeFun (n) := List (Entry (Shape n))

@[match_pattern] def Shape.bot : ∀ {n}, Shape n
  | 0 => Shape0.bot
  | _+1 => ShapeS.bot

@[match_pattern] def Shape.sort (rel : Bool) : ∀ {n}, Shape n
  | 0 => Shape0.sort rel
  | _+1 => ShapeS.sort rel

@[match_pattern] abbrev Shape.nat {n} : Shape (n+1) := ShapeS.nat
@[match_pattern] abbrev Shape.zero {n} : Shape (n+1) := ShapeS.zero
@[match_pattern] abbrev Shape.succ {n} (v : Shape n) : Shape (n+1) := ShapeS.succ v
@[match_pattern] def Shape.refl {n} (w : Shape n) : Shape (n+1) := ShapeS.refl w

abbrev Shape.type : Shape n := .sort true
abbrev Shape.prop : Shape n := .sort false

instance : Inhabited (Shape n) := ⟨.bot⟩

/-! ## Bottom shapes

A λ-shape all of whose outputs are bottom carries no information, so it is
identified with `⊥` by the order (the `collapse` case of `LE`). This
replaces the old `NonZero`/`lam'` normalisation. -/

/-- `IsBot s`: `s` is `⊥`, or a graph with only bottom outputs. -/
def Shape.IsBot : ∀ {n}, Shape n → Prop
  | 0, .bot => True
  | 0, .sort _ => False
  | _+1, .bot => True
  | _+1, .lam f => ∀ e ∈ f, IsBot e.out
  | _+1, _ => False

@[simp] theorem Shape.isBot_bot : (Shape.bot (n := n)).IsBot := by cases n <;> trivial

@[simp] theorem Shape.isBot_lam {f : ShapeFun n} :
    Shape.IsBot (n := n+1) (ShapeS.lam f) ↔ ∀ e ∈ f, e.out.IsBot := Iff.rfl

/-! ## Well-formed shapes

Labels are compared by plain definitional equality, which is reflexive
only on well-typed terms.  `Shape.WF Δ` says every label occurring in a
shape is well-typed in `Δ`; it is the hypothesis of `Shape.LE.refl`.
Note this is a genuine invariant of the model (interpretations only ever
produce well-typed labels), unlike the saturation conditions of the old
`ShapeFun.WF`, which are gone. -/

/-- Every entry of a graph has a well-typed label and well-formed shapes. -/
def ShapeFun.WF (Δ : List Term) (W : Shape n → Prop) (f : ShapeFun n) : Prop :=
  ∀ e ∈ f, (∃ u, Δ ⊢ e.ty : .sort u) ∧ Δ ⊢ e.tm : e.ty ∧ W e.inp ∧ W e.out

/-- Every label occurring in the shape is well-typed in `Δ`. -/
def Shape.WF (Δ : List Term) : ∀ {n}, Shape n → Prop
  | 0, .bot => True
  | 0, .sort _ => True
  | _+1, .bot => True
  | _+1, .sort _ => True
  | _+1, .unit _ => True
  | _+1, .nat => True
  | _+1, .zero => True
  | _+1, .succ v => WF Δ v
  | _+1, .refl w => WF Δ w
  | _+1, .id _ A a b => (∃ u, Δ ⊢ A : .sort u) ∧ Δ ⊢ a : A ∧ Δ ⊢ b : A
  | _+1, .forallE A B d f =>
      (∃ u, Δ ⊢ A : .sort u) ∧ (∃ v, A :: Δ ⊢ B : .sort v) ∧
        WF Δ d ∧ ShapeFun.WF Δ (WF Δ) f
  | _+1, .sigma A B d f =>
      (∃ u, Δ ⊢ A : .sort u) ∧ (∃ v, A :: Δ ⊢ B : .sort v) ∧
        WF Δ d ∧ ShapeFun.WF Δ (WF Δ) f
  | _+1, .pair a b => WF Δ a ∧ WF Δ b
  | _+1, .lam f => ShapeFun.WF Δ (WF Δ) f

/-! ## The order

`Shape.LE Δ` compares labels up to definitional equality in `Δ`, so it is
indexed by a context and lives in `Prop`. An entry is covered when some
entry of the larger graph has a definitionally equal label, a smaller
input and a larger output; an entry with a bottom output is covered
vacuously. -/

/-- Entry-wise coverage of one graph by another, parameterised by the
order `R` at the previous level. -/
def ShapeFun.LE (Δ : List Term) (R : Shape n → Shape n → Prop) (f f' : ShapeFun n) : Prop :=
  ∀ e ∈ f, R e.out .bot ∨
    ∃ e' ∈ f', LabelEq Δ e'.ty e'.tm e.ty e.tm ∧ R e'.inp e.inp ∧ R e.out e'.out

/-- The approximation order, by recursion on the level. -/
def Shape.LE (Δ : List Term) : ∀ {n}, Shape n → Shape n → Prop
  | 0, .bot, _ => True
  | 0, .sort r, .sort r' => r = r'
  | 0, _, _ => False
  | _+1, .bot, _ => True
  | _+1, .sort r, .sort r' => r = r'
  | _+1, .unit r, .unit r' => r = r'
  | _+1, .nat, .nat => True
  | _+1, .zero, .zero => True
  | _+1, .succ v, .succ v' => LE Δ v v'
  | _+1, .refl w, .refl w' => LE Δ w w'
  | _+1, .id r A a b, .id r' A' a' b' => r = r' ∧ IdLabelEq Δ A a b A' a' b'
  | _+1, .forallE A B d f, .forallE A' B' d' f' =>
      PiLabelEq Δ A B A' B' ∧ LE Δ d d' ∧ ShapeFun.LE Δ (LE Δ) f f'
  | _+1, .sigma A B d f, .sigma A' B' d' f' =>
      PiLabelEq Δ A B A' B' ∧ LE Δ d d' ∧ ShapeFun.LE Δ (LE Δ) f f'
  | _+1, .pair a b, .pair a' b' => LE Δ a a' ∧ LE Δ b b'
  | _+1, .lam f, .lam f' => ShapeFun.LE Δ (LE Δ) f f'
  -- a λ-shape with only bottom outputs is below anything
  | _+1, .lam f, _ => ∀ e ∈ f, LE Δ e.out .bot
  | _+1, _, _ => False

@[simp] theorem Shape.LE.bot {s : Shape n} : Shape.LE Δ .bot s := by
  cases n <;> trivial

theorem Shape.LE.refl_aux : ∀ {n} {s : Shape n}, Shape.WF Δ s → Shape.LE Δ s s := by
  intro n
  induction n with
  | zero => intro s _; cases s <;> trivial
  | succ n ih =>
    intro s hs
    have hfun : ∀ f : ShapeFun n, ShapeFun.WF Δ (Shape.WF Δ) f →
        ShapeFun.LE Δ (Shape.LE Δ) f f := fun f hf e he =>
      have ⟨⟨_, hty⟩, htm, hin, hout⟩ := hf e he
      .inr ⟨e, he, LabelEq.refl hty htm, ih hin, ih hout⟩
    cases s with
    | bot => trivial
    | sort => rfl
    | unit => rfl
    | nat => trivial
    | zero => trivial
    | succ v => exact ih hs
    | refl w => exact ih hs
    | id =>
      have ⟨⟨_, hA⟩, ha, hb⟩ := hs
      exact ⟨rfl, IdLabelEq.refl hA ha hb⟩
    | forallE A B d f =>
      have ⟨⟨_, hA⟩, ⟨_, hB⟩, hd, hf⟩ := hs
      exact ⟨PiLabelEq.refl hA hB, ih hd, hfun f hf⟩
    | sigma A B d f =>
      have ⟨⟨_, hA⟩, ⟨_, hB⟩, hd, hf⟩ := hs
      exact ⟨PiLabelEq.refl hA hB, ih hd, hfun f hf⟩
    | pair a b => exact ⟨ih hs.1, ih hs.2⟩
    | lam f => exact hfun f hs

/-- Composing coverage of graphs.  This is the step that forces the label
to carry its type: the two `LabelEq` proofs are chained by
`LabelEq.trans`, whose sort-typed component is handled by `IsDefEq.trans'`.
With a type-free label (`TmEq`) this is exactly where the argument stalls. -/
theorem ShapeFun.LE.trans_of {Δ : List Term} {n} {f f' f'' : ShapeFun n}
    (ih : ∀ {a b c : Shape n}, Shape.LE Δ a b → Shape.LE Δ b c → Shape.LE Δ a c)
    (h₁ : ShapeFun.LE Δ (Shape.LE Δ) f f') (h₂ : ShapeFun.LE Δ (Shape.LE Δ) f' f'') :
    ShapeFun.LE Δ (Shape.LE Δ) f f'' := by
  intro e he
  match h₁ e he with
  | .inl hb => exact .inl hb
  | .inr ⟨e', he', hlab, hin, hout⟩ =>
    match h₂ e' he' with
    | .inl hb' => exact .inl (ih hout hb')
    | .inr ⟨e'', he'', hlab', hin', hout'⟩ =>
      exact .inr ⟨e'', he'', hlab'.trans hlab, ih hin' hin, ih hout hout'⟩

/-- Transitivity of the order. -/
theorem Shape.LE.trans_aux (hΔ : ⊢ Δ) :
    ∀ {n} {s t u : Shape n}, Shape.LE Δ s t → Shape.LE Δ t u → Shape.LE Δ s u := by
  intro n
  induction n with
  | zero =>
    intro s t u h₁ h₂
    cases s <;> cases t <;> cases u <;> simp_all [Shape.LE]
  | succ n ih =>
    intro s t u h₁ h₂
    cases s with
    | bot => trivial
    | lam f =>
      cases t with
      | lam f' =>
        cases u with
        | lam f'' => exact ShapeFun.LE.trans_of ih h₁ h₂
        | _ =>
          intro e he
          match h₁ e he with
          | .inl hb => exact hb
          | .inr ⟨e', he', _, _, hout⟩ => exact ih hout (h₂ e' he')
      | _ =>
        cases u with
        | lam f'' => exact fun e he => .inl (h₁ e he)
        | _ => exact h₁
    | succ v => cases t <;> cases u <;> first | exact absurd h₁ id | exact absurd h₂ id
                                              | exact ih h₁ h₂
    | refl w => cases t <;> cases u <;> first | exact absurd h₁ id | exact absurd h₂ id
                                              | exact ih h₁ h₂
    | pair a b => cases t <;> cases u <;> first | exact absurd h₁ id | exact absurd h₂ id
                                                | exact ⟨ih h₁.1 h₂.1, ih h₁.2 h₂.2⟩
    | id r A a b =>
      cases t <;> cases u <;> first | exact absurd h₁ id | exact absurd h₂ id
                                    | exact ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
    | forallE A B d f =>
      cases t <;> cases u <;> first | exact absurd h₁ id | exact absurd h₂ id
                                    | exact ⟨h₁.1.trans hΔ h₂.1, ih h₁.2.1 h₂.2.1,
                                        ShapeFun.LE.trans_of ih h₁.2.2 h₂.2.2⟩
    | sigma A B d f =>
      cases t <;> cases u <;> first | exact absurd h₁ id | exact absurd h₂ id
                                    | exact ⟨h₁.1.trans hΔ h₂.1, ih h₁.2.1 h₂.2.1,
                                        ShapeFun.LE.trans_of ih h₁.2.2 h₂.2.2⟩
    | _ => cases t <;> cases u <;> simp_all [Shape.LE]

end DomainSemantics
