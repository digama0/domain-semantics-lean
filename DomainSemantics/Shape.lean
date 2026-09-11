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

@[match_pattern] abbrev Shape.unit {n} (rel : Bool) : Shape (n+1) := ShapeS.unit rel
@[match_pattern] abbrev Shape.lam {n} (f : List (Entry (Shape n))) : Shape (n+1) := ShapeS.lam f
@[match_pattern] abbrev Shape.nat {n} : Shape (n+1) := ShapeS.nat
@[match_pattern] abbrev Shape.zero {n} : Shape (n+1) := ShapeS.zero
@[match_pattern] abbrev Shape.succ {n} (v : Shape n) : Shape (n+1) := ShapeS.succ v
@[match_pattern] def Shape.refl {n} (w : Shape n) : Shape (n+1) := ShapeS.refl w

abbrev Shape.type : Shape n := .sort true
abbrev Shape.prop : Shape n := .sort false

instance : Inhabited (Shape n) := ⟨.bot⟩

/-! ## Lifting between levels

Master's `lift`, with labels carried through unchanged.  Lifting *down*
(to a level too small to hold the shape) collapses to `⊥`, as it does
there.  This is what lets the level index be hidden behind a total shape
type `TShape`, which the interpretation quantifies over. -/

def ShapeFun.lift (g : α → β) (f : List (Entry α)) : List (Entry β) :=
  f.map fun e => ⟨e.ty, e.tm, g e.inp, g e.out⟩

@[simp] theorem ShapeFun.mem_lift {g : α → β} {f} {e' : Entry β} :
    e' ∈ ShapeFun.lift g f ↔ ∃ e ∈ f, e' = ⟨e.ty, e.tm, g e.inp, g e.out⟩ := by
  simp [ShapeFun.lift, eq_comm]

def Shape.lift : ∀ {n} (m : Nat), Shape n → Shape m
  | 0, _, .sort r | _+1, _, .sort r => .sort r
  | 0, _, .bot | _+1, _, .bot | _, 0, _ => .bot
  | _+1, _+1, .unit r => .unit r
  | _+1, _+1, .forallE A B d f => .forallE A B (lift _ d) (ShapeFun.lift (lift _) f)
  | _+1, _+1, .lam f => .lam (ShapeFun.lift (lift _) f)
  | _+1, _+1, .sigma A B d f => .sigma A B (lift _ d) (ShapeFun.lift (lift _) f)
  | _+1, _+1, .pair a b => .pair (lift _ a) (lift _ b)
  | _+1, _+1, .nat => .nat
  | _+1, _+1, .zero => .zero
  | _+1, _+1, .succ v => .succ (lift _ v)
  | _+1, _+1, .id r A a b => .id r A a b
  | _+1, _+1, .refl w => .refl (lift _ w)

@[simp] theorem Shape.lift_bot {n m : Nat} : (Shape.bot : Shape n).lift m = .bot := by
  cases n <;> [rfl; cases m <;> rfl]

@[simp] theorem Shape.lift_sort {n m : Nat} {r : Bool} :
    (Shape.sort r : Shape n).lift m = .sort r := by
  cases n <;> [rfl; cases m <;> rfl]

theorem Shape.lift_self : ∀ {n} {s : Shape n}, s.lift n = s := by
  intro n
  induction n with
  | zero => intro s; cases s <;> rfl
  | succ n ih =>
    intro s
    have hf : ∀ f : ShapeFun n, ShapeFun.lift (Shape.lift n) f = f := by
      intro f
      induction f with
      | nil => rfl
      | cons e f ihf =>
        simp only [ShapeFun.lift, List.map_cons] at ihf ⊢
        rw [ih, ih, ihf]
    cases s with
    | bot | sort | unit | nat | zero | id => rfl
    | succ v => show ShapeS.succ _ = _; rw [ih]
    | refl w => show ShapeS.refl _ = _; rw [ih]
    | pair a b => show ShapeS.pair _ _ = _; rw [ih, ih]
    | lam f => show ShapeS.lam _ = _; rw [hf]
    | forallE A B d f => show ShapeS.forallE _ _ _ _ = _; rw [ih, hf]
    | sigma A B d f => show ShapeS.sigma _ _ _ _ = _; rw [ih, hf]

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

/-! ## Substitution

Shapes carry syntactic labels, so a substitution acts on them.  The action
is purely structural (the semantic components are untouched apart from
recursing), and since it does not inspect the labels it needs no typing
hypotheses; those appear only in the *preservation* lemmas below, which is
the whole "no quotient, preservation lemmas instead" policy in miniature.
Note `B` in a Π/Σ label lives under a binder, hence `σ.lift`. -/

/-- Substitute in a graph, given the action on the shapes at this level. -/
def ShapeFun.subst (g : Shape n → Shape n) (σ : Subst) (f : ShapeFun n) : ShapeFun n :=
  f.map fun e => ⟨e.ty.subst σ, e.tm.subst σ, g e.inp, g e.out⟩

def Shape.subst : ∀ {n}, Shape n → Subst → Shape n
  | 0, .bot, _ => .bot
  | 0, .sort r, _ => .sort r
  | _+1, .bot, _ => .bot
  | _+1, .sort r, _ => .sort r
  | _+1, .unit r, _ => .unit r
  | _+1, .nat, _ => .nat
  | _+1, .zero, _ => .zero
  | _+1, .succ v, σ => .succ (subst v σ)
  | _+1, .refl w, σ => .refl (subst w σ)
  | _+1, .id r A a b, σ => .id r (A.subst σ) (a.subst σ) (b.subst σ)
  | _+1, .forallE A B d f, σ =>
      .forallE (A.subst σ) (B.subst σ.lift) (subst d σ) (ShapeFun.subst (subst · σ) σ f)
  | _+1, .sigma A B d f, σ =>
      .sigma (A.subst σ) (B.subst σ.lift) (subst d σ) (ShapeFun.subst (subst · σ) σ f)
  | _+1, .pair a b, σ => .pair (subst a σ) (subst b σ)
  | _+1, .lam f, σ => .lam (ShapeFun.subst (subst · σ) σ f)

@[simp] theorem Shape.subst_bot {n} {τ : Subst} : (Shape.bot (n := n)).subst τ = .bot := by
  cases n <;> rfl

@[simp] theorem Shape.subst_sort {n} {r : Bool} {τ : Subst} :
    (Shape.sort r : Shape n).subst τ = .sort r := by cases n <;> rfl

@[simp] theorem ShapeFun.mem_subst {g : Shape n → Shape n} {σ f} {e' : Entry (Shape n)} :
    e' ∈ ShapeFun.subst g σ f ↔
      ∃ e ∈ f, e' = ⟨e.ty.subst σ, e.tm.subst σ, g e.inp, g e.out⟩ := by
  simp [ShapeFun.subst, eq_comm]

/-- Entries with definitionally equal labels and compatible inputs have
compatible outputs — **at every later typed stage**.

The quantification over later stages is what makes the condition stable
under substitution, and it sits inside the graph clause only, exactly as in
the other repo's `Shape.Compatible σ` (`Basis/InternalCoherence.lean`),
whose `lam` clause likewise reads `∀ i j Γ₂ (σ₁ : Γ₂ ⟶ _), … (σ₁ ≫ σ) …`.
It is needed because a substitution can *create* label equalities — two
distinct variables becoming definitionally equal — so a merely local
condition would say nothing about the entries that then collide. -/
def ShapeFun.Compat (R : List Term → Shape n → Shape n → Prop)
    (Δ : List Term) (f f' : ShapeFun n) : Prop :=
  ∀ e ∈ f, ∀ e' ∈ f', ∀ (Θ : List Term) (τ : Subst), ⊢ Θ → Ctx.SubstEq Θ τ τ Δ →
    LabelEq Θ (e.ty.subst τ) (e.tm.subst τ) (e'.ty.subst τ) (e'.tm.subst τ) →
    R Θ (e.inp.subst τ) (e'.inp.subst τ) → R Θ (e.out.subst τ) (e'.out.subst τ)

def Shape.Compat : ∀ {n}, List Term → Shape n → Shape n → Prop
  | 0, _, .bot, _ => True
  | 0, _, _, .bot => True
  | 0, _, .sort r, .sort r' => r = r'
  | _+1, _, .bot, _ => True
  | _+1, _, _, .bot => True
  | _+1, Δ, .lam f, .lam f' => ShapeFun.Compat Compat Δ f f'
  | _+1, _, .sort r, .sort r' => r = r'
  | _+1, _, .unit r, .unit r' => r = r'
  | _+1, _, .nat, .nat => True
  | _+1, _, .zero, .zero => True
  | _+1, Δ, .succ v, .succ v' => Compat Δ v v'
  | _+1, Δ, .refl w, .refl w' => Compat Δ w w'
  | _+1, Δ, .pair a b, .pair a' b' => Compat Δ a a' ∧ Compat Δ b b'
  | _+1, Δ, .id r A a b, .id r' A' a' b' => r = r' ∧ IdLabelEq Δ A a b A' a' b'
  | _+1, Δ, .forallE A B d f, .forallE A' B' d' f' =>
      PiLabelEq Δ A B A' B' ∧ Compat Δ d d' ∧ ShapeFun.Compat Compat Δ f f'
  | _+1, Δ, .sigma A B d f, .sigma A' B' d' f' =>
      PiLabelEq Δ A B A' B' ∧ Compat Δ d d' ∧ ShapeFun.Compat Compat Δ f f'
  | _+1, _, _, _ => False

/-! ## Well-formed shapes

Labels are compared by plain definitional equality, which is reflexive
only on well-typed terms.  `Shape.WF Γ` says every label occurring in a
shape is well-typed in `Γ`; it is the hypothesis of `Shape.LE.refl`.
Note this is a genuine invariant of the model (interpretations only ever
produce well-typed labels), unlike the saturation conditions of the old
`ShapeFun.WF`, which are gone. -/

/-- Every entry of a graph has a well-typed label and well-formed shapes. -/
def ShapeFun.WF (Γ : List Term) (W : Shape n → Prop) (f : ShapeFun n) : Prop :=
  ∀ e ∈ f, (∃ u, Γ ⊢ e.ty : .sort u) ∧ Γ ⊢ e.tm : e.ty ∧ W e.inp ∧ W e.out

/-- Every label occurring in the shape is well-typed in `Γ`. -/
def Shape.WF (Γ : List Term) : ∀ {n}, Shape n → Prop
  | 0, .bot => True
  | 0, .sort _ => True
  | _+1, .bot => True
  | _+1, .sort _ => True
  | _+1, .unit _ => True
  | _+1, .nat => True
  | _+1, .zero => True
  | _+1, .succ v => WF Γ v
  | _+1, .refl w => WF Γ w
  | _+1, .id _ A a b => (∃ u, Γ ⊢ A : .sort u) ∧ Γ ⊢ a : A ∧ Γ ⊢ b : A
  | _+1, .forallE A B d f =>
      (∃ u, Γ ⊢ A : .sort u) ∧ (∃ v, A :: Γ ⊢ B : .sort v) ∧
        WF Γ d ∧ ShapeFun.WF Γ (WF Γ) f ∧ ShapeFun.Compat Shape.Compat Γ f f
  | _+1, .sigma A B d f =>
      (∃ u, Γ ⊢ A : .sort u) ∧ (∃ v, A :: Γ ⊢ B : .sort v) ∧
        WF Γ d ∧ ShapeFun.WF Γ (WF Γ) f ∧ ShapeFun.Compat Shape.Compat Γ f f
  | _+1, .pair a b => WF Γ a ∧ WF Γ b
  -- master's `NonZero`, strengthened to every entry: a well-formed λ-shape
  -- carries real information, so `IsBot` collapses to `= .bot` and the
  -- collapse clauses disappear from `LE`, `Compat` and `join`
  -- the last conjunct is **internal coherence**, the other repo's
  -- `IsCoherent`: entries whose labels become definitionally equal at some
  -- later stage, with compatible inputs there, must have compatible outputs
  -- there.  It is what makes the graph lookup's joins exist, and it belongs
  -- here because `WF` is the single "good shape" predicate the
  -- interpretation will carry anyway.
  | _+1, .lam f =>
      f ≠ [] ∧ (∀ e ∈ f, ¬ e.out.IsBot) ∧ ShapeFun.WF Γ (WF Γ) f ∧
        ShapeFun.Compat Shape.Compat Γ f f

/-! ## The order

`Shape.LE Γ` compares labels up to definitional equality in `Γ`, so it is
indexed by a context and lives in `Prop`. An entry is covered when some
entry of the larger graph has a definitionally equal label, a smaller
input and a larger output; an entry with a bottom output is covered
vacuously. -/

/-- Entry-wise coverage of one graph by another, parameterised by the
order `R` at the previous level. -/
def ShapeFun.LE (Γ : List Term) (R : Shape n → Shape n → Prop) (f f' : ShapeFun n) : Prop :=
  ∀ e ∈ f, ∃ e' ∈ f', LabelEq Γ e'.ty e'.tm e.ty e.tm ∧ R e'.inp e.inp ∧ R e.out e'.out

/-- The approximation order, by recursion on the level. -/
def Shape.LE (Γ : List Term) : ∀ {n}, Shape n → Shape n → Prop
  | 0, .bot, _ => True
  | 0, .sort r, .sort r' => r = r'
  | 0, _, _ => False
  | _+1, .bot, _ => True
  | _+1, .sort r, .sort r' => r = r'
  | _+1, .unit r, .unit r' => r = r'
  | _+1, .nat, .nat => True
  | _+1, .zero, .zero => True
  | _+1, .succ v, .succ v' => LE Γ v v'
  | _+1, .refl w, .refl w' => LE Γ w w'
  | _+1, .id r A a b, .id r' A' a' b' => r = r' ∧ IdLabelEq Γ A a b A' a' b'
  | _+1, .forallE A B d f, .forallE A' B' d' f' =>
      PiLabelEq Γ A B A' B' ∧ LE Γ d d' ∧ ShapeFun.LE Γ (LE Γ) f f'
  | _+1, .sigma A B d f, .sigma A' B' d' f' =>
      PiLabelEq Γ A B A' B' ∧ LE Γ d d' ∧ ShapeFun.LE Γ (LE Γ) f f'
  | _+1, .pair a b, .pair a' b' => LE Γ a a' ∧ LE Γ b b'
  | _+1, .lam f, .lam f' => ShapeFun.LE Γ (LE Γ) f f'
  | _+1, _, _ => False

@[simp] theorem Shape.LE.bot {s : Shape n} : Shape.LE Γ .bot s := by
  cases n <;> trivial

theorem Shape.LE.refl_aux : ∀ {n} {s : Shape n}, Shape.WF Γ s → Shape.LE Γ s s := by
  intro n
  induction n with
  | zero => intro s _; cases s <;> trivial
  | succ n ih =>
    intro s hs
    have hfun : ∀ f : ShapeFun n, ShapeFun.WF Γ (Shape.WF Γ) f →
        ShapeFun.LE Γ (Shape.LE Γ) f f := fun f hf e he =>
      have ⟨⟨_, hty⟩, htm, hin, hout⟩ := hf e he
      ⟨e, he, LabelEq.refl hty htm, ih hin, ih hout⟩
    cases s with
    | bot | nat | zero => trivial
    | sort | unit => rfl
    | succ | refl => exact ih hs
    | id =>
      have ⟨⟨_, hA⟩, ha, hb⟩ := hs
      exact ⟨rfl, .refl hA ha hb⟩
    | forallE A B d f =>
      have ⟨⟨_, hA⟩, ⟨_, hB⟩, hd, hf, _⟩ := hs
      exact ⟨.refl hA hB, ih hd, hfun f hf⟩
    | sigma A B d f =>
      have ⟨⟨_, hA⟩, ⟨_, hB⟩, hd, hf, _⟩ := hs
      exact ⟨.refl hA hB, ih hd, hfun f hf⟩
    | pair => exact ⟨ih hs.1, ih hs.2⟩
    | lam => exact hfun _ hs.2.2.1

/-- With the collapse clauses gone, only `⊥` is below `⊥`. -/
theorem Shape.le_bot_iff : ∀ {n} {s : Shape n}, Shape.LE Δ s .bot ↔ s = .bot := by
  intro n
  cases n with
  | zero =>
    intro s
    cases s with
    | bot => exact ⟨fun _ => rfl, fun _ => trivial⟩
    | sort => exact ⟨fun h => absurd h id, fun h => nomatch h⟩
  | succ n =>
    intro s
    cases s with
    | bot => exact ⟨fun _ => rfl, fun _ => trivial⟩
    | _ => exact ⟨fun h => absurd h id, fun h => nomatch h⟩

/-- Substitution composes on shapes, as it does on terms. -/
theorem Shape.subst_subst {σ τ : Subst} : ∀ {n} {x : Shape n},
    (x.subst σ).subst τ = x.subst (σ.comp τ) := by
  intro n
  induction n with
  | zero => intro x; cases x <;> rfl
  | succ n ih =>
    intro x
    cases x with
    | bot | sort | unit | nat | zero => rfl
    | succ v => show ShapeS.succ _ = ShapeS.succ _; rw [ih]
    | refl w => show ShapeS.refl _ = ShapeS.refl _; rw [ih]
    | pair a b => show ShapeS.pair _ _ = ShapeS.pair _ _; rw [ih, ih]
    | id r A a b =>
      show ShapeS.id _ _ _ _ = ShapeS.id _ _ _ _
      simp [DomainSemantics.subst_subst]
    | lam f =>
      show ShapeS.lam _ = ShapeS.lam _
      simp [ShapeFun.subst, DomainSemantics.subst_subst, ih]
    | forallE A B d f =>
      show ShapeS.forallE _ _ _ _ = ShapeS.forallE _ _ _ _
      simp [ShapeFun.subst, DomainSemantics.subst_subst, Subst.comp_lift, ih]
    | sigma A B d f =>
      show ShapeS.sigma _ _ _ _ = ShapeS.sigma _ _ _ _
      simp [ShapeFun.subst, DomainSemantics.subst_subst, Subst.comp_lift, ih]

/-- The total shape domain: a shape together with its level, as master's
`TShape`.  The interpretation quantifies over this, so that the level
index never appears in the statement of a soundness lemma. -/
def TShape := Σ n, Shape n

/-- Inject a shape into `TShape` by remembering its level. -/
abbrev Shape.T {n} (s : Shape n) : TShape := ⟨n, s⟩

namespace TShape

def LE (Δ : List Term) (a b : TShape) : Prop :=
  Shape.LE Δ (a.2.lift (max a.1 b.1)) (b.2.lift (max a.1 b.1))

def WF (Δ : List Term) (a : TShape) : Prop := Shape.WF Δ a.2

def bot : TShape := Shape.T (n := 0) .bot

def sort (r : Bool) : TShape := Shape.T (n := 0) (.sort r)

abbrev type : TShape := sort true
abbrev prop : TShape := sort false

end TShape

/-! ## Compatibility and join

`Compat Δ x y` says `x` and `y` can be joined.  For graphs it is master's
condition, with the label premise added: entries with definitionally equal
labels and compatible inputs must have compatible outputs.  That single
clause is what the other repo splits into `IsCoherent` (`f` against
itself) and `InternallyCompatible` (`f` against `g`).

`join` is context-free and total, producing junk (`⊥`) on mismatched
heads; it is a least upper bound only for compatible, well-formed shapes.
On graphs it is **append**, which is the lub for entry-wise coverage; the
old `ShapeFun.join` re-applied the graphs because they had to stay
saturated. -/

/-- `Join Δ x y z`: `z` is a least upper bound of `x` and `y` in the
context `Δ`.  This is master's `WShape.Join`, and it is the form used in
proofs: it is insensitive to which of two definitionally equal labels a
witness happens to carry, and does not presuppose that a join exists. -/
def Shape.Join (Δ : List Term) {n} (x y z : Shape n) : Prop :=
  ∀ w, Shape.LE Δ z w ↔ (Shape.LE Δ x w ∧ Shape.LE Δ y w)

/-- The join.  Total and context-free.

Since a well-formed λ-shape is never information-free, a λ-shape facing a
different head is genuinely incompatible, so the mixed-`lam` clauses that
the other repo's `cSup` needs are unnecessary here.  Labels of the left argument
are kept elsewhere, which is legitimate under `Compat Δ` since they are
then definitionally equal to the right one's. -/
def Shape.join : ∀ {n}, Shape n → Shape n → Shape n
  | 0, .bot, b => b
  | 0, a, .bot => a
  | 0, a, _ => a
  | _+1, .bot, b => b
  | _+1, a, .bot => a
  | _+1, .lam f, .lam f' => .lam (f ++ f')
  | _+1, .forallE A B d f, .forallE _ _ d' f' => .forallE A B (join d d') (f ++ f')
  | _+1, .sigma A B d f, .sigma _ _ d' f' => .sigma A B (join d d') (f ++ f')
  | _+1, .succ v, .succ v' => .succ (join v v')
  | _+1, .refl w, .refl w' => .refl (join w w')
  | _+1, .pair a b, .pair a' b' => .pair (join a a') (join b b')
  | _+1, a, _ => a

/-- Composing coverage of graphs.  This is the step that forces the label
to carry its type: the two `LabelEq` proofs are chained by
`LabelEq.trans`, whose sort-typed component is handled by `IsDefEq.trans'`.
With a type-free label (`TmEq`) this is exactly where the argument stalls. -/
theorem ShapeFun.LE.trans_of {Γ : List Term} {n} {f f' f'' : ShapeFun n}
    (ih : ∀ {a b c : Shape n}, Shape.LE Γ a b → Shape.LE Γ b c → Shape.LE Γ a c)
    (h₁ : ShapeFun.LE Γ (Shape.LE Γ) f f') (h₂ : ShapeFun.LE Γ (Shape.LE Γ) f' f'') :
    ShapeFun.LE Γ (Shape.LE Γ) f f'' := by
  intro e he
  have ⟨e', he', hlab, hin, hout⟩ := h₁ e he
  have ⟨e'', he'', hlab', hin', hout'⟩ := h₂ e' he'
  exact ⟨e'', he'', hlab'.trans hlab, ih hin' hin, ih hout hout'⟩

/-- Transitivity of the order. -/
theorem Shape.LE.trans_aux (hΓ : ⊢ Γ) {n} {s t u : Shape n}
    (h₁ : Shape.LE Γ s t) (h₂ : Shape.LE Γ t u) : Shape.LE Γ s u := by
  induction n with
  | zero => cases s <;> cases t <;> cases u <;> simp_all [Shape.LE]
  | succ _ ih
  cases s with
  | bot => trivial
  | lam f =>
    cases t with
    | lam f' =>
      cases u with
      | lam f'' => exact h₁.trans_of ih h₂
      | _ => exact absurd h₂ id
    | _ => exact absurd h₁ id
  | succ | refl =>
    cases t <;> try cases h₁
    cases u <;> try cases h₂
    exact ih h₁ h₂
  | pair =>
    cases t <;> cases h₁
    cases u <;> cases h₂
    exact ⟨ih ‹_› ‹_›, ih ‹_› ‹_›⟩
  | id =>
    cases t <;> cases h₁
    cases u <;> cases h₂
    exact ⟨.trans ‹_› ‹_›, .trans ‹_› ‹_›⟩
  | forallE | sigma =>
    cases t <;> cases h₁; rename_i h₁₁ h₁₂
    cases u <;> cases h₂; rename_i h₂₁ h₂₂
    exact ⟨h₁₁.trans hΓ h₂₁, ih h₁₂.1 h₂₂.1, h₁₂.2.trans_of ih h₂₂.2⟩
  | _ => cases t <;> cases u <;> simp_all [Shape.LE]

/-! ## Preservation under typed substitution

The order is stable along a typed substitution.  This is where the label
relations' `subst` lemmas are consumed, and it is the reason every
reindexing statement in the development carries `⊢ Θ` and `Θ ⊢ τ : Δ`:
definitional equality is only stable under typed substitutions. -/

theorem ShapeFun.LE.subst_of {Δ Θ : List Term} {τ : Subst} {n} {f f' : ShapeFun n}
    (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ)
    (ih : ∀ {a b : Shape n}, Shape.LE Δ a b → Shape.LE Θ (a.subst τ) (b.subst τ))
    (h : ShapeFun.LE Δ (Shape.LE Δ) f f') :
    ShapeFun.LE Θ (Shape.LE Θ) (ShapeFun.subst (Shape.subst · τ) τ f)
      (ShapeFun.subst (Shape.subst · τ) τ f') := by
  intro d hd
  obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 hd
  have ⟨e', he', hlab, hin, hout⟩ := h e he
  exact ⟨_, ShapeFun.mem_subst.2 ⟨e', he', rfl⟩, hlab.subst hΘ W, ih hin, ih hout⟩

theorem Shape.LE.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ) :
    ∀ {n} {s t : Shape n}, Shape.LE Δ s t → Shape.LE Θ (s.subst τ) (t.subst τ) := by
  intro n
  induction n with
  | zero => intro s t h; cases s <;> cases t <;> simp_all [Shape.LE, Shape.subst]
  | succ n ih =>
    intro s t h
    cases s with
    | bot => trivial
    | lam f =>
      cases t with
      | lam f' => exact ShapeFun.LE.subst_of hΘ W ih h
      | _ => exact absurd h id
    | succ v => cases t <;> first | exact absurd h id | exact ih h
    | refl w => cases t <;> first | exact absurd h id | exact ih h
    | pair a b => cases t <;> first | exact absurd h id | exact ⟨ih h.1, ih h.2⟩
    | id r A a b =>
      cases t <;> first | exact absurd h id | exact ⟨h.1, h.2.subst hΘ W⟩
    | forallE A B d f =>
      cases t <;> first | exact absurd h id
                        | exact ⟨h.1.subst hΘ W, ih h.2.1,
                            ShapeFun.LE.subst_of hΘ W ih h.2.2⟩
    | sigma A B d f =>
      cases t <;> first | exact absurd h id
                        | exact ⟨h.1.subst hΘ W, ih h.2.1,
                            ShapeFun.LE.subst_of hΘ W ih h.2.2⟩
    | _ => cases t <;> simp_all [Shape.LE, Shape.subst]

/-! ## The join is a least upper bound

Split as usual: `join_le` (least) needs nothing, while the upper-bound
direction needs `Compat Δ` — to know the labels agree — and `WF`, since
the order is reflexive only on well-formed shapes. -/

theorem ShapeFun.LE.append {Δ : List Term} {n} {f f' g : ShapeFun n}
    (h₁ : ShapeFun.LE Δ (Shape.LE Δ) f g) (h₂ : ShapeFun.LE Δ (Shape.LE Δ) f' g) :
    ShapeFun.LE Δ (Shape.LE Δ) (f ++ f') g := by
  intro e he
  match List.mem_append.1 he with
  | .inl he => exact h₁ e he
  | .inr he => exact h₂ e he

theorem Shape.join_le : ∀ {n} {x y w : Shape n},
    Shape.LE Δ x w → Shape.LE Δ y w → Shape.LE Δ (x.join y) w := by
  intro n
  induction n with
  | zero =>
    intro x y w h₁ h₂
    cases x with
    | bot => exact h₂
    | sort r => cases y with | bot => exact h₁ | sort r' => exact h₁
  | succ n ih =>
    intro x y w h₁ h₂
    cases x with
    | bot => exact h₂
    | lam f =>
      cases y with
      | bot => exact h₁
      | lam f' =>
        cases w with
        | lam g => exact ShapeFun.LE.append h₁ h₂
        | _ => exact absurd h₁ id
      | _ => exact h₁
    | forallE A B d f =>
      cases y with
      | bot => exact h₁
      | forallE A' B' d' f' =>
        cases w <;> first
          | exact absurd h₁ id
          | exact ⟨h₁.1, ih h₁.2.1 h₂.2.1, ShapeFun.LE.append h₁.2.2 h₂.2.2⟩
      | _ => exact h₁
    | sigma A B d f =>
      cases y with
      | bot => exact h₁
      | sigma A' B' d' f' =>
        cases w <;> first
          | exact absurd h₁ id
          | exact ⟨h₁.1, ih h₁.2.1 h₂.2.1, ShapeFun.LE.append h₁.2.2 h₂.2.2⟩
      | _ => exact h₁
    | succ v =>
      cases y with
      | bot => exact h₁
      | succ v' => cases w <;> first | exact absurd h₁ id | exact ih h₁ h₂
      | _ => exact h₁
    | refl u =>
      cases y with
      | bot => exact h₁
      | refl u' => cases w <;> first | exact absurd h₁ id | exact ih h₁ h₂
      | _ => exact h₁
    | pair a b =>
      cases y with
      | bot => exact h₁
      | pair a' b' =>
        cases w <;> first | exact absurd h₁ id | exact ⟨ih h₁.1 h₂.1, ih h₁.2 h₂.2⟩
      | _ => exact h₁
    | sort r => cases y with | bot => exact h₁ | _ => exact h₁
    | unit r => cases y with | bot => exact h₁ | _ => exact h₁
    | nat => cases y with | bot => exact h₁ | _ => exact h₁
    | zero => cases y with | bot => exact h₁ | _ => exact h₁
    | id r A a b => cases y with | bot => exact h₁ | _ => exact h₁



theorem ShapeFun.LE.append_left {Δ : List Term} {n} {f f' : ShapeFun n}
    (hf : ShapeFun.WF Δ (Shape.WF Δ) f) : ShapeFun.LE Δ (Shape.LE Δ) f (f ++ f') := by
  intro e he
  have ⟨⟨_, hty⟩, htm, hin, hout⟩ := hf e he
  exact ⟨e, List.mem_append.2 (.inl he), LabelEq.refl hty htm,
    Shape.LE.refl_aux hin, Shape.LE.refl_aux hout⟩

theorem ShapeFun.LE.append_right {Δ : List Term} {n} {f f' : ShapeFun n}
    (hf' : ShapeFun.WF Δ (Shape.WF Δ) f') : ShapeFun.LE Δ (Shape.LE Δ) f' (f ++ f') := by
  intro e he
  have ⟨⟨_, hty⟩, htm, hin, hout⟩ := hf' e he
  exact ⟨e, List.mem_append.2 (.inr he), LabelEq.refl hty htm,
    Shape.LE.refl_aux hin, Shape.LE.refl_aux hout⟩

/-- The join is an upper bound.  Needs `WF` (the order is reflexive only on
well-formed shapes) and `Compat` (to know the labels agree, and to know
that a λ-shape facing a different head is information-free). -/
theorem Shape.le_join (hΔ : ⊢ Δ) : ∀ {n} {x y : Shape n}, Shape.WF Δ x → Shape.WF Δ y →
    Shape.Compat Δ x y → Shape.LE Δ x (x.join y) ∧ Shape.LE Δ y (x.join y) := by
  intro n
  induction n with
  | zero =>
    intro x y hx hy h
    cases x with
    | bot => exact ⟨trivial, Shape.LE.refl_aux hy⟩
    | sort r =>
      cases y with
      | bot => exact ⟨Shape.LE.refl_aux hx, trivial⟩
      | sort r' => exact ⟨rfl, (h : r = r').symm⟩
  | succ n ih =>
    intro x y hx hy h
    cases x with
    | bot => exact ⟨trivial, Shape.LE.refl_aux hy⟩
    | lam f =>
      cases y with
      | bot => exact ⟨Shape.LE.refl_aux hx, trivial⟩
      | lam f' =>
        exact ⟨ShapeFun.LE.append_left hx.2.2.1, ShapeFun.LE.append_right hy.2.2.1⟩
      | _ => exact absurd h id
    | forallE A B d f =>
      cases y with
      | bot => exact ⟨Shape.LE.refl_aux hx, trivial⟩
      | lam f' => exact absurd h id
      | forallE A' B' d' f' =>
        have ⟨⟨_, hA⟩, ⟨_, hB⟩, hd, hff, _⟩ := hx
        exact ⟨⟨PiLabelEq.refl hA hB, (ih hd hy.2.2.1 h.2.1).1, ShapeFun.LE.append_left hff⟩,
          ⟨h.1.symm hΔ, (ih hd hy.2.2.1 h.2.1).2, ShapeFun.LE.append_right hy.2.2.2.1⟩⟩
      | _ => exact absurd h id
    | sigma A B d f =>
      cases y with
      | bot => exact ⟨Shape.LE.refl_aux hx, trivial⟩
      | lam f' => exact absurd h id
      | sigma A' B' d' f' =>
        have ⟨⟨_, hA⟩, ⟨_, hB⟩, hd, hff, _⟩ := hx
        exact ⟨⟨PiLabelEq.refl hA hB, (ih hd hy.2.2.1 h.2.1).1, ShapeFun.LE.append_left hff⟩,
          ⟨h.1.symm hΔ, (ih hd hy.2.2.1 h.2.1).2, ShapeFun.LE.append_right hy.2.2.2.1⟩⟩
      | _ => exact absurd h id
    | succ v =>
      cases y with
      | bot => exact ⟨Shape.LE.refl_aux hx, trivial⟩
      | lam f' => exact absurd h id
      | succ v' => exact ⟨(ih hx hy h).1, (ih hx hy h).2⟩
      | _ => exact absurd h id
    | refl u =>
      cases y with
      | bot => exact ⟨Shape.LE.refl_aux hx, trivial⟩
      | lam f' => exact absurd h id
      | refl u' => exact ⟨(ih hx hy h).1, (ih hx hy h).2⟩
      | _ => exact absurd h id
    | pair a b =>
      cases y with
      | bot => exact ⟨Shape.LE.refl_aux hx, trivial⟩
      | lam f' => exact absurd h id
      | pair a' b' =>
        exact ⟨⟨(ih hx.1 hy.1 h.1).1, (ih hx.2 hy.2 h.2).1⟩,
          ⟨(ih hx.1 hy.1 h.1).2, (ih hx.2 hy.2 h.2).2⟩⟩
      | _ => exact absurd h id
    | sort r =>
      cases y with
      | bot => exact ⟨Shape.LE.refl_aux hx, trivial⟩
      | lam f' => exact absurd h id
      | sort r' => exact ⟨rfl, (h : r = r').symm⟩
      | _ => exact absurd h id
    | unit r =>
      cases y with
      | bot => exact ⟨Shape.LE.refl_aux hx, trivial⟩
      | lam f' => exact absurd h id
      | unit r' => exact ⟨rfl, (h : r = r').symm⟩
      | _ => exact absurd h id
    | nat =>
      cases y with
      | bot => exact ⟨Shape.LE.refl_aux hx, trivial⟩
      | lam f' => exact absurd h id
      | nat => exact ⟨trivial, trivial⟩
      | _ => exact absurd h id
    | zero =>
      cases y with
      | bot => exact ⟨Shape.LE.refl_aux hx, trivial⟩
      | lam f' => exact absurd h id
      | zero => exact ⟨trivial, trivial⟩
      | _ => exact absurd h id
    | id r A a b =>
      cases y with
      | bot => exact ⟨Shape.LE.refl_aux hx, trivial⟩
      | lam f' => exact absurd h id
      | id r' A' a' b' =>
        have ⟨⟨_, hA⟩, ha, hb⟩ := hx
        exact ⟨⟨rfl, IdLabelEq.refl hA ha hb⟩, ⟨h.1.symm, h.2.symm⟩⟩
      | _ => exact absurd h id

/-- Joins exist for compatible well-formed shapes, with the function as
witness. -/
theorem Shape.exists_join (hΔ : ⊢ Δ) {n} {x y : Shape n}
    (hx : Shape.WF Δ x) (hy : Shape.WF Δ y) (h : Shape.Compat Δ x y) :
    Shape.Join Δ x y (x.join y) := by
  have ⟨hl, hr⟩ := Shape.le_join hΔ hx hy h
  exact fun w => ⟨fun hw => ⟨Shape.LE.trans_aux (Γ := Δ) hΔ hl hw, Shape.LE.trans_aux (Γ := Δ) hΔ hr hw⟩,
    fun ⟨h₁, h₂⟩ => Shape.join_le h₁ h₂⟩

/-- Being information-free is invariant under substitution, in both
directions: it is a structural property that never looks at a label. -/
theorem Shape.isBot_subst_iff {τ : Subst} : ∀ {n} {s : Shape n},
    (s.subst τ).IsBot ↔ s.IsBot := by
  intro n
  induction n with
  | zero => intro s; cases s <;> exact Iff.rfl
  | succ n ih =>
    intro s
    cases s with
    | bot => exact Iff.rfl
    | lam f =>
      constructor
      · intro h e he
        exact ih.1 (h _ (ShapeFun.mem_subst.2 ⟨e, he, rfl⟩))
      · intro h d hd
        obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 hd
        exact ih.2 (h e he)
    | _ => exact Iff.rfl

/-! ## Well-formedness, compatibility and join under substitution

`join` commutes with substitution on the nose, being structural and
context-free.  Combined with `WF.subst`, `Compat.subst` and `exists_join`
this gives joins at the new stage without needing `Join` itself to
transport (which it does not: `Join Θ` quantifies over more shapes than
the image of the substitution). -/

theorem Shape.IsBot.subst {τ : Subst} : ∀ {n} {s : Shape n}, s.IsBot → (s.subst τ).IsBot := by
  intro n
  induction n with
  | zero =>
    intro s h
    cases s with
    | bot => trivial
    | sort => exact absurd h id
  | succ n ih =>
    intro s h
    cases s with
    | bot => trivial
    | lam f =>
      intro d hd
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 hd
      exact ih (h e he)
    | _ => exact absurd h id

/-- Compatibility transports along a typed substitution.  The graph clauses
go through by *composing* substitutions, which is the whole point of
quantifying over later stages inside them; the rest is the label lemmas. -/
theorem Shape.Compat.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) : ∀ {n} {x y : Shape n},
    Shape.Compat Δ x y → Shape.Compat Θ (x.subst τ) (y.subst τ) := by
  have hfun : ∀ {n} {f f' : ShapeFun n}, ShapeFun.Compat Shape.Compat Δ f f' →
      ShapeFun.Compat Shape.Compat Θ (ShapeFun.subst (Shape.subst · τ) τ f)
        (ShapeFun.subst (Shape.subst · τ) τ f') := by
    intro n f f' h d hd d' hd' Ξ υ hΞ V hlab hin
    obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 hd
    obtain ⟨e', he', rfl⟩ := ShapeFun.mem_subst.1 hd'
    have hcomp : Ctx.SubstEq Ξ (τ.comp υ) (τ.comp υ) Δ := Ctx.SubstEq.comp hΞ V W
    simp only [DomainSemantics.subst_subst,
      Shape.subst_subst] at hlab hin ⊢
    exact h e he e' he' Ξ (τ.comp υ) hΞ hcomp hlab hin
  intro n
  induction n with
  | zero => intro x y h; cases x <;> cases y <;> simp_all [Shape.Compat, Shape.subst]
  | succ n ih =>
    intro x y h
    cases x with
    | bot => trivial
    | lam f =>
      cases y with
      | bot => trivial
      | lam f' => exact hfun h
      | _ => exact absurd h id
    | forallE A B d f =>
      cases y with
      | bot => trivial
      | lam f' => exact absurd h id
      | forallE A' B' d' f' => exact ⟨h.1.subst hΘ W, ih h.2.1, hfun h.2.2⟩
      | _ => exact absurd h id
    | sigma A B d f =>
      cases y with
      | bot => trivial
      | lam f' => exact absurd h id
      | sigma A' B' d' f' => exact ⟨h.1.subst hΘ W, ih h.2.1, hfun h.2.2⟩
      | _ => exact absurd h id
    | succ v =>
      cases y with
      | bot => trivial
      | lam f' => exact absurd h id
      | succ v' => exact ih h
      | _ => exact absurd h id
    | refl w =>
      cases y with
      | bot => trivial
      | lam f' => exact absurd h id
      | refl w' => exact ih h
      | _ => exact absurd h id
    | pair a b =>
      cases y with
      | bot => trivial
      | lam f' => exact absurd h id
      | pair a' b' => exact ⟨ih h.1, ih h.2⟩
      | _ => exact absurd h id
    | id r A a b =>
      cases y with
      | bot => trivial
      | lam f' => exact absurd h id
      | id r' A' a' b' => exact ⟨h.1, h.2.subst hΘ W⟩
      | _ => exact absurd h id
    | sort r =>
      cases y with
      | bot => trivial
      | lam f' => exact absurd h id
      | sort r' => exact h
      | _ => exact absurd h id
    | unit r =>
      cases y with
      | bot => trivial
      | lam f' => exact absurd h id
      | unit r' => exact h
      | _ => exact absurd h id
    | nat =>
      cases y with
      | bot => trivial
      | lam f' => exact absurd h id
      | nat => trivial
      | _ => exact absurd h id
    | zero =>
      cases y with
      | bot => trivial
      | lam f' => exact absurd h id
      | zero => trivial
      | _ => exact absurd h id

theorem ShapeFun.WF.subst_of {Δ Θ : List Term} {τ : Subst} {n} {f : ShapeFun n}
    (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ)
    (ih : ∀ {a : Shape n}, Shape.WF Δ a → Shape.WF Θ (a.subst τ))
    (hf : ShapeFun.WF Δ (Shape.WF Δ) f) :
    ShapeFun.WF Θ (Shape.WF Θ) (ShapeFun.subst (Shape.subst · τ) τ f) := by
  intro d hd
  obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 hd
  have ⟨⟨u, hty⟩, htm, hin, hout⟩ := hf e he
  exact ⟨⟨u, hty.subst hΘ W⟩, htm.subst hΘ W, ih hin, ih hout⟩

theorem Shape.WF.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ) :
    ∀ {n} {s : Shape n}, Shape.WF Δ s → Shape.WF Θ (s.subst τ) := by
  intro n
  induction n with
  | zero => intro s _; cases s <;> trivial
  | succ n ih =>
    intro s hs
    cases s with
    | bot | sort | unit | nat | zero => trivial
    | succ v => exact ih hs
    | refl w => exact ih hs
    | pair a b => exact ⟨ih hs.1, ih hs.2⟩
    | id r A a b =>
      have ⟨⟨u, hA⟩, ha, hb⟩ := hs
      exact ⟨⟨u, hA.subst hΘ W⟩, ha.subst hΘ W, hb.subst hΘ W⟩
    | lam f =>
      refine ⟨?_, ?_, ShapeFun.WF.subst_of hΘ W ih hs.2.2.1,
        Shape.Compat.subst hΘ W (n := n+1) (x := .lam f) (y := .lam f) hs.2.2.2⟩
      · intro hnil; simp [ShapeFun.subst] at hnil; exact hs.1 hnil
      · intro d hd
        obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 hd
        exact fun hb => hs.2.1 e he (Shape.isBot_subst_iff.1 hb)
    | forallE A B d f =>
      have ⟨⟨u, hA⟩, ⟨v, hB⟩, hd, hf, hco⟩ := hs
      have hA' := hA.subst hΘ W
      have hΘA : ⊢ A.subst τ :: Θ := ⟨hΘ, _, hA'⟩
      exact ⟨⟨u, hA'⟩, ⟨v, hB.subst hΘA (W.lift hA hA')⟩,
        ih hd, ShapeFun.WF.subst_of hΘ W ih hf,
        Shape.Compat.subst hΘ W (n := n+1) (x := .lam f) (y := .lam f) hco⟩
    | sigma A B d f =>
      have ⟨⟨u, hA⟩, ⟨v, hB⟩, hd, hf, hco⟩ := hs
      have hA' := hA.subst hΘ W
      have hΘA : ⊢ A.subst τ :: Θ := ⟨hΘ, _, hA'⟩
      exact ⟨⟨u, hA'⟩, ⟨v, hB.subst hΘA (W.lift hA hA')⟩,
        ih hd, ShapeFun.WF.subst_of hΘ W ih hf,
        Shape.Compat.subst hΘ W (n := n+1) (x := .lam f) (y := .lam f) hco⟩

theorem Shape.join_subst {τ : Subst} : ∀ {n} {x y : Shape n},
    (x.join y).subst τ = (x.subst τ).join (y.subst τ) := by
  intro n
  induction n with
  | zero => intro x y; cases x <;> cases y <;> rfl
  | succ n ih =>
    intro x y
    cases x with
    | bot => rfl
    | lam f =>
      cases y with
      | bot => rfl
      | lam f' => show Shape.lam _ = Shape.lam _; simp [ShapeFun.subst]
      | _ => rfl
    | forallE A B d f =>
      cases y with
      | bot => rfl
      | forallE A' B' d' f' =>
        show ShapeS.forallE _ _ _ _ = ShapeS.forallE _ _ _ _
        simp [ShapeFun.subst, ih]
      | _ => rfl
    | sigma A B d f =>
      cases y with
      | bot => rfl
      | sigma A' B' d' f' =>
        show ShapeS.sigma _ _ _ _ = ShapeS.sigma _ _ _ _
        simp [ShapeFun.subst, ih]
      | _ => rfl
    | succ v =>
      cases y with
      | bot => rfl
      | succ v' => show Shape.succ _ = Shape.succ _; rw [ih]
      | _ => rfl
    | refl u =>
      cases y with
      | bot => rfl
      | refl u' => show Shape.refl _ = Shape.refl _; rw [ih]
      | _ => rfl
    | pair a b =>
      cases y with
      | bot => rfl
      | pair a' b' => show ShapeS.pair _ _ = ShapeS.pair _ _; rw [ih, ih]
      | _ => rfl
    | sort r => cases y with | bot => rfl | _ => rfl
    | unit r => cases y with | bot => rfl | _ => rfl
    | nat => cases y with | bot => rfl | _ => rfl
    | zero => cases y with | bot => rfl | _ => rfl
    | id r A a b => cases y with | bot => rfl | _ => rfl

/-! ### Is `IsBot` a usable invariant?

Two facts decide whether bottom outputs can be forbidden inside graphs
(master's `NonZero` / `lam'`, strengthened to a per-entry condition).
Unlike saturation — which failed because substitution merges label classes
— being information-free is *structural*: it never inspects a label, so it
is invariant under substitution in **both** directions, and it is
decidable. -/

def Shape.decIsBot : ∀ {n} (s : Shape n), Decidable s.IsBot
  | 0, .bot => .isTrue trivial
  | 0, .sort _ => .isFalse id
  | _+1, .bot => .isTrue trivial
  | (n+1), .lam f =>
      @List.decidableBAll _ (fun e : Entry (Shape n) => Shape.IsBot e.out)
        (fun e => Shape.decIsBot e.out) f
  | _+1, .sort _ | _+1, .unit _ | _+1, .nat | _+1, .zero
  | _+1, .succ _ | _+1, .refl _ | _+1, .pair _ _
  | _+1, .id _ _ _ _ | _+1, .forallE _ _ _ _ | _+1, .sigma _ _ _ _ => .isFalse id

instance {n} {s : Shape n} : Decidable s.IsBot := Shape.decIsBot s

/-! ## Compatibility: symmetry, anti-monotonicity, common upper bounds

These are what the relational graph lookup needs.  Master gets away
without them because its lookup is a saturated max-below *function*; ours
collects matching entries and joins them, so it has to know the joins
exist. -/

theorem Shape.Compat.symm : ∀ {n} {Δ : List Term} {a b : Shape n}, ⊢ Δ →
    Shape.Compat Δ a b → Shape.Compat Δ b a := by
  intro n
  induction n with
  | zero => intro Δ a b _ h; cases a <;> cases b <;> simp_all [Shape.Compat]
  | succ n ih =>
    intro Δ a b hΔ h
    have hfun : ∀ {f g : ShapeFun n}, ShapeFun.Compat Shape.Compat Δ f g →
        ShapeFun.Compat Shape.Compat Δ g f := by
      intro f g hfg e he e' he' Θ τ hΘ W hlab hin
      exact ih hΘ (hfg e' he' e he Θ τ hΘ W hlab.symm (ih hΘ hin))
    cases a with
    | bot => cases b <;> trivial
    | lam f =>
      cases b with
      | bot => trivial
      | lam g => exact hfun h
      | _ => exact absurd h id
    | forallE A B d f =>
      cases b with
      | bot => trivial
      | forallE A' B' d' f' => exact ⟨h.1.symm hΔ, ih hΔ h.2.1, hfun h.2.2⟩
      | _ => exact absurd h id
    | sigma A B d f =>
      cases b with
      | bot => trivial
      | sigma A' B' d' f' => exact ⟨h.1.symm hΔ, ih hΔ h.2.1, hfun h.2.2⟩
      | _ => exact absurd h id
    | succ v => cases b with | bot => trivial | succ v' => exact ih hΔ h | _ => exact absurd h id
    | refl w => cases b with | bot => trivial | refl w' => exact ih hΔ h | _ => exact absurd h id
    | pair x y =>
      cases b with
      | bot => trivial
      | pair x' y' => exact ⟨ih hΔ h.1, ih hΔ h.2⟩
      | _ => exact absurd h id
    | id r A a' b' =>
      cases b with
      | bot => trivial
      | id r' A'' a'' b'' => exact ⟨h.1.symm, h.2.symm⟩
      | _ => exact absurd h id
    | sort r => cases b with | bot => trivial | sort r' => exact Eq.symm h | _ => exact absurd h id
    | unit r => cases b with | bot => trivial | unit r' => exact Eq.symm h | _ => exact absurd h id
    | nat => cases b with | bot => trivial | nat => trivial | _ => exact absurd h id
    | zero => cases b with | bot => trivial | zero => trivial | _ => exact absurd h id

/-- Compatibility is **anti-monotone on the right**.

The graph case is where the hereditary quantification earns its keep: the
covering entry's label agrees with the query's at the later stage by
transitivity of `LabelEq`, its input is compatible by the inductive
hypothesis, so the hypothesis applies there and hands back compatible
outputs, which the inductive hypothesis pushes back down.

Stated one-sided on purpose.  A two-sided induction would need
reflexivity of `LE` on the left argument, and reflexivity holds only on
well-formed shapes, which would drag a `WF` hypothesis into every use. -/
theorem Shape.Compat.anti_right : ∀ {n} {Δ : List Term} {a b b' : Shape n}, ⊢ Δ →
    Shape.Compat Δ a b → Shape.LE Δ b' b → Shape.Compat Δ a b' := by
  intro n
  induction n with
  | zero =>
    intro Δ a b b' _ h hb
    cases a <;> cases b <;> cases b' <;> simp_all [Shape.Compat, Shape.LE]
  | succ n ih =>
    intro Δ a b b' hΔ h hb
    cases a with
    | bot => trivial
    | lam f =>
      cases b with
      | bot => cases b' with | bot => trivial | _ => exact absurd hb id
      | lam g =>
        cases b' with
        | bot => trivial
        | lam g' =>
            intro e he e' he' Θ τ hΘ W hlab hin
            have ⟨e₂, he₂, hl₂, hi₂, ho₂⟩ := hb e' he'
            exact ih hΘ (h e he e₂ he₂ Θ τ hΘ W
                (hlab.trans (hl₂.subst hΘ W).symm)
                (ih hΘ hin (Shape.LE.subst hΘ W hi₂)))
              (Shape.LE.subst hΘ W ho₂)
        | _ => exact absurd hb id
      | _ => exact absurd h id
    | succ v =>
      cases b with
      | bot => cases b' with | bot => trivial | _ => exact absurd hb id
      | succ w =>
        cases b' with
        | bot => trivial
        | succ w' =>
          exact ih hΔ h hb
        | _ => exact absurd hb id
      | _ => exact absurd h id
    | refl v =>
      cases b with
      | bot => cases b' with | bot => trivial | _ => exact absurd hb id
      | refl w =>
        cases b' with
        | bot => trivial
        | refl w' =>
          exact ih hΔ h hb
        | _ => exact absurd hb id
      | _ => exact absurd h id
    | pair x y =>
      cases b with
      | bot => cases b' with | bot => trivial | _ => exact absurd hb id
      | pair u v =>
        cases b' with
        | bot => trivial
        | pair u' v' =>
          exact ⟨ih hΔ h.1 hb.1, ih hΔ h.2 hb.2⟩
        | _ => exact absurd hb id
      | _ => exact absurd h id
    | id r A₀ a₀ b₀ =>
      cases b with
      | bot => cases b' with | bot => trivial | _ => exact absurd hb id
      | id rb Ab ab bb =>
        cases b' with
        | bot => trivial
        | id r' A₁ a₁ b₁ =>
          exact ⟨h.1.trans hb.1.symm, h.2.trans hb.2.symm⟩
        | _ => exact absurd hb id
      | _ => exact absurd h id
    | forallE A₀ B₀ d f =>
      cases b with
      | bot => cases b' with | bot => trivial | _ => exact absurd hb id
      | forallE Ab Bb db fb =>
        cases b' with
        | bot => trivial
        | forallE A₁ B₁ e' g' =>
          refine ⟨h.1.trans hΔ (hb.1.symm hΔ), ih hΔ h.2.1 hb.2.1, ?_⟩
          intro e he e' he' Θ τ hΘ W hlab hin
          have ⟨e₂, he₂, hl₂, hi₂, ho₂⟩ := hb.2.2 e' he'
          exact ih hΘ (h.2.2 e he e₂ he₂ Θ τ hΘ W
              (hlab.trans (hl₂.subst hΘ W).symm)
              (ih hΘ hin (Shape.LE.subst hΘ W hi₂)))
            (Shape.LE.subst hΘ W ho₂)
        | _ => exact absurd hb id
      | _ => exact absurd h id
    | sigma A₀ B₀ d f =>
      cases b with
      | bot => cases b' with | bot => trivial | _ => exact absurd hb id
      | sigma Ab Bb db fb =>
        cases b' with
        | bot => trivial
        | sigma A₁ B₁ e' g' =>
          refine ⟨h.1.trans hΔ (hb.1.symm hΔ), ih hΔ h.2.1 hb.2.1, ?_⟩
          intro e he e' he' Θ τ hΘ W hlab hin
          have ⟨e₂, he₂, hl₂, hi₂, ho₂⟩ := hb.2.2 e' he'
          exact ih hΘ (h.2.2 e he e₂ he₂ Θ τ hΘ W
              (hlab.trans (hl₂.subst hΘ W).symm)
              (ih hΘ hin (Shape.LE.subst hΘ W hi₂)))
            (Shape.LE.subst hΘ W ho₂)
        | _ => exact absurd hb id
      | _ => exact absurd h id
    | sort r =>
      cases b with
      | bot => cases b' with | bot => trivial | _ => exact absurd hb id
      | sort rb =>
        cases b' with
        | bot => trivial
        | sort s => exact (h : r = rb).trans (hb : s = rb).symm
        | _ => exact absurd hb id
      | _ => exact absurd h id
    | unit r =>
      cases b with
      | bot => cases b' with | bot => trivial | _ => exact absurd hb id
      | unit rb =>
        cases b' with
        | bot => trivial
        | unit s => exact (h : r = rb).trans (hb : s = rb).symm
        | _ => exact absurd hb id
      | _ => exact absurd h id
    | nat =>
      cases b with
      | bot => cases b' with | bot => trivial | _ => exact absurd hb id
      | nat => cases b' with | bot => trivial | nat => trivial | _ => exact absurd hb id
      | _ => exact absurd h id
    | zero =>
      cases b with
      | bot => cases b' with | bot => trivial | _ => exact absurd hb id
      | zero => cases b' with | bot => trivial | zero => trivial | _ => exact absurd hb id
      | _ => exact absurd h id

/-- Compatibility is anti-monotone in both arguments. -/
theorem Shape.Compat.anti {n} {Δ : List Term} {a b a' b' : Shape n} (hΔ : ⊢ Δ)
    (h : Shape.Compat Δ a b) (ha : Shape.LE Δ a' a) (hb : Shape.LE Δ b' b) :
    Shape.Compat Δ a' b' :=
  Shape.Compat.symm hΔ (Shape.Compat.anti_right hΔ
    (Shape.Compat.symm hΔ (Shape.Compat.anti_right hΔ h hb)) ha)

/-- Two shapes below a common **coherent** upper bound are compatible.
This is the form the graph lookup needs: whenever two entries are selected
by the same query their inputs are both below the query shape, so this
supplies the hypothesis that coherence asks for. -/
theorem Shape.Compat.of_common_upper {n} {Δ : List Term} {a b c : Shape n} (hΔ : ⊢ Δ)
    (hc : Shape.Compat Δ c c) (ha : Shape.LE Δ a c) (hb : Shape.LE Δ b c) :
    Shape.Compat Δ a b := Shape.Compat.anti hΔ hc ha hb

/-- The join of two shapes compatible with `d` is compatible with `d`.
This is the other repo's `cSup_compatible`, and it is what lets the graph
lookup be closed under joins without losing coherence. -/
theorem Shape.join_compat : ∀ {n} {Δ : List Term} {y z d : Shape n}, ⊢ Δ →
    Shape.Compat Δ y d → Shape.Compat Δ z d → Shape.Compat Δ (y.join z) d := by
  intro n
  induction n with
  | zero =>
    intro Δ y z d _ hy hz
    cases y <;> cases z <;> cases d <;> simp_all [Shape.Compat, Shape.join]
  | succ n ih =>
    intro Δ y z d hΔ hy hz
    cases y with
    | bot => exact hz
    | lam f =>
      cases z with
      | bot => exact hy
      | lam g =>
        cases d with
        | bot => trivial
        | lam h =>
          intro e he e' he' Θ τ hΘ W hlab hin
          match List.mem_append.1 he with
          | .inl he => exact hy e he e' he' Θ τ hΘ W hlab hin
          | .inr he => exact hz e he e' he' Θ τ hΘ W hlab hin
        | _ => exact absurd hy id
      | _ => exact hy
    | succ v =>
      cases z with
      | bot => exact hy
      | succ w =>
        cases d with
        | bot => trivial
        | succ u =>
          exact ih hΔ hy hz
        | _ => exact absurd hy id
      | _ => exact hy
    | refl v =>
      cases z with
      | bot => exact hy
      | refl w =>
        cases d with
        | bot => trivial
        | refl u =>
          exact ih hΔ hy hz
        | _ => exact absurd hy id
      | _ => exact hy
    | pair x₁ y₁ =>
      cases z with
      | bot => exact hy
      | pair x₂ y₂ =>
        cases d with
        | bot => trivial
        | pair u₁ u₂ =>
          exact ⟨ih hΔ hy.1 hz.1, ih hΔ hy.2 hz.2⟩
        | _ => exact absurd hy id
      | _ => exact hy
    | forallE A₁ B₁ d₁ f =>
      cases z with
      | bot => exact hy
      | forallE A₂ B₂ d₂ g =>
        cases d with
        | bot => trivial
        | forallE A₃ B₃ d₃ h =>
          refine ⟨hy.1, ih hΔ hy.2.1 hz.2.1, ?_⟩
          intro e he e' he' Θ τ hΘ W hlab hin
          match List.mem_append.1 he with
          | .inl he => exact hy.2.2 e he e' he' Θ τ hΘ W hlab hin
          | .inr he => exact hz.2.2 e he e' he' Θ τ hΘ W hlab hin
        | _ => exact absurd hy id
      | _ => exact hy
    | sigma A₁ B₁ d₁ f =>
      cases z with
      | bot => exact hy
      | sigma A₂ B₂ d₂ g =>
        cases d with
        | bot => trivial
        | sigma A₃ B₃ d₃ h =>
          refine ⟨hy.1, ih hΔ hy.2.1 hz.2.1, ?_⟩
          intro e he e' he' Θ τ hΘ W hlab hin
          match List.mem_append.1 he with
          | .inl he => exact hy.2.2 e he e' he' Θ τ hΘ W hlab hin
          | .inr he => exact hz.2.2 e he e' he' Θ τ hΘ W hlab hin
        | _ => exact absurd hy id
      | _ => exact hy
    | sort r => cases z with | bot => exact hy | _ => exact hy
    | unit r => cases z with | bot => exact hy | _ => exact hy
    | nat => cases z with | bot => exact hy | _ => exact hy
    | zero => cases z with | bot => exact hy | _ => exact hy
    | id r A₁ a₁ b₁ => cases z with | bot => exact hy | _ => exact hy

@[simp] theorem Shape.Compat.bot_left {n} {Δ : List Term} {b : Shape n} :
    Shape.Compat Δ .bot b := by cases n <;> trivial

@[simp] theorem Shape.Compat.bot_right {n} {Δ : List Term} {a : Shape n} :
    Shape.Compat Δ a .bot := by
  cases n with
  | zero => cases a <;> trivial
  | succ n => cases a <;> trivial

@[simp] theorem Shape.subst_id : ∀ {n} {s : Shape n}, s.subst .id = s := by
  intro n
  induction n with
  | zero => intro s; cases s <;> rfl
  | succ n ih =>
    intro s
    have hf : ∀ f : ShapeFun n, ShapeFun.subst (Shape.subst · .id) .id f = f := by
      intro f
      induction f with
      | nil => rfl
      | cons e f ihf =>
        simp only [ShapeFun.subst, List.map_cons] at ihf ⊢
        rw [ih, ih, ihf, DomainSemantics.subst_id, DomainSemantics.subst_id]
    cases s with
    | bot | sort | unit | nat | zero => rfl
    | succ v => show ShapeS.succ _ = _; rw [ih]
    | refl w => show ShapeS.refl _ = _; rw [ih]
    | pair a b => show ShapeS.pair _ _ = _; rw [ih, ih]
    | id r A a b =>
      show ShapeS.id _ _ _ _ = _
      rw [DomainSemantics.subst_id, DomainSemantics.subst_id, DomainSemantics.subst_id]
    | lam f => show ShapeS.lam _ = _; rw [hf]
    | forallE A B d f =>
      show ShapeS.forallE _ _ _ _ = _
      rw [ih, hf, DomainSemantics.subst_id, id_lift, DomainSemantics.subst_id]
    | sigma A B d f =>
      show ShapeS.sigma _ _ _ _ = _
      rw [ih, hf, DomainSemantics.subst_id, id_lift, DomainSemantics.subst_id]

/-- Well-formedness survives joining.  Needs compatibility, because the
coherence conjunct of the joined graph has to relate entries coming from
*different* sides, which is exactly what `Compat` supplies. -/
theorem Shape.WF.join : ∀ {n} {Δ : List Term} {y z : Shape n}, ⊢ Δ →
    Shape.Compat Δ y z → Shape.WF Δ y → Shape.WF Δ z → Shape.WF Δ (y.join z) := by
  intro n
  induction n with
  | zero => intro Δ y z _ _ hy hz; cases y <;> cases z <;> trivial
  | succ n ih =>
    intro Δ y z hΔ hc hy hz
    cases y with
    | bot => exact hz
    | lam f =>
      cases z with
      | bot => exact hy
      | lam g =>
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro hnil; exact hy.1 (List.append_eq_nil_iff.1 hnil).1
        · intro e he
          match List.mem_append.1 he with
          | .inl he => exact hy.2.1 e he
          | .inr he => exact hz.2.1 e he
        · intro e he
          match List.mem_append.1 he with
          | .inl he => exact hy.2.2.1 e he
          | .inr he => exact hz.2.2.1 e he
        · intro e he e' he' Θ τ hΘ W hlab hin
          match List.mem_append.1 he, List.mem_append.1 he' with
          | .inl he, .inl he' => exact hy.2.2.2 e he e' he' Θ τ hΘ W hlab hin
          | .inl he, .inr he' => exact hc e he e' he' Θ τ hΘ W hlab hin
          | .inr he, .inl he' =>
            exact Shape.Compat.symm hΘ
              (hc e' he' e he Θ τ hΘ W (LabelEq.symm hlab) (Shape.Compat.symm hΘ hin))
          | .inr he, .inr he' => exact hz.2.2.2 e he e' he' Θ τ hΘ W hlab hin
      | _ => exact hy
    | forallE A B d f =>
      cases z with
      | bot => exact hy
      | forallE A' B' d' g =>
        refine ⟨hy.1, hy.2.1, ih hΔ hc.2.1 hy.2.2.1 hz.2.2.1, ?_, ?_⟩
        · intro e he
          match List.mem_append.1 he with
          | .inl he => exact hy.2.2.2.1 e he
          | .inr he => exact hz.2.2.2.1 e he
        · intro e he e' he' Θ τ hΘ W hlab hin
          match List.mem_append.1 he, List.mem_append.1 he' with
          | .inl he, .inl he' => exact hy.2.2.2.2 e he e' he' Θ τ hΘ W hlab hin
          | .inl he, .inr he' => exact hc.2.2 e he e' he' Θ τ hΘ W hlab hin
          | .inr he, .inl he' =>
            exact Shape.Compat.symm hΘ
              (hc.2.2 e' he' e he Θ τ hΘ W (LabelEq.symm hlab) (Shape.Compat.symm hΘ hin))
          | .inr he, .inr he' => exact hz.2.2.2.2 e he e' he' Θ τ hΘ W hlab hin
      | _ => exact hy
    | sigma A B d f =>
      cases z with
      | bot => exact hy
      | sigma A' B' d' g =>
        refine ⟨hy.1, hy.2.1, ih hΔ hc.2.1 hy.2.2.1 hz.2.2.1, ?_, ?_⟩
        · intro e he
          match List.mem_append.1 he with
          | .inl he => exact hy.2.2.2.1 e he
          | .inr he => exact hz.2.2.2.1 e he
        · intro e he e' he' Θ τ hΘ W hlab hin
          match List.mem_append.1 he, List.mem_append.1 he' with
          | .inl he, .inl he' => exact hy.2.2.2.2 e he e' he' Θ τ hΘ W hlab hin
          | .inl he, .inr he' => exact hc.2.2 e he e' he' Θ τ hΘ W hlab hin
          | .inr he, .inl he' =>
            exact Shape.Compat.symm hΘ
              (hc.2.2 e' he' e he Θ τ hΘ W (LabelEq.symm hlab) (Shape.Compat.symm hΘ hin))
          | .inr he, .inr he' => exact hz.2.2.2.2 e he e' he' Θ τ hΘ W hlab hin
      | _ => exact hy
    | succ v => cases z with | bot => exact hy | succ w => exact ih hΔ hc hy hz | _ => exact hy
    | refl v => cases z with | bot => exact hy | refl w => exact ih hΔ hc hy hz | _ => exact hy
    | pair a b =>
      cases z with
      | bot => exact hy
      | pair a' b' => exact ⟨ih hΔ hc.1 hy.1 hz.1, ih hΔ hc.2 hy.2 hz.2⟩
      | _ => exact hy
    | sort r => cases z with | bot => exact hy | _ => exact hy
    | unit r => cases z with | bot => exact hy | _ => exact hy
    | nat => cases z with | bot => exact hy | _ => exact hy
    | zero => cases z with | bot => exact hy | _ => exact hy
    | id r A a b => cases z with | bot => exact hy | _ => exact hy

/-- A well-formed shape is coherent with itself. -/
theorem Shape.WF.coherent : ∀ {n} {s : Shape n},
    Shape.WF Δ s → Shape.Compat Δ s s := by
  intro n
  induction n with
  | zero => intro s _; cases s <;> trivial
  | succ n ih =>
    intro s hs
    cases s with
    | bot | sort | unit | nat | zero => trivial
    | succ v => exact ih hs
    | refl w => exact ih hs
    | pair a b => exact ⟨ih hs.1, ih hs.2⟩
    | id r A a b =>
      have ⟨⟨_, hA⟩, ha, hb⟩ := hs
      exact ⟨rfl, IdLabelEq.refl hA ha hb⟩
    | lam f => exact hs.2.2.2
    | forallE A B d f =>
      have ⟨⟨_, hA⟩, ⟨_, hB⟩, hd, _, hco⟩ := hs
      exact ⟨PiLabelEq.refl hA hB, ih hd, hco⟩
    | sigma A B d f =>
      have ⟨⟨_, hA⟩, ⟨_, hB⟩, hd, _, hco⟩ := hs
      exact ⟨PiLabelEq.refl hA hB, ih hd, hco⟩
