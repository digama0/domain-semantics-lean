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
  -- the label is the syntactic first component `(A, a)`, which is what
  -- lets the second component be typed at the codomain family applied there
  | pair (ty tm : Term) : Shape → Shape → ShapeS Shape
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
  | _+1, _+1, .pair ty tm a b => .pair ty tm (lift _ a) (lift _ b)
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
    | pair ty tm a b => show ShapeS.pair _ _ _ _ = _; rw [ih, ih]
    | lam f => show ShapeS.lam _ = _; rw [hf]
    | forallE A B d f => show ShapeS.forallE _ _ _ _ = _; rw [ih, hf]
    | sigma A B d f => show ShapeS.sigma _ _ _ _ = _; rw [ih, hf]

/-- Lifting *up* and then anywhere is lifting anywhere.  Master's
`lift_lift`, restricted to the disjunct that is actually used: once a
shape has been lifted to a level that already holds it, no information is
left to lose on the way to a third level. -/
theorem Shape.lift_lift {n₁ n₂ n₃} {s : Shape n₁} (h : n₁ ≤ n₂) :
    (s.lift n₂).lift n₃ = s.lift n₃ := by
  induction n₁ generalizing n₂ n₃ with | zero => cases s <;> simp [lift] | succ n₁ ih
  let n₂+1 := n₂; have h' := Nat.le_of_succ_le_succ h
  cases n₃ with | zero => cases s <;> rfl | succ n₃
  have ihf (f : ShapeFun n₁) :
      ShapeFun.lift (Shape.lift n₃) (ShapeFun.lift (Shape.lift n₂) f) =
      ShapeFun.lift (Shape.lift n₃) f := by
    induction f with | nil => rfl | cons e f ihl
    simp only [ShapeFun.lift, List.map_cons] at ihl ⊢
    rw [ih h', ih h', ihl]
  cases s with
  | bot | sort | unit | nat | zero | id => rfl
  | succ v => show ShapeS.succ _ = ShapeS.succ _; rw [ih h']
  | refl w => show ShapeS.refl _ = ShapeS.refl _; rw [ih h']
  | pair ty tm a b => show ShapeS.pair _ _ _ _ = ShapeS.pair _ _ _ _; rw [ih h', ih h']
  | lam f => show ShapeS.lam _ = ShapeS.lam _; rw [ihf]
  | forallE A B d f =>
    show ShapeS.forallE _ _ _ _ = ShapeS.forallE _ _ _ _; rw [ih h', ihf]
  | sigma A B d f =>
    show ShapeS.sigma _ _ _ _ = ShapeS.sigma _ _ _ _; rw [ih h', ihf]

/-! ## Bottom shapes

A λ-shape all of whose outputs are bottom carries no information, and
neither does a pair both of whose components carry none.  Both are
forbidden by `WF` rather than identified with `⊥` by the order, which is
what lets the order keep `⊥` as its only bottom element (`le_bot_iff`) and
the join stay a least upper bound.  This replaces the old
`NonZero`/`lam'` normalisation. -/

/-- `IsBot s`: `s` carries no information — it is `⊥`, a graph with only
bottom outputs, or a pair of two such. -/
def Shape.IsBot : ∀ {n}, Shape n → Prop
  | 0, .bot => True
  | 0, .sort _ => False
  | _+1, .bot => True
  | _+1, .lam f => ∀ e ∈ f, IsBot e.out
  | _+1, .pair _ _ a b => IsBot a ∧ IsBot b
  | _+1, _ => False

@[simp] theorem Shape.isBot_bot : (Shape.bot (n := n)).IsBot := by cases n <;> trivial

@[simp] theorem Shape.isBot_lam {f : ShapeFun n} :
    Shape.IsBot (n := n+1) (ShapeS.lam f) ↔ ∀ e ∈ f, e.out.IsBot := Iff.rfl

@[simp] theorem Shape.isBot_pair {ty tm : Term} {a b : Shape n} :
    Shape.IsBot (n := n+1) (ShapeS.pair ty tm a b) ↔ a.IsBot ∧ b.IsBot := Iff.rfl

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
  | _+1, .pair ty tm a b, σ => .pair (ty.subst σ) (tm.subst σ) (subst a σ) (subst b σ)
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
  | _+1, Δ, .pair ty tm a b, .pair ty' tm' a' b' =>
      LabelEq Δ ty tm ty' tm' ∧ Compat Δ a a' ∧ Compat Δ b b'
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
  (∀ e ∈ f, (∃ u, Γ ⊢ e.ty : .sort u) ∧ Γ ⊢ e.tm : e.ty ∧ W e.inp ∧ W e.out) ∧
  ShapeFun.Compat Shape.Compat Γ f f

/-- Every label occurring in the shape is well-typed in `Γ`. -/
def Shape.WF (Γ : List Term) : ∀ {n}, Shape n → Prop
  | 0, .bot | 0, .sort _ | _+1, .bot | _+1, .sort _ | _+1, .unit _ | _+1, .nat | _+1, .zero => True
  | _+1, .succ v => WF Γ v
  | _+1, .refl w => WF Γ w
  | _+1, .id _ A a b => (∃ u, Γ ⊢ A : .sort u) ∧ Γ ⊢ a : A ∧ Γ ⊢ b : A
  | _+1, .forallE A B d f =>
      (∃ u, Γ ⊢ A : .sort u) ∧ (∃ v, A :: Γ ⊢ B : .sort v) ∧
        WF Γ d ∧ ShapeFun.WF Γ (WF Γ) f
  | _+1, .sigma A B d f =>
      (∃ u, Γ ⊢ A : .sort u) ∧ (∃ v, A :: Γ ⊢ B : .sort v) ∧
        WF Γ d ∧ ShapeFun.WF Γ (WF Γ) f
  -- the Σ analogue of the λ non-degeneracy condition: a pair with no
  -- information in either component would be a second bottom element
  | _+1, .pair ty tm a b =>
      (∃ u, Γ ⊢ ty : .sort u) ∧ Γ ⊢ tm : ty ∧
        WF Γ a ∧ WF Γ b ∧ ¬ (a.IsBot ∧ b.IsBot)
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
      f ≠ [] ∧ (∀ e ∈ f, ¬ e.out.IsBot) ∧ ShapeFun.WF Γ (WF Γ) f

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
  | _+1, .pair ty tm a b, .pair _ _ a' b' => .pair ty tm (join a a') (join b b')
  | _+1, a, _ => a

/-! ## The order

`Shape.LE Γ` compares labels up to definitional equality in `Γ`, so it is
indexed by a context and lives in `Prop`.

A graph is covered by another when every entry's output is reached by the
**lookup** in the covering graph at that entry's label and input.  Coverage
by a single *entry* — master's order, and the other repo's `Graph.LE` — is
too fine: η needs an entry whose output is a *join* of several outputs of
the covering graph, which no single entry dominates.  Master can afford
entry coverage because its graphs are saturated, so a join of matching
outputs *is* an entry; the other repo because a λ-value is an ideal,
closed under every graph valid for its action.

The lookup is `Evaluates`, and it is defined here, **parameterised by the
order one level down**, which is what closes the recursion: `LE` at `n+1`
needs the lookup at `n`, which needs `LE` at `n`.  `HasType.lean`'s
`Evaluates` is this one at `R := Shape.LE Δ`. -/

/-- The graph lookup at a label and an input: `⊥`, the outputs of matching
entries, closed downwards and under compatible joins.  The other repo's
`Evaluates`, with the order it is relative to as a parameter.

The two side conditions are not decoration.  `lower` carries `WF` because
`WF` is not downward closed — a smaller λ-shape may have a bottom output —
so without it `Evaluates.wf` fails; and `join` carries `Compat` so that
the join is a genuine least upper bound.  Together they are what makes the
lookup's values well behaved enough for the order built on them to reflect
along `lift`. -/
inductive ShapeFun.Eval (Δ : List Term) {n} (R : Shape n → Shape n → Prop)
    (f : ShapeFun n) (A a : Term) (x : Shape n) : Shape n → Prop where
  | bot : Eval Δ R f A a x .bot
  | entry (e : Entry (Shape n)) : e ∈ f → LabelEq Δ e.ty e.tm A a → R e.inp x →
    Eval Δ R f A a x e.out
  | lower {y z} : Shape.WF Δ y → R y z → Eval Δ R f A a x z → Eval Δ R f A a x y
  | join {y z} : Shape.Compat Δ y z → Eval Δ R f A a x y → Eval Δ R f A a x z →
    Eval Δ R f A a x (y.join z)

/-- Lookup-wise coverage of one graph by another, together with the
well-formedness of both.

**The order on graphs carries their well-formedness.**  Everywhere else in
`Shape.LE` it comes for free — a clause's label conjuncts are implied by
its `LabelEq`/`PiLabelEq`/`IdLabelEq`, its sub-shape conjuncts by the
recursive `LE` — but a graph's is not: `∀ e ∈ f, Eval f' e.ty e.tm e.inp
e.out` says nothing whatever about an entry whose output is `⊥`, because
`Eval.bot` discharges it.

It is what makes the order reflect along `lift`: `Eval.lift_of` wants the
covering graph well formed and coherent, and with this conjunct
`lift_le_lift`'s own hypothesis supplies them, so its statement does not
have to. -/
def ShapeFun.LE (Δ : List Term) (R : Shape n → Shape n → Prop) (W : Shape n → Prop)
    (f f' : ShapeFun n) : Prop :=
  (∀ e ∈ f, ShapeFun.Eval Δ R f' e.ty e.tm e.inp e.out) ∧
  ShapeFun.WF Δ W f ∧ ShapeFun.WF Δ W f'

/-- Appending two mutually coherent well-formed graphs. -/
theorem ShapeFun.WF.append {Δ : List Term} {n} {W : Shape n → Prop} {f f' : ShapeFun n}
    (hf : ShapeFun.WF Δ W f) (hf' : ShapeFun.WF Δ W f')
    (hx : ShapeFun.Compat Shape.Compat Δ f f')
    (hx' : ShapeFun.Compat Shape.Compat Δ f' f) : ShapeFun.WF Δ W (f ++ f') := by
  refine ⟨fun e he => ?_, fun e he e' he' Θ τ hΘ W hlab hin => ?_⟩
  · match List.mem_append.1 he with
    | .inl he => exact hf.1 e he
    | .inr he => exact hf'.1 e he
  · match List.mem_append.1 he, List.mem_append.1 he' with
    | .inl he, .inl he' => exact hf.2 e he e' he' Θ τ hΘ W hlab hin
    | .inl he, .inr he' => exact hx e he e' he' Θ τ hΘ W hlab hin
    | .inr he, .inl he' => exact hx' e he e' he' Θ τ hΘ W hlab hin
    | .inr he, .inr he' => exact hf'.2 e he e' he' Θ τ hΘ W hlab hin

/-- The lookup grows when the label moves along a definitional equality
and the input grows. -/
theorem ShapeFun.Eval.mono {Δ : List Term} {n} {R : Shape n → Shape n → Prop}
    (htr : ∀ a b c : Shape n, R a b → R b c → R a c)
    {f : ShapeFun n} {A a A' a' : Term} {x x' y : Shape n}
    (hlab : LabelEq Δ A a A' a') (hx : R x x')
    (H : ShapeFun.Eval Δ R f A a x y) : ShapeFun.Eval Δ R f A' a' x' y := by
  induction H with
  | bot => exact .bot
  | entry e he hl hin => exact .entry e he (hl.trans hlab) (htr _ _ _ hin hx)
  | lower hw hle _ ih => exact .lower hw hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- A lookup in a covered graph is a lookup in the covering one: this is
transitivity of the order, one level up. -/
theorem ShapeFun.Eval.trans {Δ : List Term} {n} {R : Shape n → Shape n → Prop}
    (htr : ∀ a b c : Shape n, R a b → R b c → R a c)
    {f f' : ShapeFun n} {A a : Term} {x y : Shape n}
    (hf : ∀ e ∈ f, ShapeFun.Eval Δ R f' e.ty e.tm e.inp e.out)
    (H : ShapeFun.Eval Δ R f A a x y) :
    ShapeFun.Eval Δ R f' A a x y := by
  induction H with
  | bot => exact .bot
  | entry e he hl hin => exact ShapeFun.Eval.mono htr hl hin (hf e he)
  | lower hw hle _ ih => exact .lower hw hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- Adding entries preserves a lookup. -/
theorem ShapeFun.Eval.sub {Δ : List Term} {n} {R : Shape n → Shape n → Prop}
    {f f' : ShapeFun n} {A a : Term} {x y : Shape n} (hsub : ∀ e ∈ f, e ∈ f')
    (H : ShapeFun.Eval Δ R f A a x y) : ShapeFun.Eval Δ R f' A a x y := by
  induction H with
  | bot => exact .bot
  | entry e he hl hin => exact .entry e (hsub e he) hl hin
  | lower hw hle _ ih => exact .lower hw hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- The approximation order, by recursion on the level. -/
def Shape.LE (Γ : List Term) : ∀ {n}, Shape n → Shape n → Prop
  | 0, .bot, _ => True
  | 0, .sort r, .sort r' => r = r'
  | 0, _, _ => False
  | _+1, .bot, _ | _+1, .nat, .nat | _+1, .zero, .zero => True
  | _+1, .sort r, .sort r' | _+1, .unit r, .unit r' => r = r'
  | _+1, .succ v, .succ v' | _+1, .refl v, .refl v' => LE Γ v v'
  | _+1, .id r A a b, .id r' A' a' b' => r = r' ∧ IdLabelEq Γ A a b A' a' b'
  | _+1, .forallE A B d f, .forallE A' B' d' f'
  | _+1, .sigma A B d f, .sigma A' B' d' f' =>
    PiLabelEq Γ A B A' B' ∧ LE Γ d d' ∧ ShapeFun.LE Γ (LE Γ) (WF Γ) f f'
  | _+1, .pair ty tm a b, .pair ty' tm' a' b' =>
      LabelEq Γ ty tm ty' tm' ∧ LE Γ a a' ∧ LE Γ b b'
  | _+1, .lam f, .lam f' => ShapeFun.LE Γ (LE Γ) (WF Γ) f f'
  | _+1, _, _ => False

@[simp] theorem Shape.LE.bot {s : Shape n} : Shape.LE Γ .bot s := by
  cases n <;> trivial

theorem Shape.LE.refl {n} {s : Shape n} (hs : Shape.WF Γ s) : Shape.LE Γ s s := by
  induction n with
  | zero => cases s <;> trivial
  | succ n ih =>
    have hfun {f : ShapeFun n} (hf : ShapeFun.WF Γ (Shape.WF Γ) f) :
        ShapeFun.LE Γ (Shape.LE Γ) (Shape.WF Γ) f f :=
      ⟨fun e he =>
        have ⟨⟨_, hty⟩, htm, hin, _⟩ := hf.1 e he
        .entry e he (LabelEq.refl hty htm) (ih hin), hf, hf⟩
    cases s with
    | bot | nat | zero => trivial
    | sort | unit => rfl
    | succ | refl => exact ih hs
    | id =>
      have ⟨⟨_, hA⟩, ha, hb⟩ := hs
      exact ⟨rfl, .refl hA ha hb⟩
    | forallE A B d f =>
      have ⟨⟨_, hA⟩, ⟨_, hB⟩, hd, hf⟩ := hs
      exact ⟨.refl hA hB, ih hd, hfun hf⟩
    | sigma A B d f =>
      have ⟨⟨_, hA⟩, ⟨_, hB⟩, hd, hf⟩ := hs
      exact ⟨.refl hA hB, ih hd, hfun hf⟩
    | pair ty tm a b =>
      have ⟨⟨_, hty⟩, htm, ha, hb, _⟩ := hs
      exact ⟨LabelEq.refl hty htm, ih ha, ih hb⟩
    | lam => exact hfun hs.2.2

/-- With the collapse clauses gone, only `⊥` is below `⊥`. -/
theorem Shape.le_bot_iff {n} {s : Shape n} : Shape.LE Δ s .bot ↔ s = .bot := by
  cases n <;>
  · cases s with
    | bot => exact ⟨fun _ => rfl, fun _ => trivial⟩
    | _ => exact ⟨fun h => absurd h id, nofun⟩

/-- Lifting is purely structural, so it commutes with substitution at
every pair of levels. -/
theorem Shape.lift_subst {n} (m : Nat) {s : Shape n} {τ : Subst} :
    (s.subst τ).lift m = (s.lift m).subst τ := by
  induction n generalizing m with
  | zero => cases s <;> cases m <;> rfl
  | succ n ih
  cases m with | zero => cases s <;> rfl | succ m
  have ihf (f : ShapeFun n) :
      ShapeFun.lift (Shape.lift m) (ShapeFun.subst (Shape.subst · τ) τ f)
        = ShapeFun.subst (Shape.subst · τ) τ (ShapeFun.lift (Shape.lift m) f) := by
    induction f with | nil => rfl | cons e f ihl
    simp only [ShapeFun.lift, ShapeFun.subst, List.map_cons] at ihl ⊢
    rw [ih, ih, ihl]
  cases s with
  | bot | sort | unit | nat | zero | id => rfl
  | succ v => show ShapeS.succ _ = ShapeS.succ _; rw [ih]
  | refl w => show ShapeS.refl _ = ShapeS.refl _; rw [ih]
  | pair ty tm a b => show ShapeS.pair _ _ _ _ = ShapeS.pair _ _ _ _; rw [ih, ih]
  | lam f => show ShapeS.lam _ = ShapeS.lam _; rw [ihf]
  | forallE A B d f => show ShapeS.forallE .. = ShapeS.forallE ..; rw [ih, ihf]
  | sigma A B d f => show ShapeS.sigma .. = ShapeS.sigma ..; rw [ih, ihf]

/-- Lifting *up* preserves and reflects being information-free. -/
theorem Shape.lift_isBot {n m} (h : n ≤ m) {s : Shape n} : (s.lift m).IsBot ↔ s.IsBot := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rw [Shape.lift_self]
    | succ m => cases s <;> rfl
  | succ n ih =>
    let m+1 := m; have h' := Nat.le_of_succ_le_succ h
    cases s with
      | lam f => ?_
      | pair a b => exact and_congr (ih h') (ih h')
      | _ => rfl
    constructor
    · intro H e he
      exact (ih h').1 (H ⟨e.ty, e.tm, e.inp.lift m, e.out.lift m⟩
        (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩))
    · intro H e'' he''
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
      exact (ih h').2 (H e he)

/-- Lifting *up* preserves and reflects compatibility.  The hereditary
graph clause goes through because lifting commutes with substitution; note
the context must be generalised in the induction, since that clause moves
to a later stage `Θ`. -/
theorem Shape.lift_compat {n m} (h : n ≤ m) {Δ : List Term} {s t : Shape n} :
    Shape.Compat Δ (s.lift m) (t.lift m) ↔ Shape.Compat Δ s t := by
  induction n generalizing m Δ with
  | zero =>
    cases m with
    | zero => rw [Shape.lift_self, Shape.lift_self]
    | succ m => cases s <;> cases t <;> exact Iff.rfl
  | succ n ih
  let m+1 := m; have h' := Nat.le_of_succ_le_succ h
  have ihf {Δ : List Term} {f f' : ShapeFun n} :
      ShapeFun.Compat Shape.Compat Δ (ShapeFun.lift (Shape.lift m) f)
        (ShapeFun.lift (Shape.lift m) f') ↔
      ShapeFun.Compat Shape.Compat Δ f f' := by
    constructor
    · intro H e he e' he' Θ τ hΘ W hlab hin
      have := H ⟨e.ty, e.tm, e.inp.lift m, e.out.lift m⟩ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)
        ⟨e'.ty, e'.tm, e'.inp.lift m, e'.out.lift m⟩ (ShapeFun.mem_lift.2 ⟨e', he', rfl⟩)
        Θ τ hΘ W hlab
      rw [← Shape.lift_subst, ← Shape.lift_subst, ← Shape.lift_subst,
        ← Shape.lift_subst] at this
      exact (ih h').1 (this ((ih h').2 hin))
    · intro H e'' he'' e''' he''' Θ τ hΘ W hlab hin
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
      obtain ⟨e', he', rfl⟩ := ShapeFun.mem_lift.1 he'''
      rw [← Shape.lift_subst, ← Shape.lift_subst] at hin ⊢
      exact (ih h').2 (H e he e' he' Θ τ hΘ W hlab ((ih h').1 hin))
  cases s <;> cases t <;> (try rfl)
  · exact and_congr Iff.rfl (and_congr (ih h') ihf)
  · exact ihf
  · exact and_congr Iff.rfl (and_congr (ih h') ihf)
  · exact and_congr Iff.rfl (and_congr (ih h') (ih h'))
  · exact ih h'
  · exact ih h'

/-- The graph-level companion, in the form the `WF` clauses need. -/
theorem ShapeFun.lift_compat {n m} (h : n ≤ m) {Δ : List Term} {f f' : ShapeFun n} :
    ShapeFun.Compat Shape.Compat Δ (ShapeFun.lift (Shape.lift m) f)
      (ShapeFun.lift (Shape.lift m) f') ↔
    ShapeFun.Compat Shape.Compat Δ f f' := by
  constructor
  · intro H e he e' he' Θ τ hΘ W hlab hin
    have := H ⟨e.ty, e.tm, e.inp.lift m, e.out.lift m⟩ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)
      ⟨e'.ty, e'.tm, e'.inp.lift m, e'.out.lift m⟩ (ShapeFun.mem_lift.2 ⟨e', he', rfl⟩)
      Θ τ hΘ W hlab
    rw [← Shape.lift_subst, ← Shape.lift_subst, ← Shape.lift_subst,
      ← Shape.lift_subst] at this
    exact (Shape.lift_compat h).1 (this ((Shape.lift_compat h).2 hin))
  · intro H e₁ he₁ e₂ he₂ Θ τ hΘ W hlab hin
    obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he₁
    obtain ⟨e', he', rfl⟩ := ShapeFun.mem_lift.1 he₂
    rw [← Shape.lift_subst, ← Shape.lift_subst] at hin ⊢
    exact (Shape.lift_compat h).2 (H e he e' he' Θ τ hΘ W hlab ((Shape.lift_compat h).1 hin))

/-- Lifting *up* preserves and reflects well-formedness. -/
theorem Shape.lift_wf {n m} (h : n ≤ m) {s : Shape n} :
    Shape.WF Δ (s.lift m) ↔ Shape.WF Δ s := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rw [Shape.lift_self]
    | succ m => cases s <;> exact Iff.rfl
  | succ n ih =>
    let m+1 := m; have h' := Nat.le_of_succ_le_succ h
    have ihf {f : ShapeFun n} :
        ShapeFun.WF Δ (Shape.WF Δ) (ShapeFun.lift (Shape.lift m) f) ↔
        ShapeFun.WF Δ (Shape.WF Δ) f := by
      refine and_congr ?_ (ShapeFun.lift_compat h')
      constructor
      · intro H e he
        have ⟨hty, htm, hin, hout⟩ :=
          H ⟨e.ty, e.tm, e.inp.lift m, e.out.lift m⟩ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)
        exact ⟨hty, htm, (ih h').1 hin, (ih h').1 hout⟩
      · intro H e'' he''
        obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
        have ⟨hty, htm, hin, hout⟩ := H e he
        exact ⟨hty, htm, (ih h').2 hin, (ih h').2 hout⟩
    have hnil {f : ShapeFun n} :
        ShapeFun.lift (Shape.lift m) f ≠ [] ↔ f ≠ [] := by
      cases f <;> simp [ShapeFun.lift]
    have hnb {f : ShapeFun n} :
        (∀ e ∈ ShapeFun.lift (Shape.lift m) f, ¬ e.out.IsBot) ↔ (∀ e ∈ f, ¬ e.out.IsBot) := by
      constructor
      · intro H e he hb
        exact H ⟨e.ty, e.tm, e.inp.lift m, e.out.lift m⟩
          (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩) ((Shape.lift_isBot h').2 hb)
      · intro H e'' he'' hb
        obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
        exact H e he ((Shape.lift_isBot h').1 hb)
    cases s with
    | bot | sort | unit | nat | zero | id => rfl
    | succ | refl => exact ih h'
    | pair =>
      exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr (ih h')
        (and_congr (ih h')
          (not_congr (and_congr (Shape.lift_isBot h') (Shape.lift_isBot h'))))))
    | lam => exact and_congr hnil (and_congr hnb ihf)
    | forallE | sigma =>
      exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr (ih h') ihf))

/-- Substitution composes on shapes, as it does on terms. -/
theorem Shape.subst_subst {σ τ : Subst} {n} {x : Shape n} :
    (x.subst σ).subst τ = x.subst (σ.comp τ) := by
  induction n with
  | zero => cases x <;> rfl
  | succ n ih =>
    cases x with
    | bot | sort | unit | nat | zero => rfl
    | succ v => show ShapeS.succ _ = ShapeS.succ _; rw [ih]
    | refl w => show ShapeS.refl _ = ShapeS.refl _; rw [ih]
    | pair ty tm a b =>
      show ShapeS.pair _ _ _ _ = ShapeS.pair _ _ _ _
      rw [ih, ih, DomainSemantics.subst_subst, DomainSemantics.subst_subst]
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

/-- Substitution acts levelwise. -/
def subst (a : TShape) (τ : Subst) : TShape := ⟨a.1, a.2.subst τ⟩

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

/-- Lifting *up* commutes with the join. -/
theorem Shape.lift_join {n m} (h : n ≤ m) {s t : Shape n} :
    (s.lift m).join (t.lift m) = (s.join t).lift m := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rw [Shape.lift_self, Shape.lift_self, Shape.lift_self]
    | succ m => cases s <;> cases t <;> rfl
  | succ n ih =>
    let m+1 := m; have h' := Nat.le_of_succ_le_succ h
    have ihf (f f' : ShapeFun n) :
        ShapeFun.lift (Shape.lift m) f ++ ShapeFun.lift (Shape.lift m) f' =
        ShapeFun.lift (Shape.lift m) (f ++ f') := (List.map_append ..).symm
    cases s <;> cases t <;> simp only [Shape.join, Shape.lift, ih h', ihf] <;> rfl

/-- Composing coverage of graphs.  This is the step that forces the label
to carry its type: the two `LabelEq` proofs are chained by
`LabelEq.trans`, whose sort-typed component is handled by `IsDefEq.trans'`.
With a type-free label (`TmEq`) this is exactly where the argument stalls. -/
theorem ShapeFun.LE.trans_of {Γ : List Term} {n} {f f' f'' : ShapeFun n}
    (ih : ∀ {a b c : Shape n}, Shape.LE Γ a b → Shape.LE Γ b c → Shape.LE Γ a c)
    (h₁ : ShapeFun.LE Γ (Shape.LE Γ) (Shape.WF Γ) f f') (h₂ : ShapeFun.LE Γ (Shape.LE Γ) (Shape.WF Γ) f' f'') :
    ShapeFun.LE Γ (Shape.LE Γ) (Shape.WF Γ) f f'' := by
  exact ⟨fun e he => ShapeFun.Eval.trans (R := Shape.LE Γ)
      (fun _ _ _ h h' => ih h h') h₂.1 (h₁.1 e he), h₁.2.1, h₂.2.2⟩

/-- Transitivity of the order. -/
theorem Shape.LE.trans (hΓ : ⊢ Γ) {n} {s t u : Shape n}
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
    cases t <;> try exact absurd h₁ id
    cases u <;> try exact absurd h₂ id
    exact ⟨LabelEq.trans h₁.1 h₂.1, ih h₁.2.1 h₂.2.1, ih h₁.2.2 h₂.2.2⟩
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

/-! ## The join is a least upper bound

Split as usual: `join_le` (least) needs nothing, while the upper-bound
direction needs `Compat Δ` — to know the labels agree — and `WF`, since
the order is reflexive only on well-formed shapes. -/

theorem ShapeFun.LE.append {Δ : List Term} {n} {f f' g : ShapeFun n}
    (hx : ShapeFun.Compat Shape.Compat Δ f f')
    (hx' : ShapeFun.Compat Shape.Compat Δ f' f)
    (h₁ : ShapeFun.LE Δ (Shape.LE Δ) (Shape.WF Δ) f g)
    (h₂ : ShapeFun.LE Δ (Shape.LE Δ) (Shape.WF Δ) f' g) :
    ShapeFun.LE Δ (Shape.LE Δ) (Shape.WF Δ) (f ++ f') g := by
  refine ⟨fun e he => ?_, ShapeFun.WF.append h₁.2.1 h₂.2.1 hx hx', h₁.2.2⟩
  match List.mem_append.1 he with
  | .inl he => exact h₁.1 e he
  | .inr he => exact h₂.1 e he

/-- Being information-free is invariant under substitution, in both
directions: it is a structural property that never looks at a label. -/
theorem Shape.isBot_subst_iff {τ : Subst} {n} {s : Shape n} : (s.subst τ).IsBot ↔ s.IsBot := by
  induction n with | zero => cases s <;> rfl | succ n ih
  cases s with
  | bot => rfl
  | lam f =>
    constructor
    · intro h e he
      exact ih.1 (h _ (ShapeFun.mem_subst.2 ⟨e, he, rfl⟩))
    · intro h d hd
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 hd
      exact ih.2 (h e he)
  | pair a b => exact and_congr ih ih
  | _ => rfl

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
      | pair a' b' => exact ⟨LabelEq.subst hΘ W h.1, ih h.2.1, ih h.2.2⟩
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
  refine ⟨fun d hd => ?_, Shape.Compat.subst hΘ W (n := n+1) (x := .lam f) (y := .lam f) hf.2⟩
  obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 hd
  have ⟨⟨u, hty⟩, htm, hin, hout⟩ := hf.1 e he
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
    | pair ty tm a b =>
      have ⟨⟨u, hty⟩, htm, ha, hb, hnb⟩ := hs
      exact ⟨⟨u, hty.subst hΘ W⟩, htm.subst hΘ W, ih ha, ih hb,
        fun hbb => hnb ⟨Shape.isBot_subst_iff.1 hbb.1, Shape.isBot_subst_iff.1 hbb.2⟩⟩
    | id r A a b =>
      have ⟨⟨u, hA⟩, ha, hb⟩ := hs
      exact ⟨⟨u, hA.subst hΘ W⟩, ha.subst hΘ W, hb.subst hΘ W⟩
    | lam f =>
      refine ⟨?_, ?_, ShapeFun.WF.subst_of hΘ W ih hs.2.2⟩
      · intro hnil; simp [ShapeFun.subst] at hnil; exact hs.1 hnil
      · intro d hd
        obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 hd
        exact fun hb => hs.2.1 e he (Shape.isBot_subst_iff.1 hb)
    | forallE A B d f =>
      have ⟨⟨u, hA⟩, ⟨v, hB⟩, hd, hf⟩ := hs
      have hA' := hA.subst hΘ W
      have hΘA : ⊢ A.subst τ :: Θ := ⟨hΘ, _, hA'⟩
      exact ⟨⟨u, hA'⟩, ⟨v, hB.subst hΘA (W.lift hA hA')⟩,
        ih hd, ShapeFun.WF.subst_of hΘ W ih hf⟩
    | sigma A B d f =>
      have ⟨⟨u, hA⟩, ⟨v, hB⟩, hd, hf⟩ := hs
      have hA' := hA.subst hΘ W
      have hΘA : ⊢ A.subst τ :: Θ := ⟨hΘ, _, hA'⟩
      exact ⟨⟨u, hA'⟩, ⟨v, hB.subst hΘA (W.lift hA hA')⟩,
        ih hd, ShapeFun.WF.subst_of hΘ W ih hf⟩

theorem Shape.join_subst {τ : Subst} {n} {x y : Shape n} :
    (x.join y).subst τ = (x.subst τ).join (y.subst τ) := by
  induction n with
  | zero => cases x <;> cases y <;> rfl
  | succ n ih =>
    cases x with
    | bot => rfl
    | lam f =>
      cases y with | lam f' => ?_ | _ => rfl
      show Shape.lam _ = Shape.lam _; simp [ShapeFun.subst]
    | forallE A B d f =>
      cases y with | forallE A' B' d' f' => ?_ | _ => rfl
      show ShapeS.forallE _ _ _ _ = ShapeS.forallE _ _ _ _
      simp [ShapeFun.subst, ih]
    | sigma A B d f =>
      cases y with | sigma A' B' d' f' => ?_ | _ => rfl
      show ShapeS.sigma _ _ _ _ = ShapeS.sigma _ _ _ _
      simp [ShapeFun.subst, ih]
    | succ v =>
      cases y with | succ v' => ?_ | _ => rfl
      show Shape.succ _ = Shape.succ _; rw [ih]
    | refl u =>
      cases y with | refl u' => ?_ | _ => rfl
      show Shape.refl _ = Shape.refl _; rw [ih]
    | pair ty tm a b =>
      cases y with | pair ty' tm' a' b' => ?_ | _ => rfl
      show ShapeS.pair _ _ _ _ = ShapeS.pair _ _ _ _; rw [ih, ih]
    | _ => cases y <;> rfl

/-! ### Is `IsBot` a usable invariant?

Two facts decide whether bottom outputs can be forbidden inside graphs
(master's `NonZero` / `lam'`, strengthened to a per-entry condition).
Unlike saturation — which failed because substitution merges label classes
— being information-free is *structural*: it never inspects a label, so it
is invariant under substitution in **both** directions, and it is
decidable. -/

instance Shape.decIsBot : ∀ {n} (s : Shape n), Decidable s.IsBot
  | 0, .bot => .isTrue trivial
  | 0, .sort _ => .isFalse id
  | _+1, .bot => .isTrue trivial
  | (n+1), .lam f =>
      @List.decidableBAll _ (fun e : Entry (Shape n) => Shape.IsBot e.out)
        (fun e => Shape.decIsBot e.out) f
  | _+1, .pair _ _ a b => @instDecidableAnd _ _ (Shape.decIsBot a) (Shape.decIsBot b)
  | _+1, .sort _ | _+1, .unit _ | _+1, .nat | _+1, .zero
  | _+1, .succ _ | _+1, .refl _
  | _+1, .id _ _ _ _ | _+1, .forallE _ _ _ _ | _+1, .sigma _ _ _ _ => .isFalse id

/-! ## Compatibility: symmetry, anti-monotonicity, common upper bounds

These are what the relational graph lookup needs.  Master gets away
without them because its lookup is a saturated max-below *function*; ours
collects matching entries and joins them, so it has to know the joins
exist. -/

theorem Shape.Compat.symm {n} {Δ : List Term} {a b : Shape n} (hΔ : ⊢ Δ)
    (h : Shape.Compat Δ a b) : Shape.Compat Δ b a := by
  induction n generalizing Δ with
  | zero => cases a <;> cases b <;> simp_all [Shape.Compat]
  | succ n ih =>
    have hfun : ∀ {f g : ShapeFun n}, ShapeFun.Compat Shape.Compat Δ f g →
        ShapeFun.Compat Shape.Compat Δ g f := by
      intro f g hfg e he e' he' Θ τ hΘ W hlab hin
      exact ih hΘ (hfg e' he' e he Θ τ hΘ W hlab.symm (ih hΘ hin))
    cases a with
    | bot => cases b <;> trivial
    | lam f => cases b with | bot => trivial | lam g => exact hfun h | _ => cases h
    | forallE A B d f =>
      cases b with | bot => trivial | forallE A' B' d' f' => ?_ | _ => cases h
      exact ⟨h.1.symm hΔ, ih hΔ h.2.1, hfun h.2.2⟩
    | sigma A B d f =>
      cases b with | bot => trivial | sigma A' B' d' f' => ?_ | _ => cases h
      exact ⟨h.1.symm hΔ, ih hΔ h.2.1, hfun h.2.2⟩
    | succ v => cases b with | bot => trivial | succ v' => exact ih hΔ h | _ => cases h
    | refl w => cases b with | bot => trivial | refl w' => exact ih hΔ h | _ => cases h
    | pair x y =>
      cases b with | bot => trivial | pair x' y' => ?_ | _ => cases h
      exact ⟨h.1.symm, ih hΔ h.2.1, ih hΔ h.2.2⟩
    | id r A a' b' =>
      cases b with | bot => trivial | id r' A'' a'' b'' => ?_ | _ => cases h
      exact ⟨h.1.symm, h.2.symm⟩
    | sort r => cases b with | bot => trivial | sort r' => exact Eq.symm h | _ => cases h
    | unit r => cases b with | bot => trivial | unit r' => exact Eq.symm h | _ => cases h
    | nat => cases b with | bot => trivial | nat => trivial | _ => cases h
    | zero => cases b with | bot => trivial | zero => trivial | _ => cases h

/-- The lookup transports along a typed substitution.  Mutual with
`Shape.LE.subst` across the level: this is the level-`n` statement, and
the order's own substitution lemma at `n+1` passes its induction
hypothesis in as `ih`. -/
theorem ShapeFun.Eval.subst_of {Δ Θ : List Term} {τ : Subst} {n} {f : ShapeFun n}
    {A a : Term} {x c : Shape n} (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ)
    (ih : ∀ {u v : Shape n}, Shape.LE Δ u v → Shape.LE Θ (u.subst τ) (v.subst τ))
    (H : ShapeFun.Eval Δ (Shape.LE Δ) f A a x c) :
    ShapeFun.Eval Θ (Shape.LE Θ) (ShapeFun.subst (Shape.subst · τ) τ f)
      (A.subst τ) (a.subst τ) (x.subst τ) (c.subst τ) := by
  induction H with
  | bot => simp only [Shape.subst_bot]; exact .bot
  | entry e he hlab hin =>
    exact .entry _ (ShapeFun.mem_subst.2 ⟨e, he, rfl⟩) (hlab.subst hΘ W) (ih hin)
  | lower hw hle _ ihe => exact .lower (Shape.WF.subst hΘ W hw) (ih hle) ihe
  | join hc _ _ ih₁ ih₂ => exact Shape.join_subst ▸ .join (hc.subst hΘ W) ih₁ ih₂


theorem ShapeFun.LE.subst_of {Δ Θ : List Term} {τ : Subst} {n} {f f' : ShapeFun n}
    (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ)
    (ih : ∀ {a b : Shape n}, Shape.LE Δ a b → Shape.LE Θ (a.subst τ) (b.subst τ))
    (h : ShapeFun.LE Δ (Shape.LE Δ) (Shape.WF Δ) f f') :
    ShapeFun.LE Θ (Shape.LE Θ) (Shape.WF Θ) (ShapeFun.subst (Shape.subst · τ) τ f)
      (ShapeFun.subst (Shape.subst · τ) τ f') := by
  refine ⟨fun d hd => ?_, ShapeFun.WF.subst_of hΘ W (Shape.WF.subst hΘ W) h.2.1,
    ShapeFun.WF.subst_of hΘ W (Shape.WF.subst hΘ W) h.2.2⟩
  obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 hd
  exact ShapeFun.Eval.subst_of hΘ W ih (h.1 e he)

theorem Shape.LE.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ)
    {n} {s t : Shape n} (h : Shape.LE Δ s t) : Shape.LE Θ (s.subst τ) (t.subst τ) := by
  induction n with | zero => cases s <;> cases t <;> simp_all [Shape.LE, Shape.subst] | succ n ih
  cases s with
  | bot => trivial
  | lam =>
    cases t with | lam => ?_ | _ => cases h
    exact ShapeFun.LE.subst_of hΘ W ih h
  | succ | refl => cases t <;> (try cases h); exact ih h
  | pair =>
    cases t <;> try exact absurd h id
    exact ⟨LabelEq.subst hΘ W h.1, ih h.2.1, ih h.2.2⟩
  | id => cases t <;> cases h; exact ⟨‹_›, .subst hΘ W ‹_›⟩
  | forallE | sigma =>
    cases t <;> cases h; rename_i h₁ h₂
    exact ⟨h₁.subst hΘ W, ih h₂.1, ShapeFun.LE.subst_of hΘ W ih h₂.2⟩
  | _ => cases t <;> simp_all [Shape.LE, Shape.subst]

@[simp] theorem Shape.Compat.bot_left {n} {Δ : List Term} {b : Shape n} :
    Shape.Compat Δ .bot b := by cases n <;> trivial

@[simp] theorem Shape.Compat.bot_right {n} {Δ : List Term} {a : Shape n} :
    Shape.Compat Δ a .bot := by
  cases n with
  | zero => cases a <;> trivial
  | succ n => cases a <;> trivial

/-- The join of two shapes compatible with `d` is compatible with `d`.
This is the other repo's `cSup_compatible`, and it is what lets the graph
lookup be closed under joins without losing coherence. -/
theorem Shape.Compat.join : ∀ {n} {Δ : List Term} {y z d : Shape n}, ⊢ Δ →
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
          exact ⟨hy.1, ih hΔ hy.2.1 hz.2.1, ih hΔ hy.2.2 hz.2.2⟩
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
            -- the covering fact is now a lookup derivation, so the
            -- coherence of the bigger graph is applied once per matching
            -- entry and the results recombined
            have key : ∀ {y}, ShapeFun.Eval Δ (Shape.LE Δ) g e'.ty e'.tm e'.inp y →
                Shape.Compat Θ (e.out.subst τ) (y.subst τ) := by
              intro y hy
              induction hy with
              | bot => simpa only [Shape.subst_bot] using Shape.Compat.bot_right
              | entry e₂ he₂ hl₂ hi₂ =>
                exact h e he e₂ he₂ Θ τ hΘ W
                  (hlab.trans (hl₂.subst hΘ W).symm)
                  (ih hΘ hin (Shape.LE.subst hΘ W hi₂))
              | lower _ hle _ ihz => exact ih hΘ ihz (Shape.LE.subst hΘ W hle)
              | join _ _ _ ih₁ ih₂ =>
                exact Shape.join_subst ▸ ((ih₁.symm hΘ).join hΘ (ih₂.symm hΘ)).symm hΘ
            exact key (hb.1 e' he')
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
          exact ⟨LabelEq.trans h.1 hb.1.symm, ih hΔ h.2.1 hb.2.1, ih hΔ h.2.2 hb.2.2⟩
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
          -- the covering fact is now a lookup derivation, so the
          -- coherence of the bigger graph is applied once per matching
          -- entry and the results recombined
          have key : ∀ {y}, ShapeFun.Eval Δ (Shape.LE Δ) fb e'.ty e'.tm e'.inp y →
              Shape.Compat Θ (e.out.subst τ) (y.subst τ) := by
            intro y hy
            induction hy with
            | bot => simpa only [Shape.subst_bot] using Shape.Compat.bot_right
            | entry e₂ he₂ hl₂ hi₂ =>
              exact h.2.2 e he e₂ he₂ Θ τ hΘ W
                (hlab.trans (hl₂.subst hΘ W).symm)
                (ih hΘ hin (Shape.LE.subst hΘ W hi₂))
            | lower _ hle _ ihz => exact ih hΘ ihz (Shape.LE.subst hΘ W hle)
            | join _ _ _ ih₁ ih₂ =>
              exact Shape.join_subst ▸ ((ih₁.symm hΘ).join hΘ (ih₂.symm hΘ)).symm hΘ
          exact key (hb.2.2.1 e' he')
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
          -- the covering fact is now a lookup derivation, so the
          -- coherence of the bigger graph is applied once per matching
          -- entry and the results recombined
          have key : ∀ {y}, ShapeFun.Eval Δ (Shape.LE Δ) fb e'.ty e'.tm e'.inp y →
              Shape.Compat Θ (e.out.subst τ) (y.subst τ) := by
            intro y hy
            induction hy with
            | bot => simpa only [Shape.subst_bot] using Shape.Compat.bot_right
            | entry e₂ he₂ hl₂ hi₂ =>
              exact h.2.2 e he e₂ he₂ Θ τ hΘ W
                (hlab.trans (hl₂.subst hΘ W).symm)
                (ih hΘ hin (Shape.LE.subst hΘ W hi₂))
            | lower _ hle _ ihz => exact ih hΘ ihz (Shape.LE.subst hΘ W hle)
            | join _ _ _ ih₁ ih₂ =>
              exact Shape.join_subst ▸ ((ih₁.symm hΘ).join hΘ (ih₂.symm hΘ)).symm hΘ
          exact key (hb.2.2.1 e' he')
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
    | pair ty tm a b =>
      show ShapeS.pair _ _ _ _ = _
      rw [ih, ih, DomainSemantics.subst_id, DomainSemantics.subst_id]
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

/-- The left argument of a join is information-free whenever the join is.
Only the left, and that is enough: the right-hand version fails for
mismatched heads (`join (lam []) (sort r)` is `lam []`, which is
information-free, while `sort r` is not), and `WF.join` only ever needs
the left one, applied to each component of a pair. -/
theorem Shape.IsBot.of_join_left : ∀ {n} {x y : Shape n}, (x.join y).IsBot → x.IsBot := by
  intro n
  induction n with
  | zero => intro x y h; cases x <;> cases y <;> first | trivial | exact h
  | succ n ih =>
    intro x y h
    cases x with
    | bot => trivial
    | lam f =>
      cases y with
      | lam f' => intro e he; exact h e (List.mem_append.2 (.inl he))
      | _ => exact h
    | pair a b =>
      cases y with
      | pair a' b' => exact ⟨ih h.1, ih h.2⟩
      | _ => exact h
    | _ => cases y <;> exact h

theorem Shape.join_le (hΔ : ⊢ Δ) : ∀ {n} {x y w : Shape n},
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
        | lam g =>
          have hc : Shape.Compat Δ (Shape.lam f) (Shape.lam f') :=
            Shape.Compat.of_common_upper hΔ
              (show Shape.Compat Δ (Shape.lam g) (Shape.lam g) from h₁.2.2.2) h₁ h₂
          exact ShapeFun.LE.append hc (Shape.Compat.symm hΔ hc) h₁ h₂
        | _ => exact absurd h₁ id
      | _ => exact h₁
    | forallE A B d f =>
      cases y with
      | bot => exact h₁
      | forallE A' B' d' f' =>
        cases w <;> first
          | exact absurd h₁ id
          | exact ⟨h₁.1, ih h₁.2.1 h₂.2.1,
              have hc : Shape.Compat Δ (Shape.lam f) (Shape.lam f') :=
                Shape.Compat.of_common_upper hΔ
                  (show Shape.Compat Δ (Shape.lam _) (Shape.lam _) from h₁.2.2.2.2.2)
                  (show Shape.LE Δ (Shape.lam f) (Shape.lam _) from h₁.2.2)
                  (show Shape.LE Δ (Shape.lam f') (Shape.lam _) from h₂.2.2)
              ShapeFun.LE.append hc (Shape.Compat.symm hΔ hc) h₁.2.2 h₂.2.2⟩
      | _ => exact h₁
    | sigma A B d f =>
      cases y with
      | bot => exact h₁
      | sigma A' B' d' f' =>
        cases w <;> first
          | exact absurd h₁ id
          | exact ⟨h₁.1, ih h₁.2.1 h₂.2.1,
              have hc : Shape.Compat Δ (Shape.lam f) (Shape.lam f') :=
                Shape.Compat.of_common_upper hΔ
                  (show Shape.Compat Δ (Shape.lam _) (Shape.lam _) from h₁.2.2.2.2.2)
                  (show Shape.LE Δ (Shape.lam f) (Shape.lam _) from h₁.2.2)
                  (show Shape.LE Δ (Shape.lam f') (Shape.lam _) from h₂.2.2)
              ShapeFun.LE.append hc (Shape.Compat.symm hΔ hc) h₁.2.2 h₂.2.2⟩
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
        cases w <;> first
          | exact absurd h₁ id
          | exact ⟨h₁.1, ih h₁.2.1 h₂.2.1, ih h₁.2.2 h₂.2.2⟩
      | _ => exact h₁
    | sort r => cases y with | bot => exact h₁ | _ => exact h₁
    | unit r => cases y with | bot => exact h₁ | _ => exact h₁
    | nat => cases y with | bot => exact h₁ | _ => exact h₁
    | zero => cases y with | bot => exact h₁ | _ => exact h₁
    | id r A a b => cases y with | bot => exact h₁ | _ => exact h₁



theorem ShapeFun.LE.refl {Δ : List Term} {n} {f : ShapeFun n}
    (hf : ShapeFun.WF Δ (Shape.WF Δ) f) : ShapeFun.LE Δ (Shape.LE Δ) (Shape.WF Δ) f f :=
  ⟨fun e he =>
    have ⟨⟨_, hty⟩, htm, hin, _⟩ := hf.1 e he
    .entry e he (LabelEq.refl hty htm) (.refl hin), hf, hf⟩

theorem ShapeFun.LE.append_left {Δ : List Term} {n} {f f' : ShapeFun n}
    (hf : ShapeFun.WF Δ (Shape.WF Δ) f) (hfg : ShapeFun.WF Δ (Shape.WF Δ) (f ++ f')) :
    ShapeFun.LE Δ (Shape.LE Δ) (Shape.WF Δ) f (f ++ f') :=
  ⟨fun e he =>
    have ⟨⟨_, hty⟩, htm, hin, _⟩ := hf.1 e he
    .entry e (List.mem_append.2 (.inl he)) (LabelEq.refl hty htm) (.refl hin), hf, hfg⟩

theorem ShapeFun.LE.append_right {Δ : List Term} {n} {f f' : ShapeFun n}
    (hf' : ShapeFun.WF Δ (Shape.WF Δ) f') (hfg : ShapeFun.WF Δ (Shape.WF Δ) (f ++ f')) :
    ShapeFun.LE Δ (Shape.LE Δ) (Shape.WF Δ) f' (f ++ f') :=
  ⟨fun e he =>
    have ⟨⟨_, hty⟩, htm, hin, _⟩ := hf'.1 e he
    .entry e (List.mem_append.2 (.inr he)) (LabelEq.refl hty htm) (.refl hin), hf', hfg⟩

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
    | bot => exact ⟨trivial, .refl hy⟩
    | sort r =>
      cases y with
      | bot => exact ⟨.refl hx, trivial⟩
      | sort r' => exact ⟨rfl, Eq.symm (show r = r' from h)⟩
  | succ n ih =>
    intro x y hx hy h
    cases x with
    | bot => exact ⟨trivial, .refl hy⟩
    | lam f =>
      cases y with
      | bot => exact ⟨.refl hx, trivial⟩
      | lam f' =>
        have hfg := ShapeFun.WF.append hx.2.2 hy.2.2 h (Shape.Compat.symm (a := Shape.lam f) hΔ h)
        exact ⟨ShapeFun.LE.append_left hx.2.2 hfg, ShapeFun.LE.append_right hy.2.2 hfg⟩
      | _ => exact absurd h id
    | forallE A B d f =>
      cases y with
      | bot => exact ⟨.refl hx, trivial⟩
      | lam f' => exact absurd h id
      | forallE A' B' d' f' =>
        have ⟨⟨_, hA⟩, ⟨_, hB⟩, hd, hff⟩ := hx
        have hfg := ShapeFun.WF.append hff hy.2.2.2 h.2.2
          (Shape.Compat.symm (a := Shape.lam f) (b := Shape.lam f') hΔ h.2.2)
        exact ⟨⟨PiLabelEq.refl hA hB, (ih hd hy.2.2.1 h.2.1).1,
            ShapeFun.LE.append_left hff hfg⟩,
          ⟨h.1.symm hΔ, (ih hd hy.2.2.1 h.2.1).2,
            ShapeFun.LE.append_right hy.2.2.2 hfg⟩⟩
      | _ => exact absurd h id
    | sigma A B d f =>
      cases y with
      | bot => exact ⟨.refl hx, trivial⟩
      | lam f' => exact absurd h id
      | sigma A' B' d' f' =>
        have ⟨⟨_, hA⟩, ⟨_, hB⟩, hd, hff⟩ := hx
        have hfg := ShapeFun.WF.append hff hy.2.2.2 h.2.2
          (Shape.Compat.symm (a := Shape.lam f) (b := Shape.lam f') hΔ h.2.2)
        exact ⟨⟨PiLabelEq.refl hA hB, (ih hd hy.2.2.1 h.2.1).1,
            ShapeFun.LE.append_left hff hfg⟩,
          ⟨h.1.symm hΔ, (ih hd hy.2.2.1 h.2.1).2,
            ShapeFun.LE.append_right hy.2.2.2 hfg⟩⟩
      | _ => exact absurd h id
    | succ v =>
      cases y with
      | bot => exact ⟨.refl hx, trivial⟩
      | lam f' => exact absurd h id
      | succ v' => exact ⟨(ih hx hy h).1, (ih hx hy h).2⟩
      | _ => exact absurd h id
    | refl u =>
      cases y with
      | bot => exact ⟨.refl hx, trivial⟩
      | lam f' => exact absurd h id
      | refl u' => exact ⟨(ih hx hy h).1, (ih hx hy h).2⟩
      | _ => exact absurd h id
    | pair a b =>
      cases y with
      | bot => exact ⟨.refl hx, trivial⟩
      | lam f' => exact absurd h id
      | pair ty' tm' a' b' =>
        have ⟨⟨_, hty⟩, htm, hxa, hxb, _⟩ := hx
        have ⟨_, _, hya, hyb, _⟩ := hy
        exact ⟨⟨LabelEq.refl hty htm, (ih hxa hya h.2.1).1, (ih hxb hyb h.2.2).1⟩,
          ⟨h.1.symm, (ih hxa hya h.2.1).2, (ih hxb hyb h.2.2).2⟩⟩
      | _ => exact absurd h id
    | sort r =>
      cases y with
      | bot => exact ⟨.refl hx, trivial⟩
      | lam f' => exact absurd h id
      | sort r' => exact ⟨rfl, Eq.symm (show r = r' from h)⟩
      | _ => exact absurd h id
    | unit r =>
      cases y with
      | bot => exact ⟨.refl hx, trivial⟩
      | lam f' => exact absurd h id
      | unit r' => exact ⟨rfl, Eq.symm (show r = r' from h)⟩
      | _ => exact absurd h id
    | nat =>
      cases y with
      | bot => exact ⟨.refl hx, trivial⟩
      | lam f' => exact absurd h id
      | nat => exact ⟨trivial, trivial⟩
      | _ => exact absurd h id
    | zero =>
      cases y with
      | bot => exact ⟨.refl hx, trivial⟩
      | lam f' => exact absurd h id
      | zero => exact ⟨trivial, trivial⟩
      | _ => exact absurd h id
    | id r A a b =>
      cases y with
      | bot => exact ⟨.refl hx, trivial⟩
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
  exact fun w => ⟨fun hw => ⟨hl.trans hΔ hw, hr.trans hΔ hw⟩, fun ⟨h₁, h₂⟩ => Shape.join_le hΔ h₁ h₂⟩

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
    | pair a b => exact ⟨ih h.1, ih h.2⟩
    | _ => exact absurd h id

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
      | pair ty' tm' a' b' =>
        exact ⟨hy.1, hy.2.1, ih hΔ hc.2.1 hy.2.2.1 hz.2.2.1,
          ih hΔ hc.2.2 hy.2.2.2.1 hz.2.2.2.1,
          fun hb => hy.2.2.2.2
            ⟨Shape.IsBot.of_join_left hb.1, Shape.IsBot.of_join_left hb.2⟩⟩
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
    | pair ty tm a b =>
      have ⟨⟨_, hty⟩, htm, ha, hb, _⟩ := hs
      exact ⟨LabelEq.refl hty htm, ih ha, ih hb⟩
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

/-! ## The lookup's own theory, and reflection of the order along `lift`

`Eval.wf` and `Eval.compat` are what the lookup's two side conditions were
put there for, and `Eval.lift_of` is what they buy: a lookup over a lifted
graph lands below the lift of a lookup over the original.  With that, the
order reflects along `lift`, which is what makes the level index invisible
(`TShape.LE.def`).  Entry coverage would get the reflection for free —
entries of `f.lift` are lifts of entries of `f` — but could not express η;
this is the trade. -/

/-- Everything the lookup returns is well formed. -/
theorem ShapeFun.Eval.wf {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a : Term}
    {x : Shape n} (hf : ∀ e ∈ f, Shape.WF Δ e.out) :
    ∀ {y : Shape n}, ShapeFun.Eval Δ (Shape.LE Δ) f A a x y → Shape.WF Δ y := by
  intro y h
  induction h with
  | bot => cases n <;> trivial
  | entry e he _ _ => exact hf e he
  | lower hw _ _ _ => exact hw
  | join hc _ _ ih₁ ih₂ => exact Shape.WF.join hΔ hc ih₁ ih₂

/-- Any two values of one lookup are compatible, given a coherent graph
and a coherent query. -/
theorem ShapeFun.Eval.compat {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a : Term}
    {x : Shape n} (hf : ShapeFun.Compat Shape.Compat Δ f f) (hx : Shape.Compat Δ x x)
    {y z : Shape n} (hy : ShapeFun.Eval Δ (Shape.LE Δ) f A a x y)
    (hz : ShapeFun.Eval Δ (Shape.LE Δ) f A a x z) : Shape.Compat Δ y z := by
  induction hy with
  | bot => exact .bot_left
  | lower _ hle _ ih => exact ih.symm hΔ |>.anti_right hΔ hle |>.symm hΔ
  | join _ _ _ ih₁ ih₂ => exact ih₁.join hΔ ih₂
  | entry e he hlab hin
  induction hz with
  | bot => exact .bot_right
  | entry e' he' hlab' hin' =>
    simpa using hf e he e' he' Δ .id hΔ (.id hΔ)
      (by simpa using hlab.trans hlab'.symm)
      (by simpa using hx.of_common_upper hΔ hin hin')
  | lower _ hle _ ih => exact ih.anti_right hΔ hle
  | join _ _ _ ih₁ ih₂ => exact ((ih₁.symm hΔ).join hΔ (ih₂.symm hΔ)).symm hΔ

/-- A lookup transports up a level. -/
theorem ShapeFun.Eval.lift {Δ : List Term} {n k} (h : n ≤ k) {f : ShapeFun n}
    {A a : Term} {x c : Shape n}
    (ihlift : ∀ {u v : Shape n}, Shape.LE Δ u v → Shape.LE Δ (u.lift k) (v.lift k))
    (H : ShapeFun.Eval Δ (Shape.LE Δ) f A a x c) :
    ShapeFun.Eval Δ (Shape.LE Δ) (ShapeFun.lift (Shape.lift k) f) A a (x.lift k) (c.lift k) := by
  induction H with
  | bot => rw [Shape.lift_bot]; exact .bot
  | entry e he hlab hin =>
    exact .entry _ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩) hlab (ihlift hin)
  | lower hw hle _ ih => exact .lower ((Shape.lift_wf h).2 hw) (ihlift hle) ih
  | join hc _ _ ih₁ ih₂ =>
    exact Shape.lift_join h ▸ .join ((Shape.lift_compat h).2 hc) ih₁ ih₂

/-- A lookup over a lifted graph lands below the lift of a lookup over the
original.  The `join` case is where the side conditions earn their keep:
the two reflected values are compatible (`Eval.compat`) and well formed
(`Eval.wf`), so `le_join` applies and their join is an upper bound. -/
theorem ShapeFun.Eval.lift_of {Δ : List Term} (hΔ : ⊢ Δ) {n k} (h : n ≤ k) {f : ShapeFun n}
    {A a : Term} {x : Shape n}
    (ihlift : ∀ {u v : Shape n}, Shape.LE Δ (u.lift k) (v.lift k) ↔ Shape.LE Δ u v)
    (hwf : ShapeFun.WF Δ (Shape.WF Δ) f) (hco : ShapeFun.Compat Shape.Compat Δ f f)
    (hwx : Shape.WF Δ x) :
    ∀ {c' : Shape k},
      ShapeFun.Eval Δ (Shape.LE Δ) (ShapeFun.lift (Shape.lift k) f) A a (x.lift k) c' →
      ∃ c, Shape.LE Δ c' (c.lift k) ∧ ShapeFun.Eval Δ (Shape.LE Δ) f A a x c := by
  intro c' H
  induction H with
  | bot => exact ⟨.bot, by rw [Shape.lift_bot]; exact .bot, .bot⟩
  | entry e' he' hlab hin =>
    obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he'
    exact ⟨e.out, Shape.LE.refl ((Shape.lift_wf h).2 (hwf.1 e he).2.2.2),
      .entry e he hlab (ihlift.1 hin)⟩
  | lower _ hle _ ih =>
    have ⟨c, hc, hev⟩ := ih
    exact ⟨c, hle.trans hΔ hc, hev⟩
  | join _ _ _ ih₁ ih₂ =>
    have ⟨c₁, hc₁, hev₁⟩ := ih₁
    have ⟨c₂, hc₂, hev₂⟩ := ih₂
    have houts : ∀ e ∈ f, Shape.WF Δ e.out := fun e he => (hwf.1 e he).2.2.2
    have hcc : Shape.Compat Δ c₁ c₂ :=
      ShapeFun.Eval.compat hΔ hco hwx.coherent hev₁ hev₂
    have hw₁ := ShapeFun.Eval.wf hΔ houts hev₁
    have hw₂ := ShapeFun.Eval.wf hΔ houts hev₂
    have ⟨hu₁, hu₂⟩ := Shape.le_join hΔ hw₁ hw₂ hcc
    exact ⟨c₁.join c₂,
      Shape.join_le hΔ (hc₁.trans hΔ (ihlift.2 hu₁)) (hc₂.trans hΔ (ihlift.2 hu₂)),
      .join hcc hev₁ hev₂⟩


/-- Lifting *up* is an order embedding.  This is what makes the level
index invisible to `TShape.LE`: master's `lift_le_lift`, and the reason
its proof is a plain induction here rather than a `simp` over a `Bool`
function is that the order is `Prop`-valued. -/
theorem Shape.lift_le_lift (hΓ : ⊢ Γ) {n m} (h : n ≤ m) {s t : Shape n} :
    Shape.LE Γ (s.lift m) (t.lift m) ↔ Shape.LE Γ s t := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rw [Shape.lift_self, Shape.lift_self]
    | succ m => cases s <;> cases t <;> rfl
  | succ n ih
  let m+1 := m; have h' := Nat.le_of_succ_le_succ h
  have hwfiff : ∀ {f : ShapeFun n},
      ShapeFun.WF Γ (Shape.WF Γ) (ShapeFun.lift (Shape.lift m) f) ↔
      ShapeFun.WF Γ (Shape.WF Γ) f := by
    intro f
    refine and_congr ?_ (ShapeFun.lift_compat h')
    constructor
    · intro H e he
      have ⟨hty, htm, hin, hout⟩ :=
        H ⟨e.ty, e.tm, e.inp.lift m, e.out.lift m⟩ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)
      exact ⟨hty, htm, (Shape.lift_wf h').1 hin, (Shape.lift_wf h').1 hout⟩
    · intro H e' he'
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he'
      have ⟨hty, htm, hin, hout⟩ := H e he
      exact ⟨hty, htm, (Shape.lift_wf h').2 hin, (Shape.lift_wf h').2 hout⟩
  -- `←` is `Eval.lift`, `→` is `Eval.lift_of` followed by `Eval.lower`.
  -- The well-formedness both of those want is not a hypothesis of this
  -- lemma: the order on graphs carries it, so `H` supplies it itself.
  have ihf : ∀ {f f' : ShapeFun n},
      ShapeFun.LE Γ (Shape.LE Γ) (Shape.WF Γ) (ShapeFun.lift (Shape.lift m) f)
        (ShapeFun.lift (Shape.lift m) f') ↔
      ShapeFun.LE Γ (Shape.LE Γ) (Shape.WF Γ) f f' := by
    intro f f'
    refine ⟨fun H => ⟨fun e he => ?_, hwfiff.1 H.2.1, hwfiff.1 H.2.2⟩,
      fun H => ⟨fun e' he' => ?_, hwfiff.2 H.2.1, hwfiff.2 H.2.2⟩⟩
    · have hlk := H.1 ⟨e.ty, e.tm, e.inp.lift m, e.out.lift m⟩
        (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)
      have hwf' := hwfiff.1 H.2.2
      have hwe := (hwfiff.1 H.2.1).1 e he
      have ⟨c, hc, hev⟩ :=
        ShapeFun.Eval.lift_of hΓ h' (ih h') hwf' hwf'.2 hwe.2.2.1 hlk
      exact .lower hwe.2.2.2 ((ih h').1 hc) hev
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he'
      exact ShapeFun.Eval.lift h' (ih h').2 (H.1 e he)
  cases s <;> cases t <;> (try rfl)
  · exact and_congr Iff.rfl (and_congr (ih h') ihf)
  · exact ihf
  · exact and_congr Iff.rfl (and_congr (ih h') ihf)
  · exact and_congr Iff.rfl (and_congr (ih h') (ih h'))
  · exact ih h'
  · exact ih h'

/-- Lifting *preserves* the order, with no hypothesis on the context.

Split off from `lift_le_lift` deliberately.  Only the reflection direction
needs `⊢ Γ` — through `Eval.lift_of`, which uses `Eval.compat` and
`le_join` — and reflection is the minority use (a `TShape.LE` is *read* at
a higher level far more often than it is *built* from one).  Keeping
preservation hypothesis-free is what stops `⊢ Δ` from spreading to every
site that mentions the order, `Interp.sort'` among them. -/
theorem Shape.lift_le {n m} (h : n ≤ m) :
    ∀ {s t : Shape n}, Shape.LE Γ s t → Shape.LE Γ (s.lift m) (t.lift m) := by
  induction n generalizing m with
  | zero =>
    intro s t H
    cases m with
    | zero => rwa [Shape.lift_self, Shape.lift_self]
    | succ m => cases s <;> cases t <;> first | exact H | trivial | exact absurd H id
  | succ n ih
  let m+1 := m; have h' := Nat.le_of_succ_le_succ h
  have hwf {f : ShapeFun n} (H : ShapeFun.WF Γ (Shape.WF Γ) f) :
      ShapeFun.WF Γ (Shape.WF Γ) (ShapeFun.lift (Shape.lift m) f) := by
    refine ⟨fun e' he' => ?_, (ShapeFun.lift_compat h').2 H.2⟩
    obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he'
    have ⟨hty, htm, hin, hout⟩ := H.1 e he
    exact ⟨hty, htm, (Shape.lift_wf h').2 hin, (Shape.lift_wf h').2 hout⟩
  have hfun {f f' : ShapeFun n} (H : ShapeFun.LE Γ (Shape.LE Γ) (Shape.WF Γ) f f') :
      ShapeFun.LE Γ (Shape.LE Γ) (Shape.WF Γ) (ShapeFun.lift (Shape.lift m) f)
        (ShapeFun.lift (Shape.lift m) f') := by
    refine ⟨fun e' he' => ?_, hwf H.2.1, hwf H.2.2⟩
    obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he'
    exact ShapeFun.Eval.lift h' (ih h') (H.1 e he)
  intro s t H
  cases s <;> cases t <;> first
    | exact H
    | trivial
    | exact absurd H id
    | exact ih h' H
    | exact hfun H
    | exact ⟨H.1, ih h' H.2.1, hfun H.2.2⟩
    | exact ⟨H.1, ih h' H.2.1, ih h' H.2.2⟩

/-! ## The total shape domain, continued

These need the order, the join and the lift lemmas, so they come after
them rather than beside the definition of `TShape`. -/

namespace TShape

/-- Compatibility and the join, at any common level above both. -/
def Compat (Δ : List Term) (a b : TShape) : Prop :=
  Shape.Compat Δ (a.2.lift (max a.1 b.1)) (b.2.lift (max a.1 b.1))

def join (a b : TShape) : TShape :=
  ⟨max a.1 b.1, (a.2.lift (max a.1 b.1)).join (b.2.lift (max a.1 b.1))⟩

/-! The four `def` lemmas below say that the canonical level in each
definition can be replaced by any level above both arguments.  They are
what makes the level index invisible, and each is exactly one of the
`lift_*` lemmas sandwiched between two uses of `lift_lift`. -/

/-- Reading a `TShape.LE` at any level above both.  This is the
preservation half of `LE.def` and needs no hypothesis on the context;
`LE.def` itself does, because its other half reflects along `lift`. -/
theorem LE.def_mp {Δ : List Term} {a b : TShape} {k} (h1 : a.1 ≤ k) (h2 : b.1 ≤ k)
    (h : TShape.LE Δ a b) : Shape.LE Δ (a.2.lift k) (b.2.lift k) := by
  rw [show a.2.lift k = (a.2.lift (max a.1 b.1)).lift k from
        (Shape.lift_lift (Nat.le_max_left ..)).symm,
      show b.2.lift k = (b.2.lift (max a.1 b.1)).lift k from
        (Shape.lift_lift (Nat.le_max_right ..)).symm]
  exact Shape.lift_le (Nat.max_le.2 ⟨h1, h2⟩) h

theorem LE.def {Δ : List Term} (hΔ : ⊢ Δ) {a b : TShape} {k} (h1 : a.1 ≤ k) (h2 : b.1 ≤ k) :
    TShape.LE Δ a b ↔ Shape.LE Δ (a.2.lift k) (b.2.lift k) := by
  rw [show a.2.lift k = (a.2.lift (max a.1 b.1)).lift k from
        (Shape.lift_lift (Nat.le_max_left ..)).symm,
      show b.2.lift k = (b.2.lift (max a.1 b.1)).lift k from
        (Shape.lift_lift (Nat.le_max_right ..)).symm,
      Shape.lift_le_lift hΔ (Nat.max_le.2 ⟨h1, h2⟩)]
  exact Iff.rfl

theorem WF.def {Δ : List Term} {a : TShape} {k} (h : a.1 ≤ k) :
    TShape.WF Δ a ↔ Shape.WF Δ (a.2.lift k) := by
  rw [Shape.lift_wf h]; exact Iff.rfl

theorem Compat.def {Δ : List Term} {a b : TShape} {k} (h1 : a.1 ≤ k) (h2 : b.1 ≤ k) :
    TShape.Compat Δ a b ↔ Shape.Compat Δ (a.2.lift k) (b.2.lift k) := by
  rw [show a.2.lift k = (a.2.lift (max a.1 b.1)).lift k from
        (Shape.lift_lift (Nat.le_max_left ..)).symm,
      show b.2.lift k = (b.2.lift (max a.1 b.1)).lift k from
        (Shape.lift_lift (Nat.le_max_right ..)).symm,
      Shape.lift_compat (Nat.max_le.2 ⟨h1, h2⟩)]
  exact Iff.rfl

theorem join.def {a b : TShape} {k} (h1 : a.1 ≤ k) (h2 : b.1 ≤ k) :
    (TShape.join a b).2.lift k = (a.2.lift k).join (b.2.lift k) := by
  rw [show a.2.lift k = (a.2.lift (max a.1 b.1)).lift k from
        (Shape.lift_lift (Nat.le_max_left ..)).symm,
      show b.2.lift k = (b.2.lift (max a.1 b.1)).lift k from
        (Shape.lift_lift (Nat.le_max_right ..)).symm,
      Shape.lift_join (Nat.max_le.2 ⟨h1, h2⟩)]
  rfl

@[simp] theorem join_fst {a b : TShape} : (TShape.join a b).1 = max a.1 b.1 := rfl

/-! The order at the total level, from the order at each level. -/

theorem LE.refl {Δ : List Term} {a : TShape} (h : TShape.WF Δ a) : TShape.LE Δ a a :=
  Shape.LE.refl ((Shape.lift_wf (Nat.le_max_left ..)).2 h)

theorem LE.trans {Δ : List Term} (hΔ : ⊢ Δ) {a b c : TShape}
    (h1 : TShape.LE Δ a b) (h2 : TShape.LE Δ b c) : TShape.LE Δ a c := by
  have ha : a.1 ≤ max (max a.1 b.1) c.1 :=
    Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..)
  have hb : b.1 ≤ max (max a.1 b.1) c.1 :=
    Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..)
  have hc : c.1 ≤ max (max a.1 b.1) c.1 := Nat.le_max_right ..
  exact (LE.def hΔ ha hc).2
    (Shape.LE.trans hΔ ((LE.def_mp ha hb) h1) ((LE.def_mp hb hc) h2))

@[simp] theorem bot_le {Δ : List Term} {a : TShape} : TShape.LE Δ TShape.bot a := by
  show Shape.LE Δ _ _
  simp only [TShape.bot, Shape.T, Shape.lift_bot]
  exact Shape.LE.bot

/-- The order between two shapes at the *same* level is the level's own
order: the common case, and the one that needs no arithmetic. -/
theorem LE.T {Δ : List Term} {n} {s t : Shape n} :
    TShape.LE Δ (Shape.T s) (Shape.T t) ↔ Shape.LE Δ s t := by
  show Shape.LE Δ (s.lift (max n n)) (t.lift (max n n)) ↔ _
  rw [Nat.max_self, Shape.lift_self, Shape.lift_self]

theorem WF.T {Δ : List Term} {n} {s : Shape n} :
    TShape.WF Δ (Shape.T s) ↔ Shape.WF Δ s := Iff.rfl

theorem Compat.T {Δ : List Term} {n} {s t : Shape n} :
    TShape.Compat Δ (Shape.T s) (Shape.T t) ↔ Shape.Compat Δ s t := by
  refine Iff.trans (Compat.def (Nat.le_refl n) (Nat.le_refl n)) ?_
  rw [Shape.lift_self, Shape.lift_self]

/-- The join of two shapes at the same level, read back at that level.
Stated through `lift` rather than as an equation of `TShape`s because
`max n n` is only propositionally `n`. -/
theorem join.T {n} {s t : Shape n} :
    (TShape.join (Shape.T s) (Shape.T t)).2.lift n = s.join t := by
  rw [join.def (a := Shape.T s) (b := Shape.T t) (Nat.le_refl n) (Nat.le_refl n),
    Shape.lift_self, Shape.lift_self]

end TShape

/-- Anything below an information-free shape is information-free.  The
`TShape` form of `Shape.le_bot_iff`, needed because `Interp`'s `bot` rule
is indexed by a level. -/
theorem TShape.le_bot {Δ : List Term} (hΔ : ⊢ Δ) {a b : TShape} (hb : b.2 = Shape.bot)
    (h : TShape.LE Δ a b) : a.2 = Shape.bot := by
  have hk : a.1 ≤ max a.1 b.1 := Nat.le_max_left ..
  have h' := (TShape.LE.def_mp (Nat.le_max_left ..) (Nat.le_max_right ..)) h
  rw [hb, Shape.lift_bot,
    show (Shape.bot : Shape (max a.1 b.1)) = (Shape.bot : Shape a.1).lift _ from
      Shape.lift_bot.symm] at h'
  exact Shape.le_bot_iff.1 ((Shape.lift_le_lift hΔ hk).1 h')

/-- `⊥` at any level is below everything.  The companion of
`TShape.le_bot`, for the same reason: `Interp`'s `bot` rule is indexed by
a level, so its witness is not literally `TShape.bot`. -/
theorem TShape.bot_le' {Δ : List Term} {a b : TShape} (ha : a.2 = Shape.bot) :
    TShape.LE Δ a b := by
  show Shape.LE Δ (a.2.lift (max a.1 b.1)) _
  rw [ha, Shape.lift_bot]
  exact Shape.LE.bot

theorem TShape.le_bot_iff {Δ : List Term} (hΔ : ⊢ Δ) {a : TShape} :
    TShape.LE Δ a TShape.bot ↔ a.2 = .bot :=
  ⟨TShape.le_bot hΔ rfl, TShape.bot_le'⟩

/-- Reindexing the total shape domain along a typed substitution.  The
`TShape` forms of `Shape.LE.subst` and `Shape.WF.subst`: the level is
untouched, so the canonical level of the pair is untouched too. -/
@[simp] theorem TShape.subst_fst {a : TShape} {τ : Subst} : (a.subst τ).1 = a.1 := rfl

@[simp] theorem TShape.subst_T {n} {s : Shape n} {τ : Subst} :
    (Shape.T s).subst τ = Shape.T (s.subst τ) := rfl

@[simp] theorem TShape.subst_bot {τ : Subst} : TShape.bot.subst τ = TShape.bot := rfl

@[simp] theorem TShape.subst_sort {r : Bool} {τ : Subst} :
    (TShape.sort r).subst τ = TShape.sort r := rfl

theorem TShape.LE.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {a b : TShape} (h : TShape.LE Δ a b) :
    TShape.LE Θ (a.subst τ) (b.subst τ) := by
  refine (TShape.LE.def hΘ (Nat.le_max_left ..) (Nat.le_max_right ..)).2 ?_
  show Shape.LE Θ (Shape.lift (max a.1 b.1) (a.2.subst τ))
    (Shape.lift (max a.1 b.1) (b.2.subst τ))
  rw [Shape.lift_subst, Shape.lift_subst]
  exact Shape.LE.subst hΘ W ((TShape.LE.def_mp (Nat.le_max_left ..) (Nat.le_max_right ..)) h)

theorem TShape.WF.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {a : TShape} (h : TShape.WF Δ a) :
    TShape.WF Θ (a.subst τ) := Shape.WF.subst hΘ W h

/-- The **label-only Π shape**: the other repo's `piAtom`.  A Π-shape with
no information in it but the syntactic pair.  It is the probe that reads a
label back out of a Π type, and the reason is the order: a `piAtom` is
below `forallE A B d f` exactly when the labels are definitionally equal,
because the other two components of the clause are discharged by `⊥ ≤ d`
and `[] ≤ f`. -/
abbrev Shape.piAtom {n} (A B : Term) : Shape (n+1) := ShapeS.forallE A B .bot []

theorem Shape.piAtom_le_forallE {Δ : List Term} {n} {A B A' B' : Term}
    {d : Shape n} {f : ShapeFun n}
    (h : Shape.LE Δ (Shape.piAtom A B) (ShapeS.forallE A' B' d f : Shape (n+1))) :
    PiLabelEq Δ A B A' B' := h.1

theorem Shape.piAtom_le {Δ : List Term} {n} {A B A' B' : Term}
    {d : Shape n} {f : ShapeFun n} (h : PiLabelEq Δ A B A' B')
    (hf : ShapeFun.WF Δ (Shape.WF Δ) f) :
    Shape.LE Δ (Shape.piAtom A B) (ShapeS.forallE A' B' d f : Shape (n+1)) :=
  ⟨h, Shape.LE.bot, fun _ he => absurd he List.not_mem_nil,
    ⟨fun _ he => absurd he List.not_mem_nil, fun _ he => absurd he List.not_mem_nil⟩, hf⟩

@[simp] theorem Shape.lift_piAtom {n m} {A B : Term} :
    (Shape.piAtom (n := n) A B).lift (m+1) = Shape.piAtom A B := by
  show ShapeS.forallE _ _ _ _ = _
  rw [Shape.lift_bot]; rfl

theorem Shape.WF.piAtom {Δ : List Term} {n} {A B : Term} {u v}
    (hA : Δ ⊢ A : .sort u) (hB : A :: Δ ⊢ B : .sort v) :
    Shape.WF Δ (Shape.piAtom (n := n) A B) :=
  ⟨⟨u, hA⟩, ⟨v, hB⟩, by cases n <;> trivial,
    fun _ he => absurd he (List.not_mem_nil),
    fun _ he => absurd he (List.not_mem_nil)⟩

/-- `⊥` is well formed at every level. -/
@[simp] theorem TShape.WF.bot {Δ : List Term} {n} :
    TShape.WF Δ (Shape.T (n := n) Shape.bot) := by cases n <;> trivial

/-! ## The join at the total level

The four facts directedness needs, lifted from `Shape` to `TShape`.  Each
is the level-`n` statement sandwiched between two uses of the `def` lemma
that replaces the canonical level by a common one. -/

namespace TShape

theorem join_le {Δ : List Term} (hΔ : ⊢ Δ) {x y w : TShape}
    (h₁ : TShape.LE Δ x w) (h₂ : TShape.LE Δ y w) : TShape.LE Δ (x.join y) w := by
  have hx : x.1 ≤ max (max x.1 y.1) w.1 :=
    Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..)
  have hy : y.1 ≤ max (max x.1 y.1) w.1 :=
    Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..)
  have hw : w.1 ≤ max (max x.1 y.1) w.1 := Nat.le_max_right ..
  refine (TShape.LE.def hΔ (Nat.max_le.2 ⟨hx, hy⟩) hw).2 ?_
  rw [TShape.join.def hx hy]
  exact Shape.join_le hΔ ((TShape.LE.def_mp hx hw) h₁) ((TShape.LE.def_mp hy hw) h₂)

theorem le_join {Δ : List Term} (hΔ : ⊢ Δ) {x y : TShape}
    (hx : TShape.WF Δ x) (hy : TShape.WF Δ y) (hc : TShape.Compat Δ x y) :
    TShape.LE Δ x (x.join y) ∧ TShape.LE Δ y (x.join y) := by
  have h₁ : x.1 ≤ max x.1 y.1 := Nat.le_max_left ..
  have h₂ : y.1 ≤ max x.1 y.1 := Nat.le_max_right ..
  have hj : (x.join y).1 ≤ max x.1 y.1 := Nat.le_refl _
  have hjx := Shape.le_join hΔ ((TShape.WF.def h₁).1 hx) ((TShape.WF.def h₂).1 hy)
    ((TShape.Compat.def h₁ h₂).1 hc)
  rw [← TShape.join.def h₁ h₂] at hjx
  exact ⟨(TShape.LE.def hΔ h₁ hj).2 hjx.1, (TShape.LE.def hΔ h₂ hj).2 hjx.2⟩

theorem Compat.of_common_upper {Δ : List Term} (hΔ : ⊢ Δ) {a b c : TShape}
    (hc : TShape.WF Δ c) (h₁ : TShape.LE Δ a c) (h₂ : TShape.LE Δ b c) :
    TShape.Compat Δ a b := by
  have ha : a.1 ≤ max (max a.1 b.1) c.1 :=
    Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..)
  have hb : b.1 ≤ max (max a.1 b.1) c.1 :=
    Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..)
  have hcc : c.1 ≤ max (max a.1 b.1) c.1 := Nat.le_max_right ..
  exact (TShape.Compat.def ha hb).2 <| Shape.Compat.of_common_upper hΔ
    (Shape.WF.coherent ((TShape.WF.def hcc).1 hc))
    ((TShape.LE.def_mp ha hcc) h₁) ((TShape.LE.def_mp hb hcc) h₂)

theorem WF.join {Δ : List Term} (hΔ : ⊢ Δ) {y z : TShape}
    (hc : TShape.Compat Δ y z) (hy : TShape.WF Δ y) (hz : TShape.WF Δ z) :
    TShape.WF Δ (y.join z) := by
  have h₁ : y.1 ≤ max y.1 z.1 := Nat.le_max_left ..
  have h₂ : z.1 ≤ max y.1 z.1 := Nat.le_max_right ..
  show Shape.WF Δ ((Shape.lift (max y.1 z.1) y.2).join (Shape.lift (max y.1 z.1) z.2))
  exact Shape.WF.join hΔ ((TShape.Compat.def h₁ h₂).1 hc)
    ((TShape.WF.def h₁).1 hy) ((TShape.WF.def h₂).1 hz)

end TShape

/-! ## Normalising the level

A shape and its lift are equivalent in the order, so any shape may be
moved to a higher level without changing what it approximates.  This is
what lets a proof put every shape in sight at one level before touching
`HasType`, whose transport only goes up (§4.5c of `presheaf-plan.md`). -/

namespace TShape

/-- Move a shape up to level `k`. -/
def lift (m : TShape) (k : Nat) : TShape := ⟨k, m.2.lift k⟩

@[simp] theorem lift_fst {m : TShape} {k} : (m.lift k).1 = k := rfl

theorem WF.lift {Δ : List Term} {m : TShape} {k} (hk : m.1 ≤ k)
    (h : TShape.WF Δ m) : TShape.WF Δ (m.lift k) := (Shape.lift_wf hk).2 h

theorem LE.lift_le {Δ : List Term} (hΔ : ⊢ Δ) {m : TShape} {k} (hk : m.1 ≤ k)
    (h : TShape.WF Δ m) : TShape.LE Δ (m.lift k) m := by
  refine (TShape.LE.def hΔ (Nat.le_refl _) hk).2 ?_
  show Shape.LE Δ (Shape.lift k (m.2.lift k)) (m.2.lift k)
  rw [Shape.lift_self]
  exact Shape.LE.refl ((Shape.lift_wf hk).2 h)

theorem LE.le_lift {Δ : List Term} (hΔ : ⊢ Δ) {m : TShape} {k} (hk : m.1 ≤ k)
    (h : TShape.WF Δ m) : TShape.LE Δ m (m.lift k) := by
  refine (TShape.LE.def hΔ hk (Nat.le_refl _)).2 ?_
  show Shape.LE Δ (m.2.lift k) (Shape.lift k (m.2.lift k))
  rw [Shape.lift_self]
  exact Shape.LE.refl ((Shape.lift_wf hk).2 h)

end TShape

/-- Lifting *up* reflects being `⊥`. -/
theorem Shape.lift_eq_bot {Δ : List Term} (hΔ : ⊢ Δ) {n k} (h : n ≤ k) {s : Shape n}
    (hs : s.lift k = Shape.bot) : s = Shape.bot := by
  refine Shape.le_bot_iff.1 ((Shape.lift_le_lift (Γ := Δ) hΔ h).1 ?_)
  rw [Shape.lift_bot, hs]
  exact Shape.LE.bot

/-- Anything below `prop` is `⊥` or `prop` itself. -/
theorem Shape.le_prop_cases {Δ : List Term} : ∀ {n} {x : Shape n},
    Shape.LE Δ x (Shape.sort false) → x = Shape.bot ∨ x = Shape.sort false := by
  intro n x h
  cases n <;> cases x <;>
    first
      | exact .inl rfl
      | exact absurd h id
      | exact .inr (by rename_i r; cases (h : r = false); rfl)

/-! ## Least upper bounds of finite lists

A list of shapes has a join only when its members are pairwise
compatible, so the cycle argument -- which has to *talk* about the join of
an arbitrary sublist of a graph before knowing that it exists -- needs the
join relationally rather than as an operation.  `Joins` is the least upper
bound spelled out by its universal property; it is pinned only up to
mutual `≤`, which is all this order provides (labels are compared up to
definitional equality, so `LE` is a preorder, not a partial order). -/

/-- `j` is a least upper bound of the list `s`, stated by the universal
property `j ≤ w ↔ ∀ x ∈ s, x ≤ w`.

The quantifier ranges over **well-formed** `w` only: `LE Δ` compares
labels by definitional equality in `Δ`, which is reflexive only on
well-typed terms, so `LE Δ j w` for an ill-formed `w` is not a meaningful
constraint and there is no reason to be below every such `w`.  With that
restriction the two halves of the property are `Joins.le` (which needs
`WF Δ j`, since it instantiates at `w := j`) and `Joins.min`. -/
def Shape.Joins (Δ : List Term) {n} (s : List (Shape n)) (j : Shape n) : Prop :=
  ∀ w, Shape.WF Δ w → (Shape.LE Δ j w ↔ ∀ x ∈ s, Shape.LE Δ x w)

/-- Build a `Joins` from the two halves. -/
theorem Shape.Joins.of {Δ : List Term} (hΔ : ⊢ Δ) {n} {s : List (Shape n)} {j : Shape n}
    (hup : ∀ x ∈ s, Shape.LE Δ x j)
    (hmin : ∀ w, Shape.WF Δ w → (∀ x ∈ s, Shape.LE Δ x w) → Shape.LE Δ j w) :
    Shape.Joins Δ s j :=
  fun w hw => ⟨fun hjw x hx => (hup x hx).trans hΔ hjw, hmin w hw⟩

/-- `j` is an upper bound. -/
theorem Shape.Joins.le {Δ : List Term} {n} {s : List (Shape n)} {j : Shape n}
    (hj : Shape.WF Δ j) (h : Shape.Joins Δ s j) : ∀ x ∈ s, Shape.LE Δ x j :=
  (h j hj).1 (Shape.LE.refl hj)

/-- `j` is the least one. -/
theorem Shape.Joins.min {Δ : List Term} {n} {s : List (Shape n)} {j w : Shape n}
    (h : Shape.Joins Δ s j) (hw : Shape.WF Δ w) (hle : ∀ x ∈ s, Shape.LE Δ x w) :
    Shape.LE Δ j w := (h w hw).2 hle

/-- A least upper bound is unique up to mutual `≤`. -/
theorem Shape.Joins.uniq {Δ : List Term} {n} {s : List (Shape n)} {j j' : Shape n}
    (hj : Shape.WF Δ j) (hj' : Shape.WF Δ j')
    (h : Shape.Joins Δ s j) (h' : Shape.Joins Δ s j') :
    Shape.LE Δ j j' ∧ Shape.LE Δ j' j :=
  ⟨h.min hj' (h'.le hj'), h'.min hj (h.le hj)⟩

/-- `Joins` sees only the members of the list, not its order or
multiplicities.  This is what lets the sublist produced by
`List.Sublist.union` stand in for a concatenation. -/
theorem Shape.Joins.mem_congr {Δ : List Term} {n} {s t : List (Shape n)} {j : Shape n}
    (hst : ∀ x ∈ t, x ∈ s) (hts : ∀ x ∈ s, x ∈ t) (h : Shape.Joins Δ s j) :
    Shape.Joins Δ t j :=
  fun w hw => (h w hw).trans
    ⟨fun H x hx => H x (hst x hx), fun H x hx => H x (hts x hx)⟩

theorem Shape.Joins.nil {Δ : List Term} {n} : Shape.Joins Δ ([] : List (Shape n)) .bot :=
  fun _ _ => ⟨fun _ => nofun, fun _ => Shape.LE.bot⟩

theorem Shape.Joins.singleton {Δ : List Term} (hΔ : ⊢ Δ) {n} {x : Shape n}
    (hx : Shape.WF Δ x) : Shape.Joins Δ [x] x :=
  .of hΔ (fun y hy => by cases List.mem_singleton.1 hy; exact Shape.LE.refl hx)
    (fun _ _ hw => hw _ (.head _))

/-- Consing on: the binary `join` computes the least upper bound of the
extended list, given that it is a least upper bound of the two shapes. -/
theorem Shape.Joins.cons {Δ : List Term} (hΔ : ⊢ Δ) {n} {x j : Shape n} {s : List (Shape n)}
    (hx : Shape.WF Δ x) (hj : Shape.WF Δ j) (hc : Shape.Compat Δ x j)
    (h : Shape.Joins Δ s j) : Shape.Joins Δ (x :: s) (x.join j) := by
  have ⟨hu₁, hu₂⟩ := Shape.le_join hΔ hx hj hc
  refine .of hΔ (fun y hy => ?_) fun w hw hle =>
    Shape.join_le hΔ (hle x (.head _)) (h.min hw fun y hy => hle y (.tail _ hy))
  match List.mem_cons.1 hy with
  | .inl h' => cases h'; exact hu₁
  | .inr h' => exact (h.le hj y h').trans hΔ hu₂

/-- Appending: the two joins join. -/
theorem Shape.Joins.append {Δ : List Term} (hΔ : ⊢ Δ) {n} {s t : List (Shape n)}
    {j k : Shape n} (hj : Shape.WF Δ j) (hk : Shape.WF Δ k) (hc : Shape.Compat Δ j k)
    (hs : Shape.Joins Δ s j) (ht : Shape.Joins Δ t k) :
    Shape.Joins Δ (s ++ t) (j.join k) :=
  have ⟨hu₁, hu₂⟩ := Shape.le_join hΔ hj hk hc
  .of hΔ
    (fun y hy => match List.mem_append.1 hy with
      | .inl h' => (hs.le hj y h').trans hΔ hu₁
      | .inr h' => (ht.le hk y h').trans hΔ hu₂)
    (fun _ hw hle => Shape.join_le hΔ
      (hs.min hw fun y hy => hle y (List.mem_append.2 (.inl hy)))
      (ht.min hw fun y hy => hle y (List.mem_append.2 (.inr hy))))

/-- **Existence**: a list of well-formed shapes with a common upper bound
has a least upper bound, itself below that bound.  Compatibility -- the
only obstruction -- comes for free from the common bound. -/
theorem Shape.exists_joins {Δ : List Term} (hΔ : ⊢ Δ) {n} {w : Shape n} (hw : Shape.WF Δ w) :
    ∀ {s : List (Shape n)}, (∀ x ∈ s, Shape.WF Δ x) → (∀ x ∈ s, Shape.LE Δ x w) →
      ∃ j, Shape.Joins Δ s j ∧ Shape.WF Δ j ∧ Shape.LE Δ j w := by
  intro s
  induction s with
  | nil => exact fun _ _ => ⟨.bot, .nil, by cases n <;> trivial, Shape.LE.bot⟩
  | cons x s ih =>
    intro hwf hle
    have ⟨j, hj, hwj, hjw⟩ :=
      ih (fun y hy => hwf y (.tail _ hy)) (fun y hy => hle y (.tail _ hy))
    have hx := hwf x (.head _)
    have hc := Shape.Compat.of_common_upper hΔ hw.coherent (hle x (.head _)) hjw
    exact ⟨x.join j, hj.cons hΔ hx hwj hc, Shape.WF.join hΔ hc hx hwj,
      Shape.join_le hΔ (hle x (.head _)) hjw⟩

/-- `Joins` transfers along mutual `≤`, since that is all it pins down. -/
theorem Shape.Joins.congr {Δ : List Term} (hΔ : ⊢ Δ) {n} {L : List (Shape n)} {j j' : Shape n}
    (hjj' : Shape.LE Δ j j') (hj'j : Shape.LE Δ j' j) (h : Shape.Joins Δ L j) :
    Shape.Joins Δ L j' :=
  fun w hw => ⟨fun hle => (h w hw).1 (hjj'.trans hΔ hle),
    fun hub => hj'j.trans hΔ ((h w hw).2 hub)⟩

/-- Least upper bounds are preserved by `lift`.  Minimality survives the
move even though the ambient level gains shapes that are not lifts,
because the binary join commutes with `lift` (`Shape.lift_join`) and
`Shape.join_le` is unconditional. -/
theorem Shape.Joins.lift {Δ : List Term} (hΔ : ⊢ Δ) {n k} (h : n ≤ k) :
    ∀ {L : List (Shape n)} {j : Shape n}, (∀ x ∈ L, Shape.WF Δ x) → Shape.WF Δ j →
      Shape.Joins Δ L j → Shape.Joins Δ (L.map (Shape.lift k)) (j.lift k) := by
  intro L
  induction L with
  | nil =>
    intro j _ _ hj
    have hjb : Shape.LE Δ j .bot := hj.min (by cases n <;> trivial) nofun
    refine fun w hw => ⟨fun _ => nofun, fun _ => ?_⟩
    have := (Shape.lift_le_lift (Γ := Δ) hΔ h).2 hjb
    rw [Shape.lift_bot] at this
    exact this.trans hΔ Shape.LE.bot
  | cons x L ih =>
    intro j hwL hwj hj
    have hwx := hwL x (.head _)
    have hxj := hj.le hwj x (.head _)
    have ⟨j₀, hj₀, hwj₀, hj₀j⟩ :=
      Shape.exists_joins hΔ hwj (fun y hy => hwL y (.tail _ hy))
        (fun y hy => hj.le hwj y (.tail _ hy))
    have hc := Shape.Compat.of_common_upper hΔ hwj.coherent hxj hj₀j
    have ⟨h₁, h₂⟩ :=
      Shape.Joins.uniq hwj (Shape.WF.join hΔ hc hwx hwj₀) hj (hj₀.cons hΔ hwx hwj₀ hc)
    have hlift : Shape.Joins Δ ((x :: L).map (Shape.lift k)) ((x.join j₀).lift k) := by
      rw [← Shape.lift_join h]
      exact (ih (fun y hy => hwL y (.tail _ hy)) hwj₀ hj₀).cons hΔ
        ((Shape.lift_wf h).2 hwx) ((Shape.lift_wf h).2 hwj₀) ((Shape.lift_compat h).2 hc)
    exact hlift.congr hΔ ((Shape.lift_le_lift hΔ h).2 h₂) ((Shape.lift_le_lift hΔ h).2 h₁)

/-- A pairwise-compatible list has a least upper bound.  Unlike
`exists_joins` this needs no common bound to start from: the fold keeps
compatibility going by `join_compat`, which is why the statement carries
the "compatible with anything all of `L` is compatible with" clause. -/
theorem Shape.exists_joins_of_pairwise {Δ : List Term} (hΔ : ⊢ Δ) : ∀ {n} {L : List (Shape n)},
    (∀ v ∈ L, Shape.WF Δ v) → (∀ v ∈ L, ∀ w ∈ L, Shape.Compat Δ v w) →
    ∃ j, Shape.Joins Δ L j ∧ Shape.WF Δ j ∧
      ∀ w, (∀ v ∈ L, Shape.Compat Δ v w) → Shape.Compat Δ j w := by
  intro n L
  induction L with
  | nil =>
    exact fun _ _ => ⟨.bot, .nil, by cases n <;> trivial, fun _ _ => Shape.Compat.bot_left⟩
  | cons x L ih =>
    intro hwf hpw
    have ⟨j, hj, hwj, hjc⟩ :=
      ih (fun v hv => hwf v (.tail _ hv))
        (fun v hv w hw => hpw v (.tail _ hv) w (.tail _ hw))
    have hwx := hwf x (.head _)
    have hc : Shape.Compat Δ x j :=
      Shape.Compat.symm hΔ (hjc x fun v hv => hpw v (.tail _ hv) x (.head _))
    exact ⟨x.join j, hj.cons hΔ hwx hwj hc, Shape.WF.join hΔ hc hwx hwj,
      fun w hw => .join hΔ (hw x (.head _)) (hjc w fun v hv => hw v (.tail _ hv))⟩

/-- Lifting a graph preserves well-formedness of its entries. -/
theorem ShapeFun.lift_wf {Δ : List Term} {n k} (h : n ≤ k) {f : ShapeFun n}
    (hwf : ShapeFun.WF Δ (Shape.WF Δ) f) :
    ShapeFun.WF Δ (Shape.WF Δ) (ShapeFun.lift (Shape.lift k) f) := by
  refine ⟨fun e' he' => ?_, (ShapeFun.lift_compat h).2 hwf.2⟩
  obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he'
  exact ⟨(hwf.1 e he).1, (hwf.1 e he).2.1, (Shape.lift_wf h).2 (hwf.1 e he).2.2.1,
    (Shape.lift_wf h).2 (hwf.1 e he).2.2.2⟩

/-! The two projections of a lifted graph, in the unfolded form
`List.sublist_map` leaves behind. -/

theorem ShapeFun.map_lift_inp {n k} {s : List (Entry (Shape n))} :
    (s.map fun e => (⟨e.ty, e.tm, e.inp.lift k, e.out.lift k⟩ : Entry (Shape k))).map Entry.inp
      = (s.map Entry.inp).map (Shape.lift k) := by
  simp [List.map_map, Function.comp_def]

theorem ShapeFun.map_lift_out {n k} {s : List (Entry (Shape n))} :
    (s.map fun e => (⟨e.ty, e.tm, e.inp.lift k, e.out.lift k⟩ : Entry (Shape k))).map Entry.out
      = (s.map Entry.out).map (Shape.lift k) := by
  simp [List.map_map, Function.comp_def]
