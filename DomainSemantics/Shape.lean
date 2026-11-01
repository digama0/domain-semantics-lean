import DomainSemantics.Label

/-! # Labelled shapes

The semantic domain of the gluing model. This is `popl27`'s
level-graded `Shape n` with two changes:

* a function graph is a `List (Entry (Shape n))` rather than a
  `List (Shape n × Shape n)`, where an `Entry` carries the **syntactic
  argument** `tm` it is about alongside the input and output shapes; and
* `forallE`/`sigma` carry the syntactic pair `(A, B)` of the type they
  approximate, and `id` carries its syntactic triple.

The labels are what glue syntax into the domain: application looks a graph
up at the label of the argument, and Π-injectivity is then a projection out
of the Π-label. See `design.md` §1.

Because labels are compared up to definitional equality in a context, the
order `Shape.LE Δ` is context-indexed and `Prop`-valued (the old `ble` and
`Compat` were `Bool`-valued). The saturation conditions of the old
`ShapeFun.WF` (a `⊥`-input entry, closure under compatible joins, monotone
samples) are gone: graph lookup is now the join of *all* matching entries
(`ShapeFun.Eval`, below) rather than a search for a maximal one. -/

namespace DomainSemantics

/-- One entry of a function graph: applied to the syntactic argument `tm`,
on input at least `inp` the result is at least `out`.

The argument's type is not stored: it is the domain label of the shape the
graph sits in (the λ's `A`, the Π's or Σ's `A`), and every judgment about
entries (`ShapeFun.WF`, `ShapeFun.Compat`, `ShapeFun.Eval`) takes it as a
parameter.  Some type is needed, since `Δ ⊢ tm ≡ tm' : T` is typed and
dropping the type altogether would make label equality `∃ T, …`, whose
transitivity needs uniqueness of types; one per graph is enough. -/
structure Entry (α : Type) where
  tm : Term
  inp : α
  out : α
  deriving Inhabited

inductive Shape0 : Type where
  | bot : Shape0
  | sort (rel : Bool) : Shape0

/-- One step of the level-graded shape constructor. Compared with
`popl27`'s `Shape`: graphs are lists of `Entry`, and `forallE`/`sigma`/`id`
carry syntactic labels. `refl` carries nothing: no rule reads a proof of
an identity past its head (transport asks for `H ≡ refl a` at the stage),
so its only information is that it is not `⊥`. -/
inductive ShapeS (Shape : Type) : Type where
  | bot : ShapeS Shape
  | sort (rel : Bool) : ShapeS Shape
  | unit (rel : Bool) : ShapeS Shape
  | forallE (A B : Term) : Shape → List (Entry Shape) → ShapeS Shape
  -- the label is the domain `A` of the Π the λ lives in, and it is the
  -- type every entry of the graph is read at, which pins the codomain
  -- lookup at *every* well-formed valuation, not just the admissible ones
  | lam (A : Term) : List (Entry Shape) → ShapeS Shape
  | sigma (A B : Term) : Shape → List (Entry Shape) → ShapeS Shape
  -- a pair is its two components, with the first component's *term* `a`
  -- as a label: the second component's type is `B[a]`, so the code that
  -- types it is read at that name (`design.md` §2).  A graph here would
  -- make typing lower- *and* join-closed, at the price of Σ's η: an
  -- entry's input is a condition the order enforces and the term's
  -- meaning does not.  With one unconditional second component η holds
  -- and typing is lower-closed, and join-closure is the subject join
  -- read at the component itself (`TShape.Named.join`)
  | pair (A a : Term) : Shape → Shape → ShapeS Shape
  | nat : ShapeS Shape
  | zero : ShapeS Shape
  | succ (n : Shape) : ShapeS Shape
  | protected id (rel : Bool) (A a b : Term) : ShapeS Shape
  | refl : ShapeS Shape

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

/-- `⊥` and a sort are never equal, at any level.  Both are defined by
recursion on the level, so this needs the `cases` that a `match` on a
variable level cannot do. -/
theorem Shape.bot_ne_sort {n} {r : Bool} : (.bot : Shape n) ≠ .sort r := by
  cases n <;> exact fun h => by cases h

theorem Shape.sort_ne_bot {n} {r : Bool} : (.sort r : Shape n) ≠ .bot :=
  fun h => bot_ne_sort h.symm

@[match_pattern] abbrev Shape.unit {n} (rel : Bool) : Shape (n+1) := ShapeS.unit rel
@[match_pattern] abbrev Shape.lam {n} (A : Term) (f : List (Entry (Shape n))) :
    Shape (n+1) := ShapeS.lam A f
@[match_pattern] abbrev Shape.nat {n} : Shape (n+1) := ShapeS.nat
@[match_pattern] abbrev Shape.zero {n} : Shape (n+1) := ShapeS.zero
@[match_pattern] abbrev Shape.succ {n} (v : Shape n) : Shape (n+1) := ShapeS.succ v
@[match_pattern] def Shape.refl {n} : Shape (n+1) := ShapeS.refl

abbrev Shape.type : Shape n := .sort true
instance : Inhabited (Shape n) := ⟨.bot⟩

/-! ## Lifting between levels

`popl27`'s `lift`, with labels carried through unchanged.  Lifting *down*
(to a level too small to hold the shape) collapses to `⊥`, as it does
there.  This is what lets the level index be hidden behind a total shape
type `TShape`, which the interpretation quantifies over. -/

def ShapeFun.lift (g : α → β) (f : List (Entry α)) : List (Entry β) :=
  f.map fun e => ⟨e.tm, g e.inp, g e.out⟩

@[simp] theorem ShapeFun.mem_lift {g : α → β} {f} {e' : Entry β} :
    e' ∈ lift g f ↔ ∃ e ∈ f, e' = ⟨e.tm, g e.inp, g e.out⟩ := by
  simp [lift, eq_comm]

def Shape.lift : ∀ {n} (m : Nat), Shape n → Shape m
  | 0, _, .sort r | _+1, _, .sort r => .sort r
  | 0, _, .bot | _+1, _, .bot | _, 0, _ => .bot
  | _+1, _+1, .unit r => .unit r
  | _+1, _+1, .forallE A B d f => .forallE A B (lift _ d) (ShapeFun.lift (lift _) f)
  | _+1, _+1, .lam A f => .lam A (ShapeFun.lift (lift _) f)
  | _+1, _+1, .sigma A B d f => .sigma A B (lift _ d) (ShapeFun.lift (lift _) f)
  | _+1, _+1, .pair A a x y => .pair A a (lift _ x) (lift _ y)
  | _+1, _+1, .nat => .nat
  | _+1, _+1, .zero => .zero
  | _+1, _+1, .succ v => .succ (lift _ v)
  | _+1, _+1, .id r A a b => .id r A a b
  | _+1, _+1, .refl => .refl

@[simp] theorem Shape.lift_bot {n m : Nat} : (.bot : Shape n).lift m = .bot := by
  cases n <;> [rfl; cases m <;> rfl]

@[simp] theorem Shape.lift_sort {n m : Nat} {r : Bool} :
    (.sort r : Shape n).lift m = .sort r := by
  cases n <;> [rfl; cases m <;> rfl]

theorem Shape.lift_self {n} {s : Shape n} : s.lift n = s := by
  induction n with | zero => cases s <;> rfl | succ n ih
  have hf (f : ShapeFun n) : ShapeFun.lift (lift n) f = f := by
    induction f with | nil => rfl | cons e f ihf
    simp only [ShapeFun.lift, List.map_cons] at ihf ⊢
    rw [ih, ih, ihf]
  cases s with
  | bot | sort | unit | nat | zero | id | refl => rfl
  | succ v => show ShapeS.succ _ = _; rw [ih]
  | pair A a x y => show ShapeS.pair .. = _; rw [ih, ih]
  | lam Af f => show ShapeS.lam .. = _; rw [hf]
  | forallE A B d f => show ShapeS.forallE .. = _; rw [ih, hf]
  | sigma A B d f => show ShapeS.sigma .. = _; rw [ih, hf]

/-- Lifting *up* and then anywhere is lifting anywhere.  `popl27`'s
`lift_lift`, restricted to the disjunct that is actually used: once a
shape has been lifted to a level that already holds it, no information is
left to lose on the way to a third level. -/
theorem Shape.lift_lift {n₁ n₂ n₃} {s : Shape n₁} (h : n₁ ≤ n₂) :
    (s.lift n₂).lift n₃ = s.lift n₃ := by
  induction n₁ generalizing n₂ n₃ with | zero => cases s <;> simp [lift] | succ n₁ ih
  let n₂+1 := n₂; have h' := Nat.le_of_succ_le_succ h
  cases n₃ with | zero => cases s <;> rfl | succ n₃
  have ihf (f : ShapeFun n₁) :
      ShapeFun.lift (lift n₃) (ShapeFun.lift (lift n₂) f) =
      ShapeFun.lift (lift n₃) f := by
    induction f with | nil => rfl | cons e f ihl
    simp only [ShapeFun.lift, List.map_cons] at ihl ⊢
    rw [ih h', ih h', ihl]
  cases s with
  | bot | sort | unit | nat | zero | id | refl => rfl
  | succ v => show ShapeS.succ _ = .succ _; rw [ih h']
  | pair A a x y => show ShapeS.pair .. = .pair _ _ _ _; rw [ih h', ih h']
  | lam Af f => show ShapeS.lam .. = .lam _ _; rw [ihf]
  | forallE A B d f =>
    show ShapeS.forallE .. = .forallE _ _ _ _; rw [ih h', ihf]
  | sigma A B d f =>
    show ShapeS.sigma .. = .sigma _ _ _ _; rw [ih h', ihf]

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
  | _+1, .lam _ f => ∀ e ∈ f, IsBot e.out
  | _+1, .pair _ _ x y => IsBot x ∧ IsBot y
  | _+1, _ => False

@[simp] theorem Shape.isBot_bot : (bot (n := n)).IsBot := by cases n <;> trivial

def ShapeFun.subst (g : Shape n → Shape n) (σ : Subst) (f : ShapeFun n) : ShapeFun n :=
  f.map fun e => ⟨e.tm.subst σ, g e.inp, g e.out⟩

def Shape.subst : ∀ {n}, Shape n → Subst → Shape n
  | 0, .bot, _ => .bot
  | 0, .sort r, _ => .sort r
  | _+1, .bot, _ => .bot
  | _+1, .sort r, _ => .sort r
  | _+1, .unit r, _ => .unit r
  | _+1, .nat, _ => .nat
  | _+1, .zero, _ => .zero
  | _+1, .succ v, σ => .succ (subst v σ)
  | _+1, .refl, _ => .refl
  | _+1, .id r A a b, σ => .id r (A.subst σ) (a.subst σ) (b.subst σ)
  | _+1, .forallE A B d f, σ =>
      .forallE (A.subst σ) (B.subst σ.lift) (subst d σ) (ShapeFun.subst (subst · σ) σ f)
  | _+1, .sigma A B d f, σ =>
      .sigma (A.subst σ) (B.subst σ.lift) (subst d σ) (ShapeFun.subst (subst · σ) σ f)
  | _+1, .pair A a x y, σ => .pair (A.subst σ) (a.subst σ) (subst x σ) (subst y σ)
  | _+1, .lam A f, σ => .lam (A.subst σ) (ShapeFun.subst (subst · σ) σ f)

@[simp] theorem Shape.subst_bot {n} {τ : Subst} : (bot (n := n)).subst τ = .bot := by
  cases n <;> rfl

@[simp] theorem Shape.subst_sort {n} {r : Bool} {τ : Subst} :
    (.sort r : Shape n).subst τ = .sort r := by cases n <;> rfl

@[simp] theorem ShapeFun.mem_subst {g : Shape n → Shape n} {σ f} {e' : Entry (Shape n)} :
    e' ∈ subst g σ f ↔
      ∃ e ∈ f, e' = ⟨e.tm.subst σ, g e.inp, g e.out⟩ := by
  simp [subst, eq_comm]

/-- Entries with definitionally equal labels and compatible inputs have
compatible outputs — **at every later typed stage**.

The quantification over later stages is what makes the condition stable
under substitution, and it sits inside the graph clause only, exactly as in
intgrah's `Shape.Compatible σ` (`Basis/InternalCoherence.lean`),
whose `lam` clause likewise reads `∀ i j Γ₂ (σ₁ : Γ₂ ⟶ _), … (σ₁ ≫ σ) …`.
It is needed because a substitution can *create* label equalities — two
distinct variables becoming definitionally equal — so a merely local
condition would say nothing about the entries that then collide. -/
def ShapeFun.Compat (R : List Term → Shape n → Shape n → Prop)
    (Δ : List Term) (T : Term) (f f' : ShapeFun n) : Prop :=
  ∀ e ∈ f, ∀ e' ∈ f', ∀ (Θ : List Term) (τ : Subst), ⊢ Θ → Ctx.SubstEq Θ τ τ Δ →
    LabelEq Θ (T.subst τ) (e.tm.subst τ) (T.subst τ) (e'.tm.subst τ) →
    R Θ (e.inp.subst τ) (e'.inp.subst τ) → R Θ (e.out.subst τ) (e'.out.subst τ)

def Shape.Compat : ∀ {n}, List Term → Shape n → Shape n → Prop
  | 0, _, .bot, _ => True
  | 0, _, _, .bot => True
  | 0, _, .sort r, .sort r' => r = r'
  | _+1, _, .bot, _ => True
  | _+1, _, _, .bot => True
  | _+1, Δ, .lam A f, .lam A' f' => TyEq Δ A A' ∧ ShapeFun.Compat Compat Δ A f f'
  | _+1, _, .sort r, .sort r' => r = r'
  | _+1, _, .unit r, .unit r' => r = r'
  | _+1, _, .nat, .nat => True
  | _+1, _, .zero, .zero => True
  | _+1, Δ, .succ v, .succ v' => Compat Δ v v'
  | _+1, _, .refl, .refl => True
  | _+1, Δ, .pair A a x y, .pair A' a' x' y' =>
      TyEq Δ A A' ∧ (Δ ⊢ a ≡ a' : A) ∧ Compat Δ x x' ∧ Compat Δ y y'
  | _+1, Δ, .id r A a b, .id r' A' a' b' => r = r' ∧ IdLabelEq Δ A a b A' a' b'
  | _+1, Δ, .forallE A B d f, .forallE A' B' d' f' =>
      PiLabelEq Δ A B A' B' ∧ Compat Δ d d' ∧ ShapeFun.Compat Compat Δ A f f'
  | _+1, Δ, .sigma A B d f, .sigma A' B' d' f' =>
      PiLabelEq Δ A B A' B' ∧ Compat Δ d d' ∧ ShapeFun.Compat Compat Δ A f f'
  | _+1, _, _, _ => False

/-! ## Well-formed shapes

Labels are compared by plain definitional equality, which is reflexive
only on well-typed terms.  `Shape.WF Γ` says every label occurring in a
shape is well-typed in `Γ`; it is the hypothesis of `Shape.LE.refl`.
Note this is a genuine invariant of the model (interpretations only ever
produce well-typed labels), unlike the saturation conditions of the old
`ShapeFun.WF`, which are gone. -/

/-- Every entry of a graph has a well-typed label and well-formed shapes.

`oB` is the codomain the graph is read at, when there is one: an entry's
output is then well formed **naming** `B.inst e.tm`, which is what a Π-
or Σ-code's graph asks and a λ's does not. -/
def ShapeFun.WF (Γ : List Term) (T : Term) (oB : Option Term)
    (W : Shape n → Option Term → Prop) (f : ShapeFun n) : Prop :=
  (∀ e ∈ f, (∃ u, Γ ⊢ T : .sort u) ∧ Γ ⊢ e.tm : T ∧
      W e.inp none ∧ W e.out (oB.map (·.inst e.tm))) ∧
  Compat Shape.Compat Γ T f f

/-- The entries' shapes are well formed — `WF`'s first half, without the
coherence.  A *generator* (`HasType.lam`, `HasType.pair`) satisfies this
but not `ShapeFun.WF`: two generators certifying compatible λ-values need
not be compatible with each other, since a generator entry no graph entry
uses is unconstrained. -/
def ShapeFun.WFE (W : Shape n → Prop) (f : ShapeFun n) : Prop :=
  ∀ e ∈ f, W e.inp ∧ W e.out

/-- `TyEqO Γ o T'` is `TyEq Γ T T'` when a name `T` is asked for and
`True` when none is.  It is the one place `Shape.WF`'s index is read, so
at `none` every clause reduces to the structural one. -/
abbrev TyEqO (Γ : List Term) (o : Option Term) (T' : Term) : Prop :=
  match o with
  | none => True
  | some T => TyEq Γ T T'

/-- **Well-formedness, with a name when one is asked for.**  Every label
occurring in the shape is well-typed in `Γ`, and, at `some T`, the head's
own labels name `T`.

The `Option Term` index is what used to be two conjuncts bolted onto the
Π and Σ clauses: a domain code is now well formed *at `A`* and an entry's
output *at `B.inst e.tm`*, so the recursion carries canonicity instead of
restating it.  At `none` nothing is asked beyond the structure, which is
`Shape.WF` itself. -/
def Shape.WF (Γ : List Term) : ∀ {n}, Shape n → (o : Option Term := none) → Prop
  | 0, .bot, _ | _+1, .bot, _ | _+1, .zero, _ | _+1, .refl, _ => True
  | 0, .sort r, o | _+1, .sort r, o => TyEqO Γ o (.sort r)
  | _+1, .unit r, o => TyEqO Γ o (.unit r)
  | _+1, .nat, o => TyEqO Γ o .nat
  | _+1, .succ v, _ => WF Γ v
  | _+1, .id r A a b, o =>
      (∃ u, Γ ⊢ A : .sort u) ∧ (Γ ⊢ a : A) ∧ (Γ ⊢ b : A) ∧
        TyEqO Γ o (.id r A a b)
  | _+1, .forallE A B d f, o =>
      (∃ u, Γ ⊢ A : .sort u) ∧ (∃ v, A :: Γ ⊢ B : .sort v) ∧
        WF Γ d A ∧ ShapeFun.WF Γ A B (@WF Γ _) f ∧
        TyEqO Γ o (.forallE A B)
  | _+1, .sigma A B d f, o =>
      (∃ u, Γ ⊢ A : .sort u) ∧ (∃ v, A :: Γ ⊢ B : .sort v) ∧
        WF Γ d A ∧ ShapeFun.WF Γ A B (@WF Γ _) f ∧
        TyEqO Γ o (.sigma A B)
  -- the two components, with the first's name; the non-degeneracy
  -- conjunct keeps `⊥` the only bottom
  | _+1, .pair A a x y, _ =>
      ¬ (x.IsBot ∧ y.IsBot) ∧ (Γ ⊢ a : A) ∧ TyEq Γ A A ∧ WF Γ x ∧ WF Γ y
  -- `popl27`'s `NonZero`, strengthened to every entry: a well-formed λ-shape
  -- carries real information, so `IsBot` collapses to `= .bot` and the
  -- collapse clauses disappear from `LE`, `Compat` and `join`
  -- the last conjunct is **internal coherence**, intgrah's
  -- `IsCoherent`: entries whose labels become definitionally equal at some
  -- later stage, with compatible inputs there, must have compatible outputs
  -- there.  It is what makes the graph lookup's joins exist, and it belongs
  -- here because `WF` is the single "good shape" predicate the
  -- interpretation will carry anyway.
  -- the last conjunct is the domain label's own typing, which the empty
  -- graph would otherwise leave unconstrained
  | _+1, .lam A f, _ =>
      f ≠ [] ∧ (∀ e ∈ f, ¬ e.out.IsBot) ∧ ShapeFun.WF Γ A none (@WF Γ _) f ∧ TyEq Γ A A

/-- **Forgetting the name.**  The index is read only at the head, so
dropping it drops one conjunct and leaves the rest. -/
theorem Shape.WF.forget {n} {Γ : List Term} {o} {s : Shape n} (h : s.WF Γ o) :
    s.WF Γ := by
  cases n <;> cases s <;> first
    | exact h
    | trivial
    | exact ⟨h.1, h.2.1, h.2.2.1, trivial⟩
    | exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, trivial⟩

@[simp] theorem Shape.WF.bot_mem {Γ : List Term} {n} {o} :
    (Shape.bot (n := n)).WF Γ o := by cases n <;> trivial

/-- **A name moves along an equality of types.**  Only the head mentions
it, so this is one `cases` and the other conjuncts ride along. -/
theorem Shape.WF.conv {n} {Γ : List Term} {T T' : Term} {x : Shape n}
    (h : x.WF Γ T) (hT : TyEq Γ T' T) : x.WF Γ T' := by
  cases n <;> cases x <;> first
    | exact h
    | exact hT.trans h
    | exact ⟨h.1, h.2.1, h.2.2.1, hT.trans h.2.2.2⟩
    | exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, hT.trans h.2.2.2.2⟩

/-- A graph is well formed at a codomain exactly when it is well formed
and every output names the codomain read at the entry's label. -/
theorem ShapeFun.WF.name {Δ : List Term} {n} {T B : Term} {f : ShapeFun n}
    (h : f.WF Δ T none (@Shape.WF Δ _))
    (hc : ∀ e ∈ f, e.out.WF Δ (B.inst e.tm)) :
    f.WF Δ T B (@Shape.WF Δ _) := by
  refine ⟨fun e he => ?_, h.2⟩
  have ⟨hty, htm, hin, _⟩ := h.1 e he
  exact ⟨hty, htm, hin, hc e he⟩

/-- The per-entry naming a graph's index carries. -/
theorem ShapeFun.WF.canon {Δ : List Term} {n} {T B : Term} {f : ShapeFun n}
    (h : f.WF Δ T B (@Shape.WF Δ _)) :
    ∀ e ∈ f, e.out.WF Δ (B.inst e.tm) :=
  fun e he => (h.1 e he).2.2.2

/-- And back. -/
theorem ShapeFun.WF.forget {Δ : List Term} {n} {T : Term} {oB : Option Term} {f : ShapeFun n}
    (h : f.WF Δ T oB (@Shape.WF Δ _)) :
    f.WF Δ T none (@Shape.WF Δ _) := by
  refine ⟨fun e he => ?_, h.2⟩
  have ⟨hty, htm, hin, hout⟩ := h.1 e he
  exact ⟨hty, htm, hin, hout.forget⟩

/-- The join.  Total and context-free.

Since a well-formed λ-shape is never information-free, a λ-shape facing a
different head is genuinely incompatible, so the mixed-`lam` clauses that
intgrah's `cSup` needs are unnecessary here.  Labels of the left argument
are kept elsewhere, which is legitimate under `Compat Δ` since they are
then definitionally equal to the right one's. -/
def Shape.join : ∀ {n}, Shape n → Shape n → Shape n
  | 0, .bot, b => b
  | 0, a, .bot => a
  | 0, a, _ => a
  | _+1, .bot, b => b
  | _+1, a, .bot => a
  | _+1, .lam A f, .lam _ f' => .lam A (f ++ f')
  | _+1, .forallE A B d f, .forallE _ _ d' f' => .forallE A B (join d d') (f ++ f')
  | _+1, .sigma A B d f, .sigma _ _ d' f' => .sigma A B (join d d') (f ++ f')
  | _+1, .succ v, .succ v' => .succ (join v v')
  | _+1, .refl, .refl => .refl
  | _+1, .pair A a x y, .pair _ _ x' y' => .pair A a (join x x') (join y y')
  | _+1, a, _ => a

/-- The codomain names across an appended graph: the right half's names
are read at `B'` and wanted at `B`, which the Π label equality supplies
once the entry's term is typed at `A`. -/
theorem ShapeFun.codeCanonS_append {n} {Δ : List Term} (hΔ : ⊢ Δ) {A A' B B' : Term}
    {f g : ShapeFun n} (hlab : PiLabelEq Δ A B A' B') (hg : ∀ e ∈ g, Δ ⊢ e.tm : A')
    (hcf : ∀ e ∈ f, e.out.WF Δ (B.inst e.tm))
    (hcg : ∀ e ∈ g, e.out.WF Δ (B'.inst e.tm)) :
    ∀ e ∈ f ++ g, e.out.WF Δ (B.inst e.tm) := by
  obtain ⟨⟨u, hAA'⟩, v, hBB'⟩ := hlab
  intro e he
  rcases List.mem_append.1 he with h | h
  · exact hcf e h
  · exact (hcg e h).conv
      ⟨v, hAA'.hasType.1.instDF hΔ .sort hBB' (hAA'.symm.defeqDF (hg e h))⟩

/-! ## The order

`Shape.LE Γ` compares labels up to definitional equality in `Γ`, so it is
indexed by a context and lives in `Prop`.

A graph is covered by another when every entry's output is reached by the
**lookup** in the covering graph at that entry's label and input.  Coverage
by a single *entry* — `popl27`'s order, and intgrah's `Graph.LE` — is
too fine: η needs an entry whose output is a *join* of several outputs of
the covering graph, which no single entry dominates.  `popl27` can afford
entry coverage because its graphs are saturated, so a join of matching
outputs *is* an entry; intgrah because a λ-value is an ideal,
closed under every graph valid for its action.

The lookup is `ShapeFun.Eval`, and it is defined here, **parameterised by
the order one level down**, which is what closes the recursion: `LE` at
`n+1` needs the lookup at `n`, which needs `LE` at `n`.  `HasType.lean`'s
`TEvaluates` is this one at `R := Shape.LE Δ`. -/

/-- The graph lookup at a label and an input: `⊥`, the outputs of matching
entries, closed downwards and under compatible joins.  intgrah's
`Evaluates`, with the order it is relative to as a parameter.

The side condition on `join` is not decoration: it makes the join a
genuine least upper bound, and with it the lookup's values are well
behaved enough (`Eval.wf`, `Eval.compat`) for the order built on them to
reflect along `lift`.

`lower` needs no such condition, even though `WF` is not downward closed —
a smaller λ-shape may have a bottom output.  At `R := Shape.LE Δ` the
order carries the well-formedness of its lower bound (`Shape.LE.wf`), so
`Eval.wf` reads it off `R y z` itself. -/
inductive ShapeFun.Eval (Δ : List Term) {n} (R : Shape n → Shape n → Prop)
    (f : ShapeFun n) (A a : Term) (x : Shape n) : Shape n → Prop where
  | bot : Eval Δ R f A a x .bot
  | entry (e : Entry (Shape n)) : e ∈ f → LabelEq Δ A e.tm A a → R e.inp x →
    Eval Δ R f A a x e.out
  | lower {y z} : R y z → Eval Δ R f A a x z → Eval Δ R f A a x y
  | join {y z} : Shape.Compat Δ y z → Eval Δ R f A a x y → Eval Δ R f A a x z →
    Eval Δ R f A a x (y.join z)

/-- Lookup-wise coverage of one graph by another, together with the
well-formedness of both.

**The order on graphs carries their well-formedness.**  Everywhere else in
`Shape.LE` it comes for free — a clause's label conjuncts are implied by
its `LabelEq`/`PiLabelEq`/`IdLabelEq`, its sub-shape conjuncts by the
recursive `LE` — but a graph's is not: `∀ e ∈ f, Eval f' T e.tm e.inp
e.out` says nothing whatever about an entry whose output is `⊥`, because
`Eval.bot` discharges it.

It is what makes the order reflect along `lift`: `Eval.lift_of` wants the
covering graph well formed and coherent, and with this conjunct
`lift_le_lift`'s own hypothesis supplies them, so its statement does not
have to. -/
def ShapeFun.LE (Δ : List Term) (R : Shape n → Shape n → Prop)
    (W : Shape n → Option Term → Prop) (T : Term) (f f' : ShapeFun n) : Prop :=
  (∀ e ∈ f, Eval Δ R f' T e.tm e.inp e.out) ∧
  WF Δ T none W f ∧ WF Δ T none W f'

/-- Appending two mutually coherent well-formed graphs. -/
theorem ShapeFun.WF.append {Δ : List Term} {n} {Ty : Term} {oB : Option Term}
    {W : Shape n → Option Term → Prop} {f f' : ShapeFun n}
    (hf : f.WF Δ Ty oB W) (hf' : f'.WF Δ Ty oB W)
    (hx : f.Compat Shape.Compat Δ Ty f')
    (hx' : f'.Compat Shape.Compat Δ Ty f) : (f ++ f').WF Δ Ty oB W := by
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
    (H : f.Eval Δ R A a x y) : f.Eval Δ R A' a' x' y := by
  induction H with
  | bot => exact .bot
  | entry e he hl hin => exact .entry e he (hl.trans hlab).right (htr _ _ _ hin hx)
  | lower hle _ ih => exact .lower hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- A lookup in a covered graph is a lookup in the covering one: this is
transitivity of the order, one level up. -/
theorem ShapeFun.Eval.trans {Δ : List Term} {n} {R : Shape n → Shape n → Prop}
    (htr : ∀ a b c : Shape n, R a b → R b c → R a c)
    {f f' : ShapeFun n} {T A a : Term} {x y : Shape n} (hT : TyEq Δ T A)
    (hf : ∀ e ∈ f, f'.Eval Δ R T e.tm e.inp e.out)
    (H : f.Eval Δ R A a x y) :
    f'.Eval Δ R A a x y := by
  induction H with
  | bot => exact .bot
  | entry e he hl hin =>
    exact (hf e he).mono htr ⟨hT, (hl.retype hT.symm).2⟩ hin
  | lower hle _ ih => exact .lower hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

theorem ShapeFun.Compat.retype {R : List Term → Shape n → Shape n → Prop} {Δ : List Term}
    {T T' : Term} {f f' : ShapeFun n} (hT : TyEq Δ T T')
    (h : f.Compat R Δ T f') : f.Compat R Δ T' f' :=
  fun e he e' he' Θ τ hΘ W hlab hin =>
    h e he e' he' Θ τ hΘ W (hlab.retype (hT.subst hΘ W).symm) hin

theorem ShapeFun.WF.retype {Γ : List Term} {T T' : Term} {oB : Option Term}
    {W : Shape n → Option Term → Prop}
    {f : ShapeFun n} (hT : TyEq Γ T T') (h : f.WF Γ T oB W) :
    f.WF Γ T' oB W := by
  refine ⟨fun e he => ?_, h.2.retype hT⟩
  have ⟨_, htm, hi, ho⟩ := h.1 e he
  have ⟨_, hTT⟩ := hT
  exact ⟨hT.refl_r, hTT.defeqDF htm, hi, ho⟩

theorem ShapeFun.Eval.retype {Δ : List Term} {R : Shape n → Shape n → Prop} {f : ShapeFun n}
    {A A' a : Term} {x y : Shape n} (hA : TyEq Δ A A')
    (H : f.Eval Δ R A a x y) : f.Eval Δ R A' a x y := by
  induction H with
  | bot => exact .bot
  | entry e he hl hin => exact .entry e he (hl.retype hA) hin
  | lower hle _ ih => exact .lower hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

theorem ShapeFun.LE.retype {Δ : List Term} {R : Shape n → Shape n → Prop}
    {W : Shape n → Option Term → Prop} {T T' : Term} {f f' : ShapeFun n} (hT : TyEq Δ T T')
    (h : f.LE Δ R W T f') : f.LE Δ R W T' f' :=
  ⟨fun e he => (h.1 e he).retype hT, h.2.1.retype hT, h.2.2.retype hT⟩

/-- The approximation order, by recursion on the level.

**The order carries the well-formedness of its lower bound**
(`Shape.LE.wf`).  Almost every clause gives it away for free — the label
conjuncts come out of `LabelEq`/`PiLabelEq`/`IdLabelEq`, the sub-shape
conjuncts out of the recursive `LE`, a graph's out of `ShapeFun.LE` — and
the two exceptions are the two non-degeneracy conditions, which no
comparison can see: a `pair` of two `⊥`s and a `λ` with a `⊥` output are
below plenty of things.  So those two are stated here, on the left-hand
side only.

Not on the right-hand side: `⊥` is below *everything*, well formed or
not, and it has to be, or `Interp.le_id` could not invert the `bot` rule
without knowing the label is typed.  Well-formedness of an upper bound is
available only for graphs, where `ShapeFun.LE` asks for it outright
because the lookup needs it. -/
def Shape.LE (Γ : List Term) : ∀ {n}, Shape n → Shape n → Prop
  | 0, .bot, _ => True
  | 0, .sort r, .sort r' => r = r'
  | 0, _, _ => False
  | _+1, .bot, _ | _+1, .nat, .nat | _+1, .zero, .zero => True
  | _+1, .sort r, .sort r' | _+1, .unit r, .unit r' => r = r'
  | _+1, .succ v, .succ v' => LE Γ v v'
  | _+1, .refl, .refl => True
  | _+1, .id r A a b, .id r' A' a' b' => r = r' ∧ IdLabelEq Γ A a b A' a' b'
  | _+1, .forallE A B d f, .forallE A' B' d' f'
  | _+1, .sigma A B d f, .sigma A' B' d' f' =>
    PiLabelEq Γ A B A' B' ∧ LE Γ d d' ∧ ShapeFun.LE Γ (LE Γ) (@WF Γ _) A f f' ∧
      WF Γ d A ∧ ∀ e ∈ f, WF Γ e.out (B.inst e.tm)
  | _+1, .pair A a x y, .pair A' a' x' y' =>
    LE Γ x x' ∧ LE Γ y y' ∧ ¬ (x.IsBot ∧ y.IsBot) ∧ TyEq Γ A A' ∧ (Γ ⊢ a ≡ a' : A)
  | _+1, .lam A f, .lam A' f' =>
    ShapeFun.LE Γ (LE Γ) (@WF Γ _) A f f' ∧ f ≠ [] ∧ (∀ e ∈ f, ¬ e.out.IsBot) ∧
      TyEq Γ A A' ∧ TyEq Γ A A
  | _+1, _, _ => False

@[simp] theorem Shape.LE.bot {s : Shape n} : LE Γ .bot s := by
  cases n <;> trivial

/-- **A well-formed shape carries no information only if it is `⊥`.**
The two non-degeneracy conjuncts of `WF` are exactly what this needs: a
`λ` has an entry with a non-`⊥` output, and a pair has a component that is
not information-free. -/
theorem Shape.WF.eq_bot_of_isBot {Γ : List Term} {n} {s : Shape n}
    (hw : s.WF Γ) (hb : s.IsBot) : s = .bot := by
  cases n with | zero => (cases s <;> first | rfl | cases hb) | succ n
  cases s with
  | bot => rfl
  | lam A f =>
    match f, hw with
    | e :: _, hw => cases hw.2.1 e (.head _) (hb e (.head _))
  | pair A a x y => cases hw.1 hb
  | _ => cases hb

/-- The domain label of a well-formed pair shape is a type: unlike a λ's
it is a conjunct of `WF`, since a pair has no entries to read it off. -/
theorem Shape.WF.pair_dom {A a : Term} {x y : Shape n}
    (h : WF (n := n+1) Γ (.pair A a x y)) : TyEq Γ A A := h.2.2.1

/-- The domain label of a well-formed λ-shape is a type. -/
theorem Shape.WF.dom {A : Term} {f : ShapeFun n}
    (h : WF (n := n+1) Γ (.lam A f)) : TyEq Γ A A := h.2.2.2

/-- **The order carries the well-formedness of its lower bound.**

Everything here is a projection: the label conjuncts out of the label
equalities, the sub-shape conjuncts out of the recursive `LE`, a graph's
out of `ShapeFun.LE`, and the two non-degeneracy conditions out of the
clauses that were put there for this.  It is why `Eval`'s `lower` rule
needs no side condition, and why `Shape.WF Γ x` and `Shape.LE Γ x x` are
interchangeable (with `LE.refl`). -/
theorem Shape.LE.wf {Γ : List Term} {n} {x y : Shape n} (h : x.LE Γ y) :
    x.WF Γ := by
  induction n with | zero => cases x <;> trivial | succ n ih
  cases x with
  | bot | nat | zero | sort | unit => trivial
  | succ v => cases y <;> first | exact absurd h id | exact ih h
  | refl => cases y <;> first | exact absurd h id | trivial
  | id =>
    cases y <;> try exact absurd h id
    have ⟨_, ⟨u, hA⟩, ha, hb⟩ := h
    exact ⟨⟨u, hA.hasType.1⟩, ha.hasType.1, hb.hasType.1, trivial⟩
  | forallE | sigma =>
    cases y <;> try exact absurd h id
    all_goals
      have ⟨⟨⟨u, hA⟩, v, hB⟩, hd, hf, hcd, hcf⟩ := h
      exact ⟨⟨u, hA.hasType.1⟩, ⟨v, hB.hasType.1⟩, hcd, hf.2.1.name hcf, trivial⟩
  | pair =>
    cases y <;> try exact absurd h id
    exact ⟨h.2.2.1, h.2.2.2.2.hasType.1, h.2.2.2.1.refl_l, ih h.1, ih h.2.1⟩
  | lam =>
    cases y <;> try exact absurd h id
    exact ⟨h.2.1, h.2.2.1, h.1.2.1, h.2.2.2.2⟩

/-- **A name is downward closed.**  The order keeps a head's labels up to
definitional equality; `LE.wf` supplies every other conjunct. -/
theorem Shape.WF.mono_mem {Δ : List Term} (hΔ : ⊢ Δ) {n} {T : Term} {x y : Shape n}
    (h : x.LE Δ y) (hC : y.WF Δ T) : x.WF Δ T := by
  have hw := h.wf
  cases n <;> cases x <;> cases y <;> first
    | exact hw
    | exact absurd h id
    | (cases h; exact hC)
    | exact ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1,
        hC.2.2.2.2.trans (h.1.forallE hΔ).symm⟩
    | exact ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1,
        hC.2.2.2.2.trans (h.1.sigma hΔ).symm⟩
    | (cases h.1; exact ⟨hw.1, hw.2.1, hw.2.2.1, hC.2.2.2.trans (IdLabelEq.id h.2).symm⟩)

theorem Shape.LE.refl {n} {s : Shape n} (hs : s.WF Γ) : s.LE Γ s := by
  induction n with | zero => cases s <;> trivial | succ n ih
  have hfun {Ty : Term} {f : ShapeFun n}
      (hf : f.WF Γ Ty none (@WF Γ _)) :
      f.LE Γ (LE Γ) (@WF Γ _) Ty f := by
    refine ⟨fun e he => ?_, hf, hf⟩
    have ⟨⟨_, hty⟩, htm, hin, _⟩ := hf.1 e he
    exact .entry e he (.refl hty htm) (ih hin)
  cases s with
  | bot | nat | zero | refl => trivial
  | sort | unit => rfl
  | succ => exact ih hs
  | id =>
    have ⟨⟨_, hA⟩, ha, hb, _⟩ := hs
    exact ⟨rfl, .refl hA ha hb⟩
  | forallE A B d f | sigma A B d f =>
    have ⟨⟨_, hA⟩, ⟨_, hB⟩, hd, hf, _⟩ := hs
    exact ⟨.refl hA hB, ih hd.forget, hfun hf.forget, hd,
      fun e he => (hf.1 e he).2.2.2⟩
  | pair A a x y => exact ⟨ih hs.2.2.2.1, ih hs.2.2.2.2, hs.1, hs.pair_dom, hs.2.1⟩
  | lam => exact ⟨hfun hs.2.2.1, hs.1, hs.2.1, hs.dom, hs.2.2.2⟩

/-- With the collapse clauses gone, only `⊥` is below `⊥`. -/
theorem Shape.le_bot_iff {n} {s : Shape n} : s.LE Δ .bot ↔ s = .bot := by
  cases n <;> cases s with
  | bot => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | _ => exact ⟨nofun, nofun⟩

/-! ### What sits below a shape

`popl27`'s `Shape.le_sort`, `le_unit`, `le_nat_iff`, `le_succ_iff`, … , one
per head: below a shape is `⊥`, or a shape of the same head whose
components are below its.  These are the one-directional halves — the
converse is `bot_le` and the componentwise constructor — and they are what
every inversion of the order against a known head goes through. -/

theorem Shape.le_sort {Δ : List Term} {n} {r : Bool} {s : Shape n}
    (h : s.LE Δ (.sort r)) : s = .bot ∨ s = .sort r := by
  cases n with
  | zero => cases s with | bot => exact .inl rfl | sort r' => cases h; exact .inr rfl
  | succ n
  cases s with
  | bot => exact .inl rfl
  | sort r' => cases h; exact .inr rfl
  | _ => cases h

theorem Shape.le_unit {Δ : List Term} {n} {r : Bool} {s : Shape (n+1)}
    (h : LE Δ s (ShapeS.unit r)) : s = bot ∨ s = ShapeS.unit r := by
  cases s with
  | bot => exact .inl rfl
  | unit r' => cases h; exact .inr rfl
  | _ => cases h

theorem Shape.le_nat {Δ : List Term} {n} {s : Shape (n+1)}
    (h : LE Δ s ShapeS.nat) : s = bot ∨ s = ShapeS.nat := by
  cases s with
  | bot => exact .inl rfl
  | nat => exact .inr rfl
  | _ => cases h

theorem Shape.le_zero {Δ : List Term} {n} {s : Shape (n+1)}
    (h : LE Δ s ShapeS.zero) : s = bot ∨ s = ShapeS.zero := by
  cases s with
  | bot => exact .inl rfl
  | zero => exact .inr rfl
  | _ => cases h

theorem Shape.le_succ {Δ : List Term} {n} {v : Shape n} {s : Shape (n+1)}
    (h : LE Δ s (ShapeS.succ v)) :
    s = bot ∨ ∃ v', s = ShapeS.succ v' ∧ LE Δ v' v := by
  cases s with
  | bot => exact .inl rfl
  | succ v' => exact .inr ⟨v', rfl, h⟩
  | _ => cases h

theorem Shape.le_id {Δ : List Term} {n} {r : Bool} {A a b : Term} {s : Shape (n+1)}
    (h : s.LE Δ (.id r A a b)) :
    s = .bot ∨ ∃ A' a' b', s = .id r A' a' b' ∧ IdLabelEq Δ A' a' b' A a b := by
  cases s with
  | bot => exact .inl rfl
  | id r' A' a' b' => obtain ⟨rfl, hl⟩ := h; exact .inr ⟨A', a', b', rfl, hl⟩
  | _ => cases h

theorem Shape.le_forallE {Δ : List Term} {n} {A B : Term} {d : Shape n} {f : ShapeFun n}
    {s : Shape (n+1)} (h : s.LE Δ (.forallE A B d f)) :
    s = .bot ∨ ∃ A' B' d' f', s = .forallE A' B' d' f' ∧
      PiLabelEq Δ A' B' A B ∧ d'.LE Δ d ∧
      ShapeFun.LE Δ (LE Δ) (@WF Δ _) A' f' f := by
  cases s with
  | bot => exact .inl rfl
  | forallE A' B' d' f' => exact .inr ⟨A', B', d', f', rfl, h.1, h.2.1, h.2.2.1⟩
  | _ => cases h

theorem Shape.le_sigma {Δ : List Term} {n} {A B : Term} {d : Shape n} {f : ShapeFun n}
    {s : Shape (n+1)} (h : s.LE Δ (.sigma A B d f)) :
    s = .bot ∨ ∃ A' B' d' f', s = .sigma A' B' d' f' ∧
      PiLabelEq Δ A' B' A B ∧ d'.LE Δ d ∧
      ShapeFun.LE Δ (LE Δ) (@WF Δ _) A' f' f := by
  cases s with
  | bot => exact .inl rfl
  | sigma A' B' d' f' => exact .inr ⟨A', B', d', f', rfl, h.1, h.2.1, h.2.2.1⟩
  | _ => cases h

theorem Shape.lift_subst {n} (m : Nat) {s : Shape n} {τ : Subst} :
    (s.subst τ).lift m = (s.lift m).subst τ := by
  induction n generalizing m with
  | zero => cases s <;> cases m <;> rfl
  | succ n ih
  cases m with | zero => cases s <;> rfl | succ m
  have ihf (f : ShapeFun n) :
      ShapeFun.lift (lift m) (f.subst (subst · τ) τ)
        = ShapeFun.subst (subst · τ) τ (ShapeFun.lift (lift m) f) := by
    induction f with | nil => rfl | cons e f ihl
    simp only [ShapeFun.lift, ShapeFun.subst, List.map_cons] at ihl ⊢
    rw [ih, ih, ihl]
  cases s with
  | bot | sort | unit | nat | zero | id | refl => rfl
  | succ v => show ShapeS.succ _ = .succ _; rw [ih]
  | pair A a x y => show ShapeS.pair .. = .pair _ _ _ _; rw [ih, ih]
  | lam Af f => show ShapeS.lam .. = ShapeS.lam _ _; rw [ihf]
  | forallE A B d f => show ShapeS.forallE .. = ShapeS.forallE ..; rw [ih, ihf]
  | sigma A B d f => show ShapeS.sigma .. = ShapeS.sigma ..; rw [ih, ihf]

/-- Lifting *up* preserves and reflects being information-free. -/
theorem Shape.lift_isBot {n m} (h : n ≤ m) {s : Shape n} : (s.lift m).IsBot ↔ s.IsBot := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rw [lift_self]
    | succ m => cases s <;> rfl
  | succ n ih
  let m+1 := m; have h' := Nat.le_of_succ_le_succ h
  have hg (f : ShapeFun n) :
      (∀ e ∈ ShapeFun.lift (lift m) f, e.out.IsBot) ↔ ∀ e ∈ f, e.out.IsBot := by
    constructor
    · intro H e he
      exact (ih h').1 (H ⟨e.tm, e.inp.lift m, e.out.lift m⟩ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩))
    · intro H e'' he''
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
      exact (ih h').2 (H e he)
  cases s with
  | lam Af f => exact hg f
  | pair A a x y => exact and_congr (ih h') (ih h')
  | _ => rfl

/-- Lifting *up* preserves and reflects compatibility.  The hereditary
graph clause goes through because lifting commutes with substitution; note
the context must be generalised in the induction, since that clause moves
to a later stage `Θ`. -/
theorem Shape.lift_compat {n m} (h : n ≤ m) {Δ : List Term} {s t : Shape n} :
    (s.lift m).Compat Δ (t.lift m) ↔ s.Compat Δ t := by
  induction n generalizing m Δ with
  | zero =>
    cases m with
    | zero => rw [lift_self, lift_self]
    | succ m => cases s <;> cases t <;> exact .rfl
  | succ n ih
  let m+1 := m; have h' := Nat.le_of_succ_le_succ h
  have ihf {Δ : List Term} {Ty : Term} {f f' : ShapeFun n} :
      ShapeFun.Compat Compat Δ Ty (ShapeFun.lift (lift m) f)
        (ShapeFun.lift (lift m) f') ↔
      ShapeFun.Compat Compat Δ Ty f f' := by
    constructor
    · intro H e he e' he' Θ τ hΘ W hlab hin
      have := H _ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩) _ (ShapeFun.mem_lift.2 ⟨e', he', rfl⟩)
        Θ τ hΘ W hlab
      rw [← lift_subst, ← lift_subst, ← lift_subst, ← lift_subst] at this
      exact (ih h').1 (this ((ih h').2 hin))
    · intro H e'' he'' e''' he''' Θ τ hΘ W hlab hin
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
      obtain ⟨e', he', rfl⟩ := ShapeFun.mem_lift.1 he'''
      rw [← lift_subst, ← lift_subst] at hin ⊢
      exact (ih h').2 (H e he e' he' Θ τ hΘ W hlab ((ih h').1 hin))
  cases s <;> cases t <;> (try rfl)
  · exact and_congr .rfl (and_congr (ih h') ihf)
  · exact and_congr .rfl ihf
  · exact and_congr .rfl (and_congr (ih h') ihf)
  · exact and_congr .rfl (and_congr .rfl (and_congr (ih h') (ih h')))
  · exact ih h'

/-- The graph-level companion, in the form the `WF` clauses need. -/
theorem ShapeFun.lift_compat {n m} (h : n ≤ m) {Δ : List Term} {f f' : ShapeFun n} :
    Compat Shape.Compat Δ Ty (lift (Shape.lift m) f)
      (lift (Shape.lift m) f') ↔
    Compat Shape.Compat Δ Ty f f' := by
  constructor
  · intro H e he e' he' Θ τ hΘ W hlab hin
    have := H _ (mem_lift.2 ⟨e, he, rfl⟩) _ (mem_lift.2 ⟨e', he', rfl⟩) Θ τ hΘ W hlab
    rw [← Shape.lift_subst, ← Shape.lift_subst, ← Shape.lift_subst, ← Shape.lift_subst] at this
    exact (Shape.lift_compat h).1 (this ((Shape.lift_compat h).2 hin))
  · intro H e₁ he₁ e₂ he₂ Θ τ hΘ W hlab hin
    obtain ⟨e, he, rfl⟩ := mem_lift.1 he₁
    obtain ⟨e', he', rfl⟩ := mem_lift.1 he₂
    rw [← Shape.lift_subst, ← Shape.lift_subst] at hin ⊢
    exact (Shape.lift_compat h).2 (H e he e' he' Θ τ hΘ W hlab ((Shape.lift_compat h).1 hin))

/-- Lifting *up* preserves and reflects well-formedness. -/
theorem Shape.lift_wf {n m} (h : n ≤ m) {o} {s : Shape n} :
    (s.lift m).WF Δ o ↔ s.WF Δ o := by
  induction n generalizing m o with
  | zero =>
    cases m with
    | zero => rw [lift_self]
    | succ m => cases s <;> exact .rfl
  | succ n ih
  let m+1 := m; have h' := Nat.le_of_succ_le_succ h
  have ihf {Ty : Term} {oB : Option Term} {f : ShapeFun n} :
      ShapeFun.WF Δ Ty oB (@WF Δ _) (ShapeFun.lift (lift m) f) ↔
      f.WF Δ Ty oB (@WF Δ _) := by
    refine and_congr ?_ (ShapeFun.lift_compat h')
    constructor
    · intro H e he
      have ⟨hty, htm, hin, hout⟩ :=
        H ⟨e.tm, e.inp.lift m, e.out.lift m⟩ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)
      exact ⟨hty, htm, (ih h').1 hin, (ih h').1 hout⟩
    · intro H e'' he''
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
      have ⟨hty, htm, hin, hout⟩ := H e he
      exact ⟨hty, htm, (ih h').2 hin, (ih h').2 hout⟩
  have hnil {f : ShapeFun n} : ShapeFun.lift (lift m) f ≠ [] ↔ f ≠ [] := by
    cases f <;> simp [ShapeFun.lift]
  have hnb {f : ShapeFun n} :
      (∀ e ∈ ShapeFun.lift (lift m) f, ¬ e.out.IsBot) ↔ (∀ e ∈ f, ¬ e.out.IsBot) := by
    constructor
    · intro H e he hb
      exact H _ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩) ((lift_isBot h').2 hb)
    · intro H e'' he'' hb
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
      exact H e he ((lift_isBot h').1 hb)
  cases s with
  | bot | sort | unit | nat | zero | id | refl => rfl
  | succ => exact ih h'
  | pair A a x y =>
    exact and_congr (not_congr (and_congr (lift_isBot h') (lift_isBot h')))
      (and_congr .rfl (and_congr .rfl (and_congr (ih h') (ih h'))))
  | lam A f => exact and_congr hnil (and_congr hnb (and_congr ihf .rfl))
  | forallE | sigma =>
    exact and_congr .rfl (and_congr .rfl (and_congr (ih h') (and_congr ihf .rfl)))

/-- The same for a graph.  Extracted from `Shape.lift_wf`'s own `ihf`,
which cannot be reused directly because it is local to that induction. -/
theorem ShapeFun.lift_wf {n m} (h : n ≤ m) {Δ : List Term} {f : ShapeFun n} :
    WF Δ Ty oB (@Shape.WF Δ _) (lift (Shape.lift m) f) ↔
    f.WF Δ Ty oB (@Shape.WF Δ _) := by
  refine and_congr ?_ (lift_compat h)
  constructor
  · intro H e he
    have ⟨hty, htm, hin, hout⟩ :=
      H ⟨e.tm, e.inp.lift m, e.out.lift m⟩ (mem_lift.2 ⟨e, he, rfl⟩)
    exact ⟨hty, htm, (Shape.lift_wf h).1 hin, (Shape.lift_wf h).1 hout⟩
  · intro H e'' he''
    obtain ⟨e, he, rfl⟩ := mem_lift.1 he''
    have ⟨hty, htm, hin, hout⟩ := H e he
    exact ⟨hty, htm, (Shape.lift_wf h).2 hin, (Shape.lift_wf h).2 hout⟩

/-- The per-entry codomain names are lift-invariant, entry by entry. -/
theorem ShapeFun.codeCanonS_lift_iff {n m} (h : n ≤ m) {Δ : List Term} {B : Term}
    {f : ShapeFun n} :
    (∀ e ∈ lift (Shape.lift m) f, e.out.WF Δ (B.inst e.tm)) ↔
      ∀ e ∈ f, e.out.WF Δ (B.inst e.tm) := by
  refine ⟨fun H e he => (Shape.lift_wf h).1 (H _ (mem_lift.2 ⟨e, he, rfl⟩)), fun H e he => ?_⟩
  obtain ⟨a, ha, rfl⟩ := mem_lift.1 he
  exact (Shape.lift_wf h).2 (H a ha)

/-- Substitution composes on shapes, as it does on terms. -/
theorem Shape.subst_subst {σ τ : Subst} {n} {x : Shape n} :
    (x.subst σ).subst τ = x.subst (σ.comp τ) := by
  induction n with | zero => cases x <;> rfl | succ n ih
  cases x with
  | bot | sort | unit | nat | zero | refl => rfl
  | succ v => show ShapeS.succ _ = .succ _; rw [ih]
  | pair A a x y =>
    show ShapeS.pair .. = .pair ..
    simp [DomainSemantics.subst_subst, ih]
  | id r A a b =>
    show ShapeS.id .. = .id ..
    simp [DomainSemantics.subst_subst]
  | lam Af f =>
    show ShapeS.lam .. = .lam ..
    simp [ShapeFun.subst, DomainSemantics.subst_subst, ih]
  | forallE A B d f =>
    show ShapeS.forallE .. = .forallE ..
    simp [ShapeFun.subst, DomainSemantics.subst_subst, Subst.comp_lift, ih]
  | sigma A B d f =>
    show ShapeS.sigma .. = .sigma ..
    simp [ShapeFun.subst, DomainSemantics.subst_subst, Subst.comp_lift, ih]

/-- The total shape domain: a shape together with its level, as `popl27`'s
`TShape`.  The interpretation quantifies over this, so that the level
index never appears in the statement of a soundness lemma. -/
def TShape := Σ n, Shape n

/-- Inject a shape into `TShape` by remembering its level. -/
abbrev Shape.T {n} (s : Shape n) : TShape := ⟨n, s⟩

namespace TShape

def LE (Δ : List Term) (a b : TShape) : Prop :=
  Shape.LE Δ (a.2.lift (max a.1 b.1)) (b.2.lift (max a.1 b.1))

def WF (Δ : List Term) (a : TShape) (o : Option Term := none) : Prop := Shape.WF Δ a.2 o

def bot : TShape := Shape.T (n := 0) .bot

def sort (r : Bool) : TShape := Shape.T (n := 0) (.sort r)

abbrev type : TShape := sort true
abbrev prop : TShape := sort false

/-- Substitution acts levelwise. -/
def subst (a : TShape) (τ : Subst) : TShape := ⟨a.1, a.2.subst τ⟩

end TShape

/-! ## Compatibility and join

`Compat Δ x y` says `x` and `y` can be joined.  For graphs it is `popl27`'s
condition, with the label premise added: entries with definitionally equal
labels and compatible inputs must have compatible outputs.  That single
clause is what intgrah splits into `IsCoherent` (`f` against
itself) and `InternallyCompatible` (`f` against `g`).

`join` is context-free and total, producing junk (`⊥`) on mismatched
heads; it is a least upper bound only for compatible, well-formed shapes.
On graphs it is **append**, which is the lub for entry-wise coverage; the
old `ShapeFun.join` re-applied the graphs because they had to stay
saturated. -/

theorem Shape.lift_join {n m} (h : n ≤ m) {s t : Shape n} :
    (s.lift m).join (t.lift m) = (s.join t).lift m := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rw [lift_self, lift_self, lift_self]
    | succ m => cases s <;> cases t <;> rfl
  | succ n ih
  let m+1 := m; have h' := Nat.le_of_succ_le_succ h
  have ihf (f f' : ShapeFun n) :
      ShapeFun.lift (lift m) f ++ ShapeFun.lift (lift m) f' =
      ShapeFun.lift (lift m) (f ++ f') := (List.map_append ..).symm
  cases s <;> cases t <;> simp only [join, lift, ih h', ihf] <;> rfl

/-- Composing coverage of graphs.  This is the step that forces a graph to
carry a type at all: the two `LabelEq` proofs are chained by
`LabelEq.trans`, whose sort-typed component is handled by `IsDefEq.trans'`.
With a type-free label `∃ T, Δ ⊢ a ≡ a' : T`, transitivity would need
uniqueness of the middle term's type, which is the theorem this model
exists to prove. -/
theorem ShapeFun.LE.trans_of {Γ : List Term} {n} {f f' f'' : ShapeFun n}
    (ih : ∀ {a b c : Shape n}, a.LE Γ b → b.LE Γ c → a.LE Γ c)
    (h₁ : f.LE Γ (Shape.LE Γ) (@Shape.WF Γ _) Ty f')
    (h₂ : f'.LE Γ (Shape.LE Γ) (@Shape.WF Γ _) Ty f'') :
    f.LE Γ (Shape.LE Γ) (@Shape.WF Γ _) Ty f'' := by
  refine ⟨fun e he => ?_, h₁.2.1, h₂.2.2⟩
  exact Eval.trans (R := Shape.LE Γ) (fun _ _ _ h h' => ih h h') (h₁.2.1.1 e he).1 h₂.1
    (h₁.1 e he)

/-- Transitivity of the order. -/
theorem Shape.LE.trans (hΓ : ⊢ Γ) {n} {s t u : Shape n}
    (h₁ : s.LE Γ t) (h₂ : t.LE Γ u) : s.LE Γ u := by
  induction n with
  | zero => cases s <;> cases t <;> cases u <;> simp_all [LE]
  | succ _ ih
  cases s with
  | bot => trivial
  | lam Af f =>
    cases t with | lam Af' f' => ?_ | _ => cases h₁
    cases u with | lam Af'' f'' => ?_ | _ => cases h₂
    refine ⟨?_, h₁.2.1, h₁.2.2.1, h₁.2.2.2.1.trans h₂.2.2.2.1, h₁.2.2.2.2⟩
    exact h₁.1.trans_of ih (h₂.1.retype h₁.2.2.2.1.symm)
  | succ =>
    cases t <;> try cases h₁
    cases u <;> try cases h₂
    exact ih h₁ h₂
  | refl =>
    cases t <;> try cases h₁
    cases u <;> try cases h₂
    trivial
  | pair =>
    cases t <;> try exact absurd h₁ id
    cases u <;> try exact absurd h₂ id
    refine ⟨ih h₁.1 h₂.1, ih h₁.2.1 h₂.2.1, h₁.2.2.1, h₁.2.2.2.1.trans h₂.2.2.2.1, ?_⟩
    exact h₁.2.2.2.2.trans (h₁.2.2.2.1.symm.defeqDF h₂.2.2.2.2)
  | id =>
    cases t <;> cases h₁
    cases u <;> cases h₂
    exact ⟨.trans ‹_› ‹_›, .trans ‹_› ‹_›⟩
  | forallE | sigma =>
    cases t <;> cases h₁; rename_i h₁₁ h₁₂
    cases u <;> cases h₂; rename_i h₂₁ h₂₂
    refine ⟨h₁₁.trans hΓ h₂₁, ih h₁₂.1 h₂₂.1, ?_, h₁₂.2.2.1, h₁₂.2.2.2⟩
    exact h₁₂.2.1.trans_of ih (h₂₂.2.1.retype h₁₁.1.symm)
  | _ => cases t <;> cases u <;> simp_all [LE]

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
    (hx : f.Compat Shape.Compat Δ Ty f')
    (hx' : f'.Compat Shape.Compat Δ Ty f)
    (h₁ : f.LE Δ (Shape.LE Δ) (@Shape.WF Δ _) Ty g)
    (h₂ : f'.LE Δ (Shape.LE Δ) (@Shape.WF Δ _) Ty g) :
    (f ++ f').LE Δ (Shape.LE Δ) (@Shape.WF Δ _) Ty g := by
  refine ⟨fun e he => ?_, h₁.2.1.append h₂.2.1 hx hx', h₁.2.2⟩
  match List.mem_append.1 he with
  | .inl he => exact h₁.1 e he
  | .inr he => exact h₂.1 e he

/-- Being information-free is invariant under substitution, in both
directions: it is a structural property that never looks at a label. -/
theorem Shape.isBot_subst_iff {τ : Subst} {n} {s : Shape n} : (s.subst τ).IsBot ↔ s.IsBot := by
  induction n with | zero => cases s <;> rfl | succ n ih
  have hg (f : ShapeFun n) :
      (∀ e ∈ ShapeFun.subst (subst · τ) τ f, e.out.IsBot) ↔ ∀ e ∈ f, e.out.IsBot := by
    constructor
    · intro h e he
      exact ih.1 (h _ (ShapeFun.mem_subst.2 ⟨e, he, rfl⟩))
    · intro h d hd
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 hd
      exact ih.2 (h e he)
  cases s with
  | bot => rfl
  | lam Af f => exact hg f
  | pair A a x y => exact and_congr ih ih
  | _ => rfl

/-- Compatibility transports along a typed substitution.  The graph clauses
go through by *composing* substitutions, which is the whole point of
quantifying over later stages inside them; the rest is the label lemmas. -/
theorem ShapeFun.Compat.subst {Δ Θ : List Term} {τ : Subst}
    (W : Ctx.SubstEq Θ τ τ Δ) {n} {Ty : Term} {f f' : ShapeFun n}
    (h : f.Compat Shape.Compat Δ Ty f') :
    (f.subst (Shape.subst · τ) τ).Compat Shape.Compat Θ (Ty.subst τ)
      (ShapeFun.subst (Shape.subst · τ) τ f') := by
  intro d hd d' hd' Ξ υ hΞ V hlab hin
  obtain ⟨e, he, rfl⟩ := mem_subst.1 hd
  obtain ⟨e', he', rfl⟩ := mem_subst.1 hd'
  have hcomp : Ctx.SubstEq Ξ (τ.comp υ) (τ.comp υ) Δ := Ctx.SubstEq.comp hΞ V W
  simp only [subst_subst, Shape.subst_subst] at hlab hin ⊢
  exact h e he e' he' Ξ (τ.comp υ) hΞ hcomp hlab hin

theorem Shape.Compat.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {n} {x y : Shape n}
    (h : x.Compat Δ y) : (x.subst τ).Compat Θ (y.subst τ) := by
  induction n with
  | zero => cases x <;> cases y <;> simp_all [Compat, Shape.subst]
  | succ n ih
  have hfun {Ty : Term} {f f' : ShapeFun n} := @ShapeFun.Compat.subst _ _ _ W n Ty f f'
  cases x with
  | bot => trivial
  | lam Af f =>
    cases y with | bot => trivial | lam Af' f' => ?_ | _ => cases h
    exact ⟨h.1.subst hΘ W, hfun h.2⟩
  | forallE A B d f =>
    cases y with | bot => trivial | forallE A' B' d' f' => ?_ | _ => cases h
    exact ⟨h.1.subst hΘ W, ih h.2.1, hfun h.2.2⟩
  | sigma A B d f =>
    cases y with | bot => trivial | sigma A' B' d' f' => ?_ | _ => cases h
    exact ⟨h.1.subst hΘ W, ih h.2.1, hfun h.2.2⟩
  | succ v =>
    cases y with | bot => trivial | succ v' => ?_ | _ => cases h
    exact ih h
  | refl => cases y with | bot | refl => trivial | _ => cases h
  | pair a b =>
    cases y with | bot => trivial | pair A' a' x' y' => ?_ | _ => cases h
    exact ⟨h.1.subst hΘ W, h.2.1.subst hΘ W, ih h.2.2.1, ih h.2.2.2⟩
  | id r A a b =>
    cases y with | bot => trivial | id r' A' a' b' => ?_ | _ => cases h
    exact ⟨h.1, h.2.subst hΘ W⟩
  | sort r => cases y with | bot => trivial | sort r' => exact h | _ => cases h
  | unit r => cases y with | bot => trivial | unit r' => exact h | _ => cases h
  | nat => cases y with | bot | nat => trivial | _ => cases h
  | zero => cases y with | bot | zero => trivial | _ => cases h

theorem ShapeFun.WF.subst_of {Δ Θ : List Term} {τ : Subst} {n} {f : ShapeFun n}
    (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ)
    (ih : ∀ {o} {a : Shape n}, a.WF Δ o → (a.subst τ).WF Θ (o.map (·.subst τ)))
    (hf : f.WF Δ Ty oB (@Shape.WF Δ _)) :
    WF Θ (Ty.subst τ) (oB.map (·.subst τ.lift)) (@Shape.WF Θ _)
      (f.subst (Shape.subst · τ) τ) := by
  refine ⟨fun d hd => ?_, Compat.subst W hf.2⟩
  obtain ⟨e, he, rfl⟩ := mem_subst.1 hd
  have ⟨⟨u, hty⟩, htm, hin, hout⟩ := hf.1 e he
  refine ⟨⟨u, hty.subst hΘ W⟩, htm.subst hΘ W, ih hin, ?_⟩
  -- the codomain reads at the substituted label, which is `subst_inst`
  have h := ih hout
  cases oB with
  | none => exact h
  | some B => simpa [subst_inst] using h

theorem ShapeFun.WFE.subst_of {Δ Θ : List Term} {τ : Subst} {n} {f : ShapeFun n}
    (ih : ∀ {a : Shape n}, a.WF Δ → (a.subst τ).WF Θ)
    (hf : f.WFE (Shape.WF Δ)) :
    WFE (Shape.WF Θ) (subst (Shape.subst · τ) τ f) := by
  intro d hd
  obtain ⟨e, he, rfl⟩ := mem_subst.1 hd
  exact ⟨ih (hf e he).1, ih (hf e he).2⟩

/-- A name substitutes with the shape it names. -/
nonrec theorem TyEqO.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ)
    {o : Option Term} {T' : Term} (h : TyEqO Δ o T') :
    TyEqO Θ (o.map (·.subst τ)) (T'.subst τ) := by
  cases o with
  | none => trivial
  | some T => exact h.subst hΘ W

nonrec theorem Shape.WF.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ)
    {n o} {s : Shape n} (hs : s.WF Δ o) : (s.subst τ).WF Θ (o.map (·.subst τ)) := by
  induction n generalizing o with
  | zero => cases s <;> first | trivial | exact hs.subst hΘ W
  | succ n ih
  cases s with
  | bot | zero | refl => trivial
  | sort | unit | nat => exact hs.subst hΘ W
  | succ v => exact ih hs
  | pair A a x y =>
    have ⟨_, ha, hb, hx, hy⟩ := hs
    refine ⟨fun hbb => ?_, ha.subst hΘ W, hb.subst hΘ W, ih hx, ih hy⟩
    exact hs.1 ⟨isBot_subst_iff.1 hbb.1, isBot_subst_iff.1 hbb.2⟩
  | id r A a b =>
    have ⟨⟨u, hA⟩, ha, hb, hn⟩ := hs
    exact ⟨⟨u, hA.subst hΘ W⟩, ha.subst hΘ W, hb.subst hΘ W, hn.subst hΘ W⟩
  | lam Af f =>
    refine ⟨?_, fun d hd => ?_, ShapeFun.WF.subst_of hΘ W ih hs.2.2.1, hs.2.2.2.subst hΘ W⟩
    · intro hnil; simp [ShapeFun.subst] at hnil; exact hs.1 hnil
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 hd
      exact fun hb => hs.2.1 e he (isBot_subst_iff.1 hb)
  | forallE A B d f | sigma A B d f =>
    have ⟨⟨u, hA⟩, ⟨v, hB⟩, hd, hf, hn⟩ := hs
    have hA' := hA.subst hΘ W
    have hΘA : ⊢ A.subst τ :: Θ := ⟨hΘ, _, hA'⟩
    refine ⟨⟨u, hA'⟩, ⟨v, ?_⟩, ih hd, hf.subst_of hΘ W ih, hn.subst hΘ W⟩
    exact hB.subst hΘA (W.lift hA hA')

theorem Shape.join_subst {τ : Subst} {n} {x y : Shape n} :
    (x.join y).subst τ = (x.subst τ).join (y.subst τ) := by
  induction n with | zero => cases x <;> cases y <;> rfl | succ n ih
  cases x with
  | bot => rfl
  | lam Af f =>
    cases y with | lam Af' f' => ?_ | _ => rfl
    show lam .. = .lam _ _; simp [ShapeFun.subst]
  | forallE A B d f =>
    cases y with | forallE A' B' d' f' => ?_ | _ => rfl
    show ShapeS.forallE .. = .forallE ..
    simp [ShapeFun.subst, ih]
  | sigma A B d f =>
    cases y with | sigma A' B' d' f' => ?_ | _ => rfl
    show ShapeS.sigma .. = .sigma ..
    simp [ShapeFun.subst, ih]
  | succ v =>
    cases y with | succ v' => ?_ | _ => rfl
    show succ _ = succ _; rw [ih]
  | pair A a x₁ y₁ =>
    cases y with | pair A' a' x' y' => ?_ | _ => rfl
    show ShapeS.pair .. = .pair _ _ _ _; simp [ih]
  | _ => cases y <;> rfl

/-! ### Is `IsBot` a usable invariant?

Two facts decide whether bottom outputs can be forbidden inside graphs
(`popl27`'s `NonZero` / `lam'`, strengthened to a per-entry condition).
Unlike saturation — which failed because substitution merges label classes
— being information-free is *structural*: it never inspects a label, so it
is invariant under substitution in **both** directions, and it is
decidable. -/

instance Shape.decIsBot : ∀ {n} (s : Shape n), Decidable s.IsBot
  | 0, .bot => .isTrue trivial
  | 0, .sort _ => .isFalse id
  | _+1, .bot => .isTrue trivial
  | (n+1), .lam _ f =>
      @List.decidableBAll _ (fun e : Entry (Shape n) => IsBot e.out)
        (fun e => Shape.decIsBot e.out) f
  | _+1, .pair _ _ x y =>
      @instDecidableAnd _ _ (Shape.decIsBot x) (Shape.decIsBot y)
  | _+1, .sort _ | _+1, .unit _ | _+1, .nat | _+1, .zero
  | _+1, .succ _ | _+1, .refl
  | _+1, .id .. | _+1, .forallE .. | _+1, .sigma .. => .isFalse id

/-! ## Compatibility: symmetry, anti-monotonicity, common upper bounds

These are what the relational graph lookup needs.  `popl27` gets away
without them because its lookup is a saturated max-below *function*; ours
collects matching entries and joins them, so it has to know the joins
exist. -/

nonrec theorem Shape.Compat.symm {n} {Δ : List Term} {a b : Shape n} (hΔ : ⊢ Δ)
    (h : a.Compat Δ b) : b.Compat Δ a := by
  induction n generalizing Δ with
  | zero => cases a <;> cases b <;> simp_all [Compat]
  | succ n ih
  have hfun {Ty : Term} {f g : ShapeFun n} (hfg : f.Compat Compat Δ Ty g) :
      g.Compat Compat Δ Ty f := by
    intro e he e' he' Θ τ hΘ W hlab hin
    exact ih hΘ (hfg e' he' e he Θ τ hΘ W hlab.symm (ih hΘ hin))
  cases a with
  | bot => cases b <;> trivial
  | lam Af f =>
    cases b with | bot => trivial | lam Ag g => ?_ | _ => cases h
    exact ⟨h.1.symm, (hfun h.2).retype h.1⟩
  | forallE A B d f =>
    cases b with | bot => trivial | forallE A' B' d' f' => ?_ | _ => cases h
    exact ⟨h.1.symm hΔ, ih hΔ h.2.1, (hfun h.2.2).retype h.1.1⟩
  | sigma A B d f =>
    cases b with | bot => trivial | sigma A' B' d' f' => ?_ | _ => cases h
    exact ⟨h.1.symm hΔ, ih hΔ h.2.1, (hfun h.2.2).retype h.1.1⟩
  | succ v => cases b with | bot => trivial | succ v' => exact ih hΔ h | _ => cases h
  | refl => cases b with | bot | refl => trivial | _ => cases h
  | pair A a x y =>
    cases b with | bot => trivial | pair A' a' x' y' => ?_ | _ => cases h
    exact ⟨h.1.symm, h.1.defeqDF h.2.1.symm, ih hΔ h.2.2.1, ih hΔ h.2.2.2⟩
  | id r A a' b' =>
    cases b with | bot => trivial | id r' A'' a'' b'' => ?_ | _ => cases h
    exact ⟨h.1.symm, h.2.symm⟩
  | sort r => cases b with | bot => trivial | sort r' => exact h.symm | _ => cases h
  | unit r => cases b with | bot => trivial | unit r' => exact h.symm | _ => cases h
  | nat => cases b with | bot | nat => trivial | _ => cases h
  | zero => cases b with | bot | zero => trivial | _ => cases h

/-- The lookup transports along a typed substitution.  Mutual with
`Shape.LE.subst` across the level: this is the level-`n` statement, and
the order's own substitution lemma at `n+1` passes its induction
hypothesis in as `ih`. -/
theorem ShapeFun.Eval.subst_of {Δ Θ : List Term} {τ : Subst} {n} {f : ShapeFun n}
    {A a : Term} {x c : Shape n} (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ)
    (ih : ∀ {u v : Shape n}, u.LE Δ v → (u.subst τ).LE Θ (v.subst τ))
    (H : f.Eval Δ (Shape.LE Δ) A a x c) :
    Eval Θ (Shape.LE Θ) (subst (Shape.subst · τ) τ f)
      (A.subst τ) (a.subst τ) (x.subst τ) (c.subst τ) := by
  induction H with
  | bot => simp only [Shape.subst_bot]; exact .bot
  | entry e he hlab hin =>
    exact .entry _ (mem_subst.2 ⟨e, he, rfl⟩) (hlab.subst hΘ W) (ih hin)
  | lower hle _ ihe => exact .lower (ih hle) ihe
  | join hc _ _ ih₁ ih₂ => exact Shape.join_subst ▸ .join (hc.subst hΘ W) ih₁ ih₂

theorem ShapeFun.LE.subst_of {Δ Θ : List Term} {τ : Subst} {n} {f f' : ShapeFun n}
    (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ)
    (ih : ∀ {a b : Shape n}, a.LE Δ b → (a.subst τ).LE Θ (b.subst τ))
    (h : f.LE Δ (Shape.LE Δ) (@Shape.WF Δ _) Ty f') :
    (f.subst (Shape.subst · τ) τ).LE Θ (Shape.LE Θ) (@Shape.WF Θ _) (Ty.subst τ)
      (f'.subst (Shape.subst · τ) τ) := by
  refine ⟨fun d hd => ?_, h.2.1.subst_of hΘ W (Shape.WF.subst hΘ W),
    h.2.2.subst_of hΘ W (Shape.WF.subst hΘ W)⟩
  obtain ⟨e, he, rfl⟩ := mem_subst.1 hd
  exact Eval.subst_of hΘ W ih (h.1 e he)

theorem Shape.LE.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ)
    {n} {s t : Shape n} (h : s.LE Δ t) : (s.subst τ).LE Θ (t.subst τ) := by
  induction n with | zero => cases s <;> cases t <;> simp_all [LE, Shape.subst] | succ n ih
  cases s with
  | bot => trivial
  | lam =>
    cases t with | lam => ?_ | _ => cases h
    have hw := h.wf.subst hΘ W
    exact ⟨h.1.subst_of hΘ W ih, hw.1, hw.2.1, h.2.2.2.1.subst hΘ W, hw.2.2.2⟩
  | succ => cases t <;> (try cases h); exact ih h
  | refl => cases t <;> (try cases h); trivial
  | pair =>
    cases t <;> try exact absurd h id
    have hw := h.wf.subst hΘ W
    exact ⟨ih h.1, ih h.2.1, hw.1, h.2.2.2.1.subst hΘ W, h.2.2.2.2.subst hΘ W⟩
  | id => cases t <;> cases h; exact ⟨‹_›, .subst hΘ W ‹_›⟩
  | forallE | sigma =>
    cases t <;> cases h; rename_i h₁ h₂
    refine ⟨h₁.subst hΘ W, ih h₂.1, h₂.2.1.subst_of hΘ W ih, h₂.2.2.1.subst hΘ W, fun e he => ?_⟩
    obtain ⟨e₀, he₀, rfl⟩ := ShapeFun.mem_subst.1 he
    have := (h₂.2.2.2 e₀ he₀).subst hΘ W
    simpa [subst_inst] using this
  | _ => cases t <;> simp_all [LE, Shape.subst]

@[simp] theorem Shape.Compat.bot_left {n} {Δ : List Term} {b : Shape n} :
    Compat Δ .bot b := by cases n <;> trivial

@[simp] theorem Shape.Compat.bot_right {n} {Δ : List Term} {a : Shape n} :
    a.Compat Δ .bot := by cases n <;> cases a <;> trivial

/-- The join of two shapes compatible with `d` is compatible with `d`.
This is intgrah's `cSup_compatible`, and it is what lets the graph
lookup be closed under joins without losing coherence. -/
theorem Shape.Compat.join {n} {Δ : List Term} {y z d : Shape n} (hΔ : ⊢ Δ)
    (hy : y.Compat Δ d) (hz : z.Compat Δ d) : (y.join z).Compat Δ d := by
  induction n generalizing Δ with
  | zero => cases y <;> cases z <;> cases d <;> simp_all [Compat, Shape.join]
  | succ n ih
  cases y with
  | bot => exact hz
  | lam Af f =>
    cases z with | lam Ag g => ?_ | _ => exact hy
    cases d with | bot => trivial | lam Ah h => ?_ | _ => cases hy
    refine ⟨hy.1, fun e he e' he' Θ τ hΘ W hlab hin => ?_⟩
    cases List.mem_append.1 he with | inl he => exact hy.2 e he e' he' Θ τ hΘ W hlab hin | inr he
    exact (hz.2.retype (hz.1.trans hy.1.symm)) e he e' he' Θ τ hΘ W hlab hin
  | succ v =>
    cases z with | succ w => ?_ | _ => exact hy
    cases d with | bot => trivial | succ u => ?_ | _ => cases hy
    exact ih hΔ hy hz
  | refl =>
    cases z with | refl => ?_ | _ => exact hy
    cases d with | bot | refl => trivial | _ => cases hy
  | pair A₁ a₁ x₁ y₁ =>
    cases z with | pair A₂ a₂ x₂ y₂ => ?_ | _ => exact hy
    cases d with | bot => trivial | pair A₃ a₃ x₃ y₃ => ?_ | _ => cases hy
    exact ⟨hy.1, hy.2.1, ih hΔ hy.2.2.1 hz.2.2.1, ih hΔ hy.2.2.2 hz.2.2.2⟩
  | forallE A₁ B₁ d₁ f =>
    cases z with | forallE A₂ B₂ d₂ g => ?_ | _ => exact hy
    cases d with | bot => trivial | forallE A₃ B₃ d₃ h => ?_ | _ => cases hy
    refine ⟨hy.1, ih hΔ hy.2.1 hz.2.1, ?_⟩
    intro e he e' he' Θ τ hΘ W hlab hin
    cases List.mem_append.1 he with | inl he => exact hy.2.2 e he e' he' Θ τ hΘ W hlab hin | inr he
    exact (hz.2.2.retype (hz.1.1.trans hy.1.1.symm)) e he e' he' Θ τ hΘ W hlab hin
  | sigma A₁ B₁ d₁ f =>
    cases z with | sigma A₂ B₂ d₂ g => ?_ | _ => exact hy
    cases d with | bot => trivial | sigma A₃ B₃ d₃ h => ?_ | _ => cases hy
    refine ⟨hy.1, ih hΔ hy.2.1 hz.2.1, ?_⟩
    intro e he e' he' Θ τ hΘ W hlab hin
    cases List.mem_append.1 he with | inl he => exact hy.2.2 e he e' he' Θ τ hΘ W hlab hin | inr he
    exact (hz.2.2.retype (hz.1.1.trans hy.1.1.symm)) e he e' he' Θ τ hΘ W hlab hin
  | sort | unit | nat | zero | id => cases z <;> exact hy

/-- The graph half of `Shape.Compat.anti_right`, once, for the three
clauses that carry a graph.  The covering fact is a lookup derivation, so
the coherence of the bigger graph is applied once per matching entry and
the results recombined; `ih` is the order-antitonicity one level down,
which the recursion supplies. -/
theorem ShapeFun.Compat.anti_right_of {Δ : List Term} {n} {f g g' : ShapeFun n}
    (ih : ∀ {Θ : List Term} {a b b' : Shape n}, ⊢ Θ →
      a.Compat Θ b → b'.LE Θ b → a.Compat Θ b')
    (h : f.Compat Shape.Compat Δ Ty g)
    (hb : ∀ e ∈ g', g.Eval Δ (Shape.LE Δ) Ty e.tm e.inp e.out) :
    f.Compat Shape.Compat Δ Ty g' := by
  intro e he e' he' Θ τ hΘ W hlab hin
  suffices key : ∀ {y}, g.Eval Δ (Shape.LE Δ) Ty e'.tm e'.inp y →
      (e.out.subst τ).Compat Θ (y.subst τ) from key (hb e' he')
  intro y hy
  induction hy with
  | bot => simpa only [Shape.subst_bot] using Shape.Compat.bot_right
  | entry e₂ he₂ hl₂ hi₂ =>
    exact h e he e₂ he₂ Θ τ hΘ W (hlab.trans (hl₂.subst hΘ W).symm) (ih hΘ hin (hi₂.subst hΘ W))
  | lower hle _ ihz => exact ih hΘ ihz (hle.subst hΘ W)
  | join _ _ _ ih₁ ih₂ =>
    exact Shape.join_subst ▸ ((ih₁.symm hΘ).join hΘ (ih₂.symm hΘ)).symm hΘ

/-- Compatibility is **anti-monotone on the right**.

The graph case is where the hereditary quantification earns its keep: the
covering entry's label agrees with the query's at the later stage by
transitivity of `LabelEq`, its input is compatible by the inductive
hypothesis, so the hypothesis applies there and hands back compatible
outputs, which the inductive hypothesis pushes back down.

Stated one-sided on purpose.  A two-sided induction would need
reflexivity of `LE` on the left argument, and reflexivity holds only on
well-formed shapes, which would drag a `WF` hypothesis into every use. -/
theorem Shape.Compat.anti_right {n} {Δ : List Term} {a b b' : Shape n} (hΔ : ⊢ Δ)
    (h : a.Compat Δ b) (hb : b'.LE Δ b) : a.Compat Δ b' := by
  induction n generalizing Δ with
  | zero => cases a <;> cases b <;> cases b' <;> simp_all [Compat, LE]
  | succ n ih
  cases a with
  | bot => trivial
  | lam Af f =>
    cases b with
    | bot => cases b' with | bot => trivial | _ => cases hb
    | lam Ag g => ?_ | _ => cases h
    cases b' with | bot => trivial | lam Ag' g' => ?_ | _ => cases hb
    refine ⟨h.1.trans hb.2.2.2.1.symm, h.2.anti_right_of ih fun e he => ?_⟩
    exact (hb.1.1 e he).retype (hb.2.2.2.1.trans h.1.symm)
  | succ v =>
    cases b with
    | bot => cases b' with | bot => trivial | _ => cases hb
    | succ w => ?_ | _ => cases h
    cases b' with | bot => trivial | succ w' => ?_ | _ => cases hb
    exact ih hΔ h hb
  | refl =>
    cases b with
    | bot => cases b' with | bot => trivial | _ => cases hb
    | refl => ?_ | _ => cases h
    cases b' with | bot | refl => trivial | _ => cases hb
  | pair A₀ a₀ x y =>
    cases b with
    | bot => cases b' with | bot => trivial | _ => cases hb
    | pair Ab ab u v => ?_ | _ => cases h
    cases b' with | bot => trivial | pair A' a' x' y' => ?_ | _ => cases hb
    refine ⟨h.1.trans hb.2.2.2.1.symm, ?_, ih hΔ h.2.2.1 hb.1, ih hΔ h.2.2.2 hb.2.1⟩
    exact h.2.1.trans ((h.1.trans hb.2.2.2.1.symm).symm.defeqDF (hb.2.2.2.2.symm))
  | id r A₀ a₀ b₀ =>
    cases b with
    | bot => cases b' with | bot => trivial | _ => cases hb
    | id rb Ab ab bb => ?_ | _ => cases h
    cases b' with | bot => trivial | id r' A₁ a₁ b₁ => ?_ | _ => cases hb
    exact ⟨h.1.trans hb.1.symm, h.2.trans hb.2.symm⟩
  | forallE A₀ B₀ d f =>
    cases b with
    | bot => cases b' with | bot => trivial | _ => cases hb
    | forallE Ab Bb db fb => ?_ | _ => cases h
    cases b' with | bot => trivial | forallE A₁ B₁ e' g' => ?_ | _ => cases hb
    refine ⟨h.1.trans hΔ (hb.1.symm hΔ), ih hΔ h.2.1 hb.2.1, ?_⟩
    refine h.2.2.anti_right_of ih fun e he => ?_
    exact (hb.2.2.1.1 e he).retype (hb.1.1.trans h.1.1.symm)
  | sigma A₀ B₀ d f =>
    cases b with
    | bot => cases b' with | bot => trivial | _ => cases hb
    | sigma Ab Bb db fb => ?_ | _ => cases h
    cases b' with | bot => trivial | sigma A₁ B₁ e' g' => ?_ | _ => cases hb
    refine ⟨h.1.trans hΔ (hb.1.symm hΔ), ih hΔ h.2.1 hb.2.1, ?_⟩
    refine h.2.2.anti_right_of ih fun e he => ?_
    exact (hb.2.2.1.1 e he).retype (hb.1.1.trans h.1.1.symm)
  | sort r =>
    cases b with
    | bot => cases b' with | bot => trivial | _ => cases hb
    | sort rb => ?_ | _ => cases h
    cases b' with | bot => trivial | sort s => ?_ | _ => cases hb
    exact (h : r = rb).trans (hb : s = rb).symm
  | unit r =>
    cases b with
    | bot => cases b' with | bot => trivial | _ => cases hb
    | unit rb => ?_ | _ => cases h
    cases b' with | bot => trivial | unit s => ?_ | _ => cases hb
    exact (h : r = rb).trans (hb : s = rb).symm
  | nat =>
    cases b with
    | bot => cases b' with | bot => trivial | _ => cases hb
    | nat => ?_ | _ => cases h
    cases b' with | bot | nat => trivial | _ => cases hb
  | zero =>
    cases b with
    | bot => cases b' with | bot => trivial | _ => cases hb
    | zero => ?_ | _ => cases h
    cases b' with | bot | zero => trivial | _ => cases hb

/-- Compatibility is anti-monotone in both arguments. -/
theorem Shape.Compat.anti {n} {Δ : List Term} {a b a' b' : Shape n} (hΔ : ⊢ Δ)
    (h : a.Compat Δ b) (ha : a'.LE Δ a) (hb : b'.LE Δ b) :
    a'.Compat Δ b' :=
  (((h.anti_right hΔ hb).symm hΔ).anti_right hΔ ha).symm hΔ

/-- Two shapes below a common **coherent** upper bound are compatible.
This is the form the graph lookup needs: whenever two entries are selected
by the same query their inputs are both below the query shape, so this
supplies the hypothesis that coherence asks for. -/
theorem Shape.Compat.of_common_upper {n} {Δ : List Term} {a b c : Shape n} (hΔ : ⊢ Δ)
    (hc : c.Compat Δ c) (ha : a.LE Δ c) (hb : b.LE Δ c) :
    a.Compat Δ b := hc.anti hΔ ha hb

theorem ShapeFun.Compat.symm {n} {Δ : List Term} {f f' : ShapeFun n}
    (h : f.Compat Shape.Compat Δ Ty f') : f'.Compat Shape.Compat Δ Ty f :=
  fun e he e' he' Θ τ hΘ W hlab hin =>
    (h e' he' e he Θ τ hΘ W hlab.symm (hin.symm hΘ)).symm hΘ

/-- Two graphs under a common self-coherent graph are coherent with each
other.  The shape-level `of_common_upper` cannot be used through a `.lam`
wrapper any more — that would ask for the λ non-degeneracy of graphs which
need not have it — so it goes through `anti_right_of` directly. -/
theorem ShapeFun.Compat.of_common_upper {n} {Δ : List Term} {f f' g : ShapeFun n}
    (hg : g.Compat Shape.Compat Δ Ty g)
    (h₁ : f.LE Δ (Shape.LE Δ) (@Shape.WF Δ _) Ty g)
    (h₂ : f'.LE Δ (Shape.LE Δ) (@Shape.WF Δ _) Ty g) :
    f.Compat Shape.Compat Δ Ty f' :=
  have anti {Θ : List Term} {a b b' : Shape n} (hΘ : ⊢ Θ) :
      a.Compat Θ b → b'.LE Θ b → a.Compat Θ b' :=
    Shape.Compat.anti_right hΘ
  .anti_right_of anti (hg.anti_right_of anti h₁.1).symm h₂.1

@[simp] theorem Shape.subst_id {n} {s : Shape n} : s.subst .id = s := by
  induction n with | zero => cases s <;> rfl | succ n ih
  have hf (f : ShapeFun n) : f.subst (subst · .id) .id = f := by
    induction f with | nil => rfl | cons e f ihf
    simp only [ShapeFun.subst, List.map_cons] at ihf ⊢
    rw [ih, ih, ihf, DomainSemantics.subst_id]
  cases s with
  | bot | sort | unit | nat | zero | refl => rfl
  | succ v => show ShapeS.succ _ = _; rw [ih]
  | pair A a x y =>
    show ShapeS.pair .. = _
    rw [ih, ih, DomainSemantics.subst_id, DomainSemantics.subst_id]
  | id r A a b =>
    show ShapeS.id .. = _
    rw [DomainSemantics.subst_id, DomainSemantics.subst_id, DomainSemantics.subst_id]
  | lam Af f =>
    show ShapeS.lam .. = _
    rw [hf, DomainSemantics.subst_id]
  | forallE A B d f =>
    show ShapeS.forallE .. = _
    rw [ih, hf, DomainSemantics.subst_id, id_lift, DomainSemantics.subst_id]
  | sigma A B d f =>
    show ShapeS.sigma .. = _
    rw [ih, hf, DomainSemantics.subst_id, id_lift, DomainSemantics.subst_id]

/-- **The join keeps a name both sides carry.**  Its structural half is a
hypothesis, because the two places that need this have it already and
reach it by different routes. -/
theorem Shape.WF.join_of {n} {Γ : List Term} {T : Term} {y z : Shape n}
    (hw : (y.join z).WF Γ) (hy : y.WF Γ T) (hz : z.WF Γ T) :
    (y.join z).WF Γ T := by
  cases n <;> cases y <;> cases z <;> first
    | exact hw
    | exact hy
    | exact hz
    | exact ⟨hw.1, hw.2.1, hw.2.2.1, hy.2.2.2⟩
    | exact ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hy.2.2.2.2⟩

/-- The left argument of a join is information-free whenever the join is.
Only the left, and that is enough: the right-hand version fails for
mismatched heads (`join (lam []) (sort r)` is `lam []`, which is
information-free, while `sort r` is not), and `WF.join` only ever needs
the left one, applied to each component of a pair. -/
theorem Shape.IsBot.of_join_left {n} {x y : Shape n} (h : (x.join y).IsBot) : x.IsBot := by
  induction n with | zero => cases x <;> cases y <;> trivial | succ n ih
  cases x with
  | bot => trivial
  | lam Af f =>
    cases y with | lam Af' f' => ?_ | _ => exact h
    intro e he; exact h e (List.mem_append.2 (.inl he))
  | pair A a x₁ y₁ =>
    cases y with | pair A' a' x' y' => ?_ | _ => exact h
    exact ⟨ih h.1, ih h.2⟩
  | _ => cases y <;> exact h

theorem Shape.join_le (hΔ : ⊢ Δ) {n} {x y w : Shape n}
    (h₁ : x.LE Δ w) (h₂ : y.LE Δ w) : (x.join y).LE Δ w := by
  induction n with
  | zero => cases x with | bot => exact h₂ | sort r => cases y <;> exact h₁
  | succ n ih
  cases x with
  | bot => exact h₂
  | lam Af f =>
    cases y with | lam Af' f' => ?_ | _ => exact h₁
    cases w with | lam Ag g => ?_ | _ => cases h₁
    have h₂' := h₂.1.retype (h₂.2.2.2.1.trans h₁.2.2.2.1.symm)
    have hc : ShapeFun.Compat Compat Δ Af f f' :=
      h₁.1.2.2.2.of_common_upper h₁.1 h₂'
    refine ⟨ShapeFun.LE.append hc hc.symm h₁.1 h₂', ?_, ?_, h₁.2.2.2⟩
    · exact fun hnil => h₁.2.1 (List.append_eq_nil_iff.1 hnil).1
    · exact fun e he => (List.mem_append.1 he).elim (h₁.2.2.1 e) (h₂.2.2.1 e)
  | forallE A B d f =>
    cases y with | bot => exact h₁ | forallE A' B' d' f' => ?_ | _ => exact h₁
    cases w <;> try exact absurd h₁ id
    refine ⟨h₁.1, ih h₁.2.1 h₂.2.1, ?_, ?_, ?_⟩
    · have h₂' := h₂.2.2.1.retype (h₂.1.1.trans h₁.1.1.symm)
      have hc : ShapeFun.Compat Compat Δ A f f' :=
        h₁.2.2.1.2.2.2.of_common_upper h₁.2.2.1 h₂'
      exact ShapeFun.LE.append hc hc.symm h₁.2.2.1 h₂'
    · have hpi := h₁.1.trans hΔ (h₂.1.symm hΔ)
      exact (ih h₁.2.1 h₂.2.1).wf.join_of h₁.2.2.2.1 (h₂.2.2.2.1.conv hpi.1)
    · have hpi := h₁.1.trans hΔ (h₂.1.symm hΔ)
      refine ShapeFun.codeCanonS_append hΔ hpi (fun e he => ?_) h₁.2.2.2.2 h₂.2.2.2.2
      exact (h₂.wf.2.2.2.1.1 e he).2.1
  | sigma A B d f =>
    cases y with | bot => exact h₁ | sigma A' B' d' f' => ?_ | _ => exact h₁
    cases w <;> try exact absurd h₁ id
    refine ⟨h₁.1, ih h₁.2.1 h₂.2.1, ?_, ?_, ?_⟩
    · have h₂' := h₂.2.2.1.retype (h₂.1.1.trans h₁.1.1.symm)
      have hc : ShapeFun.Compat Compat Δ A f f' :=
        h₁.2.2.1.2.2.2.of_common_upper h₁.2.2.1 h₂'
      exact ShapeFun.LE.append hc hc.symm h₁.2.2.1 h₂'
    · have hpi := h₁.1.trans hΔ (h₂.1.symm hΔ)
      exact (ih h₁.2.1 h₂.2.1).wf.join_of h₁.2.2.2.1 (h₂.2.2.2.1.conv hpi.1)
    · have hpi := h₁.1.trans hΔ (h₂.1.symm hΔ)
      refine ShapeFun.codeCanonS_append hΔ hpi (fun e he => ?_) h₁.2.2.2.2 h₂.2.2.2.2
      exact (h₂.wf.2.2.2.1.1 e he).2.1
  | succ v =>
    cases y with | succ v' => ?_ | _ => exact h₁
    cases w <;> first | exact absurd h₁ id | exact ih h₁ h₂
  | refl =>
    cases y with | refl => ?_ | _ => exact h₁
    cases w <;> first | exact absurd h₁ id | trivial
  | pair A a x₁ y₁ =>
    cases y with | pair A' a' x' y' => ?_ | _ => exact h₁
    cases w <;> try exact absurd h₁ id
    refine ⟨ih h₁.1 h₂.1, ih h₁.2.1 h₂.2.1, fun hbb => ?_, h₁.2.2.2⟩
    exact h₁.2.2.1 ⟨hbb.1.of_join_left, hbb.2.of_join_left⟩
  | sort | unit | nat | zero | id => cases y <;> exact h₁

theorem ShapeFun.LE.refl {Δ : List Term} {n} {f : ShapeFun n}
    (hf : f.WF Δ Ty none (@Shape.WF Δ _)) :
    f.LE Δ (Shape.LE Δ) (@Shape.WF Δ _) Ty f := by
  refine ⟨fun e he => ?_, hf, hf⟩
  have ⟨⟨_, hty⟩, htm, hin, _⟩ := hf.1 e he
  exact .entry e he (.refl hty htm) (.refl hin)

theorem ShapeFun.LE.append_left {Δ : List Term} {n} {f f' : ShapeFun n}
    (hf : f.WF Δ Ty none (@Shape.WF Δ _))
    (hfg : (f ++ f').WF Δ Ty none (@Shape.WF Δ _)) :
    f.LE Δ (Shape.LE Δ) (@Shape.WF Δ _) Ty (f ++ f') := by
  refine ⟨fun e he => ?_, hf, hfg⟩
  have ⟨⟨_, hty⟩, htm, hin, _⟩ := hf.1 e he
  exact .entry e (List.mem_append.2 (.inl he)) (.refl hty htm) (.refl hin)

theorem ShapeFun.LE.append_right {Δ : List Term} {n} {f f' : ShapeFun n}
    (hf' : f'.WF Δ Ty none (@Shape.WF Δ _))
    (hfg : (f ++ f').WF Δ Ty none (@Shape.WF Δ _)) :
    f'.LE Δ (Shape.LE Δ) (@Shape.WF Δ _) Ty (f ++ f') := by
  refine ⟨fun e he => ?_, hf', hfg⟩
  have ⟨⟨_, hty⟩, htm, hin, _⟩ := hf'.1 e he
  exact .entry e (List.mem_append.2 (.inr he)) (.refl hty htm) (.refl hin)

/-- The join is an upper bound.  Needs `WF` (the order is reflexive only on
well-formed shapes) and `Compat` (to know the labels agree, and to know
that a λ-shape facing a different head is information-free). -/
theorem Shape.le_join (hΔ : ⊢ Δ) {n} {x y : Shape n} (hx : x.WF Δ) (hy : y.WF Δ)
    (h : x.Compat Δ y) : x.LE Δ (x.join y) ∧ y.LE Δ (x.join y) := by
  induction n with
  | zero =>
    cases x with | bot => exact ⟨trivial, .refl hy⟩ | sort r => ?_
    cases y with | bot => exact ⟨.refl hx, trivial⟩ | sort r' => ?_
    exact ⟨rfl, (show r = r' from h).symm⟩
  | succ n ih
  cases x with
  | bot => exact ⟨trivial, .refl hy⟩
  | lam Af f =>
    cases y with | bot => exact ⟨.refl hx, trivial⟩ | lam Af' f' => ?_ | _ => cases h
    have hxf := hx.2.2.1.forget
    have hyf := hy.2.2.1.forget
    have hfg := hxf.append (hyf.retype h.1.symm) h.2 h.2.symm
    refine ⟨⟨.append_left hxf hfg, hx.1, hx.2.1, hx.dom, hx.2.2.2⟩, ?_⟩
    exact ⟨.append_right hyf (hfg.retype h.1), hy.1, hy.2.1, h.1.symm, hy.2.2.2⟩
  | forallE A B d f =>
    cases y with | bot => exact ⟨.refl hx, trivial⟩ | forallE A' B' d' f' => ?_ | _ => cases h
    have ⟨⟨_, hA⟩, ⟨_, hB⟩, hd, hff, _⟩ := hx
    have hxf := hff.forget
    have hyf := hy.2.2.2.1.forget
    have hfg := hxf.append (hyf.retype h.1.1.symm) h.2.2 h.2.2.symm
    have hle := ih hd.forget hy.2.2.1.forget h.2.1
    refine ⟨?_, h.1.symm hΔ, hle.2, ?_, hy.2.2.1, hy.2.2.2.1.canon⟩
    · exact ⟨.refl hA hB, hle.1, .append_left hxf hfg, hd, hff.canon⟩
    exact .append_right hyf (hfg.retype h.1.1)
  | sigma A B d f =>
    cases y with | bot => exact ⟨.refl hx, trivial⟩ | sigma A' B' d' f' => ?_ | _ => cases h
    have ⟨⟨_, hA⟩, ⟨_, hB⟩, hd, hff, _⟩ := hx
    have hxf := hff.forget
    have hyf := hy.2.2.2.1.forget
    have hfg := hxf.append (hyf.retype h.1.1.symm) h.2.2 h.2.2.symm
    have hle := ih hd.forget hy.2.2.1.forget h.2.1
    refine ⟨?_, h.1.symm hΔ, hle.2, ?_, hy.2.2.1, hy.2.2.2.1.canon⟩
    · exact ⟨.refl hA hB, hle.1, .append_left hxf hfg, hd, hff.canon⟩
    exact .append_right hyf (hfg.retype h.1.1)
  | succ v =>
    cases y with | bot => exact ⟨.refl hx, trivial⟩ | succ v' => ?_ | _ => cases h
    exact ih hx hy h
  | refl => cases y with | bot => exact ⟨.refl hx, trivial⟩ | refl => trivial | _ => cases h
  | pair A a x₁ y₁ =>
    cases y with | bot => exact ⟨.refl hx, trivial⟩ | pair A' a' x' y' => ?_ | _ => cases h
    have hxx := ih hx.2.2.2.1 hy.2.2.2.1 h.2.2.1
    have hyy := ih hx.2.2.2.2 hy.2.2.2.2 h.2.2.2
    refine ⟨⟨hxx.1, hyy.1, hx.1, hx.pair_dom, hx.2.1⟩, hxx.2, hyy.2, hy.1, h.1.symm, ?_⟩
    exact h.1.defeqDF h.2.1.symm
  | sort r =>
    cases y with | bot => exact ⟨.refl hx, trivial⟩ | sort r' => ?_ | _ => cases h
    exact ⟨rfl, (show r = r' from h).symm⟩
  | unit r =>
    cases y with | bot => exact ⟨.refl hx, trivial⟩ | unit r' => ?_ | _ => cases h
    exact ⟨rfl, (show r = r' from h).symm⟩
  | nat => cases y with | bot => exact ⟨.refl hx, trivial⟩ | nat => trivial | _ => cases h
  | zero => cases y with | bot => exact ⟨.refl hx, trivial⟩ | zero => trivial | _ => cases h
  | id r A a b =>
    cases y with | bot => exact ⟨.refl hx, trivial⟩ | id r' A' a' b' => ?_ | _ => cases h
    have ⟨⟨_, hA⟩, ha, hb, _⟩ := hx
    exact ⟨⟨rfl, .refl hA ha hb⟩, ⟨h.1.symm, h.2.symm⟩⟩

theorem Shape.WF.join {n} {Δ : List Term} {y z : Shape n} (hΔ : ⊢ Δ)
    (hc : y.Compat Δ z) (hy : y.WF Δ) (hz : z.WF Δ) :
    (y.join z).WF Δ := by
  induction n with | zero => cases y <;> cases z <;> trivial | succ n ih
  cases y with
  | bot => exact hz
  | lam Af f =>
    cases z with | lam Ag g => ?_ | _ => exact hy
    refine ⟨fun hnil => ?_, fun e he => ?_, ?_, hy.2.2.2⟩
    · exact hy.1 (List.append_eq_nil_iff.1 hnil).1
    · match List.mem_append.1 he with
      | .inl he => exact hy.2.1 e he
      | .inr he => exact hz.2.1 e he
    · exact hy.2.2.1.forget.append (hz.2.2.1.forget.retype hc.1.symm) hc.2 hc.2.symm
  | forallE A B d f | sigma A B d f =>
    cases z <;> try exact hy
    refine ⟨hy.1, hy.2.1, ?_, .name ?_ ?_, trivial⟩
    · exact (ih hc.2.1 hy.2.2.1.forget hz.2.2.1.forget).join_of hy.2.2.1 (hz.2.2.1.conv hc.1.1)
    · exact hy.2.2.2.1.forget.append (hz.2.2.2.1.forget.retype hc.1.1.symm) hc.2.2 hc.2.2.symm
    refine ShapeFun.codeCanonS_append hΔ hc.1 (fun e he => ?_) hy.2.2.2.1.canon hz.2.2.2.1.canon
    exact (hz.2.2.2.1.1 e he).2.1
  | succ v => cases z with | succ w => exact ih hc hy hz | _ => exact hy
  | refl => cases z with | refl => trivial | _ => exact hy
  | pair A a x₁ y₁ =>
    cases z with | pair A' a' x' y' => ?_ | _ => exact hy
    refine ⟨fun hb => ?_, hy.2.1, hy.2.2.1, ih hc.2.2.1 hy.2.2.2.1 hz.2.2.2.1,
      ih hc.2.2.2 hy.2.2.2.2 hz.2.2.2.2⟩
    exact hy.1 ⟨hb.1.of_join_left, hb.2.of_join_left⟩
  | sort | unit | nat | zero | id => cases z <;> exact hy

/-- The join keeps a name both sides carry: its structural half is
`WF.join` and its naming half is the surviving `TyEqO` conjunct. -/
theorem Shape.WF.join_mem {n} {Δ : List Term} {y z : Shape n} {o} (hΔ : ⊢ Δ)
    (hc : y.Compat Δ z) (hy : y.WF Δ o) (hz : z.WF Δ o) :
    (y.join z).WF Δ o := by
  have hw := hy.forget.join hΔ hc hz.forget
  cases o with
  | none => exact hw
  | some T => exact hw.join_of hy hz

/-- A well-formed shape is coherent with itself. -/
theorem Shape.WF.coherent {n} {s : Shape n} (hs : s.WF Δ) : s.Compat Δ s := by
  induction n with | zero => cases s <;> trivial | succ n ih
  cases s with
  | bot | sort | unit | nat | zero | refl => trivial
  | succ v => exact ih hs
  | pair A a x y => exact ⟨hs.pair_dom, hs.2.1, ih hs.2.2.2.1, ih hs.2.2.2.2⟩
  | id r A a b =>
    have ⟨⟨_, hA⟩, ha, hb, _⟩ := hs
    exact ⟨rfl, .refl hA ha hb⟩
  | lam Af f => exact ⟨hs.dom, hs.2.2.1.2⟩
  | forallE A B d f | sigma A B d f =>
    have ⟨⟨_, hA⟩, ⟨_, hB⟩, hd, hf, _⟩ := hs
    exact ⟨.refl hA hB, ih hd.forget, hf.2⟩

/-! ## The lookup's own theory, and reflection of the order along `lift`

`Eval.wf` and `Eval.compat` are what the lookup's `join` side condition
was put there for, and `Eval.lift_of` is what it buys: a lookup over a lifted
graph lands below the lift of a lookup over the original.  With that, the
order reflects along `lift`, which is what makes the level index invisible
(`TShape.LE.def`).  Entry coverage would get the reflection for free —
entries of `f.lift` are lifts of entries of `f` — but could not express η;
this is the trade. -/

/-- Everything the lookup returns is well formed. -/
theorem ShapeFun.Eval.wf {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a : Term}
    {x : Shape n} (hf : ∀ e ∈ f, e.out.WF Δ) {y : Shape n}
    (h : f.Eval Δ (Shape.LE Δ) A a x y) : y.WF Δ := by
  induction h with
  | bot => cases n <;> trivial
  | entry e he => exact hf e he
  | lower hle => exact hle.wf
  | join hc _ _ ih₁ ih₂ => exact ih₁.join hΔ hc ih₂

/-- Any two values of one lookup are compatible, given a coherent graph
and a coherent query. -/
theorem ShapeFun.Eval.compat {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a : Term}
    {x : Shape n} (hf : f.Compat Shape.Compat Δ A f) (hx : x.Compat Δ x)
    {y z : Shape n} (hy : f.Eval Δ (Shape.LE Δ) A a x y)
    (hz : f.Eval Δ (Shape.LE Δ) A a x z) : y.Compat Δ z := by
  induction hy with
  | bot => exact .bot_left
  | lower hle _ ih => exact ih.symm hΔ |>.anti_right hΔ hle |>.symm hΔ
  | join _ _ _ ih₁ ih₂ => exact ih₁.join hΔ ih₂
  | entry e he hlab hin
  induction hz with
  | bot => exact .bot_right
  | entry e' he' hlab' hin' =>
    have := hf e he e' he' Δ .id hΔ (.id hΔ) ?_ ?_
    · simpa using this
    · simpa using hlab.trans hlab'.symm
    simpa using hx.of_common_upper hΔ hin hin'
  | lower hle _ ih => exact ih.anti_right hΔ hle
  | join _ _ _ ih₁ ih₂ => exact ((ih₁.symm hΔ).join hΔ (ih₂.symm hΔ)).symm hΔ

/-- A lookup transports up a level. -/
theorem ShapeFun.Eval.lift {Δ : List Term} {n k} (h : n ≤ k) {f : ShapeFun n}
    {A a : Term} {x c : Shape n}
    (ihlift : ∀ {u v : Shape n}, u.LE Δ v → (u.lift k).LE Δ (v.lift k))
    (H : f.Eval Δ (Shape.LE Δ) A a x c) :
    Eval Δ (Shape.LE Δ) (ShapeFun.lift (Shape.lift k) f) A a (x.lift k) (c.lift k) := by
  induction H with
  | bot => rw [Shape.lift_bot]; exact .bot
  | entry e he hlab hin =>
    exact .entry _ (mem_lift.2 ⟨e, he, rfl⟩) hlab (ihlift hin)
  | lower hle _ ih => exact .lower (ihlift hle) ih
  | join hc _ _ ih₁ ih₂ =>
    exact Shape.lift_join h ▸ .join ((Shape.lift_compat h).2 hc) ih₁ ih₂

/-- A lookup over a lifted graph lands below the lift of a lookup over the
original.  The `join` case is where the side condition earns its keep:
the two reflected values are compatible (`Eval.compat`) and well formed
(`Eval.wf`), so `le_join` applies and their join is an upper bound. -/
theorem ShapeFun.Eval.lift_of {Δ : List Term} (hΔ : ⊢ Δ) {n k} (h : n ≤ k) {f : ShapeFun n}
    {A a : Term} {x : Shape n}
    (ihlift : ∀ {u v : Shape n}, (u.lift k).LE Δ (v.lift k) ↔ u.LE Δ v)
    (hwf : f.WF Δ A oB (@Shape.WF Δ _)) (hco : f.Compat Shape.Compat Δ A f)
    (hwx : x.WF Δ) {c' : Shape k}
    (H : Eval Δ (Shape.LE Δ) (ShapeFun.lift (Shape.lift k) f) A a (x.lift k) c') :
    ∃ c, c'.LE Δ (c.lift k) ∧ f.Eval Δ (Shape.LE Δ) A a x c := by
  induction H with
  | bot => exact ⟨.bot, by rw [Shape.lift_bot]; exact .bot, .bot⟩
  | entry e' he' hlab hin =>
    obtain ⟨e, he, rfl⟩ := mem_lift.1 he'
    refine ⟨e.out, ?_, .entry e he hlab (ihlift.1 hin)⟩
    exact .refl ((Shape.lift_wf h).2 (hwf.1 e he).2.2.2.forget)
  | lower hle _ ih =>
    have ⟨c, hc, hev⟩ := ih
    exact ⟨c, hle.trans hΔ hc, hev⟩
  | join _ _ _ ih₁ ih₂ =>
    have ⟨c₁, hc₁, hev₁⟩ := ih₁
    have ⟨c₂, hc₂, hev₂⟩ := ih₂
    have houts : ∀ e ∈ f, Shape.WF Δ e.out := fun e he => (hwf.1 e he).2.2.2.forget
    have hcc : Shape.Compat Δ c₁ c₂ := compat hΔ hco hwx.coherent hev₁ hev₂
    have hw₁ := wf hΔ houts hev₁
    have hw₂ := wf hΔ houts hev₂
    have ⟨hu₁, hu₂⟩ := Shape.le_join hΔ hw₁ hw₂ hcc
    refine ⟨c₁.join c₂, ?_, .join hcc hev₁ hev₂⟩
    exact Shape.join_le hΔ (hc₁.trans hΔ (ihlift.2 hu₁)) (hc₂.trans hΔ (ihlift.2 hu₂))

/-- Lifting *up* is an order embedding.  This is what makes the level
index invisible to `TShape.LE`: `popl27`'s `lift_le_lift`, and the reason
its proof is a plain induction here rather than a `simp` over a `Bool`
function is that the order is `Prop`-valued. -/
theorem Shape.lift_le_lift (hΓ : ⊢ Γ) {n m} (h : n ≤ m) {s t : Shape n} :
    (s.lift m).LE Γ (t.lift m) ↔ s.LE Γ t := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rw [lift_self, lift_self]
    | succ m => cases s <;> cases t <;> rfl
  | succ n ih
  let m+1 := m; have h' := Nat.le_of_succ_le_succ h
  have hwfiff {Ty : Term} {oB : Option Term} {f : ShapeFun n} :
      ShapeFun.WF Γ Ty oB (@WF Γ _) (ShapeFun.lift (lift m) f) ↔
      f.WF Γ Ty oB (@WF Γ _) := by
    refine and_congr ?_ (ShapeFun.lift_compat h')
    constructor
    · intro H e he
      have ⟨hty, htm, hin, hout⟩ :=
        H ⟨e.tm, e.inp.lift m, e.out.lift m⟩ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)
      exact ⟨hty, htm, (lift_wf h').1 hin, (lift_wf h').1 hout⟩
    · intro H e' he'
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he'
      have ⟨hty, htm, hin, hout⟩ := H e he
      exact ⟨hty, htm, (lift_wf h').2 hin, (lift_wf h').2 hout⟩
  -- `←` is `Eval.lift`, `→` is `Eval.lift_of` followed by `Eval.lower`.
  -- The well-formedness both of those want is not a hypothesis of this
  -- lemma: the order on graphs carries it, so `H` supplies it itself.
  have ihf {Ty : Term} {f f' : ShapeFun n} :
      ShapeFun.LE Γ (LE Γ) (@WF Γ _) Ty (ShapeFun.lift (lift m) f)
        (ShapeFun.lift (lift m) f') ↔
      f.LE Γ (LE Γ) (@WF Γ _) Ty f' := by
    refine ⟨fun H => ⟨fun e he => ?_, hwfiff.1 H.2.1, hwfiff.1 H.2.2⟩,
      fun H => ⟨fun e' he' => ?_, hwfiff.2 H.2.1, hwfiff.2 H.2.2⟩⟩
    · have hlk := H.1 ⟨e.tm, e.inp.lift m, e.out.lift m⟩ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)
      have hwf' := hwfiff.1 H.2.2
      have hwe := (hwfiff.1 H.2.1).1 e he
      have ⟨c, hc, hev⟩ := ShapeFun.Eval.lift_of hΓ h' (ih h') hwf' hwf'.2 hwe.2.2.1 hlk
      exact .lower ((ih h').1 hc) hev
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he'
      exact ShapeFun.Eval.lift h' (ih h').2 (H.1 e he)
  have hnil {f : ShapeFun n} : ShapeFun.lift (lift m) f ≠ [] ↔ f ≠ [] := by
    cases f <;> simp [ShapeFun.lift]
  have hnb {f : ShapeFun n} :
      (∀ e ∈ ShapeFun.lift (lift m) f, ¬ e.out.IsBot) ↔ (∀ e ∈ f, ¬ e.out.IsBot) := by
    constructor
    · intro H e he hb
      exact H _ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩) ((lift_isBot h').2 hb)
    · intro H e'' he'' hb
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
      exact H e he ((lift_isBot h').1 hb)
  cases s <;> cases t <;> (try rfl)
  · exact and_congr .rfl (and_congr (ih h') (and_congr ihf
      (and_congr (lift_wf h') (ShapeFun.codeCanonS_lift_iff h'))))
  · exact and_congr ihf (and_congr hnil (and_congr hnb .rfl))
  · exact and_congr .rfl (and_congr (ih h') (and_congr ihf
      (and_congr (lift_wf h') (ShapeFun.codeCanonS_lift_iff h'))))
  · exact and_congr (ih h') (and_congr (ih h')
      (and_congr (not_congr (and_congr (lift_isBot h') (lift_isBot h')))
        (and_congr .rfl .rfl)))
  · exact ih h'

/-- Lifting *preserves* the order, with no hypothesis on the context.

Split off from `lift_le_lift` deliberately.  Only the reflection direction
needs `⊢ Γ` — through `Eval.lift_of`, which uses `Eval.compat` and
`le_join` — and reflection is the minority use (a `TShape.LE` is *read* at
a higher level far more often than it is *built* from one).  Keeping
preservation hypothesis-free is what stops `⊢ Δ` from spreading to every
site that mentions the order, `Interp.sort'` among them. -/
theorem Shape.lift_le {n m} (h : n ≤ m) {s t : Shape n} (H : s.LE Γ t) :
    (s.lift m).LE Γ (t.lift m) := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rwa [lift_self, lift_self]
    | succ m => cases s <;> cases t <;> first | exact H | trivial
  | succ n ih
  let m+1 := m; have h' := Nat.le_of_succ_le_succ h
  have hwf {Ty : Term} {oB : Option Term} {f : ShapeFun n}
      (H : f.WF Γ Ty oB (@WF Γ _)) :
      ShapeFun.WF Γ Ty oB (@WF Γ _) (ShapeFun.lift (lift m) f) := by
    refine ⟨fun e' he' => ?_, (ShapeFun.lift_compat h').2 H.2⟩
    obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he'
    have ⟨hty, htm, hin, hout⟩ := H.1 e he
    exact ⟨hty, htm, (lift_wf h').2 hin, (lift_wf h').2 hout⟩
  have hfun {Ty : Term} {f f' : ShapeFun n}
      (H : f.LE Γ (LE Γ) (@WF Γ _) Ty f') :
      ShapeFun.LE Γ (LE Γ) (@WF Γ _) Ty (ShapeFun.lift (lift m) f)
        (ShapeFun.lift (lift m) f') := by
    refine ⟨fun e' he' => ?_, hwf H.2.1, hwf H.2.2⟩
    obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he'
    exact ShapeFun.Eval.lift h' (ih h') (H.1 e he)
  have hnil {f : ShapeFun n} (H : f ≠ []) : ShapeFun.lift (lift m) f ≠ [] := by
    cases f <;> simp_all [ShapeFun.lift]
  have hnb {f : ShapeFun n} (H : ∀ e ∈ f, ¬ e.out.IsBot) :
      ∀ e ∈ ShapeFun.lift (lift m) f, ¬ e.out.IsBot := by
    intro e'' he'' hb
    obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
    exact H e he ((lift_isBot h').1 hb)
  cases s <;> cases t <;> first
    | exact H
    | trivial
    | exact ih h' H
    | exact ⟨hfun H.1, hnil H.2.1, hnb H.2.2.1, H.2.2.2.1, H.2.2.2.2⟩
    | exact ⟨H.1, ih h' H.2.1, hfun H.2.2.1, (Shape.lift_wf h').2 H.2.2.2.1,
        (ShapeFun.codeCanonS_lift_iff h').2 H.2.2.2.2⟩
    | exact ⟨ih h' H.1, ih h' H.2.1, fun hbb =>
        H.2.2.1 ⟨(lift_isBot h').1 hbb.1, (lift_isBot h').1 hbb.2⟩,
        H.2.2.2.1, H.2.2.2.2⟩

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
    (h : a.LE Δ b) : (a.2.lift k).LE Δ (b.2.lift k) := by
  rw [show a.2.lift k = (a.2.lift (max a.1 b.1)).lift k from
        (Shape.lift_lift (Nat.le_max_left ..)).symm,
      show b.2.lift k = (b.2.lift (max a.1 b.1)).lift k from
        (Shape.lift_lift (Nat.le_max_right ..)).symm]
  exact Shape.lift_le (Nat.max_le.2 ⟨h1, h2⟩) h

theorem LE.def {Δ : List Term} (hΔ : ⊢ Δ) {a b : TShape} {k} (h1 : a.1 ≤ k) (h2 : b.1 ≤ k) :
    a.LE Δ b ↔ (a.2.lift k).LE Δ (b.2.lift k) := by
  rw [show a.2.lift k = (a.2.lift (max a.1 b.1)).lift k from
        (Shape.lift_lift (Nat.le_max_left ..)).symm,
      show b.2.lift k = (b.2.lift (max a.1 b.1)).lift k from
        (Shape.lift_lift (Nat.le_max_right ..)).symm,
      Shape.lift_le_lift hΔ (Nat.max_le.2 ⟨h1, h2⟩)]
  exact .rfl

theorem WF.def {Δ : List Term} {a : TShape} {o} {k} (h : a.1 ≤ k) :
    a.WF Δ o ↔ (a.2.lift k).WF Δ o := (Shape.lift_wf h).symm

theorem Compat.def {Δ : List Term} {a b : TShape} {k} (h1 : a.1 ≤ k) (h2 : b.1 ≤ k) :
    a.Compat Δ b ↔ (a.2.lift k).Compat Δ (b.2.lift k) := by
  rw [show a.2.lift k = (a.2.lift (max a.1 b.1)).lift k from
        (Shape.lift_lift (Nat.le_max_left ..)).symm,
      show b.2.lift k = (b.2.lift (max a.1 b.1)).lift k from
        (Shape.lift_lift (Nat.le_max_right ..)).symm,
      Shape.lift_compat (Nat.max_le.2 ⟨h1, h2⟩)]
  exact .rfl

theorem join.def {a b : TShape} {k} (h1 : a.1 ≤ k) (h2 : b.1 ≤ k) :
    (a.join b).2.lift k = (a.2.lift k).join (b.2.lift k) := by
  rw [show a.2.lift k = (a.2.lift (max a.1 b.1)).lift k from
        (Shape.lift_lift (Nat.le_max_left ..)).symm,
      show b.2.lift k = (b.2.lift (max a.1 b.1)).lift k from
        (Shape.lift_lift (Nat.le_max_right ..)).symm,
      Shape.lift_join (Nat.max_le.2 ⟨h1, h2⟩)]
  rfl

nonrec theorem LE.refl {Δ : List Term} {a : TShape} (h : a.WF Δ) : a.LE Δ a :=
  .refl ((Shape.lift_wf (Nat.le_max_left ..)).2 h)

theorem LE.trans {Δ : List Term} (hΔ : ⊢ Δ) {a b c : TShape}
    (h1 : a.LE Δ b) (h2 : b.LE Δ c) : a.LE Δ c := by
  have ha : a.1 ≤ max (max a.1 b.1) c.1 :=
    Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..)
  have hb : b.1 ≤ max (max a.1 b.1) c.1 :=
    Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..)
  have hc : c.1 ≤ max (max a.1 b.1) c.1 := Nat.le_max_right ..
  exact (LE.def hΔ ha hc).2 ((def_mp ha hb h1).trans hΔ (def_mp hb hc h2))

theorem LE.T {Δ : List Term} {n} {s t : Shape n} :
    LE Δ (Shape.T s) (Shape.T t) ↔ Shape.LE Δ s t := by
  show (s.lift (max n n)).LE Δ (t.lift (max n n)) ↔ _
  rw [Nat.max_self, Shape.lift_self, Shape.lift_self]

theorem WF.T {Δ : List Term} {n} {s : Shape n} {o} :
    WF Δ (Shape.T s) o ↔ Shape.WF Δ s o := Iff.rfl

theorem Compat.T {Δ : List Term} {n} {s t : Shape n} :
    Compat Δ (Shape.T s) (Shape.T t) ↔ Shape.Compat Δ s t := by
  refine (Compat.def n.le_refl n.le_refl).trans ?_
  rw [Shape.lift_self, Shape.lift_self]

theorem join_T {n} {s t : Shape n} :
    s.T.join t.T = (s.join t).T := by
  show (⟨max n n, (s.lift (max n n)).join (t.lift (max n n))⟩ : TShape) = _
  rw [Nat.max_self, Shape.lift_self, Shape.lift_self]

end TShape

/-- Anything below an information-free shape is information-free.  The
`TShape` form of `Shape.le_bot_iff`, needed because `Interp`'s `bot` rule
is indexed by a level. -/
theorem TShape.le_bot {Δ : List Term} (hΔ : ⊢ Δ) {a b : TShape} (hb : b.2 = .bot)
    (h : a.LE Δ b) : a.2 = .bot := by
  have hk : a.1 ≤ max a.1 b.1 := Nat.le_max_left ..
  have h' := LE.def_mp (Nat.le_max_left ..) (Nat.le_max_right ..) h
  rw [hb, Shape.lift_bot,
    show (Shape.bot : Shape (max a.1 b.1)) = (Shape.bot : Shape a.1).lift _ from
      Shape.lift_bot.symm] at h'
  exact Shape.le_bot_iff.1 ((Shape.lift_le_lift hΔ hk).1 h')

/-- `⊥` at any level is below everything.  The companion of
`TShape.le_bot`, for the same reason: `Interp`'s `bot` rule is indexed by
a level, so its witness is not literally `TShape.bot`. -/
theorem TShape.bot_le' {Δ : List Term} {a b : TShape} (ha : a.2 = .bot) :
    a.LE Δ b := by
  show (a.2.lift (max a.1 b.1)).LE Δ _
  rw [ha, Shape.lift_bot]
  exact .bot

@[simp] theorem TShape.subst_T {n} {s : Shape n} {τ : Subst} :
    s.T.subst τ = (s.subst τ).T := rfl

theorem TShape.LE.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {a b : TShape} (h : a.LE Δ b) :
    (a.subst τ).LE Θ (b.subst τ) := by
  refine (LE.def hΘ (Nat.le_max_left ..) (Nat.le_max_right ..)).2 ?_
  show ((a.2.subst τ).lift (max a.1 b.1)).LE Θ
    ((b.2.subst τ).lift (max a.1 b.1))
  rw [Shape.lift_subst, Shape.lift_subst]
  exact (def_mp (Nat.le_max_left ..) (Nat.le_max_right ..) h).subst hΘ W

nonrec theorem TShape.WF.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {a : TShape} {o} (h : a.WF Δ o) :
    (a.subst τ).WF Θ (o.map (·.subst τ)) := h.subst hΘ W

/-- The join of two information-free shapes is information-free. -/
theorem TShape.join_eq_bot {a b : TShape} (ha : a.2 = .bot) (hb : b.2 = .bot) :
    (a.join b).2 = .bot := by
  show (a.2.lift (max a.1 b.1)).join (b.2.lift (max a.1 b.1)) = .bot
  rw [ha, hb]
  simp only [Shape.lift_bot]
  cases max a.1 b.1 <;> rfl

/-- Joining with `⊥`, at the shape level. -/
@[simp] theorem Shape.bot_join {n} {s : Shape n} : (bot (n := n)).join s = s := by
  cases n <;> cases s <;> rfl

@[simp] theorem Shape.join_bot {n} {s : Shape n} : s.join (bot (n := n)) = s := by
  cases n <;> cases s <;> rfl

theorem TShape.LE.succ_of {Δ : List Term} (hΔ : ⊢ Δ) {a b : TShape} (h : a.LE Δ b) :
    LE Δ (Shape.T (n := a.1+1) (ShapeS.succ a.2))
      (Shape.T (n := b.1+1) (ShapeS.succ b.2)) := by
  refine (LE.def hΔ (k := max a.1 b.1 + 1) ?_ ?_).2 h
  · exact Nat.succ_le_succ (Nat.le_max_left ..)
  · exact Nat.succ_le_succ (Nat.le_max_right ..)

theorem TShape.LE.refl_of {Δ : List Term} (hΔ : ⊢ Δ) {j k : Nat} :
    LE Δ (Shape.T (n := j+1) (ShapeS.refl)) (Shape.T (n := k+1) (ShapeS.refl)) := by
  refine (LE.def hΔ (k := max j k + 1) ?_ ?_).2 trivial
  · exact Nat.succ_le_succ (Nat.le_max_left ..)
  · exact Nat.succ_le_succ (Nat.le_max_right ..)

nonrec theorem TShape.Compat.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {a b : TShape} (h : a.Compat Δ b) :
    (a.subst τ).Compat Θ (b.subst τ) := by
  show ((a.2.subst τ).lift (max a.1 b.1)).Compat Θ
    ((b.2.subst τ).lift (max a.1 b.1))
  rw [Shape.lift_subst, Shape.lift_subst]
  exact h.subst hΘ W

/-- Substitution is levelwise, so it passes through the join's `lift`s. -/
theorem TShape.join_subst {τ : Subst} {a b : TShape} :
    (a.join b).subst τ = (a.subst τ).join (b.subst τ) := by
  show (⟨max a.1 b.1, ((a.2.lift (max a.1 b.1)).join (b.2.lift (max a.1 b.1))).subst τ⟩
    : TShape) = ⟨max a.1 b.1, _⟩
  rw [Shape.join_subst, ← Shape.lift_subst, ← Shape.lift_subst]
  rfl

/-- The **label-only Π shape**: intgrah's `piAtom`.  A Π-shape with
no information in it but the syntactic pair.  It is the probe that reads a
label back out of a Π type, and the reason is the order: a `piAtom` is
below `forallE A B d f` exactly when the labels are definitionally equal,
because the other two components of the clause are discharged by `⊥ ≤ d`
and `[] ≤ f`. -/
abbrev Shape.piAtom {n} (A B : Term) : Shape (n+1) := ShapeS.forallE A B .bot []

theorem Shape.piAtom_le_forallE {Δ : List Term} {n} {A B A' B' : Term}
    {d : Shape n} {f : ShapeFun n}
    (h : (piAtom A B).LE Δ (.forallE A' B' d f : Shape (n+1))) :
    PiLabelEq Δ A B A' B' := h.1

@[simp] theorem Shape.lift_piAtom {n m} {A B : Term} :
    (piAtom (n := n) A B).lift (m+1) = .piAtom A B := by
  show ShapeS.forallE .. = _
  rw [lift_bot]; rfl

theorem Shape.WF.piAtom {Δ : List Term} {n} {A B : Term} {u v}
    (hA : Δ ⊢ A : .sort u) (hB : A :: Δ ⊢ B : .sort v) :
    (Shape.piAtom (n := n) A B).WF Δ := by
  refine ⟨⟨u, hA⟩, ⟨v, hB⟩, ?_, ⟨?_, ?_⟩, ?_⟩ <;> first
    | trivial
    | (cases n <;> trivial)
    | (intro e he; cases he)
    | (intro e he _ he' _ _ _ _ _ _; cases he)

/-- The label-only Σ shape, the same probe for Σ types. -/
abbrev Shape.sigmaAtom {n} (A B : Term) : Shape (n+1) := ShapeS.sigma A B .bot []

theorem Shape.sigmaAtom_le_sigma {Δ : List Term} {n} {A B A' B' : Term}
    {d : Shape n} {f : ShapeFun n}
    (h : (sigmaAtom A B).LE Δ (.sigma A' B' d f : Shape (n+1))) :
    PiLabelEq Δ A B A' B' := h.1

@[simp] theorem Shape.lift_sigmaAtom {n m} {A B : Term} :
    (sigmaAtom (n := n) A B).lift (m+1) = .sigmaAtom A B := by
  show ShapeS.sigma .. = _
  rw [lift_bot]; rfl

theorem Shape.WF.sigmaAtom {Δ : List Term} {n} {A B : Term} {u v}
    (hA : Δ ⊢ A : .sort u) (hB : A :: Δ ⊢ B : .sort v) :
    (Shape.sigmaAtom (n := n) A B).WF Δ := by
  refine ⟨⟨u, hA⟩, ⟨v, hB⟩, ?_, ⟨?_, ?_⟩, ?_⟩ <;> first
    | trivial
    | (cases n <;> trivial)
    | (intro e he; cases he)
    | (intro e he _ he' _ _ _ _ _ _; cases he)

/-- `⊥` is well formed at every level. -/
@[simp] theorem TShape.WF.bot {Δ : List Term} {n} {o} :
    (Shape.T (n := n) .bot).WF Δ o := by cases n <;> trivial

/-- The instance of a type family at two equal arguments. -/
theorem TyEq.inst {Δ : List Term} (hΔ : ⊢ Δ) {A B B' a a' : Term} {u v : Bool}
    (hA : Δ ⊢ A : .sort u) (hB : A :: Δ ⊢ B ≡ B' : .sort v) (ha : Δ ⊢ a ≡ a' : A) :
    TyEq Δ (B.inst a) (B'.inst a') :=
  ⟨v, hA.instDF hΔ .sort hB ha⟩

/-- The same with the codomain equation packaged, so the level stays
hidden. -/
theorem TyEq.inst' {Δ : List Term} (hΔ : ⊢ Δ) {A B B' a a' : Term} {u : Bool}
    (hA : Δ ⊢ A : .sort u) (hB : TyEq (A :: Δ) B B') (ha : Δ ⊢ a ≡ a' : A) :
    TyEq Δ (B.inst a) (B'.inst a') :=
  match hB with
  | ⟨_, hB⟩ => .inst hΔ hA hB ha

/-- A sort-shaped code names a sort, at every level. -/
theorem TShape.WF.sort_iff {Δ : List Term} {T : Term} {k} {j : Bool} :
    (Shape.T (n := k) (.sort j)).WF Δ T ↔ TyEq Δ T (.sort j) := by
  cases k <;> exact .rfl

/-- The total-level conversion. -/
nonrec theorem TShape.WF.conv {Δ : List Term} {T T' : Term} {x : TShape}
    (h : x.WF Δ T) (hT : TyEq Δ T' T) : x.WF Δ T' :=
  h.conv hT

/-! ## The join at the total level

The four facts directedness needs, lifted from `Shape` to `TShape`.  Each
is the level-`n` statement sandwiched between two uses of the `def` lemma
that replaces the canonical level by a common one. -/

namespace TShape

theorem join_le {Δ : List Term} (hΔ : ⊢ Δ) {x y w : TShape}
    (h₁ : x.LE Δ w) (h₂ : y.LE Δ w) : (x.join y).LE Δ w := by
  have hx : x.1 ≤ max (max x.1 y.1) w.1 :=
    Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..)
  have hy : y.1 ≤ max (max x.1 y.1) w.1 :=
    Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..)
  have hw : w.1 ≤ max (max x.1 y.1) w.1 := Nat.le_max_right ..
  refine (LE.def hΔ (Nat.max_le.2 ⟨hx, hy⟩) hw).2 ?_
  rw [join.def hx hy]
  exact Shape.join_le hΔ ((LE.def_mp hx hw) h₁) ((LE.def_mp hy hw) h₂)

theorem le_join {Δ : List Term} (hΔ : ⊢ Δ) {x y : TShape}
    (hx : x.WF Δ) (hy : y.WF Δ) (hc : x.Compat Δ y) :
    x.LE Δ (x.join y) ∧ y.LE Δ (x.join y) := by
  have h₁ : x.1 ≤ max x.1 y.1 := Nat.le_max_left ..
  have h₂ : y.1 ≤ max x.1 y.1 := Nat.le_max_right ..
  have hj : (x.join y).1 ≤ max x.1 y.1 := Nat.le_refl _
  have hjx := Shape.le_join hΔ ((WF.def h₁).1 hx) ((WF.def h₂).1 hy) ((Compat.def h₁ h₂).1 hc)
  rw [← join.def h₁ h₂] at hjx
  exact ⟨(LE.def hΔ h₁ hj).2 hjx.1, (LE.def hΔ h₂ hj).2 hjx.2⟩

theorem Compat.of_common_upper {Δ : List Term} (hΔ : ⊢ Δ) {a b c : TShape}
    (hc : c.WF Δ) (h₁ : a.LE Δ c) (h₂ : b.LE Δ c) :
    a.Compat Δ b := by
  have ha : a.1 ≤ max (max a.1 b.1) c.1 :=
    Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..)
  have hb : b.1 ≤ max (max a.1 b.1) c.1 :=
    Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..)
  have hcc : c.1 ≤ max (max a.1 b.1) c.1 := Nat.le_max_right ..
  refine (Compat.def ha hb).2 <| .of_common_upper hΔ ?_ (LE.def_mp ha hcc h₁) (LE.def_mp hb hcc h₂)
  exact ((WF.def hcc).1 hc).coherent

@[simp] theorem Compat.bot_left {Δ : List Term} {n} {b : TShape} :
    (Shape.T (n := n) .bot).Compat Δ b := by
  refine (Compat.def (Nat.le_max_left ..) (Nat.le_max_right ..)).2 ?_
  rw [show (Shape.T (n := n) Shape.bot).2.lift _ = Shape.bot from Shape.lift_bot]
  exact .bot_left

@[simp] theorem Compat.bot_right {Δ : List Term} {n} {a : TShape} :
    a.Compat Δ (Shape.T (n := n) .bot) := by
  refine (Compat.def (Nat.le_max_left ..) (Nat.le_max_right ..)).2 ?_
  rw [show (Shape.T (n := n) Shape.bot).2.lift _ = Shape.bot from Shape.lift_bot]
  exact .bot_right

theorem Compat.symm {Δ : List Term} (hΔ : ⊢ Δ) {a b : TShape}
    (h : a.Compat Δ b) : b.Compat Δ a :=
  (Compat.def (k := max a.1 b.1) (Nat.le_max_right ..) (Nat.le_max_left ..)).2 <|
    ((Compat.def (Nat.le_max_left ..) (Nat.le_max_right ..)).1 h).symm hΔ

/-- Compatibility is anti-monotone on the right: `TShape.Compat.anti_right`
is `Shape.Compat.anti_right` at a level above all three. -/
theorem Compat.anti_right {Δ : List Term} (hΔ : ⊢ Δ) {a b b' : TShape}
    (h : a.Compat Δ b) (hb : b'.LE Δ b) : a.Compat Δ b' := by
  have ha : a.1 ≤ max (max a.1 b.1) b'.1 :=
    Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..)
  have hbk : b.1 ≤ max (max a.1 b.1) b'.1 :=
    Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..)
  have hb'k : b'.1 ≤ max (max a.1 b.1) b'.1 := Nat.le_max_right ..
  exact (Compat.def ha hb'k).2 <| ((Compat.def ha hbk).1 h).anti_right hΔ (LE.def_mp hb'k hbk hb)

/-- The join of two shapes compatible with `d` is compatible with `d`. -/
theorem Compat.join {Δ : List Term} (hΔ : ⊢ Δ) {y z d : TShape}
    (hy : y.Compat Δ d) (hz : z.Compat Δ d) :
    (y.join z).Compat Δ d := by
  have h₁ : y.1 ≤ max (max y.1 z.1) d.1 :=
    Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..)
  have h₂ : z.1 ≤ max (max y.1 z.1) d.1 :=
    Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..)
  have hd : d.1 ≤ max (max y.1 z.1) d.1 := Nat.le_max_right ..
  refine (Compat.def (Nat.max_le.2 ⟨h₁, h₂⟩) hd).2 ?_
  rw [TShape.join.def h₁ h₂]
  exact ((Compat.def h₁ hd).1 hy).join hΔ ((Compat.def h₂ hd).1 hz)

theorem WF.join {Δ : List Term} (hΔ : ⊢ Δ) {y z : TShape} {o}
    (hc : y.Compat Δ z) (hy : y.WF Δ o) (hz : z.WF Δ o) :
    (y.join z).WF Δ o := by
  have h₁ : y.1 ≤ max y.1 z.1 := Nat.le_max_left ..
  have h₂ : z.1 ≤ max y.1 z.1 := Nat.le_max_right ..
  show ((y.2.lift (max y.1 z.1)).join (z.2.lift (max y.1 z.1))).WF Δ o
  exact ((WF.def h₁).1 hy).join_mem hΔ ((Compat.def h₁ h₂).1 hc) ((WF.def h₂).1 hz)

end TShape

/-- The total-level order. -/
theorem TShape.WF.mono {Δ : List Term} (hΔ : ⊢ Δ) {T : Term} {x x' : TShape}
    (hle : x'.LE Δ x) (hC : x.WF Δ T) :
    x'.WF Δ T := by
  have h := hle.def_mp (x'.1.le_max_left x.1) (x'.1.le_max_right x.1)
  rw [TShape.WF.def (Nat.le_max_right x'.1 x.1)] at hC
  rw [TShape.WF.def (Nat.le_max_left x'.1 x.1)]
  exact hC.mono_mem hΔ h

/-! ## Normalising the level

A shape and its lift are equivalent in the order, so any shape may be
moved to a higher level without changing what it approximates.  This is
what lets a proof put every shape in sight at one level before touching
`HasType`, where the level bookkeeping is done once and for all
(`TShape.HasType.lift_subject` and `lower_subject`; `design.md` §1). -/

namespace TShape

/-- Move a shape up to level `k`. -/
def lift (m : TShape) (k : Nat) : TShape := ⟨k, m.2.lift k⟩

theorem LE.lift_le {Δ : List Term} (hΔ : ⊢ Δ) {m : TShape} {k} (hk : m.1 ≤ k)
    (h : m.WF Δ) : (m.lift k).LE Δ m := by
  refine (TShape.LE.def hΔ (Nat.le_refl _) hk).2 ?_
  show ((m.2.lift k).lift k).LE Δ (m.2.lift k)
  rw [Shape.lift_self]
  exact .refl ((Shape.lift_wf hk).2 h)

theorem LE.le_lift {Δ : List Term} (hΔ : ⊢ Δ) {m : TShape} {k} (hk : m.1 ≤ k)
    (h : m.WF Δ) : m.LE Δ (m.lift k) := by
  refine (TShape.LE.def hΔ hk (Nat.le_refl _)).2 ?_
  show (m.2.lift k).LE Δ ((m.2.lift k).lift k)
  rw [Shape.lift_self]
  exact .refl ((Shape.lift_wf hk).2 h)

end TShape

/-- Anything below `prop` is `⊥` or `prop` itself. -/
theorem Shape.le_prop_cases {Δ : List Term} {n} {x : Shape n}
    (h : x.LE Δ (.sort false)) : x = .bot ∨ x = .sort false := by
  cases n <;> cases x <;> first
    | exact .inl rfl
    | exact absurd h id
    | exact .inr (by rename_i r; cases (h : r = false); rfl)

/-- The same at the total level: below `Prop` there is only `⊥` and `Prop`
itself. -/
theorem TShape.le_prop_cases {Δ : List Term} {b : TShape}
    (h : b.LE Δ (.sort false)) :
    b.2 = .bot ∨ b.2 = .sort false := by
  have h2 := LE.def_mp (k := b.1) (Nat.le_refl _) (Nat.zero_le _) h
  rw [Shape.lift_self] at h2
  exact Shape.le_prop_cases (show b.2.LE Δ (.sort false) from Shape.lift_sort ▸ h2)
