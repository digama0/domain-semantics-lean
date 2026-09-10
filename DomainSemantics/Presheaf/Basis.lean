import DomainSemantics.Term

/-! # Basis of the syntactic presheaf model: shapes with term labels

This is the elementary counterpart of `Basis/Shape.lean`, `Basis/Order.lean`
and `Basis/UniverseShape.lean` in `intgrah/domain-semantics-lean`.

A **shape** is a finite approximant of a value. The only difference from
the shapes of `Shape.lean` is that function graphs and Π/Id-shapes carry
**syntactic labels**: raw terms of the object language.

* An entry `(A, a, x, y)` of a graph says "applied to the syntactic
  argument `a : A`, if the input is at least `x` then the output is at
  least `y`".
* A Π-shape `pi A B d g` remembers the syntactic pair `(A, B)` it came
  from, together with a semantic domain approximant `d` and a graph `g`
  of semantic codes for the family. The label is what makes Π-injectivity
  a one-liner once soundness is known.
* An Id-shape `id A a b` is a pure label (its inhabitants are all `⊥`).

Shapes are context-free trees, but the **order** `LE Δ` is indexed by a
context `Δ`: labels are compared up to definitional equality in `Δ`.
That is how the quotient constructions of the categorical version
(`Ty`, `Tm`, `Ctx` as quotients by defeq) are replaced by side
conditions. Consequently every "reindexing" lemma carries the typing
hypotheses `⊢ Θ` and `Θ ⊢ τ : Δ` (as `Ctx.SubstEq Θ τ τ Δ`). -/

namespace DomainSemantics.Presheaf

open DomainSemantics

/-! ## Shapes and graphs -/

mutual
/-- Finite approximants of values, with syntactic labels. -/
inductive Shape : Type where
  | bot
  | sort (u : Bool)
  | unit (r : Bool)
  | id (A a b : Term)
  | pi (A B : Term) (dom : Shape) (g : Graph)
  | lam (g : Graph)
/-- A finite graph: a list of entries `(A, a, x, y)`; `(A, a)` is the
syntactic label (a term and its type), `x` the input and `y` the output. -/
inductive Graph : Type where
  | nil
  | cons (A a : Term) (x y : Shape) (g : Graph)
end

namespace Graph

/-- The entries of a graph as a list of tuples `(A, a, x, y)`. -/
def entries : Graph → List (Term × Term × Shape × Shape)
  | .nil => []
  | .cons A a x y g => (A, a, x, y) :: entries g

def append : Graph → Graph → Graph
  | .nil, g' => g'
  | .cons A a x y g, g' => .cons A a x y (append g g')

instance : Append Graph := ⟨append⟩

@[simp] theorem nil_append (g : Graph) : (.nil : Graph) ++ g = g := rfl
@[simp] theorem cons_append (g g' : Graph) :
    (.cons A a x y g : Graph) ++ g' = .cons A a x y (g ++ g') := rfl

@[simp] theorem entries_nil : entries .nil = [] := rfl
@[simp] theorem entries_cons : entries (.cons A a x y g) = (A, a, x, y) :: entries g := rfl

theorem entries_append : ∀ g g' : Graph, (g ++ g').entries = g.entries ++ g'.entries
  | .nil, _ => rfl
  | .cons _ _ _ _ g, g' => by simp [entries_append g g']

/-- The single-entry graph. -/
def single (A a : Term) (x y : Shape) : Graph := .cons A a x y .nil

end Graph

/-! ## Substitution action -/

mutual
def Shape.subst : Shape → Subst → Shape
  | .bot, _ => .bot
  | .sort u, _ => .sort u
  | .unit r, _ => .unit r
  | .id A a b, σ => .id (A.subst σ) (a.subst σ) (b.subst σ)
  | .pi A B d g, σ => .pi (A.subst σ) (B.subst σ.lift) (d.subst σ) (g.subst σ)
  | .lam g, σ => .lam (g.subst σ)
def Graph.subst : Graph → Subst → Graph
  | .nil, _ => .nil
  | .cons A a x y g, σ => .cons (A.subst σ) (a.subst σ) (x.subst σ) (y.subst σ) (g.subst σ)
end

attribute [simp] Shape.subst Graph.subst

mutual
theorem Shape.subst_id : ∀ s : Shape, s.subst .id = s
  | .bot | .sort _ | .unit _ => rfl
  | .id .. => by simp
  | .pi A B d g => by simp [Shape.subst_id d, Graph.subst_id g]
  | .lam g => by simp [Graph.subst_id g]
theorem Graph.subst_id : ∀ g : Graph, g.subst .id = g
  | .nil => rfl
  | .cons A a x y g => by simp [Shape.subst_id x, Shape.subst_id y, Graph.subst_id g]
end

attribute [simp] Shape.subst_id Graph.subst_id

mutual
theorem Shape.subst_subst : ∀ (s : Shape) (σ τ : Subst), (s.subst σ).subst τ = s.subst (σ.comp τ)
  | .bot, _, _ | .sort _, _, _ | .unit _, _, _ => rfl
  | .id .., _, _ => by simp [DomainSemantics.subst_subst]
  | .pi A B d g, σ, τ => by
    simp [DomainSemantics.subst_subst, Subst.comp_lift, Shape.subst_subst d, Graph.subst_subst g]
  | .lam g, σ, τ => by simp [Graph.subst_subst g]
theorem Graph.subst_subst : ∀ (g : Graph) (σ τ : Subst), (g.subst σ).subst τ = g.subst (σ.comp τ)
  | .nil, _, _ => rfl
  | .cons A a x y g, σ, τ => by
    simp [DomainSemantics.subst_subst, Shape.subst_subst x, Shape.subst_subst y, Graph.subst_subst g]
end

theorem Graph.subst_append : ∀ (g g' : Graph) (σ : Subst),
    (g ++ g').subst σ = g.subst σ ++ g'.subst σ
  | .nil, _, _ => rfl
  | .cons _ _ _ _ g, g', σ => by simp [Graph.subst_append g g' σ]

theorem Graph.entries_subst : ∀ (g : Graph) (σ : Subst),
    (g.subst σ).entries =
      g.entries.map fun e => (e.1.subst σ, e.2.1.subst σ, e.2.2.1.subst σ, e.2.2.2.subst σ)
  | .nil, _ => rfl
  | .cons _ _ _ _ g, σ => by simp [Graph.entries_subst g σ]

/-! ## Label equality

Labels are compared up to definitional equality in a context `Δ`. The
syntactic-equality disjunct makes the relation reflexive on ill-typed
labels too, so that `LE Δ` is a preorder on *all* shapes; on well-typed
labels it is subsumed by the defeq disjunct. -/

/-- Equality of term labels `(A, a)` (a term `a` of type `A`) in `Δ`. -/
def LabelEq (Δ : List Term) (A a A' a' : Term) : Prop :=
  (A = A' ∧ a = a') ∨ ((∃ u, Δ ⊢ A ≡ A' : .sort u) ∧ Δ ⊢ a ≡ a' : A)

/-- Equality of Π-labels `(A, B)` in `Δ`. -/
def PiLabelEq (Δ : List Term) (A B A' B' : Term) : Prop :=
  (A = A' ∧ B = B') ∨ ((∃ u, Δ ⊢ A ≡ A' : .sort u) ∧ ∃ v, A :: Δ ⊢ B ≡ B' : .sort v)

/-- Equality of Id-labels `(A, a, b)` in `Δ`. -/
def IdLabelEq (Δ : List Term) (A a b A' a' b' : Term) : Prop :=
  (A = A' ∧ a = a' ∧ b = b') ∨
    ((∃ u, Δ ⊢ A ≡ A' : .sort u) ∧ Δ ⊢ a ≡ a' : A ∧ Δ ⊢ b ≡ b' : A)

namespace LabelEq

theorem refl : LabelEq Δ A a A a := .inl ⟨rfl, rfl⟩

theorem symm : LabelEq Δ A a A' a' → LabelEq Δ A' a' A a
  | .inl ⟨h1, h2⟩ => .inl ⟨h1.symm, h2.symm⟩
  | .inr ⟨⟨u, h1⟩, h2⟩ => .inr ⟨⟨u, h1.symm⟩, h1.defeqDF h2.symm⟩

theorem trans : LabelEq Δ A a A' a' → LabelEq Δ A' a' A'' a'' → LabelEq Δ A a A'' a''
  | .inl ⟨rfl, rfl⟩, h => h
  | h, .inl ⟨rfl, rfl⟩ => h
  | .inr ⟨⟨u, h1⟩, h2⟩, .inr ⟨⟨_, h3⟩, h4⟩ =>
    .inr ⟨⟨u, h1.trans' h3⟩, h2.trans (h1.symm.defeqDF h4)⟩

/-- Labels are stable under typed substitution. -/
theorem subst (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ) :
    LabelEq Δ A a A' a' → LabelEq Θ (A.subst τ) (a.subst τ) (A'.subst τ) (a'.subst τ)
  | .inl ⟨rfl, rfl⟩ => .inl ⟨rfl, rfl⟩
  | .inr ⟨⟨u, h1⟩, h2⟩ => .inr ⟨⟨u, h1.subst hΘ W⟩, h2.subst hΘ W⟩

end LabelEq

namespace PiLabelEq

theorem refl : PiLabelEq Δ A B A B := .inl ⟨rfl, rfl⟩

theorem symm (hΔ : ⊢ Δ) : PiLabelEq Δ A B A' B' → PiLabelEq Δ A' B' A B
  | .inl ⟨h1, h2⟩ => .inl ⟨h1.symm, h2.symm⟩
  | .inr ⟨⟨u, h1⟩, v, h2⟩ => .inr ⟨⟨u, h1.symm⟩, v, (h1.defeqDF_l hΔ h2).symm⟩

theorem trans (hΔ : ⊢ Δ) :
    PiLabelEq Δ A B A' B' → PiLabelEq Δ A' B' A'' B'' → PiLabelEq Δ A B A'' B''
  | .inl ⟨rfl, rfl⟩, h => h
  | h, .inl ⟨rfl, rfl⟩ => h
  | .inr ⟨⟨u, h1⟩, v, h2⟩, .inr ⟨⟨_, h3⟩, _, h4⟩ =>
    .inr ⟨⟨u, h1.trans' h3⟩, v, h2.trans' (h1.symm.defeqDF_l hΔ h4)⟩

theorem subst (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ) :
    PiLabelEq Δ A B A' B' → PiLabelEq Θ (A.subst τ) (B.subst τ.lift) (A'.subst τ) (B'.subst τ.lift)
  | .inl ⟨rfl, rfl⟩ => .inl ⟨rfl, rfl⟩
  | .inr ⟨⟨u, h1⟩, v, h2⟩ =>
    have hA := h1.hasType.1.subst hΘ W
    have hΘA : ⊢ A.subst τ :: Θ := ⟨hΘ, _, hA⟩
    .inr ⟨⟨u, h1.subst hΘ W⟩, v, h2.subst hΘA (W.lift h1.hasType.1 hA)⟩

end PiLabelEq

namespace IdLabelEq

theorem refl : IdLabelEq Δ A a b A a b := .inl ⟨rfl, rfl, rfl⟩

theorem symm : IdLabelEq Δ A a b A' a' b' → IdLabelEq Δ A' a' b' A a b
  | .inl ⟨h1, h2, h3⟩ => .inl ⟨h1.symm, h2.symm, h3.symm⟩
  | .inr ⟨⟨u, h1⟩, h2, h3⟩ => .inr ⟨⟨u, h1.symm⟩, h1.defeqDF h2.symm, h1.defeqDF h3.symm⟩

theorem trans : IdLabelEq Δ A a b A' a' b' → IdLabelEq Δ A' a' b' A'' a'' b'' →
    IdLabelEq Δ A a b A'' a'' b''
  | .inl ⟨rfl, rfl, rfl⟩, h => h
  | h, .inl ⟨rfl, rfl, rfl⟩ => h
  | .inr ⟨⟨u, h1⟩, h2, h3⟩, .inr ⟨⟨_, h4⟩, h5, h6⟩ =>
    .inr ⟨⟨u, h1.trans' h4⟩, h2.trans (h1.symm.defeqDF h5), h3.trans (h1.symm.defeqDF h6)⟩

theorem subst (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ) :
    IdLabelEq Δ A a b A' a' b' →
    IdLabelEq Θ (A.subst τ) (a.subst τ) (b.subst τ) (A'.subst τ) (a'.subst τ) (b'.subst τ)
  | .inl ⟨rfl, rfl, rfl⟩ => .inl ⟨rfl, rfl, rfl⟩
  | .inr ⟨⟨u, h1⟩, h2, h3⟩ => .inr ⟨⟨u, h1.subst hΘ W⟩, h2.subst hΘ W, h3.subst hΘ W⟩

end IdLabelEq

/-! ## The order -/

mutual
/-- Shapes that are "morally `⊥`": `⊥` itself and graphs all of whose
outputs are bottom. -/
inductive IsBottom : Shape → Prop where
  | bot : IsBottom .bot
  | lam : GraphBottom g → IsBottom (.lam g)
inductive GraphBottom : Graph → Prop where
  | nil : GraphBottom .nil
  | cons : IsBottom y → GraphBottom g → GraphBottom (.cons A a x y g)
end

mutual
/-- The approximation order at context `Δ`. Labels are compared up to
defeq in `Δ`; graph order is entrywise coverage (`GraphLE`). -/
inductive LE (Δ : List Term) : Shape → Shape → Prop where
  | collapse : IsBottom a → LE Δ a b
  | sort : LE Δ (.sort u) (.sort u)
  | unit : LE Δ (.unit r) (.unit r)
  | id : IdLabelEq Δ A a b A' a' b' → LE Δ (.id A a b) (.id A' a' b')
  | pi : PiLabelEq Δ A B A' B' → LE Δ d d' → GraphLE Δ g g' → LE Δ (.pi A B d g) (.pi A' B' d' g')
  | lam : GraphLE Δ g g' → LE Δ (.lam g) (.lam g')
/-- `GraphLE Δ g g'`: every entry of `g` is covered by `g'`. -/
inductive GraphLE (Δ : List Term) : Graph → Graph → Prop where
  | nil : GraphLE Δ .nil g'
  | cons : Entry Δ g' A a x y → GraphLE Δ g g' → GraphLE Δ (.cons A a x y g) g'
/-- `Entry Δ g A a x y`: the graph `g` covers the entry `(A, a, x, y)`:
either the output is bottom, or `g` has an entry with a defeq label, a
smaller input and a larger output. -/
inductive Entry (Δ : List Term) : Graph → Term → Term → Shape → Shape → Prop where
  | bottom : IsBottom y → Entry Δ g A a x y
  | head : LabelEq Δ A' a' A a → LE Δ x' x → LE Δ y y' → Entry Δ (.cons A' a' x' y' g) A a x y
  | tail : Entry Δ g A a x y → Entry Δ (.cons A' a' x' y' g) A a x y
end

