import DomainSemantics.HasType

namespace DomainSemantics

/-- The lookup, over `TShape`: same four rules, level-independent by
construction rather than by a `lift` lemma. -/
inductive TEval (Δ : List Term) {n'} (f : ShapeFun n') (A a : Term) (x : TShape) :
    TShape → Prop where
  | bot : TEval Δ f A a x TShape.bot
  | entry (e : Entry (Shape n')) : e ∈ f → LabelEq Δ e.ty e.tm A a →
    TShape.LE Δ ⟨n', e.inp⟩ x → TEval Δ f A a x ⟨n', e.out⟩
  | lower {y z} : TShape.LE Δ y z → TEval Δ f A a x z → TEval Δ f A a x y
  | join {y z} : TShape.Compat Δ y z → TEval Δ f A a x y → TEval Δ f A a x z →
    TEval Δ f A a x (TShape.join y z)

/-- Positivity probe: typing as a single inductive over `TShape`, with the
`lam` clause carrying a dominating graph at an arbitrary level.  The
codomain witness is a *function* argument, not an `∃` inside the premise. -/
inductive THasType (Δ : List Term) : TShape → TShape → Prop where
  | bot {a} : THasType Δ a TShape.type → THasType Δ TShape.bot a
  | sort {r} : THasType Δ (TShape.sort r) (TShape.sort true)
  | unlift {n k} : n ≤ k → {m : Shape n} → {a : TShape} →
    THasType Δ ⟨k, m.lift k⟩ a → THasType Δ ⟨n, m⟩ a
  | forallE {n} {A B : Term} {d : Shape n} {f : ShapeFun n} {r : Bool} :
    THasType Δ ⟨n, d⟩ TShape.type →
    (∀ e ∈ f, THasType Δ ⟨n, e.out⟩ TShape.type) →
    THasType Δ ⟨n+1, ShapeS.forallE A B d f⟩ (TShape.sort r)
  | lam {n n₀ n'} {g : ShapeFun n} {g₀ : ShapeFun n₀} {f : ShapeFun n'}
      {A B : Term} {d : Shape n'} (cs : Entry (Shape n₀) → Shape n') :
    THasType Δ ⟨n', d⟩ TShape.type →
    (∀ e ∈ f, THasType Δ ⟨n', e.out⟩ TShape.type) →
    TShape.LE Δ ⟨n+1, ShapeS.lam g⟩ ⟨n₀+1, ShapeS.lam g₀⟩ →
    (∀ e ∈ g₀, Shape.WF Δ (cs e)) →
    (∀ e ∈ g₀, TEval Δ f e.ty e.tm ⟨n₀, e.inp⟩ ⟨n', cs e⟩) →
    (∀ e ∈ g₀, THasType Δ ⟨n₀, e.out⟩ ⟨n', cs e⟩) →
    THasType Δ ⟨n+1, ShapeS.lam g⟩ ⟨n'+1, ShapeS.forallE A B d f⟩

end DomainSemantics

namespace DomainSemantics
/-- The payoff: lowering a λ typing is transitivity of the order, full stop. -/
example {Δ : List Term} (hΔ : ⊢ Δ) {n n₀ n' k}
    {g : ShapeFun n} {g' : ShapeFun k} {g₀ : ShapeFun n₀} {f : ShapeFun n'}
    {A B : Term} {d : Shape n'} (cs : Entry (Shape n₀) → Shape n')
    (h1 : THasType Δ ⟨n', d⟩ TShape.type)
    (h2 : ∀ e ∈ f, THasType Δ ⟨n', e.out⟩ TShape.type)
    (hdom : TShape.LE Δ ⟨n+1, ShapeS.lam g⟩ ⟨n₀+1, ShapeS.lam g₀⟩)
    (h4 : ∀ e ∈ g₀, Shape.WF Δ (cs e))
    (h5 : ∀ e ∈ g₀, TEval Δ f e.ty e.tm ⟨n₀, e.inp⟩ ⟨n', cs e⟩)
    (h6 : ∀ e ∈ g₀, THasType Δ ⟨n₀, e.out⟩ ⟨n', cs e⟩)
    (hle : TShape.LE Δ ⟨k+1, ShapeS.lam g'⟩ ⟨n+1, ShapeS.lam g⟩) :
    THasType Δ ⟨k+1, ShapeS.lam g'⟩ ⟨n'+1, ShapeS.forallE A B d f⟩ :=
  .lam cs h1 h2 (hle.trans hΔ hdom) h4 h5 h6
end DomainSemantics
