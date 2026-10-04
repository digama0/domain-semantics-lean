import DomainSemantics.HasType

/-! # The interpretation relation

`Interp Δ Γ t σ ρ m` says that the shape `m` is a lower bound on an
interpretation of the term `t` at the **stage** `(Δ, σ)`, under the
valuation `ρ`.  It is master's `LE_Interp`, with two changes.

* It carries a stage.  `Γ` is the context the term lives in, `Δ` the
  context the shape's labels live in, and `σ` a substitution from `Γ` to
  `Δ`.  This is the presheaf structure of the other repo, spelled out
  syntactically: the "presheaf over contexts" is the family of relations
  indexed by `(Δ, σ)`, and naturality is the substitution lemma.
* Every binder rule extends the stage with a **label term** as well as the
  valuation with a shape.  For `lam` and `forallE` the label comes from the
  graph entry, which is exactly what the gluing gives us; for `natCase` and
  `Y` it has to be supplied as a premise, together with the definitional
  equation that justifies it.

Reading `m` as a lower bound is what makes the relation monotone
(`Interp.mono`), as in master.  There is no `⊥`-escape anywhere else: the
`bot` constructor covers every term.

Σ mirrors Π throughout.  The `pair` shape carries the syntactic pair
`(A[σ], a[σ])` of its first component, which is what lets the second
component be typed at the codomain family applied there; `fst` and `snd`
read a component off a pair shape exactly as `app` reads an output off a
λ-shape. -/

namespace DomainSemantics

/-! ## Valuations -/

/-- A valuation assigns each de Bruijn index a `TShape`. -/
def Valuation := Nat → TShape

/-- The empty valuation: every index maps to `⊥`. -/
def Valuation.nil : Valuation := fun _ => TShape.bot

/-- Push a new value onto the front of a valuation (under-binder extension). -/
def Valuation.push (ρ : Valuation) (u : TShape) : Valuation
  | 0 => u
  | n+1 => ρ n

/-- Drop the head, for going under a binder in the context. -/
def Valuation.tail (ro : Valuation) : Valuation := fun i => ro (i+1)

/-- Reindex a valuation along a substitution of the stage: the action of
the presheaf on morphisms, which for us is `Shape.subst` slotwise. -/
def Valuation.subst (ro : Valuation) (tau : Subst) : Valuation := fun i => (ro i).subst tau

@[simp] theorem Valuation.tail_push {ro : Valuation} {u} : (ro.push u).tail = ro := rfl

@[simp] theorem Valuation.subst_apply {ro : Valuation} {tau i} :
    ro.subst tau i = (ro i).subst tau := rfl

@[simp] theorem Valuation.subst_push {ro : Valuation} {tau u} :
    (ro.push u).subst tau = (ro.subst tau).push (u.subst tau) := by
  funext i; cases i <;> rfl

/-- Pointwise order on valuations, at a stage. -/
def Valuation.LE (Δ : List Term) (ρ ρ' : Valuation) : Prop := ∀ i, TShape.LE Δ (ρ i) (ρ' i)

/-- Pointwise well-formedness. -/
def Valuation.WF (Δ : List Term) (ρ : Valuation) : Prop := ∀ i, TShape.WF Δ (ρ i)

theorem Valuation.LE.refl {Δ : List Term} {ρ : Valuation} (h : ρ.WF Δ) : ρ.LE Δ ρ :=
  fun i => TShape.LE.refl (h i)

theorem Valuation.LE.trans {Δ : List Term} (hΔ : ⊢ Δ) {ρ ρ' ρ'' : Valuation}
    (h : ρ.LE Δ ρ') (h' : ρ'.LE Δ ρ'') : ρ.LE Δ ρ'' :=
  fun i => TShape.LE.trans hΔ (h i) (h' i)

@[simp] theorem Valuation.push_zero {ρ : Valuation} {u} : (ρ.push u) 0 = u := rfl
@[simp] theorem Valuation.push_succ {ρ : Valuation} {u i} : (ρ.push u) (i+1) = ρ i := rfl

theorem Valuation.LE.push {Δ : List Term} {ρ ρ' : Valuation} {u u' : TShape} :
    (ρ.push u).LE Δ (ρ'.push u') ↔ ρ.LE Δ ρ' ∧ TShape.LE Δ u u' :=
  ⟨fun H => ⟨fun _ => H (_+1), H 0⟩, fun ⟨H1, H2⟩ => fun | 0 => H2 | _+1 => H1 _⟩

theorem Valuation.WF.push {Δ : List Term} {ρ : Valuation} {u : TShape}
    (h : ρ.WF Δ) (hu : TShape.WF Δ u) : (ρ.push u).WF Δ
  | 0 => hu
  | _+1 => h _

theorem Valuation.WF.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {ρ : Valuation} (h : ρ.WF Δ) : (ρ.subst τ).WF Θ :=
  fun i => TShape.WF.subst hΘ W (h i)

/-! ## Total-level shapes for the atoms -/

namespace TShape

abbrev unit (r : Bool) : TShape := Shape.T (n := 1) (ShapeS.unit r)
abbrev nat : TShape := Shape.T (n := 1) ShapeS.nat
abbrev zero : TShape := Shape.T (n := 1) ShapeS.zero

end TShape

/-! ## The relation -/

/-- `m` approximates the interpretation of `t` at stage `(Δ, σ)` under `ρ`. -/
inductive Interp (Δ : List Term) : List Term → Term → Subst → Valuation → TShape → Prop where
  /-- `⊥` approximates everything, including the terms Σ is deferred on. -/
  | bot {n} : Interp Δ Γ t σ ρ (Shape.T (n := n) .bot)
  | bvar : TShape.WF Δ m → TShape.LE Δ m (ρ i) → Interp Δ Γ (.bvar i) σ ρ m
  | sort : TShape.WF Δ m → TShape.LE Δ m (.sort r) → Interp Δ Γ (.sort r) σ ρ m
  | unit : TShape.WF Δ m → TShape.LE Δ m (.unit r) → Interp Δ Γ (.unit r) σ ρ m
  -- `star r` has only the `bot` rule: the unit type's inhabitant carries
  -- no information, which is what makes `unit_eta` sound
  | nat : TShape.WF Δ m → TShape.LE Δ m .nat → Interp Δ Γ .nat σ ρ m
  | zero : TShape.WF Δ m → TShape.LE Δ m .zero → Interp Δ Γ .zero σ ρ m
  | succ {n} {v : Shape n} :
    Interp Δ Γ N σ ρ v.T → TShape.WF Δ m →
    TShape.LE Δ m (Shape.T (n := n+1) v.succ) → Interp Δ Γ (.succ N) σ ρ m
  /-- Application is the **graph lookup at the syntactic label**.  The
  argument's type is not recorded by `Term.app`; it is read off the
  function's λ-shape, whose domain label `A` (a term of `Δ`) every entry's
  type agrees with (`Shape.WF`).  The label is `(A, a[σ])`.

  Taking the type from the shape rather than as a free parameter is what
  pins the lookup at every well-formed valuation, admissible or not.
  Naming it in `Δ` rather than in `Γ` is also what makes `Interp.subst` an
  equivalence: a substitution in the term leaves the label's type alone.

  The lookup is `TEvaluates`, over `TShape`s, not the level-indexed
  `Evaluates`: the input and output of a lookup in a *bigger* graph land at
  that graph's level, and the reflection back down does not exist
  (`Evaluates.lift` is one-directional).  Directedness needs exactly that
  move, so the rule is stated where it is available. -/
  | app {n} {g : ShapeFun n} {x y : TShape} {A : Term} :
    Interp Δ Γ F σ ρ (Shape.T (n := n+1) (ShapeS.lam A g)) →
    Interp Δ Γ a σ ρ x →
    TEvaluates Δ g A (a.subst σ) x y →
    TShape.WF Δ m →
    TShape.LE Δ m y →
    -- the label is the argument's type, at the stage: this is what makes the
    -- clause stage-invariant, and the only place the lookup's *type* is pinned
    (∃ A₀, (Γ ⊢ a : A₀) ∧ TyEq Δ A (A₀.subst σ)) →
    Interp Δ Γ (.app F a) σ ρ m
  /-- The binder rule.  The shape is labelled by the domain `A[σ]`, and
  each entry of the graph is a *probe*: a label term `e.tm` at a type
  definitionally equal to the domain (part of `Shape.WF`), an input typed
  at the domain shape (master's `HasDom`, and what makes the extended
  valuation admissible), and the body's interpretation at the stage
  extended by that term.  The premises
  are kept separate rather than conjoined, so that the nested `Interp`
  occurrence stays under `∀` and `→` only and the kernel accepts the
  definition. -/
  | lam {n} {g : ShapeFun n} {d : TShape} {A b : Term} :
    Interp Δ Γ A σ ρ d →
    TShape.HasType Δ d TShape.type →
    Shape.WF Δ (Shape.lam (A.subst σ) g) →
    (∀ e ∈ g, TShape.HasType Δ e.inp.T d) →
    (∀ e ∈ g, Interp Δ (A :: Γ) b (σ.cons e.tm) (ρ.push e.inp.T) e.out.T) →
    TShape.WF Δ m →
    TShape.LE Δ m (Shape.T (n := n+1) (ShapeS.lam (A.subst σ) g)) →
    (∃ u, Γ ⊢ A : .sort u) →
    Interp Δ Γ (.lam A b) σ ρ m
  /-- The Π-shape carries the syntactic pair `(A[σ], B[σ.lift])`.  That
  label is the whole gluing trick: Π-injectivity falls out of soundness by
  projecting it. -/
  | forallE {n} {g : ShapeFun n} {d : Shape n} {A B : Term} :
    Interp Δ Γ A σ ρ (Shape.T d) →
    TShape.HasType Δ (Shape.T d) TShape.type →
    Shape.WF (n := n+1) Δ (.forallE (A.subst σ) (B.subst σ.lift) d g) →
    (∀ e ∈ g, ∃ u, Δ ⊢ e.ty ≡ A.subst σ : .sort u) →
    (∀ e ∈ g, TShape.HasType Δ e.inp.T d.T) →
    (∀ e ∈ g, Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push e.inp.T) e.out.T) →
    TShape.WF Δ m →
    TShape.LE Δ m (Shape.T (n := n+1) (.forallE (A.subst σ) (B.subst σ.lift) d g)) →
    (∃ u, Γ ⊢ A : .sort u) → (∃ v, A :: Γ ⊢ B : .sort v) →
    Interp Δ Γ (.forallE A B) σ ρ m
  /-- Σ, mirroring `forallE` exactly. -/
  | sigma {n} {g : ShapeFun n} {d : Shape n} {A B : Term} :
      Interp Δ Γ A σ ρ (Shape.T d) →
      TShape.HasType Δ (Shape.T d) TShape.type →
      Shape.WF (n := n+1) Δ (ShapeS.sigma (A.subst σ) (B.subst σ.lift) d g) →
      (∀ e ∈ g, ∃ u, Δ ⊢ e.ty ≡ A.subst σ : .sort u) →
      (∀ e ∈ g, TShape.HasType Δ (Shape.T e.inp) (Shape.T d)) →
      (∀ e ∈ g, Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push (Shape.T e.inp)) (Shape.T e.out)) →
      TShape.WF Δ m →
      TShape.LE Δ m
        (Shape.T (n := n+1) (ShapeS.sigma (A.subst σ) (B.subst σ.lift) d g)) →
      (∃ u, Γ ⊢ A : .sort u) → (∃ v, A :: Γ ⊢ B : .sort v) →
      Interp Δ Γ (.sigma A B) σ ρ m
  /-- A pair is its first component together with a **graph**, mirroring
  `lam` (§5.1b).  An entry `(A[σ], a[σ], inp, out)` reads "with at least
  `inp` of the first component, the second is at least `out`", and it is
  the *type* of the second component that makes that conditional: the
  codomain family is read at `inp`, which is why the entry carries the type
  witness `c` — as `tr` carries its motive's.  Without it an entry could
  promise a big second component at a tiny first one, which no typing
  could justify. -/
  | pair {n} {x : Shape n} {g₀ : List (Entry (Shape n) × TShape)} {d : TShape}
      {A B a b : Term} :
      Interp Δ Γ a σ ρ (Shape.T x) →
      Interp Δ Γ A σ ρ d →
      TShape.HasType Δ d TShape.type →
      Shape.WF (n := n+1) Δ (ShapeS.pair (A.subst σ) x (g₀.map (·.1))) →
      (∀ e ∈ g₀, Δ ⊢ e.1.tm ≡ a.subst σ : e.1.ty) →
      (∀ e ∈ g₀, TShape.HasType Δ e.1.inp.T d) →
      (∀ e ∈ g₀, Interp Δ Γ a σ ρ e.1.inp.T) →
      (∀ e ∈ g₀, Interp Δ Γ b σ ρ e.1.out.T) →
      (∀ e ∈ g₀, Interp Δ (A :: Γ) B (σ.cons e.1.tm) (ρ.push e.1.inp.T) e.2) →
      (∀ e ∈ g₀, TShape.HasType Δ e.1.out.T e.2) →
      TShape.WF Δ m →
      TShape.LE Δ m (Shape.T (n := n+1) (ShapeS.pair (A.subst σ) x (g₀.map (·.1)))) →
      (∃ u, Γ ⊢ A : .sort u) → (Γ ⊢ a : A) →
      Interp Δ Γ (.pair A B a b) σ ρ m
  /-- The first projection reads the first component. -/
  | fst {n} {A₀ : Term} {x : Shape n} {g : ShapeFun n} :
      Interp Δ Γ p σ ρ (Shape.T (n := n+1) (ShapeS.pair A₀ x g)) →
      TShape.WF Δ m →
      TShape.LE Δ m (Shape.T x) →
      Interp Δ Γ (.fst p) σ ρ m
  /-- The second projection is a **graph lookup**, as `app` is: at the
  pair's own domain label, at the term `fst p`, and with the first
  component as the input.  Reading it anywhere else would read a second
  component conditional on more of the first than `p` has. -/
  | snd {n} {A₀ : Term} {x : Shape n} {g : ShapeFun n} {y : TShape} :
      Interp Δ Γ p σ ρ (Shape.T (n := n+1) (ShapeS.pair A₀ x g)) →
      TEvaluates Δ g A₀ ((Term.fst p).subst σ) (Shape.T x) y →
      TShape.WF Δ m →
      TShape.LE Δ m y →
      (∃ A₁, (Γ ⊢ Term.fst p : A₁) ∧ TyEq Δ A₀ (A₁.subst σ)) →
      Interp Δ Γ (.snd p) σ ρ m
  /-- The equation is what the `succ` branch also carries, and for the same
  reason: the *type* of a `natCase` is `C[M]`, and the branch's value is
  typed at `C[zero]`, so soundness needs the two stages to be one.  The
  shape `M ↦ zero` is semantic information; only the equation is syntax. -/
  | natCase_zero :
    Interp Δ Γ M σ ρ .zero →
    Δ ⊢ M.subst σ ≡ .zero : .nat →
    Interp Δ Γ a σ ρ m →
    (Γ ⊢ M : Term.nat) →
    Interp Δ Γ (.natCase C M a b) σ ρ m
  /-- There is no syntactic predecessor former, so the label term for the
  body's binder is supplied as a premise, together with the definitional
  equation that makes it the right one. -/
  | natCase_succ {n} {v : Shape n} {t : Term} :
    Interp Δ Γ M σ ρ (Shape.T (n := n+1) v.succ) →
    Shape.WF Δ v →
    Δ ⊢ M.subst σ ≡ .succ t : .nat →
    Interp Δ (.nat :: Γ) b (σ.cons t) (ρ.push v.T) m →
    (Γ ⊢ M : Term.nat) →
    Interp Δ Γ (.natCase C M a b) σ ρ m
  /-- The fixed point is a least fixed point for free: the constructor
  refers to the relation it is defining, so only finitely many unfoldings
  can ever produce a given approximant. -/
  | protected Y {A b : Term} {x : TShape} :
    Interp Δ Γ (.Y A b) σ ρ x →
    TShape.WF Δ x →
    Interp Δ (A :: Γ) b (σ.cons ((A.Y b).subst σ)) (ρ.push x) m →
    (∃ u, Γ ⊢ A : .sort u) → (Γ ⊢ Term.Y A b : A) →
    Interp Δ Γ (.Y A b) σ ρ m
  /-- The identity type is **label-only**: no sub-shapes, so the shape
  records nothing but the syntax. -/
  | id : TShape.WF Δ m →
    TShape.LE Δ m (Shape.T (n := 1) (.id r (A.subst σ) (a.subst σ) (b.subst σ))) →
    (∃ u, Γ ⊢ A : .sort u) → (Γ ⊢ a : A) → (Γ ⊢ b : A) →
    Interp Δ Γ (.id r A a b) σ ρ m
  /-- `refl` has a shape only in the proof-relevant sort; at `r = false`
  the `bot` rule is all there is, which is proof irrelevance. -/
  | refl {n} {v : Shape n} :
    Interp Δ Γ a σ ρ (Shape.T v) →
    TShape.WF Δ m →
    TShape.LE Δ m (Shape.T (n := n+1) (.refl v)) →
    Interp Δ Γ (.refl true a) σ ρ m
  /-- Transport.  Master's constructor, with the motive evaluated at the
  stage extended by `b`, which is the label term the motive's binder is
  instantiated with — **and with the endpoints' equation at the stage**.

  That equation is what the proof-irrelevant identity type needs, and it
  is the one thing an unlabelled model cannot say.  At `r = false` a
  proof has only the `⊥` shape (`HasType.proofIrrel`), so nothing about
  it can license the transport's value; the other repo's answer is that
  the proof never licenses it — `⟦tr A a b C x h⟧ = rawExtend ⟦C[b]⟧ ⟦x⟧`
  is a *coercion*, and its computation rule is **K**: `tr A a b C x h ≡ x`
  as soon as `a ≡ b`, whatever `h` is.  Here `a ≡ b` is a judgment, so the
  clause carries it at the stage, exactly as `natCase_zero` carries
  `M[σ] ≡ zero`.  Without it a *stuck* transport (endpoints not equal at
  the stage) would still be given `X`'s approximants, which no syntactic
  rule can justify: that is the hole left in the old, context-free
  `LE_Interp` (`Adequacy.lean`), and the reason for the labelled redesign.

  At `r = true` the proof is informative and the `refl`-shape premise is
  kept as well; `tr_refl` supplies both. -/
  | tr {v vA m' cb : TShape} {r : Bool} {A a b C X H : Term} :
    TShape.WF Δ m →
    TShape.LE Δ m m' →
    Interp Δ Γ X σ ρ m' →
    Interp Δ Γ a σ ρ v →
    Interp Δ Γ b σ ρ v →
    Interp Δ Γ A σ ρ vA →
    TShape.WF Δ v →
    TShape.HasType Δ v vA →
    Interp Δ (A :: Γ) C (σ.cons (b.subst σ)) (ρ.push v) cb →
    TShape.HasType Δ cb TShape.type →
    TShape.HasType Δ m' cb →
    (r = true → Interp Δ Γ H σ ρ (Shape.T (n := v.1+1) (ShapeS.refl v.2))) →
    Δ ⊢ a.subst σ ≡ b.subst σ : A.subst σ →
    (∃ u, Γ ⊢ A : .sort u) → (Γ ⊢ a : A) → (Γ ⊢ b : A) →
    Interp Δ Γ (.tr r A a b C X H) σ ρ m

/-! ## Monotonicity

Both directions master has: down in the shape, up in the valuation.
Neither touches the stage, so both are the same induction as there. -/

theorem Interp.wf {Δ Γ : List Term} {t : Term} {σ ρ m}
    (H : Interp Δ Γ t σ ρ m) : TShape.WF Δ m := by
  induction H with
  | bot => exact .bot
  | bvar hw | sort hw | unit hw | nat hw | zero hw | succ _ hw
  | app _ _ _ hw | lam _ _ _ _ _ hw | forallE _ _ _ _ _ _ hw | id hw | refl _ hw | tr hw
  | sigma _ _ _ _ _ _ hw | pair _ _ _ _ _ _ _ _ _ _ hw | fst _ hw | snd _ _ hw
  | natCase_zero _ _ _ _ _ hw | natCase_succ _ _ _ _ _ _ hw
  | Y _ _ _ _ _ _ hw => exact hw

theorem Interp.mono (hΔ : ⊢ Δ) {Γ : List Term} {t : Term} {σ ρ} {m m' : TShape}
    (hw : TShape.WF Δ m) (h : TShape.LE Δ m m') (H : Interp Δ Γ t σ ρ m') :
    Interp Δ Γ t σ ρ m := by
  induction H generalizing m with
  | bot =>
    obtain ⟨k, s⟩ := m
    cases show s = .bot from TShape.le_bot hΔ rfl h
    exact .bot
  | bvar _ h1 => exact .bvar hw (TShape.LE.trans hΔ h h1)
  | sort _ h1 => exact .sort hw (TShape.LE.trans hΔ h h1)
  | unit _ h1 => exact .unit hw (TShape.LE.trans hΔ h h1)
  | nat _ h1 => exact .nat hw (TShape.LE.trans hΔ h h1)
  | zero _ h1 => exact .zero hw (TShape.LE.trans hΔ h h1)
  | succ hv _ h1 => exact .succ hv hw (TShape.LE.trans hΔ h h1)
  | app hF ha hev _ h1 hty => exact .app hF ha hev hw (TShape.LE.trans hΔ h h1) hty
  | lam hA hd hwf hdom hbody _ h1 hAt =>
    exact .lam hA hd hwf hdom hbody hw (TShape.LE.trans hΔ h h1) hAt
  | forallE hA hd hwf hlab hdom hbody _ h1 hAt hBt =>
    exact .forallE hA hd hwf hlab hdom hbody hw (TShape.LE.trans hΔ h h1) hAt hBt
  | sigma hA hd hwf hlab hdom hbody _ h1 hAt hBt =>
    exact .sigma hA hd hwf hlab hdom hbody hw (TShape.LE.trans hΔ h h1) hAt hBt
  | pair ha hA hd hwf hlab hdom hinp hout hbody hty _ h1 hAt hat =>
    exact .pair ha hA hd hwf hlab hdom hinp hout hbody hty hw
      (TShape.LE.trans hΔ h h1) hAt hat
  | fst hp _ h1 => exact .fst hp hw (TShape.LE.trans hΔ h h1)
  | snd hp hq _ h1 hty => exact .snd hp hq hw (TShape.LE.trans hΔ h h1) hty
  | natCase_zero hM hz _ hMt _ iha => exact .natCase_zero hM hz (iha hw h) hMt
  | natCase_succ hM hwv heq _ hMt _ ihb => exact .natCase_succ hM hwv heq (ihb hw h) hMt
  | Y hself hwx _ hAt hYt _ ihb => exact .Y hself hwx (ihb hw h) hAt hYt
  | id _ h1 hAt hat hbt => exact .id hw (TShape.LE.trans hΔ h h1) hAt hat hbt
  | refl hv _ h1 => exact .refl hv hw (TShape.LE.trans hΔ h h1)
  | tr _ hle hX ha hb hA hwv hvA hC hcb hm' hH heq hAt hat hbt _ _ _ _ _ _ =>
    exact .tr hw (TShape.LE.trans hΔ h hle) hX ha hb hA hwv hvA hC hcb hm' hH heq
      hAt hat hbt

theorem Interp.mono_val {Γ : List Term} {t : Term} {σ} {ρ ρ' : Valuation} {m : TShape}
    (hΔ : ⊢ Δ) (hρ : ρ.LE Δ ρ') (H : Interp Δ Γ t σ ρ m) : Interp Δ Γ t σ ρ' m := by
  induction H generalizing ρ' with
  | bot => exact .bot
  | bvar hw h1 => exact .bvar hw (h1.trans hΔ (hρ _))
  | sort hw h1 => exact .sort hw h1
  | unit hw h1 => exact .unit hw h1
  | nat hw h1 => exact .nat hw h1
  | zero hw h1 => exact .zero hw h1
  | succ _ hw h1 ihv => exact .succ (ihv hρ) hw h1
  | app _ _ hev hw h1 hty ihF iha => exact .app (ihF hρ) (iha hρ) hev hw h1 hty
  | lam _ hd hwf hdom _ hw h1 hAt ihA ihbody =>
    refine .lam (ihA hρ) hd hwf hdom (fun e he => ?_) hw h1 hAt
    exact ihbody e he (Valuation.LE.push.2 ⟨hρ, .refl (hwf.2.2.1.1 e he).2.2.1⟩)
  | forallE _ hd hwf hlab hdom _ hw h1 hAt hBt ihA ihbody =>
    refine .forallE (ihA hρ) hd hwf hlab hdom (fun e he => ?_) hw h1 hAt hBt
    exact ihbody e he (Valuation.LE.push.2 ⟨hρ, .refl (hwf.2.2.2.1 e he).2.2.1⟩)
  | sigma _ hd hwf hlab hdom _ hw h1 hAt hBt ihA ihbody =>
    exact .sigma (ihA hρ) hd hwf hlab hdom (fun e he => ihbody e he
      (Valuation.LE.push.2 ⟨hρ, TShape.LE.refl (a := Shape.T e.inp)
        (hwf.2.2.2.1 e he).2.2.1⟩)) hw h1 hAt hBt
  | pair _ _ hd hwf hlab hdom _ _ hbody hty hw h1 hAt hat iha ihA ihinp ihout ihbody =>
    exact .pair (iha hρ) (ihA hρ) hd hwf hlab hdom (fun e he => ihinp e he hρ)
      (fun e he => ihout e he hρ)
      (fun e he => ihbody e he (Valuation.LE.push.2 ⟨hρ, TShape.LE.refl
        (a := e.1.inp.T) (hwf.2.2.1.1 _ (List.mem_map.2 ⟨e, he, rfl⟩)).2.2.1⟩)) hty hw h1
      hAt hat
  | fst _ hw h1 ihp => exact .fst (ihp hρ) hw h1
  | snd _ hq hw h1 hty ihp => exact .snd (ihp hρ) hq hw h1 hty
  | natCase_zero _ hz _ hMt ihM iha => exact .natCase_zero (ihM hρ) hz (iha hρ) hMt
  | natCase_succ _ hwv heq _ hMt ihM ihb =>
    refine .natCase_succ (ihM hρ) hwv heq ?_ hMt
    exact ihb (Valuation.LE.push.2 ⟨hρ, .refl (a := Shape.T _) hwv⟩)
  | Y _ hwx _ hAt hYt ihself ihb =>
    exact .Y (ihself hρ) hwx (ihb (Valuation.LE.push.2 ⟨hρ, .refl hwx⟩)) hAt hYt
  | id hw h1 hAt hat hbt => exact .id hw h1 hAt hat hbt
  | refl _ hw h1 ihv => exact .refl (ihv hρ) hw h1
  | tr hw hle _ _ _ _ hwv hvA _ hcb hm' _ heq hAt hat hbt ihX iha ihb ihA ihC ihH =>
    refine .tr hw hle (ihX hρ) (iha hρ) (ihb hρ) (ihA hρ) hwv hvA ?_ hcb hm'
      (fun hr => ihH hr hρ) heq hAt hat hbt
    exact ihC (Valuation.LE.push.2 ⟨hρ, .refl hwv⟩)

/-! ### Changing the context

With the labels' typings in the clauses, an interpretation no longer
reads at *any* context: it reads at any context the typings survive in,
which is any context definitionally equal to this one.  That is all the
binder congruences need — they move a body from `A :: Γ` to `A' :: Γ`
after the domain has changed — and it is what the annotations' typings
buy. -/

theorem IsDefEq.ctx_id {Γ Γ' : List Term} (hΓ' : ⊢ Γ')
    (W : Ctx.SubstEq Γ' Subst.id Subst.id Γ) {e₁ e₂ A : Term}
    (h : Γ ⊢ e₁ ≡ e₂ : A) : Γ' ⊢ e₁ ≡ e₂ : A := by simpa using h.subst hΓ' W

theorem Ctx.SubstEq.id_lift {Γ Γ' : List Term} {A : Term} {u : Bool} (hΓ' : ⊢ Γ')
    (W : Ctx.SubstEq Γ' Subst.id Subst.id Γ) (hA : Γ ⊢ A : .sort u) :
    Ctx.SubstEq (A :: Γ') Subst.id Subst.id (A :: Γ) := by
  have h := W.lift hA (by simpa using IsDefEq.ctx_id hΓ' W hA)
  simpa using h

/-- The context change the binder congruences need: the head has moved
along a definitional equality. -/
theorem Ctx.SubstEq.defeqHead {Γ : List Term} {A A' : Term} {u : Bool} (hΓ : ⊢ Γ)
    (hAA' : Γ ⊢ A ≡ A' : .sort u) : Ctx.SubstEq (A' :: Γ) Subst.id Subst.id (A :: Γ) := by
  refine .cons (Ctx.SubstEq.id hΓ).skip hAA'.hasType.1 ?_
  rw [show A.subst Subst.id.tail = A.lift' (.skip .refl) by
    show A.subst (Subst.id.lift_r (.skip .refl)) = _
    rw [← lift'_subst, subst_id]]
  exact (hAA'.weak' (Ctx.Lift'.skip (A := A') .refl)).symm.defeqDF
    (.bvar Lookup.zero (hAA'.hasType.2.weak' (Ctx.Lift'.skip (A := A') .refl)))

theorem Interp.ctx {Δ Γ : List Term} {t σ ρ m} (H : Interp Δ Γ t σ ρ m) :
    ∀ {Γ' : List Term}, ⊢ Γ' → Ctx.SubstEq Γ' Subst.id Subst.id Γ →
      Interp Δ Γ' t σ ρ m := by
  induction H with
  | bot => exact fun _ _ => .bot
  | bvar hw h => exact fun _ _ => .bvar hw h
  | sort hw h => exact fun _ _ => .sort hw h
  | unit hw h => exact fun _ _ => .unit hw h
  | nat hw h => exact fun _ _ => .nat hw h
  | zero hw h => exact fun _ _ => .zero hw h
  | succ _ hw h ih => exact fun hΓ' W => .succ (ih hΓ' W) hw h
  | app _ _ hev hw h hty ihF iha =>
    intro Γ' hΓ' W
    obtain ⟨A₀, hat, hTy⟩ := hty
    exact .app (ihF hΓ' W) (iha hΓ' W) hev hw h ⟨A₀, IsDefEq.ctx_id hΓ' W hat, hTy⟩
  | @lam _ _ _ _ _ _ _ A _ _ hd hwf hdom _ hw h hAt ihA ihbody =>
    intro Γ' hΓ' W
    obtain ⟨u, hA⟩ := hAt
    have hA' : Γ' ⊢ A ≡ A : Term.sort u := IsDefEq.ctx_id hΓ' W hA
    exact .lam (ihA hΓ' W) hd hwf hdom
      (fun e he => ihbody e he ⟨hΓ', _, hA'⟩ (W.id_lift hΓ' hA)) hw h ⟨u, hA'⟩
  | @forallE _ _ _ _ _ _ _ A B _ hd hwf hlab hdom _ hw h hAt hBt ihA ihbody =>
    intro Γ' hΓ' W
    obtain ⟨u, hA⟩ := hAt
    obtain ⟨v, hB⟩ := hBt
    have hA' : Γ' ⊢ A ≡ A : Term.sort u := IsDefEq.ctx_id hΓ' W hA
    have hΓ'A : ⊢ (A :: Γ') := ⟨hΓ', _, hA'⟩
    exact .forallE (ihA hΓ' W) hd hwf hlab hdom
      (fun e he => ihbody e he hΓ'A (W.id_lift hΓ' hA)) hw h ⟨u, hA'⟩
      ⟨v, IsDefEq.ctx_id hΓ'A (W.id_lift hΓ' hA) hB⟩
  | @sigma _ _ _ _ _ _ _ A B _ hd hwf hlab hdom _ hw h hAt hBt ihA ihbody =>
    intro Γ' hΓ' W
    obtain ⟨u, hA⟩ := hAt
    obtain ⟨v, hB⟩ := hBt
    have hA' : Γ' ⊢ A ≡ A : Term.sort u := IsDefEq.ctx_id hΓ' W hA
    have hΓ'A : ⊢ (A :: Γ') := ⟨hΓ', _, hA'⟩
    exact .sigma (ihA hΓ' W) hd hwf hlab hdom
      (fun e he => ihbody e he hΓ'A (W.id_lift hΓ' hA)) hw h ⟨u, hA'⟩
      ⟨v, IsDefEq.ctx_id hΓ'A (W.id_lift hΓ' hA) hB⟩
  | @pair _ _ _ _ _ _ _ _ A _ a _ _ _ hd hwf hlab hdom _ _ hbody hty hw h hAt hat
      iha ihA ihinp ihout ihbody =>
    intro Γ' hΓ' W
    obtain ⟨u, hA⟩ := hAt
    have hA' : Γ' ⊢ A ≡ A : Term.sort u := IsDefEq.ctx_id hΓ' W hA
    exact .pair (iha hΓ' W) (ihA hΓ' W) hd hwf hlab hdom
      (fun e he => ihinp e he hΓ' W) (fun e he => ihout e he hΓ' W)
      (fun e he => ihbody e he ⟨hΓ', _, hA'⟩ (W.id_lift hΓ' hA)) hty hw h ⟨u, hA'⟩
      (IsDefEq.ctx_id hΓ' W hat)
  | fst _ hw h ihp => exact fun hΓ' W => .fst (ihp hΓ' W) hw h
  | snd _ hq hw h hty ihp =>
    intro Γ' hΓ' W
    obtain ⟨A₁, hft, hTy⟩ := hty
    exact .snd (ihp hΓ' W) hq hw h ⟨A₁, IsDefEq.ctx_id hΓ' W hft, hTy⟩
  | natCase_zero _ hz _ hMt ihM iha =>
    exact fun hΓ' W => .natCase_zero (ihM hΓ' W) hz (iha hΓ' W) (IsDefEq.ctx_id hΓ' W hMt)
  | natCase_succ _ hwv heq _ hMt ihM ihb =>
    intro Γ' hΓ' W
    exact .natCase_succ (ihM hΓ' W) hwv heq
      (ihb ⟨hΓ', _, .nat⟩ (W.id_lift hΓ' .nat)) (IsDefEq.ctx_id hΓ' W hMt)
  | @Y _ _ _ _ A _ _ _ hwx _ hAt hYt ihself ihb =>
    intro Γ' hΓ' W
    obtain ⟨u, hA⟩ := hAt
    have hA' : Γ' ⊢ A ≡ A : Term.sort u := IsDefEq.ctx_id hΓ' W hA
    exact .Y (ihself hΓ' W) hwx (ihb ⟨hΓ', _, hA'⟩ (W.id_lift hΓ' hA)) ⟨u, hA'⟩
      (IsDefEq.ctx_id hΓ' W hYt)
  | id hw h hAt hat hbt =>
    intro Γ' hΓ' W
    obtain ⟨u, hA⟩ := hAt
    exact .id hw h ⟨u, IsDefEq.ctx_id hΓ' W hA⟩ (IsDefEq.ctx_id hΓ' W hat)
      (IsDefEq.ctx_id hΓ' W hbt)
  | refl _ hw h ihv => exact fun hΓ' W => .refl (ihv hΓ' W) hw h
  | @tr _ _ _ _ _ _ _ _ _ A _ _ _ _ _ hw hle _ _ _ _ hwv hvA _ hcb hm' _ heq hAt hat hbt
      ihX iha ihb ihA ihC ihH =>
    intro Γ' hΓ' W
    obtain ⟨u, hA⟩ := hAt
    have hA' : Γ' ⊢ A ≡ A : Term.sort u := IsDefEq.ctx_id hΓ' W hA
    exact .tr hw hle (ihX hΓ' W) (iha hΓ' W) (ihb hΓ' W) (ihA hΓ' W) hwv hvA
      (ihC ⟨hΓ', _, hA'⟩ (W.id_lift hΓ' hA)) hcb hm' (fun hr => ihH hr hΓ' W) heq
      ⟨u, hA'⟩ (IsDefEq.ctx_id hΓ' W hat) (IsDefEq.ctx_id hΓ' W hbt)

/-! ## Constructors at the canonical shape

Master's primed forms.  Each takes the well-formedness that `LE` needs to
be reflexive, which master gets from its shapes being a `WF` subtype. -/

theorem Interp.bvar' {Δ Γ σ ρ i} (h : TShape.WF Δ (ρ i)) :
    Interp Δ Γ (.bvar i) σ ρ (ρ i) := .bvar h (TShape.LE.refl h)

theorem Interp.sort' {Δ Γ σ ρ r} :
    Interp Δ Γ (.sort r) σ ρ (TShape.sort r) :=
  .sort trivial (TShape.LE.refl (a := TShape.sort r) trivial)

theorem Interp.unit' {Δ Γ σ ρ r} :
    Interp Δ Γ (.unit r) σ ρ (TShape.unit r) :=
  .unit trivial (TShape.LE.refl (a := TShape.unit r) trivial)

theorem Interp.nat' {Δ Γ σ ρ} : Interp Δ Γ .nat σ ρ TShape.nat :=
  .nat trivial (TShape.LE.refl (a := TShape.nat) trivial)

theorem Interp.zero' {Δ Γ σ ρ} : Interp Δ Γ .zero σ ρ TShape.zero :=
  .zero trivial (TShape.LE.refl (a := TShape.zero) trivial)

theorem Interp.succ' {Δ Γ σ ρ N} {n} {v : Shape n}
    (hv : Interp Δ Γ N σ ρ (Shape.T v)) (h : Shape.WF Δ v) :
    Interp Δ Γ (.succ N) σ ρ (Shape.T (n := n+1) (ShapeS.succ v)) :=
  .succ hv h (TShape.LE.refl (a := Shape.T (n := n+1) (ShapeS.succ v)) h)

/-! ## Inversion for the atoms

Every rule but `bot` pins the head of the term, so these are one `cases`
each.  They are what the soundness induction reads a subderivation with,
and — for `forallE` — what eventually yields Π-injectivity, since the
shape it returns carries the syntactic pair. -/

theorem Interp.le_sort {Δ Γ σ ρ m r}
    (H : Interp Δ Γ (.sort r) σ ρ m) : TShape.LE Δ m (TShape.sort r) := by
  cases H with
  | bot => exact TShape.bot_le' rfl
  | sort _ h => exact h

theorem Interp.le_unit {Δ Γ σ ρ m r}
    (H : Interp Δ Γ (.unit r) σ ρ m) : TShape.LE Δ m (TShape.unit r) := by
  cases H with
  | bot => exact TShape.bot_le' rfl
  | unit _ h => exact h

theorem Interp.le_nat {Δ Γ σ ρ m}
    (H : Interp Δ Γ .nat σ ρ m) : TShape.LE Δ m TShape.nat := by
  cases H with
  | bot => exact TShape.bot_le' rfl
  | nat _ h => exact h

theorem Interp.le_zero {Δ Γ σ ρ m}
    (H : Interp Δ Γ .zero σ ρ m) : TShape.LE Δ m TShape.zero := by
  cases H with
  | bot => exact TShape.bot_le' rfl
  | zero _ h => exact h

theorem Interp.le_id {Δ Γ σ ρ m r A a b}
    (H : Interp Δ Γ (.id r A a b) σ ρ m) :
    TShape.LE Δ m
      (Shape.T (n := 1) (ShapeS.id r (A.subst σ) (a.subst σ) (b.subst σ))) := by
  cases H with
  | bot => exact TShape.bot_le' rfl
  | id _ h => exact h

theorem Interp.bvar_iff {Δ Γ σ ρ m i} :
    Interp Δ Γ (.bvar i) σ ρ m ↔ TShape.WF Δ m ∧ TShape.LE Δ m (ρ i) :=
  ⟨fun H => ⟨H.wf, by cases H with
      | bot => exact TShape.bot_le' rfl
      | bvar _ h => exact h⟩,
   fun ⟨hw, h⟩ => .bvar hw h⟩

theorem Interp.le_succ {Δ Γ σ ρ m N}
    (H : Interp Δ Γ (.succ N) σ ρ m) :
    ∃ n, ∃ v : Shape n, Interp Δ Γ N σ ρ (Shape.T v) ∧
      TShape.LE Δ m (Shape.T (n := n+1) (ShapeS.succ v)) := by
  cases H with
  | bot => exact ⟨0, .bot, .bot, TShape.bot_le' rfl⟩
  | succ hv _ h => exact ⟨_, _, hv, h⟩

/-- The Π case.  The shape the interpretation lands in **records the
syntactic pair** `(A[σ], B[σ.lift])`, which is what makes injectivity of
`forallE` a projection out of soundness rather than a consequence of
adequacy. -/
theorem Interp.le_forallE {Δ Γ σ ρ m A B}
    (H : Interp Δ Γ (.forallE A B) σ ρ m) :
    m.2 = Shape.bot ∨
    ∃ n, ∃ d : Shape n, ∃ g : ShapeFun n,
      TShape.LE Δ m (Shape.T (n := n+1) (.forallE (A.subst σ) (B.subst σ.lift) d g)) := by
  cases H with
  | bot => exact .inl rfl
  | forallE _ _ _ _ _ _ _ h => exact .inr ⟨_, _, _, h⟩

/-- The Σ case, as `le_forallE`. -/
theorem Interp.le_sigma (H : Interp Δ Γ (.sigma A B) σ ρ m) :
    m.2 = Shape.bot ∨
      ∃ n, ∃ d : Shape n, ∃ g : ShapeFun n,
        TShape.LE Δ m
          (Shape.T (n := n+1) (.sigma (A.subst σ) (B.subst σ.lift) d g)) := by
  cases H with
  | bot => exact .inl rfl
  | sigma _ _ _ _ _ _ _ h => exact .inr ⟨_, _, _, h⟩

/-! ## The Π label, in and out

This is the other repo's `mem_piAtom_pi_iff`, and the point of the whole
labelling.  He proves that the label-only Π atom is a member of a Π value
**iff** its label is the reindexed label; equality of labels there is
equality in his quotient, which is definitional equality, which is our
`PiLabelEq`.

Master has nothing like this.  In its place master carries
`StrongSoundCore`, a second inductive with one constructor per term former
running in lockstep with the semantics, so that the logical relation can
read the head former back out — and then needs `LogRel.lean` plus
`Adequacy.lean` to connect it to reduction.  Here the head former is
*inside the shape*, so reading it back is a projection out of the order.

Both directions hold, and neither needs soundness: `piAtom` builds the
probe, `le_piAtom` reads the label off it.  Soundness is what lets the two
be composed across a definitional equality, which is how `forallE_inv`
will go. -/

/-- The probe exists: a well-typed Π has its own label-only atom among its
approximants. -/
theorem Interp.piAtom (hA : Δ ⊢ A.subst σ : .sort u)
    (hB : A.subst σ :: Δ ⊢ B.subst σ.lift : .sort v)
    (hAΓ : Γ ⊢ A : .sort u) (hBΓ : A :: Γ ⊢ B : .sort v) :
    Interp Δ Γ (.forallE A B) σ ρ (Shape.T (n := 1) (.piAtom (A.subst σ) (B.subst σ.lift))) :=
  .forallE (d := (Shape.bot : Shape 0)) .bot (.bot .sort)
    (Shape.WF.piAtom hA hB) nofun nofun nofun
    (.piAtom hA hB) (TShape.LE.T.2 (.refl (.piAtom hA hB))) ⟨u, hAΓ⟩ ⟨v, hBΓ⟩

/-- And the probe reports: if the atom approximates `⟦forallE A B⟧`, its
label is definitionally the Π's own label.  Π-injectivity is this plus
soundness, with no adequacy in between. -/
theorem Interp.le_piAtom (H : Interp Δ Γ (.forallE A B) σ ρ (Shape.T (n := 1) (.piAtom A' B'))) :
    PiLabelEq Δ A' B' (A.subst σ) (B.subst σ.lift) := by
  cases H with | forallE _ _ _ _ _ _ _ h _ _
  have h' := (TShape.LE.def_mp (Nat.succ_le_succ (Nat.zero_le _)) (Nat.le_refl _)) h
  rw [Shape.lift_piAtom, Shape.lift_self] at h'
  exact Shape.piAtom_le_forallE h'

/-- The Σ probe, as `piAtom`. -/
theorem Interp.sigmaAtom (hA : Δ ⊢ A.subst σ : .sort u)
    (hB : A.subst σ :: Δ ⊢ B.subst σ.lift : .sort v)
    (hAΓ : Γ ⊢ A : .sort u) (hBΓ : A :: Γ ⊢ B : .sort v) :
    Interp Δ Γ (.sigma A B) σ ρ (Shape.T (n := 1) (.sigmaAtom (A.subst σ) (B.subst σ.lift))) :=
  .sigma (d := (Shape.bot : Shape 0)) .bot (.bot .sort)
    (Shape.WF.sigmaAtom hA hB) nofun nofun nofun
    (.sigmaAtom hA hB) (TShape.LE.T.2 (.refl (.sigmaAtom hA hB))) ⟨u, hAΓ⟩ ⟨v, hBΓ⟩

theorem Interp.le_sigmaAtom
    (H : Interp Δ Γ (.sigma A B) σ ρ (Shape.T (n := 1) (.sigmaAtom A' B'))) :
    PiLabelEq Δ A' B' (A.subst σ) (B.subst σ.lift) := by
  cases H with | sigma _ _ _ _ _ _ _ h _ _
  have h' := (TShape.LE.def_mp (Nat.succ_le_succ (Nat.zero_le _)) (Nat.le_refl _)) h
  rw [Shape.lift_sigmaAtom, Shape.lift_self] at h'
  exact Shape.sigmaAtom_le_sigma h'

/-! ## Naturality in the stage

The presheaf property, and the reason every shape-level notion had to be
shown stable under `Shape.subst` first.  For the other repo this is
functoriality of `ΩLower` and costs nothing; here the stage is raw syntax,
so it is an induction, and each case is the corresponding `subst` lemma
one level down.

Note the term's own context `Γ` does not move: only the stage does.  That
is what makes this independent of the substitution lemma for terms, which
moves `Γ` and leaves the stage's shape alone. -/

theorem Interp.subst (H : Interp Δ Γ t σ ρ m) (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ) :
    Interp Θ Γ t (σ.comp τ) (ρ.subst τ) (m.subst τ) := by
  induction H generalizing Θ τ with
  | bot => simp only [TShape.subst_T, Shape.subst_bot]; exact .bot
  | bvar hw h1 => exact .bvar (.subst hΘ W hw) (h1.subst hΘ W)
  | sort hw h1 => exact .sort (hw.subst hΘ W) (by simpa using .subst hΘ W h1)
  | unit hw h1 => exact .unit (hw.subst hΘ W) (h1.subst hΘ W)
  | nat hw h1 => exact .nat (hw.subst hΘ W) (h1.subst hΘ W)
  | zero hw h1 => exact .zero (hw.subst hΘ W) (h1.subst hΘ W)
  | succ _ hw h1 ihv => exact .succ (ihv hΘ W) (hw.subst hΘ W) (h1.subst hΘ W)
  | app _ _ hev hw h1 hty ihF iha =>
    have hev' := TEvaluates.subst hΘ W hev
    rw [subst_subst] at hev'
    obtain ⟨A₀, hat, hTy⟩ := hty
    refine .app (ihF hΘ W) (iha hΘ W) hev' (hw.subst hΘ W) (h1.subst hΘ W) ⟨A₀, hat, ?_⟩
    have := TyEq.subst hΘ W hTy
    rwa [subst_subst] at this
  | lam _ hd hwf hdom _ hw h1 hAt ihA ihbody =>
    have hwf' := hwf.subst hΘ W; have h1' := h1.subst hΘ W
    rw [Shape.subst, subst_subst] at hwf'
    simp only [TShape.subst_T, Shape.subst, subst_subst] at h1'
    refine .lam (ihA hΘ W) (TShape.HasType.subst hΘ W hd) hwf' ?_ ?_
      (hw.subst hΘ W) h1' hAt
    · intro e' he'
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      exact TShape.HasType.subst hΘ W (hdom e he)
    · intro e' he'
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have := ihbody e he hΘ W
      rwa [Subst.cons_comp, Valuation.subst_push, TShape.subst_T] at this
  | forallE _ hd hwf hlab hdom _ hw h1 hAt hBt ihA ihbody =>
    have hwf' := hwf.subst hΘ W
    have h1' := h1.subst hΘ W
    simp only [TShape.subst_T, Shape.subst, subst_subst, ← Subst.comp_lift] at hwf' h1'
    refine .forallE (ihA hΘ W) (TShape.HasType.subst hΘ W hd) hwf' (fun e' he' => ?_)
      (fun e' he' => ?_) (fun e' he' => ?_) (hw.subst hΘ W) h1' hAt hBt
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have ⟨u, hu⟩ := hlab e he
      exact ⟨u, by rw [← subst_subst]; exact hu.subst hΘ W⟩
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      exact TShape.HasType.subst hΘ W (hdom e he)
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have := ihbody e he hΘ W
      rwa [Subst.cons_comp, Valuation.subst_push, TShape.subst_T] at this
  | sigma _ hd hwf hlab hdom _ hw h1 hAt hBt ihA ihbody =>
    have hwf' := hwf.subst hΘ W
    have h1' := h1.subst hΘ W
    simp only [TShape.subst_T, Shape.subst, subst_subst, ← Subst.comp_lift] at hwf' h1'
    refine .sigma (ihA hΘ W) (TShape.HasType.subst hΘ W hd) hwf' (fun e' he' => ?_)
      (fun e' he' => ?_) (fun e' he' => ?_) (hw.subst hΘ W) h1' hAt hBt
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have ⟨u, hu⟩ := hlab e he
      exact ⟨u, by rw [← subst_subst]; exact hu.subst hΘ W⟩
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      exact TShape.HasType.subst hΘ W (hdom e he)
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have := ihbody e he hΘ W
      rwa [Subst.cons_comp, Valuation.subst_push, TShape.subst_T] at this
  | @pair _ _ _ _ _ _ g₀ _ _ _ _ _ ha hA hd hwf hlab hdom hinp hout hbody hty hw h1 hAt hat
      iha ihA ihinp ihout ihbody =>
    have hwf' := hwf.subst hΘ W
    have h1' := h1.subst hΘ W
    simp only [TShape.subst_T, Shape.subst, subst_subst, ShapeFun.subst,
      List.map_map, Function.comp_def] at hwf' h1'
    refine .pair (g₀ := g₀.map fun p =>
        (⟨p.1.ty.subst τ, p.1.tm.subst τ, p.1.inp.subst τ, p.1.out.subst τ⟩, p.2.subst τ))
      (iha hΘ W) (ihA hΘ W) (TShape.HasType.subst hΘ W hd) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (hw.subst hΘ W) ?_ hAt hat
    · simpa [List.map_map, Function.comp_def] using hwf'
    · intro e he
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
      have := (hlab p hp).subst hΘ W
      rwa [subst_subst] at this
    · intro e he
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
      exact TShape.HasType.subst hΘ W (hdom p hp)
    · intro e he
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
      exact ihinp p hp hΘ W
    · intro e he
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
      exact ihout p hp hΘ W
    · intro e he
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
      have := ihbody p hp hΘ W
      rwa [Subst.cons_comp, Valuation.subst_push, TShape.subst_T] at this
    · intro e he
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
      exact TShape.HasType.subst hΘ W (hty p hp)
    · simpa [List.map_map, Function.comp_def] using h1'
  | fst _ hw h1 ihp => exact .fst (ihp hΘ W) (hw.subst hΘ W) (h1.subst hΘ W)
  | snd _ hq hw h1 hty ihp =>
    have hq' := hq.subst hΘ W
    rw [subst_subst] at hq'
    obtain ⟨A₁, hft, hTy⟩ := hty
    refine .snd (ihp hΘ W) hq' (hw.subst hΘ W) (h1.subst hΘ W) ⟨A₁, hft, ?_⟩
    have := TyEq.subst hΘ W hTy
    rwa [subst_subst] at this
  | natCase_zero _ hz _ hMt ihM iha =>
    have hz' := hz.subst hΘ W
    rw [subst_subst] at hz'
    exact .natCase_zero (ihM hΘ W) hz' (iha hΘ W) hMt
  | natCase_succ _ hwv heq _ hMt ihM ihb =>
    have heq' := heq.subst hΘ W
    rw [subst_subst] at heq'
    refine .natCase_succ (ihM hΘ W) (hwv.subst hΘ W) heq' ?_ hMt
    have := ihb hΘ W
    rwa [Subst.cons_comp, Valuation.subst_push, TShape.subst_T] at this
  | Y _ hwx _ hAt hYt ihself ihb =>
    refine .Y (ihself hΘ W) (hwx.subst hΘ W) ?_ hAt hYt
    have := ihb hΘ W
    rwa [Subst.cons_comp, subst_subst, Valuation.subst_push] at this
  | id hw h1 hAt hat hbt =>
    have := h1.subst hΘ W
    simp only [TShape.subst_T, Shape.subst, subst_subst] at this
    exact .id (hw.subst hΘ W) this hAt hat hbt
  | refl _ hw h1 ihv => exact .refl (ihv hΘ W) (hw.subst hΘ W) (h1.subst hΘ W)
  | tr hw hle _ _ _ _ hwv hvA _ hcb hm' _ heq hAt hat hbt ihX iha ihb ihA ihC ihH =>
    have heq' := heq.subst hΘ W
    rw [subst_subst, subst_subst, subst_subst] at heq'
    refine .tr (hw.subst hΘ W) (hle.subst hΘ W) (ihX hΘ W) (iha hΘ W) (ihb hΘ W) (ihA hΘ W)
      (hwv.subst hΘ W) (hvA.subst hΘ W) ?_ (hcb.subst hΘ W) (hm'.subst hΘ W)
      (fun hr => ihH hr hΘ W) heq' hAt hat hbt
    have := ihC hΘ W
    rwa [Subst.cons_comp, subst_subst, Valuation.subst_push] at this

/-! ## Weakening

Master's `weak'_iff`, in the direction that builds.  A renaming `l` of the
term is matched by a stage `σ'` and valuation `ρ'` that agree with `σ` and
`ρ` along it; the labels are then literally the same terms, since
`(t.lift' l).subst σ' = t.subst σ` once `σ = σ' ∘ l`.

The term's context moves freely here, and that is worth saying plainly:
with the `app` rule's typing premises gone (they were redundant), no rule
mentions `Γ` other than to thread it, so it carries no information.  It is
kept as an index because it is where those premises belong if they are
ever wanted back, and because it documents which context each
subderivation is about. -/

theorem Subst.lift_l_cons : (Subst.lift_l l σ).cons e = Subst.lift_l l.cons (σ.cons e) := by
  funext i; cases i <;> rfl

theorem Interp.weak' {Δ : List Term} {Γ t σ' ρ m l} (H : Interp Δ Γ t (Subst.lift_l l σ') ρ m)
    {Γ' ρ'} (WΓ : Ctx.Lift' l Γ Γ') (hρ : ∀ i, ρ i = ρ' (Lift.liftVar l i)) :
    Interp Δ Γ' (t.lift' l) σ' ρ' m := by
  generalize hσ : Subst.lift_l l σ' = σ at H
  induction H generalizing Γ' l σ' ρ' with subst hσ
  | bot => exact .bot
  | bvar hw h1 => exact .bvar hw (hρ _ ▸ h1)
  | sort hw h1 => exact .sort hw h1
  | unit hw h1 => exact .unit hw h1
  | nat hw h1 => exact .nat hw h1
  | zero hw h1 => exact .zero hw h1
  | succ _ hw h1 ihv => exact .succ (ihv WΓ hρ rfl) hw h1
  | app _ _ hev hw h1 hty ihF iha =>
    rw [← subst_lift'] at hev
    obtain ⟨A₀, hat, hTy⟩ := hty
    refine .app (ihF WΓ hρ rfl) (iha WΓ hρ rfl) hev hw h1 ⟨A₀.lift' l, hat.weak' WΓ, ?_⟩
    rwa [subst_lift']
  | lam _ hd hwf hdom _ hw h1 hAt ihA ihbody =>
    rw [← subst_lift'] at hwf h1
    obtain ⟨u, hA⟩ := hAt
    refine .lam (ihA WΓ hρ rfl) hd hwf hdom ?_ hw h1 ⟨u, hA.weak' WΓ⟩
    intro e he
    refine ihbody e he (l := l.cons) WΓ.cons (fun i => ?_) Subst.lift_l_cons.symm
    cases i <;> simp_all [Valuation.push]
  | forallE _ hd hwf hlab hdom _ hw h1 hAt hBt ihA ihbody =>
    rw [Subst.lift_l_lift, ← subst_lift', ← subst_lift'] at hwf h1
    obtain ⟨u, hA⟩ := hAt
    obtain ⟨v, hB⟩ := hBt
    refine .forallE (ihA WΓ hρ rfl) hd hwf ?_ hdom ?_ hw h1 ⟨u, hA.weak' WΓ⟩
      ⟨v, hB.weak' WΓ.cons⟩
    · intro e he
      have ⟨u, hu⟩ := hlab e he
      exact ⟨u, by rwa [subst_lift']⟩
    · intro e he
      refine ihbody e he (l := l.cons) WΓ.cons (fun i => ?_) Subst.lift_l_cons.symm
      cases i <;> simp_all [Valuation.push]
  | sigma _ hd hwf hlab hdom _ hw h1 hAt hBt ihA ihbody =>
    rw [Subst.lift_l_lift, ← subst_lift', ← subst_lift'] at hwf h1
    obtain ⟨u, hA⟩ := hAt
    obtain ⟨v, hB⟩ := hBt
    refine .sigma (ihA WΓ hρ rfl) hd hwf ?_ hdom ?_ hw h1 ⟨u, hA.weak' WΓ⟩
      ⟨v, hB.weak' WΓ.cons⟩
    · intro e he
      have ⟨u, hu⟩ := hlab e he
      exact ⟨u, by rwa [subst_lift']⟩
    · intro e he
      refine ihbody e he (l := l.cons) WΓ.cons (fun i => ?_) Subst.lift_l_cons.symm
      cases i <;> simp_all [Valuation.push]
  | pair _ _ hd hwf hlab hdom _ _ hbody hty hw h1 hAt hat iha ihA ihinp ihout ihbody =>
    rw [← subst_lift'] at hwf h1 hlab
    obtain ⟨u, hA⟩ := hAt
    refine .pair (iha WΓ hρ rfl) (ihA WΓ hρ rfl) hd hwf hlab hdom
      (fun e he => ihinp e he WΓ hρ rfl)
      (fun e he => ihout e he WΓ hρ rfl) (fun e he => ?_) hty hw h1 ⟨u, hA.weak' WΓ⟩
      (hat.weak' WΓ)
    refine ihbody e he (l := l.cons) WΓ.cons (fun i => ?_) Subst.lift_l_cons.symm
    cases i <;> simp_all [Valuation.push]
  | fst _ hw h1 ihp => exact .fst (ihp WΓ hρ rfl) hw h1
  | snd _ hq hw h1 hty ihp =>
    rw [← subst_lift'] at hq
    obtain ⟨A₁, hft, hTy⟩ := hty
    refine .snd (ihp WΓ hρ rfl) hq hw h1 ⟨A₁.lift' l, ?_, ?_⟩
    · have := hft.weak' WΓ
      simpa using this
    · rwa [subst_lift']
  | natCase_zero _ hz _ hMt ihM iha =>
    rw [← subst_lift'] at hz
    exact .natCase_zero (ihM WΓ hρ rfl) hz (iha WΓ hρ rfl) (by simpa using hMt.weak' WΓ)
  | natCase_succ _ hwv heq _ hMt ihM ihb =>
    rw [← subst_lift'] at heq
    refine .natCase_succ (ihM WΓ hρ rfl) hwv heq ?_ (by simpa using hMt.weak' WΓ)
    refine ihb (l := l.cons) (by simpa using WΓ.cons (A := Term.nat)) (fun i => ?_)
      Subst.lift_l_cons.symm
    cases i <;> simp_all [Valuation.push]
  | Y _ hwx _ hAt hYt ihself ihb =>
    obtain ⟨u, hA⟩ := hAt
    refine .Y (ihself WΓ hρ rfl) hwx ?_ ⟨u, hA.weak' WΓ⟩ (by simpa using hYt.weak' WΓ)
    refine ihb (l := l.cons) WΓ.cons (fun i => ?_) ?_
    · cases i <;> simp_all [Valuation.push]
    · rw [← Subst.lift_l_cons]
      exact congrArg _ (subst_lift' (e := Term.Y _ _))
  | id hw h1 hAt hat hbt =>
    simp only [← subst_lift'] at h1
    obtain ⟨u, hA⟩ := hAt
    exact .id hw h1 ⟨u, hA.weak' WΓ⟩ (hat.weak' WΓ) (hbt.weak' WΓ)
  | refl _ hw h1 ihv => exact .refl (ihv WΓ hρ rfl) hw h1
  | tr hw hle _ _ _ _ hwv hvA _ hcb hm' _ heq hAt hat hbt ihX iha ihb ihA ihC ihH =>
    rw [← subst_lift', ← subst_lift', ← subst_lift'] at heq
    obtain ⟨u, hA⟩ := hAt
    refine .tr hw hle (ihX WΓ hρ rfl) (iha WΓ hρ rfl) (ihb WΓ hρ rfl) (ihA WΓ hρ rfl)
      hwv hvA ?_ hcb hm' (fun hr => ihH hr WΓ hρ rfl) heq ⟨u, hA.weak' WΓ⟩
      (hat.weak' WΓ) (hbt.weak' WΓ)
    refine ihC (l := l.cons) WΓ.cons (fun i => ?_) ?_
    · cases i <;> simp_all [Valuation.push]
    · rw [← Subst.lift_l_cons]
      exact congrArg _ (subst_lift')

/-- Composing with a lifted substitution, under an extended stage. -/
theorem Subst.lift_comp_cons {θ σ : Subst} {e : Term} :
    θ.lift.comp (σ.cons e) = (θ.comp σ).cons e := by
  funext i; cases i with
  | zero => rfl
  | succ i => exact lift_subst_cons

/-- **Substitution in the term, the constructive direction.**  An
approximant of `t` at the composed stage, under a valuation whose slots
approximate the `θ i`, is an approximant of `t[θ]`.  Master's
`LE_Interp.subst` in the direction that needs no directedness: every
clause is rebuilt verbatim, with `subst_subst` for the labels and
`Interp.weak'` for the slot a binder adds. -/
theorem Interp.of_substTerm {Δ Γ : List Term} {t : Term} {τ ρ' m} (hΔ : ⊢ Δ)
    (H : Interp Δ Γ t τ ρ' m) :
    ∀ {Γ' : List Term} {θ σ ρ}, ⊢ Γ' → Ctx.SubstEq Γ' θ θ Γ → τ = θ.comp σ →
      (∀ i, Interp Δ Γ' (θ i) σ ρ (ρ' i)) →
      Interp Δ Γ' (t.subst θ) σ ρ m := by
  induction H with
  | bot => intro _ _ _ _ _ _ _ _; exact .bot
  | bvar hw h1 => intro _ _ _ _ _ _ _ hθ; exact Interp.mono hΔ hw h1 (hθ _)
  | sort hw h1 => intro _ _ _ _ _ _ _ _; exact .sort hw h1
  | unit hw h1 => intro _ _ _ _ _ _ _ _; exact .unit hw h1
  | nat hw h1 => intro _ _ _ _ _ _ _ _; exact .nat hw h1
  | zero hw h1 => intro _ _ _ _ _ _ _ _; exact .zero hw h1
  | succ _ hw h1 ihv =>
    intro _ _ _ _ hΓ' Wθ hτ hθ; exact .succ (ihv hΓ' Wθ hτ hθ) hw h1
  | app _ _ hev hw h1 hty ihF iha =>
    intro Γ' θ σ ρ hΓ' Wθ hτ hθ
    subst hτ
    rw [← subst_subst] at hev
    obtain ⟨A₀, hat, hTy⟩ := hty
    refine .app (ihF hΓ' Wθ rfl hθ) (iha hΓ' Wθ rfl hθ) hev hw h1
      ⟨A₀.subst θ, hat.subst hΓ' Wθ, ?_⟩
    rwa [subst_subst]
  | @lam _ _ _ _ _ _ _ A _ hA hd hwf hdom hbody hw h1 hAt ihA ihbody =>
    intro Γ' θ σ ρ hΓ' Wθ hτ hθ
    subst hτ
    rw [← subst_subst] at hwf h1
    obtain ⟨u, hAty⟩ := hAt
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hAty.subst hΓ' Wθ
    refine .lam (ihA hΓ' Wθ rfl hθ) hd hwf hdom (fun e he => ?_) hw h1 ⟨u, hAθ⟩
    refine ihbody e he ⟨hΓ', _, hAθ⟩ (Wθ.lift hAty hAθ) Subst.lift_comp_cons.symm (fun i => ?_)
    cases i with
    | zero => exact .bvar (hwf.2.2.1.1 e he).2.2.1 (TShape.LE.refl (hwf.2.2.1.1 e he).2.2.1)
    | succ i => exact Interp.weak' (l := .skip .refl) (hθ i) (.skip .refl) (fun _ => rfl)
  | @forallE _ _ _ _ _ _ _ A B hA hd hwf hlab hdom hbody hw h1 hAt hBt ihA ihbody =>
    intro Γ' θ σ ρ hΓ' Wθ hτ hθ
    subst hτ
    rw [Subst.comp_lift, ← subst_subst, ← subst_subst] at hwf h1
    obtain ⟨u, hAty⟩ := hAt
    obtain ⟨v, hBty⟩ := hBt
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hAty.subst hΓ' Wθ
    have hΓ'A : ⊢ (A.subst θ :: Γ') := ⟨hΓ', _, hAθ⟩
    refine .forallE (ihA hΓ' Wθ rfl hθ) hd hwf (fun e he => ?_) hdom (fun e he => ?_) hw h1
      ⟨u, hAθ⟩ ⟨v, hBty.subst hΓ'A (Wθ.lift hAty hAθ)⟩
    · obtain ⟨u, hu⟩ := hlab e he
      exact ⟨u, by rwa [← subst_subst] at hu⟩
    · refine ihbody e he hΓ'A (Wθ.lift hAty hAθ) Subst.lift_comp_cons.symm (fun i => ?_)
      cases i with
      | zero =>
        exact .bvar (hwf.2.2.2.1 e he).2.2.1 (TShape.LE.refl (hwf.2.2.2.1 e he).2.2.1)
      | succ i => exact Interp.weak' (l := .skip .refl) (hθ i) (.skip .refl) (fun _ => rfl)
  | @sigma _ _ _ _ _ _ _ A B hA hd hwf hlab hdom hbody hw h1 hAt hBt ihA ihbody =>
    intro Γ' θ σ ρ hΓ' Wθ hτ hθ
    subst hτ
    rw [Subst.comp_lift, ← subst_subst, ← subst_subst] at hwf h1
    obtain ⟨u, hAty⟩ := hAt
    obtain ⟨v, hBty⟩ := hBt
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hAty.subst hΓ' Wθ
    have hΓ'A : ⊢ (A.subst θ :: Γ') := ⟨hΓ', _, hAθ⟩
    refine .sigma (ihA hΓ' Wθ rfl hθ) hd hwf (fun e he => ?_) hdom (fun e he => ?_) hw h1
      ⟨u, hAθ⟩ ⟨v, hBty.subst hΓ'A (Wθ.lift hAty hAθ)⟩
    · obtain ⟨u, hu⟩ := hlab e he
      exact ⟨u, by rwa [← subst_subst] at hu⟩
    · refine ihbody e he hΓ'A (Wθ.lift hAty hAθ) Subst.lift_comp_cons.symm (fun i => ?_)
      cases i with
      | zero =>
        exact .bvar (hwf.2.2.2.1 e he).2.2.1 (TShape.LE.refl (hwf.2.2.2.1 e he).2.2.1)
      | succ i => exact Interp.weak' (l := .skip .refl) (hθ i) (.skip .refl) (fun _ => rfl)
  | @pair _ _ _ _ _ _ _ _ A _ a _ ha hA hd hwf hlab hdom hinp hout hbody hty hw h1 hAt hat
      iha ihA ihinp ihout ihbody =>
    intro Γ' θ σ ρ hΓ' Wθ hτ hθ
    subst hτ
    rw [← subst_subst] at hwf h1
    obtain ⟨u, hAty⟩ := hAt
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hAty.subst hΓ' Wθ
    refine .pair (iha hΓ' Wθ rfl hθ) (ihA hΓ' Wθ rfl hθ) hd hwf (fun e he => ?_) hdom
      (fun e he => ihinp e he hΓ' Wθ rfl hθ) (fun e he => ihout e he hΓ' Wθ rfl hθ)
      (fun e he => ?_) hty hw h1 ⟨u, hAθ⟩ (hat.subst hΓ' Wθ)
    · have := hlab e he; rwa [← subst_subst] at this
    · refine ihbody e he ⟨hΓ', _, hAθ⟩ (Wθ.lift hAty hAθ) Subst.lift_comp_cons.symm
        (fun i => ?_)
      cases i with
      | zero =>
        exact .bvar (hwf.2.2.1.1 e.1 (List.mem_map.2 ⟨e, he, rfl⟩)).2.2.1
          (TShape.LE.refl (hwf.2.2.1.1 e.1 (List.mem_map.2 ⟨e, he, rfl⟩)).2.2.1)
      | succ i => exact Interp.weak' (l := .skip .refl) (hθ i) (.skip .refl) (fun _ => rfl)
  | fst _ hw h1 ihp =>
    intro _ _ _ _ hΓ' Wθ hτ hθ; exact .fst (ihp hΓ' Wθ hτ hθ) hw h1
  | snd _ hq hw h1 hty ihp =>
    intro Γ' θ σ ρ hΓ' Wθ hτ hθ
    subst hτ
    rw [← subst_subst] at hq
    obtain ⟨A₁, hft, hTy⟩ := hty
    refine .snd (ihp hΓ' Wθ rfl hθ) hq hw h1 ⟨A₁.subst θ, ?_, ?_⟩
    · simpa using hft.subst hΓ' Wθ
    · rwa [subst_subst]
  | natCase_zero _ hz _ hMt ihM iha =>
    intro Γ' θ σ ρ hΓ' Wθ hτ hθ
    subst hτ
    rw [← subst_subst] at hz
    exact .natCase_zero (ihM hΓ' Wθ rfl hθ) hz (iha hΓ' Wθ rfl hθ)
      (by simpa using hMt.subst hΓ' Wθ)
  | natCase_succ _ hwv heq _ hMt ihM ihb =>
    intro Γ' θ σ ρ hΓ' Wθ hτ hθ
    subst hτ
    rw [← subst_subst] at heq
    refine .natCase_succ (ihM hΓ' Wθ rfl hθ) hwv heq ?_ (by simpa using hMt.subst hΓ' Wθ)
    refine ihb (θ := θ.lift) ⟨hΓ', _, (.nat : Γ' ⊢ Term.nat : Term.type)⟩
      (by simpa using Wθ.lift (.nat) (.nat)) Subst.lift_comp_cons.symm (fun i => ?_)
    cases i with
    | zero => exact .bvar (TShape.WF.T.2 hwv) (TShape.LE.refl (TShape.WF.T.2 hwv))
    | succ i => exact Interp.weak' (l := .skip .refl) (hθ i) (.skip .refl) (fun _ => rfl)
  | @Y _ _ _ _ A b _ _ hwx _ hAt hYt ihself ihb =>
    intro Γ' θ σ ρ hΓ' Wθ hτ hθ
    subst hτ
    obtain ⟨u, hAty⟩ := hAt
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hAty.subst hΓ' Wθ
    refine .Y (ihself hΓ' Wθ rfl hθ) hwx ?_ ⟨u, hAθ⟩ (by simpa using hYt.subst hΓ' Wθ)
    simp only [Term.subst, subst_subst, ← Subst.comp_lift]
    refine ihb ⟨hΓ', _, hAθ⟩ (Wθ.lift hAty hAθ) Subst.lift_comp_cons.symm (fun i => ?_)
    cases i with
    | zero => exact .bvar hwx (TShape.LE.refl hwx)
    | succ i => exact Interp.weak' (l := .skip .refl) (hθ i) (.skip .refl) (fun _ => rfl)
  | id hw h1 hAt hat hbt =>
    intro Γ' θ σ ρ hΓ' Wθ hτ hθ
    subst hτ
    simp only [← subst_subst] at h1
    obtain ⟨u, hAty⟩ := hAt
    exact .id hw h1 ⟨u, hAty.subst hΓ' Wθ⟩ (hat.subst hΓ' Wθ) (hbt.subst hΓ' Wθ)
  | refl _ hw h1 ihv =>
    intro _ _ _ _ hΓ' Wθ hτ hθ; exact .refl (ihv hΓ' Wθ hτ hθ) hw h1
  | @tr _ _ _ _ _ _ _ _ _ A _ _ _ _ _ hw hle _ _ _ _ hwv hvA _ hcb hm' _ heq hAt hat hbt
      ihX iha ihb ihA ihC ihH =>
    intro Γ' θ σ ρ hΓ' Wθ hτ hθ
    subst hτ
    rw [← subst_subst, ← subst_subst, ← subst_subst] at heq
    obtain ⟨u, hAty⟩ := hAt
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hAty.subst hΓ' Wθ
    refine .tr hw hle (ihX hΓ' Wθ rfl hθ) (iha hΓ' Wθ rfl hθ) (ihb hΓ' Wθ rfl hθ)
      (ihA hΓ' Wθ rfl hθ) hwv hvA ?_ hcb hm' (fun hr => ihH hr hΓ' Wθ rfl hθ) heq
      ⟨u, hAθ⟩ (hat.subst hΓ' Wθ) (hbt.subst hΓ' Wθ)
    rw [subst_subst]
    refine ihC ⟨hΓ', _, hAθ⟩ (Wθ.lift hAty hAθ) Subst.lift_comp_cons.symm (fun i => ?_)
    cases i with
    | zero => exact .bvar hwv (TShape.LE.refl hwv)
    | succ i => exact Interp.weak' (l := .skip .refl) (hθ i) (.skip .refl) (fun _ => rfl)

/-- **Strengthening along a renaming**, the direction `Interp.weak'` does
not give.  With the labels' typings in the clauses this is no longer a
statement about raw terms: moving an interpretation into a *smaller*
context means moving its typings there, and the syntax has weakening but
not strengthening.  So the lemma is indexed by a typing of the term in
the small context, and the induction runs on that — the same shape as
`IsDefEq.stage`, and for the same reason.

Master proves the raw version by casing on the term at each step; here
each case of the *typing* supplies the premises the clause needs. -/
theorem Interp.unweak {Δ Γ : List Term} {t T : Term} (hΓ : ⊢ Γ) (ht : Γ ⊢ t : T) :
    ∀ {Γ' l σ' ρ ρ' m}, Ctx.Lift' l Γ Γ' → (∀ i, ρ i = ρ' (Lift.liftVar l i)) →
      Interp Δ Γ' (t.lift' l) σ' ρ' m → Interp Δ Γ t (σ'.lift_l l) ρ m := by
  sorry

theorem Interp.weak_iff {Δ Γ Γ' : List Term} {t T σ' ρ ρ' m l} (hΓ : ⊢ Γ)
    (ht : Γ ⊢ t : T) (WΓ : Ctx.Lift' l Γ Γ') (hρ : ∀ i, ρ i = ρ' (Lift.liftVar l i)) :
    Interp Δ Γ' (t.lift' l) σ' ρ' m ↔ Interp Δ Γ t (Subst.lift_l l σ') ρ m :=
  ⟨fun H => Interp.unweak hΓ ht WΓ hρ H, fun H => H.weak' WΓ hρ⟩

/-- Directedness of a term's approximants **at one stage**: any two have a
well-formed upper bound that is again an approximant.

This is the other repo's `IsDirected` verbatim -- his conclusion is a
common upper bound *in the set*, not the join, and compatibility is a
consequence (`Compat.of_common_upper`) rather than a hypothesis.  Master's
`compat_join` states the derived `Compat ∧ join` form instead.

It is a property of a *stage*, not of a term-in-context: `SoundDir` is its
closure over well-formed stages, and the lemmas below take it as a
hypothesis so that they do not have to wait for soundness. -/
def Interp.Dir (Δ Γ : List Term) (t : Term) (σ : Subst) (ρ : Valuation) : Prop :=
  ∀ {{m₁ m₂}}, Interp Δ Γ t σ ρ m₁ → Interp Δ Γ t σ ρ m₂ →
    ∃ s, TShape.WF Δ s ∧ Interp Δ Γ t σ ρ s ∧ TShape.LE Δ m₁ s ∧ TShape.LE Δ m₂ s

/-- Directedness gives compatibility and the join, master's form. -/
theorem Interp.Dir.join {Δ Γ : List Term} {t σ ρ} (hΔ : ⊢ Δ)
    (h : Interp.Dir Δ Γ t σ ρ) {m₁ m₂}
    (h₁ : Interp Δ Γ t σ ρ m₁) (h₂ : Interp Δ Γ t σ ρ m₂) :
    TShape.Compat Δ m₁ m₂ ∧ Interp Δ Γ t σ ρ (m₁.join m₂) := by
  obtain ⟨s, hws, hs, hle₁, hle₂⟩ := h h₁ h₂
  have hc := TShape.Compat.of_common_upper hΔ hws hle₁ hle₂
  exact ⟨hc, hs.mono hΔ (TShape.WF.join hΔ hc h₁.wf h₂.wf) (TShape.join_le hΔ hle₁ hle₂)⟩

/-- Collect a per-element existential into a list of pairs. -/
theorem List.exists_pairs {α β : Type _} {P : α → β → Prop} :
    ∀ {g : List α}, (∀ e ∈ g, ∃ c, P e c) →
      ∃ g₀ : List (α × β), g₀.map Prod.fst = g ∧ ∀ p ∈ g₀, P p.1 p.2
  | [], _ => ⟨[], rfl, by simp⟩
  | e :: g, h => by
    obtain ⟨c, hc⟩ := h e (by simp)
    obtain ⟨g₀, hmap, hall⟩ := List.exists_pairs (g := g) (fun e' he' => h e' (by simp [he']))
    refine ⟨(e, c) :: g₀, by simp [hmap], fun p hp => ?_⟩
    match List.mem_cons.1 hp with
    | .inl h => exact h ▸ hc
    | .inr h => exact hall p h

/-! ### Merging valuations

The forward direction of term substitution reads one valuation out of
each subderivation and has to return a single one.  Valuations join
slotwise, and a slot's join is again an approximant of its `θ i` by that
term's directedness — which is why `substTerm` takes directedness of
every `θ i` as a hypothesis, and `inst` directedness of its argument. -/

def Valuation.join (ρ₁ ρ₂ : Valuation) : Valuation := fun i => (ρ₁ i).join (ρ₂ i)

/-- A valuation whose every slot approximates the corresponding `θ i`. -/
def Valuation.Approx (Δ Γ : List Term) (θ σ : Subst) (ρ ρ' : Valuation) : Prop :=
  ∀ i, Interp Δ Γ (θ i) σ ρ (ρ' i)

theorem Valuation.Approx.nil {Δ Γ : List Term} {θ σ ρ} :
    Valuation.Approx Δ Γ θ σ ρ Valuation.nil := fun _ => .bot

theorem Valuation.Approx.wf {Δ Γ : List Term} {θ σ ρ ρ'}
    (h : Valuation.Approx Δ Γ θ σ ρ ρ') : Valuation.WF Δ ρ' := fun i => (h i).wf

/-- Two approximating valuations join to one, slotwise. -/
theorem Valuation.Approx.join {Δ Γ : List Term} {θ σ ρ ρ₁ ρ₂} (hΔ : ⊢ Δ)
    (hθ : ∀ i, Interp.Dir Δ Γ (θ i) σ ρ)
    (h₁ : Valuation.Approx Δ Γ θ σ ρ ρ₁) (h₂ : Valuation.Approx Δ Γ θ σ ρ ρ₂) :
    Valuation.Approx Δ Γ θ σ ρ (ρ₁.join ρ₂) ∧
      Valuation.LE Δ ρ₁ (ρ₁.join ρ₂) ∧ Valuation.LE Δ ρ₂ (ρ₁.join ρ₂) := by
  have key : ∀ i, Interp Δ Γ (θ i) σ ρ ((ρ₁.join ρ₂) i) ∧
      TShape.LE Δ (ρ₁ i) ((ρ₁.join ρ₂) i) ∧ TShape.LE Δ (ρ₂ i) ((ρ₁.join ρ₂) i) := by
    intro i
    obtain ⟨hc, hj⟩ := (hθ i).join hΔ (h₁ i) (h₂ i)
    obtain ⟨hl₁, hl₂⟩ := TShape.le_join hΔ (h₁ i).wf (h₂ i).wf hc
    exact ⟨hj, hl₁, hl₂⟩
  exact ⟨fun i => (key i).1, fun i => (key i).2.1, fun i => (key i).2.2⟩

/-- And a list of them folds to one. -/
theorem Valuation.Approx.foldr {Δ Γ : List Term} {θ σ ρ} (hΔ : ⊢ Δ)
    (hθ : ∀ i, Interp.Dir Δ Γ (θ i) σ ρ) :
    ∀ {l : List Valuation}, (∀ ρ' ∈ l, Valuation.Approx Δ Γ θ σ ρ ρ') →
      Valuation.Approx Δ Γ θ σ ρ (l.foldr Valuation.join Valuation.nil) ∧
        ∀ ρ' ∈ l, Valuation.LE Δ ρ' (l.foldr Valuation.join Valuation.nil)
  | [], _ => ⟨Valuation.Approx.nil, by simp⟩
  | ρ₀ :: l, h => by
    obtain ⟨hrest, hle⟩ := Valuation.Approx.foldr (l := l) hΔ hθ
      (fun ρ' hρ' => h ρ' (by simp [hρ']))
    obtain ⟨hj, hl₁, hl₂⟩ :=
      Valuation.Approx.join hΔ hθ (h ρ₀ (by simp)) hrest
    refine ⟨hj, fun ρ' hρ' => ?_⟩
    match List.mem_cons.1 hρ' with
    | .inl rfl => exact hl₁
    | .inr hm => exact fun i => TShape.LE.trans hΔ (hle ρ' hm i) (hl₂ i)

/-- Directedness of a variable: the slot itself is the upper bound. -/
theorem Interp.Dir.bvar {Δ Γ : List Term} {i σ ρ} (hρ : TShape.WF Δ (ρ i)) :
    Interp.Dir Δ Γ (.bvar i) σ ρ := by
  intro m₁ m₂ h₁ h₂
  refine ⟨ρ i, hρ, .bvar hρ (TShape.LE.refl hρ), ?_, ?_⟩
  · cases h₁ with
    | bot => exact TShape.bot_le' rfl
    | bvar _ hle => exact hle
  · cases h₂ with
    | bot => exact TShape.bot_le' rfl
    | bvar _ hle => exact hle

/-- Directedness survives weakening: an approximant of `t↑` at an extended
stage is one of `t` at the old one, and back (`Interp.weak_iff`). -/
theorem Interp.Dir.weak {Δ Γ Γ' : List Term} {t T σ ρ x e} (hΓ : ⊢ Γ) (ht : Γ ⊢ t : T)
    (WΓ : Ctx.Lift' (.skip .refl) Γ Γ') (h : Interp.Dir Δ Γ t σ ρ) :
    Interp.Dir Δ Γ' t.lift (σ.cons e) (ρ.push x) := by
  intro m₁ m₂ h₁ h₂
  have hiff : ∀ {m}, Interp Δ Γ' t.lift (σ.cons e) (ρ.push x) m ↔
      Interp Δ Γ t σ ρ m := fun {_} => Interp.weak_iff hΓ ht WΓ (fun _ => rfl)
  obtain ⟨s, hws, hs, hs₁, hs₂⟩ := h (hiff.1 h₁) (hiff.1 h₂)
  exact ⟨s, hws, hiff.2 hs, hs₁, hs₂⟩

/-- **A transport computes only by K.**  If the endpoints are not
definitionally equal at the stage, the transport has no information —
the `tr` clause cannot fire and only `bot` is left.

This is the fact the old, context-free `LE_Interp` cannot state, and it
is what an adequacy proof needs: a *stuck* transport must not be given
the transported value's shapes, because no syntactic rule relates the
two.  Here the motive is read at the stage `σ.cons (b[σ])`, so `C[b]` is
pinned by the syntax of `b`, and the endpoints' equation can be demanded
alongside it. -/
theorem Interp.tr_bot_of_ne {Δ Γ : List Term} {r : Bool} {A a b C X H : Term} {σ ρ m}
    (h : Interp Δ Γ (.tr r A a b C X H) σ ρ m)
    (hne : ¬ (Δ ⊢ a.subst σ ≡ b.subst σ : A.subst σ)) : m.2 = Shape.bot := by
  cases h with
  | bot => rfl
  | tr _ _ _ _ _ _ _ _ _ _ _ _ heq => exact absurd heq hne

/-- The same example `LE_Interp.tr_stuck` settles the other way: the
transport `tr false nat zero (succ zero) nat zero h`, which no rule
computes, has only `⊥` here, because `zero ≢ succ zero`.  (That the
endpoints are not equal is `IsDefEq.sound`'s business, so it is a
hypothesis; the point is that the clause now *asks*.) -/
theorem Interp.tr_stuck_bot {Δ Γ : List Term} {σ ρ m H}
    (hne : ¬ (Δ ⊢ Term.zero ≡ Term.succ Term.zero : Term.nat))
    (h : Interp Δ Γ (.tr false .nat .zero (.succ .zero) .nat .zero H) σ ρ m) :
    m.2 = Shape.bot :=
  Interp.tr_bot_of_ne h (by simpa using hne)

/-- An approximant of a variable is below its slot. -/
theorem Interp.le_bvar {Δ Γ : List Term} {i σ ρ m}
    (H : Interp Δ Γ (.bvar i) σ ρ m) : TShape.LE Δ m (ρ i) := by
  cases H with
  | bot => exact TShape.bot_le' rfl
  | bvar _ h => exact h

/-- **A substitution the model can strengthen along**: every slot is
either typed in the target context or a variable.  `Subst.one a` is one
— slot `0` is the argument, the rest are variables — and lifting
preserves it, which is all the merges under a binder need.

The alternative would be a lemma saying an interpretation ignores the
slots past the end of its context; this is the same fact, in the form
the callers can hand over. -/
def Subst.Good (Γ' : List Term) (θ : Subst) : Prop :=
  ∀ i, (∃ T, Γ' ⊢ θ i : T) ∨ (∃ j, θ i = .bvar j)

theorem Subst.Good.lift {Γ' : List Term} {θ : Subst} {A : Term} (h : Subst.Good Γ' θ) :
    Subst.Good (A :: Γ') θ.lift := by
  intro i
  cases i with
  | zero => exact .inr ⟨0, rfl⟩
  | succ i =>
    match h i with
    | .inl ⟨T, hT⟩ => exact .inl ⟨T.lift, hT.weak' (Ctx.Lift'.skip (A := A) .refl)⟩
    | .inr ⟨j, hj⟩ => exact .inr ⟨j+1, by simp [Subst.lift, hj, Term.lift]⟩

theorem Subst.Good.one {Γ' : List Term} {a T : Term} (ha : Γ' ⊢ a : T) :
    Subst.Good Γ' (Subst.one a) := by
  intro i
  cases i with
  | zero => exact .inl ⟨T, ha⟩
  | succ i => exact .inr ⟨i, rfl⟩

/-- Strengthening at one such slot: typed slots go by `Interp.unweak`,
variables by hand — both sides of `Interp.bvar` say the same thing. -/
theorem Interp.unweak_slot {Δ Γ' Γ'' : List Term} {s : Term} (hΓ' : ⊢ Γ')
    (WΓ : Ctx.Lift' (.skip .refl) Γ' Γ'')
    (hs : (∃ T, Γ' ⊢ s : T) ∨ (∃ j, s = .bvar j))
    {σ e ρ x m} (H : Interp Δ Γ'' s.lift (σ.cons e) (ρ.push x) m) :
    Interp Δ Γ' s σ ρ m := by
  match hs with
  | .inl ⟨T, hT⟩ => exact Interp.unweak hΓ' hT WΓ (fun _ => rfl) H
  | .inr ⟨j, hj⟩ =>
    subst hj
    exact .bvar H.wf (by simpa using Interp.le_bvar (i := j+1) H)

/-- Directedness at a good slot, weakened. -/
theorem Interp.Dir.weak_slot {Δ Γ' Γ'' : List Term} {s : Term} (hΓ' : ⊢ Γ')
    (WΓ : Ctx.Lift' (.skip .refl) Γ' Γ'')
    (hs : (∃ T, Γ' ⊢ s : T) ∨ (∃ j, s = .bvar j))
    {σ e ρ x} (h : Interp.Dir Δ Γ' s σ ρ) :
    Interp.Dir Δ Γ'' s.lift (σ.cons e) (ρ.push x) := by
  intro m₁ m₂ h₁ h₂
  have hiff : ∀ {m}, Interp Δ Γ'' s.lift (σ.cons e) (ρ.push x) m ↔ Interp Δ Γ' s σ ρ m :=
    fun {_} => ⟨Interp.unweak_slot hΓ' WΓ hs, fun H => H.weak' WΓ (fun _ => rfl)⟩
  obtain ⟨s', hws, hs', hs₁, hs₂⟩ := h (hiff.1 h₁) (hiff.1 h₂)
  exact ⟨s', hws, hiff.2 hs', hs₁, hs₂⟩


/-- The merge under a binder, shared by every clause that has one: each
element of the list contributes a valuation whose slot `0` is the
binder's own and whose tail approximates `θ`, and the tails fold to one
valuation that serves them all. -/
theorem Interp.body_merge {Δ Γ Γ' Γ'' : List Term} {α : Type} {b : Term} {θ σ ρ} (hΔ : ⊢ Δ)
    (hΓ' : ⊢ Γ') (hgood : Subst.Good Γ' θ) (WΓ : Ctx.Lift' (.skip .refl) Γ' Γ'')
    (hθ : ∀ i, Interp.Dir Δ Γ' (θ i) σ ρ)
    {l : List α} {tm : α → Term} {inp out : α → TShape}
    (hwf : ∀ e ∈ l, TShape.WF Δ (inp e))
    (ih : ∀ {Γ₂ Γ₂' : List Term} {θ₂ σ₂ ρ₂ m₂}, (∀ i, Interp.Dir Δ Γ₂' (θ₂ i) σ₂ ρ₂) →
      Interp Δ Γ₂' (b.subst θ₂) σ₂ ρ₂ m₂ →
      ∃ ρ', Interp Δ Γ₂ b (θ₂.comp σ₂) ρ' m₂ ∧ Valuation.Approx Δ Γ₂' θ₂ σ₂ ρ₂ ρ')
    (hbody : ∀ e ∈ l, Interp Δ Γ'' (b.subst θ.lift) (σ.cons (tm e)) (ρ.push (inp e)) (out e)) :
    ∃ ρ', Valuation.Approx Δ Γ' θ σ ρ ρ' ∧
      ∀ e ∈ l, Interp Δ Γ b ((θ.comp σ).cons (tm e)) (ρ'.push (inp e)) (out e) := by
  -- the lifted substitution is directed at the extended stage
  have hθ' : ∀ (e : α), e ∈ l → ∀ i,
      Interp.Dir Δ Γ'' (θ.lift i) (σ.cons (tm e)) (ρ.push (inp e)) := by
    intro e he i
    cases i with
    | zero => exact Interp.Dir.bvar (ρ := ρ.push (inp e)) (i := 0) (hwf e he)
    | succ i => exact Interp.Dir.weak_slot hΓ' WΓ (hgood i) (hθ i)
  -- one valuation per element, by the induction hypothesis
  obtain ⟨ps, hps, hall⟩ := List.exists_pairs (β := Valuation)
    (P := fun e ρ'' => Interp Δ Γ b ((θ.lift).comp (σ.cons (tm e))) ρ'' (out e) ∧
      Valuation.Approx Δ Γ'' θ.lift (σ.cons (tm e)) (ρ.push (inp e)) ρ'')
    (fun e he => ih (hθ' e he) (hbody e he))
  -- their tails approximate `θ` at the outer stage, and fold to one
  have htail : ∀ ρ'' ∈ ps.map (fun p => Valuation.tail p.2),
      Valuation.Approx Δ Γ' θ σ ρ ρ'' := by
    intro ρ'' hρ''
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hρ''
    exact fun i => Interp.unweak_slot hΓ' WΓ (hgood i) ((hall p hp).2 (i+1))
  obtain ⟨hAj, hles⟩ := Valuation.Approx.foldr hΔ hθ htail
  refine ⟨_, hAj, fun e he => ?_⟩
  -- the element's own valuation is below the fold, slot by slot
  obtain ⟨p, hp, rfl⟩ : ∃ p ∈ ps, p.1 = e := by
    have : e ∈ ps.map Prod.fst := hps ▸ he
    obtain ⟨p, hp, hpe⟩ := List.mem_map.1 this
    exact ⟨p, hp, hpe⟩
  have hzero : TShape.LE Δ (p.2 0) (inp p.1) :=
    Interp.le_bvar (Γ := Γ'') (i := 0) (σ := σ.cons (tm p.1)) ((hall p hp).2 0)
  refine Interp.mono_val hΔ (fun i => ?_)
    (Subst.lift_comp_cons (θ := θ) (σ := σ) (e := tm p.1) ▸ (hall p hp).1)
  cases i with
  | zero => exact hzero
  | succ i => exact hles _ (List.mem_map.2 ⟨p, hp, rfl⟩) i

/-- The same merge without a binder: several approximants of one
subterm, one valuation for all of them. -/
theorem Interp.list_merge {Δ Γ Γ' : List Term} {α : Type} {t : Term} {θ σ ρ} (hΔ : ⊢ Δ)
    (hθ : ∀ i, Interp.Dir Δ Γ' (θ i) σ ρ)
    {l : List α} {out : α → TShape}
    (ih : ∀ {Γ₂ Γ₂' : List Term} {θ₂ σ₂ ρ₂ m₂}, (∀ i, Interp.Dir Δ Γ₂' (θ₂ i) σ₂ ρ₂) →
      Interp Δ Γ₂' (t.subst θ₂) σ₂ ρ₂ m₂ →
      ∃ ρ', Interp Δ Γ₂ t (θ₂.comp σ₂) ρ' m₂ ∧ Valuation.Approx Δ Γ₂' θ₂ σ₂ ρ₂ ρ')
    (hl : ∀ e ∈ l, Interp Δ Γ' (t.subst θ) σ ρ (out e)) :
    ∃ ρ', Valuation.Approx Δ Γ' θ σ ρ ρ' ∧
      ∀ e ∈ l, Interp Δ Γ t (θ.comp σ) ρ' (out e) := by
  obtain ⟨ps, hps, hall⟩ := List.exists_pairs (β := Valuation)
    (P := fun e ρ'' => Interp Δ Γ t (θ.comp σ) ρ'' (out e) ∧
      Valuation.Approx Δ Γ' θ σ ρ ρ'')
    (fun e he => ih hθ (hl e he))
  obtain ⟨hAj, hles⟩ := Valuation.Approx.foldr (l := ps.map Prod.snd) hΔ hθ (by
    intro ρ'' hρ''
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hρ''
    exact (hall p hp).2)
  refine ⟨_, hAj, fun e he => ?_⟩
  obtain ⟨p, hp, rfl⟩ : ∃ p ∈ ps, p.1 = e := by
    have : e ∈ ps.map Prod.fst := hps ▸ he
    obtain ⟨p, hp, hpe⟩ := List.mem_map.1 this
    exact ⟨p, hp, hpe⟩
  exact Interp.mono_val hΔ (hles _ (List.mem_map.2 ⟨p, hp, rfl⟩)) (hall p hp).1

/-- **Substitution in the term, the analytic direction.**  An approximant
of `t[θ]` is an approximant of `t` at the composed stage, under *some*
valuation whose slots approximate the `θ i`.

With the clauses typed this is a statement about a **typed** `t`: the
interpretation it builds is of `t` in `Γ`, so every clause needs `Γ`'s
typings, and only a typing derivation has them.  So the induction moves
from the term to the typing — the same move as `Interp.unweak` and
`IsDefEq.stage`.  The `bvar` case is still where the valuation is built
(slot `i` holds the approximant, every other slot `⊥`), the merges are
still `Valuation.Approx.foldr` with `body_merge`/`list_merge` under
binders, and `Y` still needs its own induction on the tower.

`Subst.Good` is what the merges need: past the end of `Γ` the slots are
variables, and those strengthen by hand. -/
theorem Interp.to_substTerm {Δ : List Term} (hΔ : ⊢ Δ) :
    ∀ {t T : Term} {Γ Γ' : List Term} {θ σ ρ m}, ⊢ Γ → (Γ ⊢ t : T) → ⊢ Γ' →
      Subst.Good Γ' θ → Ctx.SubstEq Γ' θ θ Γ →
      (∀ i, Interp.Dir Δ Γ' (θ i) σ ρ) →
      Interp Δ Γ' (t.subst θ) σ ρ m →
      ∃ ρ', Interp Δ Γ t (θ.comp σ) ρ' m ∧ Valuation.Approx Δ Γ' θ σ ρ ρ' := by
  sorry

/-- Substitution in the **term**, in master's `∃ ρ'` form.  A substitution
`θ` from `Γ` into `Γ'` turns an approximant of `t[θ]` into an approximant
of `t` under a valuation whose slots approximate the `θ i`, with the stage
moving from `σ` to `θ.comp σ` — the one place the two kinds of
substitution meet.

The `←` direction needs `Interp.weak'` (the `lam` case gains a valuation
slot) and none of the hypotheses.  The `→` direction merges the valuations
that several subderivations return, one slot at a time, which is what
`hθ` is for: master uses its global `compat_join` there, and we take
directedness of each `θ i` as a hypothesis so that this lemma does not
have to wait for soundness.  Labels need no stage lemma: `A[θ ∘ σ]` and
`A[θ][σ]` are equal on the nose (`subst_subst`). -/
theorem Interp.substTerm {T : Term} (hΔ : ⊢ Δ) {θ : Subst} (hΓ : ⊢ Γ) (ht : Γ ⊢ t : T)
    (hΓ' : ⊢ Γ') (hgood : Subst.Good Γ' θ) (Wθ : Ctx.SubstEq Γ' θ θ Γ)
    (hθ : ∀ i, Interp.Dir Δ Γ' (θ i) σ ρ) :
    Interp Δ Γ' (t.subst θ) σ ρ m ↔
    ∃ ρ', Interp Δ Γ t (θ.comp σ) ρ' m ∧ ∀ i, Interp Δ Γ' (θ i) σ ρ (ρ' i) :=
  ⟨Interp.to_substTerm hΔ hΓ ht hΓ' hgood Wθ hθ,
    fun ⟨_, h, hs⟩ => Interp.of_substTerm hΔ h hΓ' Wθ rfl hs⟩

/-- The single-substitution form, which is what `beta` uses: `b[a]` at
stage `σ` is `b` at the stage extended by `a[σ]`, under the valuation
extended by an approximant of `a`.  Master's `LE_Interp.inst`. -/
theorem Interp.inst {B : Term} (hΔ : ⊢ Δ) (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u)
    (hat : Γ ⊢ a : A) (hb : A :: Γ ⊢ b : B)
    (ha : Interp.Dir Δ Γ a σ ρ) (hρ : Valuation.WF Δ ρ) :
    Interp Δ Γ (b.inst a) σ ρ m ↔
    ∃ x, Interp Δ (A :: Γ) b ((Subst.one a).comp σ) (ρ.push x) m ∧ Interp Δ Γ a σ ρ x :=
  -- at `θ = one a`: slot `0` holds the argument's approximant and slot
  -- `i+1` the valuation's own, and `Subst.Good` holds for just that reason
  have hgood : Subst.Good Γ (Subst.one a) := Subst.Good.one hat
  have Wθ : Ctx.SubstEq Γ (Subst.one a) (Subst.one a) (A :: Γ) := by
    refine .cons ?_ hA ?_
    · simpa [Subst.one] using Ctx.SubstEq.id hΓ
    · simpa [Subst.one, subst_id] using hat
  ⟨fun h => by
    obtain ⟨ρ', hb', hs⟩ := Interp.to_substTerm (Γ := A :: Γ) hΔ ⟨hΓ, _, hA⟩ hb hΓ hgood Wθ
      (fun i => by
        cases i with
        | zero => exact ha
        | succ i => exact Interp.Dir.bvar (hρ i)) h
    refine ⟨ρ' 0, Interp.mono_val hΔ (fun i => ?_) hb', hs 0⟩
    cases i with
    | zero => exact TShape.LE.refl (hs 0).wf
    | succ i => exact Interp.le_bvar (Γ := Γ) (i := i) (σ := σ) (hs (i+1))
  , fun ⟨x, hb', hx⟩ => Interp.of_substTerm hΔ hb' hΓ Wθ rfl (fun i => by
    cases i with
    | zero => exact hx
    | succ i => exact .bvar (hρ i) (TShape.LE.refl (hρ i)))⟩

-- Stage invariance under a definitionally equal stage is **not** a lemma
-- about `Interp`: for a raw `t` it is false.  Take `t = .forallE A B` with
-- `A` ill-typed in `Γ` but `A[σ]` typed in `Δ`; the `forallE` rule holds
-- with label `A[σ]`, and nothing relates `A[σ']` to it, because no rule
-- types a label in `Γ` -- `hlab` types it in `Δ`.  So the statement has to
-- be indexed by a typing derivation of `t`, and it lives with soundness as
-- `IsDefEq.stage` (`Presheaf.lean`).

/-- The interpretation is closed under moving a shape up a level.  A shape
and its lift are equivalent in the order and `Interp` is downward closed,
so this is `Interp.mono` in one line — and it is what lets a proof
normalise every shape to a common level before applying a typing lemma,
whose transport only goes up. -/
theorem Interp.lift {Δ Γ : List Term} {t σ ρ} {m : TShape} (hΔ : ⊢ Δ) {k}
    (hk : m.1 ≤ k) (H : Interp Δ Γ t σ ρ m) : Interp Δ Γ t σ ρ (m.lift k) :=
  H.mono hΔ (TShape.WF.lift hk H.wf) (TShape.LE.lift_le hΔ hk H.wf)
