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
      Interp Δ Γ (.snd p) σ ρ m
  /-- The equation is what the `succ` branch also carries, and for the same
  reason: the *type* of a `natCase` is `C[M]`, and the branch's value is
  typed at `C[zero]`, so soundness needs the two stages to be one.  The
  shape `M ↦ zero` is semantic information; only the equation is syntax. -/
  | natCase_zero :
    Interp Δ Γ M σ ρ .zero →
    Δ ⊢ M.subst σ ≡ .zero : .nat →
    Interp Δ Γ a σ ρ m →
    Interp Δ Γ (.natCase C M a b) σ ρ m
  /-- There is no syntactic predecessor former, so the label term for the
  body's binder is supplied as a premise, together with the definitional
  equation that makes it the right one. -/
  | natCase_succ {n} {v : Shape n} {t : Term} :
    Interp Δ Γ M σ ρ (Shape.T (n := n+1) v.succ) →
    Shape.WF Δ v →
    Δ ⊢ M.subst σ ≡ .succ t : .nat →
    Interp Δ (.nat :: Γ) b (σ.cons t) (ρ.push v.T) m →
    Interp Δ Γ (.natCase C M a b) σ ρ m
  /-- The fixed point is a least fixed point for free: the constructor
  refers to the relation it is defining, so only finitely many unfoldings
  can ever produce a given approximant. -/
  | protected Y {A b : Term} {x : TShape} :
    Interp Δ Γ (.Y A b) σ ρ x →
    TShape.WF Δ x →
    Interp Δ (A :: Γ) b (σ.cons ((A.Y b).subst σ)) (ρ.push x) m →
    Interp Δ Γ (.Y A b) σ ρ m
  /-- The identity type is **label-only**: no sub-shapes, so the shape
  records nothing but the syntax. -/
  | id : TShape.WF Δ m →
    TShape.LE Δ m (Shape.T (n := 1) (.id r (A.subst σ) (a.subst σ) (b.subst σ))) →
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
  | natCase_zero _ _ _ _ hw | natCase_succ _ _ _ _ _ hw
  | Y _ _ _ _ hw => exact hw

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
  | app hF ha hev _ h1 => exact .app hF ha hev hw (TShape.LE.trans hΔ h h1)
  | lam hA hd hwf hdom hbody _ h1 =>
    exact .lam hA hd hwf hdom hbody hw (TShape.LE.trans hΔ h h1)
  | forallE hA hd hwf hlab hdom hbody _ h1 =>
    exact .forallE hA hd hwf hlab hdom hbody hw (TShape.LE.trans hΔ h h1)
  | sigma hA hd hwf hlab hdom hbody _ h1 =>
    exact .sigma hA hd hwf hlab hdom hbody hw (TShape.LE.trans hΔ h h1)
  | pair ha hA hd hwf hlab hdom hinp hout hbody hty _ h1 =>
    exact .pair ha hA hd hwf hlab hdom hinp hout hbody hty hw (TShape.LE.trans hΔ h h1)
  | fst hp _ h1 => exact .fst hp hw (TShape.LE.trans hΔ h h1)
  | snd hp hq _ h1 => exact .snd hp hq hw (TShape.LE.trans hΔ h h1)
  | natCase_zero hM hz _ _ iha => exact .natCase_zero hM hz (iha hw h)
  | natCase_succ hM hwv heq _ _ ihb => exact .natCase_succ hM hwv heq (ihb hw h)
  | Y hself hwx _ _ ihb => exact .Y hself hwx (ihb hw h)
  | id _ h1 => exact .id hw (TShape.LE.trans hΔ h h1)
  | refl hv _ h1 => exact .refl hv hw (TShape.LE.trans hΔ h h1)
  | tr _ hle hX ha hb hA hwv hvA hC hcb hm' hH heq _ _ _ _ _ _ =>
    exact .tr hw (TShape.LE.trans hΔ h hle) hX ha hb hA hwv hvA hC hcb hm' hH heq

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
  | app _ _ hev hw h1 ihF iha => exact .app (ihF hρ) (iha hρ) hev hw h1
  | lam _ hd hwf hdom _ hw h1 ihA ihbody =>
    refine .lam (ihA hρ) hd hwf hdom (fun e he => ?_) hw h1
    exact ihbody e he (Valuation.LE.push.2 ⟨hρ, .refl (hwf.2.2.1.1 e he).2.2.1⟩)
  | forallE _ hd hwf hlab hdom _ hw h1 ihA ihbody =>
    refine .forallE (ihA hρ) hd hwf hlab hdom (fun e he => ?_) hw h1
    exact ihbody e he (Valuation.LE.push.2 ⟨hρ, .refl (hwf.2.2.2.1 e he).2.2.1⟩)
  | sigma _ hd hwf hlab hdom _ hw h1 ihA ihbody =>
    exact .sigma (ihA hρ) hd hwf hlab hdom (fun e he => ihbody e he
      (Valuation.LE.push.2 ⟨hρ, TShape.LE.refl (a := Shape.T e.inp)
        (hwf.2.2.2.1 e he).2.2.1⟩)) hw h1
  | pair _ _ hd hwf hlab hdom _ _ hbody hty hw h1 iha ihA ihinp ihout ihbody =>
    exact .pair (iha hρ) (ihA hρ) hd hwf hlab hdom (fun e he => ihinp e he hρ)
      (fun e he => ihout e he hρ)
      (fun e he => ihbody e he (Valuation.LE.push.2 ⟨hρ, TShape.LE.refl
        (a := e.1.inp.T) (hwf.2.2.1.1 _ (List.mem_map.2 ⟨e, he, rfl⟩)).2.2.1⟩)) hty hw h1
  | fst _ hw h1 ihp => exact .fst (ihp hρ) hw h1
  | snd _ hq hw h1 ihp => exact .snd (ihp hρ) hq hw h1
  | natCase_zero _ hz _ ihM iha => exact .natCase_zero (ihM hρ) hz (iha hρ)
  | natCase_succ _ hwv heq _ ihM ihb =>
    refine .natCase_succ (ihM hρ) hwv heq ?_
    exact ihb (Valuation.LE.push.2 ⟨hρ, .refl (a := Shape.T _) hwv⟩)
  | Y _ hwx _ ihself ihb =>
    exact .Y (ihself hρ) hwx (ihb (Valuation.LE.push.2 ⟨hρ, .refl hwx⟩))
  | id hw h1 => exact .id hw h1
  | refl _ hw h1 ihv => exact .refl (ihv hρ) hw h1
  | tr hw hle _ _ _ _ hwv hvA _ hcb hm' _ heq ihX iha ihb ihA ihC ihH =>
    refine .tr hw hle (ihX hρ) (iha hρ) (ihb hρ) (ihA hρ) hwv hvA ?_ hcb hm'
      (fun hr => ihH hr hρ) heq
    exact ihC (Valuation.LE.push.2 ⟨hρ, .refl hwv⟩)

/-- The term's own context is not load-bearing: no rule mentions `Γ`
except to thread it, so an interpretation may be read at any context.  The
binder congruences need this, to move a body's interpretation from
`A :: Γ` to `A' :: Γ` after the domain has changed. -/
theorem Interp.ctx {Δ Γ : List Term} {t σ ρ m} (H : Interp Δ Γ t σ ρ m) :
    ∀ {Γ' : List Term}, Interp Δ Γ' t σ ρ m := by
  induction H with
  | bot => exact .bot
  | bvar hw h => exact .bvar hw h
  | sort hw h => exact .sort hw h
  | unit hw h => exact .unit hw h
  | nat hw h => exact .nat hw h
  | zero hw h => exact .zero hw h
  | succ _ hw h ih => exact .succ ih hw h
  | app _ _ hev hw h ihF iha => exact .app ihF iha hev hw h
  | lam _ hd hwf hdom _ hw h ihA ihbody =>
    exact .lam ihA hd hwf hdom (fun e he => ihbody e he) hw h
  | forallE _ hd hwf hlab hdom _ hw h ihA ihbody =>
    exact .forallE ihA hd hwf hlab hdom (fun e he => ihbody e he) hw h
  | sigma _ hd hwf hlab hdom _ hw h ihA ihbody =>
    exact .sigma ihA hd hwf hlab hdom (fun e he => ihbody e he) hw h
  | pair _ _ hd hwf hlab hdom _ _ hbody hty hw h iha ihA ihinp ihout ihbody =>
    exact .pair iha ihA hd hwf hlab hdom (fun e he => ihinp e he) (fun e he => ihout e he)
      (fun e he => ihbody e he) hty hw h
  | fst _ hw h ihp => exact .fst ihp hw h
  | snd _ hq hw h ihp => exact .snd ihp hq hw h
  | natCase_zero _ hz _ ihM iha => exact .natCase_zero ihM hz iha
  | natCase_succ _ hwv heq _ ihM ihb => exact .natCase_succ ihM hwv heq ihb
  | Y _ hwx _ ihself ihb => exact .Y ihself hwx ihb
  | id hw h => exact .id hw h
  | refl _ hw h ihv => exact .refl ihv hw h
  | tr hw hle _ _ _ _ hwv hvA _ hcb hm' _ heq ihX iha ihb ihA ihC ihH =>
    exact .tr hw hle ihX iha ihb ihA hwv hvA ihC hcb hm' (fun hr => ihH hr) heq

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
    (hB : A.subst σ :: Δ ⊢ B.subst σ.lift : .sort v) :
    Interp Δ Γ (.forallE A B) σ ρ (Shape.T (n := 1) (.piAtom (A.subst σ) (B.subst σ.lift))) :=
  .forallE (d := (Shape.bot : Shape 0)) .bot (.bot .sort)
    (Shape.WF.piAtom hA hB) nofun nofun nofun
    (.piAtom hA hB) (TShape.LE.T.2 (.refl (.piAtom hA hB)))

/-- And the probe reports: if the atom approximates `⟦forallE A B⟧`, its
label is definitionally the Π's own label.  Π-injectivity is this plus
soundness, with no adequacy in between. -/
theorem Interp.le_piAtom (H : Interp Δ Γ (.forallE A B) σ ρ (Shape.T (n := 1) (.piAtom A' B'))) :
    PiLabelEq Δ A' B' (A.subst σ) (B.subst σ.lift) := by
  cases H with | forallE _ _ _ _ _ _ _ h
  have h' := (TShape.LE.def_mp (Nat.succ_le_succ (Nat.zero_le _)) (Nat.le_refl _)) h
  rw [Shape.lift_piAtom, Shape.lift_self] at h'
  exact Shape.piAtom_le_forallE h'

/-- The Σ probe, as `piAtom`. -/
theorem Interp.sigmaAtom (hA : Δ ⊢ A.subst σ : .sort u)
    (hB : A.subst σ :: Δ ⊢ B.subst σ.lift : .sort v) :
    Interp Δ Γ (.sigma A B) σ ρ (Shape.T (n := 1) (.sigmaAtom (A.subst σ) (B.subst σ.lift))) :=
  .sigma (d := (Shape.bot : Shape 0)) .bot (.bot .sort)
    (Shape.WF.sigmaAtom hA hB) nofun nofun nofun
    (.sigmaAtom hA hB) (TShape.LE.T.2 (.refl (.sigmaAtom hA hB)))

theorem Interp.le_sigmaAtom
    (H : Interp Δ Γ (.sigma A B) σ ρ (Shape.T (n := 1) (.sigmaAtom A' B'))) :
    PiLabelEq Δ A' B' (A.subst σ) (B.subst σ.lift) := by
  cases H with | sigma _ _ _ _ _ _ _ h
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
  | app _ _ hev hw h1 ihF iha =>
    have hev' := TEvaluates.subst hΘ W hev
    rw [subst_subst] at hev'
    exact .app (ihF hΘ W) (iha hΘ W) hev' (hw.subst hΘ W) (h1.subst hΘ W)
  | lam _ hd hwf hdom _ hw h1 ihA ihbody =>
    have hwf' := hwf.subst hΘ W; have h1' := h1.subst hΘ W
    rw [Shape.subst, subst_subst] at hwf'
    simp only [TShape.subst_T, Shape.subst, subst_subst] at h1'
    refine .lam (ihA hΘ W) (TShape.HasType.subst hΘ W hd) hwf' ?_ ?_
      (hw.subst hΘ W) h1'
    · intro e' he'
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      exact TShape.HasType.subst hΘ W (hdom e he)
    · intro e' he'
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have := ihbody e he hΘ W
      rwa [Subst.cons_comp, Valuation.subst_push, TShape.subst_T] at this
  | forallE _ hd hwf hlab hdom _ hw h1 ihA ihbody =>
    have hwf' := hwf.subst hΘ W
    have h1' := h1.subst hΘ W
    simp only [TShape.subst_T, Shape.subst, subst_subst, ← Subst.comp_lift] at hwf' h1'
    refine .forallE (ihA hΘ W) (TShape.HasType.subst hΘ W hd) hwf' (fun e' he' => ?_) (fun e' he' => ?_)
      (fun e' he' => ?_) (hw.subst hΘ W) h1'
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have ⟨u, hu⟩ := hlab e he
      exact ⟨u, by rw [← subst_subst]; exact hu.subst hΘ W⟩
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      exact TShape.HasType.subst hΘ W (hdom e he)
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have := ihbody e he hΘ W
      rwa [Subst.cons_comp, Valuation.subst_push, TShape.subst_T] at this
  | sigma _ hd hwf hlab hdom _ hw h1 ihA ihbody =>
    have hwf' := hwf.subst hΘ W
    have h1' := h1.subst hΘ W
    simp only [TShape.subst_T, Shape.subst, subst_subst, ← Subst.comp_lift] at hwf' h1'
    refine .sigma (ihA hΘ W) (TShape.HasType.subst hΘ W hd) hwf' (fun e' he' => ?_) (fun e' he' => ?_)
      (fun e' he' => ?_) (hw.subst hΘ W) h1'
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have ⟨u, hu⟩ := hlab e he
      exact ⟨u, by rw [← subst_subst]; exact hu.subst hΘ W⟩
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      exact TShape.HasType.subst hΘ W (hdom e he)
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have := ihbody e he hΘ W
      rwa [Subst.cons_comp, Valuation.subst_push, TShape.subst_T] at this
  | @pair _ _ _ _ _ _ g₀ _ _ _ _ _ ha hA hd hwf hlab hdom hinp hout hbody hty hw h1
      iha ihA ihinp ihout ihbody =>
    have hwf' := hwf.subst hΘ W
    have h1' := h1.subst hΘ W
    simp only [TShape.subst_T, Shape.subst, subst_subst, ShapeFun.subst,
      List.map_map, Function.comp_def] at hwf' h1'
    refine .pair (g₀ := g₀.map fun p =>
        (⟨p.1.ty.subst τ, p.1.tm.subst τ, p.1.inp.subst τ, p.1.out.subst τ⟩, p.2.subst τ))
      (iha hΘ W) (ihA hΘ W) (TShape.HasType.subst hΘ W hd) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (hw.subst hΘ W) ?_
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
  | snd _ hq hw h1 ihp =>
    have hq' := hq.subst hΘ W
    rw [subst_subst] at hq'
    exact .snd (ihp hΘ W) hq' (hw.subst hΘ W) (h1.subst hΘ W)
  | natCase_zero _ hz _ ihM iha =>
    have hz' := hz.subst hΘ W
    rw [subst_subst] at hz'
    exact .natCase_zero (ihM hΘ W) hz' (iha hΘ W)
  | natCase_succ _ hwv heq _ ihM ihb =>
    have heq' := heq.subst hΘ W
    rw [subst_subst] at heq'
    refine .natCase_succ (ihM hΘ W) (hwv.subst hΘ W) heq' ?_
    have := ihb hΘ W
    rwa [Subst.cons_comp, Valuation.subst_push, TShape.subst_T] at this
  | Y _ hwx _ ihself ihb =>
    refine .Y (ihself hΘ W) (hwx.subst hΘ W) ?_
    have := ihb hΘ W
    rwa [Subst.cons_comp, subst_subst, Valuation.subst_push] at this
  | id hw h1 =>
    have := h1.subst hΘ W
    simp only [TShape.subst_T, Shape.subst, subst_subst] at this
    exact .id (hw.subst hΘ W) this
  | refl _ hw h1 ihv => exact .refl (ihv hΘ W) (hw.subst hΘ W) (h1.subst hΘ W)
  | tr hw hle _ _ _ _ hwv hvA _ hcb hm' _ heq ihX iha ihb ihA ihC ihH =>
    have heq' := heq.subst hΘ W
    rw [subst_subst, subst_subst, subst_subst] at heq'
    refine .tr (hw.subst hΘ W) (hle.subst hΘ W) (ihX hΘ W) (iha hΘ W) (ihb hΘ W) (ihA hΘ W)
      (hwv.subst hΘ W) (hvA.subst hΘ W) ?_ (hcb.subst hΘ W) (hm'.subst hΘ W)
      (fun hr => ihH hr hΘ W) heq'
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
    {Γ' ρ'} (hρ : ∀ i, ρ i = ρ' (Lift.liftVar l i)) :
    Interp Δ Γ' (t.lift' l) σ' ρ' m := by
  generalize hσ : Subst.lift_l l σ' = σ at H
  induction H generalizing Γ' l σ' ρ' with subst hσ
  | bot => exact .bot
  | bvar hw h1 => exact .bvar hw (hρ _ ▸ h1)
  | sort hw h1 => exact .sort hw h1
  | unit hw h1 => exact .unit hw h1
  | nat hw h1 => exact .nat hw h1
  | zero hw h1 => exact .zero hw h1
  | succ _ hw h1 ihv => exact .succ (ihv hρ rfl) hw h1
  | app _ _ hev hw h1 ihF iha =>
    rw [← subst_lift'] at hev
    exact .app (ihF hρ rfl) (iha hρ rfl) hev hw h1
  | lam _ hd hwf hdom _ hw h1 ihA ihbody =>
    rw [← subst_lift'] at hwf h1
    refine .lam (ihA hρ rfl) hd hwf hdom ?_ hw h1
    intro e he
    refine ihbody e he (l := l.cons) (fun i => ?_) Subst.lift_l_cons.symm
    cases i <;> simp_all [Valuation.push]
  | forallE _ hd hwf hlab hdom _ hw h1 ihA ihbody =>
    rw [Subst.lift_l_lift, ← subst_lift', ← subst_lift'] at hwf h1
    refine .forallE (ihA hρ rfl) hd hwf ?_ hdom ?_ hw h1
    · intro e he
      have ⟨u, hu⟩ := hlab e he
      exact ⟨u, by rwa [subst_lift']⟩
    · intro e he
      refine ihbody e he (l := l.cons) (fun i => ?_) Subst.lift_l_cons.symm
      cases i <;> simp_all [Valuation.push]
  | sigma _ hd hwf hlab hdom _ hw h1 ihA ihbody =>
    rw [Subst.lift_l_lift, ← subst_lift', ← subst_lift'] at hwf h1
    refine .sigma (ihA hρ rfl) hd hwf ?_ hdom ?_ hw h1
    · intro e he
      have ⟨u, hu⟩ := hlab e he
      exact ⟨u, by rwa [subst_lift']⟩
    · intro e he
      refine ihbody e he (l := l.cons) (fun i => ?_) Subst.lift_l_cons.symm
      cases i <;> simp_all [Valuation.push]
  | pair _ _ hd hwf hlab hdom _ _ hbody hty hw h1 iha ihA ihinp ihout ihbody =>
    rw [← subst_lift'] at hwf h1 hlab
    refine .pair (iha hρ rfl) (ihA hρ rfl) hd hwf hlab hdom (fun e he => ihinp e he hρ rfl)
      (fun e he => ihout e he hρ rfl) (fun e he => ?_) hty hw h1
    refine ihbody e he (l := l.cons) (fun i => ?_) Subst.lift_l_cons.symm
    cases i <;> simp_all [Valuation.push]
  | fst _ hw h1 ihp => exact .fst (ihp hρ rfl) hw h1
  | snd _ hq hw h1 ihp =>
    rw [← subst_lift'] at hq
    exact .snd (ihp hρ rfl) hq hw h1
  | natCase_zero _ hz _ ihM iha =>
    rw [← subst_lift'] at hz
    exact .natCase_zero (ihM hρ rfl) hz (iha hρ rfl)
  | natCase_succ _ hwv heq _ ihM ihb =>
    rw [← subst_lift'] at heq
    refine .natCase_succ (ihM hρ rfl) hwv heq ?_
    refine ihb (l := l.cons) (fun i => ?_) Subst.lift_l_cons.symm
    cases i <;> simp_all [Valuation.push]
  | Y _ hwx _ ihself ihb =>
    refine .Y (ihself hρ rfl) hwx ?_
    refine ihb (l := l.cons) (fun i => ?_) ?_
    · cases i <;> simp_all [Valuation.push]
    · rw [← Subst.lift_l_cons]
      exact congrArg _ (subst_lift' (e := Term.Y _ _))
  | id hw h1 =>
    simp only [← subst_lift'] at h1
    exact .id hw h1
  | refl _ hw h1 ihv => exact .refl (ihv hρ rfl) hw h1
  | tr hw hle _ _ _ _ hwv hvA _ hcb hm' _ heq ihX iha ihb ihA ihC ihH =>
    rw [← subst_lift', ← subst_lift', ← subst_lift'] at heq
    refine .tr hw hle (ihX hρ rfl) (iha hρ rfl) (ihb hρ rfl) (ihA hρ rfl) hwv hvA ?_ hcb hm'
      (fun hr => ihH hr hρ rfl) heq
    refine ihC (l := l.cons) (fun i => ?_) ?_
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
    ∀ {Γ' : List Term} {θ σ ρ}, τ = θ.comp σ →
      (∀ i, Interp Δ Γ' (θ i) σ ρ (ρ' i)) →
      Interp Δ Γ' (t.subst θ) σ ρ m := by
  induction H with
  | bot => intro _ _ _ _ _ _; exact .bot
  | bvar hw h1 => intro _ _ _ _ _ hθ; exact Interp.mono hΔ hw h1 (hθ _)
  | sort hw h1 => intro _ _ _ _ _ _; exact .sort hw h1
  | unit hw h1 => intro _ _ _ _ _ _; exact .unit hw h1
  | nat hw h1 => intro _ _ _ _ _ _; exact .nat hw h1
  | zero hw h1 => intro _ _ _ _ _ _; exact .zero hw h1
  | succ _ hw h1 ihv => intro _ _ _ _ hτ hθ; exact .succ (ihv hτ hθ) hw h1
  | app _ _ hev hw h1 ihF iha =>
    intro _ _ _ _ hτ hθ
    subst hτ
    rw [← subst_subst] at hev
    exact .app (ihF rfl hθ) (iha rfl hθ) hev hw h1
  | @lam _ _ _ _ _ _ _ _ _ hA hd hwf hdom hbody hw h1 ihA ihbody =>
    intro Γ' θ σ ρ hτ hθ
    subst hτ
    rw [← subst_subst] at hwf h1
    refine .lam (ihA rfl hθ) hd hwf hdom (fun e he => ?_) hw h1
    refine ihbody e he (θ := θ.lift) Subst.lift_comp_cons.symm (fun i => ?_)
    cases i with
    | zero => exact .bvar (hwf.2.2.1.1 e he).2.2.1 (TShape.LE.refl (hwf.2.2.1.1 e he).2.2.1)
    | succ i => exact Interp.weak' (l := .skip .refl) (hθ i) (fun _ => rfl)
  | @forallE _ _ _ _ _ _ _ _ _ hA hd hwf hlab hdom hbody hw h1 ihA ihbody =>
    intro Γ' θ σ ρ hτ hθ
    subst hτ
    rw [Subst.comp_lift, ← subst_subst, ← subst_subst] at hwf h1
    refine .forallE (ihA rfl hθ) hd hwf (fun e he => ?_) hdom (fun e he => ?_) hw h1
    · obtain ⟨u, hu⟩ := hlab e he
      exact ⟨u, by rwa [← subst_subst] at hu⟩
    · refine ihbody e he (θ := θ.lift) Subst.lift_comp_cons.symm (fun i => ?_)
      cases i with
      | zero =>
        exact .bvar (hwf.2.2.2.1 e he).2.2.1 (TShape.LE.refl (hwf.2.2.2.1 e he).2.2.1)
      | succ i => exact Interp.weak' (l := .skip .refl) (hθ i) (fun _ => rfl)
  | @sigma _ _ _ _ _ _ _ _ _ hA hd hwf hlab hdom hbody hw h1 ihA ihbody =>
    intro Γ' θ σ ρ hτ hθ
    subst hτ
    rw [Subst.comp_lift, ← subst_subst, ← subst_subst] at hwf h1
    refine .sigma (ihA rfl hθ) hd hwf (fun e he => ?_) hdom (fun e he => ?_) hw h1
    · obtain ⟨u, hu⟩ := hlab e he
      exact ⟨u, by rwa [← subst_subst] at hu⟩
    · refine ihbody e he (θ := θ.lift) Subst.lift_comp_cons.symm (fun i => ?_)
      cases i with
      | zero =>
        exact .bvar (hwf.2.2.2.1 e he).2.2.1 (TShape.LE.refl (hwf.2.2.2.1 e he).2.2.1)
      | succ i => exact Interp.weak' (l := .skip .refl) (hθ i) (fun _ => rfl)
  | @pair _ _ _ _ _ _ _ _ _ _ _ _ ha hA hd hwf hlab hdom hinp hout hbody hty hw h1
      iha ihA ihinp ihout ihbody =>
    intro Γ' θ σ ρ hτ hθ
    subst hτ
    rw [← subst_subst] at hwf h1
    refine .pair (iha rfl hθ) (ihA rfl hθ) hd hwf (fun e he => ?_) hdom
      (fun e he => ihinp e he rfl hθ) (fun e he => ihout e he rfl hθ)
      (fun e he => ?_) hty hw h1
    · have := hlab e he; rwa [← subst_subst] at this
    · refine ihbody e he (θ := θ.lift) Subst.lift_comp_cons.symm (fun i => ?_)
      cases i with
      | zero =>
        exact .bvar (hwf.2.2.1.1 e.1 (List.mem_map.2 ⟨e, he, rfl⟩)).2.2.1
          (TShape.LE.refl (hwf.2.2.1.1 e.1 (List.mem_map.2 ⟨e, he, rfl⟩)).2.2.1)
      | succ i => exact Interp.weak' (l := .skip .refl) (hθ i) (fun _ => rfl)
  | fst _ hw h1 ihp => intro _ _ _ _ hτ hθ; exact .fst (ihp hτ hθ) hw h1
  | snd _ hq hw h1 ihp =>
    intro _ _ _ _ hτ hθ
    subst hτ
    rw [← subst_subst] at hq
    exact .snd (ihp rfl hθ) hq hw h1
  | natCase_zero _ hz _ ihM iha =>
    intro _ _ _ _ hτ hθ
    subst hτ
    rw [← subst_subst] at hz
    exact .natCase_zero (ihM rfl hθ) hz (iha rfl hθ)
  | natCase_succ _ hwv heq _ ihM ihb =>
    intro Γ' θ σ ρ hτ hθ
    subst hτ
    rw [← subst_subst] at heq
    refine .natCase_succ (ihM rfl hθ) hwv heq ?_
    refine ihb (θ := θ.lift) Subst.lift_comp_cons.symm (fun i => ?_)
    cases i with
    | zero => exact .bvar (TShape.WF.T.2 hwv) (TShape.LE.refl (TShape.WF.T.2 hwv))
    | succ i => exact Interp.weak' (l := .skip .refl) (hθ i) (fun _ => rfl)
  | Y _ hwx _ ihself ihb =>
    intro Γ' θ σ ρ hτ hθ
    subst hτ
    refine .Y (ihself rfl hθ) hwx ?_
    simp only [Term.subst, subst_subst, ← Subst.comp_lift]
    refine ihb (θ := θ.lift) Subst.lift_comp_cons.symm (fun i => ?_)
    cases i with
    | zero => exact .bvar hwx (TShape.LE.refl hwx)
    | succ i => exact Interp.weak' (l := .skip .refl) (hθ i) (fun _ => rfl)
  | id hw h1 =>
    intro _ _ _ _ hτ hθ
    subst hτ
    simp only [← subst_subst] at h1
    exact .id hw h1
  | refl _ hw h1 ihv => intro _ _ _ _ hτ hθ; exact .refl (ihv hτ hθ) hw h1
  | tr hw hle _ _ _ _ hwv hvA _ hcb hm' _ heq ihX iha ihb ihA ihC ihH =>
    intro Γ' θ σ ρ hτ hθ
    subst hτ
    rw [← subst_subst, ← subst_subst, ← subst_subst] at heq
    refine .tr hw hle (ihX rfl hθ) (iha rfl hθ) (ihb rfl hθ) (ihA rfl hθ) hwv hvA ?_ hcb hm'
      (fun hr => ihH hr rfl hθ) heq
    rw [subst_subst]
    refine ihC (θ := θ.lift) Subst.lift_comp_cons.symm (fun i => ?_)
    cases i with
    | zero => exact .bvar hwv (TShape.LE.refl hwv)
    | succ i => exact Interp.weak' (l := .skip .refl) (hθ i) (fun _ => rfl)

/-! ## Obligations

The lemmas about `Interp` that the soundness induction still needs, stated
so the remaining work is legible.  Each is `sorry` for now.

`Interp.subst` above is substitution in the **stage**, which is how this
model does substitution at all: nested expressions are evaluated by
extending `σ`, never by extending the context of the interpretation.  The
lemmas here are the two things that are *not* that: undoing a weakening,
and relating a substitution in the **term** to one in the stage. -/

/-- Strengthening along a renaming: master's `weak'_iff` in the direction
`Interp.weak'` does not give.  Needed wherever a body's interpretation has
to be read back at the outer stage — master uses it for `eta` and for both
`Y` lemmas.  Master proves it by `generalize`-ing the renamed term and
casing on the original at each step. -/
theorem Interp.unweak {Δ Γ' : List Term} {u σ' ρ' m}
    (H : Interp Δ Γ' u σ' ρ' m) :
    ∀ {Γ t l ρ}, (∀ i, ρ i = ρ' (Lift.liftVar l i)) → t.lift' l = u →
      Interp Δ Γ t (σ'.lift_l l) ρ m := by
  induction H with
  | bot => intro _ _ _ _ _ _; exact .bot
  | bvar hw h1 =>
    intro _ t l ρ hρ ht; cases t <;> cases ht
    exact .bvar hw (hρ _ ▸ h1)
  | sort hw h1 => intro _ t l ρ hρ ht; cases t <;> cases ht; exact .sort hw h1
  | unit hw h1 => intro _ t l ρ hρ ht; cases t <;> cases ht; exact .unit hw h1
  | nat hw h1 => intro _ t l ρ hρ ht; cases t <;> cases ht; exact .nat hw h1
  | zero hw h1 => intro _ t l ρ hρ ht; cases t <;> cases ht; exact .zero hw h1
  | succ _ hw h1 ihv =>
    intro _ t l ρ hρ ht; cases t <;> cases ht
    exact .succ (ihv hρ rfl) hw h1
  | app _ _ hev hw h1 ihF iha =>
    intro _ t l ρ hρ ht; cases t <;> cases ht
    rw [subst_lift'] at hev
    exact .app (ihF hρ rfl) (iha hρ rfl) hev hw h1
  | lam _ hd hwf hdom _ hw h1 ihA ihbody =>
    intro _ t l ρ hρ ht; cases t <;> cases ht
    rw [subst_lift'] at hwf h1
    refine .lam (ihA hρ rfl) hd hwf hdom ?_ hw h1
    intro e he
    refine Subst.lift_l_cons ▸ ihbody e he (l := l.cons) (fun i => ?_) rfl
    cases i <;> simp_all [Valuation.push]
  | forallE _ hd hwf hlab hdom _ hw h1 ihA ihbody =>
    intro _ t l ρ hρ ht; cases t <;> cases ht
    rw [subst_lift'] at hlab
    rw [subst_lift', subst_lift', ← Subst.lift_l_lift] at hwf h1
    refine .forallE (ihA hρ rfl) hd hwf hlab hdom ?_ hw h1
    intro e he
    refine Subst.lift_l_cons ▸ ihbody e he (l := l.cons) (fun i => ?_) rfl
    cases i <;> simp_all [Valuation.push]
  | sigma _ hd hwf hlab hdom _ hw h1 ihA ihbody =>
    intro _ t l ρ hρ ht; cases t <;> cases ht
    rw [subst_lift'] at hlab
    rw [subst_lift', subst_lift', ← Subst.lift_l_lift] at hwf h1
    refine .sigma (ihA hρ rfl) hd hwf hlab hdom ?_ hw h1
    intro e he
    refine Subst.lift_l_cons ▸ ihbody e he (l := l.cons) (fun i => ?_) rfl
    cases i <;> simp_all [Valuation.push]
  | pair _ _ hd hwf hlab hdom _ _ hbody hty hw h1 iha ihA ihinp ihout ihbody =>
    intro _ t l ρ hρ ht; cases t <;> cases ht
    rw [subst_lift'] at hwf h1 hlab
    refine .pair (iha hρ rfl) (ihA hρ rfl) hd hwf hlab hdom (fun e he => ihinp e he hρ rfl)
      (fun e he => ihout e he hρ rfl) (fun e he => ?_) hty hw h1
    refine Subst.lift_l_cons ▸ ihbody e he (l := l.cons) (fun i => ?_) rfl
    cases i <;> simp_all [Valuation.push]
  | fst _ hw h1 ihp =>
    intro _ t l ρ hρ ht; cases t <;> cases ht
    exact .fst (ihp hρ rfl) hw h1
  | snd _ hq hw h1 ihp =>
    intro _ t l ρ hρ ht; cases t <;> cases ht
    simp only [Term.subst, subst_lift'] at hq ⊢
    exact .snd (ihp hρ rfl) hq hw h1
  | natCase_zero _ hz _ ihM iha =>
    intro _ t l ρ hρ ht; cases t <;> cases ht
    rw [subst_lift'] at hz
    exact .natCase_zero (ihM hρ rfl) hz (iha hρ rfl)
  | natCase_succ _ hwv heq _ ihM ihb =>
    intro _ t l ρ hρ ht; cases t <;> cases ht
    rw [subst_lift'] at heq
    refine .natCase_succ (ihM hρ rfl) hwv heq ?_
    refine Subst.lift_l_cons ▸ ihb (l := l.cons) (fun i => ?_) rfl
    cases i <;> simp_all [Valuation.push]
  | Y _ hwx _ ihself ihb =>
    intro _ t l ρ hρ ht; cases t <;> cases ht
    refine .Y (ihself hρ rfl) hwx ?_
    rw [← subst_lift' (e := Term.Y _ _)]
    refine Subst.lift_l_cons ▸ ihb (l := l.cons) (fun i => ?_) rfl
    cases i <;> simp_all [Valuation.push]
  | id hw h1 =>
    intro _ t l ρ hρ ht; cases t <;> cases ht
    simp only [subst_lift'] at h1
    exact .id hw h1
  | refl _ hw h1 ihv =>
    intro _ t l ρ hρ ht; cases t <;> cases ht
    exact .refl (ihv hρ rfl) hw h1
  | tr hw hle _ _ _ _ hwv hvA _ hcb hm' _ heq ihX iha ihb ihA ihC ihH =>
    intro _ t l ρ hρ ht; cases t <;> cases ht
    rw [subst_lift', subst_lift', subst_lift'] at heq
    refine .tr hw hle (ihX hρ rfl) (iha hρ rfl) (ihb hρ rfl) (ihA hρ rfl) hwv hvA ?_ hcb hm'
      (fun hr => ihH hr hρ rfl) heq
    rw [← subst_lift']
    refine Subst.lift_l_cons ▸ ihC (l := l.cons) (fun i => ?_) rfl
    cases i <;> simp_all [Valuation.push]

theorem Interp.weak_iff (hρ : ∀ i, ρ i = ρ' (Lift.liftVar l i)) :
    Interp Δ Γ' (t.lift' l) σ' ρ' m ↔ Interp Δ Γ t (Subst.lift_l l σ') ρ m :=
  ⟨fun H => H.unweak hρ rfl, fun H => H.weak' hρ⟩

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
theorem Interp.Dir.weak {Δ Γ Γ' : List Term} {t σ ρ x e} (h : Interp.Dir Δ Γ t σ ρ) :
    Interp.Dir Δ Γ' t.lift (σ.cons e) (ρ.push x) := by
  intro m₁ m₂ h₁ h₂
  have hiff : ∀ {m}, Interp Δ Γ' t.lift (σ.cons e) (ρ.push x) m ↔
      Interp Δ Γ t σ ρ m := fun {_} => Interp.weak_iff (fun _ => rfl)
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

/-- The merge under a binder, shared by every clause that has one: each
element of the list contributes a valuation whose slot `0` is the
binder's own and whose tail approximates `θ`, and the tails fold to one
valuation that serves them all. -/
theorem Interp.body_merge {Δ Γ Γ' Γ'' : List Term} {α : Type} {b : Term} {θ σ ρ} (hΔ : ⊢ Δ)
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
    | succ i => exact (hθ i).weak
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
    exact fun i => Interp.weak_iff (l := .skip .refl) (fun _ => rfl) |>.1 ((hall p hp).2 (i+1))
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

/-- The fixed point's case of the analytic direction: `Interp.Y` is
recursive in its own term, so this is an induction on the tower, with the
body's induction hypothesis passed in. -/
theorem Interp.to_substTerm_Y {Δ : List Term} (hΔ : ⊢ Δ) {A b : Term}
    (ihb : ∀ {Γ₂ Γ₂' : List Term} {θ₂ σ₂ ρ₂ m₂}, (∀ i, Interp.Dir Δ Γ₂' (θ₂ i) σ₂ ρ₂) →
      Interp Δ Γ₂' (b.subst θ₂) σ₂ ρ₂ m₂ →
      ∃ ρ', Interp Δ Γ₂ b (θ₂.comp σ₂) ρ' m₂ ∧ Valuation.Approx Δ Γ₂' θ₂ σ₂ ρ₂ ρ')
    {Γ' : List Term} {u σ ρ m} (H : Interp Δ Γ' u σ ρ m) :
    ∀ {Γ : List Term} {θ}, u = (Term.Y A b).subst θ →
      (∀ i, Interp.Dir Δ Γ' (θ i) σ ρ) →
      ∃ ρ', Interp Δ Γ (.Y A b) (θ.comp σ) ρ' m ∧ Valuation.Approx Δ Γ' θ σ ρ ρ' := by
  induction H with
  | bot => intro _ _ _ _; exact ⟨Valuation.nil, .bot, Valuation.Approx.nil⟩
  | @Y Γ₃ σ₃ ρ₃ m₃ A₂ b₂ x hself hwx hbody ihself _ =>
    rintro Γ θ ⟨⟩ hθ
    obtain ⟨ρ₀, hself', hA₀⟩ := ihself rfl hθ
    obtain ⟨ρ₁, hA₁, hbody'⟩ := Interp.body_merge (Γ := A :: Γ) hΔ hθ
      (l := [()]) (tm := fun _ => (Term.Y (A.subst θ) (b.subst θ.lift)).subst σ₃)
      (inp := fun _ => x)
      (out := fun _ => m₃) (fun _ _ => hwx) ihb (fun _ _ => hbody)
    obtain ⟨hAj, hles⟩ := Valuation.Approx.foldr (l := [ρ₀, ρ₁]) hΔ hθ (by
      intro ρ' hρ'
      match List.mem_cons.1 hρ' with
      | .inl h => exact h ▸ hA₀
      | .inr h => exact (List.mem_singleton.1 h) ▸ hA₁)
    refine ⟨_, .Y (Interp.mono_val hΔ (hles ρ₀ (by simp)) hself') hwx ?_, hAj⟩
    have hb := Interp.mono_val hΔ (Valuation.LE.push.2
      ⟨hles ρ₁ (by simp), TShape.LE.refl hwx⟩) (hbody' () (by simp))
    simp only [Term.subst, subst_subst, ← Subst.comp_lift] at hb ⊢
    exact hb
  | _ => intro _ _ hu _; cases hu

/-- **Substitution in the term, the analytic direction.**  An approximant
of `t[θ]` is an approximant of `t` at the composed stage, under *some*
valuation whose slots approximate the `θ i`.

The induction is on the **term**, not on the derivation: `(bvar i)[θ]` is
`θ i`, which has no head to invert, and that case is where the valuation
is built (slot `i` holds the approximant, every other slot `⊥`).
Everywhere else the substituted term has the same head, so the clause
inverts, and the subderivations' valuations are merged by
`Valuation.Approx.foldr` — one call to each `θ i`'s directedness per
slot.  Under a binder the body's valuation comes back with the binder's
own slot in front; `Interp.weak_iff` strips it off the rest. -/
theorem Interp.to_substTerm {Δ : List Term} (hΔ : ⊢ Δ) :
    ∀ {t : Term} {Γ Γ' : List Term} {θ σ ρ m}, (∀ i, Interp.Dir Δ Γ' (θ i) σ ρ) →
      Interp Δ Γ' (t.subst θ) σ ρ m →
      ∃ ρ', Interp Δ Γ t (θ.comp σ) ρ' m ∧ Valuation.Approx Δ Γ' θ σ ρ ρ' := by
  intro t
  induction t with
  | bvar i =>
    intro Γ Γ' θ σ ρ m _ h
    refine ⟨fun j => if j = i then m else TShape.bot, ?_, fun j => ?_⟩
    · exact .bvar h.wf (by simp only [if_pos rfl]; exact TShape.LE.refl h.wf)
    · by_cases hj : j = i
      · subst hj; simpa using h
      · simpa only [if_neg hj] using Interp.bot (t := θ j) (n := 0)
  | sort u =>
    intro Γ Γ' θ σ ρ m _ h
    cases h with
    | bot => exact ⟨Valuation.nil, .bot, Valuation.Approx.nil⟩
    | sort hw hle => exact ⟨Valuation.nil, .sort hw hle, Valuation.Approx.nil⟩
  | unit r =>
    intro Γ Γ' θ σ ρ m _ h
    cases h with
    | bot => exact ⟨Valuation.nil, .bot, Valuation.Approx.nil⟩
    | unit hw hle => exact ⟨Valuation.nil, .unit hw hle, Valuation.Approx.nil⟩
  | star r =>
    intro Γ Γ' θ σ ρ m _ h
    cases h with
    | bot => exact ⟨Valuation.nil, .bot, Valuation.Approx.nil⟩
  | nat =>
    intro Γ Γ' θ σ ρ m _ h
    cases h with
    | bot => exact ⟨Valuation.nil, .bot, Valuation.Approx.nil⟩
    | nat hw hle => exact ⟨Valuation.nil, .nat hw hle, Valuation.Approx.nil⟩
  | zero =>
    intro Γ Γ' θ σ ρ m _ h
    cases h with
    | bot => exact ⟨Valuation.nil, .bot, Valuation.Approx.nil⟩
    | zero hw hle => exact ⟨Valuation.nil, .zero hw hle, Valuation.Approx.nil⟩
  | succ N ih =>
    intro Γ Γ' θ σ ρ m hθ h
    cases h with
    | bot => exact ⟨Valuation.nil, .bot, Valuation.Approx.nil⟩
    | succ hv hw hle =>
      obtain ⟨ρ', hv', hA⟩ := ih hθ hv
      exact ⟨ρ', .succ hv' hw hle, hA⟩
  | id r A a b ihA iha ihb =>
    intro Γ Γ' θ σ ρ m _ h
    cases h with
    | bot => exact ⟨Valuation.nil, .bot, Valuation.Approx.nil⟩
    | id hw hle =>
      refine ⟨Valuation.nil, .id hw ?_, Valuation.Approx.nil⟩
      simpa only [subst_subst] using hle
  | refl r a ih =>
    intro Γ Γ' θ σ ρ m hθ h
    cases h with
    | bot => exact ⟨Valuation.nil, .bot, Valuation.Approx.nil⟩
    | refl hv hw hle =>
      obtain ⟨ρ', hv', hA⟩ := ih hθ hv
      exact ⟨ρ', .refl hv' hw hle, hA⟩
  | app f a ihf iha =>
    intro Γ Γ' θ σ ρ m hθ h
    cases h with
    | bot => exact ⟨Valuation.nil, .bot, Valuation.Approx.nil⟩
    | app hF ha hev hw hle =>
      obtain ⟨ρ₁, hf', hA₁⟩ := ihf hθ hF
      obtain ⟨ρ₂, ha', hA₂⟩ := iha hθ ha
      obtain ⟨hAj, hles⟩ := Valuation.Approx.foldr (l := [ρ₁, ρ₂]) hΔ hθ (by
        intro ρ' hρ'
        match List.mem_cons.1 hρ' with
        | .inl h => exact h ▸ hA₁
        | .inr h => exact (List.mem_singleton.1 h) ▸ hA₂)
      rw [subst_subst] at hev
      exact ⟨_, .app (Interp.mono_val hΔ (hles ρ₁ (by simp)) hf')
        (Interp.mono_val hΔ (hles ρ₂ (by simp)) ha') hev hw hle, hAj⟩
  | fst p ih =>
    intro Γ Γ' θ σ ρ m hθ h
    cases h with
    | bot => exact ⟨Valuation.nil, .bot, Valuation.Approx.nil⟩
    | fst hp hw hle =>
      obtain ⟨ρ', hp', hA⟩ := ih hθ hp
      exact ⟨ρ', .fst hp' hw hle, hA⟩
  | snd p ih =>
    intro Γ Γ' θ σ ρ m hθ h
    cases h with
    | bot => exact ⟨Valuation.nil, .bot, Valuation.Approx.nil⟩
    | snd hp hq hw hle =>
      obtain ⟨ρ', hp', hA⟩ := ih hθ hp
      simp only [Term.subst, subst_subst] at hq ⊢
      exact ⟨ρ', .snd hp' hq hw hle, hA⟩
  | lam A e ihA ihe =>
    intro Γ Γ' θ σ ρ m hθ h
    cases h with
    | bot => exact ⟨Valuation.nil, .bot, Valuation.Approx.nil⟩
    | @lam _ _ _ _ n g d _ _ hAint hd hwf hdom hbody hw hle =>
      obtain ⟨ρ₀, hA', hA₀⟩ := ihA hθ hAint
      obtain ⟨ρ₁, hA₁, hbody'⟩ := Interp.body_merge (Γ := A :: Γ) hΔ hθ
        (l := g) (tm := Entry.tm) (inp := fun e' => e'.inp.T) (out := fun e' => e'.out.T)
        (fun e' he' => (hwf.2.2.1.1 e' he').2.2.1) ihe hbody
      obtain ⟨hAj, hles⟩ := Valuation.Approx.foldr (l := [ρ₀, ρ₁]) hΔ hθ (by
        intro ρ' hρ'
        match List.mem_cons.1 hρ' with
        | .inl h => exact h ▸ hA₀
        | .inr h => exact (List.mem_singleton.1 h) ▸ hA₁)
      rw [subst_subst] at hwf hle
      exact ⟨_, .lam (Interp.mono_val hΔ (hles ρ₀ (by simp)) hA') hd hwf hdom
        (fun e' he' => Interp.mono_val hΔ
          (Valuation.LE.push.2 ⟨hles ρ₁ (by simp), TShape.LE.refl (hwf.2.2.1.1 e' he').2.2.1⟩)
          (hbody' e' he')) hw hle, hAj⟩
  | forallE A B ihA ihB =>
    intro Γ Γ' θ σ ρ m hθ h
    cases h with
    | bot => exact ⟨Valuation.nil, .bot, Valuation.Approx.nil⟩
    | @forallE _ _ _ _ n g d _ _ hAint hd hwf hlab hdom hbody hw hle =>
      obtain ⟨ρ₀, hA', hA₀⟩ := ihA hθ hAint
      obtain ⟨ρ₁, hA₁, hbody'⟩ := Interp.body_merge (Γ := A :: Γ) hΔ hθ
        (l := g) (tm := Entry.tm) (inp := fun e' => e'.inp.T) (out := fun e' => e'.out.T)
        (fun e' he' => (hwf.2.2.2.1 e' he').2.2.1) ihB hbody
      obtain ⟨hAj, hles⟩ := Valuation.Approx.foldr (l := [ρ₀, ρ₁]) hΔ hθ (by
        intro ρ' hρ'
        match List.mem_cons.1 hρ' with
        | .inl h => exact h ▸ hA₀
        | .inr h => exact (List.mem_singleton.1 h) ▸ hA₁)
      simp only [subst_subst, ← Subst.comp_lift] at hwf hle
      refine ⟨_, .forallE (Interp.mono_val hΔ (hles ρ₀ (by simp)) hA') hd hwf
        (fun e' he' => ?_) hdom
        (fun e' he' => Interp.mono_val hΔ
          (Valuation.LE.push.2 ⟨hles ρ₁ (by simp),
            TShape.LE.refl (hwf.2.2.2.1 e' he').2.2.1⟩)
          (hbody' e' he')) hw hle, hAj⟩
      obtain ⟨u, hu⟩ := hlab e' he'
      exact ⟨u, by rwa [subst_subst] at hu⟩
  | sigma A B ihA ihB =>
    intro Γ Γ' θ σ ρ m hθ h
    cases h with
    | bot => exact ⟨Valuation.nil, .bot, Valuation.Approx.nil⟩
    | @sigma _ _ _ _ n g d _ _ hAint hd hwf hlab hdom hbody hw hle =>
      obtain ⟨ρ₀, hA', hA₀⟩ := ihA hθ hAint
      obtain ⟨ρ₁, hA₁, hbody'⟩ := Interp.body_merge (Γ := A :: Γ) hΔ hθ
        (l := g) (tm := Entry.tm) (inp := fun e' => e'.inp.T) (out := fun e' => e'.out.T)
        (fun e' he' => (hwf.2.2.2.1 e' he').2.2.1) ihB hbody
      obtain ⟨hAj, hles⟩ := Valuation.Approx.foldr (l := [ρ₀, ρ₁]) hΔ hθ (by
        intro ρ' hρ'
        match List.mem_cons.1 hρ' with
        | .inl h => exact h ▸ hA₀
        | .inr h => exact (List.mem_singleton.1 h) ▸ hA₁)
      simp only [subst_subst, ← Subst.comp_lift] at hwf hle
      refine ⟨_, .sigma (Interp.mono_val hΔ (hles ρ₀ (by simp)) hA') hd hwf
        (fun e' he' => ?_) hdom
        (fun e' he' => Interp.mono_val hΔ
          (Valuation.LE.push.2 ⟨hles ρ₁ (by simp),
            TShape.LE.refl (hwf.2.2.2.1 e' he').2.2.1⟩)
          (hbody' e' he')) hw hle, hAj⟩
      obtain ⟨u, hu⟩ := hlab e' he'
      exact ⟨u, by rwa [subst_subst] at hu⟩
  | pair A B a b ihA ihB iha ihb =>
    intro Γ Γ' θ σ ρ m hθ hm
    cases hm with
    | bot => exact ⟨Valuation.nil, .bot, Valuation.Approx.nil⟩
    | @pair _ _ _ _ n x g₀ d _ _ _ _ hai hAi hd hwf hlab hdom hinp hout hcode hcty hw hle =>
      obtain ⟨ρ₀, ha', hA₀⟩ := iha hθ hai
      obtain ⟨ρ₁, hA₁, hinp'⟩ := Interp.list_merge (Γ := Γ) hΔ hθ
        (l := g₀) (out := fun e => e.1.inp.T) iha hinp
      obtain ⟨ρ₂, hA'', hA₂⟩ := ihA hθ hAi
      obtain ⟨ρ₃, hA₃, hout'⟩ := Interp.list_merge (Γ := Γ) hΔ hθ
        (l := g₀) (out := fun e => e.1.out.T) ihb hout
      obtain ⟨ρ₄, hA₄, hcode'⟩ := Interp.body_merge (Γ := A :: Γ) hΔ hθ
        (l := g₀) (tm := fun e => e.1.tm) (inp := fun e => e.1.inp.T) (out := fun e => e.2)
        (fun e he => (hwf.2.2.1.1 e.1 (List.mem_map.2 ⟨e, he, rfl⟩)).2.2.1) ihB hcode
      obtain ⟨hAj, hles⟩ := Valuation.Approx.foldr (l := [ρ₀, ρ₁, ρ₂, ρ₃, ρ₄]) hΔ hθ (by
        intro ρ' hρ'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ'
        rcases hρ' with rfl | rfl | rfl | rfl | rfl
        exacts [hA₀, hA₁, hA₂, hA₃, hA₄])
      rw [subst_subst] at hwf hle
      refine ⟨_, .pair (Interp.mono_val hΔ (hles ρ₀ (by simp)) ha')
        (Interp.mono_val hΔ (hles ρ₂ (by simp)) hA'') hd hwf (fun e he => ?_) hdom
        (fun e he => Interp.mono_val hΔ (hles ρ₁ (by simp)) (hinp' e he))
        (fun e he => Interp.mono_val hΔ (hles ρ₃ (by simp)) (hout' e he))
        (fun e he => ?_) hcty hw hle, hAj⟩
      · have := hlab e he; rwa [subst_subst] at this
      · exact Interp.mono_val hΔ (Valuation.LE.push.2 ⟨hles ρ₄ (by simp),
          TShape.LE.refl (hwf.2.2.1.1 e.1 (List.mem_map.2 ⟨e, he, rfl⟩)).2.2.1⟩)
          (hcode' e he)
  | natCase C M a b ihC ihM iha ihb =>
    intro Γ Γ' θ σ ρ m hθ h
    cases h with
    | bot => exact ⟨Valuation.nil, .bot, Valuation.Approx.nil⟩
    | natCase_zero hM hz ha =>
      obtain ⟨ρ₀, hM', hA₀⟩ := ihM hθ hM
      obtain ⟨ρ₁, ha', hA₁⟩ := iha hθ ha
      obtain ⟨hAj, hles⟩ := Valuation.Approx.foldr (l := [ρ₀, ρ₁]) hΔ hθ (by
        intro ρ' hρ'
        match List.mem_cons.1 hρ' with
        | .inl h => exact h ▸ hA₀
        | .inr h => exact (List.mem_singleton.1 h) ▸ hA₁)
      rw [subst_subst] at hz
      exact ⟨_, .natCase_zero (Interp.mono_val hΔ (hles ρ₀ (by simp)) hM') hz
        (Interp.mono_val hΔ (hles ρ₁ (by simp)) ha'), hAj⟩
    | @natCase_succ _ _ _ _ _ _ _ _ n v t hM hwv heq hb =>
      obtain ⟨ρ₀, hM', hA₀⟩ := ihM hθ hM
      obtain ⟨ρ₁, hA₁, hb'⟩ := Interp.body_merge (Γ := Term.nat :: Γ) hΔ hθ
        (l := [()]) (tm := fun _ => t) (inp := fun _ => v.T) (out := fun _ => m)
        (fun _ _ => TShape.WF.T.2 hwv) ihb (fun _ _ => hb)
      obtain ⟨hAj, hles⟩ := Valuation.Approx.foldr (l := [ρ₀, ρ₁]) hΔ hθ (by
        intro ρ' hρ'
        match List.mem_cons.1 hρ' with
        | .inl h => exact h ▸ hA₀
        | .inr h => exact (List.mem_singleton.1 h) ▸ hA₁)
      rw [subst_subst] at heq
      refine ⟨_, .natCase_succ (Interp.mono_val hΔ (hles ρ₀ (by simp)) hM') hwv heq ?_, hAj⟩
      exact Interp.mono_val hΔ (Valuation.LE.push.2
        ⟨hles ρ₁ (by simp), TShape.LE.refl (TShape.WF.T.2 hwv)⟩) (hb' () (by simp))
  | Y A b ihA ihb =>
    intro Γ Γ' θ σ ρ m hθ h
    exact Interp.to_substTerm_Y hΔ ihb h rfl hθ
  | tr r A a b C X H ihA iha ihb ihC ihX ihH =>
    intro Γ Γ' θ σ ρ m hθ hm
    cases hm with
    | bot => exact ⟨Valuation.nil, .bot, Valuation.Approx.nil⟩
    | @tr _ _ _ _ v vA m'' cb _ _ _ _ _ _ _ hw hle hXi hai hbi hAi hwv hvA hCi hcb hm' hHi
        heq =>
      obtain ⟨ρ₀, hX', hA₀⟩ := ihX hθ hXi
      obtain ⟨ρ₁, ha', hA₁⟩ := iha hθ hai
      obtain ⟨ρ₂, hb', hA₂⟩ := ihb hθ hbi
      obtain ⟨ρ₃, hA'', hA₃⟩ := ihA hθ hAi
      obtain ⟨ρ₄, hA₄, hC'⟩ := Interp.body_merge (Γ := A :: Γ) hΔ hθ
        (l := [()]) (tm := fun _ => (b.subst θ).subst σ) (inp := fun _ => v)
        (out := fun _ => cb) (fun _ _ => hwv) ihC (fun _ _ => hCi)
      obtain ⟨ρ₅, hA₅, hH'⟩ := Interp.list_merge (Γ := Γ) hΔ hθ
        (l := if r = true then [()] else []) (out := fun _ =>
          Shape.T (n := v.1+1) (ShapeS.refl v.2)) ihH (by
        intro e he
        exact hHi (by
          by_cases hr : r = true
          · exact hr
          · simp [hr] at he))
      obtain ⟨hAj, hles⟩ := Valuation.Approx.foldr (l := [ρ₀, ρ₁, ρ₂, ρ₃, ρ₄, ρ₅]) hΔ hθ (by
        intro ρ' hρ'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ'
        rcases hρ' with rfl | rfl | rfl | rfl | rfl | rfl
        exacts [hA₀, hA₁, hA₂, hA₃, hA₄, hA₅])
      refine ⟨_, .tr hw hle (Interp.mono_val hΔ (hles ρ₀ (by simp)) hX')
        (Interp.mono_val hΔ (hles ρ₁ (by simp)) ha')
        (Interp.mono_val hΔ (hles ρ₂ (by simp)) hb')
        (Interp.mono_val hΔ (hles ρ₃ (by simp)) hA'') hwv hvA ?_ hcb hm' ?_ ?_, hAj⟩
      · have := Interp.mono_val hΔ (Valuation.LE.push.2
          ⟨hles ρ₄ (by simp), TShape.LE.refl hwv⟩) (hC' () (by simp))
        rwa [subst_subst] at this
      · intro hr
        exact Interp.mono_val hΔ (hles ρ₅ (by simp)) (hH' () (by simp [hr]))
      · rwa [subst_subst, subst_subst, subst_subst] at heq

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
theorem Interp.substTerm (hΔ : ⊢ Δ) {θ : Subst}
    (hθ : ∀ i, Interp.Dir Δ Γ' (θ i) σ ρ) :
    Interp Δ Γ' (t.subst θ) σ ρ m ↔
    ∃ ρ', Interp Δ Γ t (θ.comp σ) ρ' m ∧ ∀ i, Interp Δ Γ' (θ i) σ ρ (ρ' i) :=
  ⟨Interp.to_substTerm hΔ hθ, fun ⟨_, h, hs⟩ => Interp.of_substTerm hΔ h rfl hs⟩

/-- The single-substitution form, which is what `beta` uses: `b[a]` at
stage `σ` is `b` at the stage extended by `a[σ]`, under the valuation
extended by an approximant of `a`.  Master's `LE_Interp.inst`. -/
theorem Interp.inst (hΔ : ⊢ Δ) (ha : Interp.Dir Δ Γ a σ ρ) (hρ : Valuation.WF Δ ρ) :
    Interp Δ Γ (b.inst a) σ ρ m ↔
    ∃ x, Interp Δ (A :: Γ) b ((Subst.one a).comp σ) (ρ.push x) m ∧ Interp Δ Γ a σ ρ x :=
  -- at `θ = one a`: slot `0` holds the argument's approximant and slot
  -- `i+1` the valuation's own
  ⟨fun h => by
    obtain ⟨ρ', hb, hs⟩ := Interp.to_substTerm (Γ := A :: Γ) hΔ (θ := Subst.one a)
      (fun i => by
        cases i with
        | zero => exact ha
        | succ i => exact Interp.Dir.bvar (hρ i)) h
    refine ⟨ρ' 0, Interp.mono_val hΔ (fun i => ?_) hb, hs 0⟩
    cases i with
    | zero => exact TShape.LE.refl (hs 0).wf
    | succ i => exact Interp.le_bvar (Γ := Γ) (i := i) (σ := σ) (hs (i+1))
  , fun ⟨x, hb, hx⟩ => Interp.of_substTerm hΔ hb rfl (fun i => by
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
