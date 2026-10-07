import DomainSemantics.Annot
import DomainSemantics.Regular
import DomainSemantics.HasType
import DomainSemantics.Canon

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

@[simp] theorem Valuation.subst_push {ro : Valuation} {tau u} :
    (ro.push u).subst tau = (ro.subst tau).push (u.subst tau) := by
  funext i; cases i <;> rfl

/-- Pointwise order on valuations, at a stage. -/
def Valuation.LE (Δ : List Term) (ρ ρ' : Valuation) : Prop := ∀ i, TShape.LE Δ (ρ i) (ρ' i)

/-- Pointwise well-formedness. -/
def Valuation.WF (Δ : List Term) (ρ : Valuation) : Prop := ∀ i, TShape.WF Δ (ρ i)

theorem Valuation.LE.refl {Δ : List Term} {ρ : Valuation} (h : ρ.WF Δ) : ρ.LE Δ ρ :=
  fun i => TShape.LE.refl (h i)

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
    -- the label types the argument, *stably*: this is what makes the clause
    -- stage-invariant, and the only place the lookup's type is pinned
    Stable Δ Γ σ a A →
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
    (∀ e ∈ g, TShape.Named Δ d e.tm e.inp.T) →
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
    (∀ e ∈ g, TShape.Named Δ d.T e.tm e.inp.T) →
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
      (∀ e ∈ g, TShape.Named Δ (Shape.T d) e.tm (Shape.T e.inp)) →
      (∀ e ∈ g, Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push (Shape.T e.inp)) (Shape.T e.out)) →
      TShape.WF Δ m →
      TShape.LE Δ m
        (Shape.T (n := n+1) (ShapeS.sigma (A.subst σ) (B.subst σ.lift) d g)) →
      (∃ u, Γ ⊢ A : .sort u) → (∃ v, A :: Γ ⊢ B : .sort v) →
      Interp Δ Γ (.sigma A B) σ ρ m
  /-- A pair is its two components, with the first's term as its name
  (§4.7e).  The name is what the codomain code is read at — the second
  component's type is `B[a]` — and it is also what `snd` queries, so the
  value says which term its first component stands for.  There is no
  graph: an entry's input would be a condition the order enforces and the
  term's meaning does not, which is exactly what Σ's η cannot have. -/
  | pair {n} {x y : Shape n} {d c : TShape} {A B a b : Term} :
      Interp Δ Γ a σ ρ (Shape.T x) →
      Interp Δ Γ b σ ρ (Shape.T y) →
      Interp Δ Γ A σ ρ d →
      TShape.HasType Δ d TShape.type →
      TShape.Named Δ d (a.subst σ) (Shape.T x) →
      TShape.CodeCanonS Δ (A.subst σ) d →
      Shape.WF (n := n+1) Δ (ShapeS.pair (A.subst σ) (a.subst σ) x y) →
      Interp Δ (A :: Γ) B (σ.cons (a.subst σ)) (ρ.push (Shape.T x)) c →
      TShape.Dom Δ c (Shape.T y) →
      TShape.WF Δ m →
      TShape.LE Δ m
        (Shape.T (n := n+1) (ShapeS.pair (A.subst σ) (a.subst σ) x y)) →
      (∃ u, Γ ⊢ A : .sort u) → (Γ ⊢ a : A) →
      Interp Δ Γ (.pair A B a b) σ ρ m
  /-- The first projection reads the first component. -/
  | fst {n} {A₀ a₀ : Term} {x y : Shape n} :
      Interp Δ Γ p σ ρ (Shape.T (n := n+1) (ShapeS.pair A₀ a₀ x y)) →
      TShape.WF Δ m →
      TShape.LE Δ m (Shape.T x) →
      Interp Δ Γ (.fst p) σ ρ m
  /-- The second projection reads the second component, at a pair whose
  name is `fst p` — the §4.7a label invariant, now a clause premise
  rather than a graph query.  The name is what makes `snd p`'s type
  `B[fst p]` rather than `B` at some other term. -/
  | snd {n} {A₀ a₀ : Term} {x y : Shape n} :
      Interp Δ Γ p σ ρ (Shape.T (n := n+1) (ShapeS.pair A₀ a₀ x y)) →
      Δ ⊢ a₀ ≡ (Term.fst p).subst σ : A₀ →
      TShape.WF Δ m →
      TShape.LE Δ m (Shape.T y) →
      Stable Δ Γ σ (Term.fst p) A₀ →
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
  | protected Y {A b : Term} {x d : TShape} :
    Interp Δ Γ (.Y A b) σ ρ x →
    TShape.WF Δ x →
    Interp Δ Γ A σ ρ d →
    TShape.HasType Δ d TShape.type →
    TShape.Named Δ d ((A.Y b).subst σ) x →
    TShape.CodeCanonS Δ (A.subst σ) d →
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
  | refl {n} :
    TShape.WF Δ m →
    TShape.LE Δ m (Shape.T (n := n+1) .refl) →
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
  rule can justify: that is the hole left in master's context-free
  `LE_Interp`, and the reason for the labelled redesign.

  At `r = true` the proof is informative, and the clause asks for it to
  *be* `refl` at the stage, as a judgment.  A `refl`-shaped approximant is
  not enough: with no UIP a variable `h : Id A a a` may hold a `refl`
  slot while `tr A a a C X h` is stuck, and the transport would then pass
  on `X`'s values, whose pairs are named `fst X` rather than
  `fst (tr … X h)` — which breaks Σ's η (§4.7i).  With the equation the
  transport is `X` by `tr_refl`, and names move along it.  At `r = false`
  the equation is `proofIrrel`, so only `a ≡ b` is asked. -/
  | tr {v vA m' cb : TShape} {r : Bool} {A a b C X H : Term} :
    TShape.WF Δ m →
    TShape.LE Δ m m' →
    Interp Δ Γ X σ ρ m' →
    Interp Δ Γ a σ ρ v →
    Interp Δ Γ b σ ρ v →
    Interp Δ Γ A σ ρ vA →
    TShape.WF Δ v →
    TShape.Named Δ vA (b.subst σ) v →
    TShape.CodeCanonS Δ (A.subst σ) vA →
    Interp Δ (A :: Γ) C (σ.cons (b.subst σ)) (ρ.push v) cb →
    TShape.HasType Δ cb TShape.type →
    TShape.Named Δ cb (X.subst σ) m' →
    TShape.CodeCanonS Δ (C.subst (σ.cons (b.subst σ))) cb →
    (r = true → Δ ⊢ H.subst σ ≡ .refl true (a.subst σ) :
      .id true (A.subst σ) (a.subst σ) (b.subst σ)) →
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
  | app _ _ _ hw | lam _ _ _ _ _ hw | forallE _ _ _ _ _ hw | id hw | refl hw | tr hw
  | sigma _ _ _ _ _ hw | pair _ _ _ _ _ _ _ _ _ hw | fst _ hw | snd _ _ hw
  | natCase_zero _ _ _ _ _ hw | natCase_succ _ _ _ _ _ _ hw
  | Y _ _ _ _ _ _ _ _ _ _ _ hw => exact hw

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
  | lam hA hd hwf hNV hbody _ h1 hAt =>
    have hdom := fun e he => (hNV e he).dom
    have hcan := fun e he => (hNV e he).val
    exact .lam hA hd hwf (fun e he => .of_dom (hdom e he) (hcan e he)) hbody hw (TShape.LE.trans hΔ h h1) hAt
  | forallE hA hd hwf hNV hbody _ h1 hAt hBt =>
    have hdom := fun e he => (hNV e he).dom
    have hcan := fun e he => (hNV e he).val
    exact .forallE hA hd  hwf (fun e he => .of_dom (hdom e he) (hcan e he)) hbody hw (TShape.LE.trans hΔ h h1) hAt hBt
  | sigma hA hd hwf hNV hbody _ h1 hAt hBt =>
    have hdom := fun e he => (hNV e he).dom
    have hcan := fun e he => (hNV e he).val
    exact .sigma hA hd  hwf (fun e he => .of_dom (hdom e he) (hcan e he)) hbody hw (TShape.LE.trans hΔ h h1) hAt hBt
  | pair ha hb hA hd hNV hdc hwf hcode hcty _ h1 hAt hat =>
    have hdx := hNV.dom
    have hxc := hNV.val
    exact .pair ha hb hA hd (.of_dom hdx hxc) hdc hwf hcode hcty hw
      (TShape.LE.trans hΔ h h1) hAt hat
  | fst hp _ h1 => exact .fst hp hw (TShape.LE.trans hΔ h h1)
  | snd hp hlab _ h1 hty => exact .snd hp hlab hw (TShape.LE.trans hΔ h h1) hty
  | natCase_zero hM hz _ hMt _ iha => exact .natCase_zero hM hz (iha hw h) hMt
  | natCase_succ hM hwv heq _ hMt _ ihb => exact .natCase_succ hM hwv heq (ihb hw h) hMt
  | Y hself hwx hA hdty hNV hdc _ hAt hYt _ _ ihb =>
    have hDom := hNV.dom
    have hxc := hNV.val
    exact .Y hself hwx hA hdty (.of_dom hDom hxc) hdc (ihb hw h) hAt hYt
  | id _ h1 hAt hat hbt => exact .id hw (TShape.LE.trans hΔ h h1) hAt hat hbt
  | refl _ h1 => exact .refl hw (TShape.LE.trans hΔ h h1)
  | tr _ hle hX ha hb hA hwv hNV hvc hC hcb hNV2 hcbc hH heq hAt hat hbt _ _ _ _ _ =>
    have hvA := hNV.dom
    have hbc := hNV.val
    have hm' := hNV2.dom
    have hmc := hNV2.val
    exact .tr hw (TShape.LE.trans hΔ h hle) hX ha hb hA hwv (.of_dom hvA hbc) hvc hC hcb (.of_dom hm' hmc) hcbc hH heq
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
  | lam _ hd hwf hNV _ hw h1 hAt ihA ihbody =>
    have hdom := fun e he => (hNV e he).dom
    have hcan := fun e he => (hNV e he).val
    refine .lam (ihA hρ) hd hwf (fun e he => .of_dom (hdom e he) (hcan e he)) (fun e he => ?_) hw h1 hAt
    exact ihbody e he (Valuation.LE.push.2 ⟨hρ, .refl (hwf.2.2.1.1 e he).2.2.1⟩)
  | forallE _ hd hwf hNV _ hw h1 hAt hBt ihA ihbody =>
    have hdom := fun e he => (hNV e he).dom
    have hcan := fun e he => (hNV e he).val
    refine .forallE (ihA hρ) hd  hwf (fun e he => .of_dom (hdom e he) (hcan e he)) (fun e he => ?_) hw h1 hAt hBt
    exact ihbody e he (Valuation.LE.push.2 ⟨hρ, .refl (hwf.2.2.2.1.1 e he).2.2.1⟩)
  | sigma _ hd hwf hNV _ hw h1 hAt hBt ihA ihbody =>
    have hdom := fun e he => (hNV e he).dom
    have hcan := fun e he => (hNV e he).val
    exact .sigma (ihA hρ) hd  hwf (fun e he => .of_dom (hdom e he) (hcan e he)) (fun e he => ihbody e he
      (Valuation.LE.push.2 ⟨hρ, TShape.LE.refl (a := Shape.T e.inp)
        (hwf.2.2.2.1.1 e he).2.2.1⟩)) hw h1 hAt hBt
  | pair _ _ _ hd hNV hdc hwf _ hcty hw h1 hAt hat iha ihb ihA ihcode =>
    have hdx := hNV.dom
    have hxc := hNV.val
    exact .pair (iha hρ) (ihb hρ) (ihA hρ) hd (.of_dom hdx hxc) hdc hwf
      (ihcode (Valuation.LE.push.2 ⟨hρ, TShape.LE.refl (TShape.WF.T.2 hwf.2.2.2.1)⟩))
      hcty hw h1 hAt hat
  | fst _ hw h1 ihp => exact .fst (ihp hρ) hw h1
  | snd _ hq hw h1 hty ihp => exact .snd (ihp hρ) hq hw h1 hty
  | natCase_zero _ hz _ hMt ihM iha => exact .natCase_zero (ihM hρ) hz (iha hρ) hMt
  | natCase_succ _ hwv heq _ hMt ihM ihb =>
    refine .natCase_succ (ihM hρ) hwv heq ?_ hMt
    exact ihb (Valuation.LE.push.2 ⟨hρ, .refl (a := Shape.T _) hwv⟩)
  | Y _ hwx _ hdty hNV hdc _ hAt hYt ihself ihA ihb =>
    have hDom := hNV.dom
    have hxc := hNV.val
    exact .Y (ihself hρ) hwx (ihA hρ) hdty (.of_dom hDom hxc) hdc
      (ihb (Valuation.LE.push.2 ⟨hρ, .refl hwx⟩)) hAt hYt
  | id hw h1 hAt hat hbt => exact .id hw h1 hAt hat hbt
  | refl hw h1 => exact .refl hw h1
  | tr hw hle _ _ _ _ hwv hNV hvc _ hcb hNV2 hcbc hH heq hAt hat hbt ihX iha ihb ihA ihC =>
    have hvA := hNV.dom
    have hbc := hNV.val
    have hm' := hNV2.dom
    have hmc := hNV2.val
    refine .tr hw hle (ihX hρ) (iha hρ) (ihb hρ) (ihA hρ) hwv (.of_dom hvA hbc) hvc ?_ hcb (.of_dom hm' hmc) hcbc
      hH heq hAt hat hbt
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
    exact .app (ihF hΓ' W) (iha hΓ' W) hev hw h (hty.ctx W)
  | @lam _ _ _ _ _ _ _ A _ _ hd hwf hNV _ hw h hAt ihA ihbody =>
    have hdom := fun e he => (hNV e he).dom
    have hcan := fun e he => (hNV e he).val
    intro Γ' hΓ' W
    obtain ⟨u, hA⟩ := hAt
    have hA' : Γ' ⊢ A ≡ A : Term.sort u := IsDefEq.ctx_id hΓ' W hA
    exact .lam (ihA hΓ' W) hd hwf (fun e he => .of_dom (hdom e he) (hcan e he))
      (fun e he => ihbody e he ⟨hΓ', _, hA'⟩ (W.id_lift hΓ' hA)) hw h ⟨u, hA'⟩
  | @forallE _ _ _ _ _ _ _ A B _ hd hwf hNV _ hw h hAt hBt ihA ihbody =>
    have hdom := fun e he => (hNV e he).dom
    have hcan := fun e he => (hNV e he).val
    intro Γ' hΓ' W
    obtain ⟨u, hA⟩ := hAt
    obtain ⟨v, hB⟩ := hBt
    have hA' : Γ' ⊢ A ≡ A : Term.sort u := IsDefEq.ctx_id hΓ' W hA
    have hΓ'A : ⊢ (A :: Γ') := ⟨hΓ', _, hA'⟩
    exact .forallE (ihA hΓ' W) hd  hwf (fun e he => .of_dom (hdom e he) (hcan e he))
      (fun e he => ihbody e he hΓ'A (W.id_lift hΓ' hA)) hw h ⟨u, hA'⟩
      ⟨v, IsDefEq.ctx_id hΓ'A (W.id_lift hΓ' hA) hB⟩
  | @sigma _ _ _ _ _ _ _ A B _ hd hwf hNV _ hw h hAt hBt ihA ihbody =>
    have hdom := fun e he => (hNV e he).dom
    have hcan := fun e he => (hNV e he).val
    intro Γ' hΓ' W
    obtain ⟨u, hA⟩ := hAt
    obtain ⟨v, hB⟩ := hBt
    have hA' : Γ' ⊢ A ≡ A : Term.sort u := IsDefEq.ctx_id hΓ' W hA
    have hΓ'A : ⊢ (A :: Γ') := ⟨hΓ', _, hA'⟩
    exact .sigma (ihA hΓ' W) hd  hwf (fun e he => .of_dom (hdom e he) (hcan e he))
      (fun e he => ihbody e he hΓ'A (W.id_lift hΓ' hA)) hw h ⟨u, hA'⟩
      ⟨v, IsDefEq.ctx_id hΓ'A (W.id_lift hΓ' hA) hB⟩
  | pair _ _ _ hd hNV hdc hwf _ hcty hw h hAt hat iha ihb ihA ihcode =>
    have hdx := hNV.dom
    have hxc := hNV.val
    intro Γ' hΓ' W
    obtain ⟨u, hA⟩ := hAt
    have hA' := IsDefEq.ctx_id hΓ' W hA
    exact .pair (iha hΓ' W) (ihb hΓ' W) (ihA hΓ' W) hd (.of_dom hdx hxc) hdc hwf
      (ihcode ⟨hΓ', _, hA'⟩ (W.id_lift hΓ' hA)) hcty hw h ⟨u, hA'⟩
      (IsDefEq.ctx_id hΓ' W hat)
  | fst _ hw h ihp => exact fun hΓ' W => .fst (ihp hΓ' W) hw h
  | snd _ hlab hw h hty ihp =>
    intro Γ' hΓ' W
    exact .snd (ihp hΓ' W) hlab hw h (hty.ctx W)
  | natCase_zero _ hz _ hMt ihM iha =>
    exact fun hΓ' W => .natCase_zero (ihM hΓ' W) hz (iha hΓ' W) (IsDefEq.ctx_id hΓ' W hMt)
  | natCase_succ _ hwv heq _ hMt ihM ihb =>
    intro Γ' hΓ' W
    exact .natCase_succ (ihM hΓ' W) hwv heq
      (ihb ⟨hΓ', _, .nat⟩ (W.id_lift hΓ' .nat)) (IsDefEq.ctx_id hΓ' W hMt)
  | @Y _ _ _ _ A _ _ _ _ hwx _ hdty hNV hdc _ hAt hYt ihself ihA ihb =>
    have hDom := hNV.dom
    have hxc := hNV.val
    intro Γ' hΓ' W
    obtain ⟨u, hA⟩ := hAt
    have hA' : Γ' ⊢ A ≡ A : Term.sort u := IsDefEq.ctx_id hΓ' W hA
    exact .Y (ihself hΓ' W) hwx (ihA hΓ' W) hdty (.of_dom hDom hxc) hdc
      (ihb ⟨hΓ', _, hA'⟩ (W.id_lift hΓ' hA)) ⟨u, hA'⟩
      (IsDefEq.ctx_id hΓ' W hYt)
  | id hw h hAt hat hbt =>
    intro Γ' hΓ' W
    obtain ⟨u, hA⟩ := hAt
    exact .id hw h ⟨u, IsDefEq.ctx_id hΓ' W hA⟩ (IsDefEq.ctx_id hΓ' W hat)
      (IsDefEq.ctx_id hΓ' W hbt)
  | refl hw h => exact fun _ _ => .refl hw h
  | @tr _ _ _ _ _ _ _ _ _ A _ _ _ _ _ hw hle _ _ _ _ hwv hNV hvc _ hcb hNV2 hcbc hH heq hAt hat hbt 
      ihX iha ihb ihA ihC =>
    have hvA := hNV.dom
    have hbc := hNV.val
    have hm' := hNV2.dom
    have hmc := hNV2.val
    intro Γ' hΓ' W
    obtain ⟨u, hA⟩ := hAt
    have hA' : Γ' ⊢ A ≡ A : Term.sort u := IsDefEq.ctx_id hΓ' W hA
    exact .tr hw hle (ihX hΓ' W) (iha hΓ' W) (ihb hΓ' W) (ihA hΓ' W) hwv (.of_dom hvA hbc) hvc
      (ihC ⟨hΓ', _, hA'⟩ (W.id_lift hΓ' hA)) hcb (.of_dom hm' hmc) hcbc hH heq
      ⟨u, hA'⟩ (IsDefEq.ctx_id hΓ' W hat) (IsDefEq.ctx_id hΓ' W hbt)

/-! ## Constructors at the canonical shape

Master's primed forms.  Each takes the well-formedness that `LE` needs to
be reflexive, which master gets from its shapes being a `WF` subtype. -/

theorem Interp.sort' {Δ Γ σ ρ r} :
    Interp Δ Γ (.sort r) σ ρ (TShape.sort r) :=
  .sort trivial (TShape.LE.refl (a := TShape.sort r) trivial)

theorem Interp.unit' {Δ Γ σ ρ r} :
    Interp Δ Γ (.unit r) σ ρ (TShape.unit r) :=
  .unit trivial (TShape.LE.refl (a := TShape.unit r) trivial)

theorem Interp.nat' {Δ Γ σ ρ} : Interp Δ Γ .nat σ ρ TShape.nat :=
  .nat trivial (TShape.LE.refl (a := TShape.nat) trivial)

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

theorem Interp.le_forallE {Δ Γ σ ρ m A B}
    (H : Interp Δ Γ (.forallE A B) σ ρ m) :
    m.2 = Shape.bot ∨
    ∃ n, ∃ d : Shape n, ∃ g : ShapeFun n,
      TShape.LE Δ m (Shape.T (n := n+1) (.forallE (A.subst σ) (B.subst σ.lift) d g)) := by
  cases H with
  | bot => exact .inl rfl
  | forallE _ _ _ _ _ _ h => exact .inr ⟨_, _, _, h⟩

/-- The Σ case, as `le_forallE`. -/
theorem Interp.le_sigma (H : Interp Δ Γ (.sigma A B) σ ρ m) :
    m.2 = Shape.bot ∨
      ∃ n, ∃ d : Shape n, ∃ g : ShapeFun n,
        TShape.LE Δ m
          (Shape.T (n := n+1) (.sigma (A.subst σ) (B.subst σ.lift) d g)) := by
  cases H with
  | bot => exact .inl rfl
  | sigma _ _ _ _ _ _ h => exact .inr ⟨_, _, _, h⟩

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
    (Shape.WF.piAtom hA hB) nofun nofun
    (.piAtom hA hB) (TShape.LE.T.2 (.refl (.piAtom hA hB))) ⟨u, hAΓ⟩ ⟨v, hBΓ⟩

/-- And the probe reports: if the atom approximates `⟦forallE A B⟧`, its
label is definitionally the Π's own label.  Π-injectivity is this plus
soundness, with no adequacy in between. -/
theorem Interp.le_piAtom (H : Interp Δ Γ (.forallE A B) σ ρ (Shape.T (n := 1) (.piAtom A' B'))) :
    PiLabelEq Δ A' B' (A.subst σ) (B.subst σ.lift) := by
  cases H with | forallE _ _ _ _ _ _ h _ _
  have h' := (TShape.LE.def_mp (Nat.succ_le_succ (Nat.zero_le _)) (Nat.le_refl _)) h
  rw [Shape.lift_piAtom, Shape.lift_self] at h'
  exact Shape.piAtom_le_forallE h'

/-- The Σ probe, as `piAtom`. -/
theorem Interp.sigmaAtom (hA : Δ ⊢ A.subst σ : .sort u)
    (hB : A.subst σ :: Δ ⊢ B.subst σ.lift : .sort v)
    (hAΓ : Γ ⊢ A : .sort u) (hBΓ : A :: Γ ⊢ B : .sort v) :
    Interp Δ Γ (.sigma A B) σ ρ (Shape.T (n := 1) (.sigmaAtom (A.subst σ) (B.subst σ.lift))) :=
  .sigma (d := (Shape.bot : Shape 0)) .bot (.bot .sort)
    (Shape.WF.sigmaAtom hA hB) nofun nofun
    (.sigmaAtom hA hB) (TShape.LE.T.2 (.refl (.sigmaAtom hA hB))) ⟨u, hAΓ⟩ ⟨v, hBΓ⟩

theorem Interp.le_sigmaAtom
    (H : Interp Δ Γ (.sigma A B) σ ρ (Shape.T (n := 1) (.sigmaAtom A' B'))) :
    PiLabelEq Δ A' B' (A.subst σ) (B.subst σ.lift) := by
  cases H with | sigma _ _ _ _ _ _ h _ _
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
    exact .app (ihF hΘ W) (iha hΘ W) hev' (hw.subst hΘ W) (h1.subst hΘ W)
      (hty.subst W)
  | lam _ hd hwf hNV _ hw h1 hAt ihA ihbody =>
    have hwf' := hwf.subst hΘ W; have h1' := h1.subst hΘ W
    rw [Shape.subst, subst_subst] at hwf'
    simp only [TShape.subst_T, Shape.subst, subst_subst] at h1'
    refine .lam (ihA hΘ W) (TShape.HasType.subst hΘ W hd) hwf' ?_ ?_
      (hw.subst hΘ W) h1' hAt
    · intro e' he'
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      exact TShape.Named.subst hΘ W (hNV e he)
    · intro e' he'
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have := ihbody e he hΘ W
      rwa [Subst.cons_comp, Valuation.subst_push, TShape.subst_T] at this
  | forallE _ hd hwf hNV _ hw h1 hAt hBt ihA ihbody =>
    have hwf' := hwf.subst hΘ W
    have h1' := h1.subst hΘ W
    simp only [TShape.subst_T, Shape.subst, subst_subst, ← Subst.comp_lift] at hwf' h1'
    refine .forallE (ihA hΘ W) (TShape.HasType.subst hΘ W hd) hwf'
      (fun e' he' => ?_) (fun e' he' => ?_) (hw.subst hΘ W) h1' hAt hBt
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      exact TShape.Named.subst hΘ W (hNV e he)
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have := ihbody e he hΘ W
      rwa [Subst.cons_comp, Valuation.subst_push, TShape.subst_T] at this
  | sigma _ hd hwf hNV _ hw h1 hAt hBt ihA ihbody =>
    have hwf' := hwf.subst hΘ W
    have h1' := h1.subst hΘ W
    simp only [TShape.subst_T, Shape.subst, subst_subst, ← Subst.comp_lift] at hwf' h1'
    refine .sigma (ihA hΘ W) (TShape.HasType.subst hΘ W hd) hwf'
      (fun e' he' => ?_) (fun e' he' => ?_) (hw.subst hΘ W) h1' hAt hBt
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      exact TShape.Named.subst hΘ W (hNV e he)
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have := ihbody e he hΘ W
      rwa [Subst.cons_comp, Valuation.subst_push, TShape.subst_T] at this
  | @pair _ _ _ _ _ _ _ _ _ _ _ _ _ ha hb hA hd hNV hdc hwf hcode hcty hw h1 
      hAt hat iha ihb ihA ihcode =>
    have hwf' := hwf.subst hΘ W
    have h1' := h1.subst hΘ W
    simp only [TShape.subst_T, Shape.subst, subst_subst] at hwf' h1'
    have hcode' := ihcode hΘ W
    rw [Subst.cons_comp, Valuation.subst_push, TShape.subst_T, subst_subst] at hcode'
    exact .pair (iha hΘ W) (ihb hΘ W) (ihA hΘ W)
      (TShape.HasType.subst hΘ W hd)
      (by simpa [subst_subst] using TShape.Named.subst hΘ W hNV)
      (by simpa [subst_subst] using TShape.CodeCanonS.subst hΘ W hdc)
      hwf' hcode' (by simpa using TShape.Dom.subst hΘ W hcty)
      (hw.subst hΘ W) h1' hAt hat
  | fst _ hw h1 ihp => exact .fst (ihp hΘ W) (hw.subst hΘ W) (h1.subst hΘ W)
  | snd _ hlab hw h1 hty ihp =>
    have hlab' := IsDefEq.subst hΘ W hlab
    rw [subst_subst] at hlab'
    exact .snd (ihp hΘ W) hlab' (hw.subst hΘ W) (h1.subst hΘ W) (hty.subst W)
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
  | Y _ hwx _ hdty hNV hdc _ hAt hYt ihself ihA ihb =>
    refine .Y (ihself hΘ W) (hwx.subst hΘ W) (ihA hΘ W)
      (TShape.HasType.subst hΘ W hdty)
      (by simpa [subst_subst] using TShape.Named.subst hΘ W hNV)
      (by simpa [subst_subst] using TShape.CodeCanonS.subst hΘ W hdc) ?_ hAt hYt
    have := ihb hΘ W
    rwa [Subst.cons_comp, subst_subst, Valuation.subst_push] at this
  | id hw h1 hAt hat hbt =>
    have := h1.subst hΘ W
    simp only [TShape.subst_T, Shape.subst, subst_subst] at this
    exact .id (hw.subst hΘ W) this hAt hat hbt
  | refl hw h1 => exact .refl (hw.subst hΘ W) (h1.subst hΘ W)
  | tr hw hle _ _ _ _ hwv hNV hvc _ hcb hNV2 hcbc hH heq hAt hat hbt ihX iha ihb ihA ihC =>
    have heq' := heq.subst hΘ W
    rw [subst_subst, subst_subst, subst_subst] at heq'
    refine .tr (hw.subst hΘ W) (hle.subst hΘ W) (ihX hΘ W) (iha hΘ W) (ihb hΘ W) (ihA hΘ W)
      (hwv.subst hΘ W)
      (by simpa [subst_subst] using TShape.Named.subst hΘ W hNV)
      (by simpa [subst_subst] using TShape.CodeCanonS.subst hΘ W hvc)
      ?_ (hcb.subst hΘ W)
      (by simpa [subst_subst] using TShape.Named.subst hΘ W hNV2)
      (by have h := TShape.CodeCanonS.subst hΘ W hcbc
          rwa [subst_subst, Subst.cons_comp, subst_subst] at h)
      (fun hr => by simpa [subst_subst, Term.subst] using (hH hr).subst hΘ W) heq' hAt hat hbt
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

theorem Interp.weak' {Δ : List Term} {Γ t σ' ρ m l} (hΓ : ⊢ Γ)
    (H : Interp Δ Γ t (Subst.lift_l l σ') ρ m)
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
  | succ _ hw h1 ihv => exact .succ (ihv hΓ WΓ hρ rfl) hw h1
  | app _ _ hev hw h1 hty ihF iha =>
    rw [← subst_lift'] at hev
    exact .app (ihF hΓ WΓ hρ rfl) (iha hΓ WΓ hρ rfl) hev hw h1 (hty.weak' hΓ WΓ)
  | lam _ hd hwf hNV _ hw h1 hAt ihA ihbody =>
    have hdom := fun e he => (hNV e he).dom
    have hcan := fun e he => (hNV e he).val
    rw [← subst_lift'] at hwf h1
    obtain ⟨u, hA⟩ := hAt
    refine .lam (ihA hΓ WΓ hρ rfl) hd hwf (fun e he => .of_dom (hdom e he) (hcan e he)) ?_ hw h1 ⟨u, hA.weak' WΓ⟩
    intro e he
    refine ihbody e he ⟨hΓ, _, hA⟩ (l := l.cons) WΓ.cons (fun i => ?_) Subst.lift_l_cons.symm
    cases i <;> simp_all [Valuation.push]
  | forallE _ hd hwf hNV _ hw h1 hAt hBt ihA ihbody =>
    have hdom := fun e he => (hNV e he).dom
    have hcan := fun e he => (hNV e he).val
    rw [Subst.lift_l_lift, ← subst_lift', ← subst_lift'] at hwf h1
    obtain ⟨u, hA⟩ := hAt
    obtain ⟨v, hB⟩ := hBt
    refine .forallE (ihA hΓ WΓ hρ rfl) hd hwf (fun e he => .of_dom (hdom e he) (hcan e he)) ?_ hw h1 ⟨u, hA.weak' WΓ⟩
      ⟨v, hB.weak' WΓ.cons⟩
    · intro e he
      refine ihbody e he ⟨hΓ, _, hA⟩ (l := l.cons) WΓ.cons (fun i => ?_) Subst.lift_l_cons.symm
      cases i <;> simp_all [Valuation.push]
  | sigma _ hd hwf hNV _ hw h1 hAt hBt ihA ihbody =>
    have hdom := fun e he => (hNV e he).dom
    have hcan := fun e he => (hNV e he).val
    rw [Subst.lift_l_lift, ← subst_lift', ← subst_lift'] at hwf h1
    obtain ⟨u, hA⟩ := hAt
    obtain ⟨v, hB⟩ := hBt
    refine .sigma (ihA hΓ WΓ hρ rfl) hd hwf (fun e he => .of_dom (hdom e he) (hcan e he)) ?_ hw h1 ⟨u, hA.weak' WΓ⟩
      ⟨v, hB.weak' WΓ.cons⟩
    · intro e he
      refine ihbody e he ⟨hΓ, _, hA⟩ (l := l.cons) WΓ.cons (fun i => ?_) Subst.lift_l_cons.symm
      cases i <;> simp_all [Valuation.push]
  | pair _ _ _ hd hNV hdc hwf _ hcty hw h1 hAt hat iha ihb ihA ihcode =>
    have hdx := hNV.dom
    have hxc := hNV.val
    simp only [← subst_lift'] at hwf h1 hdc hxc
    obtain ⟨u, hA⟩ := hAt
    refine .pair (iha hΓ WΓ hρ rfl) (ihb hΓ WΓ hρ rfl) (ihA hΓ WΓ hρ rfl) hd (.of_dom hdx hxc) hdc
      hwf ?_
      hcty hw h1 ⟨u, hA.weak' WΓ⟩ (hat.weak' WΓ)
    refine ihcode ⟨hΓ, _, hA⟩ (l := l.cons) WΓ.cons (fun i => ?_)
      (by rw [subst_lift']; exact Subst.lift_l_cons.symm)
    cases i <;> simp_all [Valuation.push]
  | fst _ hw h1 ihp => exact .fst (ihp hΓ WΓ hρ rfl) hw h1
  | snd _ hlab hw h1 hty ihp =>
    rw [← subst_lift'] at hlab
    exact .snd (ihp hΓ WΓ hρ rfl) hlab hw h1 (by simpa using hty.weak' hΓ WΓ)
  | natCase_zero _ hz _ hMt ihM iha =>
    rw [← subst_lift'] at hz
    exact .natCase_zero (ihM hΓ WΓ hρ rfl) hz (iha hΓ WΓ hρ rfl) (by simpa using hMt.weak' WΓ)
  | natCase_succ _ hwv heq _ hMt ihM ihb =>
    rw [← subst_lift'] at heq
    refine .natCase_succ (ihM hΓ WΓ hρ rfl) hwv heq ?_ (by simpa using hMt.weak' WΓ)
    refine ihb ⟨hΓ, _, .nat⟩ (l := l.cons) (by simpa using WΓ.cons (A := Term.nat)) (fun i => ?_)
      Subst.lift_l_cons.symm
    cases i <;> simp_all [Valuation.push]
  | Y _ hwx hA hdty hNV hdc _ hAt hYt ihself ihA ihb =>
    have hDom := hNV.dom
    have hxc := hNV.val
    obtain ⟨u, hA⟩ := hAt
    simp only [← subst_lift'] at hdc hxc
    refine .Y (ihself hΓ WΓ hρ rfl) hwx (ihA hΓ WΓ hρ rfl) hdty (.of_dom hDom hxc) hdc ?_
      ⟨u, hA.weak' WΓ⟩
      (by simpa using hYt.weak' WΓ)
    refine ihb ⟨hΓ, _, hA⟩ (l := l.cons) WΓ.cons (fun i => ?_) ?_
    · cases i <;> simp_all [Valuation.push]
    · rw [← Subst.lift_l_cons]
      exact congrArg _ (subst_lift' (e := Term.Y _ _))
  | id hw h1 hAt hat hbt =>
    simp only [← subst_lift'] at h1
    obtain ⟨u, hA⟩ := hAt
    exact .id hw h1 ⟨u, hA.weak' WΓ⟩ (hat.weak' WΓ) (hbt.weak' WΓ)
  | refl hw h1 => exact .refl hw h1
  | tr hw hle _ _ _ _ hwv hNV hvc _ hcb hNV2 hcbc hH heq hAt hat hbt ihX iha ihb ihA ihC =>
    have hvA := hNV.dom
    have hbc := hNV.val
    have hm' := hNV2.dom
    have hmc := hNV2.val
    rw [← subst_lift', ← subst_lift', ← subst_lift'] at heq
    simp only [← subst_lift'] at hvc hbc
    obtain ⟨u, hA⟩ := hAt
    refine .tr hw hle (ihX hΓ WΓ hρ rfl) (iha hΓ WΓ hρ rfl) (ihb hΓ WΓ hρ rfl) (ihA hΓ WΓ hρ rfl)
      hwv (.of_dom hvA hbc) hvc ?_ hcb
      (by simpa only [subst_lift'] using TShape.Named.of_dom hm' hmc)
      (by simpa only [subst_lift', Subst.lift_l_cons] using hcbc)
      (fun hr => by simpa only [← subst_lift'] using hH hr) heq
      ⟨u, hA.weak' WΓ⟩
      (hat.weak' WΓ) (hbt.weak' WΓ)
    refine ihC ⟨hΓ, _, hA⟩ (l := l.cons) WΓ.cons (fun i => ?_) ?_
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
    exact .app (ihF hΓ' Wθ rfl hθ) (iha hΓ' Wθ rfl hθ) hev hw h1 (hty.substTerm Wθ)
  | @lam _ _ _ _ _ _ _ A _ hA hd hwf hNV hbody hw h1 hAt ihA ihbody =>
    have hdom := fun e he => (hNV e he).dom
    have hcan := fun e he => (hNV e he).val
    intro Γ' θ σ ρ hΓ' Wθ hτ hθ
    subst hτ
    rw [← subst_subst] at hwf h1
    obtain ⟨u, hAty⟩ := hAt
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hAty.subst hΓ' Wθ
    refine .lam (ihA hΓ' Wθ rfl hθ) hd hwf (fun e he => .of_dom (hdom e he) (hcan e he)) (fun e he => ?_) hw h1 ⟨u, hAθ⟩
    refine ihbody e he ⟨hΓ', _, hAθ⟩ (Wθ.lift hAty hAθ) Subst.lift_comp_cons.symm (fun i => ?_)
    cases i with
    | zero => exact .bvar (hwf.2.2.1.1 e he).2.2.1 (TShape.LE.refl (hwf.2.2.1.1 e he).2.2.1)
    | succ i => exact Interp.weak' (l := .skip .refl) hΓ' (hθ i) (.skip .refl) (fun _ => rfl)
  | @forallE _ _ _ _ _ _ _ A B hA hd hwf hNV hbody hw h1 hAt hBt ihA ihbody =>
    have hdom := fun e he => (hNV e he).dom
    have hcan := fun e he => (hNV e he).val
    intro Γ' θ σ ρ hΓ' Wθ hτ hθ
    subst hτ
    rw [Subst.comp_lift, ← subst_subst, ← subst_subst] at hwf h1
    obtain ⟨u, hAty⟩ := hAt
    obtain ⟨v, hBty⟩ := hBt
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hAty.subst hΓ' Wθ
    have hΓ'A : ⊢ (A.subst θ :: Γ') := ⟨hΓ', _, hAθ⟩
    refine .forallE (ihA hΓ' Wθ rfl hθ) hd hwf (fun e he => .of_dom (hdom e he) (hcan e he)) (fun e he => ?_) hw h1
      ⟨u, hAθ⟩ ⟨v, hBty.subst hΓ'A (Wθ.lift hAty hAθ)⟩
    · refine ihbody e he hΓ'A (Wθ.lift hAty hAθ) Subst.lift_comp_cons.symm (fun i => ?_)
      cases i with
      | zero =>
        exact .bvar (hwf.2.2.2.1.1 e he).2.2.1 (TShape.LE.refl (hwf.2.2.2.1.1 e he).2.2.1)
      | succ i => exact Interp.weak' (l := .skip .refl) hΓ' (hθ i) (.skip .refl) (fun _ => rfl)
  | @sigma _ _ _ _ _ _ _ A B hA hd hwf hNV hbody hw h1 hAt hBt ihA ihbody =>
    have hdom := fun e he => (hNV e he).dom
    have hcan := fun e he => (hNV e he).val
    intro Γ' θ σ ρ hΓ' Wθ hτ hθ
    subst hτ
    rw [Subst.comp_lift, ← subst_subst, ← subst_subst] at hwf h1
    obtain ⟨u, hAty⟩ := hAt
    obtain ⟨v, hBty⟩ := hBt
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hAty.subst hΓ' Wθ
    have hΓ'A : ⊢ (A.subst θ :: Γ') := ⟨hΓ', _, hAθ⟩
    refine .sigma (ihA hΓ' Wθ rfl hθ) hd hwf (fun e he => .of_dom (hdom e he) (hcan e he)) (fun e he => ?_) hw h1
      ⟨u, hAθ⟩ ⟨v, hBty.subst hΓ'A (Wθ.lift hAty hAθ)⟩
    · refine ihbody e he hΓ'A (Wθ.lift hAty hAθ) Subst.lift_comp_cons.symm (fun i => ?_)
      cases i with
      | zero =>
        exact .bvar (hwf.2.2.2.1.1 e he).2.2.1 (TShape.LE.refl (hwf.2.2.2.1.1 e he).2.2.1)
      | succ i => exact Interp.weak' (l := .skip .refl) hΓ' (hθ i) (.skip .refl) (fun _ => rfl)
  | pair _ _ _ hd hNV hdc hwf _ hcty hw h1 hAt hat iha ihb ihA ihcode =>
    have hdx := hNV.dom
    have hxc := hNV.val
    intro Γ' θ σ ρ hΓ' Wθ hτ hθ
    subst hτ
    rw [← subst_subst] at hwf h1 hdc hxc
    obtain ⟨u, hAty⟩ := hAt
    have hAθ := hAty.subst hΓ' Wθ
    refine .pair (iha hΓ' Wθ rfl hθ) (ihb hΓ' Wθ rfl hθ) (ihA hΓ' Wθ rfl hθ) hd (.of_dom hdx hxc) hdc
      (by simpa [← subst_subst] using hwf) ?_ hcty hw
      (by simpa [← subst_subst] using h1) ⟨u, hAθ⟩ (hat.subst hΓ' Wθ)
    refine ihcode ⟨hΓ', _, hAθ⟩ (Wθ.lift hAty hAθ)
      (by rw [← subst_subst]; exact Subst.lift_comp_cons.symm) (fun i => ?_)
    cases i with
    | zero =>
      exact .bvar (TShape.WF.T.2 hwf.2.2.2.1) (TShape.LE.refl (TShape.WF.T.2 hwf.2.2.2.1))
    | succ i => exact Interp.weak' (l := .skip .refl) hΓ' (hθ i) (.skip .refl) (fun _ => rfl)
  | fst _ hw h1 ihp =>
    intro _ _ _ _ hΓ' Wθ hτ hθ; exact .fst (ihp hΓ' Wθ hτ hθ) hw h1
  | snd _ hlab hw h1 hty ihp =>
    intro Γ' θ σ ρ hΓ' Wθ hτ hθ
    subst hτ
    rw [← subst_subst] at hlab
    exact .snd (ihp hΓ' Wθ rfl hθ) hlab hw h1 (by simpa using hty.substTerm Wθ)
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
    | succ i => exact Interp.weak' (l := .skip .refl) hΓ' (hθ i) (.skip .refl) (fun _ => rfl)
  | @Y _ _ _ _ A b _ _ _ hwx _ hdty hNV hdc _ hAt hYt ihself ihA ihb =>
    have hDom := hNV.dom
    have hxc := hNV.val
    intro Γ' θ σ ρ hΓ' Wθ hτ hθ
    subst hτ
    rw [← subst_subst] at hdc hxc
    obtain ⟨u, hAty⟩ := hAt
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hAty.subst hΓ' Wθ
    refine .Y (ihself hΓ' Wθ rfl hθ) hwx (ihA hΓ' Wθ rfl hθ) hdty (.of_dom hDom hxc) hdc ?_ ⟨u, hAθ⟩
      (by simpa using hYt.subst hΓ' Wθ)
    simp only [Term.subst, subst_subst, ← Subst.comp_lift]
    refine ihb ⟨hΓ', _, hAθ⟩ (Wθ.lift hAty hAθ) Subst.lift_comp_cons.symm (fun i => ?_)
    cases i with
    | zero => exact .bvar hwx (TShape.LE.refl hwx)
    | succ i => exact Interp.weak' (l := .skip .refl) hΓ' (hθ i) (.skip .refl) (fun _ => rfl)
  | id hw h1 hAt hat hbt =>
    intro Γ' θ σ ρ hΓ' Wθ hτ hθ
    subst hτ
    simp only [← subst_subst] at h1
    obtain ⟨u, hAty⟩ := hAt
    exact .id hw h1 ⟨u, hAty.subst hΓ' Wθ⟩ (hat.subst hΓ' Wθ) (hbt.subst hΓ' Wθ)
  | refl hw h1 =>
    intro _ _ _ _ _ _ _ _; exact .refl hw h1
  | @tr _ _ _ _ _ _ _ _ _ A _ _ _ _ _ hw hle _ _ _ _ hwv hNV hvc _ hcb hNV2 hcbc hH heq hAt hat hbt 
      ihX iha ihb ihA ihC =>
    have hvA := hNV.dom
    have hbc := hNV.val
    have hm' := hNV2.dom
    have hmc := hNV2.val
    intro Γ' θ σ ρ hΓ' Wθ hτ hθ
    subst hτ
    rw [← subst_subst, ← subst_subst, ← subst_subst] at heq
    rw [← subst_subst] at hvc hbc
    obtain ⟨u, hAty⟩ := hAt
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hAty.subst hΓ' Wθ
    refine .tr hw hle (ihX hΓ' Wθ rfl hθ) (iha hΓ' Wθ rfl hθ) (ihb hΓ' Wθ rfl hθ)
      (ihA hΓ' Wθ rfl hθ) hwv (.of_dom hvA hbc) hvc ?_ hcb
      (by simpa only [subst_subst] using TShape.Named.of_dom hm' hmc)
      (by simpa only [subst_subst, Subst.lift_comp_cons] using hcbc)
      (fun hr => by simpa only [← subst_subst] using hH hr) heq
      ⟨u, hAθ⟩ (hat.subst hΓ' Wθ) (hbt.subst hΓ' Wθ)
    rw [subst_subst]
    refine ihC ⟨hΓ', _, hAθ⟩ (Wθ.lift hAty hAθ) Subst.lift_comp_cons.symm (fun i => ?_)
    cases i with
    | zero => exact .bvar hwv (TShape.LE.refl hwv)
    | succ i => exact Interp.weak' (l := .skip .refl) hΓ' (hθ i) (.skip .refl) (fun _ => rfl)

/-- **Strengthening along a renaming**, the direction `Interp.weak'` does
not give.  With the labels' typings in the clauses this is no longer a
statement about raw terms: moving an interpretation into a *smaller*
context means moving its typings there, and the syntax has weakening but
not strengthening.  So the lemma is indexed by a typing of the term in
the small context, and the induction runs on that — the same shape as
`IsDefEq.stage`, and for the same reason.

Master proves the raw version by casing on the term at each step; here
each case of the *typing* supplies the premises the clause needs. -/
theorem Interp.unweak {Δ : List Term} (hΔ : ⊢ Δ) :
    ∀ {t : Term} {Γ Γ' : List Term} {l σ' ρ ρ' m}, ⊢ Γ → t.Annot Γ →
      Ctx.Lift' l Γ Γ' → Ctx.SubstEq Δ σ' σ' Γ' → (∀ i, ρ i = ρ' (Lift.liftVar l i)) →
      Interp Δ Γ' (t.lift' l) σ' ρ' m → Interp Δ Γ t (σ'.lift_l l) ρ m := by
  intro t
  induction t with
  | bvar i =>
    intro Γ Γ' l σ' ρ ρ' m _ _ _ _ hρ H
    cases H with
    | bot => exact .bot
    | bvar hw hle => exact .bvar hw (hρ _ ▸ hle)
  | sort u =>
    intro Γ Γ' l σ' ρ ρ' m _ _ _ _ _ H
    cases H with
    | bot => exact .bot
    | sort hw hle => exact .sort hw hle
  | unit r =>
    intro Γ Γ' l σ' ρ ρ' m _ _ _ _ _ H
    cases H with
    | bot => exact .bot
    | unit hw hle => exact .unit hw hle
  | star r =>
    intro Γ Γ' l σ' ρ ρ' m _ _ _ _ _ H
    cases H with | bot => exact .bot
  | nat =>
    intro Γ Γ' l σ' ρ ρ' m _ _ _ _ _ H
    cases H with
    | bot => exact .bot
    | nat hw hle => exact .nat hw hle
  | zero =>
    intro Γ Γ' l σ' ρ ρ' m _ _ _ _ _ H
    cases H with
    | bot => exact .bot
    | zero hw hle => exact .zero hw hle
  | succ N ih =>
    intro Γ Γ' l σ' ρ ρ' m hΓ hAnn WΓ hd hρ H
    cases H with
    | bot => exact .bot
    | succ hv hw hle => exact .succ (ih hΓ hAnn WΓ hd hρ hv) hw hle
  | app F a ihF iha =>
    intro Γ Γ' l σ' ρ ρ' m hΓ hAnn WΓ hd hρ H
    obtain ⟨hat, hAF, hAa⟩ := hAnn
    cases H with
    | bot => exact .bot
    | app hF hx hev hw hle hty =>
      rw [subst_lift'] at hev
      exact .app (ihF hΓ hAF WΓ hd hρ hF) (iha hΓ hAa WΓ hd hρ hx) hev hw hle
        (hty.unweak WΓ hd)
  | lam A b ihA ihb =>
    intro Γ Γ' l σ' ρ ρ' m hΓ hAnn WΓ hd hρ H
    obtain ⟨⟨u, hA⟩, hAA, hAb⟩ := hAnn
    cases H with
    | bot => exact .bot
    | lam hAint hdty hwf hNV hbody hw hle _ =>
      have hdom := fun e he => (hNV e he).dom
      have hcan := fun e he => (hNV e he).val
      simp only [subst_lift'] at hwf hle
      have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
      refine .lam (ihA hΓ hAA WΓ hd hρ hAint) hdty hwf (fun e he => .of_dom (hdom e he) (hcan e he)) (fun e he => ?_) hw hle
        ⟨u, hA⟩
      have htm : Δ ⊢ e.tm : (A.lift' l).subst σ' := by
        rw [subst_lift']
        exact (hwf.2.2.1.1 e he).2.1
      have hd' : Ctx.SubstEq Δ (σ'.cons e.tm) (σ'.cons e.tm) (A.lift' l :: Γ') :=
        .cons hd (hA.weak' WΓ) htm
      rw [Subst.lift_l_cons]
      exact ihb hΓA hAb WΓ.cons hd' (fun i => by cases i <;> simp_all [Valuation.push])
        (hbody e he)
  | forallE A B ihA ihB =>
    intro Γ Γ' l σ' ρ ρ' m hΓ hAnn WΓ hd hρ H
    obtain ⟨⟨u, hA⟩, ⟨v, hB⟩, hAA, hAB⟩ := hAnn
    cases H with
    | bot => exact .bot
    | forallE hAint hdty hwf hNV hbody hw hle _ _ =>
      have hdom := fun e he => (hNV e he).dom
      have hcan := fun e he => (hNV e he).val
      simp only [subst_lift', ← Subst.lift_l_lift] at hwf hle
      have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
      refine .forallE (ihA hΓ hAA WΓ hd hρ hAint) hdty hwf (fun e he => .of_dom (hdom e he) (hcan e he)) (fun e he => ?_) hw hle
        ⟨u, hA⟩ ⟨v, hB⟩
      have htm : Δ ⊢ e.tm : (A.lift' l).subst σ' := by
        have := (hwf.2.2.2.1.1 e he).2.1
        first | exact this | (rw [subst_lift']; exact this)
      have hd' : Ctx.SubstEq Δ (σ'.cons e.tm) (σ'.cons e.tm) (A.lift' l :: Γ') :=
        .cons hd (hA.weak' WΓ) htm
      rw [Subst.lift_l_cons]
      exact ihB hΓA hAB WΓ.cons hd' (fun i => by cases i <;> simp_all [Valuation.push])
        (hbody e he)
  | sigma A B ihA ihB =>
    intro Γ Γ' l σ' ρ ρ' m hΓ hAnn WΓ hd hρ H
    obtain ⟨⟨u, hA⟩, ⟨v, hB⟩, hAA, hAB⟩ := hAnn
    cases H with
    | bot => exact .bot
    | sigma hAint hdty hwf hNV hbody hw hle _ _ =>
      have hdom := fun e he => (hNV e he).dom
      have hcan := fun e he => (hNV e he).val
      simp only [subst_lift', ← Subst.lift_l_lift] at hwf hle
      have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
      refine .sigma (ihA hΓ hAA WΓ hd hρ hAint) hdty hwf (fun e he => .of_dom (hdom e he) (hcan e he)) (fun e he => ?_) hw hle
        ⟨u, hA⟩ ⟨v, hB⟩
      have htm : Δ ⊢ e.tm : (A.lift' l).subst σ' := by
        have := (hwf.2.2.2.1.1 e he).2.1
        first | exact this | (rw [subst_lift']; exact this)
      have hd' : Ctx.SubstEq Δ (σ'.cons e.tm) (σ'.cons e.tm) (A.lift' l :: Γ') :=
        .cons hd (hA.weak' WΓ) htm
      rw [Subst.lift_l_cons]
      exact ihB hΓA hAB WΓ.cons hd' (fun i => by cases i <;> simp_all [Valuation.push])
        (hbody e he)
  | pair A B a b ihA ihB iha ihb =>
    intro Γ Γ' l σ' ρ ρ' m hΓ hAnn WΓ hd hρ H
    obtain ⟨⟨u, hA⟩, ⟨v, hB⟩, hat, hAA, hAB, hAa, hAb⟩ := hAnn
    cases H with
    | bot => exact .bot
    | pair hainp hbout hAint hdty hNV hdc hwf hcode hcty hw hle _ _ =>
      have hdx := hNV.dom
      have hxc := hNV.val
      simp only [subst_lift'] at hwf hle hdc hxc
      refine .pair (iha hΓ hAa WΓ hd hρ hainp) (ihb hΓ hAb WΓ hd hρ hbout)
        (ihA hΓ hAA WΓ hd hρ hAint) hdty (.of_dom hdx hxc) hdc hwf ?_ hcty hw hle ⟨u, hA⟩ hat
      have htm : Δ ⊢ (a.lift' l).subst σ' : (A.lift' l).subst σ' :=
        IsDefEq.subst hΔ hd (hat.weak' WΓ)
      have hd' : Ctx.SubstEq Δ (σ'.cons ((a.lift' l).subst σ'))
          (σ'.cons ((a.lift' l).subst σ')) (A.lift' l :: Γ') :=
        .cons hd (hA.weak' WΓ) htm
      rw [Subst.lift_l_cons, ← subst_lift']
      exact ihB ⟨hΓ, _, hA⟩ hAB WΓ.cons hd'
        (fun i => by cases i <;> simp_all [Valuation.push]) hcode
  | fst p ih =>
    intro Γ Γ' l σ' ρ ρ' m hΓ hAnn WΓ hd hρ H
    cases H with
    | bot => exact .bot
    | fst hp hw hle => exact .fst (ih hΓ hAnn WΓ hd hρ hp) hw hle
  | snd p ih =>
    intro Γ Γ' l σ' ρ ρ' m hΓ hAnn WΓ hd hρ H
    obtain ⟨hft, hAp⟩ := hAnn
    cases H with
    | bot => exact .bot
    | snd hp hev hw hle hty =>
      simp only [Term.subst, subst_lift'] at hev
      exact .snd (ih hΓ hAp WΓ hd hρ hp) hev hw hle
        (Stable.unweak (a := Term.fst p) WΓ hd hty)
  | natCase C M a b ihC ihM iha ihb =>
    intro Γ Γ' l σ' ρ ρ' m hΓ hAnn WΓ hd hρ H
    obtain ⟨hMt, hAC, hAM, hAa, hAb⟩ := hAnn
    cases H with
    | bot => exact .bot
    | natCase_zero hM hz ha _ =>
      rw [subst_lift'] at hz
      exact .natCase_zero (ihM hΓ hAM WΓ hd hρ hM) hz (iha hΓ hAa WΓ hd hρ ha) hMt
    | natCase_succ hM hwv heq hbody _ =>
      rw [subst_lift'] at heq
      refine .natCase_succ (ihM hΓ hAM WΓ hd hρ hM) hwv heq ?_ hMt
      have hd' : Ctx.SubstEq Δ (σ'.cons _) (σ'.cons _) (Term.nat :: Γ') :=
        .cons hd .nat (heq.succ_regular (.inr rfl))
      rw [Subst.lift_l_cons]
      refine ihb ⟨hΓ, _, .nat⟩ hAb (by simpa using WΓ.cons (A := Term.nat)) hd'
        (fun i => ?_) (by simpa using hbody)
      cases i with
      | zero => rfl
      | succ i => simp [Valuation.push, hρ i]
  | Y A b ihA ihb =>
    intro Γ Γ' l σ' ρ ρ' m hΓ hAnn WΓ hd hρ H
    obtain ⟨⟨u, hA⟩, hYt, hAA, hAb⟩ := hAnn
    -- the tower is not structural in the term, so this one case runs on
    -- the derivation: each level's self-premise is the level below
    have key : ∀ {Γ₂ : List Term} {t' σ₂ ρ₂ m}, Interp Δ Γ₂ t' σ₂ ρ₂ m →
        ∀ {l ρ}, t' = (Term.Y A b).lift' l → Ctx.Lift' l Γ Γ₂ →
          Ctx.SubstEq Δ σ₂ σ₂ Γ₂ → (∀ i, ρ i = ρ₂ (Lift.liftVar l i)) →
          Interp Δ Γ (Term.Y A b) (σ₂.lift_l l) ρ m := by
      intro Γ₂ t' σ₂ ρ₂ m H
      induction H with
      | @Y Γ₂ σ₂ ρ₂ m A₂ b₂ x d hx hwx hAd hdty hNV hdc hbody _ _ ihx _ _ =>
        have hDom := hNV.dom
        have hxc := hNV.val
        intro l ρ ht' WΓ hd hρ
        cases ht'
        have hYsub : ((A.lift' l).Y (b.lift' l.cons)).subst σ₂
            = (Term.Y A b).subst (σ₂.lift_l l) := subst_lift' (e := Term.Y A b)
        have hd' : Ctx.SubstEq Δ (σ₂.cons ((Term.Y A b).subst (σ₂.lift_l l)))
            (σ₂.cons ((Term.Y A b).subst (σ₂.lift_l l))) (A.lift' l :: Γ₂) :=
          .cons hd (hA.weak' WΓ)
            (hYsub ▸ IsDefEq.subst hΔ hd (hYt.weak' WΓ))
        refine .Y (ihx rfl WΓ hd hρ) hwx (ihA hΓ hAA WΓ hd hρ hAd) hdty
          (.of_dom hDom (hYsub ▸ hxc))
          (by simpa only [subst_lift'] using hdc) ?_ ⟨u, hA⟩ hYt
        rw [Subst.lift_l_cons]
        refine ihb ⟨hΓ, _, hA⟩ hAb WΓ.cons hd' (fun i => ?_) (hYsub ▸ hbody)
        cases i with
        | zero => rfl
        | succ i => simp [Valuation.push, hρ i]
      | bot => exact fun _ _ _ _ => .bot
      | _ => intro l ρ ht' _ _ _; simp at ht'
    exact key H rfl WΓ hd hρ
  | id r A a b ihA iha ihb =>
    intro Γ Γ' l σ' ρ ρ' m hΓ hAnn WΓ hd hρ H
    obtain ⟨⟨u, hA⟩, hat, hbt, hAA, hAa, hAb⟩ := hAnn
    cases H with
    | bot => exact .bot
    | id hw hle _ _ _ =>
      simp only [subst_lift'] at hle
      exact .id hw hle ⟨u, hA⟩ hat hbt
  | refl r a ih =>
    intro Γ Γ' l σ' ρ ρ' m hΓ hAnn WΓ hd hρ H
    cases H with
    | bot => exact .bot
    | refl hw hle => exact .refl hw hle
  | tr r A a b C X Hp ihA iha ihb ihC ihX ihH =>
    intro Γ Γ' l σ' ρ ρ' m hΓ hAnn WΓ hd hρ H
    obtain ⟨⟨u, hA⟩, hat, hbt, hht, _, hAA, hAa, hAb, hAC, hAX, hAH⟩ := hAnn
    cases H with
    | bot => exact .bot
    | tr hw hle hX ha hb hAint hwv hNV hvc hC hcb hNV2 hcbc hH heq _ _ _ =>
      have hvA := hNV.dom
      have hbc := hNV.val
      have hm' := hNV2.dom
      have hmc := hNV2.val
      simp only [subst_lift'] at heq hvc hbc hmc
      simp only [subst_lift'] at hcbc
      refine .tr hw hle (ihX hΓ hAX WΓ hd hρ hX) (iha hΓ hAa WΓ hd hρ ha)
        (ihb hΓ hAb WΓ hd hρ hb) (ihA hΓ hAA WΓ hd hρ hAint) hwv (.of_dom hvA hbc) hvc ?_ hcb (.of_dom hm' hmc)
        (by simpa only [Subst.lift_l_cons] using hcbc)
        (fun hr => by simpa only [subst_lift'] using hH hr) heq ⟨u, hA⟩ hat hbt
      have hd' : Ctx.SubstEq Δ (σ'.cons (b.subst (σ'.lift_l l)))
          (σ'.cons (b.subst (σ'.lift_l l))) (A.lift' l :: Γ') :=
        .cons hd (hA.weak' WΓ)
          (by simpa [subst_lift'] using IsDefEq.subst hΔ hd (hbt.weak' WΓ))
      rw [Subst.lift_l_cons]
      refine ihC ⟨hΓ, _, hA⟩ hAC WΓ.cons hd' (fun i => ?_)
        (by simpa [subst_lift'] using hC)
      cases i with
      | zero => rfl
      | succ i => simp [Valuation.push, hρ i]

/-- The transported value's annotated type is the motive at `b`, at a
stage where the endpoints agree. -/
theorem TyEq.tr_motive {Γ Δ : List Term} {A a a₀ b C C₀ : Term} {u v : Bool} {σ : Subst}
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hA : Γ ⊢ A : .sort u)
    (ha₀ : Γ ⊢ a₀ ≡ a : A) (hC₀ : A :: Γ ⊢ C₀ ≡ C : .sort v)
    (heq : Δ ⊢ a.subst σ ≡ b.subst σ : A.subst σ) :
    TyEq Δ ((C₀.inst a₀).subst σ) (C.subst (σ.cons (b.subst σ))) := by
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  have hC1 := hC₀.subst (Γ₀ := A.subst σ :: Δ) ⟨hΔ, _, hAσ⟩ (W.lift hA hAσ)
  rw [subst_inst, ← inst_lift_cons]
  exact ⟨v, IsDefEq.instDF hΔ hAσ .sort hC1 ((ha₀.subst hΔ W).trans heq)⟩

/-- **Stage invariance.**  The interpretation depends on its stage only up
to definitional equality.  Master needs no such lemma, his shapes carrying
no labels; the other repo gets it from the quotient, two definitionally
equal substitutions being the *same* morphism of `Ctx`.

Here every clause carries what its own labels need to move: a binder's
annotation is typed in `Γ` (so `IsDefEq.subst'` moves its label), a
`natCase`'s scrutinee is a numeral (so its branch equation moves), a
`pair`'s first component is typed at the annotation (so the entries' label
terms move), and an `app`'s or `snd`'s query is `Stable` at the shape's
label — which is exactly the equation `TEvaluates.mono` asks for, and the
one thing no typing in `Γ` could supply, the label being a term of `Δ`.

So the induction is structural in the term, with `Term.Annot` for the
annotations.  `Y` is the one case that is not structural: its tower
premise is the same term one level down, so that case runs on the
derivation. -/
theorem Interp.stage {Δ : List Term} (hΔ : ⊢ Δ) :
    ∀ {t : Term} {Γ : List Term} {σ σ₂ ρ m}, ⊢ Γ → t.Annot Γ →
      Ctx.SubstEq Δ σ σ₂ Γ → Interp Δ Γ t σ ρ m → Interp Δ Γ t σ₂ ρ m := by
  intro t
  induction t with
  | bvar i =>
    intro Γ σ σ₂ ρ m _ _ _ H
    cases H with
    | bot => exact .bot
    | bvar hw hle => exact .bvar hw hle
  | sort u =>
    intro Γ σ σ₂ ρ m _ _ _ H
    cases H with
    | bot => exact .bot
    | sort hw hle => exact .sort hw hle
  | unit r =>
    intro Γ σ σ₂ ρ m _ _ _ H
    cases H with
    | bot => exact .bot
    | unit hw hle => exact .unit hw hle
  | star r =>
    intro Γ σ σ₂ ρ m _ _ _ H
    cases H with | bot => exact .bot
  | nat =>
    intro Γ σ σ₂ ρ m _ _ _ H
    cases H with
    | bot => exact .bot
    | nat hw hle => exact .nat hw hle
  | zero =>
    intro Γ σ σ₂ ρ m _ _ _ H
    cases H with
    | bot => exact .bot
    | zero hw hle => exact .zero hw hle
  | succ N ih =>
    intro Γ σ σ₂ ρ m hΓ hAnn W H
    cases H with
    | bot => exact .bot
    | succ hv hw hle => exact .succ (ih hΓ hAnn W hv) hw hle
  | app F a ihF iha =>
    intro Γ σ σ₂ ρ m hΓ hAnn W H
    obtain ⟨hat, hAF, hAa⟩ := hAnn
    cases H with
    | bot => exact .bot
    | app hF hx hev hw hle hty =>
      have heq := hty.move hΔ W
      exact .app (ihF hΓ hAF W hF) (iha hΓ hAa W hx)
        (TEvaluates.mono hΔ ⟨heq.hasType.1.isType hΔ, heq⟩ (TShape.LE.refl hx.wf) hev)
        hw hle (hty.stage W)
  | lam A b ihA ihb =>
    intro Γ σ σ₂ ρ m hΓ hAnn W H
    obtain ⟨⟨u, hA⟩, hAA, hAb⟩ := hAnn
    have hAσ : TyEq Δ (A.subst σ) (A.subst σ₂) := ⟨u, IsDefEq.subst' hΔ W hA⟩
    cases H with
    | bot => exact .bot
    | @lam _ _ _ _ _ _ _ _ _ hAint hdty hwf hNV hbody hw hle _ =>
      have hdom := fun e he => (hNV e he).dom
      have hcan := fun e he => (hNV e he).val
      refine .lam (ihA hΓ hAA W hAint) hdty
        ⟨hwf.1, hwf.2.1, hwf.2.2.1.retype hAσ, hAσ.refl_r⟩
        (fun e he => .of_dom (hdom e he) (hcan e he)) (fun e he => ?_) hw
        (hle.trans hΔ (TShape.LE.T.2
          ⟨ShapeFun.LE.refl hwf.2.2.1, hwf.1, hwf.2.1, hAσ, hwf.2.2.2⟩))
        ⟨u, hA⟩
      have W' : Ctx.SubstEq Δ (σ.cons e.tm) (σ₂.cons e.tm) (A :: Γ) :=
        .cons W hA (hwf.2.2.1.1 e he).2.1
      exact ihb ⟨hΓ, _, hA⟩ hAb W' (hbody e he)
  | forallE A B ihA ihB =>
    intro Γ σ σ₂ ρ m hΓ hAnn W H
    obtain ⟨⟨u, hA⟩, ⟨v, hB⟩, hAA, hAB⟩ := hAnn
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
    have hAσ : Δ ⊢ A.subst σ ≡ A.subst σ₂ : .sort u := IsDefEq.subst' hΔ W hA
    have hBσ : A.subst σ :: Δ ⊢ B.subst σ.lift ≡ B.subst σ₂.lift : .sort v :=
      IsDefEq.subst' (Γ₀ := A.subst σ :: Δ) ⟨hΔ, _, hAσ.hasType.1⟩
        (W.lift hA hAσ.hasType.1) hB
    cases H with
    | bot => exact .bot
    | forallE hAint hdty hwf hNV hbody hw hle _ _ =>
      have hdom := fun e he => (hNV e he).dom
      have hcan := fun e he => (hNV e he).val
      refine .forallE (ihA hΓ hAA W hAint) hdty
        ⟨⟨u, hAσ.hasType.2⟩, ⟨v, (hAσ.defeqDF_l hΔ hBσ).hasType.2⟩, hwf.2.2.1,
          hwf.2.2.2.1.retype ⟨u, hAσ⟩,
          hwf.2.2.2.2.1.conv ⟨u, hAσ.symm⟩,
          fun e he => (hwf.2.2.2.2.2 e he).conv
            ⟨v, (hAσ.hasType.2).instDF hΔ .sort (hAσ.defeqDF_l hΔ hBσ).symm
              (hAσ.defeqDF ((hwf.2.2.2.1.1 e he).2.1))⟩⟩
        (fun e he => .of_dom (hdom e he) (hcan e he)) (fun e he => ?_) hw
        (hle.trans hΔ (TShape.LE.T.2
          ⟨⟨⟨u, hAσ⟩, v, hBσ⟩, .refl hwf.2.2.1, .refl hwf.2.2.2.1,
            hwf.2.2.2.2.1, hwf.2.2.2.2.2⟩))
        ⟨u, hA⟩ ⟨v, hB⟩
      have W' : Ctx.SubstEq Δ (σ.cons e.tm) (σ₂.cons e.tm) (A :: Γ) :=
        .cons W hA (hwf.2.2.2.1.1 e he).2.1
      exact ihB hΓA hAB W' (hbody e he)
  | sigma A B ihA ihB =>
    intro Γ σ σ₂ ρ m hΓ hAnn W H
    obtain ⟨⟨u, hA⟩, ⟨v, hB⟩, hAA, hAB⟩ := hAnn
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
    have hAσ : Δ ⊢ A.subst σ ≡ A.subst σ₂ : .sort u := IsDefEq.subst' hΔ W hA
    have hBσ : A.subst σ :: Δ ⊢ B.subst σ.lift ≡ B.subst σ₂.lift : .sort v :=
      IsDefEq.subst' (Γ₀ := A.subst σ :: Δ) ⟨hΔ, _, hAσ.hasType.1⟩
        (W.lift hA hAσ.hasType.1) hB
    cases H with
    | bot => exact .bot
    | sigma hAint hdty hwf hNV hbody hw hle _ _ =>
      have hdom := fun e he => (hNV e he).dom
      have hcan := fun e he => (hNV e he).val
      refine .sigma (ihA hΓ hAA W hAint) hdty
        ⟨⟨u, hAσ.hasType.2⟩, ⟨v, (hAσ.defeqDF_l hΔ hBσ).hasType.2⟩, hwf.2.2.1,
          hwf.2.2.2.1.retype ⟨u, hAσ⟩,
          hwf.2.2.2.2.1.conv ⟨u, hAσ.symm⟩,
          fun e he => (hwf.2.2.2.2.2 e he).conv
            ⟨v, (hAσ.hasType.2).instDF hΔ .sort (hAσ.defeqDF_l hΔ hBσ).symm
              (hAσ.defeqDF ((hwf.2.2.2.1.1 e he).2.1))⟩⟩
        (fun e he => .of_dom (hdom e he) (hcan e he)) (fun e he => ?_) hw
        (hle.trans hΔ (TShape.LE.T.2
          ⟨⟨⟨u, hAσ⟩, v, hBσ⟩, .refl hwf.2.2.1, .refl hwf.2.2.2.1,
            hwf.2.2.2.2.1, hwf.2.2.2.2.2⟩))
        ⟨u, hA⟩ ⟨v, hB⟩
      have W' : Ctx.SubstEq Δ (σ.cons e.tm) (σ₂.cons e.tm) (A :: Γ) :=
        .cons W hA (hwf.2.2.2.1.1 e he).2.1
      exact ihB hΓA hAB W' (hbody e he)
  | pair A B a b ihA ihB iha ihb =>
    intro Γ σ σ₂ ρ m hΓ hAnn W H
    obtain ⟨⟨u, hA⟩, ⟨v, hB⟩, hat, hAA, hAB, hAa, hAb⟩ := hAnn
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
    have hAσ : TyEq Δ (A.subst σ) (A.subst σ₂) := ⟨u, IsDefEq.subst' hΔ W hA⟩
    have haσ : Δ ⊢ a.subst σ ≡ a.subst σ₂ : A.subst σ := IsDefEq.subst' hΔ W hat
    cases H with
    | bot => exact .bot
    | @pair _ _ _ _ _ _ _ _ _ _ _ _ _ hainp hbout hAint hdty hNV hdc hwf hcode hcty hw hle 
        _ _ =>
      have hdx := hNV.dom
      have hxc := hNV.val
      have hwf' := show Shape.WF (n := _+1) Δ (ShapeS.pair (A.subst σ₂) (a.subst σ₂) _ _) from
        ⟨hwf.1, hAσ.choose_spec.defeqDF (haσ.symm.trans haσ), TyEq.refl_r hAσ,
          hwf.2.2.2.1, hwf.2.2.2.2⟩
      have hle'₀ := show Shape.LE (n := _+1) Δ (ShapeS.pair (A.subst σ) (a.subst σ) _ _)
          (ShapeS.pair (A.subst σ₂) (a.subst σ₂) _ _) from
        ⟨Shape.LE.refl hwf.2.2.2.1, Shape.LE.refl hwf.2.2.2.2, hwf.1, hAσ, haσ⟩
      have hle' := TShape.LE.T.2 hle'₀
      have W' : Ctx.SubstEq Δ (σ.cons (a.subst σ)) (σ₂.cons (a.subst σ₂)) (A :: Γ) :=
        .cons W hA haσ
      exact .pair (iha hΓ hAa W hainp) (ihb hΓ hAb W hbout)
        (ihA hΓ hAA W hAint) hdty ((TShape.Named.of_dom hdx hxc).defeq hΔ hdc haσ)
        (TShape.CodeCanonS.conv hdc (TyEq.symm hAσ)) hwf' (ihB hΓA hAB W' hcode) hcty hw
        (hle.trans hΔ hle') ⟨u, hA⟩ hat
  | fst p ih =>
    intro Γ σ σ₂ ρ m hΓ hAnn W H
    cases H with
    | bot => exact .bot
    | fst hp hw hle => exact .fst (ih hΓ hAnn W hp) hw hle
  | snd p ih =>
    intro Γ σ σ₂ ρ m hΓ hAnn W H
    obtain ⟨hft, hAp⟩ := hAnn
    cases H with
    | bot => exact .bot
    | snd hp hlab hw hle hty =>
      have heq := hty.move hΔ W
      exact .snd (ih hΓ hAp W hp) (hlab.trans heq) hw hle (hty.stage W)
  | natCase C M a b ihC ihM iha ihb =>
    intro Γ σ σ₂ ρ m hΓ hAnn W H
    obtain ⟨hMt, hAC, hAM, hAa, hAb⟩ := hAnn
    have hΓN : ⊢ (Term.nat :: Γ) := ⟨hΓ, _, .nat⟩
    have hMσ : Δ ⊢ M.subst σ ≡ M.subst σ₂ : Term.nat := IsDefEq.subst' hΔ W hMt
    cases H with
    | bot => exact .bot
    | natCase_zero hM hz ha _ =>
      exact .natCase_zero (ihM hΓ hAM W hM) (hMσ.symm.trans hz) (iha hΓ hAa W ha) hMt
    | natCase_succ hM hwv heq hbody _ =>
      refine .natCase_succ (ihM hΓ hAM W hM) hwv (hMσ.symm.trans heq) ?_ hMt
      have W' : Ctx.SubstEq Δ (σ.cons _) (σ₂.cons _) (Term.nat :: Γ) :=
        .cons W .nat (heq.succ_regular (.inr rfl))
      exact ihb hΓN hAb W' hbody
  | Y A b ihA ihb =>
    intro Γ σ σ₂ ρ m hΓ hAnn W H
    -- the tower is not structural in the term, so this one case runs on
    -- the derivation: each level's self-premise is the level below
    have key : ∀ {Γ₂ : List Term} {t' σ' ρ' m}, Interp Δ Γ₂ t' σ' ρ' m →
        ∀ {σ₃}, t' = Term.Y A b → ⊢ Γ₂ → (Term.Y A b).Annot Γ₂ →
          Ctx.SubstEq Δ σ' σ₃ Γ₂ → Interp Δ Γ₂ (Term.Y A b) σ₃ ρ' m := by
      intro Γ₂ t' σ' ρ' m H
      induction H with
      | @Y Γ₂ σ' ρ' m A₂ b₂ x d hx hwx hAd hdty hNV hdc hbody _ _ ihx _ _ =>
        have hDom := hNV.dom
        have hxc := hNV.val
        intro σ₃ ht' hΓ₂ hAnn₂ W₂
        cases ht'
        obtain ⟨⟨u, hA⟩, hYt, hAA, hAb⟩ := hAnn₂
        have hYσ : Δ ⊢ (Term.Y A b).subst σ' ≡ (Term.Y A b).subst σ₃ : A.subst σ' :=
          IsDefEq.subst' hΔ W₂ hYt
        have W' : Ctx.SubstEq Δ (σ'.cons ((Term.Y A b).subst σ'))
            (σ₃.cons ((Term.Y A b).subst σ₃)) (A :: Γ₂) := .cons W₂ hA hYσ
        exact .Y (ihx rfl hΓ₂ ⟨⟨u, hA⟩, hYt, hAA, hAb⟩ W₂) hwx (ihA hΓ₂ hAA W₂ hAd) hdty ((TShape.Named.of_dom hDom hxc).defeq hΔ hdc hYσ)
          (TShape.CodeCanonS.conv hdc (TyEq.symm ⟨u, IsDefEq.subst' hΔ W₂ hA⟩))
          (ihb ⟨hΓ₂, _, hA⟩ hAb W' hbody) ⟨u, hA⟩ hYt
      | bot => intro σ₃ _ _ _ _; exact .bot
      | _ => intro σ₃ ht' _ _ _; simp at ht'
    exact key H rfl hΓ hAnn W
  | id r A a b ihA iha ihb =>
    intro Γ σ σ₂ ρ m hΓ hAnn W H
    obtain ⟨⟨u, hA⟩, hat, hbt, hAA, hAa, hAb⟩ := hAnn
    cases H with
    | bot => exact .bot
    | id hw hle _ _ _ =>
      refine .id hw (hle.trans hΔ (TShape.LE.T.2
        ⟨rfl, ⟨u, IsDefEq.subst' hΔ W hA⟩, IsDefEq.subst' hΔ W hat,
          IsDefEq.subst' hΔ W hbt⟩)) ⟨u, hA⟩ hat hbt
  | refl r a ih =>
    intro Γ σ σ₂ ρ m hΓ hAnn W H
    cases H with
    | bot => exact .bot
    | refl hw hle => exact .refl hw hle
  | tr r A a b C X Hp ihA iha ihb ihC ihX ihH =>
    intro Γ σ σ₂ ρ m hΓ hAnn W H
    obtain ⟨⟨u, hA⟩, hat, hbt, hht, ⟨a₀, C₀, v₀, hx₀, ha₀, hC₀⟩, hAA, hAa, hAb, hAC, hAX, hAH⟩ :=
      hAnn
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
    have hbσ : Δ ⊢ b.subst σ ≡ b.subst σ₂ : A.subst σ := IsDefEq.subst' hΔ W hbt
    have haσ : Δ ⊢ a.subst σ ≡ a.subst σ₂ : A.subst σ := IsDefEq.subst' hΔ W hat
    have WC : Ctx.SubstEq Δ (σ.cons (b.subst σ)) (σ₂.cons (b.subst σ₂)) (A :: Γ) :=
      .cons W hA hbσ
    cases H with
    | bot => exact .bot
    | tr hw hle hX ha hb hAint hwv hNV hvc hC hcb hNV2 hcbc hH heq _ _ _ =>
      have hvA := hNV.dom
      have hbc := hNV.val
      have hm' := hNV2.dom
      have hmc := hNV2.val
      have hAσ : Δ ⊢ A.subst σ ≡ A.subst σ₂ : .sort u := IsDefEq.subst' hΔ W hA
      refine .tr hw hle (ihX hΓ hAX W hX) (iha hΓ hAa W ha) (ihb hΓ hAb W hb)
        (ihA hΓ hAA W hAint) hwv ((TShape.Named.of_dom hvA hbc).defeq hΔ hvc hbσ)
        (TShape.CodeCanonS.conv hvc (TyEq.symm ⟨u, hAσ⟩)) (ihC hΓA hAC WC hC) hcb
        ((TShape.Named.of_dom hm' hmc).defeq hΔ
          (hcbc.conv (TyEq.tr_motive hΔ W.left hA ha₀ hC₀ heq)) (IsDefEq.subst' hΔ W hx₀))
        (TShape.CodeCanonS.conv hcbc ⟨v₀, (IsDefEq.subst' hΔ WC hC₀.hasType.2).symm⟩)
        (fun hr => ?_) ?_ ⟨u, hA⟩ hat hbt
      · -- the proof's equation moves with the stage, retyped at the new one
        have hHσ := IsDefEq.subst' hΔ W hht
        have hId : Δ ⊢ Term.id true (A.subst σ) (a.subst σ) (b.subst σ) ≡
            Term.id true (A.subst σ₂) (a.subst σ₂) (b.subst σ₂) : .sort true :=
          IsDefEq.idDF hAσ haσ hbσ
        have hrefl : Δ ⊢ Term.refl true (a.subst σ) ≡ Term.refl true (a.subst σ₂) :
            Term.id true (A.subst σ) (a.subst σ) (b.subst σ) := by
          have hA1 := hAσ.hasType.1; have ha1 := haσ.hasType.1
          exact (IsDefEq.idDF hA1 ha1 heq).defeqDF
            (IsDefEq.reflDF hA1 haσ (IsDefEq.idDF (r := true) hA1 ha1 ha1))
        cases hr
        exact hId.defeqDF ((hHσ.symm.trans (hH rfl)).trans hrefl)
      have h1 : Δ ⊢ a.subst σ₂ ≡ b.subst σ₂ : A.subst σ :=
        (haσ.symm.trans heq).trans hbσ
      exact ((IsDefEq.subst' hΔ W hA)).defeqDF h1

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

theorem Interp.tr_bot_of_ne {Δ Γ : List Term} {r : Bool} {A a b C X H : Term} {σ ρ m}
    (h : Interp Δ Γ (.tr r A a b C X H) σ ρ m)
    (hne : ¬ (Δ ⊢ a.subst σ ≡ b.subst σ : A.subst σ)) : m.2 = Shape.bot := by
  cases h with
  | bot => rfl
  | tr _ _ _ _ _ _ _ _ _ _ _ _ _ _ heq => exact absurd heq hne

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
  ∀ i, (θ i).Annot Γ'

theorem Subst.Good.lift {Γ' : List Term} {θ : Subst} {A : Term} (h : Subst.Good Γ' θ) :
    Subst.Good (A :: Γ') θ.lift := by
  intro i
  cases i with
  | zero => exact trivial
  | succ i =>
    have := (h i).weak' (Ctx.Lift'.skip (A := A) .refl)
    exact this

theorem Subst.Good.one {Γ' : List Term} {a : Term} (ha : a.Annot Γ') :
    Subst.Good Γ' (Subst.one a) := by
  intro i
  cases i with
  | zero => exact ha
  | succ i => exact trivial

/-- Strengthening at one slot, which is all the merges need: the slot is
well-annotated, so `Interp.unweak` applies at `.skip .refl`. -/
theorem Interp.unweak_slot {Δ Γ' Γ'' : List Term} {s : Term} (hΔ : ⊢ Δ) (hΓ' : ⊢ Γ')
    (WΓ : Ctx.Lift' (.skip .refl) Γ' Γ'') (hs : s.Annot Γ')
    {σ e ρ x m} (hd : Ctx.SubstEq Δ (σ.cons e) (σ.cons e) Γ'')
    (H : Interp Δ Γ'' s.lift (σ.cons e) (ρ.push x) m) :
    Interp Δ Γ' s σ ρ m :=
  Interp.unweak hΔ hΓ' hs WΓ hd (fun _ => rfl) H

/-- Directedness at a good slot, weakened. -/
theorem Interp.Dir.weak_slot {Δ Γ' Γ'' : List Term} {s : Term} (hΔ : ⊢ Δ) (hΓ' : ⊢ Γ')
    (WΓ : Ctx.Lift' (.skip .refl) Γ' Γ'') (hs : s.Annot Γ')
    {σ e ρ x} (hd : Ctx.SubstEq Δ (σ.cons e) (σ.cons e) Γ'')
    (h : Interp.Dir Δ Γ' s σ ρ) :
    Interp.Dir Δ Γ'' s.lift (σ.cons e) (ρ.push x) := by
  intro m₁ m₂ h₁ h₂
  have hiff : ∀ {m}, Interp Δ Γ'' s.lift (σ.cons e) (ρ.push x) m ↔ Interp Δ Γ' s σ ρ m :=
    fun {_} => ⟨Interp.unweak_slot hΔ hΓ' WΓ hs hd, fun H => H.weak' hΓ' WΓ (fun _ => rfl)⟩
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
    (hdcons : ∀ e ∈ l, Ctx.SubstEq Δ (σ.cons (tm e)) (σ.cons (tm e)) Γ'')
    (hwf : ∀ e ∈ l, TShape.WF Δ (inp e))
    (ih : ∀ {e : α}, e ∈ l → ∀ {m₂},
      Interp Δ Γ'' (b.subst θ.lift) (σ.cons (tm e)) (ρ.push (inp e)) m₂ →
      ∃ ρ', Interp Δ Γ b (θ.lift.comp (σ.cons (tm e))) ρ' m₂ ∧
        Valuation.Approx Δ Γ'' θ.lift (σ.cons (tm e)) (ρ.push (inp e)) ρ')
    (hbody : ∀ e ∈ l, Interp Δ Γ'' (b.subst θ.lift) (σ.cons (tm e)) (ρ.push (inp e)) (out e)) :
    ∃ ρ', Valuation.Approx Δ Γ' θ σ ρ ρ' ∧
      ∀ e ∈ l, Interp Δ Γ b ((θ.comp σ).cons (tm e)) (ρ'.push (inp e)) (out e) := by
  -- the lifted substitution is directed at the extended stage
  have hθ' : ∀ (e : α), e ∈ l → ∀ i,
      Interp.Dir Δ Γ'' (θ.lift i) (σ.cons (tm e)) (ρ.push (inp e)) := by
    intro e he i
    cases i with
    | zero => exact Interp.Dir.bvar (ρ := ρ.push (inp e)) (i := 0) (hwf e he)
    | succ i => exact Interp.Dir.weak_slot hΔ hΓ' WΓ (hgood i) (hdcons e he) (hθ i)
  -- one valuation per element, by the induction hypothesis
  obtain ⟨ps, hps, hall⟩ := List.exists_pairs (β := Valuation)
    (P := fun e ρ'' => Interp Δ Γ b ((θ.lift).comp (σ.cons (tm e))) ρ'' (out e) ∧
      Valuation.Approx Δ Γ'' θ.lift (σ.cons (tm e)) (ρ.push (inp e)) ρ'')
    (fun e he => ih he (hbody e he))
  -- their tails approximate `θ` at the outer stage, and fold to one
  have htail : ∀ ρ'' ∈ ps.map (fun p => Valuation.tail p.2),
      Valuation.Approx Δ Γ' θ σ ρ ρ'' := by
    intro ρ'' hρ''
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hρ''
    exact fun i =>
      Interp.unweak_slot hΔ hΓ' WΓ (hgood i) (hdcons p.1 (hps ▸ List.mem_map.2 ⟨p, hp, rfl⟩))
        ((hall p hp).2 (i+1))
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

def Adm (Δ : List Term) (_Γ₀ Γ : List Term) (σ : Subst) (ρ : Valuation) : Prop :=
  Valuation.WF Δ ρ ∧
    ∀ {i A}, Lookup Γ i A → ∃ a, Interp Δ Γ A σ ρ a ∧ TShape.Slot Δ (A.subst σ) a (σ i) (ρ i)

/-- The all-bottom valuation is admissible, for free.  This is the
hypothesis every inversion theorem is run under; with the base context
now vestigial it holds at any. -/
theorem Adm.bot {Δ Γ : List Term} {σ : Subst} : Adm Δ Γ Γ σ Valuation.nil :=
  ⟨fun _ => trivial, fun _ => ⟨TShape.bot, .bot, TShape.Named.bot, Shape.CodeCanonS.bot⟩⟩

/-- Admissible valuations are well formed, slotwise. -/
theorem Adm.wf {Δ Γ₀ Γ : List Term} {σ ρ} (h : Adm Δ Γ₀ Γ σ ρ) : Valuation.WF Δ ρ := h.1

/-- The slot a variable reads is typed at an approximant of its type:
what `SoundTy`'s `bvar` case needs, and now the definition. -/
theorem Adm.lookup {Δ Γ₀ Γ : List Term} {σ ρ} (h : Adm Δ Γ₀ Γ σ ρ) (_hΓ : ⊢ Γ) :
    ∀ {i A}, Lookup Γ i A → ∃ a, Interp Δ Γ A σ ρ a ∧ TShape.HasType Δ (ρ i) a :=
  fun hl => (h.2 hl).imp fun _ ⟨hI, hD, _⟩ => ⟨hI, hD.hasType⟩

theorem Adm.lookupCanon {Δ Γ₀ Γ : List Term} {σ ρ} (h : Adm Δ Γ₀ Γ σ ρ) :
    ∀ {i A}, Lookup Γ i A →
      ∃ a, Interp Δ Γ A σ ρ a ∧ TShape.Slot Δ (A.subst σ) a (σ i) (ρ i) := h.2

/-- Weakening the stage by one slot: `A` at `σ.tail` under `ρ` is
`A.lift` at `σ` under `ρ.push x`.  `Interp.weak'` at `Lift.refl.skip`. -/
theorem Interp.weak_one {Δ Γ Γ' : List Term} {A : Term} {σ ρ x m} (hΓ : ⊢ Γ)
    (WΓ : Ctx.Lift' Lift.refl.skip Γ Γ')
    (H : Interp Δ Γ A σ.tail ρ m) : Interp Δ Γ' A.lift σ (ρ.push x) m :=
  Interp.weak' (l := Lift.refl.skip) hΓ (Subst.tail_eq_lift_l ▸ H) WΓ (fun _ => rfl)

/-- Extending an admissible valuation by a typed slot: the old `cons`
constructor, now a lemma.  It asks for `⊢ Γ`, since the slots below are
re-read one binder up (`Interp.weak_one`).  It does *not* ask that the
type's approximants be types: `Adm` has no clause that would read it. -/
theorem Adm.cons {Δ Γ₀ Γ : List Term} {A : Term} {σ ρ x a} (h : Adm Δ Γ₀ Γ σ.tail ρ)
    (hΓ : ⊢ Γ) (ha : Interp Δ Γ A σ.tail ρ a) (hx : TShape.WF Δ x)
    (hxa : TShape.Named Δ a (σ 0) x) (hac : TShape.CodeCanonS Δ (A.subst σ.tail) a) :
    Adm Δ Γ₀ (A :: Γ) σ (ρ.push x) := by
  refine ⟨Valuation.WF.push h.wf hx, ?_⟩
  intro i A' hl
  cases hl with
  | zero =>
    exact ⟨a, Interp.weak_one hΓ (.skip .refl) ha, hxa, by rwa [lift_subst]⟩
  | succ hl =>
    obtain ⟨b, hb, hn, hbc⟩ := h.2 hl
    exact ⟨b, Interp.weak_one hΓ (.skip .refl) hb, hn, by rwa [lift_subst]⟩

/-! ## What the substitution lemma needs that the term does not say

`Interp.to_substTerm` takes an interpretation of `t[θ]` in `Γ'` apart and
rebuilds it for `t` in `Γ`.  Most of each clause's premises come back from
`Term.Annot`; two do not, and both are *semantic*:

* at a binder, rebuilding the extended stage's admissibility needs every
  approximant of the annotation to be a type (`IsTypeAt`);
* at an `app` or `snd`, the clause's label link has to be recognised in
  the smaller context, and what does that is the function's — resp. the
  pair's — own typing (`PinApp`, `PinSnd`).

These are `HasFixedness` in the original, where `HasSubstitution.app`
takes it as a hypothesis and `outputAtom_rawPi_fixed_support` turns it
into exactly this: a non-`⊥` response sits at a genuine point of the
domain.  They are stated here without `SoundTy`, so that `Interp.lean`
stays below it, and discharged in `Presheaf.lean` as a third conclusion of
`IsDefEq.sound` (§3.1d of the strategy note). -/

/-- **Every valuation approximating `θ` is below an admissible one that
still approximates it.**  `Adm` is not upward closed — enlarging a
valuation breaks its slots' typings — so this does not come for free, and
it is what lets the conditions below be stated where they are *provable*:
at the `Γ` side, each an immediate consequence of the subterm's own
`SoundTy`.

`Valuation.Approx.canon_one` (`Presheaf.lean`) is this at a single
substitution, which is the only kind that arises, and `Saturates.lift`
carries it under a binder. -/
def Subst.Saturates (Δ Γ₀ Γ Γ' : List Term) (θ σ : Subst) (ρ : Valuation) : Prop :=
  ∀ {ρ'}, Valuation.Approx Δ Γ' θ σ ρ ρ' →
    ∃ ρ'', Valuation.LE Δ ρ' ρ'' ∧ Valuation.Approx Δ Γ' θ σ ρ ρ'' ∧
      Adm Δ Γ₀ Γ (θ.comp σ) ρ''

/-- Every approximant of `A` at an admissible stage is a type:
`SoundTy Γ A (.sort u)`'s `isType` half, spelled without `SoundTy` so
that `Interp.lean` stays below it. -/
def IsTypeAt (Γ : List Term) (A : Term) : Prop :=
  ∀ {Δ Γ₀ : List Term} {σ ρ}, ⊢ Δ → Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ₀ Γ σ ρ →
    ∀ {c}, Interp Δ Γ A σ ρ c →
      TShape.HasType Δ c TShape.type ∧ TShape.CodeCanonS Δ (A.subst σ) c

/-- Every approximant of `t` at an admissible stage is typed at an
approximant of `A`: `SoundTy Γ t A`'s `approx` half.  Needed at the two
binders whose slot is not an entry input — `natCase`'s and `Y`'s. -/
def TypedAt (Γ : List Term) (t A : Term) : Prop :=
  ∀ {Δ Γ₀ : List Term} {σ ρ}, ⊢ Δ → Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ₀ Γ σ ρ →
    ∀ {m}, Interp Δ Γ t σ ρ m → ∃ a, Interp Δ Γ A σ ρ a ∧ TShape.HasType Δ m a

/-- A λ-shape approximating `F` has its label definitionally equal to the
argument's type at the stage.  In the original this is the function's
Π-fixedness and `outputAtom_rawPi_fixed_support`; here it is
`Interp.lam_label_ty` on `SoundTy F (Π A B)`. -/
def PinApp (Γ : List Term) (F a : Term) : Prop :=
  ∀ {Δ Γ₀ : List Term} {σ ρ} {n} {A : Term} {g : ShapeFun n}, ⊢ Δ →
    Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ₀ Γ σ ρ →
    Interp Δ Γ F σ ρ (Shape.T (n := n+1) (ShapeS.lam A g)) → Stable Δ Γ σ a A

/-- The Σ twin, for `snd`: a pair shape approximating `p` has its label
definitionally equal to the type of `fst p` at the stage. -/
def PinSnd (Γ : List Term) (p : Term) : Prop :=
  ∀ {Δ Γ₀ : List Term} {σ ρ} {n} {A a₀ : Term} {x y : Shape n}, ⊢ Δ →
    Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ₀ Γ σ ρ →
    Interp Δ Γ p σ ρ (Shape.T (n := n+1) (ShapeS.pair A a₀ x y)) →
    Stable Δ Γ σ (Term.fst p) A

/-- The two gathered over the whole term, structurally — the semantic
counterpart of `Term.Annot`. -/
def Term.Pinned : Term → List Term → Prop
  | .bvar _, _ => True
  | .sort _, _ => True
  | .unit _, _ => True
  | .star _, _ => True
  | .nat, _ => True
  | .zero, _ => True
  | .app F a, Γ => PinApp Γ F a ∧ F.Pinned Γ ∧ a.Pinned Γ
  | .lam A b, Γ => IsTypeAt Γ A ∧ A.Pinned Γ ∧ b.Pinned (A :: Γ)
  | .forallE A B, Γ => IsTypeAt Γ A ∧ A.Pinned Γ ∧ B.Pinned (A :: Γ)
  | .sigma A B, Γ => IsTypeAt Γ A ∧ A.Pinned Γ ∧ B.Pinned (A :: Γ)
  | .pair A B a b, Γ =>
    IsTypeAt Γ A ∧ A.Pinned Γ ∧ B.Pinned (A :: Γ) ∧ a.Pinned Γ ∧ b.Pinned Γ
  | .fst p, Γ => p.Pinned Γ
  | .snd p, Γ => PinSnd Γ p ∧ p.Pinned Γ
  | .succ n, Γ => n.Pinned Γ
  | .natCase C M a b, Γ =>
    TypedAt Γ M .nat ∧ C.Pinned (.nat :: Γ) ∧ M.Pinned Γ ∧ a.Pinned Γ ∧ b.Pinned (.nat :: Γ)
  | .Y A b, Γ =>
    IsTypeAt Γ A ∧ TypedAt Γ (.Y A b) A ∧ A.Pinned Γ ∧ b.Pinned (A :: Γ)
  | .id _ A a b, Γ => A.Pinned Γ ∧ a.Pinned Γ ∧ b.Pinned Γ
  | .refl _ a, Γ => a.Pinned Γ
  | .tr _ A a b C x h, Γ =>
    IsTypeAt Γ A ∧ A.Pinned Γ ∧ a.Pinned Γ ∧ b.Pinned Γ ∧ C.Pinned (A :: Γ) ∧
      x.Pinned Γ ∧ h.Pinned Γ

/-- `nat` is a type at every stage, so its binders cost nothing. -/
theorem IsTypeAt.nat {Γ : List Term} : IsTypeAt Γ Term.nat := by
  intro _ _ _ _ hΔ _ _ _ hb
  refine ⟨TShape.HasType.mono_l hΔ .nat (Interp.le_nat hb), ?_⟩
  exact TShape.CodeCanonS.mono hΔ (Interp.le_nat hb) (x := TShape.nat)
    (show TyEq _ _ _ from TyEq.refl .nat)

/-- `zero` is a numeral at every stage. -/
theorem TypedAt.zero {Γ : List Term} : TypedAt Γ Term.zero Term.nat := by
  intro _ _ _ _ hΔ _ _ _ hm
  exact ⟨TShape.nat, Interp.nat',
    TShape.HasType.mono_l hΔ (TShape.HasType.zero) (Interp.le_zero hm)⟩

/-- The successor of the slot a `natCase` branch binds: the slot is a
numeral because the stage is admissible, so the successor is one too.
This is the lifted motive's argument at `natCase`. -/
theorem TypedAt.succ_bvar0 {Γ : List Term} :
    TypedAt (Term.nat :: Γ) (Term.succ (.bvar 0)) Term.nat := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  refine ⟨TShape.nat, Interp.nat', ?_⟩
  cases hm with
  | bot => exact .bot .nat
  | succ hv hw hle =>
    obtain ⟨c, hc, hct, _⟩ := hAdm.2 (i := 0) .zero
    have h0 : Shape.IsNumeral (ρ 0).2 :=
      TShape.HasType.isNumeral hΔ (Interp.le_nat hc) hct.hasType
    have hvty := TShape.HasType.mono_l hΔ h0.hasType (Interp.le_bvar hv)
    exact TShape.HasType.mono_l hΔ
      (TShape.HasType.succ (TShape.HasType.isNumeral hΔ
        (TShape.LE.refl (a := TShape.nat) trivial) hvty)) hle

/-- **Saturation carries under a binder.**  The binder's own slot `y` is
kept, and the tail is saturated by the hypothesis — so the valuation
never grows except where the substitution's own argument lives, which is
why this closes instead of cascading.

`hd` is what the binder costs: *somewhere* among the valuations
approximating `θ`, the annotation has an approximant typing `y`.  At a
graph entry that is the clause's own `hdom` transported; at `natCase` and
`Y` it is the scrutinee's — resp. the tower's — `TypedAt`. -/
theorem Subst.Saturates.lift {Δ Γ₀ Γ Γ' : List Term} {A : Term} {θ σ ρ : _} {e y}
    (hΔ : ⊢ Δ) (hΓ : ⊢ Γ) (hΓ' : ⊢ Γ') (hgood : Subst.Good Γ' θ)
    (Wθ : Ctx.SubstEq Γ' θ θ Γ) (Wσ : Ctx.SubstEq Δ σ σ Γ')
    (hθ : ∀ i, Interp.Dir Δ Γ' (θ i) σ ρ)
    (hcons : Ctx.SubstEq Δ (σ.cons e) (σ.cons e) (A.subst θ :: Γ'))
    (hwy : TShape.WF Δ y) (hye : TShape.ValCanon Δ e y) (hAty : IsTypeAt Γ A)
    (hd : ∃ ρ_d d, Valuation.Approx Δ Γ' θ σ ρ ρ_d ∧
      Interp Δ Γ A (θ.comp σ) ρ_d d ∧ TShape.Dom Δ d y)
    (hSat : Subst.Saturates Δ Γ₀ Γ Γ' θ σ ρ) :
    Subst.Saturates Δ Γ₀ (A :: Γ) (A.subst θ :: Γ') θ.lift (σ.cons e) (ρ.push y) := by
  intro ρ' hρ'
  obtain ⟨ρ_d, d, hApd, hdI, hyd⟩ := hd
  -- the tail approximates `θ` one context down
  have htail : Valuation.Approx Δ Γ' θ σ ρ (Valuation.tail ρ') := by
    intro i
    exact Interp.unweak_slot hΔ hΓ' (.skip .refl) (hgood i) hcons (hρ' (i + 1))
  -- saturate the tail together with the annotation's witness
  obtain ⟨hApj, hlj₁, hlj₂⟩ := Valuation.Approx.join hΔ hθ htail hApd
  obtain ⟨ρ'', hle, hAp, hAdm⟩ := hSat hApj
  refine ⟨ρ''.push y, fun i => ?_, fun i => ?_, ?_⟩
  · cases i with
    | zero => exact Interp.le_bvar (i := 0) (ρ := ρ.push y) (hρ' 0)
    | succ i => exact TShape.LE.trans hΔ (hlj₁ i) (hle i)
  · cases i with
    | zero => exact .bvar hwy (TShape.LE.refl hwy)
    | succ i =>
      have hAi : Interp Δ Γ' (θ i) (Subst.lift_l Lift.refl.skip (σ.cons e)) ρ (ρ'' i) :=
        hAp i
      have := Interp.weak' (Γ' := A.subst θ :: Γ') (ρ' := ρ.push y) hΓ' hAi
        (.skip .refl) (fun _ => rfl)
      simpa using this
  · -- and the extended valuation is admissible, by `Adm.cons`
    have hdI' : Interp Δ Γ A (θ.comp σ) ρ'' d :=
      Interp.mono_val hΔ (fun i => TShape.LE.trans hΔ (hlj₂ i) (hle i)) hdI
    have hstage : (θ.lift).comp (σ.cons e) = (θ.comp σ).cons e := by
      funext i; cases i with
      | zero => rfl
      | succ i => exact lift_subst_cons
    rw [hstage]
    exact Adm.cons hAdm hΓ hdI' hwy (.of_dom hyd hye)
      (hAty hΔ (Ctx.SubstEq.comp hΔ Wσ Wθ) hAdm hdI').2

/-! ### Weakening the clause conditions

These restrict along a context lift, and what restricts with them is the
*stage*: `Ctx.SubstEq.lift_l` for the substitution and `Adm.unlift` for
the valuation.  Only `natCase` needs them, for the motive it reads one
context deeper. -/

/-- Admissibility restricts along a context lift.  A variable of the
smaller context is one of the bigger (`Lookup.weak'`) and its type is the
same term lifted, so `Interp.unweak` moves that type's approximant down —
which is exactly the data `Adm` keeps. -/
theorem Adm.unlift {Δ Γ₀ Γ Γ' : List Term} {l σ ρ} (hΔ : ⊢ Δ) (hΓ : ⊢ Γ)
    (WΓ : Ctx.Lift' l Γ Γ') (W : Ctx.SubstEq Δ σ σ Γ') (h : Adm Δ Γ₀ Γ' σ ρ) :
    Adm Δ Γ₀ Γ (σ.lift_l l) (fun i => ρ (Lift.liftVar l i)) := by
  refine ⟨fun i => h.wf _, fun {i A} hlk => ?_⟩
  obtain ⟨a, ha, hn, hac⟩ := h.2 (hlk.weak' WΓ)
  exact ⟨a, Interp.unweak hΔ hΓ (Ctx.WF.lookup hΓ hlk).choose_spec.annot.1 WΓ W
    (fun _ => rfl) ha, hn, by rwa [subst_lift'] at hac⟩

theorem IsTypeAt.weak' {Γ Γ' : List Term} {l : Lift} {A : Term} (hΓ : ⊢ Γ)
    (hA : A.Annot Γ) (WΓ : Ctx.Lift' l Γ Γ') (h : IsTypeAt Γ A) :
    IsTypeAt Γ' (A.lift' l) := by
  intro Δ Γ₀ σ ρ hΔ W hAdm c hc
  have := h hΔ (Ctx.SubstEq.lift_l WΓ hΓ W) (Adm.unlift hΔ hΓ WΓ W hAdm)
    (Interp.unweak hΔ hΓ hA WΓ W (fun _ => rfl) hc)
  rwa [← subst_lift'] at this

theorem TypedAt.weak' {Γ Γ' : List Term} {l : Lift} {t A : Term} (hΓ : ⊢ Γ)
    (ht : t.Annot Γ) (WΓ : Ctx.Lift' l Γ Γ') (h : TypedAt Γ t A) :
    TypedAt Γ' (t.lift' l) (A.lift' l) := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m hm
  obtain ⟨a, ha, hty⟩ := h hΔ (Ctx.SubstEq.lift_l WΓ hΓ W) (Adm.unlift hΔ hΓ WΓ W hAdm)
    (Interp.unweak hΔ hΓ ht WΓ W (fun _ => rfl) hm)
  exact ⟨a, Interp.weak' hΓ ha WΓ (fun _ => rfl), hty⟩

theorem PinApp.weak' {Γ Γ' : List Term} {l : Lift} {F a : Term} (hΓ : ⊢ Γ)
    (hF : F.Annot Γ) (WΓ : Ctx.Lift' l Γ Γ') (h : PinApp Γ F a) :
    PinApp Γ' (F.lift' l) (a.lift' l) := by
  intro Δ Γ₀ σ ρ n A g hΔ W hAdm hf
  exact Stable.weak' hΓ WΓ
    (h hΔ (Ctx.SubstEq.lift_l WΓ hΓ W) (Adm.unlift hΔ hΓ WΓ W hAdm)
      (Interp.unweak hΔ hΓ hF WΓ W (fun _ => rfl) hf))

theorem PinSnd.weak' {Γ Γ' : List Term} {l : Lift} {p : Term} (hΓ : ⊢ Γ)
    (hp : p.Annot Γ) (WΓ : Ctx.Lift' l Γ Γ') (h : PinSnd Γ p) :
    PinSnd Γ' (p.lift' l) := by
  intro Δ Γ₀ σ ρ n A a₀ x y hΔ W hAdm hf
  exact Stable.weak' (a := Term.fst p) hΓ WΓ
    (h hΔ (Ctx.SubstEq.lift_l WΓ hΓ W) (Adm.unlift hΔ hΓ WΓ W hAdm)
      (Interp.unweak hΔ hΓ hp WΓ W (fun _ => rfl) hf))

theorem Term.Pinned.weak' : ∀ {t : Term} {Γ Γ' : List Term} {l : Lift}, ⊢ Γ →
    t.Annot Γ → Ctx.Lift' l Γ Γ' → t.Pinned Γ → (t.lift' l).Pinned Γ' := by
  intro t
  induction t with
  | bvar | sort | unit | star | nat | zero => exact fun _ _ _ _ => trivial
  | succ _ ih => exact fun hΓ hA W h => ih hΓ hA W h
  | fst _ ih | refl _ _ ih => exact fun hΓ hA W h => ih hΓ hA W h
  | app _ _ ihF iha =>
    rintro Γ Γ' l hΓ ⟨_, hAF, hAa⟩ W ⟨hp, hF, ha⟩
    exact ⟨hp.weak' hΓ hAF W, ihF hΓ hAF W hF, iha hΓ hAa W ha⟩
  | snd _ ih =>
    rintro Γ Γ' l hΓ ⟨_, hAp⟩ W ⟨hp, hpp⟩
    exact ⟨hp.weak' hΓ hAp W, ih hΓ hAp W hpp⟩
  | lam A b ihA ihb =>
    rintro Γ Γ' l hΓ ⟨⟨u, hA⟩, hAA, hAb⟩ W ⟨hty, hPA, hPb⟩
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, u, hA⟩
    exact ⟨hty.weak' hΓ hAA W, ihA hΓ hAA W hPA, ihb hΓA hAb W.cons hPb⟩
  | forallE A B ihA ihB =>
    rintro Γ Γ' l hΓ ⟨⟨u, hA⟩, _, hAA, hAB⟩ W ⟨hty, hPA, hPB⟩
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, u, hA⟩
    exact ⟨hty.weak' hΓ hAA W, ihA hΓ hAA W hPA, ihB hΓA hAB W.cons hPB⟩
  | sigma A B ihA ihB =>
    rintro Γ Γ' l hΓ ⟨⟨u, hA⟩, _, hAA, hAB⟩ W ⟨hty, hPA, hPB⟩
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, u, hA⟩
    exact ⟨hty.weak' hΓ hAA W, ihA hΓ hAA W hPA, ihB hΓA hAB W.cons hPB⟩
  | pair A B a b ihA ihB iha ihb =>
    rintro Γ Γ' l hΓ ⟨⟨u, hA⟩, _, _, hAA, hAB, hAa, hAb⟩ W ⟨hty, hPA, hPB, hPa, hPb⟩
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, u, hA⟩
    exact ⟨hty.weak' hΓ hAA W, ihA hΓ hAA W hPA, ihB hΓA hAB W.cons hPB,
      iha hΓ hAa W hPa, ihb hΓ hAb W hPb⟩
  | natCase C M a b ihC ihM iha ihb =>
    rintro Γ Γ' l hΓ ⟨_, hAC, hAM, hAa, hAb⟩ W ⟨hM, hPC, hPM, hPa, hPb⟩
    have hΓN : ⊢ (Term.nat :: Γ) := ⟨hΓ, _, .nat⟩
    have WN : Ctx.Lift' l.cons (Term.nat :: Γ) (Term.nat :: Γ') := by
      simpa using W.cons (A := Term.nat)
    have hM' : TypedAt Γ' (M.lift' l) Term.nat := TypedAt.weak' hΓ hAM W hM
    exact ⟨hM', ihC hΓN hAC WN hPC, ihM hΓ hAM W hPM,
      iha hΓ hAa W hPa, ihb hΓN hAb WN hPb⟩
  | Y A b ihA ihb =>
    rintro Γ Γ' l hΓ ⟨⟨u, hA⟩, hYtm, hAA, hAb⟩ W ⟨hty, hYt, hPA, hPb⟩
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, u, hA⟩
    have hYt' : TypedAt Γ' (Term.Y (A.lift' l) (b.lift' l.cons)) (A.lift' l) :=
      TypedAt.weak' (t := Term.Y A b) hΓ ⟨⟨u, hA⟩, hYtm, hAA, hAb⟩ W hYt
    exact ⟨hty.weak' hΓ hAA W, hYt', ihA hΓ hAA W hPA, ihb hΓA hAb W.cons hPb⟩
  | id r A a b ihA iha ihb =>
    rintro Γ Γ' l hΓ ⟨_, _, _, hAA, hAa, hAb⟩ W ⟨hPA, hPa, hPb⟩
    exact ⟨ihA hΓ hAA W hPA, iha hΓ hAa W hPa, ihb hΓ hAb W hPb⟩
  | tr r A a b C X Hp ihA iha ihb ihC ihX ihH =>
    rintro Γ Γ' l hΓ ⟨⟨u, hA⟩, _, _, _, _, hAA, hAa, hAb, hAC, hAX, hAH⟩ W
      ⟨hty, hPA, hPa, hPb, hPC, hPX, hPH⟩
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, u, hA⟩
    exact ⟨hty.weak' hΓ hAA W, ihA hΓ hAA W hPA, iha hΓ hAa W hPa, ihb hΓ hAb W hPb,
      ihC hΓA hAC W.cons hPC, ihX hΓ hAX W hPX, ihH hΓ hAH W hPH⟩

/-- **Substitution in the term, the analytic direction.**  An approximant
of `t[θ]` is an approximant of `t` at the composed stage, under *some*
valuation whose slots approximate the `θ i`.

The clauses' `Γ`-level premises come back from `Term.Annot`, and their
semantic ones — a binder's annotation being a type, an eliminator's label
being the subject's own — from `Term.Pinned`, which is the original's
`HasFixedness` threaded structurally.  The `bvar` case is where the
valuation is built (slot `i` holds the approximant, every other slot
`⊥`), the merges are `Valuation.Approx.foldr` through
`body_merge`/`list_merge` under binders, and `Y` runs on the tower. -/
theorem Interp.to_substTerm {Δ : List Term} (hΔ : ⊢ Δ) :
    ∀ {t : Term} {Γ Γ₀ Γ' : List Term} {θ σ ρ m}, ⊢ Γ → t.Annot Γ → t.Pinned Γ → ⊢ Γ' →
      Subst.Good Γ' θ → Ctx.SubstEq Γ' θ θ Γ → Ctx.SubstEq Δ σ σ Γ' →
      Adm Δ Γ₀ Γ' σ ρ → Subst.Saturates Δ Γ₀ Γ Γ' θ σ ρ →
      (∀ i, Interp.Dir Δ Γ' (θ i) σ ρ) →
      Interp Δ Γ' (t.subst θ) σ ρ m →
      ∃ ρ', Interp Δ Γ t (θ.comp σ) ρ' m ∧ Valuation.Approx Δ Γ' θ σ ρ ρ' := by
  intro t
  induction t with
  | bvar i =>
    intro Γ Γ₀ Γ' θ σ ρ m _ _ _ _ _ _ _ _ _ _ H
    refine ⟨fun j => if j = i then m else TShape.bot, .bvar H.wf ?_, fun j => ?_⟩
    · simp only [if_pos]; exact TShape.LE.refl H.wf
    · by_cases hj : j = i
      · subst hj; simpa using H
      · simp only [if_neg hj]; exact .bot
  | sort u =>
    intro Γ Γ₀ Γ' θ σ ρ m _ _ _ _ _ _ _ _ _ _ H
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | sort hw hle => exact ⟨Valuation.nil, .sort hw hle, .nil⟩
  | unit r =>
    intro Γ Γ₀ Γ' θ σ ρ m _ _ _ _ _ _ _ _ _ _ H
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | unit hw hle => exact ⟨Valuation.nil, .unit hw hle, .nil⟩
  | star r =>
    intro Γ Γ₀ Γ' θ σ ρ m _ _ _ _ _ _ _ _ _ _ H
    cases H with | bot => exact ⟨Valuation.nil, .bot, .nil⟩
  | nat =>
    intro Γ Γ₀ Γ' θ σ ρ m _ _ _ _ _ _ _ _ _ _ H
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | nat hw hle => exact ⟨Valuation.nil, .nat hw hle, .nil⟩
  | zero =>
    intro Γ Γ₀ Γ' θ σ ρ m _ _ _ _ _ _ _ _ _ _ H
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | zero hw hle => exact ⟨Valuation.nil, .zero hw hle, .nil⟩
  | succ N ih =>
    intro Γ Γ₀ Γ' θ σ ρ m hΓ hAnn hPin hΓ' hgood Wθ Wσ hAdm hSat hθ H
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | succ hv hw hle =>
      obtain ⟨ρ', hv', hA⟩ := ih hΓ hAnn hPin hΓ' hgood Wθ Wσ hAdm hSat hθ hv
      exact ⟨ρ', .succ hv' hw hle, hA⟩
  | app F a ihF iha =>
    intro Γ Γ₀ Γ' θ σ ρ m hΓ hAnn hPin hΓ' hgood Wθ Wσ hAdm hSat hθ H
    obtain ⟨⟨T, hat⟩, hAF, hAa⟩ := hAnn
    obtain ⟨hpin, hPF, hPa⟩ := hPin
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | app hF hx hev hw hle hty =>
      obtain ⟨ρ₁, hF', hA₁⟩ := ihF hΓ hAF hPF hΓ' hgood Wθ Wσ hAdm hSat hθ hF
      obtain ⟨ρ₂, hx', hA₂⟩ := iha hΓ hAa hPa hΓ' hgood Wθ Wσ hAdm hSat hθ hx
      obtain ⟨hAj, hl₁, hl₂⟩ := Valuation.Approx.join hΔ hθ hA₁ hA₂
      obtain ⟨ρ₃, hle₃, hAp₃, hAdm₃⟩ := hSat hAj
      rw [subst_subst] at hev
      have hF₃ := Interp.mono_val hΔ (fun i => (hl₁ i).trans hΔ (hle₃ i)) hF'
      refine ⟨ρ₃, .app hF₃
        (Interp.mono_val hΔ (fun i => (hl₂ i).trans hΔ (hle₃ i)) hx') hev hw hle ?_, hAp₃⟩
      exact hpin hΔ (Ctx.SubstEq.comp hΔ Wσ Wθ) hAdm₃ hF₃
  | fst p ih =>
    intro Γ Γ₀ Γ' θ σ ρ m hΓ hAnn hPin hΓ' hgood Wθ Wσ hAdm hSat hθ H
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | fst hp hw hle =>
      obtain ⟨ρ', hp', hA⟩ := ih hΓ hAnn hPin hΓ' hgood Wθ Wσ hAdm hSat hθ hp
      exact ⟨ρ', .fst hp' hw hle, hA⟩
  | snd p ih =>
    intro Γ Γ₀ Γ' θ σ ρ m hΓ hAnn hPin hΓ' hgood Wθ Wσ hAdm hSat hθ H
    obtain ⟨⟨T, hft⟩, hAp⟩ := hAnn
    obtain ⟨hpin, hPp⟩ := hPin
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | snd hp hev hw hle hty =>
      obtain ⟨ρ', hp', hA⟩ := ih hΓ hAp hPp hΓ' hgood Wθ Wσ hAdm hSat hθ hp
      obtain ⟨ρ₃, hle₃, hAp₃, hAdm₃⟩ := hSat hA
      simp only [Term.subst, subst_subst] at hev
      have hp₃ := Interp.mono_val hΔ hle₃ hp'
      exact ⟨ρ₃, .snd hp₃ hev hw hle
        (hpin hΔ (Ctx.SubstEq.comp hΔ Wσ Wθ) hAdm₃ hp₃), hAp₃⟩
  | refl r a ih =>
    intro Γ Γ₀ Γ' θ σ ρ m hΓ hAnn hPin hΓ' hgood Wθ Wσ hAdm hSat hθ H
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | refl hw hle => exact ⟨Valuation.nil, .refl hw hle, .nil⟩
  | id r A a b ihA iha ihb =>
    intro Γ Γ₀ Γ' θ σ ρ m hΓ hAnn hPin hΓ' hgood Wθ Wσ hAdm hSat hθ H
    obtain ⟨⟨u, hA⟩, hat, hbt, hAA, hAa, hAb⟩ := hAnn
    obtain ⟨hPA, hPa, hPb⟩ := hPin
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | id hw hle _ _ _ =>
      simp only [subst_subst] at hle
      exact ⟨Valuation.nil, .id hw hle ⟨u, hA⟩ hat hbt, .nil⟩
  | lam A b ihA ihb =>
    intro Γ Γ₀ Γ' θ σ ρ m hΓ hAnn hPin hΓ' hgood Wθ Wσ hAdm hSat hθ H
    obtain ⟨⟨u, hA⟩, hAA, hAb⟩ := hAnn
    obtain ⟨hAty, hPA, hPb⟩ := hPin
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hA.subst hΓ' Wθ
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | @lam _ _ _ _ n g d _ _ hAint hdty hwf hNV hbody hw hle _ =>
      have hdom := fun e he => (hNV e he).dom
      have hcan := fun e he => (hNV e he).val
      simp only [subst_subst] at hwf hle
      -- the entries' label terms are typed at the annotation, so each
      -- extends the stage
      have hcons : ∀ e ∈ g, Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A.subst θ :: Γ') := by
        intro e he
        refine .cons Wσ hAθ ?_
        show Δ ⊢ e.tm ≡ e.tm : (A.subst θ).subst σ
        rw [subst_subst]
        exact (hwf.2.2.1.1 e he).2.1
      -- the source-side `isType`, through the `Γ`-side one
      have hisTypeSrc' : ∀ b, Interp Δ Γ' (A.subst θ) σ ρ b →
          TShape.HasType Δ b TShape.type ∧ TShape.CodeCanonS Δ ((A.subst θ).subst σ) b := by
        intro b hb
        obtain ⟨ρ_b, hb', hApb⟩ := ihA hΓ hAA hPA hΓ' hgood Wθ Wσ hAdm hSat hθ hb
        obtain ⟨ρ_s, hles, hAps, hAdms⟩ := hSat hApb
        rw [subst_subst]
        exact hAty hΔ (Ctx.SubstEq.comp hΔ Wσ Wθ) hAdms (Interp.mono_val hΔ hles hb')
      have hisTypeSrc := fun b hb => (hisTypeSrc' b hb).1
      have hAdmE : ∀ e ∈ g, Adm Δ Γ₀ (A.subst θ :: Γ') (σ.cons e.tm) (ρ.push e.inp.T) :=
        fun e he => Adm.cons hAdm hΓ' hAint
          (TShape.WF.T.2 (hwf.2.2.1.1 e he).2.2.1) (hNV e he)
          (hisTypeSrc' _ hAint).2
      have hSatE : ∀ e ∈ g, Subst.Saturates Δ Γ₀ (A :: Γ) (A.subst θ :: Γ')
          θ.lift (σ.cons e.tm) (ρ.push e.inp.T) := by
        intro e he
        obtain ⟨ρ_d, hd', hApd⟩ := ihA hΓ hAA hPA hΓ' hgood Wθ Wσ hAdm hSat hθ hAint
        exact Subst.Saturates.lift hΔ hΓ hΓ' hgood Wθ Wσ hθ (hcons e he)
          (TShape.WF.T.2 (hwf.2.2.1.1 e he).2.2.1) (hcan e he) hAty
          ⟨ρ_d, _, hApd, hd', hdom e he⟩ hSat
      obtain ⟨ρ₁, hA', hAp₁⟩ := ihA hΓ hAA hPA hΓ' hgood Wθ Wσ hAdm hSat hθ hAint
      obtain ⟨ρ₂, hAp₂, hbody'⟩ :=
        Interp.body_merge (Γ := A :: Γ) (b := b) hΔ hΓ' hgood (.skip .refl) hθ
          (l := g) (tm := fun e => e.tm) (inp := fun e => e.inp.T)
          (out := fun e => e.out.T) hcons
          (fun e he => (hwf.2.2.1.1 e he).2.2.1)
          (fun {e} he {m₂} hb₂ =>
            ihb ⟨hΓ, _, hA⟩ hAb hPb ⟨hΓ', _, hAθ⟩ hgood.lift (Wθ.lift hA hAθ) (hcons e he)
              (hAdmE e he) (hSatE e he)
              (fun i => by
                cases i with
                | zero => exact Interp.Dir.bvar (hwf.2.2.1.1 e he).2.2.1
                | succ i =>
                  exact Interp.Dir.weak_slot hΔ hΓ' (.skip .refl) (hgood i)
                    (hcons e he) (hθ i))
              hb₂)
          hbody
      obtain ⟨hAj, hl₁, hl₂⟩ := Valuation.Approx.join hΔ hθ hAp₁ hAp₂
      refine ⟨_, .lam (Interp.mono_val hΔ hl₁ hA') hdty hwf (fun e he => .of_dom (hdom e he) (hcan e he)) (fun e he => ?_) hw hle
        ⟨u, hA⟩, hAj⟩
      exact Interp.mono_val hΔ (fun i => by
        cases i with
        | zero => exact TShape.LE.refl (hwf.2.2.1.1 e he).2.2.1
        | succ i => exact hl₂ i) (hbody' e he)
  | forallE A B ihA ihB =>
    intro Γ Γ₀ Γ' θ σ ρ m hΓ hAnn hPin hΓ' hgood Wθ Wσ hAdm hSat hθ H
    obtain ⟨⟨u, hA⟩, ⟨v, hB⟩, hAA, hAB⟩ := hAnn
    obtain ⟨hAty, hPA, hPB⟩ := hPin
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hA.subst hΓ' Wθ
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | @forallE _ _ _ _ n g d _ _ hAint hdty hwf hNV hbody hw hle _ _ =>
      have hdom := fun e he => (hNV e he).dom
      have hcan := fun e he => (hNV e he).val
      simp only [subst_subst, ← Subst.comp_lift] at hwf hle
      have hcons : ∀ e ∈ g, Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A.subst θ :: Γ') := by
        intro e he
        refine .cons Wσ hAθ ?_
        show Δ ⊢ e.tm ≡ e.tm : (A.subst θ).subst σ
        rw [subst_subst]
        exact (hwf.2.2.2.1.1 e he).2.1
      have hisTypeSrc' : ∀ b, Interp Δ Γ' (A.subst θ) σ ρ b →
          TShape.HasType Δ b TShape.type ∧ TShape.CodeCanonS Δ ((A.subst θ).subst σ) b := by
        intro b hb
        obtain ⟨ρ_b, hb', hApb⟩ := ihA hΓ hAA hPA hΓ' hgood Wθ Wσ hAdm hSat hθ hb
        obtain ⟨ρ_s, hles, hAps, hAdms⟩ := hSat hApb
        rw [subst_subst]
        exact hAty hΔ (Ctx.SubstEq.comp hΔ Wσ Wθ) hAdms (Interp.mono_val hΔ hles hb')
      have hisTypeSrc := fun b hb => (hisTypeSrc' b hb).1
      have hAdmE : ∀ e ∈ g, Adm Δ Γ₀ (A.subst θ :: Γ') (σ.cons e.tm) (ρ.push e.inp.T) :=
        fun e he => Adm.cons hAdm hΓ' hAint
          (TShape.WF.T.2 (hwf.2.2.2.1.1 e he).2.2.1) (hNV e he)
          (hisTypeSrc' _ hAint).2
      have hSatE : ∀ e ∈ g, Subst.Saturates Δ Γ₀ (A :: Γ) (A.subst θ :: Γ')
          θ.lift (σ.cons e.tm) (ρ.push e.inp.T) := by
        intro e he
        obtain ⟨ρ_d, hd', hApd⟩ := ihA hΓ hAA hPA hΓ' hgood Wθ Wσ hAdm hSat hθ hAint
        exact Subst.Saturates.lift hΔ hΓ hΓ' hgood Wθ Wσ hθ (hcons e he)
          (TShape.WF.T.2 (hwf.2.2.2.1.1 e he).2.2.1) (hcan e he) hAty
          ⟨ρ_d, _, hApd, hd', hdom e he⟩ hSat
      obtain ⟨ρ₁, hA', hAp₁⟩ := ihA hΓ hAA hPA hΓ' hgood Wθ Wσ hAdm hSat hθ hAint
      obtain ⟨ρ₂, hAp₂, hbody'⟩ :=
        Interp.body_merge (Γ := A :: Γ) (b := B) hΔ hΓ' hgood (.skip .refl) hθ
          (l := g) (tm := fun e => e.tm) (inp := fun e => e.inp.T)
          (out := fun e => e.out.T) hcons
          (fun e he => (hwf.2.2.2.1.1 e he).2.2.1)
          (fun {e} he {m₂} hb₂ =>
            ihB ⟨hΓ, _, hA⟩ hAB hPB ⟨hΓ', _, hAθ⟩ hgood.lift (Wθ.lift hA hAθ) (hcons e he)
              (hAdmE e he) (hSatE e he)
              (fun i => by
                cases i with
                | zero => exact Interp.Dir.bvar (hwf.2.2.2.1.1 e he).2.2.1
                | succ i =>
                  exact Interp.Dir.weak_slot hΔ hΓ' (.skip .refl) (hgood i)
                    (hcons e he) (hθ i))
              hb₂)
          hbody
      obtain ⟨hAj, hl₁, hl₂⟩ := Valuation.Approx.join hΔ hθ hAp₁ hAp₂
      refine ⟨_, .forallE (Interp.mono_val hΔ hl₁ hA') hdty  hwf (fun e he => .of_dom (hdom e he) (hcan e he))
        (fun e he => ?_) hw hle ⟨u, hA⟩ ⟨v, hB⟩, hAj⟩
      exact Interp.mono_val hΔ (fun i => by
        cases i with
        | zero => exact TShape.LE.refl (hwf.2.2.2.1.1 e he).2.2.1
        | succ i => exact hl₂ i) (hbody' e he)
  | sigma A B ihA ihB =>
    intro Γ Γ₀ Γ' θ σ ρ m hΓ hAnn hPin hΓ' hgood Wθ Wσ hAdm hSat hθ H
    obtain ⟨⟨u, hA⟩, ⟨v, hB⟩, hAA, hAB⟩ := hAnn
    obtain ⟨hAty, hPA, hPB⟩ := hPin
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hA.subst hΓ' Wθ
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | @sigma _ _ _ _ n g d _ _ hAint hdty hwf hNV hbody hw hle _ _ =>
      have hdom := fun e he => (hNV e he).dom
      have hcan := fun e he => (hNV e he).val
      simp only [subst_subst, ← Subst.comp_lift] at hwf hle
      have hcons : ∀ e ∈ g, Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A.subst θ :: Γ') := by
        intro e he
        refine .cons Wσ hAθ ?_
        show Δ ⊢ e.tm ≡ e.tm : (A.subst θ).subst σ
        rw [subst_subst]
        exact (hwf.2.2.2.1.1 e he).2.1
      have hisTypeSrc' : ∀ b, Interp Δ Γ' (A.subst θ) σ ρ b →
          TShape.HasType Δ b TShape.type ∧ TShape.CodeCanonS Δ ((A.subst θ).subst σ) b := by
        intro b hb
        obtain ⟨ρ_b, hb', hApb⟩ := ihA hΓ hAA hPA hΓ' hgood Wθ Wσ hAdm hSat hθ hb
        obtain ⟨ρ_s, hles, hAps, hAdms⟩ := hSat hApb
        rw [subst_subst]
        exact hAty hΔ (Ctx.SubstEq.comp hΔ Wσ Wθ) hAdms (Interp.mono_val hΔ hles hb')
      have hisTypeSrc := fun b hb => (hisTypeSrc' b hb).1
      have hAdmE : ∀ e ∈ g, Adm Δ Γ₀ (A.subst θ :: Γ') (σ.cons e.tm) (ρ.push e.inp.T) :=
        fun e he => Adm.cons hAdm hΓ' hAint
          (TShape.WF.T.2 (hwf.2.2.2.1.1 e he).2.2.1) (hNV e he)
          (hisTypeSrc' _ hAint).2
      have hSatE : ∀ e ∈ g, Subst.Saturates Δ Γ₀ (A :: Γ) (A.subst θ :: Γ')
          θ.lift (σ.cons e.tm) (ρ.push e.inp.T) := by
        intro e he
        obtain ⟨ρ_d, hd', hApd⟩ := ihA hΓ hAA hPA hΓ' hgood Wθ Wσ hAdm hSat hθ hAint
        exact Subst.Saturates.lift hΔ hΓ hΓ' hgood Wθ Wσ hθ (hcons e he)
          (TShape.WF.T.2 (hwf.2.2.2.1.1 e he).2.2.1) (hcan e he) hAty
          ⟨ρ_d, _, hApd, hd', hdom e he⟩ hSat
      obtain ⟨ρ₁, hA', hAp₁⟩ := ihA hΓ hAA hPA hΓ' hgood Wθ Wσ hAdm hSat hθ hAint
      obtain ⟨ρ₂, hAp₂, hbody'⟩ :=
        Interp.body_merge (Γ := A :: Γ) (b := B) hΔ hΓ' hgood (.skip .refl) hθ
          (l := g) (tm := fun e => e.tm) (inp := fun e => e.inp.T)
          (out := fun e => e.out.T) hcons
          (fun e he => (hwf.2.2.2.1.1 e he).2.2.1)
          (fun {e} he {m₂} hb₂ =>
            ihB ⟨hΓ, _, hA⟩ hAB hPB ⟨hΓ', _, hAθ⟩ hgood.lift (Wθ.lift hA hAθ) (hcons e he)
              (hAdmE e he) (hSatE e he)
              (fun i => by
                cases i with
                | zero => exact Interp.Dir.bvar (hwf.2.2.2.1.1 e he).2.2.1
                | succ i =>
                  exact Interp.Dir.weak_slot hΔ hΓ' (.skip .refl) (hgood i)
                    (hcons e he) (hθ i))
              hb₂)
          hbody
      obtain ⟨hAj, hl₁, hl₂⟩ := Valuation.Approx.join hΔ hθ hAp₁ hAp₂
      refine ⟨_, .sigma (Interp.mono_val hΔ hl₁ hA') hdty  hwf (fun e he => .of_dom (hdom e he) (hcan e he))
        (fun e he => ?_) hw hle ⟨u, hA⟩ ⟨v, hB⟩, hAj⟩
      exact Interp.mono_val hΔ (fun i => by
        cases i with
        | zero => exact TShape.LE.refl (hwf.2.2.2.1.1 e he).2.2.1
        | succ i => exact hl₂ i) (hbody' e he)
  | pair A B a b ihA ihB iha ihb =>
    intro Γ Γ₀ Γ' θ σ ρ m hΓ hAnn hPin hΓ' hgood Wθ Wσ hAdm hSat hθ H
    obtain ⟨⟨u, hA⟩, ⟨v, hB⟩, hat, hAA, hAB, hAa, hAb⟩ := hAnn
    obtain ⟨hAty, hPA, hPB, hPa, hPb⟩ := hPin
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hA.subst hΓ' Wθ
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | @pair _ _ _ _ n x y d c _ _ _ _ hainp hbout hAint hdty hNV hdc hwf hcode hcty 
        hw hle _ _ =>
      have hdx := hNV.dom
      have hxc := hNV.val
      simp only [subst_subst] at hwf hle
      have htm : Δ ⊢ (a.subst θ).subst σ ≡ (a.subst θ).subst σ : (A.subst θ).subst σ := by
        rw [subst_subst, subst_subst]
        exact IsDefEq.subst hΔ (Ctx.SubstEq.comp hΔ Wσ Wθ) hat
      have hcons : Ctx.SubstEq Δ (σ.cons ((a.subst θ).subst σ))
          (σ.cons ((a.subst θ).subst σ)) (A.subst θ :: Γ') := .cons Wσ hAθ htm
      have hisTypeSrc' : ∀ b, Interp Δ Γ' (A.subst θ) σ ρ b →
          TShape.HasType Δ b TShape.type ∧ TShape.CodeCanonS Δ ((A.subst θ).subst σ) b := by
        intro b hb
        obtain ⟨ρ_b, hb', hApb⟩ := ihA hΓ hAA hPA hΓ' hgood Wθ Wσ hAdm hSat hθ hb
        obtain ⟨ρ_s, hles, hAps, hAdms⟩ := hSat hApb
        rw [subst_subst]
        exact hAty hΔ (Ctx.SubstEq.comp hΔ Wσ Wθ) hAdms (Interp.mono_val hΔ hles hb')
      have hisTypeSrc := fun b hb => (hisTypeSrc' b hb).1
      have hAdmE : Adm Δ Γ₀ (A.subst θ :: Γ') (σ.cons ((a.subst θ).subst σ)) (ρ.push x.T) :=
        Adm.cons hAdm hΓ' hAint (TShape.WF.T.2 hwf.2.2.2.1) (.of_dom hdx hxc) hdc
      have hSatE :
          Subst.Saturates Δ Γ₀ (A :: Γ) (A.subst θ :: Γ') θ.lift
            (σ.cons ((a.subst θ).subst σ)) (ρ.push x.T) := by
        obtain ⟨ρ_d, hd', hApd⟩ := ihA hΓ hAA hPA hΓ' hgood Wθ Wσ hAdm hSat hθ hAint
        exact Subst.Saturates.lift hΔ hΓ hΓ' hgood Wθ Wσ hθ hcons
          (TShape.WF.T.2 hwf.2.2.2.1) hxc hAty ⟨ρ_d, _, hApd, hd', hdx⟩ hSat
      obtain ⟨ρ₁, hA', hAp₁⟩ := ihA hΓ hAA hPA hΓ' hgood Wθ Wσ hAdm hSat hθ hAint
      obtain ⟨ρ₂, ha', hAp₂⟩ := iha hΓ hAa hPa hΓ' hgood Wθ Wσ hAdm hSat hθ hainp
      obtain ⟨ρ₃, hb', hAp₃⟩ := ihb hΓ hAb hPb hΓ' hgood Wθ Wσ hAdm hSat hθ hbout
      obtain ⟨ρ₄, hAp₄, hcode'⟩ :=
        Interp.body_merge (Γ := A :: Γ) (b := B) hΔ hΓ' hgood (.skip .refl) hθ
          (l := [()]) (tm := fun _ => (a.subst θ).subst σ) (inp := fun _ => x.T)
          (out := fun _ => c) (fun _ _ => hcons) (fun _ _ => TShape.WF.T.2 hwf.2.2.2.1)
          (fun {_} _ {m₂} hb₂ =>
            ihB ⟨hΓ, _, hA⟩ hAB hPB ⟨hΓ', _, hAθ⟩ hgood.lift (Wθ.lift hA hAθ) hcons
              hAdmE hSatE
              (fun i => by
                cases i with
                | zero => exact Interp.Dir.bvar (TShape.WF.T.2 hwf.2.2.2.1)
                | succ i =>
                  exact Interp.Dir.weak_slot hΔ hΓ' (.skip .refl) (hgood i) hcons (hθ i))
              hb₂)
          (fun _ _ => hcode)
      obtain ⟨hAj₁, hl₁, hl₂⟩ := Valuation.Approx.join hΔ hθ hAp₁ hAp₂
      obtain ⟨hAj₂, hl₃, hl₄⟩ := Valuation.Approx.join hΔ hθ hAp₃ hAp₄
      obtain ⟨hAj, hl₅, hl₆⟩ := Valuation.Approx.join hΔ hθ hAj₁ hAj₂
      refine ⟨_, .pair
        (Interp.mono_val hΔ (fun i => (hl₂ i).trans hΔ (hl₅ i)) ha')
        (Interp.mono_val hΔ (fun i => (hl₃ i).trans hΔ (hl₆ i)) hb')
        (Interp.mono_val hΔ (fun i => (hl₁ i).trans hΔ (hl₅ i)) hA')
        hdty (by simpa only [subst_subst] using TShape.Named.of_dom hdx hxc)
        (by simpa only [subst_subst] using hdc)
        hwf ?_ hcty hw hle ⟨u, hA⟩ hat, hAj⟩
      have hcode'' := hcode' () (by simp)
      rw [subst_subst] at hcode''
      exact Interp.mono_val hΔ (fun i => by
        cases i with
        | zero => exact TShape.LE.refl (TShape.WF.T.2 hwf.2.2.2.1)
        | succ i => exact TShape.LE.trans hΔ (hl₄ i) (hl₆ i)) hcode''
  | natCase C M a b ihC ihM iha ihb =>
    intro Γ Γ₀ Γ' θ σ ρ m hΓ hAnn hPin hΓ' hgood Wθ Wσ hAdm hSat hθ H
    obtain ⟨hMt, hAC, hAM, hAa, hAb⟩ := hAnn
    obtain ⟨hMty, hPC, hPM, hPa, hPb⟩ := hPin
    have hΓN : ⊢ (Term.nat :: Γ) := ⟨hΓ, _, .nat⟩
    have hΓN' : ⊢ (Term.nat :: Γ') := ⟨hΓ', _, .nat⟩
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | natCase_zero hM hz ha _ =>
      rw [subst_subst] at hz
      obtain ⟨ρ₁, hM', hAp₁⟩ := ihM hΓ hAM hPM hΓ' hgood Wθ Wσ hAdm hSat hθ hM
      obtain ⟨ρ₂, ha', hAp₂⟩ := iha hΓ hAa hPa hΓ' hgood Wθ Wσ hAdm hSat hθ ha
      obtain ⟨hAj, hl₁, hl₂⟩ := Valuation.Approx.join hΔ hθ hAp₁ hAp₂
      exact ⟨_, .natCase_zero (Interp.mono_val hΔ hl₁ hM') hz
        (Interp.mono_val hΔ hl₂ ha') hMt, hAj⟩
    | @natCase_succ _ _ _ _ _ _ _ _ n v t hM hwv heq hbody _ =>
      rw [subst_subst] at heq
      have hcons : Ctx.SubstEq Δ (σ.cons t) (σ.cons t) (Term.nat :: Γ') :=
        .cons Wσ .nat (heq.succ_regular (.inr rfl))
      -- the slot is the scrutinee's predecessor, hence a numeral: read the
      -- scrutinee's own typing on the `Γ` side, where it is provable
      obtain ⟨ρ_M, hM₀, hApM⟩ := ihM hΓ hAM hPM hΓ' hgood Wθ Wσ hAdm hSat hθ hM
      obtain ⟨ρ_s, hles, hAps, hAdms⟩ := hSat hApM
      have hvnat : TShape.HasType Δ v.T TShape.nat := by
        obtain ⟨c, hc, hty⟩ := hMty hΔ (Ctx.SubstEq.comp hΔ Wσ Wθ) hAdms
          (Interp.mono_val hΔ hles hM₀)
        exact (TShape.HasType.isNumeral hΔ (Interp.le_nat hc) hty).pred.hasType
      have hisTypeNat : ∀ b, Interp Δ Γ' Term.nat σ ρ b → TShape.HasType Δ b TShape.type :=
        fun _ hb => TShape.HasType.mono_l hΔ .nat (Interp.le_nat hb)
      have hvcan : TShape.ValCanon Δ t v.T := Shape.ValCanon.of_numeral
        (TShape.HasType.isNumeral hΔ (TShape.LE.refl (a := TShape.nat) trivial) hvnat)
      have hAdmE : Adm Δ Γ₀ (Term.nat :: Γ') (σ.cons t) (ρ.push v.T) :=
        Adm.cons hAdm hΓ' Interp.nat' (TShape.WF.T.2 hwv)
          (.of_dom (TShape.Dom.of_not_binder (fun h => h) hvnat) hvcan) (TyEq.refl .nat)
      have hSatE : Subst.Saturates Δ Γ₀ (Term.nat :: Γ) (Term.nat :: Γ')
          θ.lift (σ.cons t) (ρ.push v.T) := by
        refine Subst.Saturates.lift (A := Term.nat) hΔ hΓ hΓ' hgood Wθ Wσ hθ
          (by simpa using hcons) (TShape.WF.T.2 hwv) hvcan
          IsTypeAt.nat ?_ hSat
        exact ⟨ρ_s, TShape.nat, hAps, Interp.nat',
          TShape.Dom.of_not_binder (fun h => h) hvnat⟩
      obtain ⟨ρ₁, hM', hAp₁⟩ := ihM hΓ hAM hPM hΓ' hgood Wθ Wσ hAdm hSat hθ hM
      obtain ⟨ρ₂, hAp₂, hbody'⟩ :=
        Interp.body_merge (Γ := Term.nat :: Γ) (b := b) (Γ'' := Term.nat :: Γ') hΔ hΓ'
          hgood (by simpa using Ctx.Lift'.skip (A := Term.nat) (.refl (Γ := Γ'))) hθ
          (l := [()]) (tm := fun _ => t) (inp := fun _ => v.T) (out := fun _ => m)
          (fun _ _ => hcons) (fun _ _ => TShape.WF.T.2 hwv)
          (fun {_} _ {m₂} hb₂ =>
            ihb hΓN hAb hPb hΓN' hgood.lift (by simpa using Wθ.lift (.nat) (.nat)) hcons
              hAdmE hSatE
              (fun i => by
                cases i with
                | zero => exact Interp.Dir.bvar (TShape.WF.T.2 hwv)
                | succ i =>
                  exact Interp.Dir.weak_slot hΔ hΓ' (.skip .refl) (hgood i) hcons (hθ i))
              hb₂)
          (fun _ _ => hbody)
      obtain ⟨hAj, hl₁, hl₂⟩ := Valuation.Approx.join hΔ hθ hAp₁ hAp₂
      refine ⟨_, .natCase_succ (Interp.mono_val hΔ hl₁ hM') hwv heq ?_ hMt, hAj⟩
      exact Interp.mono_val hΔ (fun i => by
        cases i with
        | zero => exact TShape.LE.refl (TShape.WF.T.2 hwv)
        | succ i => exact hl₂ i) (hbody' () (by simp))
  | Y A b ihA ihb =>
    intro Γ Γ₀ Γ' θ σ ρ m hΓ hAnn hPin hΓ' hgood Wθ Wσ hAdm hSat hθ H
    obtain ⟨⟨u, hA⟩, hYt, hAA, hAb⟩ := hAnn
    obtain ⟨hAty, hYty, hPA, hPb⟩ := hPin
    -- the tower is not structural in the term, so this case runs on the
    -- derivation, each level's self-premise being the level below
    have key : ∀ {Γ₂ : List Term} {t' σ₂ ρ₂ m}, Interp Δ Γ₂ t' σ₂ ρ₂ m →
        t' = (Term.Y A b).subst θ → ⊢ Γ₂ → Subst.Good Γ₂ θ → Ctx.SubstEq Γ₂ θ θ Γ →
        Ctx.SubstEq Δ σ₂ σ₂ Γ₂ → Adm Δ Γ₀ Γ₂ σ₂ ρ₂ → Subst.Saturates Δ Γ₀ Γ Γ₂ θ σ₂ ρ₂ →
        (∀ i, Interp.Dir Δ Γ₂ (θ i) σ₂ ρ₂) →
        ∃ ρ', Interp Δ Γ (Term.Y A b) (θ.comp σ₂) ρ' m ∧
          Valuation.Approx Δ Γ₂ θ σ₂ ρ₂ ρ' := by
      intro Γ₂ t' σ₂ ρ₂ m H
      induction H with
      | bot => exact fun _ _ _ _ _ _ _ _ => ⟨Valuation.nil, .bot, .nil⟩
      | @Y Γ₂ σ₂ ρ₂ m A₂ b₂ x d hx hwx hAd hdty hNV hdc hbody _ _ ihx _ _ =>
        have hDom := hNV.dom
        have hxc := hNV.val
        intro ht' hΓ₂ hgood₂ Wθ₂ Wσ₂ hAdm₂ hSat₂ hθ₂
        cases ht'
        have hAθ : Γ₂ ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hA.subst hΓ₂ Wθ₂
        have hcons : Ctx.SubstEq Δ (σ₂.cons (((Term.Y A b).subst θ).subst σ₂))
            (σ₂.cons (((Term.Y A b).subst θ).subst σ₂)) (A.subst θ :: Γ₂) :=
          .cons Wσ₂ hAθ (IsDefEq.subst hΔ Wσ₂ (IsDefEq.subst hΓ₂ Wθ₂ hYt))
        -- the slot's own hereditary typing is a premise of the clause, so
        -- the extended stage needs only the annotation moved to `Γ`
        obtain ⟨ρ₁, hx', hAp₁⟩ := ihx rfl hΓ₂ hgood₂ Wθ₂ Wσ₂ hAdm₂ hSat₂ hθ₂
        obtain ⟨ρ_d, hd', hApd⟩ := ihA hΓ hAA hPA hΓ₂ hgood₂ Wθ₂ Wσ₂ hAdm₂ hSat₂ hθ₂ hAd
        have hisTypeSrc' : ∀ c, Interp Δ Γ₂ (A.subst θ) σ₂ ρ₂ c →
            TShape.HasType Δ c TShape.type ∧ TShape.CodeCanonS Δ ((A.subst θ).subst σ₂) c := by
          intro c hc
          obtain ⟨ρ_c, hc', hApc⟩ := ihA hΓ hAA hPA hΓ₂ hgood₂ Wθ₂ Wσ₂ hAdm₂ hSat₂ hθ₂ hc
          obtain ⟨ρ_t, hlet, hApt, hAdmt⟩ := hSat₂ hApc
          rw [subst_subst]
          exact hAty hΔ (Ctx.SubstEq.comp hΔ Wσ₂ Wθ₂) hAdmt (Interp.mono_val hΔ hlet hc')
        have hisTypeSrc := fun c hc => (hisTypeSrc' c hc).1
        have hAdmE : Adm Δ Γ₀ (A.subst θ :: Γ₂)
            (σ₂.cons (((Term.Y A b).subst θ).subst σ₂)) (ρ₂.push x) :=
          Adm.cons hAdm₂ hΓ₂ hAd hwx (.of_dom hDom hxc) hdc
        have hSatE : Subst.Saturates Δ Γ₀ (A :: Γ) (A.subst θ :: Γ₂) θ.lift
            (σ₂.cons (((Term.Y A b).subst θ).subst σ₂)) (ρ₂.push x) :=
          Subst.Saturates.lift hΔ hΓ hΓ₂ hgood₂ Wθ₂ Wσ₂ hθ₂ hcons hwx hxc hAty
            ⟨ρ_d, d, hApd, hd', hDom⟩ hSat₂
        obtain ⟨ρ₂, hAp₂, hbody'⟩ :=
          Interp.body_merge (Γ := A :: Γ) (b := b) hΔ hΓ₂ hgood₂ (.skip .refl) hθ₂
            (l := [()]) (tm := fun _ => ((Term.Y A b).subst θ).subst σ₂)
            (inp := fun _ => x) (out := fun _ => m)
            (fun _ _ => hcons) (fun _ _ => hwx)
            (fun {_} _ {m₂} hb₂ =>
              ihb ⟨hΓ, _, hA⟩ hAb hPb ⟨hΓ₂, _, hAθ⟩ hgood₂.lift (Wθ₂.lift hA hAθ) hcons
                hAdmE hSatE
                (fun i => by
                  cases i with
                  | zero => exact Interp.Dir.bvar hwx
                  | succ i =>
                    exact Interp.Dir.weak_slot hΔ hΓ₂ (.skip .refl) (hgood₂ i) hcons
                      (hθ₂ i))
                hb₂)
            (fun _ _ => hbody)
        obtain ⟨hAj₀, hl₁, hl₂⟩ := Valuation.Approx.join hΔ hθ₂ hAp₁ hAp₂
        obtain ⟨hAj, hlj, hld⟩ := Valuation.Approx.join hΔ hθ₂ hAj₀ hApd
        refine ⟨_, .Y (Interp.mono_val hΔ (fun i => (hl₁ i).trans hΔ (hlj i)) hx') hwx
          (Interp.mono_val hΔ hld hd') hdty
          (.of_dom hDom (by rw [← subst_subst (e := Term.Y A b)]; exact hxc))
          (by rw [← subst_subst]; exact hdc) ?_ ⟨u, hA⟩ hYt, hAj⟩
        have hb' := hbody' () (by simp)
        rw [show ((Term.Y A b).subst θ).subst σ₂ = (Term.Y A b).subst (θ.comp σ₂) from
          subst_subst] at hb'
        exact Interp.mono_val hΔ (fun i => by
          cases i with
          | zero => exact TShape.LE.refl hwx
          | succ i => exact (hl₂ i).trans hΔ (hlj i)) hb'
      | _ => intro ht' _ _ _ _ _ _ _; cases ht'
    exact key H rfl hΓ' hgood Wθ Wσ hAdm hSat hθ
  | tr r A a b C X Hp ihA iha ihb ihC ihX ihH =>
    intro Γ Γ₀ Γ' θ σ ρ m hΓ hAnn hPin hΓ' hgood Wθ Wσ hAdm hSat hθ H
    obtain ⟨⟨u, hA⟩, hat, hbt, hht, _, hAA, hAa, hAb, hAC, hAX, hAH⟩ := hAnn
    obtain ⟨hAty, hPA, hPa, hPb, hPC, hPX, hPH⟩ := hPin
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hA.subst hΓ' Wθ
    have hbθ : Δ ⊢ (b.subst θ).subst σ ≡ (b.subst θ).subst σ : (A.subst θ).subst σ :=
      IsDefEq.subst hΔ Wσ (IsDefEq.subst hΓ' Wθ hbt)
    have hcons : Ctx.SubstEq Δ (σ.cons ((b.subst θ).subst σ))
        (σ.cons ((b.subst θ).subst σ)) (A.subst θ :: Γ') := .cons Wσ hAθ hbθ
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | @tr _ _ _ _ v vA m' cb _ _ _ _ _ _ _ hw hle hX ha hb hAint hwv hNV hvc hC hcb hNV2 hcbc 
        hH heq _ _ _ =>
      have hvA := hNV.dom
      have hbc := hNV.val
      have hm' := hNV2.dom
      have hmc := hNV2.val
      simp only [subst_subst] at heq
      obtain ⟨ρ₁, hX', hAp₁⟩ := ihX hΓ hAX hPX hΓ' hgood Wθ Wσ hAdm hSat hθ hX
      obtain ⟨ρ₂, ha', hAp₂⟩ := iha hΓ hAa hPa hΓ' hgood Wθ Wσ hAdm hSat hθ ha
      obtain ⟨ρ₃, hb', hAp₃⟩ := ihb hΓ hAb hPb hΓ' hgood Wθ Wσ hAdm hSat hθ hb
      obtain ⟨ρ₄, hA', hAp₄⟩ := ihA hΓ hAA hPA hΓ' hgood Wθ Wσ hAdm hSat hθ hAint
      have hisTypeSrc' : ∀ c, Interp Δ Γ' (A.subst θ) σ ρ c →
          TShape.HasType Δ c TShape.type ∧ TShape.CodeCanonS Δ ((A.subst θ).subst σ) c := by
        intro c hc
        obtain ⟨ρ_c, hc', hApc⟩ := ihA hΓ hAA hPA hΓ' hgood Wθ Wσ hAdm hSat hθ hc
        obtain ⟨ρ_t, hlet, hApt, hAdmt⟩ := hSat hApc
        rw [subst_subst]
        exact hAty hΔ (Ctx.SubstEq.comp hΔ Wσ Wθ) hAdmt (Interp.mono_val hΔ hlet hc')
      have hisTypeSrc := fun c hc => (hisTypeSrc' c hc).1
      have hAdmE : Adm Δ Γ₀ (A.subst θ :: Γ') (σ.cons ((b.subst θ).subst σ)) (ρ.push v) :=
        Adm.cons hAdm hΓ' hAint hwv (.of_dom hvA hbc) hvc
      have hSatE : Subst.Saturates Δ Γ₀ (A :: Γ) (A.subst θ :: Γ') θ.lift
          (σ.cons ((b.subst θ).subst σ)) (ρ.push v) :=
        Subst.Saturates.lift hΔ hΓ hΓ' hgood Wθ Wσ hθ hcons hwv hbc hAty
          ⟨ρ₄, _, hAp₄, hA', hvA⟩ hSat
      obtain ⟨ρ₅, hAp₅, hC'⟩ :=
        Interp.body_merge (Γ := A :: Γ) (b := C) hΔ hΓ' hgood (.skip .refl) hθ
          (l := [()]) (tm := fun _ => (b.subst θ).subst σ) (inp := fun _ => v)
          (out := fun _ => cb)
          (fun _ _ => hcons) (fun _ _ => hwv)
          (fun {_} _ {m₂} hb₂ =>
            ihC ⟨hΓ, _, hA⟩ hAC hPC ⟨hΓ', _, hAθ⟩ hgood.lift (Wθ.lift hA hAθ) hcons
              hAdmE hSatE
              (fun i => by
                cases i with
                | zero => exact Interp.Dir.bvar hwv
                | succ i =>
                  exact Interp.Dir.weak_slot hΔ hΓ' (.skip .refl) (hgood i) hcons (hθ i))
              hb₂)
          (fun _ _ => hC)
      obtain ⟨hAj₁, hl₁, hl₂⟩ := Valuation.Approx.join hΔ hθ hAp₁ hAp₂
      obtain ⟨hAj₂, hl₃, hl₄⟩ := Valuation.Approx.join hΔ hθ hAp₃ hAp₄
      obtain ⟨hAj₄, hl₇, hl₈⟩ := Valuation.Approx.join hΔ hθ hAj₁ hAj₂
      obtain ⟨hAj, hl₉, hl₁₀⟩ := Valuation.Approx.join hΔ hθ hAj₄ hAp₅
      have hCb := hC' () (by simp)
      rw [show (b.subst θ).subst σ = b.subst (θ.comp σ) from subst_subst] at hCb
      refine ⟨_, .tr hw hle
        (Interp.mono_val hΔ (fun i => (hl₁ i).trans hΔ ((hl₇ i).trans hΔ (hl₉ i))) hX')
        (Interp.mono_val hΔ (fun i => (hl₂ i).trans hΔ ((hl₇ i).trans hΔ (hl₉ i))) ha')
        (Interp.mono_val hΔ (fun i => (hl₃ i).trans hΔ ((hl₈ i).trans hΔ (hl₉ i))) hb')
        (Interp.mono_val hΔ (fun i => (hl₄ i).trans hΔ ((hl₈ i).trans hΔ (hl₉ i))) hA')
        hwv (by simpa only [subst_subst] using TShape.Named.of_dom hvA hbc)
        (by simpa only [subst_subst] using hvc)
        ?_ hcb (by simpa only [subst_subst] using TShape.Named.of_dom hm' hmc)
        (by simpa only [subst_subst, Subst.lift_comp_cons] using hcbc)
        (fun hr => by simpa only [subst_subst] using hH hr)
        heq ⟨u, hA⟩ hat hbt, hAj⟩
      exact Interp.mono_val hΔ (fun i => by
        cases i with
        | zero => exact TShape.LE.refl hwv
        | succ i => exact hl₁₀ i) hCb




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
theorem Interp.substTerm {T : Term} {Γ₀ : List Term} (hΔ : ⊢ Δ) {θ : Subst} (hΓ : ⊢ Γ)
    (ht : Γ ⊢ t : T) (hPin : t.Pinned Γ)
    (hΓ' : ⊢ Γ') (hgood : Subst.Good Γ' θ) (Wθ : Ctx.SubstEq Γ' θ θ Γ)
    (Wσ : Ctx.SubstEq Δ σ σ Γ') (hAdm : Adm Δ Γ₀ Γ' σ ρ)
    (hSat : Subst.Saturates Δ Γ₀ Γ Γ' θ σ ρ)
    (hθ : ∀ i, Interp.Dir Δ Γ' (θ i) σ ρ) :
    Interp Δ Γ' (t.subst θ) σ ρ m ↔
    ∃ ρ', Interp Δ Γ t (θ.comp σ) ρ' m ∧ ∀ i, Interp Δ Γ' (θ i) σ ρ (ρ' i) :=
  ⟨Interp.to_substTerm hΔ hΓ ht.annot.1 hPin hΓ' hgood Wθ Wσ hAdm hSat hθ,
    fun ⟨_, h, hs⟩ => Interp.of_substTerm hΔ h hΓ' Wθ rfl hs⟩

/-- The single-substitution form, which is what `beta` uses: `b[a]` at
stage `σ` is `b` at the stage extended by `a[σ]`, under the valuation
extended by an approximant of `a`.  Master's `LE_Interp.inst`. -/
theorem Interp.inst {B : Term} {Γ₀ : List Term} (hΔ : ⊢ Δ) (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A : .sort u) (hat : Γ ⊢ a : A) (hb : A :: Γ ⊢ b : B)
    (hPin : b.Pinned (A :: Γ)) (Wσ : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ₀ Γ σ ρ)
    (hSat : Subst.Saturates Δ Γ₀ (A :: Γ) Γ (Subst.one a) σ ρ)
    (ha : Interp.Dir Δ Γ a σ ρ) (hρ : Valuation.WF Δ ρ) :
    Interp Δ Γ (b.inst a) σ ρ m ↔
    ∃ x, Interp Δ (A :: Γ) b ((Subst.one a).comp σ) (ρ.push x) m ∧ Interp Δ Γ a σ ρ x :=
  -- at `θ = one a`: slot `0` holds the argument's approximant and slot
  -- `i+1` the valuation's own, and `Subst.Good` holds for just that reason
  have hgood : Subst.Good Γ (Subst.one a) := Subst.Good.one hat.annot.1
  have Wθ : Ctx.SubstEq Γ (Subst.one a) (Subst.one a) (A :: Γ) := by
    refine .cons ?_ hA ?_
    · simpa [Subst.one] using Ctx.SubstEq.id hΓ
    · simpa [Subst.one, subst_id] using hat
  ⟨fun h => by
    obtain ⟨ρ', hb', hs⟩ := Interp.to_substTerm (Γ := A :: Γ) hΔ ⟨hΓ, _, hA⟩ hb.annot.1
      hPin hΓ hgood Wθ Wσ hAdm hSat
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

/-- Directedness over a list: finitely many approximants of one term have
one above them all.  `Interp.Dir.join` iterated, with `⊥` at the empty
list — what η needs, since the expansion's graph is finite. -/
theorem Interp.Dir.list {Δ Γ : List Term} {t σ ρ} (hΔ : ⊢ Δ) (h : Interp.Dir Δ Γ t σ ρ)
    {α : Type} {ms : α → TShape} : ∀ (l : List α), (∀ a ∈ l, Interp Δ Γ t σ ρ (ms a)) →
      ∃ s, TShape.WF Δ s ∧ Interp Δ Γ t σ ρ s ∧ ∀ a ∈ l, TShape.LE Δ (ms a) s
  | [], _ => ⟨TShape.bot, trivial, .bot, fun _ h => absurd h (by simp)⟩
  | a :: l, hl => by
    obtain ⟨s, hws, hs, hle⟩ := Interp.Dir.list hΔ h l (fun b hb => hl b (.tail _ hb))
    have ha := hl a (.head _)
    obtain ⟨hc, hj⟩ := h.join hΔ ha hs
    obtain ⟨hla, hls⟩ := TShape.le_join hΔ ha.wf hws hc
    refine ⟨_, TShape.WF.join hΔ hc ha.wf hws, hj, fun b hb => ?_⟩
    cases hb with
    | head => exact hla
    | tail _ hb => exact TShape.LE.trans hΔ (hle b hb) hls
