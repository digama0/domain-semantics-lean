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
λ-shape.

After the relation's own theory comes what a *stage* has to satisfy for it
to be of use: admissibility `Adm`, the three valuation relations it is
bounded by, and the semantic side conditions that `Interp.to_substTerm`
needs and the subject's syntax does not supply (`IsTypeAt`, `PinApp` and
`PinSnd`, collected per former as `Term.Pinned`).  All of them are stated
without `SoundTy`, which is what keeps this file below soundness. -/

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

/-- Pointwise order on valuations, at a stage, **over `Γ`'s variables
only**.  A `Valuation` is a total function, so it has slots past the end
of the context it interprets, and those are junk: a substitution into `Γ`
has `.bvar i` at every slot past `Γ`, in range or not.  Saying nothing
about them is what lets the junk go unmentioned, and `Lookup` is how the
context says where its variables stop — chosen over `i < Γ.length`
because `Lookup.weak'` already transports it across a context lift, which
a bare bound would need a new lemma for at every index-moving step. -/
def Valuation.LE (Δ Γ : List Term) (ρ ρ' : Valuation) : Prop :=
  ∀ {{i A}}, Lookup Γ i A → TShape.LE Δ (ρ i) (ρ' i)

/-- Pointwise well-formedness, over `Γ`'s variables only. -/
def Valuation.WF (Δ Γ : List Term) (ρ : Valuation) : Prop :=
  ∀ {{i A}}, Lookup Γ i A → TShape.WF Δ (ρ i)

theorem Valuation.LE.refl {Δ Γ : List Term} {ρ : Valuation} (h : ρ.WF Δ Γ) :
    ρ.LE Δ Γ ρ := fun {_ _} hlk => .refl (h hlk)

theorem Valuation.LE.push {Δ Γ : List Term} {A : Term} {ρ ρ' : Valuation}
    {u u' : TShape} :
    (ρ.push u).LE Δ (A :: Γ) (ρ'.push u') ↔ ρ.LE Δ Γ ρ' ∧ u.LE Δ u' :=
  ⟨fun H => ⟨fun {_ _} hlk => H (.succ hlk), H .zero⟩,
    fun ⟨H1, H2⟩ => fun {_ _} => fun
      | .zero => H2
      | .succ hlk => H1 hlk⟩

theorem Valuation.WF.push {Δ Γ : List Term} {A : Term} {ρ : Valuation} {u : TShape}
    (h : ρ.WF Δ Γ) (hu : u.WF Δ) : (ρ.push u).WF Δ (A :: Γ)
  | _, _, .zero => hu
  | _, _, .succ hlk => h hlk

theorem Valuation.WF.subst {Δ Θ Γ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {ρ : Valuation} (h : ρ.WF Δ Γ) :
    (ρ.subst τ).WF Θ Γ := fun {_ _} hlk => (h hlk).subst hΘ W

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
  | bvar : Lookup Γ i A → TShape.LE Δ m (ρ i) →
    Interp Δ Γ (.bvar i) σ ρ m
  | sort : TShape.LE Δ m (.sort r) → Interp Δ Γ (.sort r) σ ρ m
  | unit : TShape.LE Δ m (.unit r) → Interp Δ Γ (.unit r) σ ρ m
  -- `star r` has only the `bot` rule: the unit type's inhabitant carries
  -- no information, which is what makes `unit_eta` sound
  | nat : TShape.LE Δ m .nat → Interp Δ Γ .nat σ ρ m
  | zero : TShape.LE Δ m .zero → Interp Δ Γ .zero σ ρ m
  | succ {n} {v : Shape n} :
    Interp Δ Γ N σ ρ v.T → TShape.LE Δ m (Shape.T (n := n+1) v.succ) → Interp Δ Γ (.succ N) σ ρ m
  /-- Application is the **graph lookup at the syntactic label**.  The
  argument's type is not recorded by `Term.app`; it is read off the
  function's λ-shape, whose domain label `A` (a term of `Δ`) every entry's
  type agrees with (`Shape.WF`).  The label is `(A, a[σ])`.

  Taking the type from the shape rather than as a free parameter is what
  pins the lookup at every well-formed valuation, admissible or not.
  Naming it in `Δ` rather than in `Γ` is also what makes `Interp.subst` an
  equivalence: a substitution in the term leaves the label's type alone.

  The lookup is `TEvaluates`, over `TShape`s, not the level-indexed
  `ShapeFun.Eval`: the input and output of a lookup in a *bigger* graph
  land at that graph's level, and the reflection back down does not exist
  (`ShapeFun.Eval.lift` only goes up).  Directedness needs exactly that
  move, so the rule is stated where it is available. -/
  | app {n} {g : ShapeFun n} {x y : TShape} {A : Term} :
    Interp Δ Γ F σ ρ (Shape.T (n := n+1) (ShapeS.lam A g)) →
    Interp Δ Γ a σ ρ x →
    TEvaluates Δ g A (a.subst σ) x y →
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
    (∀ e ∈ g, TShape.Named Δ d e.inp.T e.tm) →
    (∀ e ∈ g, Interp Δ (A :: Γ) b (σ.cons e.tm) (ρ.push e.inp.T) e.out.T) →
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
    (∀ e ∈ g, TShape.Named Δ d.T e.inp.T e.tm) →
    (∀ e ∈ g, Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push e.inp.T) e.out.T) →
    TShape.LE Δ m (Shape.T (n := n+1) (.forallE (A.subst σ) (B.subst σ.lift) d g)) →
    (∃ u, Γ ⊢ A : .sort u) → (∃ v, A :: Γ ⊢ B : .sort v) →
    Interp Δ Γ (.forallE A B) σ ρ m
  /-- Σ, mirroring `forallE` exactly. -/
  | sigma {n} {g : ShapeFun n} {d : Shape n} {A B : Term} :
      Interp Δ Γ A σ ρ (Shape.T d) →
      TShape.HasType Δ (Shape.T d) TShape.type →
      Shape.WF (n := n+1) Δ (ShapeS.sigma (A.subst σ) (B.subst σ.lift) d g) →
      (∀ e ∈ g, TShape.Named Δ (Shape.T d) (Shape.T e.inp) e.tm) →
      (∀ e ∈ g, Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push (Shape.T e.inp)) (Shape.T e.out)) →
      TShape.LE Δ m
        (Shape.T (n := n+1) (ShapeS.sigma (A.subst σ) (B.subst σ.lift) d g)) →
      (∃ u, Γ ⊢ A : .sort u) → (∃ v, A :: Γ ⊢ B : .sort v) →
      Interp Δ Γ (.sigma A B) σ ρ m
  /-- A pair is its two components, with the first's term as its name
  (`design.md` §2).  The name is what the codomain code is read at — the second
  component's type is `B[a]` — and it is also what `snd` queries, so the
  value says which term its first component stands for.  There is no
  graph: an entry's input would be a condition the order enforces and the
  term's meaning does not, which is exactly what Σ's η cannot have. -/
  | pair {n} {x y : Shape n} {d c : TShape} {A B a b : Term} :
      Interp Δ Γ a σ ρ (Shape.T x) →
      Interp Δ Γ b σ ρ (Shape.T y) →
      Interp Δ Γ A σ ρ d →
      TShape.HasType Δ d TShape.type →
      TShape.Slot Δ (A.subst σ) d (a.subst σ) (Shape.T x) →
      Shape.WF (n := n+1) Δ (ShapeS.pair (A.subst σ) (a.subst σ) x y) →
      Interp Δ (A :: Γ) B (σ.cons (a.subst σ)) (ρ.push (Shape.T x)) c →
      TShape.Named Δ c (Shape.T y) none →
      TShape.LE Δ m
        (Shape.T (n := n+1) (ShapeS.pair (A.subst σ) (a.subst σ) x y)) →
      (∃ u, Γ ⊢ A : .sort u) → (Γ ⊢ a : A) →
      Interp Δ Γ (.pair A B a b) σ ρ m
  /-- The first projection reads the first component. -/
  | fst {n} {A₀ a₀ : Term} {x y : Shape n} :
      Interp Δ Γ p σ ρ (Shape.T (n := n+1) (ShapeS.pair A₀ a₀ x y)) →
      TShape.LE Δ m (Shape.T x) →
      Interp Δ Γ (.fst p) σ ρ m
  /-- The second projection reads the second component, at a pair whose
  name is `fst p` — the label invariant of `design.md` §6, as a clause
  premise rather than a graph query.  The name is what makes `snd p`'s
  type `B[fst p]` rather than `B` at some other term. -/
  | snd {n} {A₀ a₀ : Term} {x y : Shape n} :
      Interp Δ Γ p σ ρ (Shape.T (n := n+1) (ShapeS.pair A₀ a₀ x y)) →
      Δ ⊢ a₀ ≡ (Term.fst p).subst σ : A₀ →
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
    Δ ⊢ M.subst σ ≡ .succ t : .nat →
    Interp Δ (.nat :: Γ) b (σ.cons t) (ρ.push v.T) m →
    (Γ ⊢ M : Term.nat) →
    Interp Δ Γ (.natCase C M a b) σ ρ m
  /-- The fixed point is a least fixed point for free: the constructor
  refers to the relation it is defining, so only finitely many unfoldings
  can ever produce a given approximant. -/
  | protected Y {A b : Term} {x d : TShape} :
    Interp Δ Γ (.Y A b) σ ρ x →
    Interp Δ Γ A σ ρ d →
    TShape.HasType Δ d TShape.type →
    TShape.Slot Δ (A.subst σ) d ((A.Y b).subst σ) x →
    Interp Δ (A :: Γ) b (σ.cons ((A.Y b).subst σ)) (ρ.push x) m →
    (∃ u, Γ ⊢ A : .sort u) → (Γ ⊢ Term.Y A b : A) →
    Interp Δ Γ (.Y A b) σ ρ m
  /-- The identity type is **label-only**: no sub-shapes, so the shape
  records nothing but the syntax. -/
  | protected id : TShape.LE Δ m (Shape.T (n := 1) (.id r (A.subst σ) (a.subst σ) (b.subst σ))) →
    (∃ u, Γ ⊢ A : .sort u) → (Γ ⊢ a : A) → (Γ ⊢ b : A) →
    Interp Δ Γ (.id r A a b) σ ρ m
  /-- `refl` has a shape only in the proof-relevant sort; at `r = false`
  the `bot` rule is all there is, which is proof irrelevance. -/
  | protected refl {n} :
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
  `fst (tr … X h)` — which breaks Σ's η (`design.md` §6).  With the
  equation the transport is `X` by `tr_refl`, and names move along it.  At
  `r = false` the equation is `proofIrrel`, so only `a ≡ b` is asked. -/
  | tr {v vA m' cb : TShape} {r : Bool} {A a b C X H : Term} :
    TShape.LE Δ m m' →
    Interp Δ Γ X σ ρ m' →
    Interp Δ Γ a σ ρ v →
    Interp Δ Γ b σ ρ v →
    Interp Δ Γ A σ ρ vA →
    TShape.Slot Δ (A.subst σ) vA (b.subst σ) v →
    Interp Δ (A :: Γ) C (σ.cons (b.subst σ)) (ρ.push v) cb →
    TShape.HasType Δ cb TShape.type →
    TShape.Slot Δ (C.subst (σ.cons (b.subst σ))) cb (X.subst σ) m' →
    (r = true → Δ ⊢ H.subst σ ≡ .refl true (a.subst σ) :
      .id true (A.subst σ) (a.subst σ) (b.subst σ)) →
    Δ ⊢ a.subst σ ≡ b.subst σ : A.subst σ →
    (∃ u, Γ ⊢ A : .sort u) → (Γ ⊢ a : A) → (Γ ⊢ b : A) →
    Interp Δ Γ (.tr r A a b C X H) σ ρ m

theorem Interp.of_bot {Δ Γ σ ρ} {t : Term} {m : TShape} (h : m.2 = .bot) :
    Interp Δ Γ t σ ρ m := by
  have hm : m = Shape.T (n := m.1) m.2 := rfl
  rw [h] at hm
  exact hm ▸ .bot

/-! ## Monotonicity

Both directions master has: down in the shape, up in the valuation.
Neither touches the stage, so both are the same induction as there. -/

theorem Interp.wf {Δ Γ : List Term} {t : Term} {σ ρ m}
    (H : Interp Δ Γ t σ ρ m) : m.WF Δ := by
  induction H with
  | bot => exact .bot
  | bvar _ h | sort h | unit h | nat h | zero h | succ _ h
  | app _ _ _ h | lam _ _ _ _ _ h | forallE _ _ _ _ _ h | id h | refl h | tr h
  | sigma _ _ _ _ _ h | pair _ _ _ _ _ _ _ _ h | fst _ h | snd _ _ h => exact h.wf
  -- the eliminators read `m` off a subderivation, so the bound is there
  | natCase_zero _ _ _ _ _ ih | natCase_succ _ _ _ _ _ ih
  | Y _ _ _ _ _ _ _ _ _ ih => exact ih

theorem Interp.mono (hΔ : ⊢ Δ) {Γ : List Term} {t : Term} {σ ρ} {m m' : TShape}
    (h : m.LE Δ m') (H : Interp Δ Γ t σ ρ m') :
    Interp Δ Γ t σ ρ m := by
  induction H generalizing m with
  | bot =>
    obtain ⟨k, s⟩ := m
    cases show s = .bot from TShape.le_bot hΔ rfl h
    exact .bot
  | bvar hlk h1 => exact .bvar hlk (h.trans hΔ h1)
  | sort h1 => exact .sort (h.trans hΔ h1)
  | unit h1 => exact .unit (h.trans hΔ h1)
  | nat h1 => exact .nat (h.trans hΔ h1)
  | zero h1 => exact .zero (h.trans hΔ h1)
  | succ hv h1 => exact .succ hv (h.trans hΔ h1)
  | app hF ha hev h1 hty => exact .app hF ha hev (h.trans hΔ h1) hty
  | lam hA hd hwf hNV hbody h1 hAt => exact .lam hA hd hwf hNV hbody (h.trans hΔ h1) hAt
  | forallE hA hd hwf hNV hbody h1 hAt hBt =>
    exact .forallE hA hd hwf hNV hbody (h.trans hΔ h1) hAt hBt
  | sigma hA hd hwf hNV hbody h1 hAt hBt =>
    exact .sigma hA hd hwf hNV hbody (h.trans hΔ h1) hAt hBt
  | pair ha hb hA hd hslot hwf hcode hcty h1 hAt hat =>
    exact .pair ha hb hA hd hslot hwf hcode hcty (h.trans hΔ h1) hAt hat
  | fst hp h1 => exact .fst hp (h.trans hΔ h1)
  | snd hp hlab h1 hty => exact .snd hp hlab (h.trans hΔ h1) hty
  | natCase_zero hM hz _ hMt _ iha => exact .natCase_zero hM hz (iha h) hMt
  | natCase_succ hM heq _ hMt _ ihb => exact .natCase_succ hM heq (ihb h) hMt
  | Y hself hA hdty hslot _ hAt hYt _ _ ihb => exact .Y hself hA hdty hslot (ihb h) hAt hYt
  | id h1 hAt hat hbt => exact .id (h.trans hΔ h1) hAt hat hbt
  | refl h1 => exact .refl (h.trans hΔ h1)
  | tr hle hX ha hb hA hslotv hC hcb hslotc hH heq hAt hat hbt =>
    have hm' := hslotc.1.forget
    exact .tr (h.trans hΔ hle) hX ha hb hA hslotv hC hcb hslotc hH heq hAt hat hbt

theorem Interp.mono_val {Γ : List Term} {t : Term} {σ} {ρ ρ' : Valuation} {m : TShape}
    (hΔ : ⊢ Δ) (hρ : ρ.LE Δ Γ ρ') (H : Interp Δ Γ t σ ρ m) : Interp Δ Γ t σ ρ' m := by
  induction H generalizing ρ' with
  | bot => exact .bot
  | bvar hlk h1 => exact .bvar hlk (h1.trans hΔ (hρ hlk))
  | sort h1 => exact .sort h1
  | unit h1 => exact .unit h1
  | nat h1 => exact .nat h1
  | zero h1 => exact .zero h1
  | succ _ h1 ihv => exact .succ (ihv hρ) h1
  | app _ _ hev h1 hty ihF iha => exact .app (ihF hρ) (iha hρ) hev h1 hty
  | lam _ hd hwf hNV _ h1 hAt ihA ihbody =>
    refine .lam (ihA hρ) hd hwf hNV (fun e he => ?_) h1 hAt
    exact ihbody e he (Valuation.LE.push.2 ⟨hρ, .refl (hwf.2.2.1.1 e he).2.2.1⟩)
  | forallE _ hd hwf hNV _ h1 hAt hBt ihA ihbody =>
    refine .forallE (ihA hρ) hd hwf hNV (fun e he => ?_) h1 hAt hBt
    exact ihbody e he (Valuation.LE.push.2 ⟨hρ, .refl (hwf.2.2.2.1.1 e he).2.2.1⟩)
  | sigma _ hd hwf hNV _ h1 hAt hBt ihA ihbody =>
    refine .sigma (ihA hρ) hd hwf hNV (fun e he => ?_) h1 hAt hBt
    exact ihbody e he
      (Valuation.LE.push.2 ⟨hρ, TShape.LE.refl (a := e.inp.T) (hwf.2.2.2.1.1 e he).2.2.1⟩)
  | pair _ _ _ hd hslot hwf _ hcty h1 hAt hat iha ihb ihA ihcode =>
    refine .pair (iha hρ) (ihb hρ) (ihA hρ) hd hslot hwf ?_ hcty h1 hAt hat
    exact ihcode (Valuation.LE.push.2 ⟨hρ, .refl (TShape.WF.T.2 hwf.2.2.2.1)⟩)
  | fst _ h1 ihp => exact .fst (ihp hρ) h1
  | snd _ hq h1 hty ihp => exact .snd (ihp hρ) hq h1 hty
  | natCase_zero _ hz _ hMt ihM iha => exact .natCase_zero (ihM hρ) hz (iha hρ) hMt
  | natCase_succ hM heq _ hMt ihM ihb =>
    refine .natCase_succ (ihM hρ) heq ?_ hMt
    exact ihb (Valuation.LE.push.2 ⟨hρ, .refl (a := Shape.T _) hM.wf⟩)
  | Y hself _ hdty hslot _ hAt hYt ihself ihA ihb =>
    refine .Y (ihself hρ) (ihA hρ) hdty hslot ?_ hAt hYt
    exact ihb (Valuation.LE.push.2 ⟨hρ, .refl hself.wf⟩)
  | id h1 hAt hat hbt => exact .id h1 hAt hat hbt
  | refl h1 => exact .refl h1
  | tr hle _ ha _ _ hslotv _ hcb hslotc hH heq hAt hat hbt ihX iha ihb ihA ihC =>
    have hm' := hslotc.1.forget
    refine .tr hle (ihX hρ) (iha hρ) (ihb hρ) (ihA hρ) hslotv ?_ hcb hslotc hH heq hAt hat hbt
    exact ihC (Valuation.LE.push.2 ⟨hρ, .refl ha.wf⟩)

/-! ### Changing the context

With the labels' typings in the clauses, an interpretation no longer
reads at *any* context: it reads at any context the typings survive in,
which is any context definitionally equal to this one.  That is all the
binder congruences need — they move a body from `A :: Γ` to `A' :: Γ`
after the domain has changed — and it is what the annotations' typings
buy. -/

theorem IsDefEq.ctx_id {Γ Γ' : List Term} (hΓ' : ⊢ Γ')
    (W : Ctx.SubstEq Γ' .id .id Γ) {e₁ e₂ A : Term}
    (h : Γ ⊢ e₁ ≡ e₂ : A) : Γ' ⊢ e₁ ≡ e₂ : A := by simpa using h.subst hΓ' W

theorem Ctx.SubstEq.id_lift {Γ Γ' : List Term} {A : Term} {u : Bool} (hΓ' : ⊢ Γ')
    (W : SubstEq Γ' .id .id Γ) (hA : Γ ⊢ A : .sort u) :
    SubstEq (A :: Γ') .id .id (A :: Γ) := by
  have h := W.lift hA (by simpa using hA.ctx_id hΓ' W)
  simpa using h

/-- The context change the binder congruences need: the head has moved
along a definitional equality. -/
theorem Ctx.SubstEq.defeqHead {Γ : List Term} {A A' : Term} {u : Bool} (hΓ : ⊢ Γ)
    (hAA' : Γ ⊢ A ≡ A' : .sort u) : SubstEq (A' :: Γ) .id .id (A :: Γ) := by
  refine .cons (SubstEq.id hΓ).skip hAA'.hasType.1 ?_
  rw [show A.subst Subst.id.tail = A.lift' (.skip .refl) by
    show A.subst (Subst.id.lift_r (.skip .refl)) = _
    rw [← lift'_subst, subst_id]]
  exact (hAA'.weak' (Lift'.skip (A := A') .refl)).symm.defeqDF
    (.bvar .zero (hAA'.hasType.2.weak' (Lift'.skip (A := A') .refl)))

/-- The lookup transport `Interp.ctx` asks for when only the head of the
context changed, which is the only way its callers use it. -/
theorem Lookup.cons_head {Γ : List Term} {A A' : Term} :
    ∀ {{i B}}, Lookup (A :: Γ) i B → ∃ B', Lookup (A' :: Γ) i B'
  | _, _, .zero => ⟨_, .zero⟩
  | _, _, .succ h => ⟨_, .succ h⟩

/-- The lookup transport `Interp.ctx` asks for, extended by a binder. -/
theorem Lookup.cons_transport {Γ Γ' : List Term} {A : Term}
    (hL : ∀ {{i B}}, Lookup Γ i B → ∃ B', Lookup Γ' i B') :
    ∀ {{i B}}, Lookup (A :: Γ) i B → ∃ B', Lookup (A :: Γ') i B'
  | _, _, .zero => ⟨_, .zero⟩
  | _, _, .succ h => match hL h with | ⟨_, h'⟩ => ⟨_, .succ h'⟩

theorem Interp.ctx {Δ Γ : List Term} {t σ ρ m} (H : Interp Δ Γ t σ ρ m)
    {Γ' : List Term} (hΓ' : ⊢ Γ') (W : Ctx.SubstEq Γ' .id .id Γ)
    (hL : ∀ {{i A}}, Lookup Γ i A → ∃ A', Lookup Γ' i A') : Interp Δ Γ' t σ ρ m := by
  induction H generalizing Γ' with
  | bot => exact .bot
  | bvar hlk h => obtain ⟨_, hlk'⟩ := hL hlk; exact .bvar hlk' h
  | sort h => exact .sort h
  | unit h => exact .unit h
  | nat h => exact .nat h
  | zero h => exact .zero h
  | succ _ h ih => exact .succ (ih hΓ' W hL) h
  | app _ _ hev h hty ihF iha => exact .app (ihF hΓ' W hL) (iha hΓ' W hL) hev h (hty.ctx W)
  | @lam _ _ _ _ _ _ _ A _ _ hd hwf hNV _ h hAt ihA ihbody =>
    obtain ⟨u, hA⟩ := hAt
    have hA' : Γ' ⊢ A ≡ A : .sort u := hA.ctx_id hΓ' W
    refine .lam (ihA hΓ' W hL) hd hwf hNV (fun e he => ?_) h ⟨u, hA'⟩
    exact ihbody e he ⟨hΓ', _, hA'⟩ (W.id_lift hΓ' hA) (Lookup.cons_transport hL)
  | @forallE _ _ _ _ _ _ _ A B _ hd hwf hNV _ h hAt hBt ihA ihbody =>
    obtain ⟨u, hA⟩ := hAt
    obtain ⟨v, hB⟩ := hBt
    have hA' : Γ' ⊢ A ≡ A : .sort u := hA.ctx_id hΓ' W
    have hΓ'A : ⊢ (A :: Γ') := ⟨hΓ', _, hA'⟩
    refine .forallE (ihA hΓ' W hL) hd hwf hNV (fun e he => ?_) h ⟨u, hA'⟩
      ⟨v, hB.ctx_id hΓ'A (W.id_lift hΓ' hA)⟩
    exact ihbody e he hΓ'A (W.id_lift hΓ' hA) (Lookup.cons_transport hL)
  | @sigma _ _ _ _ _ _ _ A B _ hd hwf hNV _ h hAt hBt ihA ihbody =>
    obtain ⟨u, hA⟩ := hAt
    obtain ⟨v, hB⟩ := hBt
    have hA' : Γ' ⊢ A ≡ A : .sort u := hA.ctx_id hΓ' W
    have hΓ'A : ⊢ (A :: Γ') := ⟨hΓ', _, hA'⟩
    refine .sigma (ihA hΓ' W hL) hd hwf hNV (fun e he => ?_) h ⟨u, hA'⟩
      ⟨v, hB.ctx_id hΓ'A (W.id_lift hΓ' hA)⟩
    exact ihbody e he hΓ'A (W.id_lift hΓ' hA) (Lookup.cons_transport hL)
  | pair _ _ _ hd hslot hwf _ hcty h hAt hat iha ihb ihA ihcode =>
    obtain ⟨u, hA⟩ := hAt
    have hA' := hA.ctx_id hΓ' W
    refine .pair (iha hΓ' W hL) (ihb hΓ' W hL) (ihA hΓ' W hL) hd hslot hwf ?_ hcty h ⟨u, hA'⟩
      (hat.ctx_id hΓ' W)
    exact ihcode ⟨hΓ', _, hA'⟩ (W.id_lift hΓ' hA) (Lookup.cons_transport hL)
  | fst _ h ihp => exact .fst (ihp hΓ' W hL) h
  | snd _ hlab h hty ihp => exact .snd (ihp hΓ' W hL) hlab h (hty.ctx W)
  | natCase_zero _ hz _ hMt ihM iha =>
    exact .natCase_zero (ihM hΓ' W hL) hz (iha hΓ' W hL) (hMt.ctx_id hΓ' W)
  | natCase_succ hM heq _ hMt ihM ihb =>
    refine .natCase_succ (ihM hΓ' W hL) heq ?_ (hMt.ctx_id hΓ' W)
    exact ihb ⟨hΓ', _, .nat⟩ (W.id_lift hΓ' .nat) (Lookup.cons_transport hL)
  | @Y _ _ _ _ A _ _ _ _ _ hdty hslot _ hAt hYt ihself ihA ihb =>
    obtain ⟨u, hA⟩ := hAt
    have hA' : Γ' ⊢ A ≡ A : .sort u := hA.ctx_id hΓ' W
    refine .Y (ihself hΓ' W hL) (ihA hΓ' W hL) hdty hslot ?_ ⟨u, hA'⟩ (hYt.ctx_id hΓ' W)
    exact ihb ⟨hΓ', _, hA'⟩ (W.id_lift hΓ' hA) (Lookup.cons_transport hL)
  | id h hAt hat hbt =>
    obtain ⟨u, hA⟩ := hAt
    exact .id h ⟨u, hA.ctx_id hΓ' W⟩ (hat.ctx_id hΓ' W) (hbt.ctx_id hΓ' W)
  | refl h => exact .refl h
  | @tr _ _ _ _ _ _ _ _ _ A _ _ _ _ _ hle _ _ _ _ hslotv _ hcb hslotc hH heq hAt hat hbt
      ihX iha ihb ihA ihC =>
    have hm' := hslotc.1.forget
    obtain ⟨u, hA⟩ := hAt
    have hA' : Γ' ⊢ A ≡ A : .sort u := hA.ctx_id hΓ' W
    refine .tr hle (ihX hΓ' W hL) (iha hΓ' W hL) (ihb hΓ' W hL) (ihA hΓ' W hL) hslotv ?_ hcb
      hslotc hH heq ⟨u, hA'⟩ (hat.ctx_id hΓ' W) (hbt.ctx_id hΓ' W)
    exact ihC ⟨hΓ', _, hA'⟩ (W.id_lift hΓ' hA) (Lookup.cons_transport hL)

/-! ## Constructors at the canonical shape

Master's primed forms.  Each takes the well-formedness that `LE` needs to
be reflexive, which master gets from its shapes being a `WF` subtype. -/

theorem Interp.sort' {Δ Γ σ ρ r} :
    Interp Δ Γ (.sort r) σ ρ (.sort r) :=
  .sort (TShape.LE.refl (a := .sort r) trivial)

theorem Interp.unit' {Δ Γ σ ρ r} :
    Interp Δ Γ (.unit r) σ ρ (.unit r) :=
  .unit (TShape.LE.refl (a := .unit r) trivial)

theorem Interp.nat' {Δ Γ σ ρ} : Interp Δ Γ .nat σ ρ .nat :=
  .nat (TShape.LE.refl (a := .nat) trivial)

theorem Interp.le_sort {Δ Γ σ ρ m r}
    (H : Interp Δ Γ (.sort r) σ ρ m) : m.LE Δ (.sort r) := by
  cases H with
  | bot => exact TShape.bot_le' rfl
  | sort h => exact h

theorem Interp.le_unit {Δ Γ σ ρ m r}
    (H : Interp Δ Γ (.unit r) σ ρ m) : m.LE Δ (.unit r) := by
  cases H with
  | bot => exact TShape.bot_le' rfl
  | unit h => exact h

theorem Interp.le_nat {Δ Γ σ ρ m}
    (H : Interp Δ Γ .nat σ ρ m) : m.LE Δ .nat := by
  cases H with
  | bot => exact TShape.bot_le' rfl
  | nat h => exact h

theorem Interp.le_zero {Δ Γ σ ρ m}
    (H : Interp Δ Γ .zero σ ρ m) : m.LE Δ .zero := by
  cases H with
  | bot => exact TShape.bot_le' rfl
  | zero h => exact h

theorem Interp.le_id {Δ Γ σ ρ m r A a b}
    (H : Interp Δ Γ (.id r A a b) σ ρ m) :
    m.LE Δ
      (Shape.T (n := 1) (.id r (A.subst σ) (a.subst σ) (b.subst σ))) := by
  cases H with
  | bot => exact TShape.bot_le' rfl
  | id h => exact h

/-- A variable's approximant is below its slot.  One-directional: the
converse would have to produce the clause's `Lookup`, and a shape sitting
below a slot says nothing about the context. -/
theorem Interp.bvar_le {Δ Γ σ ρ m i} (H : Interp Δ Γ (.bvar i) σ ρ m) :
    m.LE Δ (ρ i) := by
  cases H with
  | bot => exact TShape.bot_le' rfl
  | bvar _ h => exact h

theorem Interp.le_forallE {Δ Γ σ ρ m A B}
    (H : Interp Δ Γ (.forallE A B) σ ρ m) :
    m.2 = .bot ∨
    ∃ n, ∃ d : Shape n, ∃ g : ShapeFun n,
      m.LE Δ (Shape.T (n := n+1) (.forallE (A.subst σ) (B.subst σ.lift) d g)) := by
  cases H with
  | bot => exact .inl rfl
  | forallE _ _ _ _ _ h => exact .inr ⟨_, _, _, h⟩

/-- The Σ case, as `le_forallE`. -/
theorem Interp.le_sigma (H : Interp Δ Γ (.sigma A B) σ ρ m) :
    m.2 = .bot ∨
      ∃ n, ∃ d : Shape n, ∃ g : ShapeFun n,
        m.LE Δ
          (Shape.T (n := n+1) (.sigma (A.subst σ) (B.subst σ.lift) d g)) := by
  cases H with
  | bot => exact .inl rfl
  | sigma _ _ _ _ _ h => exact .inr ⟨_, _, _, h⟩

/-! ## The Π label, in and out

This is the other repo's `mem_piAtom_pi_iff`, and the point of the whole
labelling.  He proves that the label-only Π atom is a member of a Π value
**iff** its label is the reindexed label; equality of labels there is
equality in his quotient, which is definitional equality, which is our
`PiLabelEq`.

Master has nothing like this.  In its place master carries a second
inductive with one constructor per term former running in lockstep with
the semantics, so that the logical relation can read the head former back
out — and then needs `LogRel.lean` plus
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
  .forallE (d := (.bot : Shape 0)) .bot (.bot .sort) (.piAtom hA hB) nofun nofun
    (TShape.LE.T.2 (.refl (.piAtom hA hB))) ⟨u, hAΓ⟩ ⟨v, hBΓ⟩

/-- And the probe reports: if the atom approximates `⟦forallE A B⟧`, its
label is definitionally the Π's own label.  Π-injectivity is this plus
soundness, with no adequacy in between. -/
theorem Interp.le_piAtom (H : Interp Δ Γ (.forallE A B) σ ρ (Shape.T (n := 1) (.piAtom A' B'))) :
    PiLabelEq Δ A' B' (A.subst σ) (B.subst σ.lift) := by
  cases H with | forallE _ _ _ _ _ h
  have h' := (TShape.LE.def_mp (Nat.succ_le_succ (Nat.zero_le _)) (Nat.le_refl _)) h
  rw [Shape.lift_piAtom, Shape.lift_self] at h'
  exact Shape.piAtom_le_forallE h'

/-- The Σ probe, as `piAtom`. -/
theorem Interp.sigmaAtom (hA : Δ ⊢ A.subst σ : .sort u)
    (hB : A.subst σ :: Δ ⊢ B.subst σ.lift : .sort v)
    (hAΓ : Γ ⊢ A : .sort u) (hBΓ : A :: Γ ⊢ B : .sort v) :
    Interp Δ Γ (.sigma A B) σ ρ (Shape.T (n := 1) (.sigmaAtom (A.subst σ) (B.subst σ.lift))) :=
  .sigma (d := (.bot : Shape 0)) .bot (.bot .sort) (.sigmaAtom hA hB) nofun nofun
    (TShape.LE.T.2 (.refl (.sigmaAtom hA hB))) ⟨u, hAΓ⟩ ⟨v, hBΓ⟩

theorem Interp.le_sigmaAtom
    (H : Interp Δ Γ (.sigma A B) σ ρ (Shape.T (n := 1) (.sigmaAtom A' B'))) :
    PiLabelEq Δ A' B' (A.subst σ) (B.subst σ.lift) := by
  cases H with | sigma _ _ _ _ _ h
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
  | bvar hlk h1 => exact .bvar hlk (h1.subst hΘ W)
  | sort h1 => exact .sort (by simpa using .subst hΘ W h1)
  | unit h1 => exact .unit (h1.subst hΘ W)
  | nat h1 => exact .nat (h1.subst hΘ W)
  | zero h1 => exact .zero (h1.subst hΘ W)
  | succ _ h1 ihv => exact .succ (ihv hΘ W) (h1.subst hΘ W)
  | app _ _ hev h1 hty ihF iha =>
    have hev' := hev.subst hΘ W
    rw [subst_subst] at hev'
    exact .app (ihF hΘ W) (iha hΘ W) hev' (h1.subst hΘ W) (hty.subst W)
  | lam _ hd hwf hNV _ h1 hAt ihA ihbody =>
    have hwf' := hwf.subst hΘ W; have h1' := h1.subst hΘ W
    rw [Shape.subst, subst_subst] at hwf'
    simp only [TShape.subst_T, Shape.subst, subst_subst] at h1'
    refine .lam (ihA hΘ W) (hd.subst hΘ W) hwf' (fun e' he' => ?_) (fun e' he' => ?_) h1' hAt
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      exact (hNV e he).subst hΘ W
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have := ihbody e he hΘ W
      rwa [Subst.cons_comp, Valuation.subst_push, TShape.subst_T] at this
  | forallE _ hd hwf hNV _ h1 hAt hBt ihA ihbody =>
    have hwf' := hwf.subst hΘ W
    have h1' := h1.subst hΘ W
    simp only [TShape.subst_T, Shape.subst, subst_subst, ← Subst.comp_lift] at hwf' h1'
    refine .forallE (ihA hΘ W) (hd.subst hΘ W) hwf'
      (fun e' he' => ?_) (fun e' he' => ?_) h1' hAt hBt
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      exact (hNV e he).subst hΘ W
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have := ihbody e he hΘ W
      rwa [Subst.cons_comp, Valuation.subst_push, TShape.subst_T] at this
  | sigma _ hd hwf hNV _ h1 hAt hBt ihA ihbody =>
    have hwf' := hwf.subst hΘ W
    have h1' := h1.subst hΘ W
    simp only [TShape.subst_T, Shape.subst, subst_subst, ← Subst.comp_lift] at hwf' h1'
    refine .sigma (ihA hΘ W) (hd.subst hΘ W) hwf'
      (fun e' he' => ?_) (fun e' he' => ?_) h1' hAt hBt
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      exact (hNV e he).subst hΘ W
    · obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have := ihbody e he hΘ W
      rwa [Subst.cons_comp, Valuation.subst_push, TShape.subst_T] at this
  | @pair _ _ _ _ _ _ _ _ _ _ _ _ _ ha hb hA hd hslot hwf hcode hcty h1
      hAt hat iha ihb ihA ihcode =>
    have hwf' := hwf.subst hΘ W
    have h1' := h1.subst hΘ W
    simp only [TShape.subst_T, Shape.subst, subst_subst] at hwf' h1'
    have hcode' := ihcode hΘ W
    rw [Subst.cons_comp, Valuation.subst_push, TShape.subst_T, subst_subst] at hcode'
    refine .pair (iha hΘ W) (ihb hΘ W) (ihA hΘ W) (hd.subst hΘ W) ?_ hwf' hcode' ?_ h1' hAt hat
    · simpa [subst_subst] using hslot.subst hΘ W
    · simpa using hcty.subst hΘ W
  | fst _ h1 ihp => exact .fst (ihp hΘ W) (h1.subst hΘ W)
  | snd _ hlab h1 hty ihp =>
    have hlab' := hlab.subst hΘ W
    rw [subst_subst] at hlab'
    exact .snd (ihp hΘ W) hlab' (h1.subst hΘ W) (hty.subst W)
  | natCase_zero _ hz _ hMt ihM iha =>
    have hz' := hz.subst hΘ W
    rw [subst_subst] at hz'
    exact .natCase_zero (ihM hΘ W) hz' (iha hΘ W) hMt
  | natCase_succ hM heq _ hMt ihM ihb =>
    have heq' := heq.subst hΘ W
    rw [subst_subst] at heq'
    refine .natCase_succ (ihM hΘ W) heq' ?_ hMt
    have := ihb hΘ W
    rwa [Subst.cons_comp, Valuation.subst_push, TShape.subst_T] at this
  | Y hself _ hdty hslot _ hAt hYt ihself ihA ihb =>
    refine .Y (ihself hΘ W) (ihA hΘ W) (hdty.subst hΘ W) ?_ ?_ hAt hYt
    · simpa [subst_subst] using hslot.subst hΘ W
    have := ihb hΘ W
    rwa [Subst.cons_comp, subst_subst, Valuation.subst_push] at this
  | id h1 hAt hat hbt =>
    have := h1.subst hΘ W
    simp only [TShape.subst_T, Shape.subst, subst_subst] at this
    exact .id this hAt hat hbt
  | refl h1 => exact .refl (h1.subst hΘ W)
  | tr hle _ ha _ _ hslotv _ hcb hslotc hH heq hAt hat hbt ihX iha ihb ihA ihC =>
    have heq' := heq.subst hΘ W
    rw [subst_subst, subst_subst, subst_subst] at heq'
    refine .tr (hle.subst hΘ W) (ihX hΘ W) (iha hΘ W) (ihb hΘ W) (ihA hΘ W) ?_ ?_ (hcb.subst hΘ W)
      ?_ (fun hr => ?_) heq' hAt hat hbt
    · simpa [subst_subst] using hslotv.subst hΘ W
    · have := ihC hΘ W
      rwa [Subst.cons_comp, subst_subst, Valuation.subst_push] at this
    · simpa [subst_subst, Subst.cons_comp] using hslotc.subst hΘ W
    · simpa [subst_subst, Term.subst] using (hH hr).subst hΘ W

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

theorem Subst.lift_l_cons : (lift_l l σ).cons e = lift_l l.cons (σ.cons e) := by
  funext i; cases i <;> rfl

theorem Interp.weak' {Δ : List Term} {Γ t σ' ρ m l} (hΓ : ⊢ Γ)
    (H : Interp Δ Γ t (σ'.lift_l l) ρ m)
    {Γ' ρ'} (WΓ : Ctx.Lift' l Γ Γ') (hρ : ∀ i, ρ i = ρ' (l.liftVar i)) :
    Interp Δ Γ' (t.lift' l) σ' ρ' m := by
  generalize hσ : σ'.lift_l l = σ at H
  induction H generalizing Γ' l σ' ρ' with subst hσ
  | bot => exact .bot
  | bvar hlk h1 => exact .bvar (hlk.weak' WΓ) (hρ _ ▸ h1)
  | sort h1 => exact .sort h1
  | unit h1 => exact .unit h1
  | nat h1 => exact .nat h1
  | zero h1 => exact .zero h1
  | succ _ h1 ihv => exact .succ (ihv hΓ WΓ hρ rfl) h1
  | app _ _ hev h1 hty ihF iha =>
    rw [← subst_lift'] at hev
    exact .app (ihF hΓ WΓ hρ rfl) (iha hΓ WΓ hρ rfl) hev h1 (hty.weak' hΓ WΓ)
  | lam _ hd hwf hNV _ h1 hAt ihA ihbody =>
    rw [← subst_lift'] at hwf h1
    obtain ⟨u, hA⟩ := hAt
    refine .lam (ihA hΓ WΓ hρ rfl) hd hwf hNV (fun e he => ?_) h1 ⟨u, hA.weak' WΓ⟩
    refine ihbody e he ⟨hΓ, _, hA⟩ (l := l.cons) WΓ.cons (fun i => ?_) Subst.lift_l_cons.symm
    cases i <;> simp_all [Valuation.push]
  | forallE _ hd hwf hNV _ h1 hAt hBt ihA ihbody =>
    rw [Subst.lift_l_lift, ← subst_lift', ← subst_lift'] at hwf h1
    obtain ⟨u, hA⟩ := hAt
    obtain ⟨v, hB⟩ := hBt
    refine .forallE (ihA hΓ WΓ hρ rfl) hd hwf hNV (fun e he => ?_) h1 ⟨u, hA.weak' WΓ⟩
      ⟨v, hB.weak' WΓ.cons⟩
    refine ihbody e he ⟨hΓ, _, hA⟩ (l := l.cons) WΓ.cons (fun i => ?_) Subst.lift_l_cons.symm
    cases i <;> simp_all [Valuation.push]
  | sigma _ hd hwf hNV _ h1 hAt hBt ihA ihbody =>
    rw [Subst.lift_l_lift, ← subst_lift', ← subst_lift'] at hwf h1
    obtain ⟨u, hA⟩ := hAt
    obtain ⟨v, hB⟩ := hBt
    refine .sigma (ihA hΓ WΓ hρ rfl) hd hwf hNV (fun e he => ?_) h1 ⟨u, hA.weak' WΓ⟩
      ⟨v, hB.weak' WΓ.cons⟩
    refine ihbody e he ⟨hΓ, _, hA⟩ (l := l.cons) WΓ.cons (fun i => ?_) Subst.lift_l_cons.symm
    cases i <;> simp_all [Valuation.push]
  | pair _ _ _ hd hslot hwf _ hcty h1 hAt hat iha ihb ihA ihcode =>
    simp only [← subst_lift'] at hwf h1 hslot
    obtain ⟨u, hA⟩ := hAt
    refine .pair (iha hΓ WΓ hρ rfl) (ihb hΓ WΓ hρ rfl) (ihA hΓ WΓ hρ rfl) hd hslot
      hwf ?_ hcty h1 ⟨u, hA.weak' WΓ⟩ (hat.weak' WΓ)
    refine ihcode ⟨hΓ, _, hA⟩ (l := l.cons) WΓ.cons (fun i => ?_)
      (by rw [subst_lift']; exact Subst.lift_l_cons.symm)
    cases i <;> simp_all [Valuation.push]
  | fst _ h1 ihp => exact .fst (ihp hΓ WΓ hρ rfl) h1
  | snd _ hlab h1 hty ihp =>
    rw [← subst_lift'] at hlab
    exact .snd (ihp hΓ WΓ hρ rfl) hlab h1 (by simpa using hty.weak' hΓ WΓ)
  | natCase_zero _ hz _ hMt ihM iha =>
    rw [← subst_lift'] at hz
    exact .natCase_zero (ihM hΓ WΓ hρ rfl) hz (iha hΓ WΓ hρ rfl) (by simpa using hMt.weak' WΓ)
  | natCase_succ hM heq _ hMt ihM ihb =>
    rw [← subst_lift'] at heq
    refine .natCase_succ (ihM hΓ WΓ hρ rfl) heq ?_ (by simpa using hMt.weak' WΓ)
    refine ihb ⟨hΓ, _, .nat⟩ (l := l.cons) (by simpa using WΓ.cons (A := .nat)) (fun i => ?_)
      Subst.lift_l_cons.symm
    cases i <;> simp_all [Valuation.push]
  | Y _ hA hdty hslot _ hAt hYt ihself ihA ihb =>
    obtain ⟨u, hA⟩ := hAt
    simp only [← subst_lift'] at hslot
    refine .Y (ihself hΓ WΓ hρ rfl) (ihA hΓ WΓ hρ rfl) hdty hslot ?_ ⟨u, hA.weak' WΓ⟩
      (by simpa using hYt.weak' WΓ)
    refine ihb ⟨hΓ, _, hA⟩ (l := l.cons) WΓ.cons (fun i => ?_) ?_
    · cases i <;> simp_all [Valuation.push]
    · rw [← Subst.lift_l_cons]
      exact congrArg _ (subst_lift' (e := Term.Y ..))
  | id h1 hAt hat hbt =>
    simp only [← subst_lift'] at h1
    obtain ⟨u, hA⟩ := hAt
    exact .id h1 ⟨u, hA.weak' WΓ⟩ (hat.weak' WΓ) (hbt.weak' WΓ)
  | refl h1 => exact .refl h1
  | tr hle _ ha _ _ hslotv _ hcb hslotc hH heq hAt hat hbt ihX iha ihb ihA ihC =>
    have hm' := hslotc.1.forget
    rw [← subst_lift', ← subst_lift', ← subst_lift'] at heq
    simp only [← subst_lift'] at hslotv
    obtain ⟨u, hA⟩ := hAt
    refine .tr hle (ihX hΓ WΓ hρ rfl) (iha hΓ WΓ hρ rfl) (ihb hΓ WΓ hρ rfl) (ihA hΓ WΓ hρ rfl)
      hslotv ?_ hcb ?_ (fun hr => ?_) heq ⟨u, hA.weak' WΓ⟩ (hat.weak' WΓ) (hbt.weak' WΓ)
    · refine ihC ⟨hΓ, _, hA⟩ (l := l.cons) WΓ.cons (fun i => ?_) ?_
      · cases i <;> simp_all [Valuation.push]
      · rw [← Subst.lift_l_cons]
        exact congrArg _ subst_lift'
    · simpa only [subst_lift', Subst.lift_l_cons] using hslotc
    · simpa only [← subst_lift'] using hH hr

/-- Composing with a lifted substitution, under an extended stage. -/
theorem Subst.lift_comp_cons {θ σ : Subst} {e : Term} :
    θ.lift.comp (σ.cons e) = (θ.comp σ).cons e := by
  funext i; cases i with | zero => rfl | succ i => exact lift_subst_cons

/-- **Substitution in the term, the constructive direction.**  An
approximant of `t` at the composed stage, under a valuation whose slots
approximate the `θ i`, is an approximant of `t[θ]`.  Master's
`LE_Interp.subst` in the direction that needs no directedness: every
clause is rebuilt verbatim, with `subst_subst` for the labels and
`Interp.weak'` for the slot a binder adds. -/
theorem Interp.of_substTerm {Δ Γ : List Term} {t : Term} {τ ρ' m} (hΔ : ⊢ Δ)
    (H : Interp Δ Γ t τ ρ' m) {Γ' : List Term} {θ σ ρ} (hΓ' : ⊢ Γ')
    (Wθ : Ctx.SubstEq Γ' θ θ Γ) (hτ : τ = θ.comp σ)
    (hθ : ∀ {{i A'}}, Lookup Γ i A' → Interp Δ Γ' (θ i) σ ρ (ρ' i)) :
    Interp Δ Γ' (t.subst θ) σ ρ m := by
  induction H generalizing Γ' θ σ ρ with
  | bot => exact .bot
  | bvar hlk h1 => exact (hθ hlk).mono hΔ h1
  | sort h1 => exact .sort h1
  | unit h1 => exact .unit h1
  | nat h1 => exact .nat h1
  | zero h1 => exact .zero h1
  | succ _ h1 ihv => exact .succ (ihv hΓ' Wθ hτ hθ) h1
  | app _ _ hev h1 hty ihF iha =>
    subst hτ
    rw [← subst_subst] at hev
    exact .app (ihF hΓ' Wθ rfl hθ) (iha hΓ' Wθ rfl hθ) hev h1 (hty.substTerm Wθ)
  | @lam _ _ _ _ _ _ _ A _ hA hd hwf hNV hbody h1 hAt ihA ihbody =>
    subst hτ
    rw [← subst_subst] at hwf h1
    obtain ⟨u, hAty⟩ := hAt
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : .sort u := hAty.subst hΓ' Wθ
    refine .lam (ihA hΓ' Wθ rfl hθ) hd hwf hNV (fun e he => ?_) h1 ⟨u, hAθ⟩
    refine ihbody e he ⟨hΓ', _, hAθ⟩ (Wθ.lift hAty hAθ) Subst.lift_comp_cons.symm
      (fun {_ _} hlk => ?_)
    cases hlk with
    | zero => exact .bvar .zero (.refl (hwf.2.2.1.1 e he).2.2.1)
    | succ hlk => exact weak' (l := .skip .refl) hΓ' (hθ hlk) (.skip .refl) (fun _ => rfl)
  | @forallE _ _ _ _ _ _ _ A B hA hd hwf hNV hbody h1 hAt hBt ihA ihbody =>
    subst hτ
    rw [Subst.comp_lift, ← subst_subst, ← subst_subst] at hwf h1
    obtain ⟨u, hAty⟩ := hAt
    obtain ⟨v, hBty⟩ := hBt
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : .sort u := hAty.subst hΓ' Wθ
    have hΓ'A : ⊢ (A.subst θ :: Γ') := ⟨hΓ', _, hAθ⟩
    refine .forallE (ihA hΓ' Wθ rfl hθ) hd hwf hNV (fun e he => ?_) h1
      ⟨u, hAθ⟩ ⟨v, hBty.subst hΓ'A (Wθ.lift hAty hAθ)⟩
    refine ihbody e he hΓ'A (Wθ.lift hAty hAθ) Subst.lift_comp_cons.symm (fun {_ _} hlk => ?_)
    cases hlk with
    | zero => exact .bvar .zero (.refl (hwf.2.2.2.1.1 e he).2.2.1)
    | succ hlk => exact weak' (l := .skip .refl) hΓ' (hθ hlk) (.skip .refl) (fun _ => rfl)
  | @sigma _ _ _ _ _ _ _ A B hA hd hwf hNV hbody h1 hAt hBt ihA ihbody =>
    subst hτ
    rw [Subst.comp_lift, ← subst_subst, ← subst_subst] at hwf h1
    obtain ⟨u, hAty⟩ := hAt
    obtain ⟨v, hBty⟩ := hBt
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : .sort u := hAty.subst hΓ' Wθ
    have hΓ'A : ⊢ (A.subst θ :: Γ') := ⟨hΓ', _, hAθ⟩
    refine .sigma (ihA hΓ' Wθ rfl hθ) hd hwf hNV (fun e he => ?_) h1
      ⟨u, hAθ⟩ ⟨v, hBty.subst hΓ'A (Wθ.lift hAty hAθ)⟩
    refine ihbody e he hΓ'A (Wθ.lift hAty hAθ) Subst.lift_comp_cons.symm (fun {_ _} hlk => ?_)
    cases hlk with
    | zero => exact .bvar .zero (.refl (hwf.2.2.2.1.1 e he).2.2.1)
    | succ hlk => exact weak' (l := .skip .refl) hΓ' (hθ hlk) (.skip .refl) (fun _ => rfl)
  | pair _ _ _ hd hslot hwf _ hcty h1 hAt hat iha ihb ihA ihcode =>
    subst hτ
    rw [← subst_subst] at hwf h1
    simp only [← subst_subst] at hslot
    obtain ⟨u, hAty⟩ := hAt
    have hAθ := hAty.subst hΓ' Wθ
    refine .pair (iha hΓ' Wθ rfl hθ) (ihb hΓ' Wθ rfl hθ) (ihA hΓ' Wθ rfl hθ) hd hslot ?_ ?_ hcty
      ?_ ⟨u, hAθ⟩ (hat.subst hΓ' Wθ)
    · simpa [← subst_subst] using hwf
    · refine ihcode ⟨hΓ', _, hAθ⟩ (Wθ.lift hAty hAθ) ?_ (fun {_ _} hlk => ?_)
      · rw [← subst_subst]; exact Subst.lift_comp_cons.symm
      cases hlk with
      | zero => exact .bvar .zero (.refl (TShape.WF.T.2 hwf.2.2.2.1))
      | succ hlk => exact weak' (l := .skip .refl) hΓ' (hθ hlk) (.skip .refl) (fun _ => rfl)
    · simpa [← subst_subst] using h1
  | fst _ h1 ihp => exact .fst (ihp hΓ' Wθ hτ hθ) h1
  | snd _ hlab h1 hty ihp =>
    subst hτ
    rw [← subst_subst] at hlab
    exact .snd (ihp hΓ' Wθ rfl hθ) hlab h1 (by simpa using hty.substTerm Wθ)
  | natCase_zero _ hz _ hMt ihM iha =>
    subst hτ
    rw [← subst_subst] at hz
    exact .natCase_zero (ihM hΓ' Wθ rfl hθ) hz (iha hΓ' Wθ rfl hθ) (by simpa using hMt.subst hΓ' Wθ)
  | natCase_succ hM heq _ hMt ihM ihb =>
    subst hτ
    rw [← subst_subst] at heq
    refine .natCase_succ (ihM hΓ' Wθ rfl hθ) heq ?_ (by simpa using hMt.subst hΓ' Wθ)
    refine ihb (θ := θ.lift) ⟨hΓ', _, (.nat : Γ' ⊢ .nat : .type)⟩
      (by simpa using Wθ.lift .nat .nat) Subst.lift_comp_cons.symm (fun {_ _} hlk => ?_)
    cases hlk with
    | zero => exact .bvar .zero (.refl (TShape.WF.T.2 hM.wf))
    | succ hlk => exact weak' (l := .skip .refl) hΓ' (hθ hlk) (.skip .refl) (fun _ => rfl)
  | @Y _ _ _ _ A b _ _ _ _ hdty hslot _ hAt hYt ihself ihA ihb =>
    subst hτ
    simp only [← subst_subst] at hslot
    obtain ⟨u, hAty⟩ := hAt
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : .sort u := hAty.subst hΓ' Wθ
    refine .Y (ihself hΓ' Wθ rfl hθ) (ihA hΓ' Wθ rfl hθ) hdty hslot ?_ ⟨u, hAθ⟩
      (by simpa using hYt.subst hΓ' Wθ)
    simp only [Term.subst, subst_subst, ← Subst.comp_lift]
    refine ihb ⟨hΓ', _, hAθ⟩ (Wθ.lift hAty hAθ) Subst.lift_comp_cons.symm (fun {_ _} hlk => ?_)
    cases hlk with
    | zero => exact .bvar .zero (.refl hslot.1.wf.forget)
    | succ hlk => exact weak' (l := .skip .refl) hΓ' (hθ hlk) (.skip .refl) (fun _ => rfl)
  | id h1 hAt hat hbt =>
    subst hτ
    simp only [← subst_subst] at h1
    obtain ⟨u, hAty⟩ := hAt
    exact .id h1 ⟨u, hAty.subst hΓ' Wθ⟩ (hat.subst hΓ' Wθ) (hbt.subst hΓ' Wθ)
  | refl h1 => exact .refl h1
  | @tr _ _ _ _ _ _ _ _ _ A _ _ _ _ _ hle _ _ _ _ hslotv _ hcb hslotc hH heq hAt hat hbt
      ihX iha ihb ihA ihC =>
    have hm' := hslotc.1.forget
    subst hτ
    rw [← subst_subst, ← subst_subst, ← subst_subst] at heq
    simp only [← subst_subst] at hslotv
    obtain ⟨u, hAty⟩ := hAt
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : .sort u := hAty.subst hΓ' Wθ
    refine .tr hle (ihX hΓ' Wθ rfl hθ) (iha hΓ' Wθ rfl hθ) (ihb hΓ' Wθ rfl hθ) (ihA hΓ' Wθ rfl hθ)
      hslotv ?_ hcb ?_ (fun hr => ?_) heq ⟨u, hAθ⟩ (hat.subst hΓ' Wθ) (hbt.subst hΓ' Wθ)
    · rw [subst_subst]
      refine ihC ⟨hΓ', _, hAθ⟩ (Wθ.lift hAty hAθ) Subst.lift_comp_cons.symm (fun {_ _} hlk => ?_)
      cases hlk with
      | zero => exact .bvar .zero (.refl hslotv.1.wf.forget)
      | succ hlk => exact weak' (l := .skip .refl) hΓ' (hθ hlk) (.skip .refl) (fun _ => rfl)
    · simpa only [subst_subst, Subst.lift_comp_cons] using hslotc
    · simpa only [← subst_subst] using hH hr

/-- **Strengthening along a renaming**, the direction `Interp.weak'` does
not give.  With the labels' typings in the clauses this is no longer a
statement about raw terms: moving an interpretation into a *smaller*
context means moving its typings there, and the syntax has weakening but
not strengthening.  So the lemma is indexed by a typing of the term in
the small context, and the induction runs on that — the same shape as
`IsDefEq.stage`, and for the same reason.

Master proves the raw version by casing on the term at each step; here
each case of the *typing* supplies the premises the clause needs. -/
theorem Interp.unweak {Δ : List Term} (hΔ : ⊢ Δ) {t : Term} {Γ Γ' : List Term} {l σ' ρ ρ' m T}
    (hΓ : ⊢ Γ) (hAnn : Γ ⊢ t : T) (WΓ : Ctx.Lift' l Γ Γ') (hd : Ctx.SubstEq Δ σ' σ' Γ')
    (hρ : ∀ i, ρ i = ρ' (l.liftVar i)) (H : Interp Δ Γ' (t.lift' l) σ' ρ' m) :
    Interp Δ Γ t (σ'.lift_l l) ρ m := by
  induction t generalizing Γ Γ' l σ' ρ ρ' m T with
  | bvar i =>
    cases H with | bot => exact .bot | bvar _ hle
    obtain ⟨_, hlk⟩ := hAnn.bvar_regular (.inl rfl)
    exact .bvar hlk (hρ _ ▸ hle)
  | sort u => cases H with | bot => exact .bot | sort hle => exact .sort hle
  | unit r => cases H with | bot => exact .bot | unit hle => exact .unit hle
  | star r => cases H with | bot => exact .bot
  | nat => cases H with | bot => exact .bot | nat hle => exact .nat hle
  | zero => cases H with | bot => exact .bot | zero hle => exact .zero hle
  | succ N ih =>
    cases H with | bot => exact .bot | succ hv hle
    exact .succ (ih hΓ (hAnn.succ_regular (.inl rfl)) WΓ hd hρ hv) hle
  | app F a ihF iha =>
    obtain ⟨⟨_, _, hAF⟩, _, hAa⟩ := hAnn.app_regular (.inl rfl)
    cases H with | bot => exact .bot | app hF hx hev hle hty
    rw [subst_lift'] at hev
    exact .app (ihF hΓ hAF WΓ hd hρ hF) (iha hΓ hAa WΓ hd hρ hx) hev hle (hty.unweak WΓ hd)
  | lam A b ihA ihb =>
    obtain ⟨⟨u, hA⟩, _, hAb⟩ := hAnn.lam_regular (.inl rfl)
    have hAA := hA
    cases H with | bot => exact .bot | lam hAint hdty hwf hNV hbody hle
    simp only [subst_lift'] at hwf hle
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
    refine .lam (ihA hΓ hAA WΓ hd hρ hAint) hdty hwf hNV (fun e he => ?_) hle ⟨u, hA⟩
    have htm : Δ ⊢ e.tm : (A.lift' l).subst σ' := by
      rw [subst_lift']
      exact (hwf.2.2.1.1 e he).2.1
    have hd' : Ctx.SubstEq Δ (σ'.cons e.tm) (σ'.cons e.tm) (A.lift' l :: Γ') :=
      .cons hd (hA.weak' WΓ) htm
    rw [Subst.lift_l_cons]
    exact ihb hΓA hAb WΓ.cons hd' (fun i => by cases i <;> simp_all [Valuation.push]) (hbody e he)
  | forallE A B ihA ihB =>
    obtain ⟨⟨u, hA⟩, v, hB⟩ := hAnn.forallE_regular (.inl rfl)
    have hAA := hA
    have hAB := hB
    cases H with | bot => exact .bot | forallE hAint hdty hwf hNV hbody hle
    simp only [subst_lift', ← Subst.lift_l_lift] at hwf hle
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
    refine .forallE (ihA hΓ hAA WΓ hd hρ hAint) hdty hwf hNV (fun e he => ?_) hle
      ⟨u, hA⟩ ⟨v, hB⟩
    have htm : Δ ⊢ e.tm : (A.lift' l).subst σ' := by
      have := (hwf.2.2.2.1.1 e he).2.1
      first | exact this | (rw [subst_lift']; exact this)
    have hd' : Ctx.SubstEq Δ (σ'.cons e.tm) (σ'.cons e.tm) (A.lift' l :: Γ') :=
      .cons hd (hA.weak' WΓ) htm
    rw [Subst.lift_l_cons]
    exact ihB hΓA hAB WΓ.cons hd' (fun i => by cases i <;> simp_all [Valuation.push]) (hbody e he)
  | sigma A B ihA ihB =>
    obtain ⟨⟨u, hA⟩, v, hB⟩ := hAnn.sigma_regular (.inl rfl)
    have hAA := hA
    have hAB := hB
    cases H with | bot => exact .bot | sigma hAint hdty hwf hNV hbody hle
    simp only [subst_lift', ← Subst.lift_l_lift] at hwf hle
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
    refine .sigma (ihA hΓ hAA WΓ hd hρ hAint) hdty hwf hNV (fun e he => ?_) hle
      ⟨u, hA⟩ ⟨v, hB⟩
    have htm : Δ ⊢ e.tm : (A.lift' l).subst σ' := by
      have := (hwf.2.2.2.1.1 e he).2.1
      first | exact this | (rw [subst_lift']; exact this)
    have hd' : Ctx.SubstEq Δ (σ'.cons e.tm) (σ'.cons e.tm) (A.lift' l :: Γ') :=
      .cons hd (hA.weak' WΓ) htm
    rw [Subst.lift_l_cons]
    exact ihB hΓA hAB WΓ.cons hd' (fun i => by cases i <;> simp_all [Valuation.push]) (hbody e he)
  | pair A B a b ihA ihB iha ihb =>
    obtain ⟨⟨u, hA⟩, ⟨_, hAB⟩, hat, _, hAb⟩ := hAnn.pair_regular (.inl rfl)
    have hAA := hA
    have hAa := hat
    cases H with | bot => exact .bot | pair hainp hbout hAint hdty hslot hwf hcode hcty hle
    simp only [subst_lift'] at hwf hle hslot
    refine .pair (iha hΓ hAa WΓ hd hρ hainp) (ihb hΓ hAb WΓ hd hρ hbout)
      (ihA hΓ hAA WΓ hd hρ hAint) hdty hslot hwf ?_ hcty hle ⟨u, hA⟩ hat
    have htm : Δ ⊢ (a.lift' l).subst σ' : (A.lift' l).subst σ' :=
      (hat.weak' WΓ).subst hΔ hd
    have hd' : Ctx.SubstEq Δ (σ'.cons ((a.lift' l).subst σ'))
        (σ'.cons ((a.lift' l).subst σ')) (A.lift' l :: Γ') :=
      .cons hd (hA.weak' WΓ) htm
    rw [Subst.lift_l_cons, ← subst_lift']
    exact ihB ⟨hΓ, _, hA⟩ hAB WΓ.cons hd' (fun i => by cases i <;> simp_all [Valuation.push]) hcode
  | fst p ih =>
    cases H with | bot => exact .bot | fst hp hle
    obtain ⟨_, _, hAp⟩ := hAnn.fst_regular (.inl rfl)
    exact .fst (ih hΓ hAp WΓ hd hρ hp) hle
  | snd p ih =>
    cases H with | bot => exact .bot | snd hp hev hle hty
    simp only [Term.subst, subst_lift'] at hev
    obtain ⟨_, _, hAp⟩ := hAnn.snd_regular (.inl rfl)
    exact .snd (ih hΓ hAp WΓ hd hρ hp) hev hle (Stable.unweak (a := .fst p) WΓ hd hty)
  | natCase C M a b ihC ihM iha ihb =>
    obtain ⟨hMt, ⟨_, hAa⟩, _, hAb⟩ := hAnn.natCase_regular (.inl rfl)
    have hAM := hMt
    cases H with
    | bot => exact .bot
    | natCase_zero hM hz ha =>
      rw [subst_lift'] at hz
      exact .natCase_zero (ihM hΓ hAM WΓ hd hρ hM) hz (iha hΓ hAa WΓ hd hρ ha) hMt
    | natCase_succ hM heq hbody
    rw [subst_lift'] at heq
    refine .natCase_succ (ihM hΓ hAM WΓ hd hρ hM) heq ?_ hMt
    have hd' : Ctx.SubstEq Δ (σ'.cons _) (σ'.cons _) (.nat :: Γ') :=
      .cons hd .nat (heq.succ_regular (.inr rfl))
    rw [Subst.lift_l_cons]
    refine ihb ⟨hΓ, _, .nat⟩ hAb (by simpa using WΓ.cons (A := Term.nat)) hd'
      (fun i => ?_) (by simpa using hbody)
    cases i with | zero => rfl | succ i => simp [Valuation.push, hρ i]
  | Y A b ihA ihb =>
    obtain ⟨⟨u, hA⟩, hYt, _, hAb⟩ := hAnn.Y_regular (.inl rfl)
    have hAA := hA
    -- the tower is not structural in the term, so this one case runs on
    -- the derivation: each level's self-premise is the level below
    have key {Γ₂ : List Term} {t' σ₂ ρ₂ m} (H : Interp Δ Γ₂ t' σ₂ ρ₂ m) {l ρ}
        (ht' : t' = (Term.Y A b).lift' l) (WΓ : Ctx.Lift' l Γ Γ₂)
        (hd : Ctx.SubstEq Δ σ₂ σ₂ Γ₂) (hρ : ∀ i, ρ i = ρ₂ (l.liftVar i)) :
        Interp Δ Γ (.Y A b) (σ₂.lift_l l) ρ m := by
      induction H with
      | bot => exact .bot
      | @Y Γ₂ σ₂ ρ₂ m A₂ b₂ x d hx hAd hdty hslot hbody _ _ ihx => ?_
      | _ => simp at ht'
      cases ht'
      have hYsub : ((A.lift' l).Y (b.lift' l.cons)).subst σ₂
          = (Term.Y A b).subst (σ₂.lift_l l) := subst_lift' (e := .Y A b)
      have hd' : Ctx.SubstEq Δ (σ₂.cons ((Term.Y A b).subst (σ₂.lift_l l)))
          (σ₂.cons ((Term.Y A b).subst (σ₂.lift_l l))) (A.lift' l :: Γ₂) :=
        .cons hd (hA.weak' WΓ) (hYsub ▸ IsDefEq.subst hΔ hd (hYt.weak' WΓ))
      refine .Y (ihx rfl WΓ hd hρ) (ihA hΓ hAA WΓ hd hρ hAd) hdty ?_ ?_ ⟨u, hA⟩ hYt
      · simpa only [subst_lift', ← hYsub] using hslot
      rw [Subst.lift_l_cons]
      refine ihb ⟨hΓ, _, hA⟩ hAb WΓ.cons hd' (fun i => ?_) (hYsub ▸ hbody)
      cases i with | zero => rfl | succ i => simp [Valuation.push, hρ i]
    exact key H rfl WΓ hd hρ
  | id r A a b ihA iha ihb =>
    obtain ⟨⟨u, hA⟩, hat, hbt⟩ := hAnn.id_regular (.inl rfl)
    cases H with | bot => exact .bot | id hle
    simp only [subst_lift'] at hle
    exact .id hle ⟨u, hA⟩ hat hbt
  | refl r a ih => cases H with | bot => exact .bot | refl hle => exact .refl hle
  | tr r A a b C X Hp ihA iha ihb ihC ihX ihH =>
    obtain ⟨⟨u, hA⟩, hat, hbt, hht, ⟨a₀, C₀, v₀, hx₀, ha₀, hC₀⟩, _, hAC⟩ :=
      hAnn.tr_regular (.inl rfl)
    have hAA := hA
    have hAa := hat
    have hAb := hbt
    have hAX := hx₀
    cases H with | bot => exact .bot | tr hle hX ha hb hAint hslotv hC hcb hslotc hH heq
    have hm' := hslotc.1.forget
    simp only [subst_lift'] at heq hslotv hslotc
    have hd' : Ctx.SubstEq Δ (σ'.cons (b.subst (σ'.lift_l l)))
        (σ'.cons (b.subst (σ'.lift_l l))) (A.lift' l :: Γ') :=
      .cons hd (hA.weak' WΓ) (by simpa [subst_lift'] using (hbt.weak' WΓ).subst hΔ hd)
    refine .tr hle (ihX hΓ hAX WΓ hd hρ hX) (iha hΓ hAa WΓ hd hρ ha) (ihb hΓ hAb WΓ hd hρ hb)
      (ihA hΓ hAA WΓ hd hρ hAint) hslotv ?_ hcb ?_ (fun hr => ?_) heq ⟨u, hA⟩ hat hbt
    · rw [Subst.lift_l_cons]
      refine ihC ⟨hΓ, _, hA⟩ hAC WΓ.cons hd' (fun i => ?_) (by simpa [subst_lift'] using hC)
      cases i with | zero => rfl | succ i => simp [Valuation.push, hρ i]
    · simpa only [Subst.lift_l_cons] using hslotc
    · simpa only [subst_lift'] using hH hr

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
  exact ⟨v, hAσ.instDF hΔ .sort hC1 ((ha₀.subst hΔ W).trans heq)⟩

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

So the induction is structural in the term, with the subject's typing
inverted a layer at a time (`Regular.lean`) for the annotations.  `Y` is the one case that is not structural: its tower
premise is the same term one level down, so that case runs on the
derivation. -/
theorem Interp.stage {Δ : List Term} (hΔ : ⊢ Δ) {t : Term} {Γ : List Term} {σ σ₂ ρ m T}
    (hΓ : ⊢ Γ) (hAnn : Γ ⊢ t : T) (W : Ctx.SubstEq Δ σ σ₂ Γ) (H : Interp Δ Γ t σ ρ m) :
    Interp Δ Γ t σ₂ ρ m := by
  induction t generalizing Γ σ σ₂ ρ m T with
  | bvar i => cases H with | bot => exact .bot | bvar hlk hle => exact .bvar hlk hle
  | sort u => cases H with | bot => exact .bot | sort hle => exact .sort hle
  | unit r => cases H with | bot => exact .bot | unit hle => exact .unit hle
  | star r => cases H with | bot => exact .bot
  | nat => cases H with | bot => exact .bot | nat hle => exact .nat hle
  | zero => cases H with | bot => exact .bot | zero hle => exact .zero hle
  | succ N ih =>
    cases H with | bot => exact .bot | succ hv hle
    exact .succ (ih hΓ (hAnn.succ_regular (.inl rfl)) W hv) hle
  | app F a ihF iha =>
    obtain ⟨⟨_, _, hAF⟩, _, hAa⟩ := hAnn.app_regular (.inl rfl)
    cases H with | bot => exact .bot | app hF hx hev hle hty
    have heq := hty.move hΔ W
    refine .app (ihF hΓ hAF W hF) (iha hΓ hAa W hx) ?_ hle (hty.stage W)
    exact hev.mono hΔ ⟨heq.hasType.1.isType hΔ, heq⟩ (.refl hx.wf)
  | lam A b ihA ihb =>
    obtain ⟨⟨u, hA⟩, _, hAb⟩ := hAnn.lam_regular (.inl rfl)
    have hAA := hA
    have hAσ : TyEq Δ (A.subst σ) (A.subst σ₂) := ⟨u, hA.subst' hΔ W⟩
    cases H with | bot => exact .bot | @lam _ _ _ _ _ _ _ _ _ hAint hdty hwf hNV hbody hle _
    refine .lam (ihA hΓ hAA W hAint) hdty ⟨hwf.1, hwf.2.1, hwf.2.2.1.retype hAσ, hAσ.refl_r⟩ hNV
      (fun e he => ?_) ?_ ⟨u, hA⟩
    · have W' : Ctx.SubstEq Δ (σ.cons e.tm) (σ₂.cons e.tm) (A :: Γ) :=
        .cons W hA (hwf.2.2.1.1 e he).2.1
      exact ihb ⟨hΓ, _, hA⟩ hAb W' (hbody e he)
    exact hle.trans hΔ (TShape.LE.T.2 ⟨.refl hwf.2.2.1, hwf.1, hwf.2.1, hAσ, hwf.2.2.2⟩)
  | forallE A B ihA ihB =>
    obtain ⟨⟨u, hA⟩, v, hB⟩ := hAnn.forallE_regular (.inl rfl)
    have hAA := hA
    have hAB := hB
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
    have hAσ : Δ ⊢ A.subst σ ≡ A.subst σ₂ : .sort u := hA.subst' hΔ W
    have hBσ : A.subst σ :: Δ ⊢ B.subst σ.lift ≡ B.subst σ₂.lift : .sort v :=
      hB.subst' (Γ₀ := A.subst σ :: Δ) ⟨hΔ, _, hAσ.hasType.1⟩ (W.lift hA hAσ.hasType.1)
    cases H with | bot => exact .bot | forallE hAint hdty hwf hNV hbody hle
    refine .forallE (ihA hΓ hAA W hAint) hdty ?_ hNV (fun e he => ?_) ?_ ⟨u, hA⟩ ⟨v, hB⟩
    · refine ⟨⟨u, hAσ.hasType.2⟩, ⟨v, (hAσ.defeqDF_l hΔ hBσ).hasType.2⟩, ?_, ?_, trivial⟩
      · exact hwf.2.2.1.conv ⟨u, hAσ.symm⟩
      refine (hwf.2.2.2.1.forget.retype ⟨u, hAσ⟩).name fun e he => ?_
      refine (hwf.2.2.2.1.canon e he).conv ⟨v, ?_⟩
      exact hAσ.hasType.2.instDF hΔ .sort (hAσ.defeqDF_l hΔ hBσ).symm
        (hAσ.defeqDF (hwf.2.2.2.1.1 e he).2.1)
    · have W' : Ctx.SubstEq Δ (σ.cons e.tm) (σ₂.cons e.tm) (A :: Γ) :=
        .cons W hA (hwf.2.2.2.1.1 e he).2.1
      exact ihB hΓA hAB W' (hbody e he)
    exact hle.trans hΔ (TShape.LE.T.2 ⟨⟨⟨u, hAσ⟩, v, hBσ⟩, .refl hwf.2.2.1.forget,
      .refl hwf.2.2.2.1.forget, hwf.2.2.1, hwf.2.2.2.1.canon⟩)
  | sigma A B ihA ihB =>
    obtain ⟨⟨u, hA⟩, v, hB⟩ := hAnn.sigma_regular (.inl rfl)
    have hAA := hA
    have hAB := hB
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
    have hAσ : Δ ⊢ A.subst σ ≡ A.subst σ₂ : .sort u := hA.subst' hΔ W
    have hBσ : A.subst σ :: Δ ⊢ B.subst σ.lift ≡ B.subst σ₂.lift : .sort v :=
      hB.subst' (Γ₀ := A.subst σ :: Δ) ⟨hΔ, _, hAσ.hasType.1⟩ (W.lift hA hAσ.hasType.1)
    cases H with | bot => exact .bot | sigma hAint hdty hwf hNV hbody hle
    refine .sigma (ihA hΓ hAA W hAint) hdty ?_ hNV (fun e he => ?_) ?_ ⟨u, hA⟩ ⟨v, hB⟩
    · refine ⟨⟨u, hAσ.hasType.2⟩, ⟨v, (hAσ.defeqDF_l hΔ hBσ).hasType.2⟩, ?_, ?_, trivial⟩
      · exact hwf.2.2.1.conv ⟨u, hAσ.symm⟩
      refine (hwf.2.2.2.1.forget.retype ⟨u, hAσ⟩).name fun e he => ?_
      refine (hwf.2.2.2.1.canon e he).conv ⟨v, ?_⟩
      exact hAσ.hasType.2.instDF hΔ .sort (hAσ.defeqDF_l hΔ hBσ).symm
        (hAσ.defeqDF (hwf.2.2.2.1.1 e he).2.1)
    · have W' : Ctx.SubstEq Δ (σ.cons e.tm) (σ₂.cons e.tm) (A :: Γ) :=
        .cons W hA (hwf.2.2.2.1.1 e he).2.1
      exact ihB hΓA hAB W' (hbody e he)
    exact hle.trans hΔ (TShape.LE.T.2 ⟨⟨⟨u, hAσ⟩, v, hBσ⟩, .refl hwf.2.2.1.forget,
      .refl hwf.2.2.2.1.forget, hwf.2.2.1, hwf.2.2.2.1.canon⟩)
  | pair A B a b ihA ihB iha ihb =>
    obtain ⟨⟨u, hA⟩, ⟨_, hAB⟩, hat, _, hAb⟩ := hAnn.pair_regular (.inl rfl)
    have hAA := hA
    have hAa := hat
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
    have hAσ : TyEq Δ (A.subst σ) (A.subst σ₂) := ⟨u, hA.subst' hΔ W⟩
    have haσ : Δ ⊢ a.subst σ ≡ a.subst σ₂ : A.subst σ := hat.subst' hΔ W
    cases H with
    | bot => exact .bot
    | @pair _ _ _ _ _ _ _ _ _ _ _ _ _ hainp hbout hAint hdty hslot hwf hcode hcty hle
    have hwf' := show Shape.WF (n := _+1) Δ (.pair (A.subst σ₂) (a.subst σ₂) ..) from
      ⟨hwf.1, hAσ.defeqDF (haσ.symm.trans haσ), hAσ.refl_r, hwf.2.2.2.1, hwf.2.2.2.2⟩
    have hle'₀ := show Shape.LE (n := _+1) Δ (.pair (A.subst σ) (a.subst σ) ..)
        (.pair (A.subst σ₂) (a.subst σ₂) ..) from
      ⟨.refl hwf.2.2.2.1, .refl hwf.2.2.2.2, hwf.1, hAσ, haσ⟩
    have hle' := TShape.LE.T.2 hle'₀
    have W' : Ctx.SubstEq Δ (σ.cons (a.subst σ)) (σ₂.cons (a.subst σ₂)) (A :: Γ) :=
      .cons W hA haσ
    exact .pair (iha hΓ hAa W hainp) (ihb hΓ hAb W hbout) (ihA hΓ hAA W hAint) hdty
      ((hslot.defeq hΔ haσ).conv hAσ.symm) hwf' (ihB hΓA hAB W' hcode) hcty
      (hle.trans hΔ hle') ⟨u, hA⟩ hat
  | fst p ih =>
    cases H with | bot => exact .bot | fst hp hle
    obtain ⟨_, _, hAp⟩ := hAnn.fst_regular (.inl rfl)
    exact .fst (ih hΓ hAp W hp) hle
  | snd p ih =>
    cases H with | bot => exact .bot | snd hp hlab hle hty
    have heq := hty.move hΔ W
    obtain ⟨_, _, hAp⟩ := hAnn.snd_regular (.inl rfl)
    exact .snd (ih hΓ hAp W hp) (hlab.trans heq) hle (hty.stage W)
  | natCase C M a b ihC ihM iha ihb =>
    obtain ⟨hMt, ⟨_, hAa⟩, _, hAb⟩ := hAnn.natCase_regular (.inl rfl)
    have hAM := hMt
    have hΓN : ⊢ (.nat :: Γ) := ⟨hΓ, _, .nat⟩
    have hMσ : Δ ⊢ M.subst σ ≡ M.subst σ₂ : .nat := hMt.subst' hΔ W
    cases H with
    | bot => exact .bot
    | natCase_zero hM hz ha =>
      exact .natCase_zero (ihM hΓ hAM W hM) (hMσ.symm.trans hz) (iha hΓ hAa W ha) hMt
    | natCase_succ hM heq hbody
    refine .natCase_succ (ihM hΓ hAM W hM) (hMσ.symm.trans heq) ?_ hMt
    have W' : Ctx.SubstEq Δ (σ.cons _) (σ₂.cons _) (.nat :: Γ) :=
      .cons W .nat (heq.succ_regular (.inr rfl))
    exact ihb hΓN hAb W' hbody
  | Y A b ihA ihb =>
    -- the tower is not structural in the term, so this one case runs on
    -- the derivation: each level's self-premise is the level below
    have key {Γ₂ : List Term} {t' σ' ρ' m} (H : Interp Δ Γ₂ t' σ' ρ' m) {σ₃ TY}
        (ht' : t' = .Y A b) (hΓ₂ : ⊢ Γ₂) (hAnn₂ : Γ₂ ⊢ .Y A b : TY)
        (W₂ : Ctx.SubstEq Δ σ' σ₃ Γ₂) : Interp Δ Γ₂ (.Y A b) σ₃ ρ' m := by
      induction H generalizing TY with
      | bot => exact .bot
      | @Y Γ₂ σ' ρ' m A₂ b₂ x d hx hAd hdty hslot hbody _ _ ihx => ?_
      | _ => simp at ht'
      cases ht'
      obtain ⟨⟨u, hA⟩, hYt, _, hAb⟩ := hAnn₂.Y_regular (.inl rfl)
      have hAA := hA
      have hYσ : Δ ⊢ (Term.Y A b).subst σ' ≡ (Term.Y A b).subst σ₃ : A.subst σ' :=
        hYt.subst' hΔ W₂
      have W' : Ctx.SubstEq Δ (σ'.cons ((Term.Y A b).subst σ'))
          (σ₃.cons ((Term.Y A b).subst σ₃)) (A :: Γ₂) := .cons W₂ hA hYσ
      refine .Y (ihx rfl hΓ₂ hYt W₂) (ihA hΓ₂ hAA W₂ hAd) hdty ?_ (ihb ⟨hΓ₂, _, hA⟩ hAb W' hbody)
        ⟨u, hA⟩ hYt
      exact (hslot.defeq hΔ hYσ).conv (.symm ⟨u, hA.subst' hΔ W₂⟩)
    exact key H rfl hΓ hAnn W
  | id r A a b ihA iha ihb =>
    obtain ⟨⟨u, hA⟩, hat, hbt⟩ := hAnn.id_regular (.inl rfl)
    cases H with | bot => exact .bot | id hle
    refine .id (hle.trans hΔ (TShape.LE.T.2 ?_)) ⟨u, hA⟩ hat hbt
    exact ⟨rfl, ⟨u, hA.subst' hΔ W⟩, hat.subst' hΔ W, hbt.subst' hΔ W⟩
  | refl r a ih => cases H with | bot => exact .bot | refl hle => exact .refl hle
  | tr r A a b C X Hp ihA iha ihb ihC ihX ihH =>
    obtain ⟨⟨u, hA⟩, hat, hbt, hht, ⟨a₀, C₀, v₀, hx₀, ha₀, hC₀⟩, _, hAC⟩ :=
      hAnn.tr_regular (.inl rfl)
    have hAA := hA
    have hAa := hat
    have hAb := hbt
    have hAX := hx₀
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
    have hbσ : Δ ⊢ b.subst σ ≡ b.subst σ₂ : A.subst σ := hbt.subst' hΔ W
    have haσ : Δ ⊢ a.subst σ ≡ a.subst σ₂ : A.subst σ := hat.subst' hΔ W
    have WC : Ctx.SubstEq Δ (σ.cons (b.subst σ)) (σ₂.cons (b.subst σ₂)) (A :: Γ) :=
      .cons W hA hbσ
    cases H with | bot => exact .bot | tr hle hX ha hb hAint hslotv hC hcb hslotc hH heq
    have hm' := hslotc.1.forget
    have hAσ : Δ ⊢ A.subst σ ≡ A.subst σ₂ : .sort u := hA.subst' hΔ W
    refine .tr hle (ihX hΓ hAX W hX) (iha hΓ hAa W ha) (ihb hΓ hAb W hb) (ihA hΓ hAA W hAint) ?_
      (ihC hΓA hAC WC hC) hcb ?_ (fun hr => ?_) ?_ ⟨u, hA⟩ hat hbt
    · exact (hslotv.defeq hΔ hbσ).conv (.symm ⟨u, hAσ⟩)
    · -- the two halves move along *different* equations here, so this one
      -- slot is rebuilt rather than transported
      refine ⟨?_, (hslotc.conv ⟨v₀, (hC₀.hasType.2.subst' hΔ WC).symm⟩).2⟩
      exact ((hslotc.conv (.tr_motive hΔ W.left hA ha₀ hC₀ heq)).defeq hΔ (hx₀.subst' hΔ W)).1
    · -- the proof's equation moves with the stage, retyped at the new one
      have hHσ := hht.subst' hΔ W
      have hId : Δ ⊢ .id true (A.subst σ) (a.subst σ) (b.subst σ) ≡
          .id true (A.subst σ₂) (a.subst σ₂) (b.subst σ₂) : .sort true :=
        .idDF hAσ haσ hbσ
      have hrefl : Δ ⊢ .refl true (a.subst σ) ≡ .refl true (a.subst σ₂) :
          .id true (A.subst σ) (a.subst σ) (b.subst σ) := by
        have hA1 := hAσ.hasType.1; have ha1 := haσ.hasType.1
        exact (IsDefEq.idDF hA1 ha1 heq).defeqDF
          (.reflDF hA1 haσ (IsDefEq.idDF (r := true) hA1 ha1 ha1))
      cases hr
      exact hId.defeqDF ((hHσ.symm.trans (hH rfl)).trans hrefl)
    have h1 : Δ ⊢ a.subst σ₂ ≡ b.subst σ₂ : A.subst σ := (haσ.symm.trans heq).trans hbσ
    exact (hA.subst' hΔ W).defeqDF h1

/-- Collect a per-element existential into a list of pairs. -/
theorem List.exists_pairs {α β : Type _} {P : α → β → Prop} {g : List α}
    (h : ∀ e ∈ g, ∃ c, P e c) :
    ∃ g₀ : List (α × β), g₀.map Prod.fst = g ∧ ∀ p ∈ g₀, P p.1 p.2 := by
  induction g with | nil => exact ⟨[], rfl, by simp⟩ | cons e g ih
  obtain ⟨c, hc⟩ := h e (by simp)
  obtain ⟨g₀, hmap, hall⟩ := ih (fun e' he' => h e' (by simp [he']))
  refine ⟨(e, c) :: g₀, by simp [hmap], fun p hp => ?_⟩
  match List.mem_cons.1 hp with
  | .inl h => exact h ▸ hc
  | .inr h => exact hall p h

/-! ### Merging valuations

The forward direction of term substitution reads one valuation out of
each subderivation and has to return a single one.  Valuations join
slotwise, and a slot's join is again an approximant of its `θ i` only by
that term's directedness — so the lemmas that do the merging live past
`IsDefEq.dir`, in `Sound.lean`, and only the two definitions they
merge are here. -/

def Valuation.join (ρ₁ ρ₂ : Valuation) : Valuation := fun i => (ρ₁ i).join (ρ₂ i)

/-- A valuation whose every slot approximates the corresponding `θ i`,
over the variables of `Γ` — the substitution's **source** — with the
approximants living in `Γ'`, its target.  The two contexts are separate
because that is the only way to say where the substitution ends: `θ` is
total, so it has junk past `Γ`, and `Ctx.SubstEq Γ' θ θ Γ` types exactly
the slots named here. -/
def Valuation.Approx (Δ Γ' Γ : List Term) (θ σ : Subst) (ρ ρ' : Valuation) : Prop :=
  ∀ {{i A}}, Lookup Γ i A → Interp Δ Γ' (θ i) σ ρ (ρ' i)

theorem Valuation.Approx.nil {Δ Γ' Γ : List Term} {θ σ ρ} :
    Approx Δ Γ' Γ θ σ ρ Valuation.nil := fun {_ _} _ => .bot

theorem Interp.tr_bot_of_ne {Δ Γ : List Term} {r : Bool} {A a b C X H : Term} {σ ρ m}
    (h : Interp Δ Γ (.tr r A a b C X H) σ ρ m)
    (hne : ¬ (Δ ⊢ a.subst σ ≡ b.subst σ : A.subst σ)) : m.2 = .bot := by
  cases h with
  | bot => rfl
  | tr _ _ _ _ _ _ _ _ _ _ heq => cases hne heq

/-- An approximant of a variable is below its slot. -/
theorem Interp.le_bvar {Δ Γ : List Term} {i σ ρ m}
    (H : Interp Δ Γ (.bvar i) σ ρ m) : m.LE Δ (ρ i) := by
  cases H with
  | bot => exact TShape.bot_le' rfl
  | bvar _ h => exact h

/-- Strengthening at one slot, which is all the merges need: the slot is
well-annotated, so `Interp.unweak` applies at `.skip .refl`. -/
theorem Interp.unweak_slot {Δ Γ' Γ'' : List Term} {s : Term} (hΔ : ⊢ Δ) (hΓ' : ⊢ Γ')
    (WΓ : Ctx.Lift' (.skip .refl) Γ' Γ'') {S : Term} (hs : Γ' ⊢ s : S)
    {σ e ρ x m} (hd : Ctx.SubstEq Δ (σ.cons e) (σ.cons e) Γ'')
    (H : Interp Δ Γ'' s.lift (σ.cons e) (ρ.push x) m) :
    Interp Δ Γ' s σ ρ m :=
  H.unweak hΔ hΓ' hs WΓ hd (fun _ => rfl)

/-- **Admissibility of a stage.**  The ambient context is well formed, the
stage is a typed substitution into it, the valuation is well formed, and
every variable's slot is an approximant of its type and a `Slot` at it —
hereditarily typed there, at a code that names the type, and named by the
variable it stands for.  The other repo's `SourceAdmissible`, plus the
naming his quotient makes unnecessary.

The last two conjuncts are what the model is for.  Dropping the naming
makes Σ's η false (see the witness in `design.md` §6), and dropping the
hereditary typing makes `Interp.lam`'s slot unusable.

The first two are bookkeeping that used to travel beside it: every
consumer of admissibility wanted `⊢ Δ` and the stage's typing too, so
they are fields rather than three premises in a row.  `Adm.ctx` and
`Adm.stage` read them back.  Slotwise well-formedness is *not* a field:
`Adm.wf` derives it from the slot's own hereditary typing. -/
def Adm (Δ Γ : List Term) (σ : Subst) (ρ : Valuation) : Prop :=
  (⊢ Δ) ∧ Ctx.SubstEq Δ σ σ Γ ∧
    ∀ {i A}, Lookup Γ i A → ∃ a, Interp Δ Γ A σ ρ a ∧ TShape.Slot Δ (A.subst σ) a (σ i) (ρ i)

theorem Adm.ctx {Δ Γ : List Term} {σ ρ} (h : Adm Δ Γ σ ρ) : ⊢ Δ := h.1

theorem Adm.stage {Δ Γ : List Term} {σ ρ} (h : Adm Δ Γ σ ρ) :
    Ctx.SubstEq Δ σ σ Γ := h.2.1

/-- The all-bottom valuation is admissible, for free.  This is the
hypothesis every inversion theorem is run under. -/
theorem Adm.bot {Δ Γ : List Term} {σ : Subst} (hΔ : ⊢ Δ)
    (W : Ctx.SubstEq Δ σ σ Γ) : Adm Δ Γ σ .nil :=
  ⟨hΔ, W, fun {_ _} _ => ⟨.bot, .bot, .bot (.bot_bot rfl), .bot_mem⟩⟩

theorem Adm.lookupCanon {Δ Γ : List Term} {σ ρ} (h : Adm Δ Γ σ ρ) :
    ∀ {i A}, Lookup Γ i A →
      ∃ a, Interp Δ Γ A σ ρ a ∧ a.Slot Δ (A.subst σ) (σ i) (ρ i) := h.2.2

/-- Admissible valuations are well formed, slotwise.  Not a field: the
slot's own hereditary typing is well-formedness at the name, and
forgetting the name leaves exactly this. -/
theorem Adm.wf {Δ Γ : List Term} {σ ρ} (h : Adm Δ Γ σ ρ) : ρ.WF Δ Γ :=
  fun {_ _} hlk =>
    match h.lookupCanon hlk with
    | ⟨_, _, hn, _⟩ => hn.wf.forget

/-- Weakening the stage by one slot: `A` at `σ.tail` under `ρ` is
`A.lift` at `σ` under `ρ.push x`.  `Interp.weak'` at `Lift.refl.skip`. -/
theorem Interp.weak_one {Δ Γ Γ' : List Term} {A : Term} {σ ρ x m} (hΓ : ⊢ Γ)
    (WΓ : Ctx.Lift' Lift.refl.skip Γ Γ')
    (H : Interp Δ Γ A σ.tail ρ m) : Interp Δ Γ' A.lift σ (ρ.push x) m :=
  weak' (l := Lift.refl.skip) hΓ (Subst.tail_eq_lift_l ▸ H) WΓ (fun _ => rfl)

/-- Extending an admissible valuation by a typed slot: the old `cons`
constructor, now a lemma.  It asks for `⊢ Γ`, since the slots below are
re-read one binder up (`Interp.weak_one`).  It does *not* ask that the
type's approximants be types: `Adm` has no clause that would read it. -/
theorem Adm.cons {Δ Γ : List Term} {A : Term} {σ ρ x a} (h : Adm Δ Γ σ.tail ρ)
    (W : Ctx.SubstEq Δ σ σ (A :: Γ))
    (hΓ : ⊢ Γ) (ha : Interp Δ Γ A σ.tail ρ a)
    (hslot : a.Slot Δ (A.subst σ.tail) (σ 0) x) :
    Adm Δ (A :: Γ) σ (ρ.push x) := by
  refine ⟨h.ctx, W, fun {i A'} hl => ?_⟩
  cases hl with
  | zero =>
    refine ⟨a, ha.weak_one hΓ (.skip .refl), hslot.1, ?_⟩
    have h2 := hslot.2; rwa [lift_subst]
  | succ hl =>
    obtain ⟨b, hb, hn, hbc⟩ := h.lookupCanon hl
    exact ⟨b, hb.weak_one hΓ (.skip .refl), hn, by rwa [lift_subst]⟩

/-! ## What the substitution lemma needs that the term does not say

`Interp.to_substTerm` takes an interpretation of `t[θ]` in `Γ'` apart and
rebuilds it for `t` in `Γ`.  Most of each clause's premises come back from
the subject's typing, inverted a layer at a time (`Regular.lean`); two do
not, and both are *semantic*:

* at a binder, rebuilding the extended stage's admissibility needs every
  approximant of the annotation to be a type (`IsTypeAt`);
* at an `app` or `snd`, the clause's label link has to be recognised in
  the smaller context, and what does that is the function's — resp. the
  pair's — own typing (`PinApp`, `PinSnd`).

These are `HasFixedness` in the original, where `HasSubstitution.app`
takes it as a hypothesis and `outputAtom_rawPi_fixed_support` turns it
into exactly this: a non-`⊥` response sits at a genuine point of the
domain.  They are stated here without `SoundTy`, so that `Interp.lean`
stays below it, and discharged in `Sound.lean` as a third conclusion of
`IsDefEq.sound` (`design.md` §4). -/

/-- **Every valuation approximating `θ` is below an admissible one that
still approximates it.**  `Adm` is not upward closed — enlarging a
valuation breaks its slots' typings — so this does not come for free, and
it is what lets the conditions below be stated where they are *provable*:
at the `Γ` side, each an immediate consequence of the subterm's own
`SoundTy`.

`Valuation.Approx.canon_one` (`Sound.lean`) is this at a single
substitution, which is the only kind that arises, and `Saturates.lift`
carries it under a binder. -/
def Subst.Saturates (Δ Γ Γ' : List Term) (θ σ : Subst) (ρ : Valuation) : Prop :=
  ∀ {{ρ'}}, Valuation.Approx Δ Γ' Γ θ σ ρ ρ' →
    ∃ ρ'', Valuation.LE Δ Γ ρ' ρ'' ∧ Valuation.Approx Δ Γ' Γ θ σ ρ ρ'' ∧
      Adm Δ Γ (θ.comp σ) ρ''

/-- Every approximant of `t`, read as a code, names `t`: what saturation
at a sort says, and what an atom's top shape gives by downward closure. -/
def CodeAt (Γ : List Term) (t : Term) : Prop :=
  ∀ {{Δ : List Term}} {{σ ρ}}, Adm Δ Γ σ ρ →
    ∀ {m}, Interp Δ Γ t σ ρ m → TShape.WF Δ m (t.subst σ)

/-- Every approximant of `t` at an admissible stage is typed at an
approximant of `A`: `SoundTy Γ t A`'s `approx` half.  Needed at the two
binders whose slot is not an entry input — `natCase`'s and `Y`'s. -/
def TypedAt (Γ : List Term) (t A : Term) : Prop :=
  ∀ {{Δ : List Term}} {σ ρ}, Adm Δ Γ σ ρ →
    ∀ {m}, Interp Δ Γ t σ ρ m → ∃ a, Interp Δ Γ A σ ρ a ∧ TShape.HasType Δ m a

/-- **Every approximant of `A` is a type, and names `A` as a code.**  Both
halves exist already: it is `TypedAt` at the top sort together with
`CodeAt`, which is how `SoundTy Γ A (.sort u)` delivers it. -/
def IsTypeAt (Γ : List Term) (A : Term) : Prop := TypedAt Γ A .type ∧ CodeAt Γ A

/-- Typed at the top sort is typed at `type` outright: the `⊥` witness the
existential allows is no weaker, since typing is monotone in the type and
`⊥` is below `type`.  This is `IsTypeAt`'s first half, read at a stage. -/
theorem TypedAt.apply {Γ Δ : List Term} {A : Term} {σ ρ} {c : TShape}
    (h : TypedAt Γ A .type) (hAdm : Adm Δ Γ σ ρ) (hc : Interp Δ Γ A σ ρ c) :
    c.HasType Δ .type := by
  obtain ⟨a, ha, hca⟩ := h hAdm hc
  exact hca.mono_r hAdm.ctx _ ha.le_sort .sort

/-- A λ-shape approximating `F` has its label definitionally equal to the
argument's type at the stage.  In the original this is the function's
Π-fixedness and `outputAtom_rawPi_fixed_support`; here it is
`Interp.lam_label_ty` on `SoundTy F (Π A B)`. -/
def PinApp (Γ : List Term) (F a : Term) : Prop :=
  ∀ {{Δ : List Term}} {σ ρ} {n} {A : Term} {g : ShapeFun n}, Adm Δ Γ σ ρ →
    Interp Δ Γ F σ ρ (Shape.T (n := n+1) (ShapeS.lam A g)) → Stable Δ Γ σ a A

/-- The Σ twin, for `snd`: a pair shape approximating `p` has its label
definitionally equal to the type of `fst p` at the stage. -/
def PinSnd (Γ : List Term) (p : Term) : Prop :=
  ∀ {{Δ : List Term}} {σ ρ} {n} {A a₀ : Term} {x y : Shape n}, Adm Δ Γ σ ρ →
    Interp Δ Γ p σ ρ (Shape.T (n := n+1) (ShapeS.pair A a₀ x y)) →
    Stable Δ Γ σ (Term.fst p) A

/-- The two gathered over the whole term, structurally — the semantic
counterpart of the shallow inversions in `Regular.lean`.

A subterm appears here only where `Interp` interprets it, since the only
consumer is `Interp.to_substTerm`, which recurses exactly where the
clauses do.  So `id` and `refl` are `True` (their clauses hold no
interpretation), a `natCase`'s motive and a `tr`'s proof are absent for
the same reason, and `Y` asks only that its annotation be a type — its
own typing would have to be proved and nothing reads it. -/
def Term.Pinned (Γ : List Term) : Term → Prop
  | .app F a => PinApp Γ F a ∧ F.Pinned Γ ∧ a.Pinned Γ
  | .lam A b => IsTypeAt Γ A ∧ A.Pinned Γ ∧ b.Pinned (A :: Γ)
  | .forallE A B | .sigma A B => IsTypeAt Γ A ∧ A.Pinned Γ ∧ B.Pinned (A :: Γ)
  | .pair A B a b => IsTypeAt Γ A ∧ A.Pinned Γ ∧ B.Pinned (A :: Γ) ∧ a.Pinned Γ ∧ b.Pinned Γ
  | .fst p => p.Pinned Γ
  | .snd p => PinSnd Γ p ∧ p.Pinned Γ
  | .succ n => n.Pinned Γ
  | .natCase _ M a b => TypedAt Γ M .nat ∧ M.Pinned Γ ∧ a.Pinned Γ ∧ b.Pinned (.nat :: Γ)
  | .Y A b => IsTypeAt Γ A ∧ A.Pinned Γ ∧ b.Pinned (A :: Γ)
  | .tr _ A a b C x _ =>
    IsTypeAt Γ A ∧ A.Pinned Γ ∧ a.Pinned Γ ∧ b.Pinned Γ ∧ C.Pinned (A :: Γ) ∧ x.Pinned Γ
  | _ => True

/-- `nat` is a type at every stage, so its binders cost nothing. -/
theorem IsTypeAt.nat {Γ : List Term} : IsTypeAt Γ .nat := by
  refine ⟨?_, ?_⟩
  · intro _ _ _ hAdm _ hb
    exact ⟨.type, .sort', .mono_l hAdm.ctx .nat hb.le_nat⟩
  · intro _ _ _ hAdm _ hb
    exact TShape.WF.mono hAdm.ctx hb.le_nat (x := .nat) (show TyEq _ _ _ from .refl .nat)

/-- `zero` is a numeral at every stage. -/
theorem TypedAt.zero {Γ : List Term} : TypedAt Γ .zero .nat := by
  intro _ _ _ hAdm _ hm
  have hΔ := hAdm.ctx
  exact ⟨.nat, .nat', TShape.HasType.zero.mono_l hΔ hm.le_zero⟩

/-- The successor of the slot a `natCase` branch binds: the slot is a
numeral because the stage is admissible, so the successor is one too.
This is the lifted motive's argument at `natCase`. -/
theorem TypedAt.succ_bvar0 {Γ : List Term} :
    TypedAt (.nat :: Γ) (.succ (.bvar 0)) .nat := by
  intro Δ σ ρ hAdm m hm
  have hΔ := hAdm.ctx
  refine ⟨.nat, .nat', ?_⟩
  cases hm with
  | bot => exact .bot .nat
  | succ hv hle =>
    obtain ⟨c, hc, hct, _⟩ := hAdm.lookupCanon (i := 0) .zero
    have h0 : (ρ 0).2.IsNumeral :=
      hct.hasType.isNumeral hΔ hc.le_nat
    have hvty := h0.hasType.mono_l hΔ hv.le_bvar
    refine TShape.HasType.mono_l hΔ (.succ ?_) hle
    exact hvty.isNumeral hΔ (.refl (a := .nat) trivial)

/-- Admissibility restricts along a context lift.  A variable of the
smaller context is one of the bigger (`Lookup.weak'`) and its type is the
same term lifted, so `Interp.unweak` moves that type's approximant down —
which is exactly the data `Adm` keeps. -/
theorem Adm.unlift {Δ Γ Γ' : List Term} {l σ ρ} (hΔ : ⊢ Δ) (hΓ : ⊢ Γ)
    (WΓ : Ctx.Lift' l Γ Γ') (W : Ctx.SubstEq Δ σ σ Γ') (h : Adm Δ Γ' σ ρ) :
    Adm Δ Γ (σ.lift_l l) (fun i => ρ (l.liftVar i)) := by
  refine ⟨hΔ, W.lift_l WΓ hΓ, fun {i A} hlk => ?_⟩
  obtain ⟨a, ha, hn, hac⟩ := h.lookupCanon (hlk.weak' WΓ)
  obtain ⟨_, hlkty⟩ := hΓ.lookup hlk
  exact ⟨a, ha.unweak hΔ hΓ hlkty WΓ W (fun _ => rfl), hn, by rwa [subst_lift'] at hac⟩

/-- A code's naming survives weakening, the same way a type's does. -/
theorem CodeAt.weak' {Γ Γ' : List Term} {l : Lift} {t T : Term} (hΓ : ⊢ Γ)
    (ht : Γ ⊢ t : T) (WΓ : Ctx.Lift' l Γ Γ') (h : CodeAt Γ t) :
    CodeAt Γ' (t.lift' l) := by
  intro Δ σ ρ hAdm c hc
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have := h (hAdm.unlift hΔ hΓ WΓ W) (hc.unweak hΔ hΓ ht WΓ W (fun _ => rfl))
  rwa [← subst_lift'] at this

theorem TypedAt.weak' {Γ Γ' : List Term} {l : Lift} {t A T : Term} (hΓ : ⊢ Γ)
    (ht : Γ ⊢ t : T) (WΓ : Ctx.Lift' l Γ Γ') (h : TypedAt Γ t A) :
    TypedAt Γ' (t.lift' l) (A.lift' l) := by
  intro Δ σ ρ hAdm m hm
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  obtain ⟨a, ha, hty⟩ := h (hAdm.unlift hΔ hΓ WΓ W) (hm.unweak hΔ hΓ ht WΓ W (fun _ => rfl))
  exact ⟨a, ha.weak' hΓ WΓ (fun _ => rfl), hty⟩

theorem IsTypeAt.weak' {Γ Γ' : List Term} {l : Lift} {A T : Term} (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A : T) (WΓ : Ctx.Lift' l Γ Γ') (h : IsTypeAt Γ A) :
    IsTypeAt Γ' (A.lift' l) :=
  ⟨h.1.weak' hΓ hA WΓ, h.2.weak' hΓ hA WΓ⟩

theorem PinApp.weak' {Γ Γ' : List Term} {l : Lift} {F a T : Term} (hΓ : ⊢ Γ)
    (hF : Γ ⊢ F : T) (WΓ : Ctx.Lift' l Γ Γ') (h : PinApp Γ F a) :
    PinApp Γ' (F.lift' l) (a.lift' l) := by
  intro Δ σ ρ n A g hAdm hf
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  exact Stable.weak' hΓ WΓ
    (h (hAdm.unlift hΔ hΓ WΓ W)
      (hf.unweak hΔ hΓ hF WΓ W (fun _ => rfl)))

theorem PinSnd.weak' {Γ Γ' : List Term} {l : Lift} {p T : Term} (hΓ : ⊢ Γ)
    (hp : Γ ⊢ p : T) (WΓ : Ctx.Lift' l Γ Γ') (h : PinSnd Γ p) :
    PinSnd Γ' (p.lift' l) := by
  intro Δ σ ρ n A a₀ x y hAdm hf
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  exact Stable.weak' (a := .fst p) hΓ WΓ
    (h (hAdm.unlift hΔ hΓ WΓ W)
      (hf.unweak hΔ hΓ hp WΓ W (fun _ => rfl)))

theorem Term.Pinned.weak' {t : Term} {Γ Γ' : List Term} {l : Lift} {T : Term} (hΓ : ⊢ Γ)
    (ht : Γ ⊢ t : T) (W : Ctx.Lift' l Γ Γ') (h : t.Pinned Γ) : (t.lift' l).Pinned Γ' := by
  induction t generalizing Γ Γ' l T with
  | bvar | sort | unit | star | nat | zero | id | refl => trivial
  | succ _ ih => exact ih hΓ (ht.succ_regular (.inl rfl)) W h
  | fst _ ih =>
    obtain ⟨_, _, hp⟩ := ht.fst_regular (.inl rfl)
    exact ih hΓ hp W h
  | app _ _ ihF iha =>
    obtain ⟨hp, hF, ha⟩ := h
    obtain ⟨⟨_, _, hAF⟩, _, hAa⟩ := ht.app_regular (.inl rfl)
    exact ⟨hp.weak' hΓ hAF W, ihF hΓ hAF W hF, iha hΓ hAa W ha⟩
  | snd _ ih =>
    obtain ⟨hp, hpp⟩ := h
    obtain ⟨_, _, hAnn⟩ := ht.snd_regular (.inl rfl)
    exact ⟨hp.weak' hΓ hAnn W, ih hΓ hAnn W hpp⟩
  | lam A b ihA ihb =>
    obtain ⟨hty, hPA, hPb⟩ := h
    obtain ⟨⟨u, hA⟩, _, hAb⟩ := ht.lam_regular (.inl rfl)
    have hAA := hA
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, u, hA⟩
    exact ⟨hty.weak' hΓ hAA W, ihA hΓ hAA W hPA, ihb hΓA hAb W.cons hPb⟩
  | forallE A B ihA ihB =>
    obtain ⟨hty, hPA, hPB⟩ := h
    obtain ⟨⟨u, hA⟩, _, hAB⟩ := ht.forallE_regular (.inl rfl)
    have hAA := hA
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, u, hA⟩
    exact ⟨hty.weak' hΓ hAA W, ihA hΓ hAA W hPA, ihB hΓA hAB W.cons hPB⟩
  | sigma A B ihA ihB =>
    obtain ⟨hty, hPA, hPB⟩ := h
    obtain ⟨⟨u, hA⟩, _, hAB⟩ := ht.sigma_regular (.inl rfl)
    have hAA := hA
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, u, hA⟩
    exact ⟨hty.weak' hΓ hAA W, ihA hΓ hAA W hPA, ihB hΓA hAB W.cons hPB⟩
  | pair A B a b ihA ihB iha ihb =>
    obtain ⟨hty, hPA, hPB, hPa, hPb⟩ := h
    obtain ⟨⟨u, hA⟩, ⟨_, hAB⟩, hAa, _, hAb⟩ := ht.pair_regular (.inl rfl)
    have hAA := hA
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, u, hA⟩
    exact ⟨hty.weak' hΓ hAA W, ihA hΓ hAA W hPA, ihB hΓA hAB W.cons hPB,
      iha hΓ hAa W hPa, ihb hΓ hAb W hPb⟩
  | natCase C M a b ihC ihM iha ihb =>
    obtain ⟨hM, hPM, hPa, hPb⟩ := h
    obtain ⟨hAM, ⟨_, hAa⟩, _, hAb⟩ := ht.natCase_regular (.inl rfl)
    have hΓN : ⊢ (.nat :: Γ) := ⟨hΓ, _, .nat⟩
    have WN : Ctx.Lift' l.cons (.nat :: Γ) (.nat :: Γ') := by
      simpa using W.cons (A := .nat)
    have hM' : TypedAt Γ' (M.lift' l) .nat := hM.weak' hΓ hAM W
    exact ⟨hM', ihM hΓ hAM W hPM, iha hΓ hAa W hPa, ihb hΓN hAb WN hPb⟩
  | Y A b ihA ihb =>
    obtain ⟨hty, hPA, hPb⟩ := h
    obtain ⟨⟨u, hA⟩, _, _, hAb⟩ := ht.Y_regular (.inl rfl)
    have hAA := hA
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, u, hA⟩
    exact ⟨hty.weak' hΓ hAA W, ihA hΓ hAA W hPA, ihb hΓA hAb W.cons hPb⟩
  | tr r A a b C X Hp ihA iha ihb ihC ihX ihH =>
    obtain ⟨hty, hPA, hPa, hPb, hPC, hPX⟩ := h
    obtain ⟨⟨u, hA⟩, hAa, hAb, _, ⟨_, _, _, hAX, _, _⟩, _, hAC⟩ := ht.tr_regular (.inl rfl)
    have hAA := hA
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, u, hA⟩
    exact ⟨hty.weak' hΓ hAA W, ihA hΓ hAA W hPA, iha hΓ hAa W hPa, ihb hΓ hAb W hPb,
      ihC hΓA hAC W.cons hPC, ihX hΓ hAX W hPX⟩

/-- The interpretation is closed under moving a shape up a level.  A shape
and its lift are equivalent in the order and `Interp` is downward closed,
so this is `Interp.mono` in one line — and it is what lets a proof
normalise every shape to a common level before applying a typing lemma,
whose transport only goes up. -/
theorem Interp.lift {Δ Γ : List Term} {t σ ρ} {m : TShape} (hΔ : ⊢ Δ) {k}
    (hk : m.1 ≤ k) (H : Interp Δ Γ t σ ρ m) : Interp Δ Γ t σ ρ (m.lift k) :=
  H.mono hΔ (.lift_le hΔ hk H.wf)
