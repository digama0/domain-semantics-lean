import DomainSemantics.HasType

/-! # The interpretation relation

`Interp Γ t Δ σ ρ m` says that the shape `m` is a lower bound on an
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

**Σ is deferred** (§5 of `presheaf-plan.md`): `sigma`, `pair`, `fst` and
`snd` get only the `bot` constructor for now, because a `pair` shape must
first carry the term label of its first component, exactly as `forallE`
and `lam` do, before its second component can be typed through the graph
lookup.  The same TODO is recorded on `Shape.HasType`. -/

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

/-! ## Total-level shapes for the atoms -/

namespace TShape

abbrev unit (r : Bool) : TShape := Shape.T (n := 1) (ShapeS.unit r)
abbrev nat : TShape := Shape.T (n := 1) ShapeS.nat
abbrev zero : TShape := Shape.T (n := 1) ShapeS.zero

end TShape

/-! ## The relation -/

/-- `m` approximates the interpretation of `t` at stage `(Δ, σ)` under `ρ`. -/
inductive Interp (Γ : List Term) :
    Term → List Term → Subst → Valuation → TShape → Prop where
  /-- `⊥` approximates everything, including the terms Σ is deferred on. -/
  | bot {n} : Interp Γ t Δ σ ρ (Shape.T (n := n) Shape.bot)
  | bvar : TShape.LE Δ m (ρ i) → Interp Γ (.bvar i) Δ σ ρ m
  | sort : TShape.LE Δ m (TShape.sort r) → Interp Γ (.sort r) Δ σ ρ m
  | unit : TShape.LE Δ m (TShape.unit r) → Interp Γ (.unit r) Δ σ ρ m
  -- `star r` has only the `bot` rule: the unit type's inhabitant carries
  -- no information, which is what makes `unit_eta` sound
  | nat : TShape.LE Δ m TShape.nat → Interp Γ .nat Δ σ ρ m
  | zero : TShape.LE Δ m TShape.zero → Interp Γ .zero Δ σ ρ m
  | succ {n} {v : Shape n} :
      Interp Γ N Δ σ ρ (Shape.T v) →
      TShape.LE Δ m (Shape.T (n := n+1) (ShapeS.succ v)) →
      Interp Γ (.succ N) Δ σ ρ m
  /-- Application is the **graph lookup at the syntactic label**.  The
  argument's type has to be named, since the label is `(A[σ], a[σ])` and
  `Term.app` does not record it; the typing premises are what make the
  label a legitimate `LabelEq` witness in `Δ` once `σ` is typed. -/
  | app {n} {g : ShapeFun n} {x y : Shape n} {A : Term} {u : Bool} :
      Interp Γ F Δ σ ρ (Shape.T (n := n+1) (ShapeS.lam g)) →
      Interp Γ a Δ σ ρ (Shape.T x) →
      Γ ⊢ A : .sort u → Γ ⊢ a : A →
      Evaluates Δ g (A.subst σ) (a.subst σ) x y →
      TShape.LE Δ m (Shape.T y) →
      Interp Γ (.app F a) Δ σ ρ m
  /-- The binder rule.  Each entry of the graph is a *probe*: a label term
  `e.tm` at a type definitionally equal to the domain, together with the
  body's interpretation at the stage extended by that term.  The premises
  are kept separate rather than conjoined, so that the nested `Interp`
  occurrence stays under `∀` and `→` only and the kernel accepts the
  definition. -/
  | lam {n} {g : ShapeFun n} {d : TShape} {A b : Term} :
      Interp Γ A Δ σ ρ d →
      Shape.WF Δ (Shape.lam g) →
      (∀ e ∈ g, ∃ u, Δ ⊢ e.ty ≡ A.subst σ : .sort u) →
      (∀ e ∈ g, Interp Γ b Δ (σ.cons e.tm) (ρ.push (Shape.T e.inp)) (Shape.T e.out)) →
      TShape.LE Δ m (Shape.T (n := n+1) (ShapeS.lam g)) →
      Interp Γ (.lam A b) Δ σ ρ m
  /-- The Π-shape carries the syntactic pair `(A[σ], B[σ.lift])`.  That
  label is the whole gluing trick: Π-injectivity falls out of soundness by
  projecting it. -/
  | forallE {n} {g : ShapeFun n} {d : Shape n} {A B : Term} :
      Interp Γ A Δ σ ρ (Shape.T d) →
      Shape.WF (n := n+1) Δ (ShapeS.forallE (A.subst σ) (B.subst σ.lift) d g) →
      (∀ e ∈ g, ∃ u, Δ ⊢ e.ty ≡ A.subst σ : .sort u) →
      (∀ e ∈ g, Interp Γ B Δ (σ.cons e.tm) (ρ.push (Shape.T e.inp)) (Shape.T e.out)) →
      TShape.LE Δ m
        (Shape.T (n := n+1) (ShapeS.forallE (A.subst σ) (B.subst σ.lift) d g)) →
      Interp Γ (.forallE A B) Δ σ ρ m
  | natCase_zero :
      Interp Γ M Δ σ ρ TShape.zero →
      Interp Γ a Δ σ ρ m →
      Interp Γ (.natCase C M a b) Δ σ ρ m
  /-- There is no syntactic predecessor former, so the label term for the
  body's binder is supplied as a premise, together with the definitional
  equation that makes it the right one. -/
  | natCase_succ {n} {v : Shape n} {t : Term} :
      Interp Γ M Δ σ ρ (Shape.T (n := n+1) (ShapeS.succ v)) →
      Shape.WF Δ v →
      Δ ⊢ M.subst σ ≡ .succ t : .nat →
      Interp Γ b Δ (σ.cons t) (ρ.push (Shape.T v)) m →
      Interp Γ (.natCase C M a b) Δ σ ρ m
  /-- The fixed point is a least fixed point for free: the constructor
  refers to the relation it is defining, so only finitely many unfoldings
  can ever produce a given approximant. -/
  | protected Y {A b : Term} {x : TShape} :
      Interp Γ (.Y A b) Δ σ ρ x →
      TShape.WF Δ x →
      Interp Γ b Δ (σ.cons ((Term.Y A b).subst σ)) (ρ.push x) m →
      Interp Γ (.Y A b) Δ σ ρ m
  /-- The identity type is **label-only**: no sub-shapes, so the shape
  records nothing but the syntax. -/
  | id : TShape.LE Δ m
        (Shape.T (n := 1) (ShapeS.id r (A.subst σ) (a.subst σ) (b.subst σ))) →
      Interp Γ (.id r A a b) Δ σ ρ m
  /-- `refl` has a shape only in the proof-relevant sort; at `r = false`
  the `bot` rule is all there is, which is proof irrelevance. -/
  | refl {n} {v : Shape n} :
      Interp Γ a Δ σ ρ (Shape.T v) →
      TShape.LE Δ m (Shape.T (n := n+1) (ShapeS.refl v)) →
      Interp Γ (.refl true a) Δ σ ρ m
  /-- Transport.  Master's constructor, with the motive evaluated at the
  stage extended by `b`, which is the label term the motive's binder is
  instantiated with. -/
  | tr {v vA m' cb : TShape} {r : Bool} {A a b C X H : Term} :
      TShape.LE Δ m m' →
      Interp Γ X Δ σ ρ m' →
      Interp Γ a Δ σ ρ v →
      Interp Γ b Δ σ ρ v →
      Interp Γ A Δ σ ρ vA →
      TShape.WF Δ v →
      TShape.HasType Δ v vA →
      Interp Γ C Δ (σ.cons (b.subst σ)) (ρ.push v) cb →
      TShape.HasType Δ m' cb →
      (r = true → Interp Γ H Δ σ ρ (Shape.T (n := v.1+1) (ShapeS.refl v.2))) →
      Interp Γ (.tr r A a b C X H) Δ σ ρ m

/-! ## Monotonicity

Both directions master has: down in the shape, up in the valuation.
Neither touches the stage, so both are the same induction as there. -/

theorem Interp.mono {Γ : List Term} (hΔ : ⊢ Δ) {t : Term} {σ ρ} {m m' : TShape}
    (h : TShape.LE Δ m m') (H : Interp Γ t Δ σ ρ m') : Interp Γ t Δ σ ρ m := by
  induction H generalizing m with
  | bot =>
    obtain ⟨k, s⟩ := m
    have hs : s = Shape.bot := TShape.le_bot rfl h
    subst hs
    exact .bot
  | bvar h1 => exact .bvar (TShape.LE.trans hΔ h h1)
  | sort h1 => exact .sort (TShape.LE.trans hΔ h h1)
  | unit h1 => exact .unit (TShape.LE.trans hΔ h h1)
  | nat h1 => exact .nat (TShape.LE.trans hΔ h h1)
  | zero h1 => exact .zero (TShape.LE.trans hΔ h h1)
  | succ hv h1 => exact .succ hv (TShape.LE.trans hΔ h h1)
  | app hF ha hA hty hev h1 =>
    exact .app hF ha hA hty hev (TShape.LE.trans hΔ h h1)
  | lam hA hwf hlab hbody h1 =>
    exact .lam hA hwf hlab hbody (TShape.LE.trans hΔ h h1)
  | forallE hA hwf hlab hbody h1 =>
    exact .forallE hA hwf hlab hbody (TShape.LE.trans hΔ h h1)
  | natCase_zero hM _ _ iha => exact .natCase_zero hM (iha hΔ h)
  | natCase_succ hM hwv heq _ _ ihb => exact .natCase_succ hM hwv heq (ihb hΔ h)
  | Y hself hwx _ _ ihb => exact .Y hself hwx (ihb hΔ h)
  | id h1 => exact .id (TShape.LE.trans hΔ h h1)
  | refl hv h1 => exact .refl hv (TShape.LE.trans hΔ h h1)
  | tr hle hX ha hb hA hwv hvA hC hm' hH _ _ _ _ _ _ =>
    exact .tr (TShape.LE.trans hΔ h hle) hX ha hb hA hwv hvA hC hm' hH

theorem Interp.mono_val {Γ : List Term} {t : Term} {σ} {ρ ρ' : Valuation} {m : TShape}
    (hΔ : ⊢ Δ) (hρ : ρ.LE Δ ρ') (H : Interp Γ t Δ σ ρ m) : Interp Γ t Δ σ ρ' m := by
  induction H generalizing ρ' with
  | bot => exact .bot
  | bvar h1 => exact .bvar (TShape.LE.trans hΔ h1 (hρ _))
  | sort h1 => exact .sort h1
  | unit h1 => exact .unit h1
  | nat h1 => exact .nat h1
  | zero h1 => exact .zero h1
  | succ _ h1 ihv => exact .succ (ihv hΔ hρ) h1
  | app _ _ hA hty hev h1 ihF iha => exact .app (ihF hΔ hρ) (iha hΔ hρ) hA hty hev h1
  | lam _ hwf hlab _ h1 ihA ihbody =>
    exact .lam (ihA hΔ hρ) hwf hlab (fun e he => ihbody e he hΔ
      (Valuation.LE.push.2 ⟨hρ, TShape.LE.refl (a := Shape.T e.inp) (hwf.2.2.1 e he).2.2.1⟩)) h1
  | forallE _ hwf hlab _ h1 ihA ihbody =>
    exact .forallE (ihA hΔ hρ) hwf hlab (fun e he => ihbody e he hΔ
      (Valuation.LE.push.2 ⟨hρ, TShape.LE.refl (a := Shape.T e.inp) (hwf.2.2.2.1 e he).2.2.1⟩)) h1
  | natCase_zero _ _ ihM iha => exact .natCase_zero (ihM hΔ hρ) (iha hΔ hρ)
  | natCase_succ _ hwv heq _ ihM ihb =>
    exact .natCase_succ (ihM hΔ hρ) hwv heq
      (ihb hΔ (Valuation.LE.push.2 ⟨hρ, TShape.LE.refl (a := Shape.T _) hwv⟩))
  | Y _ hwx _ ihself ihb =>
    exact .Y (ihself hΔ hρ) hwx (ihb hΔ (Valuation.LE.push.2 ⟨hρ, TShape.LE.refl hwx⟩))
  | id h1 => exact .id h1
  | refl _ h1 ihv => exact .refl (ihv hΔ hρ) h1
  | tr hle _ _ _ _ hwv hvA _ hm' _ ihX iha ihb ihA ihC ihH =>
    exact .tr hle (ihX hΔ hρ) (iha hΔ hρ) (ihb hΔ hρ) (ihA hΔ hρ) hwv hvA
      (ihC hΔ (Valuation.LE.push.2 ⟨hρ, TShape.LE.refl hwv⟩)) hm'
      (fun hr => ihH hr hΔ hρ)

/-! ## Constructors at the canonical shape

Master's primed forms.  Each takes the well-formedness that `LE` needs to
be reflexive, which master gets from its shapes being a `WF` subtype. -/

theorem Interp.bvar' {Γ : List Term} {Δ σ ρ i} (h : TShape.WF Δ (ρ i)) :
    Interp Γ (.bvar i) Δ σ ρ (ρ i) := .bvar (TShape.LE.refl h)

theorem Interp.sort' {Γ : List Term} {Δ σ ρ r} :
    Interp Γ (.sort r) Δ σ ρ (TShape.sort r) :=
  .sort (TShape.LE.refl (a := TShape.sort r) trivial)

theorem Interp.unit' {Γ : List Term} {Δ σ ρ r} :
    Interp Γ (.unit r) Δ σ ρ (TShape.unit r) :=
  .unit (TShape.LE.refl (a := TShape.unit r) trivial)

theorem Interp.nat' {Γ : List Term} {Δ σ ρ} : Interp Γ .nat Δ σ ρ TShape.nat :=
  .nat (TShape.LE.refl (a := TShape.nat) trivial)

theorem Interp.zero' {Γ : List Term} {Δ σ ρ} : Interp Γ .zero Δ σ ρ TShape.zero :=
  .zero (TShape.LE.refl (a := TShape.zero) trivial)

theorem Interp.succ' {Γ : List Term} {Δ σ ρ N} {n} {v : Shape n}
    (hv : Interp Γ N Δ σ ρ (Shape.T v)) (h : Shape.WF Δ v) :
    Interp Γ (.succ N) Δ σ ρ (Shape.T (n := n+1) (ShapeS.succ v)) :=
  .succ hv (TShape.LE.refl (a := Shape.T (n := n+1) (ShapeS.succ v)) h)

/-! ## Inversion for the atoms

Every rule but `bot` pins the head of the term, so these are one `cases`
each.  They are what the soundness induction reads a subderivation with,
and — for `forallE` — what eventually yields Π-injectivity, since the
shape it returns carries the syntactic pair. -/

theorem Interp.le_sort {Γ : List Term} {Δ σ ρ m r}
    (H : Interp Γ (.sort r) Δ σ ρ m) : TShape.LE Δ m (TShape.sort r) := by
  cases H with
  | bot => exact TShape.bot_le' rfl
  | sort h => exact h

theorem Interp.le_unit {Γ : List Term} {Δ σ ρ m r}
    (H : Interp Γ (.unit r) Δ σ ρ m) : TShape.LE Δ m (TShape.unit r) := by
  cases H with
  | bot => exact TShape.bot_le' rfl
  | unit h => exact h

theorem Interp.le_nat {Γ : List Term} {Δ σ ρ m}
    (H : Interp Γ .nat Δ σ ρ m) : TShape.LE Δ m TShape.nat := by
  cases H with
  | bot => exact TShape.bot_le' rfl
  | nat h => exact h

theorem Interp.le_zero {Γ : List Term} {Δ σ ρ m}
    (H : Interp Γ .zero Δ σ ρ m) : TShape.LE Δ m TShape.zero := by
  cases H with
  | bot => exact TShape.bot_le' rfl
  | zero h => exact h

theorem Interp.le_id {Γ : List Term} {Δ σ ρ m r A a b}
    (H : Interp Γ (.id r A a b) Δ σ ρ m) :
    TShape.LE Δ m
      (Shape.T (n := 1) (ShapeS.id r (A.subst σ) (a.subst σ) (b.subst σ))) := by
  cases H with
  | bot => exact TShape.bot_le' rfl
  | id h => exact h

theorem Interp.bvar_iff {Γ : List Term} {Δ σ ρ m i} :
    Interp Γ (.bvar i) Δ σ ρ m ↔ TShape.LE Δ m (ρ i) :=
  ⟨fun H => by cases H with | bot => exact TShape.bot_le' rfl | bvar h => exact h, .bvar⟩

theorem Interp.le_succ {Γ : List Term} {Δ σ ρ m N}
    (H : Interp Γ (.succ N) Δ σ ρ m) :
    ∃ n, ∃ v : Shape n, Interp Γ N Δ σ ρ (Shape.T v) ∧
      TShape.LE Δ m (Shape.T (n := n+1) (ShapeS.succ v)) := by
  cases H with
  | bot => exact ⟨0, .bot, .bot, TShape.bot_le' rfl⟩
  | succ hv h => exact ⟨_, _, hv, h⟩

/-- The Π case.  The shape the interpretation lands in **records the
syntactic pair** `(A[σ], B[σ.lift])`, which is what makes injectivity of
`forallE` a projection out of soundness rather than a consequence of
adequacy. -/
theorem Interp.le_forallE {Γ : List Term} {Δ σ ρ m A B}
    (H : Interp Γ (.forallE A B) Δ σ ρ m) :
    m.2 = Shape.bot ∨
      ∃ n, ∃ d : Shape n, ∃ g : ShapeFun n,
        TShape.LE Δ m
          (Shape.T (n := n+1) (ShapeS.forallE (A.subst σ) (B.subst σ.lift) d g)) := by
  cases H with
  | bot => exact .inl rfl
  | forallE _ _ _ _ h => exact .inr ⟨_, _, _, h⟩
