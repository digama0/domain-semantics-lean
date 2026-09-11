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
  | bot {n} : Interp Δ Γ t σ ρ (Shape.T (n := n) Shape.bot)
  | bvar : TShape.WF Δ m → TShape.LE Δ m (ρ i) → Interp Δ Γ (.bvar i) σ ρ m
  | sort : TShape.WF Δ m → TShape.LE Δ m (TShape.sort r) → Interp Δ Γ (.sort r) σ ρ m
  | unit : TShape.WF Δ m → TShape.LE Δ m (TShape.unit r) → Interp Δ Γ (.unit r) σ ρ m
  -- `star r` has only the `bot` rule: the unit type's inhabitant carries
  -- no information, which is what makes `unit_eta` sound
  | nat : TShape.WF Δ m → TShape.LE Δ m TShape.nat → Interp Δ Γ .nat σ ρ m
  | zero : TShape.WF Δ m → TShape.LE Δ m TShape.zero → Interp Δ Γ .zero σ ρ m
  | succ {n} {v : Shape n} :
      Interp Δ Γ N σ ρ (Shape.T v) →
      TShape.WF Δ m →
      TShape.LE Δ m (Shape.T (n := n+1) (ShapeS.succ v)) →
      Interp Δ Γ (.succ N) σ ρ m
  /-- Application is the **graph lookup at the syntactic label**.  The
  argument's type has to be named, since `Term.app` does not record it,
  and it is named as a term of `Δ`: the label is `(A, a[σ])`.

  No typing premise is needed on `A`.  `Evaluates` only returns something
  other than `⊥` through its `entry` rule, whose `LabelEq` premise already
  forces `Δ ⊢ A ≡ e.ty : sort u` and `Δ ⊢ a[σ] ≡ e.tm : e.ty`, so the
  typing comes from the graph.  Naming the type in `Δ` rather than in `Γ`
  is also what makes `Interp.subst` an equivalence: a substitution in the
  term leaves the label's type alone. -/
  | app {n} {g : ShapeFun n} {x y : Shape n} {A : Term} :
      Interp Δ Γ F σ ρ (Shape.T (n := n+1) (ShapeS.lam g)) →
      Interp Δ Γ a σ ρ (Shape.T x) →
      Evaluates Δ g A (a.subst σ) x y →
      TShape.WF Δ m →
      TShape.LE Δ m (Shape.T y) →
      Interp Δ Γ (.app F a) σ ρ m
  /-- The binder rule.  Each entry of the graph is a *probe*: a label term
  `e.tm` at a type definitionally equal to the domain, together with the
  body's interpretation at the stage extended by that term.  The premises
  are kept separate rather than conjoined, so that the nested `Interp`
  occurrence stays under `∀` and `→` only and the kernel accepts the
  definition. -/
  | lam {n} {g : ShapeFun n} {d : TShape} {A b : Term} :
      Interp Δ Γ A σ ρ d →
      Shape.WF Δ (Shape.lam g) →
      (∀ e ∈ g, ∃ u, Δ ⊢ e.ty ≡ A.subst σ : .sort u) →
      (∀ e ∈ g, Interp Δ (A :: Γ) b (σ.cons e.tm) (ρ.push (Shape.T e.inp)) (Shape.T e.out)) →
      TShape.WF Δ m →
      TShape.LE Δ m (Shape.T (n := n+1) (ShapeS.lam g)) →
      Interp Δ Γ (.lam A b) σ ρ m
  /-- The Π-shape carries the syntactic pair `(A[σ], B[σ.lift])`.  That
  label is the whole gluing trick: Π-injectivity falls out of soundness by
  projecting it. -/
  | forallE {n} {g : ShapeFun n} {d : Shape n} {A B : Term} :
      Interp Δ Γ A σ ρ (Shape.T d) →
      Shape.WF (n := n+1) Δ (ShapeS.forallE (A.subst σ) (B.subst σ.lift) d g) →
      (∀ e ∈ g, ∃ u, Δ ⊢ e.ty ≡ A.subst σ : .sort u) →
      (∀ e ∈ g, Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push (Shape.T e.inp)) (Shape.T e.out)) →
      TShape.WF Δ m →
      TShape.LE Δ m
        (Shape.T (n := n+1) (ShapeS.forallE (A.subst σ) (B.subst σ.lift) d g)) →
      Interp Δ Γ (.forallE A B) σ ρ m
  | natCase_zero :
      Interp Δ Γ M σ ρ TShape.zero →
      Interp Δ Γ a σ ρ m →
      Interp Δ Γ (.natCase C M a b) σ ρ m
  /-- There is no syntactic predecessor former, so the label term for the
  body's binder is supplied as a premise, together with the definitional
  equation that makes it the right one. -/
  | natCase_succ {n} {v : Shape n} {t : Term} :
      Interp Δ Γ M σ ρ (Shape.T (n := n+1) (ShapeS.succ v)) →
      Shape.WF Δ v →
      Δ ⊢ M.subst σ ≡ .succ t : .nat →
      Interp Δ (.nat :: Γ) b (σ.cons t) (ρ.push (Shape.T v)) m →
      Interp Δ Γ (.natCase C M a b) σ ρ m
  /-- The fixed point is a least fixed point for free: the constructor
  refers to the relation it is defining, so only finitely many unfoldings
  can ever produce a given approximant. -/
  | protected Y {A b : Term} {x : TShape} :
      Interp Δ Γ (.Y A b) σ ρ x →
      TShape.WF Δ x →
      Interp Δ (A :: Γ) b (σ.cons ((Term.Y A b).subst σ)) (ρ.push x) m →
      Interp Δ Γ (.Y A b) σ ρ m
  /-- The identity type is **label-only**: no sub-shapes, so the shape
  records nothing but the syntax. -/
  | id : TShape.WF Δ m →
      TShape.LE Δ m
        (Shape.T (n := 1) (ShapeS.id r (A.subst σ) (a.subst σ) (b.subst σ))) →
      Interp Δ Γ (.id r A a b) σ ρ m
  /-- `refl` has a shape only in the proof-relevant sort; at `r = false`
  the `bot` rule is all there is, which is proof irrelevance. -/
  | refl {n} {v : Shape n} :
      Interp Δ Γ a σ ρ (Shape.T v) →
      TShape.WF Δ m →
      TShape.LE Δ m (Shape.T (n := n+1) (ShapeS.refl v)) →
      Interp Δ Γ (.refl true a) σ ρ m
  /-- Transport.  Master's constructor, with the motive evaluated at the
  stage extended by `b`, which is the label term the motive's binder is
  instantiated with. -/
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
      TShape.HasType Δ m' cb →
      (r = true → Interp Δ Γ H σ ρ (Shape.T (n := v.1+1) (ShapeS.refl v.2))) →
      Interp Δ Γ (.tr r A a b C X H) σ ρ m

/-! ## Monotonicity

Both directions master has: down in the shape, up in the valuation.
Neither touches the stage, so both are the same induction as there. -/

theorem Interp.wf {Δ Γ : List Term} {t : Term} {σ ρ m}
    (H : Interp Δ Γ t σ ρ m) : TShape.WF Δ m := by
  induction H with
  | bot => exact TShape.WF.bot
  | bvar hw _ => exact hw
  | sort hw _ => exact hw
  | unit hw _ => exact hw
  | nat hw _ => exact hw
  | zero hw _ => exact hw
  | succ _ hw _ => exact hw
  | app _ _ _ hw _ => exact hw
  | lam _ _ _ _ hw _ => exact hw
  | forallE _ _ _ _ hw _ => exact hw
  | id hw _ => exact hw
  | refl _ hw _ => exact hw
  | tr hw _ _ _ _ _ _ _ _ _ _ => exact hw
  | natCase_zero _ _ _ iha => exact iha
  | natCase_succ _ _ _ _ _ ihb => exact ihb
  | Y _ _ _ _ ihb => exact ihb

theorem Interp.mono (hΔ : ⊢ Δ) {Γ : List Term} {t : Term} {σ ρ} {m m' : TShape}
    (hw : TShape.WF Δ m) (h : TShape.LE Δ m m') (H : Interp Δ Γ t σ ρ m') :
    Interp Δ Γ t σ ρ m := by
  induction H generalizing m with
  | bot =>
    obtain ⟨k, s⟩ := m
    have hs : s = Shape.bot := TShape.le_bot rfl h
    subst hs
    exact .bot
  | bvar _ h1 => exact .bvar hw (TShape.LE.trans hΔ h h1)
  | sort _ h1 => exact .sort hw (TShape.LE.trans hΔ h h1)
  | unit _ h1 => exact .unit hw (TShape.LE.trans hΔ h h1)
  | nat _ h1 => exact .nat hw (TShape.LE.trans hΔ h h1)
  | zero _ h1 => exact .zero hw (TShape.LE.trans hΔ h h1)
  | succ hv _ h1 => exact .succ hv hw (TShape.LE.trans hΔ h h1)
  | app hF ha hev _ h1 => exact .app hF ha hev hw (TShape.LE.trans hΔ h h1)
  | lam hA hwf hlab hbody _ h1 =>
    exact .lam hA hwf hlab hbody hw (TShape.LE.trans hΔ h h1)
  | forallE hA hwf hlab hbody _ h1 =>
    exact .forallE hA hwf hlab hbody hw (TShape.LE.trans hΔ h h1)
  | natCase_zero hM _ _ iha => exact .natCase_zero hM (iha hw h)
  | natCase_succ hM hwv heq _ _ ihb => exact .natCase_succ hM hwv heq (ihb hw h)
  | Y hself hwx _ _ ihb => exact .Y hself hwx (ihb hw h)
  | id _ h1 => exact .id hw (TShape.LE.trans hΔ h h1)
  | refl hv _ h1 => exact .refl hv hw (TShape.LE.trans hΔ h h1)
  | tr _ hle hX ha hb hA hwv hvA hC hm' hH _ _ _ _ _ _ =>
    exact .tr hw (TShape.LE.trans hΔ h hle) hX ha hb hA hwv hvA hC hm' hH

theorem Interp.mono_val {Γ : List Term} {t : Term} {σ} {ρ ρ' : Valuation} {m : TShape}
    (hΔ : ⊢ Δ) (hρ : ρ.LE Δ ρ') (H : Interp Δ Γ t σ ρ m) : Interp Δ Γ t σ ρ' m := by
  induction H generalizing ρ' with
  | bot => exact .bot
  | bvar hw h1 => exact .bvar hw (TShape.LE.trans hΔ h1 (hρ _))
  | sort hw h1 => exact .sort hw h1
  | unit hw h1 => exact .unit hw h1
  | nat hw h1 => exact .nat hw h1
  | zero hw h1 => exact .zero hw h1
  | succ _ hw h1 ihv => exact .succ (ihv hρ) hw h1
  | app _ _ hev hw h1 ihF iha => exact .app (ihF hρ) (iha hρ) hev hw h1
  | lam _ hwf hlab _ hw h1 ihA ihbody =>
    exact .lam (ihA hρ) hwf hlab (fun e he => ihbody e he
      (Valuation.LE.push.2 ⟨hρ, TShape.LE.refl (a := Shape.T e.inp) (hwf.2.2.1 e he).2.2.1⟩))
      hw h1
  | forallE _ hwf hlab _ hw h1 ihA ihbody =>
    exact .forallE (ihA hρ) hwf hlab (fun e he => ihbody e he
      (Valuation.LE.push.2 ⟨hρ, TShape.LE.refl (a := Shape.T e.inp) (hwf.2.2.2.1 e he).2.2.1⟩))
      hw h1
  | natCase_zero _ _ ihM iha => exact .natCase_zero (ihM hρ) (iha hρ)
  | natCase_succ _ hwv heq _ ihM ihb =>
    exact .natCase_succ (ihM hρ) hwv heq
      (ihb (Valuation.LE.push.2 ⟨hρ, TShape.LE.refl (a := Shape.T _) hwv⟩))
  | Y _ hwx _ ihself ihb =>
    exact .Y (ihself hρ) hwx (ihb (Valuation.LE.push.2 ⟨hρ, TShape.LE.refl hwx⟩))
  | id hw h1 => exact .id hw h1
  | refl _ hw h1 ihv => exact .refl (ihv hρ) hw h1
  | tr hw hle _ _ _ _ hwv hvA _ hm' _ ihX iha ihb ihA ihC ihH =>
    exact .tr hw hle (ihX hρ) (iha hρ) (ihb hρ) (ihA hρ) hwv hvA
      (ihC (Valuation.LE.push.2 ⟨hρ, TShape.LE.refl hwv⟩)) hm'
      (fun hr => ihH hr hρ)

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
        TShape.LE Δ m
          (Shape.T (n := n+1) (ShapeS.forallE (A.subst σ) (B.subst σ.lift) d g)) := by
  cases H with
  | bot => exact .inl rfl
  | forallE _ _ _ _ _ h => exact .inr ⟨_, _, _, h⟩

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
theorem Interp.piAtom {Δ Γ σ ρ} {A B : Term} {u v}
    (hA : Δ ⊢ A.subst σ : .sort u) (hB : A.subst σ :: Δ ⊢ B.subst σ.lift : .sort v) :
    Interp Δ Γ (.forallE A B) σ ρ
      (Shape.T (n := 1) (Shape.piAtom (A.subst σ) (B.subst σ.lift))) :=
  .forallE (d := (Shape.bot : Shape 0)) .bot (Shape.WF.piAtom hA hB)
    (fun _ he => absurd he List.not_mem_nil)
    (fun _ he => absurd he List.not_mem_nil)
    (Shape.WF.piAtom hA hB)
    (TShape.LE.T.2 (Shape.LE.refl (Shape.WF.piAtom hA hB)))

/-- And the probe reports: if the atom approximates `⟦forallE A B⟧`, its
label is definitionally the Π's own label.  Π-injectivity is this plus
soundness, with no adequacy in between. -/
theorem Interp.le_piAtom {Δ Γ σ ρ} {A B A' B' : Term}
    (H : Interp Δ Γ (.forallE A B) σ ρ (Shape.T (n := 1) (Shape.piAtom A' B'))) :
    PiLabelEq Δ A' B' (A.subst σ) (B.subst σ.lift) := by
  cases H with
  | forallE _ _ _ _ _ h =>
    have h' := (TShape.LE.def (Nat.succ_le_succ (Nat.zero_le _)) (Nat.le_refl _)).1 h
    rw [show (Shape.T (n := 1) (Shape.piAtom A' B')).2 = Shape.piAtom A' B' from rfl,
      Shape.lift_piAtom, Shape.lift_self] at h'
    exact Shape.piAtom_le_forallE h'

/-! ## Naturality in the stage

The presheaf property, and the reason every shape-level notion had to be
shown stable under `Shape.subst` first.  For the other repo this is
functoriality of `ΩLower` and costs nothing; here the stage is raw syntax,
so it is an induction, and each case is the corresponding `subst` lemma
one level down.

Note the term's own context `Γ` does not move: only the stage does.  That
is what makes this independent of the substitution lemma for terms, which
moves `Γ` and leaves the stage's shape alone. -/

theorem Interp.natural {Δ Γ : List Term} {t : Term} {σ ρ m}
    (H : Interp Δ Γ t σ ρ m) : ∀ {Θ τ}, ⊢ Θ → Ctx.SubstEq Θ τ τ Δ →
      Interp Θ Γ t (σ.comp τ) (ρ.subst τ) (m.subst τ) := by
  induction H with
  | bot => intro Θ τ _ _; simp only [TShape.subst_T, Shape.subst_bot]; exact .bot
  | bvar hw h1 =>
    intro Θ τ hΘ W; exact .bvar (TShape.WF.subst hΘ W hw) (TShape.LE.subst hΘ W h1)
  | sort hw h1 =>
    intro Θ τ hΘ W
    exact .sort (TShape.WF.subst hΘ W hw) (by simpa using TShape.LE.subst hΘ W h1)
  | unit hw h1 =>
    intro Θ τ hΘ W; exact .unit (TShape.WF.subst hΘ W hw) (TShape.LE.subst hΘ W h1)
  | nat hw h1 =>
    intro Θ τ hΘ W; exact .nat (TShape.WF.subst hΘ W hw) (TShape.LE.subst hΘ W h1)
  | zero hw h1 =>
    intro Θ τ hΘ W; exact .zero (TShape.WF.subst hΘ W hw) (TShape.LE.subst hΘ W h1)
  | succ _ hw h1 ihv =>
    intro Θ τ hΘ W
    exact .succ (ihv hΘ W) (TShape.WF.subst hΘ W hw) (TShape.LE.subst hΘ W h1)
  | app _ _ hev hw h1 ihF iha =>
    intro Θ τ hΘ W
    have hev' := Evaluates.subst hΘ W hev
    rw [subst_subst] at hev'
    exact .app (ihF hΘ W) (iha hΘ W) hev' (TShape.WF.subst hΘ W hw)
      (TShape.LE.subst hΘ W h1)
  | lam _ hwf hlab _ hw h1 ihA ihbody =>
    intro Θ τ hΘ W
    refine .lam (ihA hΘ W) (Shape.WF.subst hΘ W hwf) ?_ ?_ (TShape.WF.subst hΘ W hw)
      (TShape.LE.subst hΘ W h1)
    · intro e' he'
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have ⟨u, hu⟩ := hlab e he
      exact ⟨u, by rw [← subst_subst]; exact hu.subst hΘ W⟩
    · intro e' he'
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have := ihbody e he hΘ W
      rwa [Subst.cons_comp, Valuation.subst_push, TShape.subst_T] at this
  | forallE _ hwf hlab _ hw h1 ihA ihbody =>
    intro Θ τ hΘ W
    have hwf' := Shape.WF.subst hΘ W hwf
    have h1' := TShape.LE.subst hΘ W h1
    simp only [TShape.subst_T, Shape.subst, subst_subst, ← Subst.comp_lift] at hwf' h1'
    refine .forallE (ihA hΘ W) hwf' ?_ ?_ (TShape.WF.subst hΘ W hw) h1'
    · intro e' he'
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have ⟨u, hu⟩ := hlab e he
      exact ⟨u, by rw [← subst_subst]; exact hu.subst hΘ W⟩
    · intro e' he'
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have := ihbody e he hΘ W
      rwa [Subst.cons_comp, Valuation.subst_push, TShape.subst_T] at this
  | natCase_zero _ _ ihM iha =>
    intro Θ τ hΘ W; exact .natCase_zero (by simpa using ihM hΘ W) (iha hΘ W)
  | natCase_succ _ hwv heq _ ihM ihb =>
    intro Θ τ hΘ W
    have heq' := heq.subst hΘ W
    rw [subst_subst] at heq'
    refine .natCase_succ (ihM hΘ W) (Shape.WF.subst hΘ W hwv) heq' ?_
    have := ihb hΘ W
    rwa [Subst.cons_comp, Valuation.subst_push, TShape.subst_T] at this
  | Y _ hwx _ ihself ihb =>
    intro Θ τ hΘ W
    refine .Y (ihself hΘ W) (TShape.WF.subst hΘ W hwx) ?_
    have := ihb hΘ W
    rwa [Subst.cons_comp, subst_subst, Valuation.subst_push] at this
  | id hw h1 =>
    intro Θ τ hΘ W
    have := TShape.LE.subst hΘ W h1
    simp only [TShape.subst_T, Shape.subst, subst_subst] at this
    exact .id (TShape.WF.subst hΘ W hw) this
  | refl _ hw h1 ihv =>
    intro Θ τ hΘ W
    exact .refl (ihv hΘ W) (TShape.WF.subst hΘ W hw) (TShape.LE.subst hΘ W h1)
  | tr hw hle _ _ _ _ hwv hvA _ hm' _ ihX iha ihb ihA ihC ihH =>
    intro Θ τ hΘ W
    refine .tr (TShape.WF.subst hΘ W hw) (TShape.LE.subst hΘ W hle) (ihX hΘ W)
      (iha hΘ W) (ihb hΘ W) (ihA hΘ W)
      (TShape.WF.subst hΘ W hwv) (TShape.HasType.subst hΘ W hvA) ?_
      (TShape.HasType.subst hΘ W hm') (fun hr => ihH hr hΘ W)
    have := ihC hΘ W
    rwa [Subst.cons_comp, subst_subst, Valuation.subst_push] at this
