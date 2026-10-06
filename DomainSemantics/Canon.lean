import DomainSemantics.HasType

/-! # Canonical names (§4.7i)

Two hereditary predicates, both relative to a *term*:

* `Shape.CodeCanon Δ T d` — the code `d` **names its type** `T`: a Σ-code
  approximating `T` carries labels `A B` with `T ≡ Σ A B`, hereditarily
  through its domain code and the outputs of its codomain graph (each of
  which names `B[e.tm]`).  Entry-based, with the empty output exempt.
* `Shape.ValCanon Δ t x` — the value `x` **names its own projections**: a
  pair standing for `t` is named `fst t`, its components stand for `fst t`
  and `snd t`; a λ-value's entry inputs stand for the entry labels and its
  outputs for `app t e.tm`; a code-shaped value names its type.

The point of the file is `Shape.ValCanon.defeq`: canonicity moves along a
definitional equality of the subject, **given the code the value is typed
at and that code's canonicity**.  The three doors of §4.7d were all ways
of asking the value to know its own type; here the code knows it, and the
code is what `Dom` already carries. -/

namespace DomainSemantics

/-- A code names its type, hereditarily.  Entry-based: a dead entry (one
whose output is `⊥`) says nothing, since the order can hand it to a
smaller code with any label type. -/
def Shape.CodeCanon (Δ : List Term) : ∀ {n}, Term → Shape n → Prop
  | 0, _, .bot => True
  | 0, T, .sort r => TyEq Δ T (.sort r)
  | _+1, _, .bot => True
  | _+1, T, .sort r => TyEq Δ T (.sort r)
  | _+1, T, .unit r => TyEq Δ T (.unit r)
  | _+1, T, .nat => TyEq Δ T .nat
  | _+1, T, .id r A a b => TyEq Δ T (.id r A a b)
  | _+1, T, .sigma A B d f =>
      TyEq Δ T (.sigma A B) ∧ CodeCanon Δ A d ∧
      ∀ e ∈ f, e.out = .bot ∨ (TyEq Δ e.ty A ∧ CodeCanon Δ (B.inst e.tm) e.out)
  | _+1, T, .forallE A B d f =>
      TyEq Δ T (.forallE A B) ∧ CodeCanon Δ A d ∧
      ∀ e ∈ f, e.out = .bot ∨ (TyEq Δ e.ty A ∧ CodeCanon Δ (B.inst e.tm) e.out)
  | _+1, _, .lam .. => True
  | _+1, _, .pair .. => True
  | _+1, _, .zero => True
  | _+1, _, .succ _ => True
  | _+1, _, .refl _ => True

/-- A value names its own projections. -/
def Shape.ValCanon (Δ : List Term) : ∀ {n}, Term → Shape n → Prop
  | 0, t, s => CodeCanon Δ t s
  | _+1, t, .pair A₀ _ a x y =>
      (Δ ⊢ a ≡ Term.fst t : A₀) ∧ ValCanon Δ (.fst t) x ∧ ValCanon Δ (.snd t) y
  | _+1, t, .lam _ _ g =>
      ∀ e ∈ g, ValCanon Δ e.tm e.inp ∧ ValCanon Δ (.app t e.tm) e.out
  | _+1, _, .zero => True
  | _+1, _, .succ _ => True
  | _+1, _, .refl _ => True
  | _+1, _, .bot => True
  | _+1, t, s@(.sort _) => CodeCanon Δ t s
  | _+1, t, s@(.unit _) => CodeCanon Δ t s
  | _+1, t, s@.nat => CodeCanon Δ t s
  | _+1, t, s@(.id ..) => CodeCanon Δ t s
  | _+1, t, s@(.sigma ..) => CodeCanon Δ t s
  | _+1, t, s@(.forallE ..) => CodeCanon Δ t s

def TShape.CodeCanon (Δ : List Term) (T : Term) (x : TShape) : Prop :=
  Shape.CodeCanon Δ T x.2

def TShape.ValCanon (Δ : List Term) (t : Term) (x : TShape) : Prop :=
  Shape.ValCanon Δ t x.2

@[simp] theorem TShape.CodeCanon.T {Δ : List Term} {T : Term} {n} {s : Shape n} :
    TShape.CodeCanon Δ T (Shape.T s) ↔ Shape.CodeCanon Δ T s := Iff.rfl

@[simp] theorem TShape.ValCanon.T {Δ : List Term} {t : Term} {n} {s : Shape n} :
    TShape.ValCanon Δ t (Shape.T s) ↔ Shape.ValCanon Δ t s := Iff.rfl

@[simp] theorem Shape.CodeCanon.bot {Δ : List Term} {T : Term} {n} :
    Shape.CodeCanon Δ T (Shape.bot (n := n)) := by cases n <;> trivial

@[simp] theorem Shape.ValCanon.bot {Δ : List Term} {t : Term} {n} :
    Shape.ValCanon Δ t (Shape.bot (n := n)) := by
  cases n with
  | zero => exact Shape.CodeCanon.bot (n := 0)
  | succ n => trivial

/-- A sort-shaped code names a sort, at every level. -/
theorem TShape.CodeCanon.sort_iff {Δ : List Term} {T : Term} {k} {j : Bool} :
    TShape.CodeCanon Δ T (Shape.T (n := k) (Shape.sort j)) ↔ TyEq Δ T (.sort j) := by
  cases k <;> exact Iff.rfl

/-- `Interp.lean`'s `Ctx.SubstEq.defeqHead`, needed one file earlier. -/
theorem Ctx.SubstEq.defeqHead' {Γ : List Term} {A A' : Term} {u : Bool} (hΓ : ⊢ Γ)
    (hAA' : Γ ⊢ A ≡ A' : .sort u) : Ctx.SubstEq (A' :: Γ) Subst.id Subst.id (A :: Γ) := by
  refine .cons (Ctx.SubstEq.id hΓ).skip hAA'.hasType.1 ?_
  rw [show A.subst Subst.id.tail = A.lift' (.skip .refl) by
    show A.subst (Subst.id.lift_r (.skip .refl)) = _
    rw [← lift'_subst, subst_id]]
  exact (hAA'.weak' (Ctx.Lift'.skip (A := A') .refl)).symm.defeqDF
    (.bvar Lookup.zero (hAA'.hasType.2.weak' (Ctx.Lift'.skip (A := A') .refl)))

/-- `Interp.lean`'s `IsDefEq.ctx_id`, needed one file earlier. -/
theorem IsDefEq.ctxId {Γ Γ' : List Term} (hΓ' : ⊢ Γ')
    (W : Ctx.SubstEq Γ' Subst.id Subst.id Γ) {e₁ e₂ A : Term}
    (h : Γ ⊢ e₁ ≡ e₂ : A) : Γ' ⊢ e₁ ≡ e₂ : A := by simpa using h.subst hΓ' W

/-- A pair of equal labels makes the two Σ-types definitionally equal. -/
theorem PiLabelEq.sigmaTyEq {Δ : List Term} {A B A' B' : Term} (hΔ : ⊢ Δ)
    (h : PiLabelEq Δ A B A' B') : TyEq Δ (Term.sigma A B) (Term.sigma A' B') :=
  ⟨_, IsDefEq.sigmaDF h.1.choose_spec h.2.choose_spec
    (IsDefEq.ctxId (show ⊢ (A' :: Δ) from ⟨hΔ, _, h.1.choose_spec.hasType.2⟩)
      (Ctx.SubstEq.defeqHead' hΔ h.1.choose_spec) h.2.choose_spec)⟩

/-- The Π twin. -/
theorem PiLabelEq.forallETyEq {Δ : List Term} {A B A' B' : Term} (hΔ : ⊢ Δ)
    (h : PiLabelEq Δ A B A' B') : TyEq Δ (Term.forallE A B) (Term.forallE A' B') :=
  ⟨_, IsDefEq.forallEDF h.1.choose_spec h.2.choose_spec
    (IsDefEq.ctxId (show ⊢ (A' :: Δ) from ⟨hΔ, _, h.1.choose_spec.hasType.2⟩)
      (Ctx.SubstEq.defeqHead' hΔ h.1.choose_spec) h.2.choose_spec)⟩

/-- The instance of a type family at two equal arguments. -/
theorem TyEq.inst {Δ : List Term} (hΔ : ⊢ Δ) {A B B' a a' : Term} {u v : Bool}
    (hA : Δ ⊢ A : .sort u) (hB : A :: Δ ⊢ B ≡ B' : .sort v) (ha : Δ ⊢ a ≡ a' : A) :
    TyEq Δ (B.inst a) (B'.inst a') :=
  ⟨v, hA.instDF hΔ .sort hB ha⟩

/-! ## Transport along the type -/

/-- **A code's canonicity moves along an equality of the type**: only the
head equation mentions the type. -/
theorem Shape.CodeCanon.conv {Δ : List Term} :
    ∀ {n} {T T' : Term} {x : Shape n}, Shape.CodeCanon Δ T x → TyEq Δ T' T →
      Shape.CodeCanon Δ T' x := by
  intro n T T' x hC hT
  cases n with
  | zero => cases x with | bot => trivial | sort r => exact hT.trans hC
  | succ n =>
    cases x with
    | bot | lam | pair | zero | succ | refl => trivial
    | sort | unit | nat | id => exact hT.trans hC
    | sigma A B d f | forallE A B d f => exact ⟨hT.trans hC.1, hC.2.1, hC.2.2⟩

/-! ## Lifting -/

/-- Canonicity is level-independent. -/
theorem Shape.CodeCanon.lift {Δ : List Term} (hΔ : ⊢ Δ) :
    ∀ {n m} (_ : n ≤ m) {T : Term} {s : Shape n},
      Shape.CodeCanon Δ T (s.lift m) ↔ Shape.CodeCanon Δ T s := by
  intro n
  induction n with
  | zero =>
    intro m _ T s
    cases m with
    | zero => rw [Shape.lift_self]
    | succ m => cases s <;> exact Iff.rfl
  | succ n ih =>
    intro m h T s
    let m+1 := m; have h' := Nat.le_of_succ_le_succ h
    have hb (s : Shape n) : s.lift m = .bot ↔ s = .bot :=
      ⟨Shape.lift_eq_bot hΔ h', fun h => h ▸ Shape.lift_bot⟩
    have hf (A B : Term) (f : ShapeFun n) :
        (∀ e ∈ ShapeFun.lift (Shape.lift m) f,
            e.out = .bot ∨ (TyEq Δ e.ty A ∧ Shape.CodeCanon Δ (B.inst e.tm) e.out)) ↔
        (∀ e ∈ f, e.out = .bot ∨ (TyEq Δ e.ty A ∧ Shape.CodeCanon Δ (B.inst e.tm) e.out)) := by
      constructor
      · intro H e he
        have := H ⟨e.ty, e.tm, e.inp.lift m, e.out.lift m⟩ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)
        simpa only [hb, ih h'] using this
      · intro H e' he'
        obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he'
        simpa only [hb, ih h'] using H e he
    cases s with
    | bot | lam | pair | zero | succ | refl | sort | unit | nat | id => exact Iff.rfl
    | sigma A B d f | forallE A B d f =>
      exact and_congr Iff.rfl (and_congr (ih h') (hf A B f))

theorem TShape.CodeCanon.lift_iff {Δ : List Term} (hΔ : ⊢ Δ) {T : Term} {a : TShape} {k}
    (h : a.1 ≤ k) : TShape.CodeCanon Δ T a ↔ Shape.CodeCanon Δ T (a.2.lift k) :=
  (Shape.CodeCanon.lift hΔ h).symm

/-! ## The join -/

/-- **Two canonical codes at one type join canonically.**  The join keeps
the left labels and appends the graphs; the right-hand entries move to
the left labels by `PiLabelEq`, which `Compat` supplies for codes. -/
theorem Shape.CodeCanon.join {Δ : List Term} (hΔ : ⊢ Δ) :
    ∀ {n} {T : Term} {y z : Shape n}, Shape.WF Δ y → Shape.WF Δ z → Shape.Compat Δ y z →
      Shape.CodeCanon Δ T y → Shape.CodeCanon Δ T z → Shape.CodeCanon Δ T (y.join z) := by
  intro n
  induction n with
  | zero =>
    intro T y z _ _ _ hy hz
    cases y with
    | bot => exact hz
    | sort r => cases z <;> exact hy
  | succ n ih =>
    intro T y z hwy hwz hc hy hz
    -- the right-hand entries of a Π/Σ graph, moved to the left labels
    have hent {A B A' B' : Term} {u : Bool} {f' : ShapeFun n} (hl : PiLabelEq Δ A B A' B')
        (hA : Δ ⊢ A : .sort u) (hw' : ShapeFun.WF Δ (Shape.WF Δ) f')
        (hz' : ∀ e ∈ f', e.out = .bot ∨ (TyEq Δ e.ty A' ∧ Shape.CodeCanon Δ (B'.inst e.tm) e.out)) :
        ∀ e ∈ f', e.out = .bot ∨ (TyEq Δ e.ty A ∧ Shape.CodeCanon Δ (B.inst e.tm) e.out) := by
      intro e he
      rcases hz' e he with h | ⟨hty, hC⟩
      · exact .inl h
      · refine .inr ⟨hty.trans (TyEq.symm hl.1), hC.conv ?_⟩
        have htm : Δ ⊢ e.tm : A := (hty.trans (TyEq.symm hl.1)).choose_spec.defeqDF (hw'.1 e he).2.1
        exact TyEq.inst hΔ hA hl.2.choose_spec htm
    cases y with
    | bot => simpa using hz
    | sigma A B d f =>
      cases z with
      | bot => simpa using hy
      | sigma A' B' d' f' =>
        obtain ⟨hl, hcd, _⟩ := hc
        refine ⟨hy.1, ih hwy.2.2.1 hwz.2.2.1 hcd hy.2.1 (hz.2.1.conv hl.1), fun e he => ?_⟩
        rcases List.mem_append.1 he with he | he
        · exact hy.2.2 e he
        · exact hent hl hwy.1.choose_spec hwz.2.2.2 hz.2.2 e he
      | _ => exact absurd hc id
    | forallE A B d f =>
      cases z with
      | bot => simpa using hy
      | forallE A' B' d' f' =>
        obtain ⟨hl, hcd, _⟩ := hc
        refine ⟨hy.1, ih hwy.2.2.1 hwz.2.2.1 hcd hy.2.1 (hz.2.1.conv hl.1), fun e he => ?_⟩
        rcases List.mem_append.1 he with he | he
        · exact hy.2.2 e he
        · exact hent hl hwy.1.choose_spec hwz.2.2.2 hz.2.2 e he
      | _ => exact absurd hc id
    | lam | pair | zero | succ | refl => cases z <;> trivial
    | sort r | unit r | nat | id =>
      cases z with
      | bot => simpa using hy
      | _ => first | exact hy | exact absurd hc id

/-! ## Downward closure -/

/-- **A code's canonicity is downward closed.**  A smaller code has the
same labels up to `PiLabelEq`, a smaller domain, and a graph each of
whose entries is covered by a lookup in the bigger graph — a join of
canonical outputs at a definitionally equal label, lowered. -/
theorem Shape.CodeCanon.mono {Δ : List Term} (hΔ : ⊢ Δ) :
    ∀ {n} {T : Term} {x x' : Shape n}, Shape.LE Δ x' x → Shape.WF Δ x →
      Shape.CodeCanon Δ T x → Shape.CodeCanon Δ T x' := by
  intro n
  induction n with
  | zero =>
    intro T x x' hle _ hC
    cases x' with
    | bot => trivial
    | sort r => cases x with | bot => exact absurd hle id | sort r' => cases hle; exact hC
  | succ n ih =>
    intro T x x' hle hw hC
    -- the covered entries of a smaller Π/Σ graph, at the bigger labels
    have hgraph {A B : Term} {u v : Bool} {f f' : ShapeFun n} (hA : Δ ⊢ A : .sort u)
        (hB : A :: Δ ⊢ B : .sort v)
        (hff : ShapeFun.LE Δ (Shape.LE Δ) (Shape.WF Δ) f' f)
        (hf : ∀ e ∈ f, e.out = .bot ∨ (TyEq Δ e.ty A ∧ Shape.CodeCanon Δ (B.inst e.tm) e.out)) :
        ∀ e ∈ f', e.out = .bot ∨ (TyEq Δ e.ty A ∧ Shape.CodeCanon Δ (B.inst e.tm) e.out) := by
      intro e' he'
      have hwo : ∀ e ∈ f, Shape.WF Δ e.out := fun e he => (hff.2.2.1 e he).2.2.2
      have hev := hff.1 e' he'
      generalize e'.out = w at hev ⊢
      induction hev with
      | bot => exact .inl rfl
      | entry e he hlab _ =>
        rcases hf e he with h | ⟨hty, hC⟩
        · exact .inl h
        · refine .inr ⟨(TyEq.symm hlab.1).trans hty, hC.conv ?_⟩
          have htm : Δ ⊢ e.tm ≡ e'.tm : A := hty.choose_spec.defeqDF hlab.2
          exact TyEq.inst hΔ hA hB htm.symm
      | lower hyz hz ihz =>
        rcases ihz with h | ⟨hty, hC⟩
        · subst h; exact .inl (Shape.le_bot_iff.1 hyz)
        · exact .inr ⟨hty, ih hyz (ShapeFun.Eval.wf hΔ hwo hz) hC⟩
      | @join y z hcyz hy hz ihy ihz =>
        rcases ihy with hy0 | ⟨hty, hCy⟩
        · subst hy0; simpa using ihz
        rcases ihz with hz0 | ⟨_, hCz⟩
        · subst hz0; simpa using Or.inr ⟨hty, hCy⟩
        exact .inr ⟨hty, Shape.CodeCanon.join hΔ (ShapeFun.Eval.wf hΔ hwo hy)
          (ShapeFun.Eval.wf hΔ hwo hz) hcyz hCy hCz⟩
    -- the labels of the smaller code, from the bigger's
    have hmove {A B A' B' : Term} {f' : ShapeFun n} (hl : PiLabelEq Δ A' B' A B)
        (hw' : ShapeFun.WF Δ (Shape.WF Δ) f')
        (hf' : ∀ e ∈ f', e.out = .bot ∨ (TyEq Δ e.ty A ∧ Shape.CodeCanon Δ (B.inst e.tm) e.out)) :
        ∀ e ∈ f', e.out = .bot ∨ (TyEq Δ e.ty A' ∧ Shape.CodeCanon Δ (B'.inst e.tm) e.out) := by
      intro e he
      rcases hf' e he with h | ⟨hty, hCe⟩
      · exact .inl h
      · refine .inr ⟨hty.trans (TyEq.symm hl.1), hCe.conv ?_⟩
        have htm : Δ ⊢ e.tm : A' := (hty.trans (TyEq.symm hl.1)).choose_spec.defeqDF (hw'.1 e he).2.1
        exact TyEq.inst hΔ hl.1.choose_spec.hasType.1 hl.2.choose_spec htm
    cases x with
    | bot => cases Shape.le_bot_iff.1 hle; trivial
    | lam | pair | zero | succ | refl =>
      cases x' <;> first | trivial | exact absurd hle id
    | sort r => rcases Shape.le_sort hle with rfl | rfl <;> [trivial; exact hC]
    | unit r =>
      cases x' with
      | bot => trivial
      | unit r' => cases hle; exact hC
      | _ => exact absurd hle id
    | nat =>
      cases x' with
      | bot => trivial
      | nat => exact hC
      | _ => exact absurd hle id
    | id r A a b =>
      rcases Shape.le_id hle with rfl | ⟨A', a', b', rfl, hl⟩
      · trivial
      · have hl' := IdLabelEq.symm hl
        exact hC.trans ⟨_, IsDefEq.idDF hl'.1.choose_spec hl'.2.1 hl'.2.2⟩
    | sigma A B d f =>
      rcases Shape.le_sigma hle with rfl | ⟨A', B', d', f', rfl, hl, hdd, hff⟩
      · trivial
      · exact ⟨hC.1.trans (PiLabelEq.sigmaTyEq hΔ hl).symm, (ih hdd hw.2.2.1 hC.2.1).conv hl.1,
          hmove hl hff.2.1 (hgraph hw.1.choose_spec hw.2.1.choose_spec hff hC.2.2)⟩
    | forallE A B d f =>
      rcases Shape.le_forallE hle with rfl | ⟨A', B', d', f', rfl, hl, hdd, hff⟩
      · trivial
      · exact ⟨hC.1.trans (PiLabelEq.forallETyEq hΔ hl).symm, (ih hdd hw.2.2.1 hC.2.1).conv hl.1,
          hmove hl hff.2.1 (hgraph hw.1.choose_spec hw.2.1.choose_spec hff hC.2.2)⟩

/-- The total-level order. -/
theorem TShape.CodeCanon.mono {Δ : List Term} (hΔ : ⊢ Δ) {T : Term} {x x' : TShape}
    (hle : TShape.LE Δ x' x) (hw : TShape.WF Δ x) (hC : TShape.CodeCanon Δ T x) :
    TShape.CodeCanon Δ T x' := by
  have h := TShape.LE.def_mp (Nat.le_max_left x'.1 x.1) (Nat.le_max_right x'.1 x.1) hle
  rw [TShape.CodeCanon.lift_iff hΔ (Nat.le_max_right x'.1 x.1)] at hC
  rw [TShape.CodeCanon.lift_iff hΔ (Nat.le_max_left x'.1 x.1)]
  exact Shape.CodeCanon.mono hΔ h ((TShape.WF.def (Nat.le_max_right x'.1 x.1)).1 hw) hC

/-- The total-level join. -/
theorem TShape.CodeCanon.join {Δ : List Term} (hΔ : ⊢ Δ) {T : Term} {y z : TShape}
    (hwy : TShape.WF Δ y) (hwz : TShape.WF Δ z) (hc : TShape.Compat Δ y z)
    (hy : TShape.CodeCanon Δ T y) (hz : TShape.CodeCanon Δ T z) :
    TShape.CodeCanon Δ T (TShape.join y z) := by
  have h1 := Nat.le_max_left y.1 z.1; have h2 := Nat.le_max_right y.1 z.1
  rw [TShape.CodeCanon.lift_iff hΔ (k := max y.1 z.1) (Nat.le_refl _), TShape.join.def h1 h2]
  exact Shape.CodeCanon.join hΔ ((TShape.WF.def h1).1 hwy) ((TShape.WF.def h2).1 hwz)
    ((TShape.Compat.def h1 h2).1 hc) ((TShape.CodeCanon.lift_iff hΔ h1).1 hy)
    ((TShape.CodeCanon.lift_iff hΔ h2).1 hz)

/-! ## The lookup

A lookup in a canonical code's codomain graph at a well-typed query is a
canonical code of the family at that query.  This is the query-based
reading of the entry-based condition; it is a theorem rather than the
definition because the definition has to survive substitution, and an
entry that is dead at one stage can be live at a later one. -/
theorem TShape.CodeCanon.lookup {Δ : List Term} (hΔ : ⊢ Δ) {n} {A B q : Term} {u v : Bool}
    {f : ShapeFun n} (hw : ShapeFun.WF Δ (Shape.WF Δ) f)
    (hf : ∀ e ∈ f, e.out = .bot ∨ (TyEq Δ e.ty A ∧ Shape.CodeCanon Δ (B.inst e.tm) e.out))
    (hA : Δ ⊢ A : .sort u) (hB : A :: Δ ⊢ B : .sort v) {x : TShape} :
    ∀ {c : TShape}, TEvaluates Δ f A q x c → TShape.CodeCanon Δ (B.inst q) c := by
  intro c h
  have hwo : ∀ e ∈ f, TShape.WF Δ e.out.T := fun e he => (hw.1 e he).2.2.2
  induction h with
  | bot => exact Shape.CodeCanon.bot
  | entry e he hlab _ =>
    rcases hf e he with h0 | ⟨hty, hC⟩
    · show Shape.CodeCanon Δ _ e.out; rw [h0]; exact Shape.CodeCanon.bot
    · refine hC.conv ?_
      have htm : Δ ⊢ e.tm ≡ q : A := hty.choose_spec.defeqDF hlab.2
      exact TyEq.inst hΔ hA hB htm.symm
  | lower hle hz ih => exact TShape.CodeCanon.mono hΔ hle (TEvaluates.wf hΔ hwo hz) ih
  | join hc hy hz ihy ihz =>
    exact TShape.CodeCanon.join hΔ (TEvaluates.wf hΔ hwo hy) (TEvaluates.wf hΔ hwo hz) hc ihy ihz

/-! ## The transport, along the subject -/

/-- **Canonicity moves along a definitional equality of the subject**,
given the code the value is hereditarily typed at and that code's own
canonicity.  The code knows the type (`T ≡ Σ A B`), so `fstDF`/`sndDF`/
`appDF` apply; the sub-values are typed at the code's sub-codes, which
are canonical for the sub-types; and the recursion is on the value. -/
theorem Shape.ValCanon.defeq {Δ : List Term} (hΔ : ⊢ Δ) :
    ∀ {n} {x : Shape n} {d : TShape} {T t t' : Term},
      TShape.Dom Δ d x.T → TShape.CodeCanon Δ T d → Shape.ValCanon Δ t x →
      (Δ ⊢ t ≡ t' : T) → Shape.ValCanon Δ t' x := by
  intro n
  induction n with
  | zero =>
    intro x d T t t' hD hC hV ht
    cases x with
    | bot => trivial
    | sort r =>
      cases hD.hasType with
      | sort =>
        have hT : TyEq Δ T (.sort true) := TShape.CodeCanon.sort_iff.1 hC
        exact Shape.CodeCanon.conv (n := 0) hV ⟨_, (hT.choose_spec.defeqDF ht).symm⟩
  | succ n ih =>
    intro x d T t t' hD hC hV ht
    -- a code-shaped value: its type is a sort, read off the code
    have hcode {k : Nat} {j : Bool} (hd : d = Shape.T (n := k) (Shape.sort j))
        (hV' : Shape.CodeCanon Δ t x) : Shape.CodeCanon Δ t' x := by
      subst hd
      have hT : TyEq Δ T (.sort j) := TShape.CodeCanon.sort_iff.1 hC
      exact hV'.conv ⟨_, (hT.choose_spec.defeqDF ht).symm⟩
    cases x with
    | bot | zero | succ | refl => trivial
    | sort r => cases hD.hasType with | sort => exact hcode rfl hV
    | unit r => cases hD.hasType with | unit => exact hcode rfl hV
    | nat => cases hD.hasType with | nat => exact hcode rfl hV
    | id r A a b => cases hD.hasType with | id => exact hcode rfl hV
    | forallE A B d f => cases hD.hasType with | forallE => exact hcode rfl hV
    | sigma A B d f => cases hD.hasType with | sigma => exact hcode rfl hV
    | pair A₀ B₀ a x y =>
      cases hD.hasType with
      | @pair _ _ _ _ _ _ _ f A B d _ _ _ _ _ hws _ _ _ _ hA₀A
      obtain ⟨c, hx₁, hev, hy₁⟩ := TShape.Dom.sg_inv hD
      obtain ⟨hT, hCd, hCf⟩ := hC
      obtain ⟨hname, hVx, hVy⟩ := hV
      have ht' : Δ ⊢ t ≡ t' : .sigma A B := hT.choose_spec.defeqDF ht
      have hfst : Δ ⊢ .fst t ≡ .fst t' : A := IsDefEq.fstDF₀ hΔ ht'
      have hsnd : Δ ⊢ .snd t ≡ .snd t' : B.inst (.fst t) := IsDefEq.sndDF₀ hΔ ht'
      have hA := hws.1.choose_spec
      have hB := hws.2.1.choose_spec
      have hname' : Δ ⊢ a ≡ .fst t : A := hA₀A.choose_spec.defeqDF hname
      refine ⟨hname.trans (hA₀A.choose_spec.symm.defeqDF hfst), ih hx₁ hCd hVx hfst, ?_⟩
      refine ih hy₁ (TShape.CodeCanon.lookup hΔ hws.2.2.2 hCf hA hB hev) hVy ?_
      exact (TyEq.inst hΔ hA hB hname'.symm).choose_spec.defeqDF hsnd
    | lam A₀ B₀ g =>
      cases hD.hasType with
      | @lam _ _ _ _ _ _ f A B d _ _ _ hwl hwf _ _ _ _ hA₀A
      cases hD with
      | base hnb _ => exact absurd trivial hnb
      | @pi _ _ _ _ _ _ cs _ hent _ hev hout
      obtain ⟨hT, hCd, hCf⟩ := hC
      have hA := hwf.1.choose_spec
      have hB := hwf.2.1.choose_spec
      intro e he
      obtain ⟨hVin, hVout⟩ := hV e he
      refine ⟨hVin, ?_⟩
      -- the entry's code, from `Dom`'s per-entry list
      have hmem : (⟨e.ty, e.tm, e.inp.T, e.out.T⟩ : Entry TShape) ∈ cs.map (·.1) := by
        rw [← hent]
        simp only [TShape.entries, Shape.graph, List.mem_map]
        exact ⟨e, he, rfl⟩
      obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hmem
      have hevp := hev p hp; have houtp := hout p hp
      simp only [hpe] at hevp houtp
      have htyA : TyEq Δ e.ty A := (hwl.2.2.2 e he).trans hA₀A
      have htm : Δ ⊢ e.tm : A := htyA.choose_spec.defeqDF (hwl.2.2.1.1 e he).2.1
      have hevA : TEvaluates Δ f A e.tm e.inp.T p.2 :=
        TEvaluates.mono hΔ ⟨htyA, (hwl.2.2.1.1 e he).2.1⟩
          (TShape.LE.refl (a := e.inp.T) (hwl.2.2.1.1 e he).2.2.1) hevp
      have happ : Δ ⊢ .app t e.tm ≡ .app t' e.tm : B.inst e.tm :=
        IsDefEq.appDF₀ hΔ (hT.choose_spec.defeqDF ht) htm
      exact ih houtp (TShape.CodeCanon.lookup hΔ hwf.2.2.2 hCf hA hB hevA) hVout happ

theorem TShape.ValCanon.defeq {Δ : List Term} (hΔ : ⊢ Δ) {x d : TShape} {T t t' : Term}
    (hD : TShape.Dom Δ d x) (hC : TShape.CodeCanon Δ T d) (hV : TShape.ValCanon Δ t x)
    (ht : Δ ⊢ t ≡ t' : T) : TShape.ValCanon Δ t' x :=
  Shape.ValCanon.defeq hΔ (x := x.2) hD hC hV ht

/-! ## Substitution

The other horn of §4.7g: the entry-based conditions substitute, because
entries map and the subject's projections commute with substitution
syntactically.  No typing is consulted. -/

theorem Shape.CodeCanon.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) :
    ∀ {n} {T : Term} {s : Shape n}, Shape.CodeCanon Δ T s →
      Shape.CodeCanon Θ (T.subst τ) (s.subst τ) := by
  intro n
  induction n with
  | zero =>
    intro T s h
    cases s with
    | bot => trivial
    | sort r => exact TyEq.subst hΘ W h
  | succ n ih =>
    intro T s h
    have hf {A B : Term} {f : ShapeFun n}
        (hf : ∀ e ∈ f, e.out = .bot ∨ (TyEq Δ e.ty A ∧ Shape.CodeCanon Δ (B.inst e.tm) e.out)) :
        ∀ e ∈ ShapeFun.subst (Shape.subst · τ) τ f,
          e.out = .bot ∨ (TyEq Θ e.ty (A.subst τ) ∧
            Shape.CodeCanon Θ ((B.subst τ.lift).inst e.tm) e.out) := by
      intro e' he'
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      rcases hf e he with h0 | ⟨hty, hC⟩
      · exact .inl (by simp [h0])
      · refine .inr ⟨TyEq.subst hΘ W hty, ?_⟩
        have := ih hC
        rwa [subst_inst] at this
    cases s with
    | bot | lam | pair | zero | succ | refl => trivial
    | sort r | unit r | nat | id => exact TyEq.subst hΘ W h
    | sigma A B d f | forallE A B d f => exact ⟨TyEq.subst hΘ W h.1, ih h.2.1, hf h.2.2⟩

theorem Shape.ValCanon.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) :
    ∀ {n} {t : Term} {s : Shape n}, Shape.ValCanon Δ t s →
      Shape.ValCanon Θ (t.subst τ) (s.subst τ) := by
  intro n
  induction n with
  | zero => intro t s h; exact Shape.CodeCanon.subst hΘ W (n := 0) h
  | succ n ih =>
    intro t s h
    cases s with
    | bot | zero | succ | refl => trivial
    | sort | unit | nat | id | sigma | forallE => exact Shape.CodeCanon.subst hΘ W h
    | pair A₀ B₀ a x y =>
      obtain ⟨hname, hx, hy⟩ := h
      exact ⟨IsDefEq.subst hΘ W hname, ih hx, ih hy⟩
    | lam A₀ B₀ g =>
      intro e' he'
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      obtain ⟨hin, hout⟩ := h e he
      exact ⟨ih hin, ih hout⟩

theorem TShape.CodeCanon.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {T : Term} {x : TShape} (h : TShape.CodeCanon Δ T x) :
    TShape.CodeCanon Θ (T.subst τ) (x.subst τ) :=
  Shape.CodeCanon.subst hΘ W h

theorem TShape.ValCanon.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {t : Term} {x : TShape} (h : TShape.ValCanon Δ t x) :
    TShape.ValCanon Θ (t.subst τ) (x.subst τ) :=
  Shape.ValCanon.subst hΘ W h
