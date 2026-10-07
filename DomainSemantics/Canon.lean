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

/-- A code names its type, hereditarily.  Entry-based, and a dead entry
(one whose output is `⊥`) says nothing of its own accord: `CodeCanon` at
`⊥` is `True`, so no exemption has to be written into the Π and Σ
clauses. -/
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
      ∀ e ∈ f, CodeCanon Δ (B.inst e.tm) e.out
  | _+1, T, .forallE A B d f =>
      TyEq Δ T (.forallE A B) ∧ CodeCanon Δ A d ∧
      ∀ e ∈ f, CodeCanon Δ (B.inst e.tm) e.out
  | _+1, _, .lam .. => True
  | _+1, _, .pair .. => True
  | _+1, _, .zero => True
  | _+1, _, .succ _ => True
  | _+1, _, .refl => True

/-- A value names its own projections. -/
def Shape.ValCanon (Δ : List Term) : ∀ {n}, Term → Shape n → Prop
  | 0, t, s => CodeCanon Δ t s
  | _+1, t, .pair A₀ a x y =>
      (Δ ⊢ a ≡ Term.fst t : A₀) ∧ ValCanon Δ (.fst t) x ∧ ValCanon Δ (.snd t) y
  | _+1, t, .lam _ g =>
      ∀ e ∈ g, ValCanon Δ e.tm e.inp ∧ ValCanon Δ (.app t e.tm) e.out
  | _+1, _, .zero => True
  | _+1, _, .succ _ => True
  | _+1, _, .refl => True
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
theorem PiLabelEq.sigmaTyEq {Δ : List Term} {A B A' B' : Term} (hΔ : ⊢ Δ) :
    PiLabelEq Δ A B A' B' → TyEq Δ (.sigma A B) (.sigma A' B')
  | ⟨⟨_, h1⟩, _, h2⟩ =>
    ⟨_, .sigmaDF h1 h2 (.ctxId (Γ' := A' :: Δ) ⟨hΔ, _, h1.hasType.2⟩ (.defeqHead' hΔ h1) h2)⟩

/-- The Π twin. -/
theorem PiLabelEq.forallETyEq {Δ : List Term} {A B A' B' : Term} (hΔ : ⊢ Δ) :
    PiLabelEq Δ A B A' B' → TyEq Δ (.forallE A B) (.forallE A' B')
  | ⟨⟨_, h1⟩, _, h2⟩ =>
    ⟨_, .forallEDF h1 h2 (.ctxId (Γ' := A' :: Δ) ⟨hΔ, _, h1.hasType.2⟩ (.defeqHead' hΔ h1) h2)⟩

/-- The instance of a type family at two equal arguments. -/
theorem TyEq.inst {Δ : List Term} (hΔ : ⊢ Δ) {A B B' a a' : Term} {u v : Bool}
    (hA : Δ ⊢ A : .sort u) (hB : A :: Δ ⊢ B ≡ B' : .sort v) (ha : Δ ⊢ a ≡ a' : A) :
    TyEq Δ (B.inst a) (B'.inst a') :=
  ⟨v, hA.instDF hΔ .sort hB ha⟩

/-! ## Transport along the type -/

/-- The deep condition implies the shallow one: they agree at the head. -/
theorem Shape.CodeCanon.shallow : ∀ {n} {Δ : List Term} {T : Term} {s : Shape n},
    Shape.CodeCanon Δ T s → Shape.CodeCanonS Δ T s
  | 0, _, _, s => by cases s <;> intro h <;> first | trivial | exact h
  | _+1, _, _, s => by cases s <;> intro h <;> first | trivial | exact h | exact h.1

theorem TShape.CodeCanon.shallow {Δ : List Term} {T : Term} {x : TShape}
    (h : TShape.CodeCanon Δ T x) : Shape.CodeCanonS Δ T x.2 := Shape.CodeCanon.shallow h

/-- **A code's canonicity moves along an equality of the type**: only the
head equation mentions the type. -/
theorem Shape.CodeCanon.conv {Δ : List Term} {n} {T T' : Term} {x : Shape n}
    (hC : Shape.CodeCanon Δ T x) (hT : TyEq Δ T' T) : Shape.CodeCanon Δ T' x := by
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
            Shape.CodeCanon Δ (B.inst e.tm) e.out) ↔
        (∀ e ∈ f, Shape.CodeCanon Δ (B.inst e.tm) e.out) := by
      constructor
      · intro H e he
        have := H ⟨e.tm, e.inp.lift m, e.out.lift m⟩ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)
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
        (hA : Δ ⊢ A : .sort u) (hw' : ShapeFun.WF Δ A' (Shape.WF Δ) f')
        (hz' : ∀ e ∈ f', Shape.CodeCanon Δ (B'.inst e.tm) e.out) :
        ∀ e ∈ f', Shape.CodeCanon Δ (B.inst e.tm) e.out := by
      intro e he
      have htm : Δ ⊢ e.tm : A := ((hw'.retype (TyEq.symm hl.1)).1 e he).2.1
      exact (hz' e he).conv (TyEq.inst hΔ hA hl.2.choose_spec htm)
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
        · exact hent hl hwy.1.choose_spec hwz.2.2.2.1 hz.2.2 e he
      | _ => exact absurd hc id
    | forallE A B d f =>
      cases z with
      | bot => simpa using hy
      | forallE A' B' d' f' =>
        obtain ⟨hl, hcd, _⟩ := hc
        refine ⟨hy.1, ih hwy.2.2.1 hwz.2.2.1 hcd hy.2.1 (hz.2.1.conv hl.1), fun e he => ?_⟩
        rcases List.mem_append.1 he with he | he
        · exact hy.2.2 e he
        · exact hent hl hwy.1.choose_spec hwz.2.2.2.1 hz.2.2 e he
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
        (hff : ShapeFun.LE Δ (Shape.LE Δ) (Shape.WF Δ) A f' f)
        (hf : ∀ e ∈ f, Shape.CodeCanon Δ (B.inst e.tm) e.out) :
        ∀ e ∈ f', Shape.CodeCanon Δ (B.inst e.tm) e.out := by
      intro e' he'
      have hwo : ∀ e ∈ f, Shape.WF Δ e.out := fun e he => (hff.2.2.1 e he).2.2.2
      have hev := hff.1 e' he'
      generalize e'.out = w at hev ⊢
      induction hev with
      | bot => exact Shape.CodeCanon.bot
      | entry e he hlab _ => exact (hf e he).conv (TyEq.inst hΔ hA hB hlab.2.symm)
      | lower hyz hz ihz => exact ih hyz (ShapeFun.Eval.wf hΔ hwo hz) ihz
      | @join y z hcyz hy hz ihy ihz =>
        exact Shape.CodeCanon.join hΔ (ShapeFun.Eval.wf hΔ hwo hy)
          (ShapeFun.Eval.wf hΔ hwo hz) hcyz ihy ihz
    -- the labels of the smaller code, from the bigger's
    have hmove {A B A' B' : Term} {f' : ShapeFun n} (hl : PiLabelEq Δ A' B' A B)
        (hw' : ShapeFun.WF Δ A' (Shape.WF Δ) f')
        (hf' : ∀ e ∈ f', Shape.CodeCanon Δ (B.inst e.tm) e.out) :
        ∀ e ∈ f', Shape.CodeCanon Δ (B'.inst e.tm) e.out := by
      intro e he
      exact (hf' e he).conv
        (TyEq.inst hΔ hl.1.choose_spec.hasType.1 hl.2.choose_spec (hw'.1 e he).2.1)
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
          hmove hl hff.2.1 (hgraph hw.1.choose_spec hw.2.1.choose_spec (hff.retype hl.1) hC.2.2)⟩
    | forallE A B d f =>
      rcases Shape.le_forallE hle with rfl | ⟨A', B', d', f', rfl, hl, hdd, hff⟩
      · trivial
      · exact ⟨hC.1.trans (PiLabelEq.forallETyEq hΔ hl).symm, (ih hdd hw.2.2.1 hC.2.1).conv hl.1,
          hmove hl hff.2.1 (hgraph hw.1.choose_spec hw.2.1.choose_spec (hff.retype hl.1) hC.2.2)⟩

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
    {f : ShapeFun n} (hw : ShapeFun.WF Δ A (Shape.WF Δ) f)
    (hf : ∀ e ∈ f, Shape.CodeCanon Δ (B.inst e.tm) e.out)
    (hA : Δ ⊢ A : .sort u) (hB : A :: Δ ⊢ B : .sort v) {x : TShape} :
    ∀ {c : TShape}, TEvaluates Δ f A q x c → TShape.CodeCanon Δ (B.inst q) c := by
  intro c h
  have hwo : ∀ e ∈ f, TShape.WF Δ e.out.T := fun e he => (hw.1 e he).2.2.2
  induction h with
  | bot => exact Shape.CodeCanon.bot
  | entry e he hlab _ =>
    exact (hf e he).conv (TyEq.inst hΔ hA hB hlab.2.symm)
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
    | pair A₀ a x y =>
      cases hD.hasType with
      | @pair _ _ _ _ _ _ f A B d _ _ _ _ _ hws _ _ _ _ hA₀A
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
      refine ih hy₁ (TShape.CodeCanon.lookup hΔ hws.2.2.2.1 hCf hA hB hev) hVy ?_
      exact (TyEq.inst hΔ hA hB hname'.symm).choose_spec.defeqDF hsnd
    | lam A₀ g =>
      cases hD.hasType with
      | @lam _ _ _ _ _ f A B d _ _ _ hwl hwf _ _ _ _ hA₀A
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
      have hmem : (⟨e.tm, e.inp.T, e.out.T⟩ : Entry TShape) ∈ cs.map (·.1) := by
        rw [← hent]
        simp only [TShape.entries, Shape.graph, List.mem_map]
        exact ⟨e, he, rfl⟩
      obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hmem
      have hevp := hev p hp; have houtp := hout p hp
      simp only [hpe] at hevp houtp
      have htm : Δ ⊢ e.tm : A := hA₀A.choose_spec.defeqDF (hwl.2.2.1.1 e he).2.1
      have happ : Δ ⊢ .app t e.tm ≡ .app t' e.tm : B.inst e.tm :=
        IsDefEq.appDF₀ hΔ (hT.choose_spec.defeqDF ht) htm
      exact ih houtp (TShape.CodeCanon.lookup hΔ hwf.2.2.2.1 hCf hA hB hevp) hVout happ

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
    have hf {B : Term} {f : ShapeFun n}
        (hf : ∀ e ∈ f, Shape.CodeCanon Δ (B.inst e.tm) e.out) :
        ∀ e ∈ ShapeFun.subst (Shape.subst · τ) τ f,
          Shape.CodeCanon Θ ((B.subst τ.lift).inst e.tm) e.out := by
      intro e' he'
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have := ih (hf e he)
      rw [subst_inst] at this
      exact this
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
    | pair A₀ a x y =>
      obtain ⟨hname, hx, hy⟩ := h
      exact ⟨IsDefEq.subst hΘ W hname, ih hx, ih hy⟩
    | lam A₀ g =>
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

/-! ## Values: the bridge, lifting and the join -/

/-- **A canonical value is a canonical code**, read as a code: on code
heads the two predicates agree, and on value heads `CodeCanon` asks
nothing.  So the saturated approximants of a *type* name it. -/
theorem Shape.ValCanon.toCode {Δ : List Term} :
    ∀ {n} {t : Term} {x : Shape n}, Shape.ValCanon Δ t x → Shape.CodeCanon Δ t x := by
  intro n t x h
  cases n with
  | zero => exact h
  | succ n => cases x <;> first | exact h | trivial

/-- Numerals carry no names. -/
theorem Shape.ValCanon.of_numeral {Δ : List Term} {t : Term} :
    ∀ {n} {x : Shape n}, Shape.IsNumeral x → Shape.ValCanon Δ t x := by
  intro n x h
  cases h <;> first | exact Shape.ValCanon.bot | trivial

theorem Shape.ValCanon.lift {Δ : List Term} (hΔ : ⊢ Δ) :
    ∀ {n m} (_ : n ≤ m) {t : Term} {s : Shape n},
      Shape.ValCanon Δ t (s.lift m) ↔ Shape.ValCanon Δ t s := by
  intro n
  induction n with
  | zero =>
    intro m _ t s
    cases m with
    | zero => rw [Shape.lift_self]
    | succ m => cases s <;> exact Iff.rfl
  | succ n ih =>
    intro m h t s
    let m+1 := m; have h' := Nat.le_of_succ_le_succ h
    cases s with
    | bot | zero | succ | refl => exact Iff.rfl
    | sort r =>
      exact (Shape.CodeCanon.lift hΔ h (T := t) (s := (ShapeS.sort r : Shape (n+1))) :)
    | unit r =>
      exact (Shape.CodeCanon.lift hΔ h (T := t) (s := (ShapeS.unit r : Shape (n+1))) :)
    | nat => exact (Shape.CodeCanon.lift hΔ h (T := t) (s := (ShapeS.nat : Shape (n+1))) :)
    | id r A a b =>
      exact (Shape.CodeCanon.lift hΔ h (T := t) (s := (ShapeS.id r A a b : Shape (n+1))) :)
    | sigma A B d f =>
      exact (Shape.CodeCanon.lift hΔ h (T := t) (s := (ShapeS.sigma A B d f : Shape (n+1))) :)
    | forallE A B d f =>
      exact (Shape.CodeCanon.lift hΔ h (T := t) (s := (ShapeS.forallE A B d f : Shape (n+1))) :)
    | pair A a x y => exact and_congr Iff.rfl (and_congr (ih h') (ih h'))
    | lam A f =>
      constructor
      · intro H e he
        have := H ⟨e.tm, e.inp.lift m, e.out.lift m⟩ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)
        exact ⟨(ih h').1 this.1, (ih h').1 this.2⟩
      · intro H e' he'
        obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he'
        exact ⟨(ih h').2 (H e he).1, (ih h').2 (H e he).2⟩

theorem TShape.ValCanon.lift_iff {Δ : List Term} (hΔ : ⊢ Δ) {t : Term} {a : TShape} {k}
    (h : a.1 ≤ k) : TShape.ValCanon Δ t a ↔ Shape.ValCanon Δ t (a.2.lift k) :=
  (Shape.ValCanon.lift hΔ h).symm

/-- **Two canonical values of one term join canonically**: the join keeps
the left name, joins components and appends graphs. -/
theorem Shape.ValCanon.join {Δ : List Term} (hΔ : ⊢ Δ) :
    ∀ {n} {t : Term} {y z : Shape n}, Shape.WF Δ y → Shape.WF Δ z → Shape.Compat Δ y z →
      Shape.ValCanon Δ t y → Shape.ValCanon Δ t z → Shape.ValCanon Δ t (y.join z) := by
  intro n
  induction n with
  | zero => intro t y z hwy hwz hc hy hz; exact Shape.CodeCanon.join hΔ hwy hwz hc hy hz
  | succ n ih =>
    intro t y z hwy hwz hc hy hz
    cases y with
    | bot => simpa using hz
    | pair A a x₁ y₁ =>
      cases z with
      | bot => simpa using hy
      | pair A' a' x₂ y₂ =>
        exact ⟨hy.1, ih hwy.2.2.2.1 hwz.2.2.2.1 hc.2.2.1 hy.2.1 hz.2.1,
          ih hwy.2.2.2.2 hwz.2.2.2.2 hc.2.2.2 hy.2.2 hz.2.2⟩
      | _ => exact absurd hc id
    | lam A f =>
      cases z with
      | bot => simpa using hy
      | lam A' f' =>
        intro e he
        rcases List.mem_append.1 he with he | he
        · exact hy e he
        · exact hz e he
      | _ => exact absurd hc id
    | zero | succ | refl =>
      cases z with
      | bot => simpa using hy
      | _ => first | trivial | exact absurd hc id
    | sort | unit | nat | id | sigma | forallE =>
      cases z with
      | bot => simpa using hy
      | _ =>
        first
        | exact absurd hc id
        | exact Shape.CodeCanon.join hΔ hwy hwz hc hy hz

theorem TShape.ValCanon.join {Δ : List Term} (hΔ : ⊢ Δ) {t : Term} {y z : TShape}
    (hwy : TShape.WF Δ y) (hwz : TShape.WF Δ z) (hc : TShape.Compat Δ y z)
    (hy : TShape.ValCanon Δ t y) (hz : TShape.ValCanon Δ t z) :
    TShape.ValCanon Δ t (TShape.join y z) := by
  have h1 := Nat.le_max_left y.1 z.1; have h2 := Nat.le_max_right y.1 z.1
  rw [TShape.ValCanon.lift_iff hΔ (k := max y.1 z.1) (Nat.le_refl _), TShape.join.def h1 h2]
  exact Shape.ValCanon.join hΔ ((TShape.WF.def h1).1 hwy) ((TShape.WF.def h2).1 hwz)
    ((TShape.Compat.def h1 h2).1 hc) ((TShape.ValCanon.lift_iff hΔ h1).1 hy)
    ((TShape.ValCanon.lift_iff hΔ h2).1 hz)

theorem TShape.ValCanon.toCode {Δ : List Term} {t : Term} {x : TShape}
    (h : TShape.ValCanon Δ t x) : TShape.CodeCanon Δ t x := Shape.ValCanon.toCode h

theorem TShape.CodeCanon.conv {Δ : List Term} {T T' : Term} {x : TShape}
    (h : TShape.CodeCanon Δ T x) (hT : TyEq Δ T' T) : TShape.CodeCanon Δ T' x :=
  Shape.CodeCanon.conv h hT

@[simp] theorem TShape.CodeCanon.bot {Δ : List Term} {T : Term} {n} :
    TShape.CodeCanon Δ T (Shape.T (n := n) Shape.bot) := Shape.CodeCanon.bot

theorem TShape.ValCanon.of_bot {Δ : List Term} {t : Term} {x : TShape} (h : x.2 = Shape.bot) :
    TShape.ValCanon Δ t x := by
  obtain ⟨n, s⟩ := x
  show Shape.ValCanon Δ t s
  rw [show s = Shape.bot from h]; exact Shape.ValCanon.bot

/-! ## The slot condition

The three facts above never travel alone.  Wherever the model records
what a valuation slot (or a dominator, or a transported value) *is*, it
records all three: the shape is hereditarily typed at a code, the code
names the type, and the shape names the term.  `Slot` is that bundle.

Its point is `Slot.defeq`: moving the name along a definitional equality
needs the other two, and with them bundled the transport takes no extra
arguments.  That is the code-indexed form of canonicity, got by
conjunction rather than by a new recursion. -/

/-- `x` is hereditarily typed at the code `d`, which names the type `T`,
and `x` names the term `t`. -/
def TShape.Slot (Δ : List Term) (T : Term) (d : TShape) (t : Term) (x : TShape) : Prop :=
  TShape.Dom Δ d x ∧ TShape.CodeCanon Δ T d ∧ TShape.ValCanon Δ t x

theorem TShape.Slot.dom {Δ : List Term} {T t : Term} {d x : TShape}
    (h : TShape.Slot Δ T d t x) : TShape.Dom Δ d x := h.1

theorem TShape.Slot.code {Δ : List Term} {T t : Term} {d x : TShape}
    (h : TShape.Slot Δ T d t x) : TShape.CodeCanon Δ T d := h.2.1

theorem TShape.Slot.val {Δ : List Term} {T t : Term} {d x : TShape}
    (h : TShape.Slot Δ T d t x) : TShape.ValCanon Δ t x := h.2.2

theorem TShape.Slot.hasType {Δ : List Term} {T t : Term} {d x : TShape}
    (h : TShape.Slot Δ T d t x) : TShape.HasType Δ x d := h.1.hasType

/-- **The transport, with nothing to pass in.**  This is what the bundle
is for: `ValCanon.defeq` needs the code and its naming, and here they are
the slot's own fields. -/
theorem TShape.Slot.defeq {Δ : List Term} (hΔ : ⊢ Δ) {T t t' : Term} {d x : TShape}
    (h : TShape.Slot Δ T d t x) (ht : Δ ⊢ t ≡ t' : T) : TShape.Slot Δ T d t' x :=
  ⟨h.1, h.2.1, TShape.ValCanon.defeq hΔ h.1 h.2.1 h.2.2 ht⟩

/-- Conversion in the type: the code's naming is the only field that sees it. -/
theorem TShape.Slot.conv {Δ : List Term} {T T' t : Term} {d x : TShape}
    (h : TShape.Slot Δ T d t x) (hT : TyEq Δ T' T) : TShape.Slot Δ T' d t x :=
  ⟨h.1, h.2.1.conv hT, h.2.2⟩

theorem TShape.Slot.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {T t : Term} {d x : TShape} (h : TShape.Slot Δ T d t x) :
    TShape.Slot Θ (T.subst τ) (d.subst τ) (t.subst τ) (x.subst τ) :=
  ⟨h.1.subst hΘ W, h.2.1.subst hΘ W, h.2.2.subst hΘ W⟩

/-! ## Merging the slot condition into one recursion

`Slot` above is the conjunction.  `Named` below is the same thing stated
as one relation, by the same induction on the code that `TShape.Dom`
uses, with the naming conjuncts folded into its clauses.  The two agree
(`Named.iff`), which is what says the merge is sound; what it costs is
that `Dom`'s term argument has to be supplied at every site.

Three observations make the fold go through:

* at a code that only filters, a shape typed there is never a `lam` or a
  `pair`, so the only naming left is a code naming its type, and
  `CodeCanon` is `True` on the numerals and on `refl`;
* at a Π, an entry's *input* names the entry's own label term and its
  *output* names the application — exactly `ValCanon`'s `lam` clause;
* at a Σ, the pair's name is its first projection and the components
  name the projections, with the equation read at the Σ's domain label
  rather than the pair shape's, the two being definitionally equal
  because `HasType.pair` says so. -/

/-- `x` is hereditarily typed at the code `d` **and names `t`**. -/
inductive TShape.Named (Δ : List Term) : TShape → Term → TShape → Prop where
  | base {d x : TShape} {t : Term} : ¬ d.IsBinder → TShape.HasType Δ x d →
    TShape.CodeCanon Δ t x → Named Δ d t x
  | pi {n} {A B t : Term} {d : Shape n} {f : ShapeFun n} {x : TShape}
      {cs : List (Entry TShape × TShape)} :
    TShape.HasType Δ x (Shape.T (n := n+1) (ShapeS.forallE A B d f)) →
    x.entries = cs.map (·.1) →
    (∀ p ∈ cs, Named Δ d.T p.1.tm p.1.inp) →
    (∀ p ∈ cs, TEvaluates Δ f A p.1.tm p.1.inp p.2) →
    (∀ p ∈ cs, Named Δ p.2 (Term.app t p.1.tm) p.1.out) →
    Named Δ (Shape.T (n := n+1) (ShapeS.forallE A B d f)) t x
  | sg {n} {A B t : Term} {d : Shape n} {f : ShapeFun n} {x : TShape}
      {ps : Option (Term × TShape × TShape)} {c : TShape} :
    TShape.HasType Δ x (Shape.T (n := n+1) (ShapeS.sigma A B d f)) →
    x.pairParts = ps →
    (∀ p ∈ ps, Δ ⊢ p.1 ≡ Term.fst t : A) →
    (∀ p ∈ ps, Named Δ d.T (Term.fst t) p.2.1) →
    (∀ p ∈ ps, TEvaluates Δ f A p.1 p.2.1 c) →
    (∀ p ∈ ps, Named Δ c (Term.snd t) p.2.2) →
    Named Δ (Shape.T (n := n+1) (ShapeS.sigma A B d f)) t x

theorem TShape.Named.dom {Δ : List Term} {d x : TShape} {t : Term}
    (h : TShape.Named Δ d t x) : TShape.Dom Δ d x := by
  induction h with
  | base hnb hty _ => exact .base hnb hty
  | pi hty hent _ hev _ ihin ihout => exact .pi hty hent ihin hev ihout
  | sg hty hps _ _ hev _ ihx ihy => exact .sg hty hps ihx hev ihy

/-- At a code that only filters, a typed shape is never a `lam` or a
`pair`, and on every other head `ValCanon` *is* `CodeCanon`.  This is
what lets `Named`'s `base` clause carry only the code's naming. -/
theorem TShape.ValCanon.of_code {Δ : List Term} {t : Term} {d x : TShape}
    (hnb : ¬ d.IsBinder) (hty : TShape.HasType Δ x d) (hc : TShape.CodeCanon Δ t x) :
    TShape.ValCanon Δ t x := by
  obtain ⟨n, s⟩ := x
  cases hty with
  | lam _ _ _ hwPi _ _ _ _ _ => exact absurd trivial hnb
  | pair _ _ _ hwSg _ _ _ _ _ => exact absurd trivial hnb
  | bot _ => exact Shape.ValCanon.bot
  | zero => trivial
  | succ _ => trivial
  | refl _ _ => trivial
  | sort => cases n <;> exact hc
  | unit _ => exact hc
  | nat => exact hc
  | id _ _ => exact hc
  | forallE _ _ _ => exact hc
  | sigma _ _ _ => exact hc

/-- **`Named` carries the naming.**  Each clause's per-part conditions
are exactly what `ValCanon` asks of the corresponding head. -/
theorem TShape.Named.val {Δ : List Term} {d x : TShape} {t : Term}
    (h : TShape.Named Δ d t x) : TShape.ValCanon Δ t x := by
  induction h with
  | base hnb hty hc => exact TShape.ValCanon.of_code hnb hty hc
  | @pi n A B t d f x cs hty hent _ hev _ ihin ihout =>
    cases hty with
    | bot _ => exact Shape.ValCanon.bot
    | refl _ _ => trivial
    | @lam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      intro e he
      have hmem : (⟨e.tm, e.inp.T, e.out.T⟩ : Entry TShape) ∈ cs.map (·.1) := by
        rw [← hent]
        simp only [TShape.entries, Shape.graph, List.mem_map]
        exact ⟨e, he, rfl⟩
      obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hmem
      have h1 := ihin p hp; have h2 := ihout p hp
      simp only [hpe] at h1 h2
      exact ⟨h1, h2⟩
  | @sg n A B t d f x ps c hty hps hname _ hev _ ihx ihy =>
    cases hty with
    | bot _ => exact Shape.ValCanon.bot
    | refl _ _ => trivial
    | @pair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA₀A =>
      subst hps
      refine ⟨?_, ?_, ?_⟩
      · exact (hA₀A.choose_spec.symm.defeqDF (hname _ rfl))
      · exact ihx _ rfl
      · exact ihy _ rfl

/-- **And it asks for nothing more.**  `Named` is exactly `Dom` together
with `ValCanon`, so folding the naming into the hereditary-typing
induction changes no theorem, only where the conditions are written. -/
theorem TShape.Named.of_dom {Δ : List Term} {d x : TShape} {t : Term}
    (hD : TShape.Dom Δ d x) (hV : TShape.ValCanon Δ t x) : TShape.Named Δ d t x := by
  revert hV
  induction hD generalizing t with
  | base hnb hty => exact fun hV => .base hnb hty (Shape.ValCanon.toCode hV)
  | @pi n A B d f x cs hty hent _ hev _ ihin ihout =>
    intro hV
    have hall : ∀ p ∈ cs, TShape.ValCanon Δ p.1.tm p.1.inp ∧
        TShape.ValCanon Δ (Term.app t p.1.tm) p.1.out := by
      cases hty with
      | bot _ =>
        have : cs = [] := by
          simpa only [TShape.entries_bot, List.map_eq_nil_iff] using hent.symm
        simp [this]
      | refl _ _ =>
        have : cs = [] := by
          simpa only [TShape.entries, Shape.graph, List.map_nil, List.map_eq_nil_iff] using hent.symm
        simp [this]
      | @lam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        intro p hp
        have hmem : p.1 ∈ cs.map (·.1) := List.mem_map.2 ⟨p, hp, rfl⟩
        rw [← hent] at hmem
        simp only [TShape.entries, Shape.graph, List.mem_map] at hmem
        obtain ⟨e, he, hpe⟩ := hmem
        obtain ⟨h1, h2⟩ := hV e he
        exact hpe ▸ ⟨h1, h2⟩
    exact .pi hty hent (fun p hp => ihin p hp (hall p hp).1) hev
      (fun p hp => ihout p hp (hall p hp).2)
  | @sg n A B d f x ps c hty hps _ hev _ ihx ihy =>
    intro hV
    have hall : ∀ p ∈ ps, (Δ ⊢ p.1 ≡ Term.fst t : A) ∧
        TShape.ValCanon Δ (Term.fst t) p.2.1 ∧ TShape.ValCanon Δ (Term.snd t) p.2.2 := by
      cases hty with
      | bot _ =>
        have : ps = none := by simpa only [TShape.pairParts_bot] using hps.symm
        simp [this]
      | refl _ _ =>
        have : ps = none := by simpa only [TShape.pairParts] using hps.symm
        simp [this]
      | @pair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA₀A =>
        subst hps
        intro p hp
        obtain rfl : p = _ := by simpa only [TShape.pairParts, Option.mem_def,
          Option.some.injEq] using hp.symm
        obtain ⟨hname, h1, h2⟩ := hV
        exact ⟨hA₀A.choose_spec.defeqDF hname, h1, h2⟩
    exact .sg hty hps (fun p hp => (hall p hp).1) (fun p hp => ihx p hp (hall p hp).2.1) hev
      (fun p hp => ihy p hp (hall p hp).2.2)

/-- **The merge, as an equivalence.** -/
theorem TShape.Named.iff {Δ : List Term} {d x : TShape} {t : Term} :
    TShape.Named Δ d t x ↔ TShape.Dom Δ d x ∧ TShape.ValCanon Δ t x :=
  ⟨fun h => ⟨h.dom, h.val⟩, fun h => .of_dom h.1 h.2⟩

/-- **So the slot condition is two notions, not three.**  What is left
over does not merge in, and for a reason: `Named` is a statement about
the value `x`, while `CodeCanon` is a statement about the *code* `d`.
They have different subjects, so no single induction carries both. -/
theorem TShape.Slot.iff {Δ : List Term} {T t : Term} {d x : TShape} :
    TShape.Slot Δ T d t x ↔ TShape.Named Δ d t x ∧ TShape.CodeCanon Δ T d :=
  ⟨fun h => ⟨.of_dom h.1 h.2.2, h.2.1⟩, fun h => ⟨h.1.dom, h.2, h.1.val⟩⟩

/-! ### `Named`'s closure properties

Each is the corresponding `Dom` lemma paired with the `ValCanon` one;
`Named.iff` is what makes that a proof. -/

theorem TShape.Named.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {d x : TShape} {t : Term} (h : TShape.Named Δ d t x) :
    TShape.Named Θ (d.subst τ) (t.subst τ) (x.subst τ) :=
  .of_dom (h.dom.subst hΘ W) (Shape.ValCanon.subst hΘ W h.val)

theorem TShape.Named.lift_subject {Δ : List Term} (hΔ : ⊢ Δ) {d x : TShape} {t : Term}
    (h : TShape.Named Δ d t x) {k} (hk : x.1 ≤ k) : TShape.Named Δ d t (x.lift k) :=
  .of_dom (h.dom.lift_subject hΔ hk) ((TShape.ValCanon.lift_iff hΔ hk).1 h.val)

theorem TShape.Named.join {Δ : List Term} (hΔ : ⊢ Δ) {y z d : TShape} {t : Term}
    (hwy : TShape.WF Δ y) (hwz : TShape.WF Δ z) (hc : TShape.Compat Δ y z)
    (hy : TShape.Named Δ d t y) (hz : TShape.Named Δ d t z) :
    TShape.Named Δ d t (y.join z) :=
  .of_dom (TShape.Dom.join hΔ hc hy.dom hz.dom)
    (TShape.ValCanon.join hΔ hwy hwz hc hy.val hz.val)

theorem TShape.Named.mono_r {Δ : List Term} (hΔ : ⊢ Δ) {d d' x : TShape} {t : Term}
    (h : TShape.Named Δ d t x) (hle : TShape.LE Δ d d')
    (hty : TShape.HasType Δ d' TShape.type) : TShape.Named Δ d' t x :=
  .of_dom (h.dom.mono_r hΔ hle hty) h.val

theorem TShape.Named.bot {Δ : List Term} {d : TShape} {t : Term} {n}
    (h : TShape.HasType Δ (Shape.T (n := n) .bot) d) :
    TShape.Named Δ d t (Shape.T (n := n) .bot) :=
  .of_dom (TShape.Dom.bot h) (TShape.ValCanon.of_bot rfl)

/-- **The transport, on the merged notion.**  This is what the merge
buys: the hereditary typing travels with the name, so moving the name
along a definitional equality needs only the code's own naming. -/
theorem TShape.Named.defeq {Δ : List Term} (hΔ : ⊢ Δ) {T t t' : Term} {d x : TShape}
    (h : TShape.Named Δ d t x) (hC : TShape.CodeCanon Δ T d)
    (ht : Δ ⊢ t ≡ t' : T) : TShape.Named Δ d t' x :=
  .of_dom h.dom (TShape.ValCanon.defeq hΔ h.dom hC h.val ht)

/-! ## The fold, as an equivalence

`Shape.WF` carries a `Shape.CodeCanonS` at every Π and Σ node it
descends through, so for a well-formed shape the hereditary condition
`Shape.CodeCanon` adds nothing beyond its own head equation.  That is
what putting the shallow name inside `WF` was for: the recursion below
is `WF`'s, not canonicity's. -/

theorem Shape.CodeCanon.of_shallow : ∀ {n} {Δ : List Term} {T : Term} {s : Shape n},
    Shape.WF Δ s → Shape.CodeCanonS Δ T s → Shape.CodeCanon Δ T s
  | 0, _, _, s => by cases s <;> intro _ h <;> first | trivial | exact h
  | n+1, Δ, T, s => by
    cases s <;> intro hw h <;> first
      | trivial
      | exact h
      | exact ⟨h, Shape.CodeCanon.of_shallow hw.2.2.1 hw.2.2.2.2.1,
          fun e he => Shape.CodeCanon.of_shallow (hw.2.2.2.1.1 e he).2.2.2
            (hw.2.2.2.2.2 e he)⟩

/-- **The fold.**  For a well-formed shape the two agree. -/
theorem Shape.CodeCanon.iff_shallow {n} {Δ : List Term} {T : Term} {s : Shape n}
    (hw : Shape.WF Δ s) : Shape.CodeCanon Δ T s ↔ Shape.CodeCanonS Δ T s :=
  ⟨Shape.CodeCanon.shallow, Shape.CodeCanon.of_shallow hw⟩

theorem TShape.CodeCanon.iff_shallow {Δ : List Term} {T : Term} {x : TShape}
    (hw : TShape.WF Δ x) : TShape.CodeCanon Δ T x ↔ Shape.CodeCanonS Δ T x.2 :=
  Shape.CodeCanon.iff_shallow hw
