import DomainSemantics.Term
import DomainSemantics.Shape

/-! # The logical relation

This file builds the level-graded logical relation `LR : LogRel Γ n`.

* `LogRelBase` packages the bare data of a logical relation: a
  `TmEq M N A m a` predicate for term equality at element/type shapes
  and a `TyEq A B a` predicate for type equality.
* `LogRel` extends `LogRelBase` with all the closure properties needed
  to prove adequacy: symmetry, transitivity, monotonicity in both
  shapes, conversion, joinability, and stability under weak-head
  reduction (`whr`).
* `LR0` is the level-0 instance: types only see `bot` and `sort` shapes.
* `LRS IH` is the successor-level instance, defined in terms of an
  inductive hypothesis `IH : LogRel Γ n`. It adds Π/λ handling — see
  `LRS.PiDefEq` for the Π-edge constraints and `LRS.LamDefEq` for the
  extensional equality of λ-bodies.
* `LR hΓ : LogRel Γ n` is the recursive combination, the object every
  client lemma actually uses. -/

namespace DomainSemantics

/-- A "typed weak-head reduction" bundle: the weak-head reduction `M ⤳* M'`
together with the IsDefEq witness `Γ ⊢ M ≡ M' : A` that justifies it.
Used by `LogRel.whr` so each per-side reduction carries its IsDefEq
justification. -/
def TypedWHRedS (Γ : List Term) (M M' A : Term) : Prop :=
  Γ ⊢ M ≡ M' : A ∧ M ⤳* M'
scoped notation:65 Γ " ⊢ " M:66 " ⤳* " M' " : " A:36 => TypedWHRedS Γ M M' A

-- theorem TypedWHRedS.defeq (h : Γ ⊢ M ⤳* M' : A) : Γ ⊢ M ≡ M' : A := h.1
-- theorem TypedWHRedS.2 (h : Γ ⊢ M ⤳* M' : A) : M ⤳* M' := h.2

/-- Reflexive typed reduction: a typing is a typed reduction to itself. -/
theorem TypedWHRedS.rfl (h : Γ ⊢ M : A) : Γ ⊢ M ⤳* M : A := ⟨h, .rfl⟩

/-- A "logical relation base": the underlying data of two indexed relations
(`TmEq` for term equality at element/type shapes, `TyEq` for type
equality at a type shape) over a fixed well-formed context. The full
`LogRel` (below) adds all closure properties as fields. -/
structure LogRelBase (Γ : List Term) (n : Nat) where
  wf : ⊢ Γ
  /-- Term validity: `M ≡ N : A` at element-shape `m` and type-shape `a`. -/
  TmEq (M N A : Term) (m a : WShape n) : Prop
  /-- Type validity: `A ≡ B` are valid types at type-shape `a`. -/
  TyEq (A B : Term) (a : WShape n) : Prop

/-- The logical relation at level `n`: a `LogRelBase` plus closure
properties (symmetry, transitivity, conversion, monotonicity, joinability,
weak-head-reduction stability, …) needed to prove adequacy. Level-0
(`LR0`) only sees `sort` and `bot` shapes; higher levels (`LRS IH`) add
Π/λ data on top of an inductive hypothesis `IH : LogRel Γ n`. -/
structure LogRel (Γ : List Term) (n : Nat) extends LogRelBase Γ n where
  sort_iff : TmEq M N A (.sort r) (.sort r') ↔
    ∃ v, Γ ⊢ A ⤳* .sort v : .sort true ∧
    ∃ u, Γ ⊢ M ⤳* .sort u : .sort true ∧ Γ ⊢ N ⤳* .sort u : .sort true
  sort_iff_ty : TyEq M N (.sort r) ↔
    ∃ u, Γ ⊢ M ⤳* .sort u : .sort true ∧ Γ ⊢ N ⤳* .sort u : .sort true
  bot : a.HasType .type → TyEq A A a → TmEq M N A .bot a
  bot_ty : TyEq A B .bot
  isType : TmEq M N A m a → TyEq A A a
  toType : TmEq M N A m (.sort r) → TyEq M N m
  left : TmEq M N A m a → TmEq M M A m a
  left_ty : TyEq M N m → TyEq M M m
  symm : Γ ⊢ M ≡ N : A → TmEq M N A m a → TmEq N M A m a
  symm_ty : TyEq M N m → TyEq N M m
  trans : Γ ⊢ M₁ ≡ M₂ : A → Γ ⊢ M₂ ≡ M₃ : A →
    TmEq M₁ M₂ A m a → TmEq M₂ M₃ A m a → TmEq M₁ M₃ A m a
  trans' : TmEq A₁ A₂ (.sort u) a s → TmEq A₂ A₃ (.sort v) a (.sort r) → TmEq A₁ A₃ (.sort u) a s
  trans_ty : TyEq M₁ M₂ m → TyEq M₂ M₃ m → TyEq M₁ M₃ m
  conv : TyEq A B a → TmEq M N A m a → TmEq M N B m a
  mono_r_2 : a ≤ a' → m.HasType a → a'.HasType .type → TmEq M N A m a' → TmEq M N A m a
  mono_r_2_ty : a ≤ a' → a.HasType .type → a'.HasType .type → TyEq A B a' → TyEq A B a
  mono_r_1 : a ≤ a' → m.HasType a → m.HasType a' → TyEq A A a' → TmEq M N A m a → TmEq M N A m a'
  mono_l : m ≤ m' → m.HasType a → m'.HasType a → TmEq M N A m' a → TmEq M N A m a
  join_ty : m₁.Compat m₂ → m₁.HasType .type → m₂.HasType .type →
    TyEq A B m₁ → TyEq A B m₂ → TyEq A B (m₁.join m₂)
  whr : Γ ⊢ M ⤳* M' : A → Γ ⊢ N ⤳* N' : A → Γ ⊢ M ≡ N : A →
    (TmEq M N A m a ↔ TmEq M' N' A m a)

theorem LogRelBase.TyEq.sort {R : LogRel Γ n} : R.TyEq (.sort u) (.sort u) (.sort r) :=
  R.sort_iff_ty.2 ⟨_, ⟨.sort, .rfl⟩, ⟨.sort, .rfl⟩⟩

/-! #### Concrete definitions at level 0 -/

def LR0.TyEq (Γ : List Term) (M N : Term) : WShape 0 → Prop
  | ⟨.bot, _⟩ => True
  | ⟨.sort _, _⟩ => ∃ u, Γ ⊢ M ⤳* .sort u : .sort true ∧ Γ ⊢ N ⤳* .sort u : .sort true

def LR0.TmEq (Γ : List Term) (M N A : Term) (m a : WShape 0) : Prop :=
  match a.1 with
  | .bot => True
  | .sort _ => ∃ u, Γ ⊢ A ⤳* .sort u : .sort true ∧ LR0.TyEq Γ M N m

theorem LR0.TyEq.left : LR0.TyEq Γ M N m → LR0.TyEq Γ M M m := by
  cases m using WShape.casesOn with | bot => intro; trivial | sort
  rintro ⟨u, hM, _⟩; exact ⟨u, hM, hM⟩

theorem LR0.TyEq.symm : LR0.TyEq Γ M N m → LR0.TyEq Γ N M m := by
  cases m using WShape.casesOn with | bot => intro; trivial | sort
  rintro ⟨u, hM, hN⟩; exact ⟨u, hN, hM⟩

theorem LR0.TyEq.trans : LR0.TyEq Γ M₁ M₂ m → LR0.TyEq Γ M₂ M₃ m → LR0.TyEq Γ M₁ M₃ m := by
  cases m using WShape.casesOn with | bot => intros; trivial | sort
  rintro ⟨u, hM1, hM2⟩ ⟨_, hM2', hM3⟩
  cases hM2.2.determ .sort hM2'.2 .sort
  exact ⟨u, hM1, hM3⟩

theorem LR0.TmEq.bot : LR0.TyEq Γ A A a → LR0.TmEq Γ M N A .bot a := by
  cases a using WShape.casesOn with | bot => intro; trivial | sort
  rintro ⟨u, hA1, _⟩; exact ⟨u, hA1, trivial⟩

/-- The level-0 logical relation: `TmEq`/`TyEq` only see `bot` (trivially
true) and `sort` (both sides whr-reduce to the same sort). All structural
laws hold by case analysis on the type-shape. -/
def LR0 (wf : ⊢ Γ) : LogRel Γ 0 where
  wf
  TmEq := LR0.TmEq Γ
  TyEq := LR0.TyEq Γ
  sort_iff := .rfl
  sort_iff_ty := .rfl
  bot _ := .bot
  bot_ty := trivial
  isType {M N A m a} := by
    cases a using WShape.casesOn with | bot => intro; trivial | sort
    rintro ⟨u, hA, _⟩; exact ⟨u, hA, hA⟩
  toType {M N A m r} h := by
    cases m using WShape.casesOn with | bot => trivial | sort
    obtain ⟨_, _, h⟩ := h; exact h
  left {M N A m a} := by
    cases a using WShape.casesOn with | bot => intro; trivial | sort
    rintro ⟨u, hA, h⟩; exact ⟨u, hA, h.left⟩
  left_ty := .left
  symm {M N A m a} _ := by
    cases a using WShape.casesOn with | bot => intro; trivial | sort
    rintro ⟨u, hA, h⟩; exact ⟨u, hA, h.symm⟩
  symm_ty := .symm
  trans {M₁ M₂ A M₃ m a} _ _ := by
    cases a using WShape.casesOn with | bot => intros; trivial | sort
    rintro ⟨u, hA, h12⟩ ⟨_, _, h23⟩; exact ⟨u, hA, h12.trans h23⟩
  trans' {A₁ A₂ u' a s A₃ v r} := by
    cases s using WShape.casesOn with | bot => intros; trivial | sort
    rintro ⟨u_A, hA, h12⟩ ⟨_, _, h23⟩; refine ⟨u_A, hA, ?_⟩
    cases a using WShape.casesOn with | bot => trivial | sort
    obtain ⟨u, hM1, hM2⟩ := h12; obtain ⟨_, hM2', hM3⟩ := h23
    cases hM2.2.determ .sort hM2'.2 .sort
    exact ⟨u, hM1, hM3⟩
  trans_ty := .trans
  conv {A B a M N m} := by
    cases a using WShape.casesOn with | bot => intros; trivial | sort
    rintro ⟨u, _, hB⟩ ⟨_, _, h⟩; exact ⟨u, hB, h⟩
  mono_r_2 {a a' M N A m} le _ _ := by
    cases a using WShape.casesOn with | bot => intro; trivial | sort
    cases WShape.sort_le.1 le; exact id
  mono_r_2_ty {a a' A B} le _ _ := by
    cases a using WShape.casesOn with | bot => intro; trivial | sort
    cases WShape.sort_le.1 le; exact id
  mono_r_1 {a a' A M N m} le ha _ hA := by
    cases m using WShape.casesOn with | bot => intro _; exact .bot hA | sort
    cases a using WShape.casesOn with | bot => cases ha.bot_r | sort
    cases WShape.sort_le.1 le; exact id
  mono_l {m m' M N A a} le _ _ := by
    cases a using WShape.casesOn with | bot => intro; trivial | sort
    cases m' using WShape.casesOn with | bot => cases WShape.le_bot.1 le; exact id | sort
    rintro ⟨u, hA, h⟩; refine ⟨u, hA, ?_⟩
    cases m using WShape.casesOn with | bot => trivial | sort => exact h
  join_ty {A B m₁ m₂} compat _ _ := by
    cases m₁ using WShape.casesOn with | bot => simp | sort
    cases m₂ using WShape.casesOn with | bot => simp +contextual | sort
    cases WShape.Compat.sort_sort.1 compat; simp
  whr {M M' A N N' m a} hM hN _ := by
    cases m using WShape.casesOn with | bot => rfl | sort
    cases a using WShape.casesOn with | bot => rfl | sort
    constructor <;> refine fun ⟨u, hA, v, r1, r2⟩ => ⟨u, hA, ?_⟩ <;> (
      have hM' := hA.1.defeqDF hM.1
      have hN' := hA.1.defeqDF hN.1
      refine ⟨v, ?_, ?_⟩)
    · exact ⟨(r1.1.symm.trans' hM').symm, hM.2.determ_l r1.2 .sort⟩
    · exact ⟨(r2.1.symm.trans' hN').symm, hN.2.determ_l r2.2 .sort⟩
    · exact ⟨(r1.1.symm.trans' hM'.symm).symm, .trans hM.2 r1.2⟩
    · exact ⟨(r2.1.symm.trans' hN'.symm).symm, .trans hN.2 r2.2⟩

/-! #### Concrete definitions at level n+1 -/

/-- Pi edge validity (merged `PiEdgeDefEq` / `PiEdgeEq2`).
For each argument `a ≡ b : A₁`, the substituted codomains are valid types.
For each argument `a : A₁`, the codomains `A₂[a]` and `B₂[a]` are equal types. -/
def LRS.PiDefEq (IH : LogRel Γ n)
    (B F₁ F₂ : Term) (b : WShape n) (f : WShapeFun n) : Prop :=
  (∀ {{a b' p}}, p.HasType b → Γ ⊢ a ≡ b' : B → IH.TmEq a b' B p b →
    IH.TyEq (F₁.inst a) (F₁.inst b') (f.app p) ∧
    IH.TyEq (F₂.inst a) (F₂.inst b') (f.app p)) ∧
  ∀ {{a p}}, p.HasType b → Γ ⊢ a : B → IH.TmEq a a B p b →
    IH.TyEq (F₁.inst a) (F₂.inst a) (f.app p)

theorem LRS.PiDefEq.left {IH : LogRel Γ n} :
    LRS.PiDefEq IH B F₁ F₂ b f → LRS.PiDefEq IH B F₁ F₁ b f := fun ⟨h1, _⟩ =>
  ⟨fun _ _ _ hp ha a1 => ⟨(h1 hp ha a1).1, (h1 hp ha a1).1⟩, fun _ _ hp ha a1 => (h1 hp ha a1).1⟩

/-- "Pi-type validity at level `n+1`": `M₁`, `M₂` both whr-reduce to Π-types
whose domains and codomains are `IH`-equal, and whose codomain-after-edge
data satisfies `PiDefEq`. -/
def LRS.ValTyPi2 (IH : LogRel Γ n) (M₁ M₂ : Term) (b : WShape n) (f : WShapeFun n) : Prop :=
  ∃ B₁ F₁ B₂ F₂ u v,
    Γ ⊢ M₁ ⤳* .forallE B₁ F₁ : .sort v ∧ Γ ⊢ M₂ ⤳* .forallE B₂ F₂ : .sort v ∧
    Γ ⊢ B₁ ≡ B₂ : .sort u ∧ B₁::Γ ⊢ F₁ ≡ F₂ : .sort v ∧ IH.TyEq B₁ B₂ b ∧
    LRS.PiDefEq IH B₁ F₁ F₂ b f

/-- "λ-equality at level `n+1`": pointwise extensional equality of the two
λ-bodies, separated into a "validity" half (each side stable under
swapping the argument by an equal one) and an "equation" half (both
sides agree on every common argument). Used by `LRS.TmEq` at `lam`-shape. -/
def LRS.LamDefEq (IH : LogRel Γ n)
    (M N A₁ A₂ : Term) (m : WShapeFun n) (a₁ : WShape n) (a₂ : WShapeFun n) : Prop :=
  (∀ {{a b p}}, WShape.HasType p a₁ → Γ ⊢ a ≡ b : A₁ → IH.TmEq a b A₁ p a₁ →
    IH.TmEq (M.app a) (M.app b) (A₂.inst a) (m.app p) (a₂.app p) ∧
    IH.TmEq (N.app a) (N.app b) (A₂.inst a) (m.app p) (a₂.app p)) ∧
  (∀ {{a p}}, WShape.HasType p a₁ → Γ ⊢ a : A₁ → IH.TmEq a a A₁ p a₁ →
    IH.TmEq (M.app a) (N.app a) (A₂.inst a) (m.app p) (a₂.app p))

/-- Monotonicity of `LamDefEq` in the type-shape: increase. -/
theorem LRS.LamDefEq.mono_r_1 {IH : LogRel Γ n}
    (le₁ : a₁ ≤ a₁') (le₂ : a₂ ≤ a₂') (hm : WShape.HasTypeLam m a₁ a₂)
    (hm' : WShape.HasTypeLam m a₁' a₂') (piEV : LRS.PiDefEq IH A₁ A₂ A₂ a₁' a₂') :
    LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ → LRS.LamDefEq IH M N A₁ A₂ m a₁' a₂' := by
  have hm_d := WShape.HasDom.iff.1 hm.2.1
  have hm_f := WShape.HasTypeLam.iff.1 hm |>.2.2
  intro ⟨pav, pae⟩
  refine ⟨fun _ _ x hx ha a1 => ?_, fun _ x hx ha a1 => ?_⟩
  all_goals
    have ⟨x', le', hax, h1⟩ := hm_d x
    have hax' := hx.isType.mono_r le₁ hax
    have a1_x := IH.mono_l le' hax' hx a1
    have a1_down := IH.mono_r_2 le₁ hax hx.isType a1_x
    have hg_x := hm_f x' hax
    have hg_p := hg_x.mono_l (WShapeFun.app_mono_r le') h1
    have le_cod := (WShapeFun.app_mono_r le').trans (WShapeFun.app_mono_l le₂ _)
    have ht_cod := (WShape.HasTypePi.iff.1 hm'.1).2 x hx
    have hm_target := ht_cod.mono_r le_cod hg_p
  · have ⟨p1, p2⟩ := pav hax ha a1_down
    have tyA₂ := (piEV.1 hx ha.hasType.1 (IH.left a1)).1
    exact ⟨IH.mono_r_1 le_cod hg_p hm_target tyA₂ (IH.mono_l h1 hg_p hg_x p1),
           IH.mono_r_1 le_cod hg_p hm_target tyA₂ (IH.mono_l h1 hg_p hg_x p2)⟩
  · have q := pae hax ha a1_down
    have tyA₂ := piEV.2 hx ha a1
    exact IH.mono_r_1 le_cod hg_p hm_target tyA₂ (IH.mono_l h1 hg_p hg_x q)

/-- Type validity at element-shape `m` (merged `TyEq` / `EqTyDefEq`).
Non-trivial at `.forallE` (Pi injectivity) and `.sort` (sort injectivity). -/
def LRS.TyEq (IH : LogRel Γ n) (M N : Term) : WShape (n+1) → Prop
  | ⟨.bot, _⟩ | ⟨.lam _, _⟩ => True
  | ⟨.sort _, _⟩ => ∃ u, Γ ⊢ M ⤳* .sort u : .sort true ∧ Γ ⊢ N ⤳* .sort u : .sort true
  | ⟨.forallE b f, wf⟩ => LRS.ValTyPi2 IH M N ⟨b, wf.1⟩ ⟨f, wf.2⟩

@[simp] theorem LRS.TyEq.bot : LRS.TyEq IH M N .bot := trivial
@[simp] theorem LRS.TyEq.sort_iff :
    LRS.TyEq (Γ := Γ) IH M N (.sort r) ↔ ∃ u,
      Γ ⊢ M ⤳* .sort u : .sort true ∧ Γ ⊢ N ⤳* .sort u : .sort true := .rfl
@[simp] theorem LRS.TyEq.forallE_iff :
    LRS.TyEq (Γ := Γ) IH M N (.forallE b f) ↔ LRS.ValTyPi2 (Γ := Γ) IH M N b f := .rfl

theorem LRS.TyEq.left {IH : LogRel Γ n} : LRS.TyEq IH M N m → LRS.TyEq IH M M m := by
  dsimp [LRS.TyEq]; split <;> try trivial
  · intro ⟨u, hM, _⟩; exact ⟨u, hM, hM⟩
  · intro ⟨B₁, F₁, _, _, u, v, rM, _, hB, hF, hValB, hE⟩
    exact ⟨B₁, F₁, B₁, F₁, u, v, rM, rM, hB.hasType.1, hF.hasType.1, IH.left_ty hValB, hE.left⟩

theorem LRS.TyEq.symm {IH : LogRel Γ n} : LRS.TyEq IH M N m → LRS.TyEq IH N M m := by
  dsimp [LRS.TyEq]; split <;> try trivial
  · intro ⟨u, hM, hN⟩; exact ⟨u, hN, hM⟩
  · intro ⟨_, _, _, _, _, _, rM, rN, hB, hF, hValB, hE1, hE2⟩
    have hValB' := IH.symm_ty hValB
    refine ⟨_, _, _, _, _, _, rN, rM, hB.symm, hB.defeqDF_l IH.wf hF.symm,
      hValB', fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
    · exact (hE1 hp (hB.symm.defeqDF ha) (IH.conv hValB' a1)).symm
    · exact IH.symm_ty (hE2 hp (hB.symm.defeqDF ha) (IH.conv hValB' a1))

theorem LRS.TyEq.trans {IH : LogRel Γ n} :
    LRS.TyEq IH M₁ M₂ m → LRS.TyEq IH M₂ M₃ m → LRS.TyEq IH M₁ M₃ m := by
  dsimp [LRS.TyEq]; split <;> try trivial
  · intro ⟨u, hM₁, hM₂⟩ ⟨u', hM₂', hM₃⟩
    cases hM₂.2.determ .sort hM₂'.2 .sort; exact ⟨u, hM₁, hM₃⟩
  · intro ⟨B₁, F₁, B₂, F₂, u, v, rM₁, rM₂, hB₁₂, hF₁₂, hValB₁₂, hE1⟩
          ⟨_, _, B₃, F₃, u', v', rM₂', rM₃, hB₂₃, hF₂₃, hValB₂₃, hE2⟩
    cases rM₂.2.determ .forallE rM₂'.2 .forallE
    have hF₂₃' := hB₁₂.symm.defeqDF_l IH.wf hF₂₃
    refine ⟨_, _, _, _, _, _, rM₁, ?_, hB₁₂.trans' hB₂₃, hF₁₂.trans' hF₂₃',
      IH.trans_ty hValB₁₂ hValB₂₃, fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
    · have := hB₂₃.forallEDF hF₂₃ (hB₂₃.defeqDF_l IH.wf hF₂₃)
      exact ⟨(rM₂.1.symm.trans' ((rM₂'.1.trans this).trans rM₃.1.symm)).symm.trans
        ((rM₂.1.symm.trans rM₂.1).trans' this), rM₃.2⟩
    · exact ⟨(hE1.1 hp ha a1).1, (hE2.1 hp (hB₁₂.defeqDF ha) (IH.conv hValB₁₂ a1)).2⟩
    · exact IH.trans_ty (hE1.2 hp ha a1) (hE2.2 hp (hB₁₂.defeqDF ha) (IH.conv hValB₁₂ a1))

theorem LRS.LamDefEq.left {IH : LogRel Γ n} :
    LRS.LamDefEq IH M N B F m m₁ m₂ → LRS.LamDefEq IH M M B F m m₁ m₂ := by
  refine fun hP => ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · exact ⟨(hP.1 hp ha a1).1, (hP.1 hp ha a1).1⟩
  · exact (hP.1 hp ha a1).1

theorem LRS.LamDefEq.symm {IH : LogRel Γ n} (hMN : Γ ⊢ M ≡ N : .forallE B F)
    (hP : LRS.LamDefEq IH M N B F m m₁ m₂) : LRS.LamDefEq IH N M B F m m₁ m₂ := by
  refine ⟨fun _ _ _ hp ha a1 => ⟨(hP.1 hp ha a1).2, (hP.1 hp ha a1).1⟩, fun _ _ hp ha a1 => ?_⟩
  have ⟨_, hAB⟩ := hMN.isType IH.wf
  have ⟨⟨_, hA⟩, _, hBcod⟩ := hAB.forallE_inv' IH.wf (.inl rfl)
  exact IH.symm (.appDF hA hBcod hMN ha (.instDF IH.wf hA .sort hBcod ha)) (hP.2 hp ha a1)

theorem LRS.LamDefEq.trans {IH : LogRel Γ n}
    (hMN12 : Γ ⊢ M₁ ≡ M₂ : .forallE B F) (hMN23 : Γ ⊢ M₂ ≡ M₃ : .forallE B F) :
    LRS.LamDefEq IH M₁ M₂ B F m m₁ m₂ →
    LRS.LamDefEq IH M₂ M₃ B F m m₁ m₂ → LRS.LamDefEq IH M₁ M₃ B F m m₁ m₂ := by
  refine fun ⟨hP1, hP2⟩ ⟨hP1', hP2'⟩ => ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · exact ⟨(hP1 hp ha a1).1, (hP1' hp ha a1).2⟩
  · have ⟨_, hAB⟩ := hMN12.isType IH.wf
    have ⟨⟨_, hA⟩, _, hBcod⟩ := hAB.forallE_inv' IH.wf (.inl rfl)
    refine IH.trans ?_ ?_ (hP2 hp ha a1) (hP2' hp ha a1)
    · exact .appDF hA hBcod hMN12 ha (.instDF IH.wf hA .sort hBcod ha)
    · exact .appDF hA hBcod hMN23 ha (.instDF IH.wf hA .sort hBcod ha)

theorem LRS.PiDefEq.mono_r_2 {IH : LogRel Γ n}
    (le₁ : b ≤ b') (le₂ : f ≤ f')
    (htpi : WShape.HasTypePi f b r) (htpi' : WShape.HasTypePi f' b' r')
    (hValA₁ : IH.TyEq A₁ A₁ b') :
    LRS.PiDefEq IH A₁ A₂ B₂ b' f' → LRS.PiDefEq IH A₁ A₂ B₂ b f
  | ⟨h1, h2⟩ => by
    have htpi_w := WShape.HasTypePi.iff.1 htpi
    have htpi'_w := WShape.HasTypePi.iff.1 htpi'
    refine ⟨fun _ _ x hp ha a1 => ?_, fun _ x hp ha a1 => ?_⟩
    all_goals
      have hp' := WShape.HasType.mono_r le₁ (WShape.HasDom.isType htpi'.1) hp
      have a2 := IH.mono_r_1 le₁ hp hp' hValA₁ a1
      have hm_tgt := (htpi_w.2 _ hp).toType; have hm_src := (htpi'_w.2 _ hp').toType
    · let ⟨t1, t2⟩ := h1 hp' ha a2
      exact ⟨IH.mono_r_2_ty (WShapeFun.app_mono_l le₂ x) hm_tgt hm_src t1,
             IH.mono_r_2_ty (WShapeFun.app_mono_l le₂ x) hm_tgt hm_src t2⟩
    · exact IH.mono_r_2_ty (WShapeFun.app_mono_l le₂ x) hm_tgt hm_src (h2 hp' ha a2)

theorem LRS.LamDefEq.mono_r_2 {IH : LogRel Γ n}
    (le₁ : a₁ ≤ a₁') (le₂ : a₂ ≤ a₂') (hm : WShape.HasTypeLam m a₁ a₂)
    (hValA₁ : IH.TyEq A₁ A₁ a₁') (htpi' : WShape.HasTypePi a₂' a₁' r') :
    LRS.LamDefEq IH M N A₁ A₂ m a₁' a₂' → LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ := by
  have hm_w := WShape.HasTypeLam.iff.1 hm
  have htpi'_w := WShape.HasTypePi.iff.1 htpi'
  intro ⟨h1, h2⟩
  refine ⟨fun _ _ x hp ha a1 => ?_, fun _ x hp ha a1 => ?_⟩
  all_goals
    have hp' := WShape.HasType.mono_r le₁ (WShape.HasDom.isType htpi'.1) hp
    have a1' := IH.mono_r_1 le₁ hp hp' hValA₁ a1
    have hm_tgt := hm_w.2.2 _ hp
    have ht_src := (htpi'_w.2 _ hp').toType
  · have ⟨d1, d2⟩ := h1 hp' ha a1'
    exact ⟨IH.mono_r_2 (WShapeFun.app_mono_l le₂ x) hm_tgt ht_src d1,
           IH.mono_r_2 (WShapeFun.app_mono_l le₂ x) hm_tgt ht_src d2⟩
  · have q := h2 hp' ha a1'
    exact IH.mono_r_2 (WShapeFun.app_mono_l le₂ _) hm_tgt ht_src q

/-- Monotonicity of `LamDefEq` in the element-shape: decrease. -/
theorem LRS.LamDefEq.mono_l {IH : LogRel Γ n}
    (le : m ≤ m') (hm : WShape.HasTypeLam m a₁ a₂)
    (hm' : WShape.HasTypeLam m' a₁ a₂) :
    LRS.LamDefEq IH M N A₁ A₂ m' a₁ a₂ → LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ := by
  have hm_w := WShape.HasTypeLam.iff.1 hm
  have hm'_w := WShape.HasTypeLam.iff.1 hm'
  intro ⟨pav, pae⟩
  refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  all_goals
    have hm_tgt := hm_w.2.2 _ hp
    have hm_src := hm'_w.2.2 _ hp
  · have ⟨d1, d2⟩ := pav hp ha a1
    exact ⟨IH.mono_l (WShapeFun.app_mono_l le _) hm_tgt hm_src d1,
           IH.mono_l (WShapeFun.app_mono_l le _) hm_tgt hm_src d2⟩
  · have q := pae hp ha a1
    exact IH.mono_l (WShapeFun.app_mono_l le _) hm_tgt hm_src q

/-- Join of `PiDefEq`: given edge validity at `(b₁, f₁)` and `(b₂, f₂)`,
produce edge validity at `(b₁.join b₂, f₁.join f₂)`.
Follows the same representative-based strategy as old `LRS.join`. -/
theorem LRS.PiDefEq.join {IH : LogRel Γ n}
    (htB₁ : b₁.HasType .type) (htB₂ : b₂.HasType .type)
    (hC_b : b₁.Compat b₂)
    (ht₁ : WShape.HasTypePi f₁ b₁ r₁) (ht₂ : WShape.HasTypePi f₂ b₂ r₂)
    (hC_f : WShapeFun.Compat f₁ f₂)
    (hE₁ : LRS.PiDefEq IH B₁ F₁ F₂ b₁ f₁)
    (hE₂ : LRS.PiDefEq IH B₁ F₁ F₂ b₂ f₂) :
    LRS.PiDefEq IH B₁ F₁ F₂ (b₁.join b₂) (f₁.join f₂) := by
  have hJ_b := WShape.Join.mk hC_b
  have htB_join := htB₁.join hC_b htB₂
  have hJ_f := WShapeFun.Join.mk hC_f
  have ht₁_w := WShape.HasTypePi.iff.1 ht₁
  have ht₂_w := WShape.HasTypePi.iff.1 ht₂
  have hd₁ := WShape.HasDom.iff.1 ht₁.1
  have hd₂ := WShape.HasDom.iff.1 ht₂.1
  refine ⟨fun _ _ p hp ha a1 => ?_, fun _ p hp ha a1 => ?_⟩
  all_goals
    obtain ⟨d_x, d_le, d_ht, d_app⟩ := hd₁ p
    have c2 := IH.mono_r_2 hJ_b.le.1 d_ht htB_join
      (IH.mono_l d_le (WShape.HasType.mono_r hJ_b.le.1 htB_join d_ht) hp a1)
    obtain ⟨e_x, e_le, e_ht, e_app⟩ := hd₂ p
    have c3 := IH.mono_r_2 hJ_b.le.2 e_ht htB_join
      (IH.mono_l e_le (WShape.HasType.mono_r hJ_b.le.2 htB_join e_ht) hp a1)
    have ht_f1 : (f₁.app p).HasType .type :=
      have ⟨_, _, hm⟩ := f₁.app_eq p; (ht₁.2 _ _ hm).toType
    have ht_f2 : (f₂.app p).HasType .type :=
      have ⟨_, _, hm⟩ := f₂.app_eq p; (ht₂.2 _ _ hm).toType
    have hJ_fp := hJ_f.app_l p
    have ⟨hC_fp, _, hC_fJ⟩ := WShape.Join.iff.1 hJ_fp
    have ht_fJ := ht_f1.join' hJ_fp ht_f2
    have ht_fJ' := ht_f1.join hC_fp ht_f2
    have cvt_d {A B} (h : IH.TyEq A B (f₁.app d_x)) : IH.TyEq A B (f₁.app p) :=
      IH.mono_r_2_ty d_app ht_f1 (ht₁_w.2 d_x d_ht).toType h
    have cvt_e {A B} (h : IH.TyEq A B (f₂.app e_x)) : IH.TyEq A B (f₂.app p) :=
      IH.mono_r_2_ty e_app ht_f2 (ht₂_w.2 e_x e_ht).toType h
  · constructor
    · exact IH.mono_r_2_ty hC_fJ ht_fJ ht_fJ' <| IH.join_ty hC_fp ht_f1 ht_f2
        (cvt_d (hE₁.1 d_ht ha c2).1) (cvt_e (hE₂.1 e_ht ha c3).1)
    · exact IH.mono_r_2_ty hC_fJ ht_fJ ht_fJ' <| IH.join_ty hC_fp ht_f1 ht_f2
        (cvt_d (hE₁.1 d_ht ha c2).2) (cvt_e (hE₂.1 e_ht ha c3).2)
  · exact IH.mono_r_2_ty hC_fJ ht_fJ ht_fJ' <| IH.join_ty hC_fp ht_f1 ht_f2
      (cvt_d (hE₁.2 d_ht ha c2)) (cvt_e (hE₂.2 e_ht ha c3))

/-- Head reduction on M, N preserves `LamDefEq`. Takes TypedWHRedS bundles. -/
theorem LRS.LamDefEq.whr {IH : LogRel Γ n}
    (hM : Γ ⊢ M ⤳* M' : .forallE A₁ A₂) (hN : Γ ⊢ N ⤳* N' : .forallE A₁ A₂)
    (hMN : Γ ⊢ M ≡ N : .forallE A₁ A₂) :
    LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ ↔ LRS.LamDefEq IH M' N' A₁ A₂ m a₁ a₂ := by
  have ⟨_, hAB⟩ := hM.1.isType IH.wf
  have ⟨⟨_, hA⟩, _, hB⟩ := hAB.forallE_inv' IH.wf (.inl rfl)
  have appEq {M M'} (h : Γ ⊢ M ≡ M' : .forallE A₁ A₂) {a b : Term}
      (hab : Γ ⊢ a ≡ b : A₁) : Γ ⊢ M.app a ≡ M'.app b : A₂.inst a :=
    .appDF hA hB h hab (.instDF IH.wf hA .sort hB hab)
  have appEq_b {M M'} (h : Γ ⊢ M ≡ M' : .forallE A₁ A₂) {a b}
      (hab : Γ ⊢ a ≡ b : A₁) : Γ ⊢ M.app b ≡ M'.app b : A₂.inst a :=
    have hConv : Γ ⊢ A₂.inst a ≡ A₂.inst b : _ := .instDF IH.wf hA .sort hB hab
    .defeqDF hConv.symm (appEq h hab.hasType.2)
  have typedApp {M M'} (h : Γ ⊢ M ⤳* M' : .forallE A₁ A₂) {a b}
      (hab : Γ ⊢ a ≡ b : A₁) : Γ ⊢ M.app b ⤳* M'.app b : A₂.inst a := ⟨appEq_b h.1 hab, h.2.app⟩
  constructor <;> intro ⟨pav, pae⟩ <;> refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · have ⟨d1, d2⟩ := pav hp ha a1
    exact ⟨(IH.whr (typedApp hM ha.hasType.1) (typedApp hM ha) (appEq hM.1.hasType.1 ha)).1 d1,
      (IH.whr (typedApp hN ha.hasType.1) (typedApp hN ha) (appEq hN.1.hasType.1 ha)).1 d2⟩
  · exact (IH.whr (typedApp hM ha.hasType.1) (typedApp hN ha.hasType.2) (appEq hMN ha)).1
      (pae hp ha a1)
  · have ⟨d1, d2⟩ := pav hp ha a1
    exact ⟨(IH.whr (typedApp hM ha.hasType.1) (typedApp hM ha) (appEq hM.1.hasType.1 ha)).2 d1,
      (IH.whr (typedApp hN ha.hasType.1) (typedApp hN ha) (appEq hN.1.hasType.1 ha)).2 d2⟩
  · exact (IH.whr (typedApp hM ha.hasType.1) (typedApp hN ha.hasType.2) (appEq hMN ha)).2
      (pae hp ha a1)

/-- Term validity at `(m, a)`. -/
def LRS.TmEq (IH : LogRel Γ n) (M N A : Term) (m a : WShape (n+1)) : Prop :=
  match ha : a.1 with
  | .bot => True
  | .sort _ => ∃ u, Γ ⊢ A ⤳* .sort u : .sort true ∧ LRS.TyEq IH M N m
  | .forallE a₁ a₂ =>
    have wfa1 := (ha ▸ a.2).1; have wfa2 := (ha ▸ a.2).2
    match hm : m.1 with
    | .bot => LRS.ValTyPi2 IH A A ⟨a₁, wfa1⟩ ⟨a₂, wfa2⟩
    | .lam mg =>
      ∃ A₁ A₂ u v, Γ ⊢ A ⤳* .forallE A₁ A₂ : .sort v ∧
      Γ ⊢ A₁ : .sort u ∧ IH.TyEq A₁ A₁ ⟨a₁, wfa1⟩ ∧ A₁::Γ ⊢ A₂ : .sort v ∧
      LRS.PiDefEq IH A₁ A₂ A₂ ⟨a₁, wfa1⟩ ⟨a₂, wfa2⟩ ∧
      LRS.LamDefEq IH M N A₁ A₂ ⟨mg, (hm ▸ m.2).1⟩ ⟨a₁, wfa1⟩ ⟨a₂, wfa2⟩
    | _ => False
  | _ => False

@[simp] theorem LRS.TmEq.bot_a : LRS.TmEq IH M N A m .bot = True := rfl
@[simp] theorem LRS.TmEq.sort_a {Γ : List Term} {n : Nat} {IH : LogRel Γ n}
    {M N A : Term} {m : WShape (n+1)} {r : Bool} :
    LRS.TmEq IH M N A m (.sort r) ↔
    ∃ u, Γ ⊢ A ⤳* .sort u : .sort true ∧ LRS.TyEq IH M N m := Iff.rfl
@[simp] theorem LRS.TmEq.bot_m :
    LRS.TmEq IH M N A .bot (.forallE a₁ a₂) ↔ LRS.ValTyPi2 IH A A a₁ a₂ := by
  show LRS.ValTyPi2 IH _ _ ⟨_, _⟩ ⟨_, _⟩ ↔ _
  simp only [Subtype.eta]
@[simp] theorem LRS.TmEq.lam_forallE (IH : LogRel Γ n) :
    LRS.TmEq IH M N A (.lam f hf) (.forallE a₁ a₂) ↔
    (∃ A₁ A₂ u v, Γ ⊢ A ⤳* .forallE A₁ A₂ : .sort v ∧
      Γ ⊢ A₁ : .sort u ∧ IH.TyEq A₁ A₁ a₁ ∧ A₁::Γ ⊢ A₂ : .sort v ∧
      LRS.PiDefEq IH A₁ A₂ A₂ a₁ a₂ ∧
      LRS.LamDefEq IH M N A₁ A₂ f a₁ a₂) := by
  show (∃ A₁ A₂ u v, _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ LRS.LamDefEq IH _ _ _ _ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩) ↔ _
  simp only [Subtype.eta]
@[simp] theorem LRS.TmEq.sort_forallE :
    LRS.TmEq IH M N A (.sort r) (.forallE a₁ a₂) ↔ False := .rfl
@[simp] theorem LRS.TmEq.forallE_forallE :
    LRS.TmEq IH M N A (.forallE b g) (.forallE a₁ a₂) ↔ False := .rfl
@[simp] theorem LRS.TyEq.lam_m : LRS.TyEq IH M N (.lam f hf) ↔ True := .rfl

theorem LRS.TmEq.isType {IH : LogRel Γ n} :
    LRS.TmEq IH M N A m a → LRS.TyEq IH A A a := by
  cases a using WShape.casesOn' with
  | sort => rintro ⟨u, hA, _⟩; exact ⟨u, hA, hA⟩ | forallE => ?_ | _ => intro; trivial
  cases m using WShape.casesOn' with | bot => exact id | lam => ?_ | _ => intro; trivial
  rintro ⟨A₁, A₂, u, v, rA, hA1, hValA, hA₂, hE, _⟩
  exact ⟨A₁, A₂, A₁, A₂, u, v, rA, rA, hA1, hA₂, IH.left_ty hValA, hE.left⟩

/-- The successor-level logical relation, defined in terms of `IH : LogRel Γ n`.
Adds Π/λ handling on top of the level-0 `sort`/`bot` skeleton; all closure
properties are proved by case analysis on the `WShape (n+1)` indices. -/
def LRS (IH : LogRel Γ n) : LogRel Γ (n+1) where
  wf := IH.wf
  TmEq := LRS.TmEq IH
  TyEq := LRS.TyEq IH
  sort_iff := .rfl
  sort_iff_ty := .rfl
  bot {A a M N} hat := by
    cases hat.unfold with
    | bot => intro; trivial
    | sort => rintro ⟨u, hA1, _⟩; exact ⟨u, hA1, trivial⟩
    | forallE => exact id
  bot_ty := trivial
  isType := (·.isType)
  left_ty := .left
  left {M N A m a} := by
    dsimp [LRS.TmEq]; split <;> try trivial
    · exact fun ⟨u, whA, h⟩ => ⟨u, whA, h.left⟩
    · cases m using WShape.casesOn' with | lam => ?_ | _ => exact id
      intro ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩
      exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP.left⟩
  symm_ty := .symm
  symm {M N A m a} hMN := by
    dsimp [LRS.TmEq]; split <;> try trivial
    · exact fun ⟨u, whA, h⟩ => ⟨u, whA, h.symm⟩
    · cases m using WShape.casesOn' with | lam => ?_ | _ => exact id
      intro ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩
      exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP.symm (rA.1.defeqDF hMN)⟩
  trans_ty := .trans
  trans {M₁ M₂ A M₃ m a} hMN12 hMN23 := by
    dsimp [LRS.TmEq]; split <;> try trivial
    · exact fun ⟨u, whA, h12⟩ ⟨_, _, h23⟩ => ⟨u, whA, h12.trans h23⟩
    · split <;> (try trivial); · exact fun h _ => h
      intro ⟨B, F, u, v, rA, hA1, hA2, hA₂, hE, hP⟩ ⟨_, _, _, _, rA', _, _, _, _, hP'⟩
      cases rA.2.determ .forallE rA'.2 .forallE
      exact ⟨_, _, _, _, rA, hA1, hA2, hA₂, hE,
        hP.trans (rA.1.defeqDF hMN12) (rA.1.defeqDF hMN23) hP'⟩
  trans' {A₁ A₂ u a s A₃ v r} := by
    dsimp [LRS.TmEq]; split <;> try intros; trivial
    · exact fun ⟨u', whA, h12⟩ ⟨_, _, h23⟩ => ⟨u', whA, h12.trans h23⟩
    · split <;> try intros; trivial
      intro ⟨_, _, _, _, rA, _⟩; cases WHNF.sort.whRedS rA.2
  conv {A A' a M N m} := by
    cases a using WShape.casesOn with try simp only [LRS.TyEq.bot, LRS.TmEq.bot_a, imp_self,
      LRS.TyEq.sort_iff, LRS.TmEq.sort_a, LRS.TyEq.lam_m]
    | lam => exact fun _ => id
    | sort =>
      rintro ⟨u, rA, rA'⟩ ⟨_, hA, h⟩
      cases rA.2.determ .sort hA.2 .sort
      exact ⟨u, rA', h⟩
    | forallE a₁ a₂
    intro H; have ⟨B, F, B', F', u, v, rA, rA', hBB', hFF', hValB, hEdge⟩ := H
    cases m using WShape.casesOn' with
    | bot => exact fun _ => H.symm.left | lam => ?_ | _ => exact id
    intro ⟨_, _, _, v', rA₁, hA1, hValA, hA₂, hEdge₁, hP⟩
    cases rA.2.determ .forallE rA₁.2 .forallE
    refine ⟨_, _, _, _, rA', hBB'.hasType.2, IH.left_ty (IH.symm_ty hValB),
      hBB'.defeqDF_l IH.wf hFF'.hasType.2, ?_, ?_⟩
    · refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩ <;>
        have ha' := hBB'.symm.defeqDF ha
      · exact and_self_iff.2 (hEdge.1 hp ha' (IH.conv (IH.symm_ty hValB) a1)).2
      · exact (hEdge.1 hp ha' (IH.conv (IH.symm_ty hValB) a1)).2
    refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩ <;> (
      have a2 := IH.conv (IH.symm_ty hValB) a1
      have ha' := hBB'.symm.defeqDF ha
      have c := hEdge.2 hp ha'.hasType.1 (IH.left a2))
    · have ⟨v1, v2⟩ := hP.1 hp ha' a2; exact ⟨IH.conv c v1, IH.conv c v2⟩
    · exact IH.conv c (hP.2 hp ha' a2)
  toType := fun ⟨_, _, h⟩ => h
  mono_r_2 {a a' M N A m} le hm ht h := by
    cases a using WShape.casesOn' with
    | bot => trivial
    | sort => cases WShape.sort_le.1 le; exact h
    | forallE a₁ a₂ =>
      obtain ⟨a₁', a₂', le1, le2, rfl⟩ := WShape.forallE_le.1 le
      have ⟨_, hp, _⟩ := WShape.HasType.forallE_l.1 hm.isType
      have ⟨_, hp', _⟩ := WShape.HasType.forallE_l.1 ht
      cases m using WShape.casesOn' with
      | bot =>
        simp only [LRS.TmEq.bot_m] at h ⊢
        obtain ⟨B₁, F₁, B₂, F₂, u, v, rA1, rA2, hBB', hFF', hValB, hEdge⟩ := h
        have hpi := (WShape.HasTypePi.iff.1 hp).1.isType
        have hpi' := (WShape.HasTypePi.iff.1 hp').1.isType
        exact ⟨B₁, F₁, B₂, F₂, u, v, rA1, rA2, hBB', hFF',
          IH.mono_r_2_ty le1 hpi hpi' hValB,
          hEdge.mono_r_2 le1 le2 hp hp' (IH.left_ty hValB)⟩
      | lam f hf =>
        simp only [LRS.TmEq.lam_forallE] at h ⊢
        have ⟨_, hp, _⟩ := WShape.HasType.forallE_l.1 hm.isType
        have ⟨_, hp', _⟩ := WShape.HasType.forallE_l.1 ht
        obtain ⟨g, hg, hm'⟩ := WShape.HasType.forallE_inv hm
        have hgf : g = f := by
          have := congrArg (·.1) hg; simp only [WShape.lam, WShape.lam'] at this
          split at this
          · injection this with this; exact WShapeFun.ext this.symm
          · cases this
        subst hgf
        let ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hEdge, hP⟩ := h
        have ht := (WShape.HasTypePi.iff.1 hp).1.isType
        have ht' := (WShape.HasTypePi.iff.1 hp').1.isType
        refine ⟨A₁, A₂, u, v, rA, hA1, IH.mono_r_2_ty le1 ht ht' hA2, hA₂, ?_⟩
        exact ⟨hEdge.mono_r_2 le1 le2 hp hp' hA2, hP.mono_r_2 le1 le2 hm' hA2 hp'⟩
      | sort => simp [LRS.TmEq.sort_forallE] at h
      | forallE => simp [LRS.TmEq.forallE_forallE] at h
    | lam f hf => exact absurd hm.isType WShape.HasType.lam_isType
  mono_r_2_ty {a a' A B} le ha ha' h := by
    cases a using WShape.casesOn' with
    | bot => trivial
    | sort => simp [LRS.TyEq] at h ⊢; cases WShape.sort_le.1 le; exact h
    | forallE a₁ a₂ =>
      simp [LRS.TyEq] at h ⊢
      obtain ⟨a₁', a₂', le1, le2, rfl⟩ := WShape.forallE_le.1 le
      have ⟨_, hp, _⟩ := WShape.HasType.forallE_l.1 ha
      have ⟨_, hp', _⟩ := WShape.HasType.forallE_l.1 ha'
      let ⟨B₁, F₁, B₂, F₂, u, v, rA, rB, hBB', hFF', hValB, hEdge⟩ := h
      have ht := (WShape.HasTypePi.iff.1 hp).1.isType
      have ht' := (WShape.HasTypePi.iff.1 hp').1.isType
      refine ⟨B₁, F₁, B₂, F₂, u, v, rA, rB, hBB', hFF', IH.mono_r_2_ty le1 ht ht' hValB, ?_⟩
      exact hEdge.mono_r_2 le1 le2 hp hp' (IH.left_ty hValB)
    | lam f hf => simp [LRS.TyEq.lam_m]
  mono_r_1 {a a' A M N m} le ha ha' hA h := by
    cases a' using WShape.casesOn' with
    | bot => simp only [LRS.TmEq.bot_a]
    | sort r =>
      obtain rfl | rfl := WShape.le_sort.1 le
      · cases ha.bot_r; obtain ⟨u, hA1, _⟩ := hA; exact ⟨u, hA1, trivial⟩
      · exact h
    | forallE a₁' a₂' =>
      obtain rfl | ⟨a₁, a₂, rfl, le1, le2⟩ := WShape.le_forallE_iff.1 le
      · cases ha.bot_r; exact hA
      · cases m using WShape.casesOn' with
        | bot => exact hA
        | lam f hf =>
          simp only [LRS.TmEq.lam_forallE] at h ⊢
          obtain ⟨g, hg, hm_lam⟩ := WShape.HasType.forallE_inv ha
          have hgf' : (WShape.lam f hf).1 = (WShape.lam' g).1 := congrArg (·.1) hg
          simp only [WShape.lam, WShape.lam'] at hgf'; split at hgf'
          · injection hgf' with hgf'
            have := WShapeFun.ext hgf'.symm; subst this  -- now f = g
            obtain ⟨g', hg', hm'_lam⟩ := WShape.HasType.forallE_inv ha'
            have hgf2 : (WShape.lam g hf).1 = (WShape.lam' g').1 := congrArg (·.1) hg'
            simp only [WShape.lam, WShape.lam'] at hgf2; split at hgf2
            · injection hgf2 with hgf2; have := WShapeFun.ext hgf2.symm; subst this
              let ⟨A₁, A₂, u, v, rA, hA1, hValA, hA₂, hEdge_src, hP⟩ := h
              let ⟨B₁, F₁, B₂, F₂, u', v', rA', rA'', hBB_tgt, hFF_tgt, hValB_tgt, hEdge_tgt⟩ := hA
              cases rA.2.determ .forallE rA'.2 .forallE
              cases rA.2.determ .forallE rA''.2 .forallE
              refine ⟨_, _, _, _, rA, hBB_tgt.hasType.1, hValB_tgt, hA₂, hEdge_tgt, ?_⟩
              exact hP.mono_r_1 le1 le2 hm_lam hm'_lam hEdge_tgt
            · cases hgf2
          · cases hgf'
        | sort => exact (LRS.TmEq.sort_forallE.1 h).elim
        | forallE => exact (LRS.TmEq.forallE_forallE.1 h).elim
      | lam f hf => exact absurd ha'.isType WShape.HasType.lam_isType
  mono_l {m m' M N A a} le hm hm' h := by
    cases a using WShape.casesOn' with
    | bot => simp only [LRS.TmEq.bot_a]
    | sort r =>
      obtain ⟨u, whA, h⟩ := h; refine ⟨u, whA, ?_⟩
      cases m using WShape.casesOn' with
      | sort => cases WShape.sort_le.1 le; exact h | forallE s f => ?_ | _ => trivial
      obtain ⟨s', f', h1, h2, rfl⟩ := WShape.forallE_le.1 le
      have ⟨_, hm_pi, _⟩ := WShape.HasType.forallE_l.1 hm
      have ⟨_, hm'_pi, _⟩ := WShape.HasType.forallE_l.1 hm'
      let ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hBB', hFF', hValB, hEdge⟩ := h
      have ht := (WShape.HasTypePi.iff.1 hm_pi).1.isType
      have ht' := (WShape.HasTypePi.iff.1 hm'_pi).1.isType
      exact ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hBB', hFF', IH.mono_r_2_ty h1 ht ht' hValB,
        hEdge.mono_r_2 h1 h2 hm_pi hm'_pi (IH.left_ty hValB)⟩
    | forallE a₁ a₂ =>
      cases m using WShape.casesOn' with | bot => exact h.isType | lam f hf => ?_ | _ => cases hm
      obtain ⟨g, hg, hm_lam⟩ := WShape.HasType.forallE_inv hm
      have hgf' : (WShape.lam f hf).1 = (WShape.lam' g).1 := congrArg (·.1) hg
      simp only [WShape.lam, WShape.lam'] at hgf'; split at hgf' <;> [skip; cases hgf']
      injection hgf' with hgf'; have := WShapeFun.ext hgf'.symm; subst this
      obtain ⟨g'', rfl, hm'_lam⟩ := WShape.HasType.forallE_inv hm'
      simp only [WShape.lam'] at le; split at le <;> [skip; cases WShape.le_bot.1 le]
      rename_i hg''nz
      let ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩ := WShape.lam_eq_lam' (hl := hg''nz) ▸ h
      exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP.mono_l le hm_lam hm'_lam⟩
    | _ => cases hm.isType
  join_ty {A B m₁ m₂} hC hm₁ hm₂ h1 h2 := by
    cases hm₁.unfold with
    | bot h₁ => rwa [WShape.bot_join]
    | sort =>
      cases hm₂.unfold with
      | bot => rwa [WShape.join_bot]
      | sort =>
        simp only [WShape.sort_join_sort] at h1 h2 ⊢
        split <;> simp_all only [LRS.TyEq.sort_iff, WShape.Compat.sort_sort]
      | _ => cases hC
    | forallE hp₁ =>
      cases hm₂.unfold with | bot => rwa [WShape.join_bot] | forallE hp₂ => ?_ | _ => cases hC
      simp only [LRS.TyEq.forallE_iff] at h1 h2
      simp [WShape.Compat, WShape.forallE, Shape.Compat] at hC
      let ⟨B₁, F₁, B₂, F₂, u, v, rA, rB, hBB, hFF, hValB₁, hEdge₁⟩ := h1
      let ⟨_, _, _, _, u', v', rA', rB', hBB', hFF', hValB₂, hEdge₂⟩ := h2
      cases rA.2.determ .forallE rA'.2 .forallE
      cases rB.2.determ .forallE rB'.2 .forallE
      simp only [LRS.TyEq.forallE_iff, WShape.forallE_join_forallE hC.1 hC.2]
      have ht₁ := (WShape.HasTypePi.iff.1 hp₁).1.isType
      have ht₂ := (WShape.HasTypePi.iff.1 hp₂).1.isType
      refine ⟨B₁, F₁, B₂, F₂, u, v, rA, rB, hBB, hFF, IH.join_ty hC.1 ht₁ ht₂ hValB₁ hValB₂, ?_⟩
      exact .join ht₁ ht₂ hC.1 hp₁ hp₂ hC.2 hEdge₁ hEdge₂
  whr {M M' A N N' m a} hM hN hMN := by
    cases a using WShape.casesOn' with
    | sort =>
      cases m using WShape.casesOn' with
      | sort =>
        constructor <;> rintro ⟨u, whA, h⟩ <;> (
          have hM' := IsDefEq.defeqDF whA.1 hM.1
          have hN' := IsDefEq.defeqDF whA.1 hN.1
          obtain ⟨v, r1, r2⟩ := h
          refine ⟨u, whA, v, ?_, ?_⟩)
        · exact ⟨(r1.1.symm.trans' hM').symm, hM.2.determ_l r1.2 .sort⟩
        · exact ⟨(r2.1.symm.trans' hN').symm, hN.2.determ_l r2.2 .sort⟩
        · exact ⟨(r1.1.symm.trans' hM'.symm).symm, .trans hM.2 r1.2⟩
        · exact ⟨(r2.1.symm.trans' hN'.symm).symm, .trans hN.2 r2.2⟩
      | forallE =>
        constructor <;> rintro ⟨u, whA, h⟩ <;> (
          have hM' := IsDefEq.defeqDF whA.1 hM.1
          have hN' := IsDefEq.defeqDF whA.1 hN.1
          obtain ⟨B₁, F₁, B₂, F₂, v₁, v₂, rM, rN, rest⟩ := h
          refine ⟨u, whA, B₁, F₁, B₂, F₂, v₁, v₂, ?_, ?_, rest⟩)
        · exact ⟨(rM.1.symm.trans' hM').symm, hM.2.determ_l rM.2 .forallE⟩
        · exact ⟨(rN.1.symm.trans' hN').symm, hN.2.determ_l rN.2 .forallE⟩
        · exact ⟨(rM.1.symm.trans' hM'.symm).symm, .trans hM.2 rM.2⟩
        · exact ⟨(rN.1.symm.trans' hN'.symm).symm, .trans hN.2 rN.2⟩
      | _ => rfl
    | forallE =>
      cases m using WShape.casesOn' with | lam => ?_ | _ => rfl
      constructor <;> intro ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩ <;>
        have' := LRS.LamDefEq.whr ⟨rA.1.defeqDF hM.1, hM.2⟩ ⟨rA.1.defeqDF hN.1, hN.2⟩
          (rA.1.defeqDF hMN)
      · exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, this.1 hP⟩
      · exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, this.2 hP⟩
    | _ => rfl

/-- The full logical relation at arbitrary level `n`, defined by recursion
on `n` from `LR0` (base) and `LRS` (step). Use this in client lemmas;
the level-specific definitions are an implementation detail. -/
def LR {Γ : List Term} (hΓ : ⊢ Γ) : LogRel Γ n :=
  match n with
  | 0 => LR0 hΓ
  | _+1 => LRS (LR hΓ)

private theorem LRS.PiDefEq.lift_aux
    {b : WShape n} {f : WShapeFun n} (le : n ≤ n') (htpi_a : WShape.HasTypePi f b true)
    (IH1 : ∀ {M N : Term} {m : WShape n}, WShape.HasType m .type →
      ((LR Γ).TyEq M N (m.lift n') ↔ (LR Γ).TyEq M N m))
    (IH2 : ∀ {M N A : Term} {m a : WShape n}, WShape.HasType m a →
      ((LR Γ).TmEq M N A (m.lift n') (a.lift _) ↔ (LR Γ).TmEq M N A m a)) :
    LRS.PiDefEq (LR Γ) B F₁ F₂ (b.lift n') (f.lift n') ↔
    LRS.PiDefEq (LR Γ) B F₁ F₂ b f := by
  have htpi_w := WShape.HasTypePi.iff.1 htpi_a
  constructor <;> intro hEdge
  · refine ⟨fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩ <;> (
      have hp' := (WShape.HasType.lift le).2 hp
      have v' := (IH2 hp).2 v)
    · have ⟨r1, r2⟩ := hEdge.1 hp' ha v'
      exact ⟨(IH1 (htpi_w.2 _ hp)).1 (WShapeFun.lift_app le ▸ r1),
             (IH1 (htpi_w.2 _ hp)).1 (WShapeFun.lift_app le ▸ r2)⟩
    · exact (IH1 (htpi_w.2 _ hp)).1 (WShapeFun.lift_app le ▸ hEdge.2 hp' ha v')
  · refine ⟨fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩ <;> (
      obtain ⟨q, d1, d2⟩ := WShapeFun.app_eq (f.lift n') _
      obtain ⟨q₀, y₀, d2₀, rfl, d3⟩ := (WShapeFun.mem_lift le).1 d2
      obtain ⟨qx', qy', d2₀', qxle, qyle, hq⟩ := WShape.HasDom.def.1 htpi_a.1 _ _ d2₀
      have v' := (IH2 hq).1 ((LR Γ).mono_l (((WShape.lift_le_lift le).2 qxle).trans d1)
        ((WShape.HasType.lift le).2 hq) hp v))
    · have ⟨r1, r2⟩ := hEdge.1 hq ha v'
      have ht_q := (htpi_w.2 _ hq).toType
      have ht_y₀ : (y₀ : WShape n).HasType WShape.type := (htpi_a.2 _ _ d2₀).toType
      have y₀_le_fqx : y₀ ≤ f.app qx' := qyle.trans (f.app_of_mem d2₀').2
      have ht_q_l : ((f.app qx').lift n').HasType WShape.type := by
        have := (WShape.HasType.lift le).2 ht_q; rwa [WShape.lift_sort] at this
      have ht_y₀_l : (y₀.lift n').HasType WShape.type := by
        have := (WShape.HasType.lift le).2 ht_y₀; rwa [WShape.lift_sort] at this
      exact d3 ▸ ⟨
        (LR Γ).mono_r_2_ty (WShape.lift_mono le y₀_le_fqx) ht_y₀_l ht_q_l ((IH1 ht_q).2 r1),
        (LR Γ).mono_r_2_ty (WShape.lift_mono le y₀_le_fqx) ht_y₀_l ht_q_l ((IH1 ht_q).2 r2)⟩
    · have hq_body := hEdge.2 hq ha v'
      have ht_q := (htpi_w.2 _ hq).toType
      have ht_y₀ : (y₀ : WShape n).HasType WShape.type := (htpi_a.2 _ _ d2₀).toType
      have y₀_le_fqx : y₀ ≤ f.app qx' := qyle.trans (f.app_of_mem d2₀').2
      have ht_q_l : ((f.app qx').lift n').HasType WShape.type := by
        have := (WShape.HasType.lift le).2 ht_q; rwa [WShape.lift_sort] at this
      have ht_y₀_l : (y₀.lift n').HasType WShape.type := by
        have := (WShape.HasType.lift le).2 ht_y₀; rwa [WShape.lift_sort] at this
      exact d3 ▸
        (LR Γ).mono_r_2_ty (WShape.lift_mono le y₀_le_fqx) ht_y₀_l ht_q_l ((IH1 ht_q).2 hq_body)

private theorem LRS.LamDefEq.lift_aux
    {g : WShapeFun n} {a₁ a₂} (le : n ≤ n') (htm : WShape.HasTypeLam g a₁ a₂)
    (IH : ∀ {M N A : Term} {m a : WShape n}, WShape.HasType m a →
      ((LR Γ).TmEq M N A (m.lift n') (a.lift _) ↔ (LR Γ).TmEq M N A m a))
    (hEdge : LRS.PiDefEq (LR Γ) A₁ A₂ A₂ a₁ a₂) :
    LRS.LamDefEq (LR Γ) (n := n') M N A₁ A₂ (g.lift n') (a₁.lift n') (a₂.lift n') ↔
    LRS.LamDefEq (LR Γ) M N A₁ A₂ g a₁ a₂ := by
  have htm_w := WShape.HasTypeLam.iff.1 htm
  constructor <;> intro hP
  · refine ⟨fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩ <;> (
      have hp' := (WShape.HasType.lift le).2 hp
      have v' := (IH hp).2 v)
    · have ⟨r1, r2⟩ := hP.1 hp' ha v'
      refine ⟨(IH (htm_w.2.2 _ hp)).1 ?_, (IH (htm_w.2.2 _ hp)).1 ?_⟩
        <;> rw [WShapeFun.lift_app le, WShapeFun.lift_app le] <;> [exact r1; exact r2]
    · apply (IH (htm_w.2.2 _ hp)).1
      rw [WShapeFun.lift_app le, WShapeFun.lift_app le]
      exact hP.2 hp' ha v'
  · refine ⟨fun a' b' p hp ha v => ?_, fun a' p hp ha v => ?_⟩
    all_goals
      obtain ⟨_, dg1, dg2⟩ := WShapeFun.app_eq (g.lift n') p
      obtain ⟨_, da1, da2⟩ := WShapeFun.app_eq (a₂.lift n') p
      obtain ⟨qg, yg, dg2₀, rfl, dg3⟩ := (WShapeFun.mem_lift le).1 dg2
      obtain ⟨qa, ya, da2₀, rfl, da3⟩ := (WShapeFun.mem_lift le).1 da2
      have ⟨yg₁, yg₂⟩ := WShapeFun.app_of_mem dg2₀
      have ⟨ya₁, ya₂⟩ := WShapeFun.app_of_mem da2₀
      have ⟨qg', qg'le, hqg, qg'app⟩ := WShape.HasDom.iff.1 htm.2.1 qg
      have ⟨qa', qa'le, hqa, qa'app⟩ := WShape.HasDom.iff.1 htm.1.1 qa
      rw [dg3, da3]
      have v_lo := (IH hqg).1 <| (LR Γ).mono_l
        (((WShape.lift_le_lift le).2 qg'le).trans dg1) ((WShape.HasType.lift le).2 hqg) hp v
      have v_lo_qa := (IH hqa).1 <| (LR Γ).mono_l
        (((WShape.lift_le_lift le).2 qa'le).trans da1) ((WShape.HasType.lift le).2 hqa) hp v
      have ht_lo := htm_w.2.2 _ hqg
      have htm_p := WShape.HasTypePi.iff'.1 htm_w.1
      have vt_qa := hEdge.2 hqa ha.hasType.1 ((LR Γ).left v_lo_qa)
      have vt_qa' := (LR Γ).mono_r_2_ty qa'app (htm_p.2 qa) (htm_p.2 qa') vt_qa
      have ya_sort := (htm_p.2 qa).mono_l ya₁ ya₂
      have ht_yg_qg' : yg.HasType (a₂.app qg') :=
        ht_lo.mono_l (WShapeFun.app_mono_r qg'le |>.trans yg₁) (yg₂.trans qg'app)
      have le_a2_ya := by
        refine (a₂.app_mono_r qg'le).trans (.trans ?_ ya₁)
        rw [← WShape.lift_le_lift le, WShapeFun.lift_app le]
        exact (WShapeFun.app_mono_r dg1 (f := a₂.lift n')).trans <| da3 ▸ WShape.lift_mono le ya₂
      have ya_sort := (htm_p.2 qa).mono_l ya₁ ya₂
      have ht_yg := ya_sort.mono_r le_a2_ya ht_yg_qg'
      have vt_ya := (LR Γ).mono_r_2_ty ya₂ ya_sort (htm_p.2 qa) vt_qa'
      have go {M N} (r : (LR Γ).TmEq M N (A₂.inst a') (g.app qg') (a₂.app qg')) :
          (LR Γ).TmEq M N (A₂.inst a') (yg.lift n') (ya.lift n') :=
        (IH ht_yg).2 <|
        (LR Γ).mono_r_1 le_a2_ya ht_yg_qg' ht_yg vt_ya <|
        (LR Γ).mono_l (yg₂.trans qg'app) ht_yg_qg' ht_lo r
    · have ⟨r1, r2⟩ := hP.1 hqg ha v_lo; exact ⟨go r1, go r2⟩
    · exact go (hP.2 hqg ha v_lo)

private theorem LR.lift_succ_aux :
    (∀ {M N : Term} {m : WShape n}, WShape.HasType m .type →
      (LRS.TyEq (n := n) (LR Γ) M N (m.lift _) ↔ (LR Γ).TyEq M N m)) ∧
    (∀ {M N A : Term} {m a : WShape n}, WShape.HasType m a →
      (LRS.TmEq (n := n) (LR Γ) M N A (m.lift _) (a.lift _) ↔ (LR Γ).TmEq M N A m a)) := by
  induction n with
  | zero =>
    refine ⟨fun {M N m} _ => ?_, fun {M N A m a} _ => ?_⟩
    · cases m using WShape.casesOn <;> trivial
    · cases m using WShape.casesOn <;> cases a using WShape.casesOn <;> trivial
  | succ k ih =>
    refine have h1 := ?_; ⟨h1, ?_⟩
    · intro M N m hmt
      cases m using WShape.casesOn' with
      | forallE b f => ?_ | _ => constructor <;> intro <;> trivial
      rw [WShape.lift_forallE (Nat.le_succ k)]
      have ⟨_, htpi, rfl⟩ := WShape.HasType.forallE_l.1 hmt
      constructor <;> intro ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hB, hF, hValB, hE⟩ <;>
        refine ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hB, hF, ?_, ?_⟩
      · exact (ih.1 (WShape.HasTypePi.iff.1 htpi).1.isType).1 hValB
      · exact (LRS.PiDefEq.lift_aux (Nat.le_succ k) htpi ih.1 ih.2).1 hE
      · exact (ih.1 (WShape.HasTypePi.iff.1 htpi).1.isType).2 hValB
      · exact (LRS.PiDefEq.lift_aux (Nat.le_succ k) htpi ih.1 ih.2).2 hE
    · intro M N A m a hma
      cases a using WShape.casesOn' with
      | bot => constructor <;> intro <;> trivial
      | sort =>
        constructor <;> rintro ⟨u, whA, h⟩
        · exact ⟨u, whA, (h1 hma.toType).1 h⟩
        · exact ⟨u, whA, (h1 hma.toType).2 h⟩
      | forallE a₁ a₂ => ?_ | _ => cases hma.isType
      have ⟨_, htpi_a, rfl⟩ := WShape.HasType.forallE_l.1 hma.isType
      obtain ⟨g, rfl, htm⟩ := WShape.HasType.forallE_inv hma
      unfold WShape.lam'; split
      · rw [WShape.lift_lam (Nat.le_succ k), WShape.lift_forallE (Nat.le_succ k)]
        simp only [LRS.TmEq.lam_forallE]
        constructor <;> intro ⟨A₁, A₂, u, v, rA, hA1, hValA, hA₂, hEdge, hP⟩ <;>
          [ have hEdge' := (LRS.PiDefEq.lift_aux (Nat.le_succ k) htm.1 ih.1 ih.2).1 hEdge;
            have hEdge' := (LRS.PiDefEq.lift_aux (Nat.le_succ k) htm.1 ih.1 ih.2).2 hEdge ] <;>
          refine ⟨A₁, A₂, u, v, rA, hA1, ?_, hA₂, hEdge', ?_⟩
        · exact (ih.1 (WShape.HasTypePi.iff.1 htpi_a).1.isType).1 hValA
        · exact (LRS.LamDefEq.lift_aux (Nat.le_succ k) htm ih.2 hEdge').1 hP
        · exact (ih.1 (WShape.HasTypePi.iff.1 htpi_a).1.isType).2 hValA
        · exact (LRS.LamDefEq.lift_aux (Nat.le_succ k) htm ih.2 hEdge).2 hP
      · simp only [WShape.lift_bot, WShape.lift_forallE (Nat.le_succ k), LRS.TmEq.bot_m]
        constructor <;>
          intro ⟨B₁, F₁, B₂, F₂, u, v, rA1, rA2, hBB', hFF', hValB, hEdge⟩ <;>
          refine ⟨B₁, F₁, B₂, F₂, u, v, rA1, rA2, hBB', hFF', ?_, ?_⟩
        · exact (ih.1 (WShape.HasTypePi.iff.1 htpi_a).1.isType).1 hValB
        · exact (LRS.PiDefEq.lift_aux (Nat.le_succ k) htpi_a ih.1 ih.2).1 hEdge
        · exact (ih.1 (WShape.HasTypePi.iff.1 htpi_a).1.isType).2 hValB
        · exact (LRS.PiDefEq.lift_aux (Nat.le_succ k) htpi_a ih.1 ih.2).2 hEdge

theorem LR.TmEq.lift {m a : WShape n} (le : n ≤ n') (hma : WShape.HasType m a) :
    (LR Γ).TmEq M N A (m.lift n') (a.lift _) ↔ (LR Γ).TmEq M N A m a := by
  induction le with | refl => simp [WShape.lift_self] | step le ih
  rw [(WShape.lift_lift (.inl le)).symm, (WShape.lift_lift (s := a) (.inl le)).symm]
  exact (LR.lift_succ_aux.2 ((WShape.HasType.lift le).2 hma)).trans ih

theorem LR.TyEq.lift {m : WShape n} (le : n ≤ n') (hmt : WShape.HasType m .type) :
    (LR Γ).TyEq (n := n') M N (m.lift _) ↔ (LR Γ).TyEq M N m := by
  induction le with | refl => simp [WShape.lift_self] | step le ih
  rw [(WShape.lift_lift (.inl le)).symm]
  have := (WShape.HasType.lift le).2 hmt
  simp [WShape.type] at this
  exact (LR.lift_succ_aux.1 this).trans ih
