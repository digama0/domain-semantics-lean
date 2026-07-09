import DomainSemantics.Sound
import DomainSemantics.LogRel

/-! # Adequacy: the fundamental theorem of the logical relation

This file proves the central theorem `LR.adequacy`: every `IsDefEq`
derivation is realised by the logical relation under every well-formed
substitution. From it we derive the principal inversion lemmas needed
downstream — `forallE_inv`, `sort_inv`, `sort_forallE_inv` — which
encode Pi and sort injectivity for the weak defeq judgment.

The machinery:
* `LR.Subst1` is the per-binding payload for a substitution: syntactic
  equality plus a semantic realiser in the logical relation.
* `LR.SubstWF Γ₀ σ σ' Γ ρ` is the two-sided substitution well-formedness
  predicate, built up from `Subst1` witnesses.
* `LR.Adequate` is the property the fundamental theorem proves by
  induction on the derivation. -/

namespace DomainSemantics

/-- Per-binding substitution well-formedness: at the new variable, the two
substituted terms (`x`, `x'`) are syntactically equal at type `A`, and
semantically they realise the logical relation at type-shape `a`. Used
as the per-step payload of `LR.SubstWF`. -/
def LR.Subst1 (Γ₀ : List Term) (x x' A₀ A A' : Term) (ρ : Valuation) (i := 0) : Prop :=
  Γ₀ ⊢ x ≡ x' : A ∧ ∃ hΓ₀ : ⊢ Γ₀, ∀ {{n}} (a : WShape n), LE_Interp ρ a.T A₀ →
    (a.HasType .type → (∃ u, Γ₀ ⊢ A ≡ A' : .sort u) ∧ (LR hΓ₀).TyEq A A' a) ∧
    ∀ {{m : WShape n}}, LE_Interp ρ m.T (.bvar i) → m.HasType a → (LR hΓ₀).TmEq x x' A m a

/-- A two-sided substitution `σ, σ'` from `Γ₀` into `Γ` whose semantic
content is realised by the valuation `ρ`. Each `cons` step bundles a
`Subst1` witness for the new variable; `id` is the identity substitution
at any well-formed context. This is the substitution domain of the
fundamental theorem. -/
inductive LR.SubstWF (Γ₀ : List Term) : Subst → Subst → List Term → Valuation → Prop where
  | id : ⊢ Γ₀ → LR.SubstWF Γ₀ .id .id Γ₀ .nil
  | cons : LR.SubstWF Γ₀ σ.tail σ'.tail Γ ρ →
    (∀ {a}, LE_Interp ρ a A →
      ∃ a', a ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .type) →
    LE_Interp ρ a A → x.HasType a → Γ ⊢ A : .sort u →
    LR.Subst1 Γ₀ σ.head σ'.head A.lift (A.subst σ.tail) (A.subst σ'.tail) (ρ.push x) →
    LR.SubstWF Γ₀ σ σ' (A :: Γ) (ρ.push x)

theorem LR.SubstWF.fits : LR.SubstWF Γ₀ σ σ' Γ ρ → ρ.Fits Γ₀ Γ
  | .id _ => .nil
  | .cons W h1 h2 h3 _ _ => .cons W.fits h1 h2 h3

theorem LR.SubstWF.wf : LR.SubstWF Γ₀ σ σ' Γ ρ → ⊢ Γ
  | .id hWF => hWF
  | .cons W _ _ _ hA _ => ⟨W.wf, _, hA⟩

theorem LR.SubstWF.wf₀ : LR.SubstWF Γ₀ σ σ' Γ ρ → ⊢ Γ₀
  | .id hWF => hWF
  | .cons W _ _ _ _ _ => W.wf₀

theorem LR.SubstWF.toSubstEq (W : LR.SubstWF Γ₀ σ σ' Γ ρ) :
    Ctx.SubstEq Γ₀ σ σ' Γ := by
  induction W with
  | id hWF => exact Ctx.SubstEq.id hWF
  | cons W h1 h2 h3 hA h0 ih => exact .cons ih hA h0.1

theorem LR.SubstWF.left (W : LR.SubstWF Γ₀ σ σ' Γ ρ) : LR.SubstWF Γ₀ σ σ Γ ρ := by
  induction W with
  | id hWF => exact .id hWF
  | cons _ h1 h2 h3 hA h0 ih =>
    have ⟨a1, _, a2⟩ := h0
    refine .cons ih h1 h2 h3 hA ⟨a1.hasType.1, ih.wf₀, fun _ a ha => ?_⟩
    refine ⟨fun ht => ?_, fun _ hM hmem => ?_⟩
    · have ⟨⟨_, h1⟩, h2⟩ := (a2 a ha).1 ht; exact ⟨⟨_, h1.hasType.1⟩, (LR _).left_ty h2⟩
    · exact (LR _).left <| (a2 a ha).2 hM hmem

theorem LR.SubstWF.symm (W : LR.SubstWF Γ₀ σ σ' Γ ρ) : LR.SubstWF Γ₀ σ' σ Γ ρ := by
  induction W with
  | id hWF => exact .id hWF
  | cons _ h1 h2 h3 hA h0 ih =>
    have ⟨a1, _, a2⟩ := h0
    refine .cons ih h1 h2 h3 hA ⟨?_, ih.wf₀, fun _ a ha => ⟨fun ht => ?_, fun _ hM hmem => ?_⟩⟩
    · have ⟨⟨_, h1⟩, _⟩ := (a2 (n := 0) _ .bot).1 (.bot .sort)
      exact h1.defeqDF h0.1.symm
    · exact let ⟨⟨u, h1⟩, h2⟩ := (a2 a ha).1 ht; ⟨⟨u, h1.symm⟩, (LR _).symm_ty h2⟩
    · let ⟨_, h2⟩ := (a2 a ha).1 hmem.isType
      exact (LR _).conv h2 ((LR _).symm a1 ((a2 a ha).2 hM hmem))

/-- Adequacy at `(M, N, A, m, a)`: for every two-sided `SubstWF`, both
substituted sides satisfy `TmEq` at the substituted type; and for every
diagonal `SubstWF`, the two substituted forms agree. This is the
property the fundamental theorem (`LR.adequacy`) proves by induction on
the IsDefEq derivation. -/
def LR.Adequate (Γ₀ Γ : List Term) (ρ : Valuation) (M N A : Term) (m a : WShape n) :=
  (∀ {{σ σ'}} (W : LR.SubstWF Γ₀ σ σ' Γ ρ),
    (LR W.wf₀).TmEq (M.subst σ) (M.subst σ') (A.subst σ) m a ∧
    (LR W.wf₀).TmEq (N.subst σ) (N.subst σ') (A.subst σ) m a) ∧
  ∀ {{σ}} (W : LR.SubstWF Γ₀ σ σ Γ ρ), (LR W.wf₀).TmEq (M.subst σ) (N.subst σ) (A.subst σ) m a

theorem LR.Adequate.bot
    (HtyA : ∀ {{σ}} (W : LR.SubstWF Γ₀ σ σ Γ ρ), (LR W.wf₀).TyEq (A.subst σ) (A.subst σ) a)
    (ha : a.HasType .type) : Adequate Γ₀ Γ ρ M N A .bot a :=
  ⟨fun _ _ W => ⟨(LR _).bot ha (HtyA W.left), (LR _).bot ha (HtyA W.left)⟩,
   fun _ W => (LR _).bot ha (HtyA W)⟩

theorem LR.Adequate.fits
    (H : ρ.Fits Γ₀ Γ → Adequate Γ₀ Γ ρ M N A m a) : Adequate Γ₀ Γ ρ M N A m a :=
  ⟨fun _ _ W => (H W.fits).1 W, fun _ W => (H W.fits).2 W⟩

theorem LR.Adequate.wf (H : ⊢ Γ → Adequate Γ₀ Γ ρ M N A m a) : Adequate Γ₀ Γ ρ M N A m a :=
  ⟨fun _ _ W => (H W.wf).1 W, fun _ W => (H W.wf).2 W⟩

theorem LR.Adequate.wf₀ (H : ⊢ Γ₀ → Adequate Γ₀ Γ ρ M N A m a) : Adequate Γ₀ Γ ρ M N A m a :=
  ⟨fun _ _ W => (H W.wf₀).1 W, fun _ W => (H W.wf₀).2 W⟩

theorem LR.Adequate.refl
    (H : ∀ {{σ σ'}}, ∀ s : LR.SubstWF Γ₀ σ σ' Γ ρ,
      (LR s.wf₀).TmEq (M.subst σ) (M.subst σ') (A.subst σ) m a) :
    Adequate Γ₀ Γ ρ M M A m a := ⟨fun _ _ W => ⟨H W, H W⟩, fun _ W => H W⟩

theorem LR.Adequate.left : Adequate Γ₀ Γ ρ M N A m a → Adequate Γ₀ Γ ρ M M A m a
  | ⟨h1, _⟩ => .refl fun _ _ W => (h1 W).1

theorem LR.Adequate.symm (H : Γ ⊢ M ≡ N : A) :
    Adequate Γ₀ Γ ρ M N A m a → Adequate Γ₀ Γ ρ N M A m a
  | ⟨h1, h2⟩ =>
    ⟨fun _ _ W => (h1 W).symm, fun _ W => (LR _).symm (H.subst' W.wf₀ W.toSubstEq) (h2 W)⟩

theorem LR.Adequate.trans (H12 : Γ ⊢ M₁ ≡ M₂ : A) (H23 : Γ ⊢ M₂ ≡ M₃ : A) :
    Adequate Γ₀ Γ ρ M₁ M₂ A m a → Adequate Γ₀ Γ ρ M₂ M₃ A m a → Adequate Γ₀ Γ ρ M₁ M₃ A m a
  | ⟨a1, a2⟩, ⟨b1, b2⟩ =>
    ⟨fun _ _ W => ⟨(a1 W).1, (b1 W).2⟩, fun _ W => (LR _).trans (H12.subst' W.wf₀ W.toSubstEq)
      (H23.subst' W.wf₀ W.toSubstEq) (a2 W) (b2 W)⟩

theorem LR.Adequate.trans' (H12 : Γ ⊢ A₁ ≡ A₂ : .sort u) (H23 : Γ ⊢ A₂ ≡ A₃ : .sort v) :
    Adequate Γ₀ Γ ρ A₁ A₂ (.sort u) a s →
    Adequate Γ₀ Γ ρ A₂ A₃ (.sort v) a (.sort r) → Adequate Γ₀ Γ ρ A₁ A₃ (.sort u) a s
  | ⟨a1, a2⟩, ⟨b1, b2⟩ => by
    refine ⟨fun _ _ W => ⟨(a1 W).1, ?_⟩, fun _ W => (LR _).trans' (a2 W) (b2 W)⟩
    have h1 := (LR _).trans' (a2 W.left) (b2 W.left)
    refine (LR _).trans' ((LR _).left ((LR _).symm ?_ h1)) (b1 W).2
    exact (H12.trans' H23).subst' W.wf₀ W.left.toSubstEq

theorem LR.Adequate.cons {hΓ₀ : ⊢ Γ₀}
    (ihA : ∀ {ρ n} {m a : WShape n}, LE_Interp ρ m.T A → LE_Interp ρ a.T (.sort u) →
      m.HasType a → Adequate Γ₀ Γ ρ A A' (.sort u) m a)
    (HA : Γ ⊢ A ≡ A' : .sort u)
    {{k : Nat}} {{a₁ p : WShape k}} {{x x' σ σ' ρ}}
    (hp : p.HasType a₁) (hA₁ : LE_Interp ρ a₁.T A)
    (hx : Γ₀ ⊢ x ≡ x' : A.subst σ) (hv : (LR hΓ₀).TmEq x x' (A.subst σ) p a₁)
    (W : SubstWF Γ₀ σ σ' Γ ρ) : SubstWF Γ₀ (σ.cons x) (σ'.cons x') (A :: Γ) (ρ.push p.T) := by
  refine W.cons (fun hA => ?_) hA₁ hp.T HA.hasType.1 ⟨hx, hΓ₀, fun n a' ha' => ?_⟩
  · have ⟨_, _, le_a, hA', hSort, hmem'⟩ := (LE_Interp.sound HA W.fits).2 hA
    exact ⟨_, le_a, hA', (TShape.HasType.mono_r hSort.le_sort .sort hmem').toType⟩
  have ha' := LE_Interp.weak_iff.1 ha'
  refine ⟨fun ht => ⟨⟨_, HA.hasType.1.subst' W.wf₀ W.toSubstEq⟩, ?_⟩, fun m' hm' ht => ?_⟩
  · have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ := (LE_Interp.sound HA W.fits).2 ha' |>.out
    refine (TyEq.lift le_n ht).1 <| (LR _).mono_r_2_ty ((TShape.LE.lift_l le_n).1 le_a)
      (WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ht)
      (WShape.HasType.mono_r hSort.le_sort' .sort hmem').toType ?_
    exact (LR _).toType <| (LR _).mono_r_1 hSort.le_sort' hmem'
      (.mono_r hSort.le_sort' .sort hmem') .sort ((ihA hA' hSort hmem').1 W).1
  · have le_k := Nat.le_max_left k n; have le_n := Nat.le_max_right k n
    have ht' := (WShape.HasType.lift le_n).2 ht
    have hp' := (WShape.HasType.lift le_k).2 hp
    have hle' := (TShape.LE.def le_n le_k).1 (LE_Interp.bvar_iff.1 hm')
    have hta₁ := WShape.lift_type ▸ (WShape.HasType.lift le_k).2 hp.isType
    have hta' := WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ht.isType
    have hc := hA₁.compat ha'
    have hj := (TShape.Join.def le_k le_n (Nat.le_refl _)).1 (.mk hc)
    rw [TShape.lift_join le_k le_n] at hj
    have ⟨hj1, hj2⟩ := hj.le
    have hJ := hta₁.join' hj hta'
    have hJ' := hJ.mono_r hj1 hp'
    refine (TmEq.lift le_n ht).1 <|
      (LR _).mono_r_2 hj2 ht' hJ <|
      (LR _).mono_l hle' (hJ.mono_r hj2 ht') hJ' <|
      (LR _).mono_r_1 hj1 hp' hJ' ?_ <| (TmEq.lift le_k hp).2 hv
    have valTyA {nd : Nat} {a : WShape nd} (hA : LE_Interp ρ a.T A) (ha : a.HasType .type) :
        (LR _).TyEq (A.subst σ) (A.subst σ) a :=
      have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ := (LE_Interp.sound HA W.left.fits).2 hA |>.out
      have v2 := (ihA hA' hSort hmem').2 W.left
      have vt := (LR _).left_ty <| (LR _).toType <| (LR _).mono_r_1 hSort.le_sort' hmem'
        (.mono_r hSort.le_sort' .sort hmem') .sort v2
      (TyEq.lift le_n ha).1 <| (LR _).mono_r_2_ty ((TShape.LE.lift_l le_n).1 le_a)
        (WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ha)
        (WShape.HasType.mono_r hSort.le_sort' .sort hmem').toType vt
    refine (LR _).join_ty ((TShape.Compat.def le_k le_n).2 hc) hta₁ hta' ?_ ?_
    · exact (TyEq.lift le_k hp.isType).2 (valTyA hA₁ hp.isType)
    · exact (TyEq.lift le_n ht.isType).2 (valTyA ha' ht.isType)

/-- Extract `TyEq` from a `TmEq` at sort type. -/
theorem LR.toValTy {m : WShape n'} {b : WShape n} (le_n : n ≤ n') (le_a : b.T ≤ m.T)
    (ht : b.HasType .type) (hSort : LE_Interp ρ a.T (.sort u)) (hmem' : m.HasType a)
    (H : (LR hΓ₀).TmEq M N (.sort u) m a) : (LR hΓ₀).TyEq M N b := by
  have hle := hSort.le_sort'
  refine (LR.TyEq.lift le_n ht).1 ?_
  refine (LR _).mono_r_2_ty ((TShape.LE.lift_l le_n).1 le_a)
    (WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ht)
    (WShape.HasType.mono_r hle .sort hmem').toType ?_
  exact (LR _).toType <| (LR _).mono_r_1 hle hmem'
    (.mono_r hle .sort hmem') .sort H

theorem LR.Adequate.bot' {Γ₀ Γ : List Term} {ρ : Valuation} {M N A : Term}
    {n : Nat} {a : WShape n} {u : Bool}
    (HtypeA : Γ ⊢ A : .sort u) (hA : LE_Interp ρ a.T A) (ha : a.HasType .type)
    (IH : ∀ {ρ' : Valuation} {n' : Nat} {m' b : WShape n'},
        LE_Interp ρ' m'.T A → LE_Interp ρ' b.T (.sort u) → m'.HasType b →
        Adequate Γ₀ Γ ρ' A A (.sort u) m' b)
    : Adequate Γ₀ Γ ρ M N A .bot a := by
  refine .bot (fun _ W => ?_) ha
  have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ := (LE_Interp.sound HtypeA W.fits).2 hA |>.out
  exact LR.toValTy le_n le_a ha hSort hmem' ((IH hA' hSort hmem').2 W)

/-- Lower an `Adequate` from a witness `(m', a')` to a smaller one `(m, a)` — used to
consume the saturated invariant returned by `adequacy_Y`. `le : m.T ≤ m'.T` lowers the
term-witness; the two type-witnesses `a, a'` (both interpreting `A`, hence compatible)
are reconciled through their join. -/
theorem LR.Adequate.mono {Γ₀ Γ : List Term} {ρ : Valuation} {M N A : Term}
    {n n' : Nat} {m a : WShape n} {m' a' : WShape n'}
    (le : m.T ≤ m'.T) (hmem : m.HasType a) (hmem' : m'.HasType a')
    (hc : a.T.Compat a'.T)
    (hAty : ∀ {{σ σ'}} (W : LR.SubstWF Γ₀ σ σ' Γ ρ), (LR W.wf₀).TyEq (A.subst σ) (A.subst σ) a)
    (H : Adequate Γ₀ Γ ρ M N A m' a') : Adequate Γ₀ Γ ρ M N A m a := by
  -- Join the two type-witnesses (both interpret `A`, so compatible via `hc`); work at `k = max n n'`.
  have hJ := TShape.Join.mk hc
  have ⟨hJ1, hJ2⟩ := (hJ _).1 .rfl          -- a.T ≤ a.T⊔a'.T,  a'.T ≤ a.T⊔a'.T
  have hkn : n ≤ max n n' := Nat.le_max_left ..
  have hkn' : n' ≤ max n n' := Nat.le_max_right ..
  have hjk : (a.T.join a'.T).1 ≤ max n n' := Nat.max_le.2 ⟨hkn, hkn'⟩
  have hJ1' := (TShape.LE.def hkn hjk).1 hJ1
  have hJ2' := (TShape.LE.def hkn' hjk).1 hJ2
  have hJ_t := (TShape.HasType.sort_r.2 hmem.isType).join' hJ (TShape.HasType.sort_r.2 hmem'.isType)
  have hmem_k := (WShape.HasType.lift hkn).2 hmem
  have hmem'_k := (WShape.HasType.lift hkn').2 hmem'
  have hJ_t' := TShape.HasType.sort_r.1 <| hJ_t.mono_l (TShape.lift_eqv hjk).2 (TShape.lift_eqv hjk).1
  -- Per component: lift to `k`, `mono_r_1` (a'→join, needs `TyEq A A join` from `hAty` ⊔ base),
  -- `mono_l` (m'→m via `le`), `mono_r_2` (join→a), unlift. (appDF template, ~441–455.)
  have lower : ∀ {M0 N0 : Term} {{σ σ'}} (W : LR.SubstWF Γ₀ σ σ' Γ ρ),
      (LR W.wf₀).TmEq M0 N0 (A.subst σ) m' a' → (LR W.wf₀).TmEq M0 N0 (A.subst σ) m a := by
    intro M0 N0 σ σ' W hv
    have ha_kty : (WShape.lift (max n n') a).HasType .type := by
      simpa using (WShape.HasType.lift hkn).2 hmem.isType
    have ha'_kty : (WShape.lift (max n n') a').HasType .type := by
      simpa using (WShape.HasType.lift hkn').2 hmem'.isType
    have tyJ := (LR _).join_ty ((TShape.Compat.def hkn hkn').2 hc) ha_kty ha'_kty
      ((TyEq.lift hkn hmem.isType).2 (hAty W)) ((TyEq.lift hkn' hmem'.isType).2 ((LR W.wf₀).isType hv))
    have tyJ' : (LR W.wf₀).TyEq (A.subst σ) (A.subst σ) ((a.T.join a'.T).snd.lift (max n n')) :=
      WShape.lift_self ▸ tyJ
    refine (LR.TmEq.lift hkn hmem).1 <| (LR _).mono_r_2 hJ1' hmem_k hJ_t' <|
      (LR _).mono_l ((TShape.LE.def hkn hkn').1 le) (.mono_r hJ1' hJ_t' hmem_k)
        (.mono_r hJ2' hJ_t' hmem'_k) <|
      (LR _).mono_r_1 hJ2' hmem'_k (.mono_r hJ2' hJ_t' hmem'_k) tyJ' <|
        (LR.TmEq.lift hkn' hmem').2 hv
  exact ⟨fun σ σ' W => ⟨lower W (H.1 W).1, lower W (H.1 W).2⟩, fun σ W => lower W (H.2 W)⟩

/-- Dedicated recursion for the `YDF` (fixed-point congruence) case of
`LR.adequacy`. Separated out because the `.Y` witness `m.T` is not a variable,
so the finite `LE_Interp`-tower recursion cannot be run inline; here the witness
is generalised (`w`) so `induction hM` fires on the `bot`/`.Y` constructors.

The `bot` leaf (`w ≤ ⊥ ⇒ m = ⊥`) gives `Adequate.bot`. The `.Y` step
head-expands both sides one unfold to `b.inst (.Y A b) ≡ b'.inst (.Y A' b')`,
discharges it with the body IH `ihb`, and feeds the recursive self-adequacy of
`.Y A b ≡ .Y A' b'` from the structurally-smaller self-witness (`ih_self`).

The three `ih*` arguments are the `LR.adequacy` IHs for the `YDF` premises. -/
theorem LR.adequacy_Y (W : ρ.Fits Γ₀ Γ)
    (HA : Γ ⊢ A ≡ A' : .sort u) (Hb : A::Γ ⊢ b ≡ b' : A.lift)
    (Hb' : A'::Γ ⊢ b ≡ b' : A'.lift)
    (ihA : ∀ {ρ : Valuation} {n} {m a : WShape n},
      LE_Interp ρ m.T A → LE_Interp ρ a.T (.sort u) → m.HasType a →
      Adequate Γ₀ Γ ρ A A' (.sort u) m a)
    (ihb : ∀ {ρ : Valuation} {n} {m a : WShape n},
      LE_Interp ρ m.T b → LE_Interp ρ a.T A.lift → m.HasType a →
      Adequate Γ₀ (A::Γ) ρ b b' A.lift m a)
    (hM : LE_Interp ρ m (.Y A b)) :
    ∃ n m' a, m ≤ m'.T ∧ LE_Interp ρ m'.T (.Y A b) ∧ LE_Interp ρ a.T A ∧ m'.HasType (n := n) a ∧
      Adequate Γ₀ Γ ρ (.Y A b) (.Y A' b') A m' a := by
  generalize eq : Term.Y A b = M at hM
  induction hM with cases eq
  | bot => exact ⟨_, _, _, .rfl, .bot, .bot, .bot' (.bot' .sort),
    .bot' HA.hasType.1 .bot (.bot' .sort) fun h1 h2 h3 => (ihA h1 h2 h3).left⟩
  | Y hbody hself ihbody ihself
  rename_i m' ρ' s
  have ⟨n, s', a', a1, a2, a3, a4, a5⟩ := ihself W rfl
  have Wc := W.cons (InterpTyped.hsort (LE_Interp.sound HA W).2) a3 a4.T
  have ⟨m'', a'', b1, b2, b3, b4⟩ := (LE_Interp.sound Hb Wc).2
    (hbody.mono_l (Valuation.LE.push.2 ⟨.rfl, a1⟩))
  have hAdq := ihb (b2.lift (Nat.le_max_left ..)) (b3.lift (Nat.le_max_right ..)) b4
  refine ⟨_, _, _, b1.trans (TShape.lift_eqv (Nat.le_max_left ..)).2,
    .lift (Nat.le_max_left ..) (.Y b2 a2), (LE_Interp.weak_iff.1 b3).lift (Nat.le_max_right ..),
    b4, fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
  · -- (1) reflexive LHS: `A.Y b` across `σ`/`σ'`, discharged by `(hAdq.1 W_LL).1` with the
    -- reflexive self `(a5.1 W).1` threaded via `Adequate.cons`.
    have redY : ∀ {C c : Term} {τ : Subst}, (Term.Y C c).subst τ ⤳* c.subst (τ.cons ((Term.Y C c).subst τ)) :=
      fun {C c τ} => inst_lift_cons ▸ .tail .rfl .Y
    have hYYL := ((IsDefEq.YDF HA Hb Hb').hasType.1).subst' W.wf₀ W.toSubstEq
    have hAss : Γ₀ ⊢ A.subst σ ≡ A.subst σ' : .sort u := (HA.hasType.1).subst' W.wf₀ W.toSubstEq
    have unfoldL1 : Γ₀ ⊢ (Term.Y A b).subst σ ≡ b.subst (σ.cons ((Term.Y A b).subst σ)) : A.subst σ := by
      have h := (IsDefEq.Y_unfold₀ W.wf HA.hasType.1 Hb.hasType.1).subst' W.wf₀ W.left.toSubstEq
      rwa [subst_inst, inst_lift_cons] at h
    have unfoldL2 : Γ₀ ⊢ (Term.Y A b).subst σ' ≡ b.subst (σ'.cons ((Term.Y A b).subst σ')) : A.subst σ := by
      have h := (IsDefEq.Y_unfold₀ W.wf HA.hasType.1 Hb.hasType.1).subst' W.wf₀ W.symm.left.toSubstEq
      rw [subst_inst, inst_lift_cons] at h
      exact hAss.symm.defeqDF h
    refine ((LR _).whr ⟨unfoldL1, redY⟩ ⟨unfoldL2, redY⟩ hYYL).2 ?_
    have W_LL := LR.Adequate.cons ihA HA a4 a3 hYYL (a5.1 W).1 W
    exact (lift_subst_cons (e := A)) ▸ (hAdq.1 W_LL).1
  · -- (2) reflexive RHS: `A'.Y b'` across `σ`/`σ'`, via `hAdq`'s `b'` component + the reflexive
    -- self `(a5.1 W).2` threaded via `Adequate.cons` (head `A'.Y b'`).
    have redY : ∀ {C c : Term} {τ : Subst}, (Term.Y C c).subst τ ⤳* c.subst (τ.cons ((Term.Y C c).subst τ)) :=
      fun {C c τ} => inst_lift_cons ▸ .tail .rfl .Y
    have hYYR := ((IsDefEq.YDF HA Hb Hb').hasType.2).subst' W.wf₀ W.toSubstEq
    have hAss : Γ₀ ⊢ A.subst σ ≡ A.subst σ' : .sort u := (HA.hasType.1).subst' W.wf₀ W.toSubstEq
    have unfoldR1 : Γ₀ ⊢ (Term.Y A' b').subst σ ≡ b'.subst (σ.cons ((Term.Y A' b').subst σ)) : A.subst σ := by
      have h := (IsDefEq.Y_unfold₀ W.wf HA.hasType.2 Hb'.hasType.2).subst' W.wf₀ W.left.toSubstEq
      rw [subst_inst, inst_lift_cons] at h
      exact (HA.subst' W.wf₀ W.left.toSubstEq).symm.defeqDF h
    have unfoldR2 : Γ₀ ⊢ (Term.Y A' b').subst σ' ≡ b'.subst (σ'.cons ((Term.Y A' b').subst σ')) : A.subst σ := by
      have h := (IsDefEq.Y_unfold₀ W.wf HA.hasType.2 Hb'.hasType.2).subst' W.wf₀ W.symm.left.toSubstEq
      rw [subst_inst, inst_lift_cons] at h
      exact hAss.symm.defeqDF ((HA.subst' W.wf₀ W.symm.left.toSubstEq).symm.defeqDF h)
    refine ((LR _).whr ⟨unfoldR1, redY⟩ ⟨unfoldR2, redY⟩ hYYR).2 ?_
    have W_R' := LR.Adequate.cons ihA HA a4 a3 hYYR (a5.1 W).2 W
    exact (lift_subst_cons (e := A)) ▸ (hAdq.1 W_R').2
  · -- (3) diagonal: `whr`-expand both `.Y` sides, then transitivity through `b.σR`
    -- using `hAdq` (b ≡ b'), with the self-diagonal `a5.2 W` threaded via `Adequate.cons`.
    have redY : ∀ {C c : Term}, (Term.Y C c).subst σ ⤳* c.subst (σ.cons ((Term.Y C c).subst σ)) :=
      fun {C c} => inst_lift_cons ▸ .tail .rfl .Y
    have hYY := (IsDefEq.YDF HA Hb Hb').subst' W.wf₀ W.toSubstEq
    have unfoldL : Γ₀ ⊢ (Term.Y A b).subst σ ≡ b.subst (σ.cons ((Term.Y A b).subst σ)) : A.subst σ := by
      have h := (IsDefEq.Y_unfold₀ W.wf HA.hasType.1 Hb.hasType.1).subst' W.wf₀ W.toSubstEq
      rwa [subst_inst, inst_lift_cons] at h
    have unfoldR : Γ₀ ⊢ (Term.Y A' b').subst σ ≡ b'.subst (σ.cons ((Term.Y A' b').subst σ)) : A.subst σ := by
      have h := (IsDefEq.Y_unfold₀ W.wf HA.hasType.2 Hb'.hasType.2).subst' W.wf₀ W.toSubstEq
      rw [subst_inst, inst_lift_cons] at h
      exact (HA.subst' W.wf₀ W.toSubstEq).symm.defeqDF h
    refine ((LR _).whr ⟨unfoldL, redY⟩ ⟨unfoldR, redY⟩ hYY).2 ?_
    have W_LR := LR.Adequate.cons ihA HA a4 a3 hYY (a5.2 W) W
    have W_RR := LR.Adequate.cons ihA HA a4 a3 hYY.hasType.2 (a5.1 W).2 W
    refine (LR _).trans ?d1 ?d2
      ((lift_subst_cons (e := A)) ▸ (hAdq.1 W_LR).1) ((lift_subst_cons (e := A)) ▸ (hAdq.2 W_RR))
    · have := (Hb.hasType.1).subst' W.wf₀ (Ctx.SubstEq.cons
        (σ := σ.cons ((Term.Y A b).subst σ)) (σ' := σ.cons ((Term.Y A' b').subst σ))
        W.toSubstEq HA.hasType.1 hYY)
      rwa [lift_subst_cons] at this
    · have := Hb.subst' W.wf₀ (Ctx.SubstEq.cons
        (σ := σ.cons ((Term.Y A' b').subst σ)) (σ' := σ.cons ((Term.Y A' b').subst σ))
        W.toSubstEq HA.hasType.1 hYY.hasType.2)
      rwa [lift_subst_cons] at this

/-- **The fundamental theorem of the logical relation.** Given a derivation
`Γ ⊢ M ≡ N : A` and a semantic realisation `(m, a)` of `(M, A)`, the
defeq is mirrored on every substitution `LR.SubstWF`: both substituted
sides satisfy `TmEq` at shape `(m, a)`, and the diagonal case yields
`TmEq` between the two. Proof: induction on `H`, calling
`LE_Interp.sound` on each premise and applying the appropriate
`LogRel` closure property at each constructor. Corollaries are the
inversion lemmas at the bottom of this file. -/
theorem LR.adequacy (H : Γ ⊢ M ≡ N : A)
    (hM : LE_Interp ρ m.T M) (hA : LE_Interp ρ a.T A) (hmem : m.HasType a) :
    Adequate (n := n) Γ₀ Γ ρ M N A m a := by
  induction H generalizing ρ n m a with
  | @bvar Γ i A _ h h2 ih =>
    refine .refl fun σ _ W => ?_
    have hTyEq_AA : (LR W.wf₀).TyEq (A.subst σ) (A.subst σ) a := by
      have ⟨_, _, _, le, le', iA, iv, hmA⟩ := (LE_Interp.sound h2 W.left.fits).2 hA |>.out
      exact (LR _).left_ty <| toValTy le le' hmem.isType iv hmA ((ih iA iv hmA).2 W.left)
    revert hTyEq_AA; clear h2 ih
    have hle := LE_Interp.bvar_iff.1 hM; clear hM
    induction W generalizing i A with
    | id =>
      cases show m = .bot from TShape.le_bot.1 (hle.trans TShape.bot_le)
      exact (LR _).bot hmem.isType
    | cons W' _ _ _ _ h0 ih =>
      let ⟨a1, hΓ₀, a2⟩ := h0
      cases h with
      | zero => simpa only [lift_subst] using fun _ => (a2 a hA).2 (.bvar hle) hmem
      | succ h' => simpa only [lift_subst] using ih h' (LE_Interp.weak_iff.1 hA) hle
  | symm H ih =>
    exact .wf fun hΓ => .fits fun W => (ih ((LE_Interp.sound H W).1.2 hM) hA hmem).symm H
  | trans H1 H2 ih1 ih2 =>
    exact .wf fun hΓ => .fits fun W =>
      (ih1 hM hA hmem).trans H1 H2 (ih2 ((LE_Interp.sound H1 W).1.1 hM) hA hmem)
  | @trans' _ A B u C v H1 H2 ih1 ih2 =>
    by_cases hm : m ≤ .bot
    · refine WShape.le_bot.1 hm ▸ .bot (fun _ _ => ?_) hmem.isType
      exact (LR _).mono_r_2_ty hA.le_sort' hmem.isType .sort .sort
    refine .wf fun hΓ => .fits fun W => ?_
    refine (ih1 hM hA hmem).trans' H1 H2 (v := v) (r := v) ?_
    refine have ihs1 := LE_Interp.sound H1 W; have hM₂ := ihs1.1.1 hM; ?_
    have ihs2 := LE_Interp.sound H2 W (m := m.T)
    have ⟨a₂, s₂, b1, b2, b3, b4⟩ := ihs2.2 hM₂
    replace b4 := TShape.HasType.sort.mono_r b3.le_sort b4
    have := TShape.HasType.mono_r hA.le_sort .sort hmem.T
    refine ih2 (ihs1.1.1 hM) (.sort TShape.sort_eqv.1) ?_
    exact WShape.HasType.T_iff.1 <| .mono_r TShape.sort_eqv.2 .sort_T <| this.retype b4 b1
  | @sort _ l =>
    refine .wf₀ fun hΓ₀ => ?_
    suffices (LR hΓ₀).TmEq (.sort l) (.sort l) (.sort true) m a from
      ⟨fun _ _ _ => ⟨this, this⟩, fun _ _ => this⟩
    cases hmem.unfold with
    | bot hm =>
      apply (LR _).bot hm
      obtain rfl | rfl := (WShape.le_sort (s := a)).1 <|
        (TShape.LE.lift_r (Nat.zero_le _)).1 hA.le_sort
      · exact (LR _).bot_ty
      · exact .sort
    | sort => exact (LR _).sort_iff.2 ⟨_, ⟨.sort, .rfl⟩, _, ⟨.sort, .rfl⟩, ⟨.sort, .rfl⟩⟩
    | _ =>
      obtain h | h := WShape.le_sort.1 hM.le_sort'
      · dsimp only at h; rw [h]
        exact (LR _).bot hmem.isType <|
          (LR _).mono_r_2_ty hA.le_sort' hmem.isType .sort .sort
      · simp [WShape.ext_iff, WShape.forallE, WShape.sort, Shape.sort,
          WShape.lam', WShape.lam, WShape.bot, Shape.bot, WShape.sigma, WShape.pair] at h <;>
        first | split at h <;> simp_all only [reduceCtorEq] | simp_all
  | @appDF Γ A u B v F F' X X' _ _ Hf Ha HBa _ _ ihf iha ihBa =>
    cases hM with
    | bot => exact .bot' HBa.hasType.1 hA hmem.isType fun h h' hm => (ihBa h h' hm).left
    | @app _ nf_app f _ _ _ x hif hia le_m
    refine .wf₀ fun hΓ₀ => ?_
    suffices ∀ {F F' X X' σ σ'}, SubstWF Γ₀ σ σ' Γ ρ →
        Γ ⊢ F ≡ F' : A.forallE B → Γ ⊢ X ≡ X' : A → Γ ⊢ B.inst X ≡ B.inst X' : .sort v →
        LE_Interp ρ f.T F → LE_Interp ρ x.T X → LE_Interp ρ a.T (B.inst X) →
        (∀ {n'} {mf af : WShape n'}, LE_Interp ρ mf.T F → LE_Interp ρ af.T (.forallE A B) →
          mf.HasType af → Adequate Γ₀ Γ ρ F F' (.forallE A B) mf af) →
        (∀ {n'} {ma aa : WShape n'}, LE_Interp ρ ma.T X → LE_Interp ρ aa.T A →
          ma.HasType aa → Adequate Γ₀ Γ ρ X X' A ma aa) →
        (∀ {n'} {mb av : WShape n'}, LE_Interp ρ mb.T (B.inst X) → LE_Interp ρ av.T (.sort v) →
          mb.HasType av → Adequate Γ₀ Γ ρ (B.inst X) (B.inst X') (.sort v) mb av) →
        (LR hΓ₀).TmEq (.subst (.app F X) σ) (.subst (.app F' X') σ') (.subst (B.inst X) σ) m a by
      refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
      · refine this W Hf.hasType.1 Ha.hasType.1 HBa.hasType.1 hif hia hA ?_ ?_ ?_
        · exact fun hf hPi hmf => (ihf hf hPi hmf).left
        · exact fun ha hA hma => (iha ha hA hma).left
        · exact fun hB hv hmb => (ihBa hB hv hmb).left
      · refine (LR _).conv ((LR _).symm_ty ?_) <| this W
          Hf.hasType.2 Ha.hasType.2 HBa.hasType.2
          ((LE_Interp.sound Hf W.fits).1.1 hif)
          ((LE_Interp.sound Ha W.fits).1.1 hia)
          ((LE_Interp.sound HBa W.fits).1.1 hA)
          (fun hf hPi hmf => ?_) (fun ha hA hma => ?_) (fun hB hv hmb => ?_)
        · have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
            (LE_Interp.sound HBa W.fits).2 hA |>.out
          exact toValTy le le' hmem.isType iv hmb ((ihBa iB iv hmb).2 W.left)
        · exact ((ihf ((LE_Interp.sound Hf W.left.fits).1.2 hf) hPi hmf).symm Hf).left
        · exact ((iha ((LE_Interp.sound Ha W.left.fits).1.2 ha) hA hma).symm Ha).left
        · exact ((ihBa ((LE_Interp.sound HBa W.left.fits).1.2 hB) hv hmb).symm HBa).left
      · exact this W Hf Ha HBa hif hia hA ihf iha ihBa
    intro F F' X X' σ σ' W hF hX hBa hif hia hA ihf iha ihBa
    have ⟨_, mf, _, le_nf, le_mf, hf', hPi, hmf⟩ :=
      (LE_Interp.sound hF W.left.fits).2 hif |>.out
    have Af := ihf hf' hPi hmf
    by_cases hm0 : mf = .bot
    · simp only [hm0] at le_mf hmf
      refine (?_ : m = .bot) ▸ (LR _).bot hmem.isType ?_
      · cases show f = .bot from TShape.le_bot.1 (le_mf.trans TShape.bot_le')
        exact TShape.le_bot.1 ((WShape.bot_app ▸ le_m).trans TShape.bot_eqv.1)
      · have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
          (LE_Interp.sound hBa W.left.fits).2 hA |>.out
        exact (LR _).left_ty <| toValTy le le' hmem.isType iv hmb
          ((ihBa iB iv hmb).2 W.left)
    cases hPi with | bot => cases hm0 hmf.bot_r | forallE haA hbA hd hiB le
    cases hmf.unfold with
    | bot => cases hm0 rfl
    | lam hg => ?_
    | sort | forallE | sigma => exact (TShape.sort_not_le_forallE le).elim
    | pair => exact (TShape.sigma_not_le_forallE le).elim
    rename_i n₁ b₁' b₂' f' n₂ b₁ b₂ f
    simp at le_nf
    let k := max n (max n₁ n₂); have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
    have le_nf_k : nf_app ≤ k := Nat.le_trans le_nf hk.2.2
    have hA' := hA.lift hk.1
    have ⟨_, le_x', hx'_a₁, hgx2⟩ := WShape.HasDom.iff.1 hg.2.1 (x.lift _)
    have hia' := (hia.lift le_nf).mono le_x'.T
    have hax' := LE_Interp.forallE' haA hbA hd hiB |>.mono le |>.forallE_inv.2 hia'
    have hJ := TShape.Join.mk (hA.compat hax')
    have ⟨hJ1, hJ2⟩ := (hJ _).1 .rfl
    have hk' := Nat.max_le.2 ⟨hk.1, hk.2.2⟩
    have hJ1' := (TShape.LE.def hk.1 hk').1 hJ1
    have hJ2' := (TShape.LE.def hk.2.2 hk').1 hJ2
    have hgx' := (WShape.HasTypeLam.iff.1 hg).2.2 _ hx'_a₁
    have hJ_t := TShape.HasType.sort_r.2 hmem.isType
      |>.join' hJ <| TShape.HasType.sort_r.2 hgx'.isType
    have hmem_k := (WShape.HasType.lift hk.1).2 hmem
    rw [subst_inst]
    have hJ_t' := TShape.HasType.sort_r.1 <|
      hJ_t.mono_l (TShape.lift_eqv hk').2 (TShape.lift_eqv hk').1
    refine (LR.TmEq.lift hk.1 hmem).1 <| (LR _).mono_r_2 hJ1' hmem_k hJ_t' ?_
    have hgx'' := (WShape.HasType.lift hk.2.2).2 hgx'
    refine (LR _).mono_l ?_ (.mono_r hJ1' hJ_t' hmem_k) (.mono_r hJ2' hJ_t' hgx'') ?_
    · exact (TShape.LE.def hk.1 hk.2.2).1 <| le_m.trans <|
        (TShape.app_mono le_mf (TShape.lift_eqv le_nf).2).trans (WShape.lam'_app ▸ hgx2.T)
    refine (LR _).mono_r_1 hJ2' hgx'' (.mono_r hJ2' hJ_t' hgx'') ?_ ?_
    · have ⟨_, _, _, le_j, le_j', hBj, hSj, hmj⟩ :=
        (LE_Interp.sound hBa W.left.fits).2 (hA.join hJ hax') |>.out
      exact (LR _).left_ty <| (TyEq.lift hk' (TShape.HasType.sort_r.1 hJ_t)).2 <|
        subst_inst ▸ toValTy le_j le_j' (TShape.HasType.sort_r.1 hJ_t) hSj hmj
          ((ihBa hBj hSj hmj).2 W.left)
    · have hAf := (LR _).trans
        (hF.subst' W.wf₀ W.left.toSubstEq)
        (hF.hasType.2.subst' W.wf₀ W.toSubstEq)
        (Af.2 W.left) (Af.1 W).2
      dsimp only [LR, LRS] at hAf
      unfold WShape.lam' at hAf; split at hAf
      · rw [LRS.TmEq.lam_forallE] at hAf
        obtain ⟨_, _, _, _, red, htA₁_loc, _, htA₂_loc, _, valPi⟩ := hAf
        cases WHNF.forallE.whRedS red.2
        have le' := (TShape.LE.def (Nat.succ_le_succ hk.2.2) (Nat.succ_le_succ hk.2.1)).1 le
        simp only [WShape.T, WShape.lift_forallE hk.2.2, WShape.lift_forallE hk.2.1,
          WShape.forallE_le_forallE] at le'
        have Aa := iha hia' (haA.mono ((TShape.LE.def hk.2.2 hk.2.1).2 le'.1)) hx'_a₁
        have hX0 := hX.subst' W.wf₀ W.left.toSubstEq
        have hX' := hX.hasType.2.subst' W.wf₀ W.toSubstEq
        have := (LR _).trans hX0 hX' (Aa.2 W.left) (Aa.1 W).2
        have hF1 := hF.subst' W.wf₀ W.toSubstEq
        have hX1 := hX.subst' W.wf₀ W.toSubstEq
        refine (TmEq.lift hk.2.2 hgx').2 <| (LR _).trans
          (.appDF₀ W.wf₀ hF1 hX0.hasType.1) (.appDF₀ W.wf₀ hF1.hasType.2 hX1)
          (valPi.2 hx'_a₁ hX1.hasType.1 <| (LR _).left this)
          (valPi.1 hx'_a₁ hX1 this).2
      · refine (hm0 ?_).elim; unfold WShape.lam'; simp_all
  | @lamDF Γ A A' u B v body body' HA HB HBody HBody' HForallETy ihA ihB ihBody ihBody' ihAB =>
    refine .wf₀ fun hΓ₀ => ?_
    suffices ∀ {X Y X' Y' σ σ'},
        Γ ⊢ A ≡ X : .sort u → X::Γ ⊢ Y : B →
        Γ ⊢ A ≡ X' : .sort u → X'::Γ ⊢ Y' : B →
        X::Γ ⊢ Y ≡ Y' : B →
        LE_Interp ρ m.T (.lam X Y) → SubstWF Γ₀ σ σ' Γ ρ →
        (∀ {k np} {p : WShape np} {mb ab : WShape k},
          (ρ.push p.T).Fits Γ₀ (A :: Γ) →
          LE_Interp (ρ.push p.T) mb.T Y → LE_Interp (ρ.push p.T) ab.T B → mb.HasType ab →
          Adequate Γ₀ (A :: Γ) (ρ.push p.T) Y Y' B mb ab) →
        (LR hΓ₀).TmEq (.subst (.lam X Y) σ) (.subst (.lam X' Y') σ')
          (.subst (.forallE A B) σ) m a by
      refine ⟨fun σ σ' W => ⟨?_, ?_⟩,
        fun σ W => this HA.hasType.1 HBody.hasType.1 HA HBody'.hasType.2 HBody hM W
          fun _ => ihBody⟩
      · exact this HA.hasType.1 HBody.hasType.1 HA.hasType.1 HBody.hasType.1 HBody.hasType.1 hM W
          fun _ hMb hBb hmb => (ihBody hMb hBb hmb).left
      · refine this HA HBody'.hasType.2 HA HBody'.hasType.2 HBody'.hasType.2 ?_ W
          fun W' hMb' hBb hmb => ?_
        · exact (LE_Interp.sound (.lamDF₀ W.wf HA HBody) W.fits).1.1 hM
        · exact ((ihBody ((LE_Interp.sound HBody W').1.2 hMb') hBb hmb).symm HBody).left
    intro X Y X' Y' σ σ' hAX hY hAX' hY' hYY' hTerm W IH
    suffices ∀ n' b (f : WShapeFun _), n = n' + 1 → a ≍ (.forallE b f : WShape (n'+1)) →
        (LR hΓ₀).TmEq (.subst (.lam X Y) σ) (.subst (.lam X' Y') σ')
          (.subst (.forallE A B) σ) m a by
      cases hmem.unfold with
      | bot hm =>
        cases hm.unfold with
        | bot => cases n <;> trivial
        | sort =>
          cases n <;> let .forallE _ _ _ _ le := hA <;> exact (TShape.sort_not_le_forallE le).elim
        | forallE => exact this _ _ _ rfl .rfl
        | sigma => let .forallE _ _ _ _ le := hA; exact (TShape.sigma_not_le_forallE le).elim
      | sort => cases n <;> let .lam _ _ _ h := hTerm <;> cases TShape.sort_not_le_lam' h
      | forallE => let .lam _ _ _ h := hTerm <;> cases TShape.forallE_not_le_lam' h
      | lam => exact this _ _ _ rfl .rfl
      | sigma => let .lam _ _ _ h := hTerm <;> cases TShape.sigma_not_le_lam' h
      | pair => let .lam _ _ _ h := hTerm <;> cases TShape.pair_not_le_lam' h
    rintro k a₁ a₂ rfl ⟨⟩
    have ⟨_, aty, _⟩ := WShape.HasType.forallE_l.1 hmem.isType
    have hTypA : Γ₀ ⊢ A.subst σ : .sort u :=
      HA.hasType.1.subst' W.left.wf₀ W.left.toSubstEq
    have hΓS : ⊢ A.subst σ :: Γ₀ :=
      ⟨W.left.wf₀, _, hTypA⟩
    have hΓAS : ⊢ A.subst σ :: Γ₀ := ⟨W.wf₀, _, hTypA⟩
    have hΓA : ⊢ A :: Γ := ⟨W.wf, _, HA.hasType.1⟩
    have hTypB : A.subst σ :: Γ₀ ⊢ B.subst σ.lift : .sort v :=
      HB.subst hΓAS (W.left.toSubstEq.lift HA.hasType.1 hTypA)
    have hA1 := hA.forallE_inv.1
    have ⟨_, a', _, le_n, le_a, hA', hSort, hmem'⟩ :=
      (LE_Interp.sound HA W.left.fits).2 hA1 |>.out
    have cons := Adequate.cons (hΓ₀ := hΓ₀) ihA HA
    obtain ⟨g, hg, htm⟩ := WShape.HasType.forallE_inv hmem
    unfold WShape.lam' at hg; split at hg <;> subst hg <;>
      [rename_i hlam; exact (LR.Adequate.bot' (M := .lam X Y) (N := .lam X' Y')
        HForallETy hA hmem.isType ihAB |>.1 W).1]
    have aty := WShape.HasTypePi.iff.1 aty
    refine ⟨A.subst σ, B.subst σ.lift, u, v, .rfl ?_, hTypA, ?_, hTypB, ?_, ?_⟩
    · exact .forallEDF₀ W.wf₀ hTypA hTypB
    · exact (LR hΓ₀).left_ty <| toValTy le_n le_a aty.1.isType hSort hmem'
        ((ihA hA' hSort hmem').2 W.left)
    · simp [LRS.PiDefEq, inst_lift_cons]
      refine have := ?_; ⟨this, fun _ _ hp ha hv => this hp ha hv⟩
      intro x x' p hp ha hv
      have W' := cons hp hA1 ha hv W.left
      have ⟨n', ab, _, le, le', iB, iv, hmb⟩ :=
        (LE_Interp.sound HB W'.fits).2 (hA.forallE_inv'.2 p) |>.out
      exact toValTy le le' (aty.2 _ hp).toType iv hmb ((ihB iB iv hmb).1 W').1
    have beta {X Y t : Term} {σ} : .app (.lam (X.subst σ) (Y.subst σ.lift)) t ⤳*
        Y.subst (σ.cons t) := inst_lift_cons (x := t) ▸ .tail .rfl .beta
    have main {Xl Yl xl Xr Yr xr σl σr n} {m a : WShape n} (W : SubstWF Γ₀ σl σr Γ ρ)
        (hB : Xl :: Γ ⊢ B : .sort v) (hX : Γ ⊢ Xl ≡ Xr : .sort u) (hY : Xl::Γ ⊢ Yl ≡ Yr : B)
        (hx : Γ₀ ⊢ xl ≡ xr : Xl.subst σl) :
        (LR hΓ₀).TmEq (Yl.subst (σl.cons xl)) (Yr.subst (σr.cons xr)) (B.subst (σl.cons xl)) m a →
        (LR hΓ₀).TmEq (((Xl.lam Yl).subst σl).app xl)
            (((Xr.lam Yr).subst σr).app xr) (B.subst (σl.cons xl)) m a := by
      have hXσ := hX.subst' hΓ₀ W.toSubstEq
      have hΓX : ⊢ _ :: _ := ⟨hΓ₀, _, hXσ.hasType.1⟩
      have W' := W.toSubstEq.lift hX.hasType.1 hXσ.hasType.1
      have hYσ := hY.subst' hΓX W'; have hBσ := hB.subst' hΓX W'
      refine ((LR _).whr ⟨?_, beta⟩ ⟨?_, beta⟩ ?_).2
      · have h := hYσ.hasType.1.beta₀ hΓ₀ hx.hasType.1
        rwa [inst_lift_cons, inst_lift_cons] at h
      · have h := hXσ.defeqDF_l hΓ₀ (hBσ.defeqDF hYσ.hasType.2)
          |>.beta₀ hΓ₀ (hXσ.defeqDF hx.hasType.2)
        rw [inst_lift_cons, inst_lift_cons] at h
        exact (hB.subst' hΓ₀ (by exact W.toSubstEq.cons hX.hasType.1 hx)).symm.defeqDF h
      · have h := (hXσ.lamDF₀ hΓ₀ hYσ).appDF₀ hΓ₀ hx; rwa [inst_lift_cons] at h
    refine ⟨fun x x' p hp ha hv => ?_, fun x p hp ha hv => ?_⟩
    all_goals
      rw [inst_lift_cons]
      have hBb_sd := hA.forallE_inv'.2 p
      replace IH W := IH W (hTerm.lam_inv' p) hBb_sd ((WShape.HasTypeLam.iff.1 htm).2.2 p hp)
    · have W' := cons hp hA1 ha hv W.left
      have hx : Γ₀ ⊢ x ≡ x' : X.subst σ := (hAX.subst' W.wf₀ W.left.toSubstEq).defeqDF ha
      constructor
      · exact main W.left (hAX.defeqDF_l W.wf HB) hAX.hasType.2 hY hx ((IH W'.fits).1 W').1
      · have vtAA' := toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).1
        have ha' := (HA.hasType.1.subst' W.wf₀ W.toSubstEq).defeqDF ha
        have hv' := (LR _).conv vtAA' hv
        have ⟨n', _, _, le, le', iB, iv, hmb⟩ := (LE_Interp.sound HB W'.fits).2 hBb_sd |>.out
        have W2 := cons hp hA1 ha.hasType.1 ((LR _).left hv) W
        have vtBB := toValTy le le' (aty.2 _ hp).toType iv hmb ((ihB iB iv hmb).1 W2).1
        refine (LR _).conv ((LR _).symm_ty vtBB) ?_
        exact main W.symm.left (hAX'.defeqDF_l W.wf HB) hAX'.hasType.2 hY'
          ((hAX'.subst' W.wf₀ W.toSubstEq).defeqDF ha)
          ((IH W'.fits).1 (cons hp hA1 ha' hv' W.symm.left)).2
    · have W' := cons hp hA1 ha hv W
      have hx : Γ₀ ⊢ x : X.subst σ := (hAX.subst' W.wf₀ W.left.toSubstEq).defeqDF ha
      refine main W (hAX.defeqDF_l W.wf HB) (hAX.symm.trans hAX') hYY' hx ?_
      refine (LR _).trans ?_ ?_ ((IH W'.fits).2 W'.left) ((IH W'.fits).1 W').2
      · exact hYY'.subst' hΓ₀ (W.left.toSubstEq.cons hAX.hasType.2 hx)
      · refine hY'.subst' hΓ₀ (.cons W.toSubstEq hAX'.hasType.2 ?_)
        exact (hAX'.subst' W.wf₀ W.left.toSubstEq).defeqDF ha
  | @forallEDF Γ A A' u body body' v HA HBody HBody' ihA ihBody =>
    cases hmem.unfold with
    | bot hm =>
      refine .bot (fun _ _ => ?_) hm
      obtain rfl | rfl := (WShape.le_sort (s := a)).1 <|
        (TShape.LE.lift_r (Nat.zero_le _)).1 hA.le_sort
      · exact (LR _).bot_ty
      · exact .sort
    | sort => cases n <;> have .forallE _ _ _ _ h := hM <;> cases TShape.sort_not_le_forallE h
    | @lam _ f₀ =>
      revert hM; unfold WShape.lam'
      split <;> [skip; exact fun _ => .bot
        (fun _ _ => (LR _).mono_r_2_ty hA.le_sort' hmem.isType .sort .sort)
        hmem.isType]
      intro | .forallE _ _ _ _ h => cases TShape.lam_not_le_forallE h
    | sigma => have .forallE _ _ _ _ h := hM; cases TShape.sigma_not_le_forallE h
    | pair => have .forallE _ _ _ _ h := hM; cases TShape.pair_not_le_forallE h
    | @forallE k a₂ a₁ r aty
    refine .wf₀ fun hΓ₀ => ?_
    have aty := WShape.HasTypePi.iff.1 aty
    have hA1 := hM.forallE_inv.1
    have cons := Adequate.cons (hΓ₀ := hΓ₀) ihA HA
    refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩ <;> (
      have ⟨_, a', _, le_n, le_a, hA', hSort, hmem'⟩ :=
        (LE_Interp.sound HA W.left.fits).2 hA1 |>.out
      have HAAσ := HA.subst' W.left.wf₀ W.left.toSubstEq
      have S' := W.toSubstEq.lift HA.hasType.1 HAAσ.hasType.1
      have hΓS : ⊢ A.subst σ :: Γ₀ := ⟨W.wf₀, _, HAAσ.hasType.1⟩
      have hΓA : ⊢ A :: Γ := ⟨W.wf, _, HA.hasType.1⟩)
    · have HAσ := HA.hasType.1.subst' W.wf₀ W.toSubstEq
      have HA'σ := HA.hasType.2.subst' W.wf₀ W.toSubstEq
      constructor
      · refine ⟨v, ⟨.sort, .rfl⟩, A.subst σ, body.subst σ.lift, A.subst σ', body.subst σ'.lift,
           u, v, ⟨?_, .rfl⟩, ⟨?_, .rfl⟩, HAσ, HBody.hasType.1.subst' hΓS S', ?_, ?_⟩
        · refine .forallEDF₀ hΓ₀ HAσ.hasType.1 (HBody.hasType.1.subst hΓS ?_)
          · exact W.left.toSubstEq.lift HA.hasType.1 HAσ.hasType.1
        · refine .forallEDF₀ hΓ₀ HAσ.hasType.2 (HBody.hasType.1.subst ?_ ?_)
          · exact ⟨W.wf₀, _, HAσ.hasType.2⟩
          · exact W.symm.left.toSubstEq.lift HA.hasType.1 HAσ.hasType.2
        · exact toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).1
        simp [LRS.PiDefEq, inst_lift_cons]
        refine ⟨fun _ _ p hp ha hv => ?_, fun _ p hp ha hv => ?_⟩ <;>
          have hB := hM.forallE_inv'.2 p <;> [constructor <;> [
            have W' := cons hp hA1 ha hv W.left;
            ( have := toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).1
              have W' := cons hp hA1 (HAσ.defeqDF ha) ((LR _).conv this hv) W.symm.left )];
            have W' := cons hp hA1 ha.hasType.1 ((LR _).left hv) W] <;>
        · have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
            (LE_Interp.sound HBody W'.fits).2 hB |>.out
          exact toValTy le le' (aty.2 _ hp).toType iv hmb ((ihBody iB iv hmb).1 W').1
      · have hΓA' : ⊢ A' :: Γ := ⟨W.wf, _, HA.hasType.2⟩
        refine ⟨v, ⟨.sort, .rfl⟩, A'.subst σ, body'.subst σ.lift, A'.subst σ', body'.subst σ'.lift,
          u, v, ⟨?_, .rfl⟩, ⟨?_, .rfl⟩, HA'σ,
          HAAσ.defeqDF_l hΓ₀ (HBody.hasType.2.subst' hΓS S'), ?_, ?_⟩
        · refine .forallEDF₀ hΓ₀ HA'σ.hasType.1 (HBody'.hasType.2.subst ?_ ?_)
          · exact ⟨W.wf₀, _, HA'σ.hasType.1⟩
          · exact W.left.toSubstEq.lift HA.hasType.2 HA'σ.hasType.1
        · refine .forallEDF₀ hΓ₀ HA'σ.hasType.2 (HBody'.hasType.2.subst ?_ ?_)
          · exact ⟨W.wf₀, _, HA'σ.hasType.2⟩
          · exact W.symm.left.toSubstEq.lift HA.hasType.2 HA'σ.hasType.2
        · exact toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).2
        simp [LRS.PiDefEq, inst_lift_cons]
        have := toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').2 W.left)
        refine ⟨fun _ _ p hp ha hv => ?_, fun _ p hp ha hv => ?_⟩ <;> (
          have hv := (LR _).conv ((LR _).symm_ty this) hv
          have ha := HAAσ.symm.defeqDF ha
          have hB := hM.forallE_inv'.2 p) <;> [constructor <;> [
            have W' := cons hp hA1 ha hv W.left;
            ( have := toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).1
              have W' := cons hp hA1 (HAσ.defeqDF ha) ((LR _).conv this hv) W.symm.left )];
            have W' := cons hp hA1 ha ((LR _).left hv) W] <;>
        · have ⟨_, _, _, le, le', iB, iv, hmb⟩ := (LE_Interp.sound HBody W'.fits).2 hB |>.out
          exact toValTy le le' (aty.2 _ hp).toType iv hmb ((ihBody iB iv hmb).1 W').2
    · refine ⟨v, ⟨.sort, .rfl⟩, A.subst σ, body.subst σ.lift, A'.subst σ, body'.subst σ.lift, u, v,
        ⟨?_, .rfl⟩, ⟨?_, .rfl⟩, HAAσ, HBody.subst' hΓS S', ?_, ?_⟩
      · exact .forallEDF₀ hΓ₀ HAAσ.hasType.1 (HBody.hasType.1.subst hΓS S')
      · refine .forallEDF₀ hΓ₀ HAAσ.hasType.2 (HBody'.hasType.2.subst ?_ ?_)
        · exact ⟨W.wf₀, _, HAAσ.hasType.2⟩
        · exact W.toSubstEq.lift HA.hasType.2 HAAσ.hasType.2
      · exact toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').2 W)
      simp [LRS.PiDefEq, inst_lift_cons]
      refine ⟨fun _ _ p hp ha hv => ?_, fun _ p hp ha hv => ?_⟩ <;> (
        have hB := hM.forallE_inv'.2 p
        have W' := cons hp hA1 ha hv W
        have ⟨_, _, _, le, le', iB, iv, hmb⟩ := (LE_Interp.sound HBody W'.fits).2 hB |>.out)
      · exact ⟨toValTy le le' (aty.2 _ hp).toType iv hmb ((ihBody iB iv hmb).1 W').1,
               toValTy le le' (aty.2 _ hp).toType iv hmb ((ihBody iB iv hmb).1 W').2⟩
      · exact toValTy le le' (aty.2 _ hp).toType iv hmb ((ihBody iB iv hmb).2 W')
  | @defeqDF Γ A' B' u' _ _ Hty He ihTy ihE =>
    have tyConv {σ} (W : SubstWF Γ₀ σ σ Γ ρ) :=
      have hA' := (LE_Interp.sound Hty W.fits).1.2 hA
      have ⟨_, a', _, le_n, le_a, hA'', hSort, hmem'⟩ :=
        (LE_Interp.sound Hty W.fits).2 hA' |>.out
      toValTy le_n le_a hmem.isType hSort hmem' ((ihTy hA'' hSort hmem').2 W)
    refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩ <;>
      have hA' := (LE_Interp.sound Hty W.left.fits).1.2 hA
    · exact ⟨(LR _).conv (tyConv W.left) ((ihE hM hA' hmem).1 W).1,
             (LR _).conv (tyConv W.left) ((ihE hM hA' hmem).1 W).2⟩
    · exact (LR _).conv (tyConv W) ((ihE hM hA' hmem).2 W)
  | beta HA He Ha Happ Hinst _ _ _ ihapp ihinst =>
    refine ⟨fun _ _ W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · exact ((ihapp hM hA hmem).1 W).1
    · refine ((ihinst ?_ hA hmem).1 W).2
      exact (LE_Interp.sound (.beta₀ W.wf He Ha) W.fits).1.1 hM
    · have H := Happ.subst' W.wf₀ W.toSubstEq
      refine ((LR _).whr ⟨H, .rfl⟩ ⟨?_, subst_inst ▸ .tail .rfl .beta⟩ H).1 ((ihapp hM hA hmem).2 W)
      exact (IsDefEq.beta HA He Ha Happ Hinst).subst' W.wf₀ W.toSubstEq
  | @eta _ e0 A0 B0 He Hlam ihe ihlam =>
    refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · exact ((ihlam hM hA hmem).1 W).1
    · exact ((ihe ((LE_Interp.sound (.eta₀ W.wf He) W.fits).1.1 hM) hA hmem).1 W).2
    have hM' := (LE_Interp.sound (.eta₀ W.wf He) W.fits).1.1 hM
    cases hmem.unfold with
    | bot hm => exact (LR _).bot hm <| (LR _).isType ((ihlam hM hA hmem).2 W)
    | sort => cases n <;> let .lam _ _ _ h := hM <;> cases TShape.sort_not_le_lam' h
    | forallE => let .lam _ _ _ h := hM; cases TShape.forallE_not_le_lam' h
    | sigma => let .lam _ _ _ h := hM <;> cases TShape.sigma_not_le_lam' h
    | pair => let .lam _ _ _ h := hM <;> cases TShape.pair_not_le_lam' h
    | lam htm
    revert hM hM' hmem; unfold WShape.lam'
    split <;> intro hM hM' hmem <;>
      [skip; exact (LR _).bot hmem.isType ((LR _).isType ((ihlam hM hA hmem).2 W))]
    have ⟨A₁, A₂, u, v, whr_t, htA₁, vtyA₁, htA₂, edge, vpi_M⟩ := (ihlam hM hA hmem).2 W
    have ⟨_, _, _, _, whr_N, _, _, _, _, vpi_N⟩ := (ihe hM' hA hmem).2 W
    cases whr_t.2.determ .forallE whr_N.2 .forallE
    cases WHNF.forallE.whRedS whr_t.2
    refine ⟨_, _, u, v, whr_t, htA₁, vtyA₁, htA₂, edge, ?_, fun a p hp ha hv => ?_⟩
    · exact fun a b p hp ha hv => ⟨(vpi_M.1 hp ha hv).1, (vpi_N.1 hp ha hv).2⟩
    have H := ((IsDefEq.eta He Hlam).subst' W.wf₀ W.toSubstEq).appDF₀ W.wf₀ ha
    refine ((LR _).whr ⟨H, ?_⟩ ⟨H.hasType.2, .rfl⟩ H).2 (vpi_N.2 hp ha hv)
    rw [(?_ : (e0.subst σ).app a = _)]; · exact .tail .rfl .beta
    rw [inst_lift_cons, Term.subst, lift_subst_cons]; rfl
  | proofIrrel Hp _ _ ihp =>
    refine .wf fun hΓ => .fits fun W => ?_
    have ⟨_, _, s, le_n, le_a, _, hSort, hmem'⟩ := (LE_Interp.sound Hp W).2 hA |>.out
    have hS := WShape.HasType.mono_r hSort.le_sort' .sort hmem'; simp at hS
    have ha' := hS.mono_r ((TShape.LE.lift_l le_n).1 le_a) ((WShape.HasType.lift le_n).2 hmem)
    cases (WShape.lift_eq_bot le_n).1 (hS.proofIrrel ha')
    exact .bot' Hp hA hmem.isType ihp
  | @sigmaDF Γ A A' u B B' v HA HB HB' ihA ihB =>
    cases hmem.unfold with
    | bot hm =>
      cases hm.unfold with
      | bot _ => exact .bot (fun _ _ => (LR _).bot_ty) hm
      | sort => exact .bot (fun _ _ => LogRelBase.TyEq.sort) hm
      | forallE | sigma => let .sort h := hA; cases (TShape.LE.lift_r (by simp [TShape.sort])).1 h
    | sort => cases n <;> have .sigma _ _ _ _ h := hM <;> cases TShape.sort_not_le_sigma h
    | @lam _ f₀ =>
      revert hM; unfold WShape.lam'
      split <;> [skip; exact fun _ => .bot
        (fun _ _ => (LR _).mono_r_2_ty hA.le_sort' hmem.isType .sort LogRelBase.TyEq.sort)
        hmem.isType]
      intro | .sigma _ _ _ _ h => cases TShape.lam_not_le_sigma h
    | forallE => have .sigma _ _ _ _ h := hM; cases TShape.forallE_not_le_sigma h
    | pair => have .sigma _ _ _ _ h := hM; cases TShape.pair_not_le_sigma h
    | @sigma k a₂ a₁ aty
    refine .wf₀ fun hΓ₀ => ?_
    have aty := WShape.HasTypePi.iff.1 (aty : WShape.HasTypePi a₂ a₁ true)
    have hA1 := hM.sigma_inv.1
    have cons := Adequate.cons (hΓ₀ := hΓ₀) ihA HA
    refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩ <;> (
      have ⟨_, a', _, le_n, le_a, hA', hSort, hmem'⟩ :=
        (LE_Interp.sound HA W.left.fits).2 hA1 |>.out
      have HAAσ := HA.subst' W.left.wf₀ W.left.toSubstEq
      have S' := W.toSubstEq.lift HA.hasType.1 HAAσ.hasType.1
      have hΓS : ⊢ A.subst σ :: Γ₀ := ⟨W.wf₀, _, HAAσ.hasType.1⟩
      have hΓA : ⊢ A :: Γ := ⟨W.wf, _, HA.hasType.1⟩)
    · have HAσ := HA.hasType.1.subst' W.wf₀ W.toSubstEq
      have HA'σ := HA.hasType.2.subst' W.wf₀ W.toSubstEq
      have hΓS' : ⊢ A.subst σ' :: Γ₀ := ⟨W.wf₀, _, HAσ.hasType.2⟩
      have hSigma_σ : Γ₀ ⊢ (A.subst σ).sigma (B.subst σ.lift) ≡
          (A.subst σ).sigma (B.subst σ.lift) : .sort true :=
        .sigmaDF₀ hΓ₀ HAσ.hasType.1
          (HB.hasType.1.subst hΓS (W.left.toSubstEq.lift HA.hasType.1 HAσ.hasType.1))
      have hSigma_σ' : Γ₀ ⊢ (A.subst σ').sigma (B.subst σ'.lift) ≡
          (A.subst σ').sigma (B.subst σ'.lift) : .sort true :=
        .sigmaDF₀ hΓ₀ HAσ.hasType.2
          (HB.hasType.1.subst hΓS' (W.symm.left.toSubstEq.lift HA.hasType.1 HAσ.hasType.2))
      constructor
      · refine ⟨true, ⟨.sort, .rfl⟩,
          A.subst σ, B.subst σ.lift, A.subst σ', B.subst σ'.lift, u, v,
          ⟨hSigma_σ, .rfl⟩, ⟨hSigma_σ', .rfl⟩, HAσ, HB.hasType.1.subst' hΓS S', ?_, ?_⟩
        · exact toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).1
        simp [LRS.PiDefEq, inst_lift_cons]
        refine ⟨fun _ _ p hp ha hv => ?_, fun _ p hp ha hv => ?_⟩ <;>
          have hB := hM.sigma_inv'.2 p <;> [constructor <;> [
            have W' := cons hp hA1 ha hv W.left;
            ( have := toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).1
              have W' := cons hp hA1 (HAσ.defeqDF ha) ((LR _).conv this hv) W.symm.left )];
            have W' := cons hp hA1 ha.hasType.1 ((LR _).left hv) W] <;>
        · have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
            (LE_Interp.sound HB W'.fits).2 hB |>.out
          exact toValTy le le' (aty.2 _ hp).toType iv hmb ((ihB iB iv hmb).1 W').1
      · have hΓA' : ⊢ A' :: Γ := ⟨W.wf, _, HA.hasType.2⟩
        have hΓA'S : ⊢ A'.subst σ :: Γ₀ := ⟨W.wf₀, _, HA'σ.hasType.1⟩
        have hΓA'S' : ⊢ A'.subst σ' :: Γ₀ := ⟨W.wf₀, _, HA'σ.hasType.2⟩
        have hSigma'_σ : Γ₀ ⊢ (A'.subst σ).sigma (B'.subst σ.lift) ≡
            (A'.subst σ).sigma (B'.subst σ.lift) : .sort true :=
          .sigmaDF₀ hΓ₀ HA'σ.hasType.1
            (HB'.hasType.2.subst hΓA'S (W.left.toSubstEq.lift HA.hasType.2 HA'σ.hasType.1))
        have hSigma'_σ' : Γ₀ ⊢ (A'.subst σ').sigma (B'.subst σ'.lift) ≡
            (A'.subst σ').sigma (B'.subst σ'.lift) : .sort true :=
          .sigmaDF₀ hΓ₀ HA'σ.hasType.2
            (HB'.hasType.2.subst hΓA'S' (W.symm.left.toSubstEq.lift HA.hasType.2 HA'σ.hasType.2))
        refine ⟨true, ⟨.sort, .rfl⟩,
          A'.subst σ, B'.subst σ.lift, A'.subst σ', B'.subst σ'.lift, u, v,
          ⟨hSigma'_σ, .rfl⟩, ⟨hSigma'_σ', .rfl⟩,
          HA'σ, HAAσ.defeqDF_l hΓ₀ (HB.hasType.2.subst' hΓS S'), ?_, ?_⟩
        · exact toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).2
        simp [LRS.PiDefEq, inst_lift_cons]
        have := toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').2 W.left)
        refine ⟨fun _ _ p hp ha hv => ?_, fun _ p hp ha hv => ?_⟩ <;> (
          have hv := (LR _).conv ((LR _).symm_ty this) hv
          have ha := HAAσ.symm.defeqDF ha
          have hB := hM.sigma_inv'.2 p) <;> [constructor <;> [
            have W' := cons hp hA1 ha hv W.left;
            ( have := toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).1
              have W' := cons hp hA1 (HAσ.defeqDF ha) ((LR _).conv this hv) W.symm.left )];
            have W' := cons hp hA1 ha ((LR _).left hv) W] <;>
        · have ⟨_, _, _, le, le', iB, iv, hmb⟩ := (LE_Interp.sound HB W'.fits).2 hB |>.out
          exact toValTy le le' (aty.2 _ hp).toType iv hmb ((ihB iB iv hmb).1 W').2
    · have hΓA' : ⊢ A' :: Γ := ⟨W.wf, _, HA.hasType.2⟩
      have hΓA'S : ⊢ A'.subst σ :: Γ₀ := ⟨W.wf₀, _, HAAσ.hasType.2⟩
      have hSigma_σ : Γ₀ ⊢ (A.subst σ).sigma (B.subst σ.lift) ≡
          (A.subst σ).sigma (B.subst σ.lift) : .sort true :=
        .sigmaDF₀ hΓ₀ HAAσ.hasType.1 (HB.hasType.1.subst hΓS S')
      have hSigma'_σ : Γ₀ ⊢ (A'.subst σ).sigma (B'.subst σ.lift) ≡
          (A'.subst σ).sigma (B'.subst σ.lift) : .sort true :=
        .sigmaDF₀ hΓ₀ HAAσ.hasType.2
          (HB'.hasType.2.subst hΓA'S (W.toSubstEq.lift HA.hasType.2 HAAσ.hasType.2))
      refine ⟨true, ⟨.sort, .rfl⟩,
        A.subst σ, B.subst σ.lift, A'.subst σ, B'.subst σ.lift, u, v,
        ⟨hSigma_σ, .rfl⟩, ⟨hSigma'_σ, .rfl⟩, HAAσ, HB.subst' hΓS S', ?_, ?_⟩
      · exact toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').2 W)
      simp [LRS.PiDefEq, inst_lift_cons]
      refine ⟨fun _ _ p hp ha hv => ?_, fun _ p hp ha hv => ?_⟩ <;> (
        have hB := hM.sigma_inv'.2 p
        have W' := cons hp hA1 ha hv W
        have ⟨_, _, _, le, le', iB, iv, hmb⟩ := (LE_Interp.sound HB W'.fits).2 hB |>.out)
      · exact ⟨toValTy le le' (aty.2 _ hp).toType iv hmb ((ihB iB iv hmb).1 W').1,
               toValTy le le' (aty.2 _ hp).toType iv hmb ((ihB iB iv hmb).1 W').2⟩
      · exact toValTy le le' (aty.2 _ hp).toType iv hmb ((ihB iB iv hmb).2 W')
  | @pairDF Γ A A' u B B' v x x' y y' HA HB HB' Hx Hy HBxx' HSigmaTy ihA ihB ihB' ihx ihy ihBa ihAB =>
    cases hmem.unfold with
    | bot hm =>
      cases hm.unfold with
      | bot _ => exact .bot (fun _ _ => (LR _).bot_ty) hm
      | sort =>
        cases n
        all_goals (let .sigma _ _ _ _ le := hA; exact (TShape.sort_not_le_sigma le).elim)
      | forallE => let .sigma _ _ _ _ le := hA; exact (TShape.forallE_not_le_sigma le).elim
      | sigma => exact LR.Adequate.bot' HSigmaTy hA hmem.isType ihAB
    | sort => cases n <;> have .pair _ _ h := hM <;> cases TShape.sort_not_le_pair' h
    | @lam k f₀ =>
      revert hM; unfold WShape.lam'
      split <;> [skip; exact fun _ => LR.Adequate.bot' HSigmaTy hA hmem.isType ihAB]
      intro | .pair _ _ h => cases TShape.lam_not_le_pair' h
    | forallE => have .pair _ _ h := hM; cases TShape.forallE_not_le_pair' h
    | sigma => have .pair _ _ h := hM; cases TShape.sigma_not_le_pair' h
    | @pair k ms mt at_ bt ph hPair
    refine .wf₀ fun hΓ₀ => .wf fun hΓ => ?_
    have hA1 := hA.sigma_inv.1
    have hPair' := WShape.HasTypePair.def.1 hPair
    have aty := WShape.HasTypePi.iff.1 (hPair'.1 : WShape.HasTypePi bt at_ true)
    have cons := Adequate.cons (hΓ₀ := hΓ₀) ihA HA
    -- Destructure hM to extract component LE_Interps and le_m
    let .pair (xV := xV) (yV := yV) hX hY le_m := hM
    -- Setup whr lemmas: .fst (.pair _ _ a _) ⤳* a and .snd (.pair _ _ _ b) ⤳* b
    have fst_pair {A B a b : Term} : (.fst (.pair A B a b) : Term) ⤳* a := .tail .rfl .pair_fst
    have snd_pair {A B a b : Term} : (.snd (.pair A B a b) : Term) ⤳* b := .tail .rfl .pair_snd
    -- Derive ms ≤ xV and mt ≤ yV from le_m for use with hX, hY
    have hms_x : LE_Interp ρ ms.T x := by
      refine hX.mono ?_
      have le_m' := le_m
      rw [show (.pair ms mt ph : WShape (k+1)) = .pair' ms mt from
        WShape.pair_eq_pair'] at le_m'
      have ⟨le_ms, _⟩ := TShape.LE.pair'_decomp le_m'
      exact (TShape.LE.def (Nat.le_max_left _ _) (Nat.le_max_right _ _)).2 le_ms
    have hmt_y : LE_Interp ρ mt.T y := by
      refine hY.mono ?_
      have le_m' := le_m
      rw [show (.pair ms mt ph : WShape (k+1)) = .pair' ms mt from
        WShape.pair_eq_pair'] at le_m'
      have ⟨_, le_mt⟩ := TShape.LE.pair'_decomp le_m'
      exact (TShape.LE.def (Nat.le_max_left _ _) (Nat.le_max_right _ _)).2 le_mt
    -- The original pair-equation (Γ-level, no substitution yet)
    have hPairEq : Γ ⊢ Term.pair A B x y ≡ Term.pair A' B' x' y' : Term.sigma A B :=
      .pairDF₀ hΓ HA HB Hx Hy
    -- pair_tmEq: returns ONE TmEq slot of the Adequate; the three slots (M-validity,
    -- N-validity, diagonal) are obtained by three different applications.
    -- Caller pre-computes the IH outputs and passes them in.
    have pair_tmEq : ∀ {A_L A_R B_L B_R x_L x_R y_L y_R σ_L σ_R}
        (W : SubstWF Γ₀ σ_L σ_R Γ ρ)
        (_hP : Γ ⊢ Term.pair A_L B_L x_L y_L ≡ Term.pair A_R B_R x_R y_R : Term.sigma A B)
        (HA_L_to_A : Γ ⊢ A_L ≡ A : .sort u)
        (HA_R_to_A : Γ ⊢ A_R ≡ A : .sort u)
        -- pairDF-style hypotheses (for .pair_fst, .pair_snd, source IsDefEqs)
        (HA_L_R : Γ ⊢ A_L ≡ A_R : .sort u)
        (HB_L_R_at_A_L : A_L::Γ ⊢ B_L ≡ B_R : .sort v)
        (HB_L_R_at_A_R : A_R::Γ ⊢ B_L ≡ B_R : .sort v)
        (Hx_L_R : Γ ⊢ x_L ≡ x_R : A_L)
        (Hy_L_R : Γ ⊢ y_L ≡ y_R : B_L.inst x_L)
        (HBxx_L_R : Γ ⊢ B_L.inst x_L ≡ B_R.inst x_R : .sort v)
        (HSigma_L : Γ ⊢ Term.sigma A_L B_L : .sort true)
        -- bridges between outer (x, y, B.inst x) and pair components
        (Hx_x_L : Γ ⊢ x ≡ x_L : A)
        (HBxx_outer_L : Γ ⊢ B.inst x ≡ B_L.inst x_L : .sort v)
        (HBxx_outer_R : Γ ⊢ B.inst x ≡ B_R.inst x_R : .sort v)
        (ihTyAA : (LR hΓ₀).TyEq (A.subst σ_L) (A.subst σ_L) at_)
        (ihTmx : (LR hΓ₀).TmEq (x_L.subst σ_L) (x_R.subst σ_R) (A.subst σ_L) ms at_)
        (ihTm_x_to_x_L : (LR hΓ₀).TmEq (x.subst σ_L) (x_L.subst σ_L) (A.subst σ_L) ms at_)
        (ihTmy : (LR hΓ₀).TmEq (y_L.subst σ_L) (y_R.subst σ_R)
                  ((B.subst σ_L.lift).inst (x.subst σ_L)) mt (bt.app ms)),
        (LR hΓ₀).TmEq
          ((Term.pair A_L B_L x_L y_L).subst σ_L) ((Term.pair A_R B_R x_R y_R).subst σ_R)
          ((Term.sigma A B).subst σ_L) (.pair ms mt ph) (.sigma at_ bt) := by
      intro A_L A_R B_L B_R x_L x_R y_L y_R σ_L σ_R W hP HA_L_to_A HA_R_to_A
        HA_L_R HB_L_R_at_A_L HB_L_R_at_A_R Hx_L_R Hy_L_R HBxx_L_R HSigma_L
        Hx_x_L HBxx_outer_L HBxx_outer_R ihTyAA ihTmx ihTm_x_to_x_L ihTmy
      show (LR hΓ₀).TmEq _ _ _ (.pair ms mt ph) (.sigma at_ bt)
      -- Type-level setup for OUTER A, B (ValTyPi2 fields)
      have HAσL : Γ₀ ⊢ A.subst σ_L : Term.sort u :=
        (HA.hasType.1.subst' W.left.wf₀ W.left.toSubstEq).hasType.1
      have hΓA_outer : ⊢ A :: Γ := ⟨W.wf, _, HA.hasType.1⟩
      have hΓS_L : ⊢ A.subst σ_L :: Γ₀ := ⟨W.wf₀, _, HAσL⟩
      have HBσL : A.subst σ_L :: Γ₀ ⊢ B.subst σ_L.lift : Term.sort v :=
        (HB.hasType.1.subst' hΓS_L
          (W.left.toSubstEq.lift HA.hasType.1 HAσL)).hasType.1
      -- pi_app helper (uses outer ihB, B at outer A::Γ)
      have pi_app : ∀ {{x' x'' : Term}} {{p : WShape k}}, p.HasType at_ →
          Γ₀ ⊢ x' ≡ x'' : A.subst σ_L →
          (LR hΓ₀).TmEq x' x'' (A.subst σ_L) p at_ →
          (LR hΓ₀).TyEq (B.subst (σ_L.cons x')) (B.subst (σ_L.cons x'')) (bt.app p) := by
        intro x' x'' p hp ha hv
        have W' := cons hp hA1 ha hv W.left
        have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
          (LE_Interp.sound HB W'.fits).2 (hA.sigma_inv'.2 p) |>.out
        exact toValTy le le' (aty.2 _ hp).toType iv hmb ((ihB iB iv hmb).1 W').1
      -- LHS pair self-typing at OUTER sigma A B (for .fst pair_L typing at A.σ_L):
      have hPairTyσ_L : Γ₀ ⊢
          (Term.pair A_L B_L x_L y_L).subst σ_L ≡
          (Term.pair A_L B_L x_L y_L).subst σ_L :
          (Term.sigma A B).subst σ_L :=
        hP.hasType.1.subst' W.left.wf₀ W.left.toSubstEq
      -- LHS-RHS pair equation at OUTER sigma A B (heterogeneous σ_L-σ_R):
      have hMNσσ : Γ₀ ⊢
          (Term.pair A_L B_L x_L y_L).subst σ_L ≡
          (Term.pair A_R B_R x_R y_R).subst σ_R :
          (Term.sigma A B).subst σ_L :=
        hP.subst' W.wf₀ W.toSubstEq
      refine ⟨A.subst σ_L, B.subst σ_L.lift, u, v, .rfl (.sigmaDF₀ hΓ₀ HAσL HBσL), HAσL, ?_, HBσL,
        ?_, ?_, hPair, ?_, ?_⟩
      · -- IH.TyEq A.σ_L A.σ_L at_
        exact ihTyAA
      · -- .fst pair_L.σ_L : A.σ_L
        exact (hPairTyσ_L.fstDF₀ W.wf₀).hasType.1
      · -- .fst pair_R.σ_R : A.σ_L
        exact (hMNσσ.fstDF₀ W.wf₀).hasType.2
      · -- PiDefEq
        simp [LRS.PiDefEq, inst_lift_cons]
        refine ⟨fun _ _ p hp ha hv => pi_app hp ha hv, fun _ p hp ha hv => pi_app hp ha hv⟩
      · -- PairDefEq pair_L pair_R
        -- ===== LHS side: setup at NATURAL A_L =====
        have HA_Lσ : Γ₀ ⊢ A_L.subst σ_L : .sort u :=
          (HA_L_to_A.hasType.1.subst' W.left.wf₀ W.left.toSubstEq).hasType.1
        have hΓA_L : ⊢ A_L :: Γ := ⟨W.wf, _, HA_L_to_A.hasType.1⟩
        have hΓA_LS_L : ⊢ A_L.subst σ_L :: Γ₀ := ⟨W.wf₀, _, HA_Lσ⟩
        have HB_Lσ : A_L.subst σ_L :: Γ₀ ⊢ B_L.subst σ_L.lift : .sort v :=
          (HB_L_R_at_A_L.hasType.1.subst hΓA_LS_L
            (W.left.toSubstEq.lift HA_L_to_A.hasType.1 HA_Lσ)).hasType.1
        have hx_LσTy : Γ₀ ⊢ x_L.subst σ_L : A_L.subst σ_L :=
          (Hx_L_R.hasType.1.subst' W.left.wf₀ W.left.toSubstEq).hasType.1
        have hy_LσTy : Γ₀ ⊢ y_L.subst σ_L : (B_L.subst σ_L.lift).inst (x_L.subst σ_L) := by
          have := (Hy_L_R.hasType.1.subst' W.left.wf₀ W.left.toSubstEq).hasType.1
          rwa [subst_inst] at this
        -- Conversion A_L.σ_L ≡ A.σ_L (diagonal at σ_L)
        have HA_L_to_A_σL : Γ₀ ⊢ A_L.subst σ_L ≡ A.subst σ_L : .sort u :=
          HA_L_to_A.subst' W.left.wf₀ W.left.toSubstEq
        -- Natural LHS pair eq at sigma A_L B_L
        have hPair_natural_eq : Γ ⊢
            Term.pair A_L B_L x_L y_L ≡ Term.pair A_R B_R x_R y_R : Term.sigma A_L B_L :=
          .pairDF₀ W.wf HA_L_R HB_L_R_at_A_L Hx_L_R Hy_L_R
        have hPair_L_natural_σL : Γ₀ ⊢
            (Term.pair A_L B_L x_L y_L).subst σ_L ≡
            (Term.pair A_L B_L x_L y_L).subst σ_L :
            (Term.sigma A_L B_L).subst σ_L :=
          hPair_natural_eq.hasType.1.subst' W.left.wf₀ W.left.toSubstEq
        have hFst_L_natural_Ty : Γ₀ ⊢
            Term.fst ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L)) :
            A_L.subst σ_L :=
          (hPair_L_natural_σL.fstDF₀ W.wf₀).hasType.1
        have hFst_L_eq_at_A_L : Γ₀ ⊢
            Term.fst ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L)) ≡
            x_L.subst σ_L : A_L.subst σ_L :=
          HB_Lσ.pair_fst₀ W.wf₀ hx_LσTy hy_LσTy
        have hFst_L_eq : Γ₀ ⊢
            Term.fst ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L)) ≡
            x_L.subst σ_L : A.subst σ_L :=
          HA_L_to_A_σL.defeqDF hFst_L_eq_at_A_L
        -- ===== RHS side: setup at NATURAL A_R, σ_R =====
        have HA_Rσ : Γ₀ ⊢ A_R.subst σ_R : .sort u :=
          (HA_R_to_A.hasType.1.subst' W.symm.left.wf₀ W.symm.left.toSubstEq).hasType.1
        have hΓA_R : ⊢ A_R :: Γ := ⟨W.wf, _, HA_R_to_A.hasType.1⟩
        have hΓA_RS_R : ⊢ A_R.subst σ_R :: Γ₀ := ⟨W.wf₀, _, HA_Rσ⟩
        have HB_Rσ : A_R.subst σ_R :: Γ₀ ⊢ B_R.subst σ_R.lift : .sort v :=
          (HB_L_R_at_A_R.hasType.2.subst hΓA_RS_R
            (W.symm.left.toSubstEq.lift HA_R_to_A.hasType.1 HA_Rσ)).hasType.1
        -- x_R typing at A_R.σ_R (via A_L → A_R conversion)
        have HA_L_R_σR : Γ₀ ⊢ A_L.subst σ_R ≡ A_R.subst σ_R : .sort u :=
          HA_L_R.subst' W.symm.left.wf₀ W.symm.left.toSubstEq
        have hx_RσTy : Γ₀ ⊢ x_R.subst σ_R : A_R.subst σ_R :=
          HA_L_R_σR.defeqDF
            (Hx_L_R.hasType.2.subst hΓ₀ W.symm.left.toSubstEq).hasType.1
        -- y_R typing at (B_R.σ_R.lift).inst (x_R.σ_R)
        have hy_RσTy : Γ₀ ⊢ y_R.subst σ_R :
            (B_R.subst σ_R.lift).inst (x_R.subst σ_R) := by
          have h1 := (Hy_L_R.hasType.2.subst hΓ₀ W.symm.left.toSubstEq).hasType.1
          rw [subst_inst] at h1
          have hBxx_σR : Γ₀ ⊢ (B_L.inst x_L).subst σ_R ≡
              (B_R.inst x_R).subst σ_R : .sort v :=
            HBxx_L_R.subst hΓ₀ W.symm.left.toSubstEq
          rw [subst_inst, subst_inst] at hBxx_σR
          exact hBxx_σR.defeqDF h1
        -- Conversion A_R.σ_R ≡ A.σ_L (heterogeneous σ_R → σ_L for the cross direction)
        have HA_R_to_A_het : Γ₀ ⊢ A_R.subst σ_R ≡ A.subst σ_L : .sort u :=
          HA_R_to_A.subst' W.wf₀ W.symm.toSubstEq
        -- Natural RHS pair self-typing at sigma A_R B_R
        have hSigmaConv : Γ ⊢ Term.sigma A_L B_L ≡ Term.sigma A_R B_R : .sort true :=
          .sigmaDF₀ W.wf HA_L_R HB_L_R_at_A_L
        have hPair_R_at_AR_BR : Γ ⊢ Term.pair A_R B_R x_R y_R : Term.sigma A_R B_R :=
          hSigmaConv.defeqDF hPair_natural_eq.hasType.2
        have hPair_R_natural_σR : Γ₀ ⊢
            (Term.pair A_R B_R x_R y_R).subst σ_R ≡
            (Term.pair A_R B_R x_R y_R).subst σ_R :
            (Term.sigma A_R B_R).subst σ_R :=
          hPair_R_at_AR_BR.subst' W.symm.left.wf₀ W.symm.left.toSubstEq
        have hFst_R_natural_Ty : Γ₀ ⊢
            Term.fst ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R)) :
            A_R.subst σ_R :=
          (hPair_R_natural_σR.fstDF₀ W.wf₀).hasType.1
        have hFst_R_eq_at_A_R : Γ₀ ⊢
            Term.fst ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R)) ≡
            x_R.subst σ_R : A_R.subst σ_R :=
          .pair_fst₀ W.wf₀ HB_Rσ hx_RσTy hy_RσTy
        have hFst_R_eq : Γ₀ ⊢
            Term.fst ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R)) ≡
            x_R.subst σ_R : A.subst σ_L :=
          HA_R_to_A_het.defeqDF hFst_R_eq_at_A_R
        -- Source IsDefEq: .fst pair_L.σ_L ≡ .fst pair_R.σ_R : A.σ_L
        have hFst_LR_src : Γ₀ ⊢
            Term.fst ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L)) ≡
            Term.fst ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R)) :
            A.subst σ_L :=
          hMNσσ.fstDF₀ W.wf₀
        refine ⟨?_, ?_⟩
        · -- IH.TmEq (.fst pair_L) (.fst pair_R) (A.σ_L) ms at_
          exact ((LR _).whr ⟨hFst_L_eq, fst_pair⟩ ⟨hFst_R_eq, fst_pair⟩ hFst_LR_src).2 ihTmx
        · -- IH.TmEq (.snd pair_L) (.snd pair_R) ((B.σ.lift).inst (.fst pair_L)) mt (bt.app ms)
          -- ===== LHS .snd: build at NATURAL (A_L, B_L, x_L), bridge to outer =====
          have hBFst_L_self : Γ₀ ⊢
              (B_L.subst σ_L.lift).inst
                (Term.fst ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L))) ≡
              (B_L.subst σ_L.lift).inst
                (Term.fst ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L))) :
              .sort v :=
            IsDefEq.instDF hΓ₀ HA_Lσ .sort HB_Lσ hFst_L_natural_Ty
          have hSnd_L_at_Fst_L : Γ₀ ⊢
              Term.snd ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L)) :
              (B_L.subst σ_L.lift).inst
                (Term.fst ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L))) :=
            (hPair_L_natural_σL.sndDF₀ W.wf₀).hasType.1
          have hBx_L_to_BFst_L : Γ₀ ⊢
              (B_L.subst σ_L.lift).inst (x_L.subst σ_L) ≡
              (B_L.subst σ_L.lift).inst
                (Term.fst ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L))) :
              .sort v :=
            IsDefEq.instDF hΓ₀ HA_Lσ .sort HB_Lσ hFst_L_eq_at_A_L.symm
          have hSnd_L_at_x_L : Γ₀ ⊢
              Term.snd ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L)) :
              (B_L.subst σ_L.lift).inst (x_L.subst σ_L) :=
            hBx_L_to_BFst_L.symm.defeqDF hSnd_L_at_Fst_L
          have hSnd_L_eq_at_x_L : Γ₀ ⊢
              Term.snd ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L)) ≡
              y_L.subst σ_L : (B_L.subst σ_L.lift).inst (x_L.subst σ_L) :=
            .pair_snd₀ W.wf₀ HB_Lσ hx_LσTy hy_LσTy
          -- Bridge from (B_L.σ_L.lift).inst (x_L.σ_L) to (B.σ_L.lift).inst (x.σ_L)
          have hBxx_L_bridge : Γ₀ ⊢
              (B.subst σ_L.lift).inst (x.subst σ_L) ≡
              (B_L.subst σ_L.lift).inst (x_L.subst σ_L) : .sort v := by
            have h := HBxx_outer_L.subst hΓ₀ W.left.toSubstEq
            rwa [subst_inst, subst_inst] at h
          have hSnd_L_eq_at_outer_x : Γ₀ ⊢
              Term.snd ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L)) ≡
              y_L.subst σ_L : (B.subst σ_L.lift).inst (x.subst σ_L) :=
            hBxx_L_bridge.symm.defeqDF hSnd_L_eq_at_x_L
          -- Bridge x.σ_L to .fst pair_L.σ_L
          have hx_x_L_σL : Γ₀ ⊢ x.subst σ_L ≡ x_L.subst σ_L : A.subst σ_L :=
            Hx_x_L.subst' W.left.wf₀ W.left.toSubstEq
          have hxσL_to_FstL : Γ₀ ⊢ x.subst σ_L ≡
              Term.fst ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L)) :
              A.subst σ_L := hx_x_L_σL.trans hFst_L_eq.symm
          have hBxFstL : Γ₀ ⊢
              (B.subst σ_L.lift).inst (x.subst σ_L) ≡
              (B.subst σ_L.lift).inst
                (Term.fst ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L))) :
              .sort v :=
            IsDefEq.instDF hΓ₀ HAσL .sort HBσL hxσL_to_FstL
          have hSnd_L_eq : Γ₀ ⊢
              Term.snd ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L)) ≡
              y_L.subst σ_L : (B.subst σ_L.lift).inst
                (Term.fst ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L))) :=
            hBxFstL.defeqDF hSnd_L_eq_at_outer_x
          -- ===== RHS .snd: build at NATURAL (A_R, B_R, x_R, σ_R), bridge to outer =====
          have hBFst_R_self : Γ₀ ⊢
              (B_R.subst σ_R.lift).inst
                (Term.fst ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R))) ≡
              (B_R.subst σ_R.lift).inst
                (Term.fst ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R))) :
              .sort v :=
            IsDefEq.instDF hΓ₀ HA_Rσ .sort HB_Rσ hFst_R_natural_Ty
          have hSnd_R_at_Fst_R : Γ₀ ⊢
              Term.snd ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R)) :
              (B_R.subst σ_R.lift).inst
                (Term.fst ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R))) :=
            (hPair_R_natural_σR.sndDF₀ W.wf₀).hasType.1
          have hBx_R_to_BFst_R : Γ₀ ⊢
              (B_R.subst σ_R.lift).inst (x_R.subst σ_R) ≡
              (B_R.subst σ_R.lift).inst
                (Term.fst ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R))) :
              .sort v :=
            IsDefEq.instDF hΓ₀ HA_Rσ .sort HB_Rσ hFst_R_eq_at_A_R.symm
          have hSnd_R_at_x_R : Γ₀ ⊢
              Term.snd ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R)) :
              (B_R.subst σ_R.lift).inst (x_R.subst σ_R) :=
            hBx_R_to_BFst_R.symm.defeqDF hSnd_R_at_Fst_R
          have hSnd_R_eq_at_x_R : Γ₀ ⊢
              Term.snd ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R)) ≡
              y_R.subst σ_R : (B_R.subst σ_R.lift).inst (x_R.subst σ_R) :=
            .pair_snd₀ W.wf₀ HB_Rσ hx_RσTy hy_RσTy
          -- Bridge from (B_R.σ_R.lift).inst (x_R.σ_R) to (B.σ_R.lift).inst (x.σ_R)
          have hBxx_R_bridge : Γ₀ ⊢
              (B.subst σ_R.lift).inst (x.subst σ_R) ≡
              (B_R.subst σ_R.lift).inst (x_R.subst σ_R) : .sort v := by
            have h := HBxx_outer_R.subst hΓ₀ W.symm.left.toSubstEq
            rwa [subst_inst, subst_inst] at h
          have hSnd_R_eq_at_outer_x_σR : Γ₀ ⊢
              Term.snd ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R)) ≡
              y_R.subst σ_R : (B.subst σ_R.lift).inst (x.subst σ_R) :=
            hBxx_R_bridge.symm.defeqDF hSnd_R_eq_at_x_R
          -- Cross-σ bridge: (B.σ_R.lift).inst (x.σ_R) ≡ (B.σ_L.lift).inst (x.σ_L)
          have hxσLR : Γ₀ ⊢ x.subst σ_L ≡ x.subst σ_R : A.subst σ_L :=
            Hx.hasType.1.subst' W.wf₀ W.toSubstEq
          have hWcons : Ctx.SubstEq Γ₀ (σ_L.cons (x.subst σ_L)) (σ_R.cons (x.subst σ_R)) (A::Γ) :=
            .cons W.toSubstEq HA.hasType.1 hxσLR
          have hBcross_inst : Γ₀ ⊢
              (B.subst σ_L.lift).inst (x.subst σ_L) ≡
              (B.subst σ_R.lift).inst (x.subst σ_R) : .sort v := by
            have h := HB.hasType.1.subst' hΓ₀ hWcons
            rwa [← inst_lift_cons, ← inst_lift_cons] at h
          have hSnd_R_eq_at_outer_x_σL : Γ₀ ⊢
              Term.snd ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R)) ≡
              y_R.subst σ_R : (B.subst σ_L.lift).inst (x.subst σ_L) :=
            hBcross_inst.symm.defeqDF hSnd_R_eq_at_outer_x_σR
          have hSnd_R_eq : Γ₀ ⊢
              Term.snd ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R)) ≡
              y_R.subst σ_R : (B.subst σ_L.lift).inst
                (Term.fst ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L))) :=
            hBxFstL.defeqDF hSnd_R_eq_at_outer_x_σL
          -- ===== Source: .snd pair_L ≡ .snd pair_R at outer type =====
          have hBFstLR_self_at_outer : Γ₀ ⊢
              (B.subst σ_L.lift).inst
                (Term.fst ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L))) ≡
              (B.subst σ_L.lift).inst
                (Term.fst ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R))) :
              .sort v :=
            IsDefEq.instDF hΓ₀ HAσL .sort HBσL hFst_LR_src
          have hSnd_LR_src : Γ₀ ⊢
              Term.snd ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L)) ≡
              Term.snd ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R)) :
              (B.subst σ_L.lift).inst
                (Term.fst ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L))) :=
            hMNσσ.sndDF₀ W.wf₀
          -- whr discharge + conv ihTmy
          refine ((LR _).whr ⟨hSnd_L_eq, snd_pair⟩ ⟨hSnd_R_eq, snd_pair⟩ hSnd_LR_src).2 ?_
          -- Build hxFst: TmEq x.σ_L (.fst pair_L.σ_L) A.σ_L ms at_ via whr from ihTm_x_to_x_L
          have hxσTy_outer : Γ₀ ⊢ x.subst σ_L : A.subst σ_L :=
            (Hx.hasType.1.subst' W.left.wf₀ W.left.toSubstEq).hasType.1
          have hxFst : (LR hΓ₀).TmEq (x.subst σ_L)
              (Term.fst ((A_L.subst σ_L).pair (B_L.subst σ_L.lift)
                (x_L.subst σ_L) (y_L.subst σ_L))) (A.subst σ_L) ms at_ :=
            ((LR _).whr ⟨hxσTy_outer, .rfl⟩ ⟨hFst_L_eq, fst_pair⟩ hxσL_to_FstL).2 ihTm_x_to_x_L
          have ty_conv := pi_app hPair'.2.1 hxσL_to_FstL hxFst
          rw [← inst_lift_cons, ← inst_lift_cons] at ty_conv
          exact (LR _).conv ty_conv ihTmy
    refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩ <;> (
      have ⟨_, a', _, le_n, le_a, hA', hSort, hmem'⟩ :=
        (LE_Interp.sound HA W.left.fits).2 hA1 |>.out
      have HAAσ := HA.subst' W.left.wf₀ W.left.toSubstEq
      have S' := W.toSubstEq.lift HA.hasType.1 HAAσ.hasType.1
      have hΓS : ⊢ A.subst σ :: Γ₀ := ⟨W.wf₀, _, HAAσ.hasType.1⟩
      have hΓA : ⊢ A :: Γ := ⟨W.wf, _, HA.hasType.1⟩)
    · -- validity (σ → σ')
      have HAσ := HA.hasType.1.subst' W.wf₀ W.toSubstEq
      have HA'σ := HA.hasType.2.subst' W.wf₀ W.toSubstEq
      have hPairTyσ : Γ₀ ⊢ Term.pair (A.subst σ) (B.subst σ.lift) (x.subst σ) (y.subst σ)
                        : Term.sigma (A.subst σ) (B.subst σ.lift) :=
        (hPairEq.subst' W.wf₀ W.toSubstEq).hasType.1
      -- σ → σ' equation for M (M.subst σ ≡ M.subst σ' at type (.sigma A B).subst σ)
      have hMMσσ' : Γ₀ ⊢ Term.pair (A.subst σ) (B.subst σ.lift) (x.subst σ) (y.subst σ) ≡
                       Term.pair (A.subst σ') (B.subst σ'.lift) (x.subst σ') (y.subst σ') :
                       Term.sigma (A.subst σ) (B.subst σ.lift) :=
        hPairEq.hasType.1.subst' W.wf₀ W.toSubstEq
      have HBσ : A.subst σ :: Γ₀ ⊢ B.subst σ.lift : Term.sort v :=
        (HB.hasType.1.subst' hΓS S').hasType.1
      -- Reusable PiDefEq helper (for PiDefEq slot and snd type-conversion below)
      have pi_app : ∀ {{x' x'' : Term}} {{p : WShape k}}, p.HasType at_ →
          Γ₀ ⊢ x' ≡ x'' : A.subst σ →
          (LR hΓ₀).TmEq x' x'' (A.subst σ) p at_ →
          (LR hΓ₀).TyEq (B.subst (σ.cons x')) (B.subst (σ.cons x'')) (bt.app p) := by
        intro x' x'' p hp ha hv
        have W' := cons hp hA1 ha hv W.left
        have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
          (LE_Interp.sound HB W'.fits).2 (hA.sigma_inv'.2 p) |>.out
        exact toValTy le le' (aty.2 _ hp).toType iv hmb ((ihB iB iv hmb).1 W').1
      constructor
      · -- M-validity: TmEq (M.subst σ) (M.subst σ') ((.sigma A B).subst σ) ms-pair-mt at_-sigma-bt
        show (LR hΓ₀).TmEq _ _ _ (.pair ms mt ph) (.sigma at_ bt)
        have hBinst_LE_M : LE_Interp ρ (bt.app ms).T (B.inst x) := hA.sigma_inv.2 hms_x
        have ihTyAA_M : (LR hΓ₀).TyEq (A.subst σ) (A.subst σ) at_ :=
          (LR _).left_ty <| toValTy le_n le_a aty.1.isType hSort hmem'
            ((ihA hA' hSort hmem').1 W).1
        have ihTmx_M : (LR hΓ₀).TmEq (x.subst σ) (x.subst σ') (A.subst σ) ms at_ :=
          ((ihx hms_x hA1 hPair'.2.1).1 W).1
        have ihTm_x_to_xL_M : (LR hΓ₀).TmEq (x.subst σ) (x.subst σ) (A.subst σ) ms at_ :=
          (LR _).left (((ihx hms_x hA1 hPair'.2.1).1 W).1)
        have ihTmy_M : (LR hΓ₀).TmEq (y.subst σ) (y.subst σ')
            ((B.subst σ.lift).inst (x.subst σ)) mt (bt.app ms) := by
          have := ((ihy hmt_y hBinst_LE_M hPair'.2.2).1 W).1
          rwa [subst_inst] at this
        exact pair_tmEq W hPairEq.hasType.1 HA.hasType.1 HA.hasType.1
          HA.hasType.1 HB.hasType.1 HB.hasType.1
          Hx.hasType.1 Hy.hasType.1 HBxx'.hasType.1 HSigmaTy.hasType.1
          Hx.hasType.1 HBxx'.hasType.1 HBxx'.hasType.1
          ihTyAA_M ihTmx_M ihTm_x_to_xL_M ihTmy_M
      · -- N-validity: TmEq (N.subst σ) (N.subst σ') ((.sigma A B).subst σ) ...
        -- N has natural type .sigma A' B'; we type it at .sigma A B via hPairEq.hasType.2
        show (LR hΓ₀).TmEq _ _ _ (.pair ms mt ph) (.sigma at_ bt)
        have hBinst_LE_N : LE_Interp ρ (bt.app ms).T (B.inst x) := hA.sigma_inv.2 hms_x
        have ihTyAA_N : (LR hΓ₀).TyEq (A.subst σ) (A.subst σ) at_ :=
          (LR _).left_ty <| toValTy le_n le_a aty.1.isType hSort hmem'
            ((ihA hA' hSort hmem').1 W).1
        have ihTmx_N : (LR hΓ₀).TmEq (x'.subst σ) (x'.subst σ') (A.subst σ) ms at_ :=
          ((ihx hms_x hA1 hPair'.2.1).1 W).2
        have ihTm_x_to_xL_N : (LR hΓ₀).TmEq (x.subst σ) (x'.subst σ) (A.subst σ) ms at_ :=
          (ihx hms_x hA1 hPair'.2.1).2 W.left
        have ihTmy_N : (LR hΓ₀).TmEq (y'.subst σ) (y'.subst σ')
            ((B.subst σ.lift).inst (x.subst σ)) mt (bt.app ms) := by
          have := ((ihy hmt_y hBinst_LE_N hPair'.2.2).1 W).2
          rwa [subst_inst] at this
        have HSigmaA'B' : Γ ⊢ Term.sigma A' B' : .sort true :=
          (IsDefEq.sigmaDF₀ W.wf HA.hasType.2 HB'.hasType.2).hasType.1
        have Hx'_at_A' : Γ ⊢ x' ≡ x' : A' := HA.defeqDF Hx.hasType.2
        have Hy'_at_B'x' : Γ ⊢ y' ≡ y' : B'.inst x' := HBxx'.defeqDF Hy.hasType.2
        exact pair_tmEq W hPairEq.hasType.2 HA.symm HA.symm
          HA.hasType.2 HB'.hasType.2 HB'.hasType.2
          Hx'_at_A' Hy'_at_B'x' HBxx'.hasType.2 HSigmaA'B'
          Hx HBxx' HBxx'
          ihTyAA_N ihTmx_N ihTm_x_to_xL_N ihTmy_N
    · -- equation (σ → σ): TmEq (M.subst σ) (N.subst σ) ((.sigma A B).subst σ) ...
      have hBinst_LE : LE_Interp ρ (bt.app ms).T (B.inst x) := hA.sigma_inv.2 hms_x
      have ihTyAA_diag : (LR hΓ₀).TyEq (A.subst σ) (A.subst σ) at_ :=
        (LR _).left_ty <| toValTy le_n le_a aty.1.isType hSort hmem'
          ((ihA hA' hSort hmem').2 W)
      have ihTmx_diag : (LR hΓ₀).TmEq (x.subst σ) (x'.subst σ) (A.subst σ) ms at_ :=
        (ihx hms_x hA1 hPair'.2.1).2 W
      have ihTm_x_to_xL_diag : (LR hΓ₀).TmEq (x.subst σ) (x.subst σ) (A.subst σ) ms at_ :=
        (LR _).left (((ihx hms_x hA1 hPair'.2.1).1 W).1)
      have ihTmy_diag : (LR hΓ₀).TmEq (y.subst σ) (y'.subst σ)
          ((B.subst σ.lift).inst (x.subst σ)) mt (bt.app ms) := by
        have := (ihy hmt_y hBinst_LE hPair'.2.2).2 W
        rwa [subst_inst] at this
      exact pair_tmEq W hPairEq HA.hasType.1 HA.symm
        HA HB HB' Hx Hy HBxx' HSigmaTy.hasType.1
        Hx.hasType.1 HBxx'.hasType.1 HBxx'
        ihTyAA_diag ihTmx_diag ihTm_x_to_xL_diag ihTmy_diag
  | @fstDF Γ A u B v p p' hA_typ hB_typ hP ihA_typ ihB_typ ihP =>
    cases hM with | bot => exact .bot' hA_typ hA hmem.isType ihA_typ | fst hP_interp le_m
    rename_i n_s s
    refine .wf₀ fun hΓ₀ => ?_
    suffices ∀ {p p' σ σ'}, SubstWF Γ₀ σ σ' Γ ρ →
        Γ ⊢ p ≡ p' : .sigma A B →
        LE_Interp ρ (WShape.T s) p →
        (∀ {n'} {mp ap : WShape n'}, LE_Interp ρ mp.T p → LE_Interp ρ ap.T (.sigma A B) →
          mp.HasType ap → Adequate Γ₀ Γ ρ p p' (.sigma A B) mp ap) →
        (LR hΓ₀).TmEq ((Term.fst p).subst σ) ((Term.fst p').subst σ') (A.subst σ) m a by
      refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
      · exact this W hP.hasType.1 hP_interp (fun hp hsig hT => (ihP hp hsig hT).left)
      · refine this W hP.hasType.2 ((LE_Interp.sound hP W.fits).1.1 hP_interp) ?_
        exact fun hp hsig hT => ((ihP ((LE_Interp.sound hP W.left.fits).1.2 hp) hsig hT).symm hP).left
      · exact this W hP hP_interp (fun hp hsig hT => ihP hp hsig hT)
    intro p p' σ σ' W hP_eq hP_in ihP_inner
    have ⟨_, mp, _, le_np, le_mp, hp', hsigmaT, hmp⟩ :=
      (LE_Interp.sound hP_eq W.left.fits).2 hP_in |>.out
    have AdP := ihP_inner hp' hsigmaT hmp
    by_cases hm0 : mp = .bot
    · simp only [hm0] at le_mp hmp
      cases show s = .bot from TShape.le_bot.1 (le_mp.trans TShape.bot_le')
      refine (TShape.le_bot.1 ((WShape.bot_fst ▸ le_m).trans TShape.bot_eqv.1) : m = .bot) ▸
        (LR _).bot hmem.isType ?_
      have ⟨_, _, _, le, le', iA, iv, hmA⟩ := (LE_Interp.sound hA_typ W.left.fits).2 hA |>.out
      exact (LR _).left_ty <| toValTy le le' hmem.isType iv hmA ((ihA_typ iA iv hmA).2 W.left)
    cases hsigmaT with | bot => cases hm0 hmp.bot_r | sigma hb1 hb2 hd hF le
    cases hmp.unfold with
    | bot => cases hm0 rfl
    | sort | sigma | forallE => exact (TShape.sort_not_le_sigma le).elim
    | lam _ => exact (TShape.forallE_not_le_sigma le).elim
    | pair hpair
    rename_i n_pair x_p y_p at_ bt_ wh_p
    have hAdP := (LR _).trans
      (hP_eq.subst' W.left.wf₀ W.left.toSubstEq)
      (hP_eq.hasType.2.subst' W.wf₀ W.toSubstEq)
      (AdP.2 W.left) (AdP.1 W).2
    dsimp only [LR, LRS] at hAdP
    rw [LRS.TmEq.pair_sigma] at hAdP
    obtain ⟨A₁, A₂, _, _, redA, _, _, _, _, _, _, _, hPair⟩ := hAdP
    cases WHNF.sigma.whRedS redA.2
    have hx_A : LE_Interp ρ at_.T A := hb1.mono <|
      (TShape.LE.def (Nat.le_max_left _ _) (Nat.le_max_right _ _)).2 (TShape.LE.sigma_decomp le).1
    let k := max n n_pair; have hk := Nat.max_le.1 (Nat.le_refl k)
    have hJ := TShape.Join.mk (hA.compat hx_A)
    have ⟨hJa, hJat⟩ := hJ.le
    have hmem_k := (WShape.HasType.lift hk.1).2 hmem
    have hxp_HT_k := (WShape.HasType.lift hk.2).2 hpair.2.1
    have hJat_w := (TShape.LE.def hk.2 (Nat.le_refl _)).1 hJat
    have hJ_t_W := TShape.HasType.sort_r.1 <|
      (TShape.HasType.sort_r.2 hmem.isType).join' hJ (TShape.HasType.sort_r.2 hpair.2.1.isType)
    have hJa_w' : a.lift k ≤ (a.T.join at_.T).snd := by
      simpa [WShape.lift_self] using (TShape.LE.def hk.1 (Nat.le_refl _)).1 hJa
    have hJat_w' : at_.lift k ≤ (a.T.join at_.T).snd := by simpa [WShape.lift_self] using hJat_w
    have hxp_HT_joined := hJ_t_W.mono_r hJat_w' hxp_HT_k
    refine (LR.TmEq.lift hk.1 hmem).1 <|
      (LR _).mono_r_2 hJa_w' hmem_k hJ_t_W <|
      (LR _).mono_l ((TShape.LE.def hk.1 hk.2).1 (le_m.trans (TShape.fst_mono le_mp)))
        (hJ_t_W.mono_r hJa_w' hmem_k) hxp_HT_joined <|
      (LR _).mono_r_1 hJat_w' hxp_HT_k hxp_HT_joined ?_ <|
      (LR.TmEq.lift hk.2 hpair.2.1).2 hPair.1
    have ⟨_, _, _, le_j, le_j', hAj, hSj, hmj⟩ :=
      (LE_Interp.sound hA_typ W.left.fits).2 (hA.join' hx_A) |>.out
    exact (LR _).left_ty <| toValTy le_j le_j' hJ_t_W hSj hmj ((ihA_typ hAj hSj hmj).2 W.left)
  | @sndDF Γ A u B v p p' hA_typ hB_typ hP hBfst ihA_typ ihB_typ ihP ihBfst =>
    cases hM with
    | bot => exact .bot' hBfst.hasType.1 hA hmem.isType fun h h' hm => (ihBfst h h' hm).left
    | snd hP_interp le_m
    rename_i n_s s
    refine .wf₀ fun hΓ₀ => ?_
    suffices ∀ {p p' σ σ'}, SubstWF Γ₀ σ σ' Γ ρ →
        Γ ⊢ p ≡ p' : .sigma A B →
        Γ ⊢ B.inst (.fst p) ≡ B.inst (.fst p') : .sort v →
        LE_Interp ρ (WShape.T s) p →
        LE_Interp ρ a.T (B.inst (.fst p)) →
        (∀ {n'} {mp ap : WShape n'}, LE_Interp ρ mp.T p → LE_Interp ρ ap.T (.sigma A B) →
          mp.HasType ap → Adequate Γ₀ Γ ρ p p' (.sigma A B) mp ap) →
        (∀ {n'} {mb av : WShape n'}, LE_Interp ρ mb.T (B.inst (.fst p)) →
          LE_Interp ρ av.T (.sort v) → mb.HasType av →
          Adequate Γ₀ Γ ρ (B.inst (.fst p)) (B.inst (.fst p')) (.sort v) mb av) →
        (LR hΓ₀).TmEq ((Term.snd p).subst σ) ((Term.snd p').subst σ')
          ((B.inst (.fst p)).subst σ) m a by
      refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
      · refine this W hP.hasType.1 hBfst.hasType.1 hP_interp hA ?_ ?_
        · exact fun hp hsig hT => (ihP hp hsig hT).left
        · exact fun hB hv hmb => (ihBfst hB hv hmb).left
      · refine (LR _).conv ((LR _).symm_ty ?_) <| this W hP.hasType.2 hBfst.hasType.2
          ((LE_Interp.sound hP W.fits).1.1 hP_interp)
          ((LE_Interp.sound hBfst W.fits).1.1 hA) (fun hp hsig hT => ?_) (fun hB hv hmb => ?_)
        · have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
            (LE_Interp.sound hBfst W.fits).2 hA |>.out
          exact toValTy le le' hmem.isType iv hmb ((ihBfst iB iv hmb).2 W.left)
        · exact ((ihP ((LE_Interp.sound hP W.left.fits).1.2 hp) hsig hT).symm hP).left
        · exact ((ihBfst ((LE_Interp.sound hBfst W.left.fits).1.2 hB) hv hmb).symm hBfst).left
      · exact this W hP hBfst hP_interp hA
          (fun hp hsig hT => ihP hp hsig hT) (fun hB hv hmb => ihBfst hB hv hmb)
    intro p p' σ σ' W hP_eq hBfst_eq hP_in hA' ihP_inner ihBfst_inner
    have ⟨_, mp, _, le_np, le_mp, hp', hsigmaT, hmp⟩ :=
      (LE_Interp.sound hP_eq W.left.fits).2 hP_in |>.out
    have AdP := ihP_inner hp' hsigmaT hmp
    by_cases hm0 : mp = .bot
    · simp only [hm0] at le_mp hmp
      cases show s = .bot from TShape.le_bot.1 (le_mp.trans TShape.bot_le')
      refine (TShape.le_bot.1 ((WShape.bot_snd ▸ le_m).trans TShape.bot_eqv.1) : m = .bot) ▸
        (LR _).bot hmem.isType ?_
      have ⟨_, _, _, le, le', iB, iv, hmb⟩ := (LE_Interp.sound hBfst_eq W.left.fits).2 hA' |>.out
      exact (LR _).left_ty <| toValTy le le' hmem.isType iv hmb ((ihBfst_inner iB iv hmb).2 W.left)
    cases hsigmaT with | bot => cases hm0 hmp.bot_r | sigma hb1 hb2 hd hF le
    cases hmp.unfold with
    | bot => cases hm0 rfl
    | sort | sigma | forallE => exact (TShape.sort_not_le_sigma le).elim
    | lam _ => exact (TShape.forallE_not_le_sigma le).elim
    | pair hpair
    rename_i n_pair x_p y_p at_ bt_ wh_p
    have hAdP := (LR _).trans (hP_eq.subst' W.left.wf₀ W.left.toSubstEq)
      (hP_eq.hasType.2.subst' W.wf₀ W.toSubstEq) (AdP.2 W.left) (AdP.1 W).2
    dsimp only [LR, LRS] at hAdP; rw [LRS.TmEq.pair_sigma] at hAdP
    obtain ⟨A₁, A₂, _, _, redA, _, _, _, _, _, _, _, hPair⟩ := hAdP
    cases WHNF.sigma.whRedS redA.2
    have hB_inst_LE := (LE_Interp.sigma' hb1 hb2 hd hF).mono le |>.sigma_inv.2 (LE_Interp.fst' hp')
    let k := max n n_pair; have hk := Nat.max_le.1 (Nat.le_refl k)
    have hJ := TShape.Join.mk (hA'.compat hB_inst_LE)
    have ⟨hJa, hJat⟩ := hJ.le
    have hmem_k := (WShape.HasType.lift hk.1).2 hmem
    have hpair_W := WShape.HasTypePair.def.1 hpair
    have hyp_HT_k := (WShape.HasType.lift hk.2).2 hpair_W.2.2
    have hJat_w := (TShape.LE.def hk.2 (Nat.le_refl _)).1 hJat
    have hJ_t_W := TShape.HasType.sort_r.1 <|
      (TShape.HasType.sort_r.2 hmem.isType).join' hJ (TShape.HasType.sort_r.2 hpair_W.2.2.isType)
    have hJa_w' : a.lift k ≤ (a.T.join (bt_.app x_p).T).snd := by
      simpa [WShape.lift_self] using (TShape.LE.def hk.1 (Nat.le_refl _)).1 hJa
    have hJat_w' : (bt_.app x_p).lift k ≤ (a.T.join (bt_.app x_p).T).snd := by
      simpa [WShape.lift_self] using hJat_w
    have hJj := hJ_t_W.mono_r hJat_w' hyp_HT_k
    rw [subst_inst]
    refine (LR.TmEq.lift hk.1 hmem).1 <|
      (LR _).mono_r_2 hJa_w' hmem_k hJ_t_W <|
      (LR _).mono_l ((TShape.LE.def hk.1 hk.2).1 (le_m.trans (TShape.snd_mono le_mp)))
        (hJ_t_W.mono_r hJa_w' hmem_k) hJj <|
      (LR _).mono_r_1 hJat_w' hyp_HT_k hJj ?_ <|
      (LR.TmEq.lift hk.2 hpair_W.2.2).2 hPair.2
    have ⟨_, _, _, le_j, le_j', hAj, hSj, hmj⟩ :=
      (LE_Interp.sound hBfst_eq W.left.fits).2 (hA'.join' hB_inst_LE) |>.out
    exact (LR _).left_ty <| subst_inst ▸ toValTy le_j le_j' hJ_t_W hSj hmj
      ((ihBfst_inner hAj hSj hmj).2 W.left)
  | @pair_fst Γ A u B v pa pb HA HB Ha Hb Hfst ihA ihB iha ihb ih_fst =>
    refine .wf fun hΓ => ?_
    have hRule : Γ ⊢ Term.fst (Term.pair A B pa pb) ≡ pa : A := .pair_fst₀ hΓ HB Ha Hb
    -- Single lemma applied 3x: whr-stability discharge converting TmEq pa.σ pa.σ' to TmEq M.σ N.σ'.
    suffices ∀ {M N : Term} {σ σ' : Subst} (W : LR.SubstWF Γ₀ σ σ' Γ ρ)
        (HM_eq_pa : Γ₀ ⊢ M.subst σ ≡ pa.subst σ : A.subst σ)
        (HN_eq_pa : Γ₀ ⊢ N.subst σ' ≡ pa.subst σ' : A.subst σ)
        (whrM : M.subst σ ⤳* pa.subst σ) (whrN : N.subst σ' ⤳* pa.subst σ')
        (Hsrc : Γ₀ ⊢ M.subst σ ≡ N.subst σ' : A.subst σ)
        (_h_iha : (LR W.wf₀).TmEq (pa.subst σ) (pa.subst σ') (A.subst σ) m a),
        (LR W.wf₀).TmEq (M.subst σ) (N.subst σ') (A.subst σ) m a by
      refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
      · -- M-validity: M = N = .fst (.pair A B pa pb)
        have hpa_LE := (LE_Interp.sound hRule W.fits).1.1 hM
        have HA_σσ' := HA.hasType.1.subst' W.wf₀ W.toSubstEq
        exact this W
          (hRule.subst' W.left.wf₀ W.left.toSubstEq)
          (HA_σσ'.symm.defeqDF (hRule.subst' W.symm.left.wf₀ W.symm.left.toSubstEq))
          (.tail .rfl .pair_fst) (.tail .rfl .pair_fst)
          (Hfst.subst' W.wf₀ W.toSubstEq)
          (((iha hpa_LE hA hmem).1 W).1)
      · -- N-validity: M = N = pa
        have hpa_LE := (LE_Interp.sound hRule W.fits).1.1 hM
        have HA_σσ' := HA.hasType.1.subst' W.wf₀ W.toSubstEq
        exact this W
          (Ha.subst' W.left.wf₀ W.left.toSubstEq)
          (HA_σσ'.symm.defeqDF (Ha.subst' W.symm.left.wf₀ W.symm.left.toSubstEq))
          .rfl .rfl
          (Ha.subst' W.wf₀ W.toSubstEq)
          (((iha hpa_LE hA hmem).1 W).2)
      · -- Diagonal: M = .fst (.pair A B pa pb), N = pa, σ_L = σ_R = σ
        have hpa_LE := (LE_Interp.sound hRule W.fits).1.1 hM
        exact this W
          (hRule.subst' W.wf₀ W.toSubstEq)
          (Ha.subst' W.wf₀ W.toSubstEq)
          (.tail .rfl .pair_fst) .rfl
          (hRule.subst' W.wf₀ W.toSubstEq)
          ((iha hpa_LE hA hmem).2 W)
    intro M N σ σ' W HM HN whrM whrN Hsrc h_iha
    exact ((LR _).whr ⟨HM, whrM⟩ ⟨HN, whrN⟩ Hsrc).2 h_iha
  | @pair_snd Γ A u B v pa pb HA HB Ha Hb Hsnd ihA ihB iha ihb ih_snd =>
    refine .wf fun hΓ => ?_
    have hRule : Γ ⊢ Term.snd (Term.pair A B pa pb) ≡ pb : B.inst pa := .pair_snd₀ hΓ HB Ha Hb
    -- Single lemma applied 3x: whr-stability discharge converting TmEq pb.σ pb.σ' to TmEq M.σ N.σ'.
    suffices ∀ {M N : Term} {σ σ' : Subst} (W : LR.SubstWF Γ₀ σ σ' Γ ρ)
        (HM_eq_pb : Γ₀ ⊢ M.subst σ ≡ pb.subst σ : (B.inst pa).subst σ)
        (HN_eq_pb : Γ₀ ⊢ N.subst σ' ≡ pb.subst σ' : (B.inst pa).subst σ)
        (whrM : M.subst σ ⤳* pb.subst σ) (whrN : N.subst σ' ⤳* pb.subst σ')
        (Hsrc : Γ₀ ⊢ M.subst σ ≡ N.subst σ' : (B.inst pa).subst σ)
        (_h_ihb : (LR W.wf₀).TmEq (pb.subst σ) (pb.subst σ') ((B.inst pa).subst σ) m a),
        (LR W.wf₀).TmEq (M.subst σ) (N.subst σ') ((B.inst pa).subst σ) m a by
      refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
      · -- M-validity: M = N = .snd (.pair A B pa pb)
        have hpb_LE := (LE_Interp.sound hRule W.fits).1.1 hM
        have HBinst_σσ' := (IsDefEq.inst0 W.wf Ha HB).subst' W.wf₀ W.toSubstEq
        exact this W
          (hRule.subst' W.left.wf₀ W.left.toSubstEq)
          (HBinst_σσ'.symm.defeqDF (hRule.subst' W.symm.left.wf₀ W.symm.left.toSubstEq))
          (.tail .rfl .pair_snd) (.tail .rfl .pair_snd)
          (Hsnd.subst' W.wf₀ W.toSubstEq)
          (((ihb hpb_LE hA hmem).1 W).1)
      · -- N-validity: M = N = pb
        have hpb_LE := (LE_Interp.sound hRule W.fits).1.1 hM
        have HBinst_σσ' := (IsDefEq.inst0 W.wf Ha HB).subst' W.wf₀ W.toSubstEq
        exact this W
          (Hb.subst' W.left.wf₀ W.left.toSubstEq)
          (HBinst_σσ'.symm.defeqDF (Hb.subst' W.symm.left.wf₀ W.symm.left.toSubstEq))
          .rfl .rfl
          (Hb.subst' W.wf₀ W.toSubstEq)
          (((ihb hpb_LE hA hmem).1 W).2)
      · -- Diagonal: M = .snd (.pair A B pa pb), N = pb, σ_L = σ_R = σ
        have hpb_LE := (LE_Interp.sound hRule W.fits).1.1 hM
        exact this W
          (hRule.subst' W.wf₀ W.toSubstEq)
          (Hb.subst' W.wf₀ W.toSubstEq)
          (.tail .rfl .pair_snd) .rfl
          (hRule.subst' W.wf₀ W.toSubstEq)
          ((ihb hpb_LE hA hmem).2 W)
    intro M N σ σ' W HM HN whrM whrN Hsrc h_ihb
    exact ((LR _).whr ⟨HM, whrM⟩ ⟨HN, whrN⟩ Hsrc).2 h_ihb
  | @fst_snd Γ p A B Hp Hpair ihp ihpair =>
    -- η-rule for pairs: .pair A B (.fst p) (.snd p) ≡ p : .sigma A B
    refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · exact ((ihpair hM hA hmem).1 W).1
    · exact ((ihp ((LE_Interp.sound (Hp.fst_snd₀ W.wf) W.fits).1.1 hM) hA hmem).1 W).2
    have hM' := (LE_Interp.sound (Hp.fst_snd₀ W.wf) W.fits).1.1 hM
    have hTyEq := (LR _).isType ((ihpair hM hA hmem).2 W)
    cases hmem.unfold with
    | bot hm => exact (LR _).bot hm hTyEq
    | sort => cases n <;> have .pair _ _ h := hM <;> cases TShape.sort_not_le_pair' h
    | forallE _ => have .pair _ _ h := hM; cases TShape.forallE_not_le_pair' h
    | lam _ =>
      revert hM; unfold WShape.lam'; split <;> [skip; exact fun _ => (LR _).bot hmem.isType hTyEq]
      intro | .pair _ _ h => cases TShape.lam_not_le_pair' h
    | sigma _ => have .pair _ _ h := hM; cases TShape.sigma_not_le_pair' h
    | pair hpair
    have ⟨A₁, A₂, u, v, whr_t, htA₁, vtyA₁, htA₂, hΓfM, _, htpair, edge, vpair_M⟩ :=
      (ihpair hM hA hmem).2 W
    cases WHNF.sigma.whRedS whr_t.2
    have ⟨_, _, _, _, whr_N, _, _, _, hΓfN, _, _, _, _⟩ := (ihp hM' hA hmem).2 W
    cases whr_t.2.determ .sigma whr_N.2 .sigma
    have := (Hp.fst_snd₀ W.wf).subst' W.wf₀ W.toSubstEq
    have H1 := this.fstDF₀ W.wf₀; have H2 := this.sndDF₀ W.wf₀
    exact ⟨A.subst σ, B.subst σ.lift, u, v, whr_t, htA₁, vtyA₁, htA₂, hΓfM, hΓfN, htpair, edge,
      ((LR _).whr ⟨H1.hasType.1, .rfl⟩ ⟨H1, .tail .rfl .pair_fst⟩ H1.hasType.1).1 vpair_M.1,
      ((LR _).whr ⟨H2.hasType.1, .rfl⟩ ⟨H2, .tail .rfl .pair_snd⟩ H2.hasType.1).1 vpair_M.2⟩
  | @YDF _ A A' u b b' HA Hb Hb' ihA ihb ihb' =>
    refine .fits fun W => ?_
    obtain ⟨_, m', a', le, _, ha', hmem', adq⟩ := LR.adequacy_Y W HA Hb Hb' ihA ihb hM
    refine adq.mono le hmem hmem' (hA.compat ha') (fun {σ σ'} W' => ?_)
    have ⟨_, _, _, le_n, le_a, hA0, hSort, hmem0⟩ := (LE_Interp.sound HA.hasType.1 W'.fits).2 hA |>.out
    exact LR.toValTy le_n le_a hmem.isType hSort hmem0 ((ihA hA0 hSort hmem0).1 W'.left).1
  | Y_unfold HyA Hyb Hyy Hyr ihA ihb ihy ihred =>
    refine ⟨fun _ _ W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · exact ((ihy hM hA hmem).1 W).1
    · exact ((ihred (LE_Interp.Y_iff.1 hM) hA hmem).1 W).1
    · have H := Hyy.subst' W.wf₀ W.toSubstEq
      refine ((LR _).whr ⟨H, .rfl⟩ ⟨?_, subst_inst ▸ .tail .rfl .Y⟩ H).1 ((ihy hM hA hmem).2 W)
      exact (IsDefEq.Y_unfold HyA Hyb Hyy Hyr).subst' W.wf₀ W.toSubstEq

theorem forallE_whRed_l (hΓ : ⊢ Γ) (d : Γ ⊢ A₀ ≡ Term.forallE B₁ F₁ : .sort s) :
    ∃ B₀ F₀, A₀ ⤳* .forallE B₀ F₀ ∧ ∃ u v, Γ ⊢ B₀ ≡ B₁ : .sort u ∧ B₀::Γ ⊢ F₀ ≡ F₁ : .sort v := by
  have hPi : LE_Interp .nil (WShape.T (n := 1) (.forallE .bot WShapeFun.bot)) (.forallE B₁ F₁) := by
    refine .forallE' .bot .bot (.bot <| .bot' .sort) fun _ h => ?_
    cases h.bot_r; exact WShapeFun.bot_app.symm ▸ .bot
  have hmem : WShape.HasType (n := 1) (.forallE .bot WShapeFun.bot) (.sort s) := by
    refine WShape.HasType.forallE_l.2 ⟨_, ?_, rfl⟩
    refine WShape.HasTypePi.iff.2 ⟨.bot (.bot' .sort), fun x hx => ?_⟩
    cases WShape.HasType.bot_r hx; exact WShapeFun.bot_app.symm ▸ .bot .sort
  have := LR.adequacy d ((LE_Interp.sound d .nil).1.2 hPi) (.sort TShape.sort_eqv.1) hmem
    |>.2 (.id hΓ)
  have ⟨_, _, _, _, _, _, _, _, redA₀, redPi, convB, convF, _⟩ :=
    subst_id ▸ subst_id ▸ subst_id ▸ this
  cases WHNF.forallE.whRedS redPi.2; exact ⟨_, _, redA₀.2, _, _, convB, convF⟩

/-- Pi–Pi injectivity: if two Pi types are definitionally equal,
their domains and codomains are each definitionally equal. -/
theorem forallE_inv (hΓ : ⊢ Γ)
    (H : Γ ⊢ Term.forallE A₀ B₀ ≡ Term.forallE A₁ B₁ : .sort s) :
    ∃ u v, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ A₀::Γ ⊢ B₀ ≡ B₁ : .sort v := by
  have ⟨_, _, red, H⟩ := forallE_whRed_l hΓ H
  cases WHNF.forallE.whRedS red; exact H

/-- Sort/Pi disjointness: a sort is never definitionally equal to a Pi-type.
A consequence of weak-head determinacy and the fact that `.sort u` is
already in WHNF. -/
theorem sort_forallE_inv (hΓ : ⊢ Γ) : ¬Γ ⊢ .sort u ≡ Term.forallE A₁ B₁ : .sort s :=
  fun H => have ⟨_, _, H⟩ := forallE_whRed_l hΓ H; nomatch WHNF.sort.whRedS H.1

/-- Sort injectivity: if two sorts are definitionally equal, their levels are equal. -/
theorem sort_inv (hΓ : ⊢ Γ) (d : Γ ⊢ Term.sort u ≡ Term.sort v : V) : u = v := by
  have hM : LE_Interp .nil (WShape.T (n := 1) (.sort u)) (.sort u) :=
    .sort TShape.sort_eqv.1
  have ⟨n, mU, mV, h1, h2, h3, hA, h5⟩ := (LE_Interp.sound d .nil).2 hM |>.out
  have h2' := WShape.lift_sort ▸ (TShape.LE.lift_l h1).1 h2; dsimp only at h2'
  cases WShape.sort_le.1 h2'
  cases show mV = (.sort true : WShape 1).lift n by
    let _+1 := n
    simp only [WShape.HasType, WShape.sort] at h5
    ext1; generalize mV.val = mv at h5
    let .sort := Shape.HasType.unfold_iff.1 h5; rfl
  have h1' : (1 : Nat) ≤ n := h1
  have := (LR.adequacy d hM (hA.unlift h1') .sort).2 (.id hΓ)
  have ⟨_, _, w, h1, h2⟩ := (LR _).sort_iff.1 (subst_id ▸ subst_id ▸ subst_id ▸ this)
  cases WHNF.sort.whRedS h1.2; cases WHNF.sort.whRedS h2.2; rfl
/-- Headline Σ-type whr-inversion (mirrors `forallE_whRed_l` for Π). -/
theorem sigma_whRed_l (hΓ : ⊢ Γ) (d : Γ ⊢ A₀ ≡ Term.sigma B₁ F₁ : .sort true) :
    ∃ B₀ F₀, A₀ ⤳* .sigma B₀ F₀ ∧
      ∃ u v, Γ ⊢ B₀ ≡ B₁ : .sort u ∧ B₀::Γ ⊢ F₀ ≡ F₁ : .sort v := by
  have hSigma : LE_Interp .nil (WShape.T (n := 1) (.sigma .bot WShapeFun.bot)) (.sigma B₁ F₁) := by
    refine .sigma' .bot .bot (.bot <| .bot' .sort) fun _ h => ?_
    cases h.bot_r; exact WShapeFun.bot_app.symm ▸ .bot
  have hmem : WShape.HasType (n := 1) (.sigma .bot WShapeFun.bot) .type := by
    refine WShape.HasType.sigma_l.2 ⟨?_, rfl⟩
    refine WShape.HasTypeSigma.def.2 ⟨.bot (.bot' .sort), fun x y h => ?_⟩
    exact (WShapeFun.mem_bot.1 h).2 ▸ .bot' .sort
  have := LR.adequacy d ((LE_Interp.sound d .nil).1.2 hSigma) (.sort TShape.sort_eqv.1) hmem
    |>.2 (.id hΓ)
  obtain ⟨_, _, _, _, _, _, _, _, redA₀, redS, convB, convF, _⟩ :=
    subst_id ▸ subst_id ▸ subst_id ▸ this
  cases WHNF.sigma.whRedS redS.2
  exact ⟨_, _, redA₀.2, _, _, convB, convF⟩

/-- Σ–Σ injectivity: if two Σ types are definitionally equal,
their domains and codomains are each definitionally equal. -/
theorem sigma_inv (hΓ : ⊢ Γ)
    (H : Γ ⊢ Term.sigma A₀ B₀ ≡ Term.sigma A₁ B₁ : .sort true) :
    ∃ u v, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ A₀::Γ ⊢ B₀ ≡ B₁ : .sort v := by
  have ⟨_, _, red, H⟩ := sigma_whRed_l hΓ H
  cases WHNF.sigma.whRedS red; exact H

/-- Sort/Σ disjointness: a sort is never definitionally equal to a Σ-type. -/
theorem sort_sigma_inv (hΓ : ⊢ Γ) : ¬Γ ⊢ .sort u ≡ Term.sigma A₁ B₁ : .sort true :=
  fun H => have ⟨_, _, H, _⟩ := sigma_whRed_l hΓ H; nomatch WHNF.sort.whRedS H

/-- Π/Σ disjointness: a Π-type is never definitionally equal to a Σ-type. -/
theorem forallE_sigma_inv (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.forallE A B ≡ Term.sigma A₁ B₁ : .sort true :=
  fun H => have ⟨_, _, H, _⟩ := sigma_whRed_l hΓ H; nomatch WHNF.forallE.whRedS H
