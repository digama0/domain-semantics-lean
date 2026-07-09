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

/-- Adequacy of the unit **type** former `.unit r : .sort r`. Factored out of the
`unit` case so that `star`/`unit_eta` (whose terms are always `⊥`) can feed it
as the `bot'` type-adequacy witness. -/
theorem LR.adequate_unit {Γ₀ Γ : List Term} {ρ : Valuation} {n : Nat}
    {m a : WShape n} {r : Bool}
    (hM : LE_Interp ρ m.T (.unit r)) (hA : LE_Interp ρ a.T (.sort r))
    (hmem : m.HasType a) :
    Adequate Γ₀ Γ ρ (.unit r) (.unit r) (.sort r) m a := by
  refine .wf₀ fun hΓ₀ => ?_
  suffices (LR hΓ₀).TmEq (.unit r) (.unit r) (.sort r) m a from
    ⟨fun _ _ _ => ⟨this, this⟩, fun _ _ => this⟩
  cases hmem.unfold with
  | bot hm =>
    apply (LR _).bot hm
    obtain rfl | rfl := (WShape.le_sort (s := a)).1 <|
      (TShape.LE.lift_r (Nat.zero_le _)).1 hA.le_sort
    · exact (LR _).bot_ty
    · exact .sort
  | unit h => exact ⟨r, ⟨.sort, .rfl⟩, r, ⟨.unit, .rfl⟩, ⟨.unit, .rfl⟩⟩
  | sort => cases TShape.sort_not_le_unit hM.le_unit
  | forallE => cases TShape.forallE_not_le_unit hM.le_unit
  | lam =>
    revert hM; unfold WShape.lam'
    split <;> [skip; exact fun _ => (LR _).bot hmem.isType <|
      (LR _).mono_r_2_ty hA.le_sort' hmem.isType .sort .sort]
    intro hM; cases TShape.lam_not_le_unit hM.le_unit
  | sigma => cases TShape.sigma_not_le_unit hM.le_unit
  | pair => cases TShape.pair_not_le_unit hM.le_unit
  | nat => cases TShape.nat_not_le_unit hM.le_unit
  | zero => cases TShape.zero_not_le_unit hM.le_unit
  | succ _ => cases TShape.succ_not_le_unit hM.le_unit
  | id => cases TShape.id_not_le_unit hM.le_unit
  | refl => cases TShape.refl_not_le_unit hM.le_unit

/-- Lower an `Adequate` from a witness `(m', a')` to a smaller one `(m, a)` — used to
consume the saturated invariant returned by `adequacy_Y`. `le : m.T ≤ m'.T` lowers the
term-witness; the two type-witnesses `a, a'` (both interpreting `A`, hence compatible)
are reconciled through their join. -/
theorem LR.Adequate.mono_r {Γ₀ Γ : List Term} {ρ : Valuation} {M N A : Term}
    {n n' : Nat} {m a : WShape n} {m' a' : WShape n'}
    (le : m.T ≤ m'.T) (hmem : m.HasType a) (hmem' : m'.HasType a')
    (hc : a.T.Compat a'.T)
    (hAty : ∀ {{σ σ'}} (W : LR.SubstWF Γ₀ σ σ' Γ ρ), (LR W.wf₀).TyEq (A.subst σ) (A.subst σ) a)
    (H : Adequate Γ₀ Γ ρ M N A m' a') : Adequate Γ₀ Γ ρ M N A m a := by
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
  have hJ_t' := TShape.HasType.sort_r.1 <|
    hJ_t.mono_l (TShape.lift_eqv hjk).2 (TShape.lift_eqv hjk).1
  have lower : ∀ {M0 N0 : Term} {{σ σ'}} (W : LR.SubstWF Γ₀ σ σ' Γ ρ),
      (LR W.wf₀).TmEq M0 N0 (A.subst σ) m' a' → (LR W.wf₀).TmEq M0 N0 (A.subst σ) m a := by
    intro M0 N0 σ σ' W hv
    have ha_kty : (WShape.lift (max n n') a).HasType .type := by
      simpa using (WShape.HasType.lift hkn).2 hmem.isType
    have ha'_kty : (WShape.lift (max n n') a').HasType .type := by
      simpa using (WShape.HasType.lift hkn').2 hmem'.isType
    have tyJ := (LR _).join_ty ((TShape.Compat.def hkn hkn').2 hc) ha_kty ha'_kty
      ((TyEq.lift hkn hmem.isType).2 (hAty W))
      ((TyEq.lift hkn' hmem'.isType).2 ((LR W.wf₀).isType hv))
    have tyJ' : (LR W.wf₀).TyEq (A.subst σ) (A.subst σ) ((a.T.join a'.T).snd.lift (max n n')) :=
      WShape.lift_self ▸ tyJ
    refine (LR.TmEq.lift hkn hmem).1 <| (LR _).mono_r_2 hJ1' hmem_k hJ_t' <|
      (LR _).mono_l ((TShape.LE.def hkn hkn').1 le) (.mono_r hJ1' hJ_t' hmem_k)
        (.mono_r hJ2' hJ_t' hmem'_k) <|
      (LR _).mono_r_1 hJ2' hmem'_k (.mono_r hJ2' hJ_t' hmem'_k) tyJ' <|
        (LR.TmEq.lift hkn' hmem').2 hv
  exact ⟨fun σ σ' W => ⟨lower W (H.1 W).1, lower W (H.1 W).2⟩, fun σ W => lower W (H.2 W)⟩

theorem LR.Adequate.nat {m a : WShape n}
    (hM : LE_Interp ρ m.T .nat) (hA : LE_Interp ρ a.T (.sort true))
    (hmem : m.HasType a) : Adequate Γ₀ Γ ρ .nat .nat (.sort true) m a := by
  refine .wf₀ fun hΓ₀ => ?_
  suffices (LR hΓ₀).TmEq .nat .nat (.sort true) m a from
    ⟨fun _ _ _ => ⟨this, this⟩, fun _ _ => this⟩
  cases hmem.unfold with
  | bot hm =>
    apply (LR _).bot hm
    obtain rfl | rfl := (WShape.le_sort (s := a)).1 <|
      (TShape.LE.lift_r (Nat.zero_le _)).1 hA.le_sort
    · exact (LR _).bot_ty
    · exact .sort
  | sort => cases n <;> (have .nat h := hM; exact (TShape.sort_not_le_nat h).elim)
  | unit => have .nat h := hM; exact (TShape.unit_not_le_nat h).elim
  | forallE => have .nat h := hM; exact (TShape.forallE_not_le_nat h).elim
  | sigma => have .nat h := hM; exact (TShape.sigma_not_le_nat h).elim
  | nat => exact ⟨true, ⟨.sort, .rfl⟩, ⟨.nat, .rfl⟩, ⟨.nat, .rfl⟩⟩
  | id => have .nat h := hM; exact (TShape.id_not_le_nat h).elim
  | refl => have .nat h := hM; exact (TShape.refl_not_le_nat h).elim
  | _ => obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := WShape.le_sort.1 <| (TShape.LE.lift_r (Nat.zero_le _)).1 hA.le_sort

theorem LR.TmEq.mono_r {Γ₀ : List Term} {hΓ₀ : ⊢ Γ₀} {Aσ M N : Term}
    {n n' : Nat} {m a : WShape n} {m' a' : WShape n'}
    (le : m.T ≤ m'.T) (hmem : m.HasType a) (hmem' : m'.HasType a')
    (hc : a.T.Compat a'.T)
    (hAty : (LR hΓ₀).TyEq Aσ Aσ a)
    (hv : (LR hΓ₀).TmEq M N Aσ m' a') : (LR hΓ₀).TmEq M N Aσ m a := by
  have hJ := TShape.Join.mk hc
  have ⟨hJ1, hJ2⟩ := (hJ _).1 .rfl
  have hkn : n ≤ max n n' := Nat.le_max_left ..
  have hkn' : n' ≤ max n n' := Nat.le_max_right ..
  have hjk : (a.T.join a'.T).1 ≤ max n n' := Nat.max_le.2 ⟨hkn, hkn'⟩
  have hJ1' := (TShape.LE.def hkn hjk).1 hJ1
  have hJ2' := (TShape.LE.def hkn' hjk).1 hJ2
  have hJ_t := (TShape.HasType.sort_r.2 hmem.isType).join' hJ (TShape.HasType.sort_r.2 hmem'.isType)
  have hmem_k := (WShape.HasType.lift hkn).2 hmem
  have hmem'_k := (WShape.HasType.lift hkn').2 hmem'
  have hJ_t' := TShape.HasType.sort_r.1 <|
    hJ_t.mono_l (TShape.lift_eqv hjk).2 (TShape.lift_eqv hjk).1
  have ha_kty : (WShape.lift (max n n') a).HasType .type := by
    simpa using (WShape.HasType.lift hkn).2 hmem.isType
  have ha'_kty : (WShape.lift (max n n') a').HasType .type := by
    simpa using (WShape.HasType.lift hkn').2 hmem'.isType
  have tyJ := (LR _).join_ty ((TShape.Compat.def hkn hkn').2 hc) ha_kty ha'_kty
    ((TyEq.lift hkn hmem.isType).2 hAty) ((TyEq.lift hkn' hmem'.isType).2 ((LR hΓ₀).isType hv))
  have tyJ' : (LR hΓ₀).TyEq Aσ Aσ ((a.T.join a'.T).snd.lift (max n n')) :=
    WShape.lift_self ▸ tyJ
  refine (LR.TmEq.lift hkn hmem).1 <| (LR _).mono_r_2 hJ1' hmem_k hJ_t' <|
    (LR _).mono_l ((TShape.LE.def hkn hkn').1 le) (.mono_r hJ1' hJ_t' hmem_k)
      (.mono_r hJ2' hJ_t' hmem'_k) <|
    (LR _).mono_r_1 hJ2' hmem'_k (.mono_r hJ2' hJ_t' hmem'_k) tyJ' <|
      (LR.TmEq.lift hkn' hmem').2 hv

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
  · have redY {C c τ} : (Term.Y C c).subst τ ⤳* c.subst (τ.cons ((Term.Y C c).subst τ)) :=
      inst_lift_cons ▸ .tail .rfl .Y
    have hYYL := ((IsDefEq.YDF HA Hb Hb').hasType.1).subst' W.wf₀ W.toSubstEq
    have hAss : Γ₀ ⊢ A.subst σ ≡ A.subst σ' : .sort u := (HA.hasType.1).subst' W.wf₀ W.toSubstEq
    have unfoldL1 : Γ₀ ⊢ (Term.Y A b).subst σ ≡
        b.subst (σ.cons ((Term.Y A b).subst σ)) : A.subst σ := by
      have h := (IsDefEq.Y_unfold₀ W.wf HA.hasType.1 Hb.hasType.1).subst' W.wf₀ W.left.toSubstEq
      rwa [subst_inst, inst_lift_cons] at h
    have unfoldL2 : Γ₀ ⊢ (Term.Y A b).subst σ' ≡
        b.subst (σ'.cons ((Term.Y A b).subst σ')) : A.subst σ := by
      have h := IsDefEq.Y_unfold₀ W.wf HA.hasType.1 Hb.hasType.1
        |>.subst' W.wf₀ W.symm.left.toSubstEq
      rw [subst_inst, inst_lift_cons] at h
      exact hAss.symm.defeqDF h
    refine ((LR _).whr ⟨unfoldL1, redY⟩ ⟨unfoldL2, redY⟩ hYYL).2 ?_
    have W_LL := LR.Adequate.cons ihA HA a4 a3 hYYL (a5.1 W).1 W
    exact (lift_subst_cons (e := A)) ▸ (hAdq.1 W_LL).1
  · -- (2) reflexive RHS: `A'.Y b'` across `σ`/`σ'`, via `hAdq`'s `b'` component + the reflexive
    -- self `(a5.1 W).2` threaded via `Adequate.cons` (head `A'.Y b'`).
    have redY {C c τ} : (Term.Y C c).subst τ ⤳* c.subst (τ.cons ((Term.Y C c).subst τ)) :=
      inst_lift_cons ▸ .tail .rfl .Y
    have hYYR := ((IsDefEq.YDF HA Hb Hb').hasType.2).subst' W.wf₀ W.toSubstEq
    have hAss : Γ₀ ⊢ A.subst σ ≡ A.subst σ' : .sort u := (HA.hasType.1).subst' W.wf₀ W.toSubstEq
    have unfoldR1 : Γ₀ ⊢ (Term.Y A' b').subst σ ≡
        b'.subst (σ.cons ((Term.Y A' b').subst σ)) : A.subst σ := by
      have h := (IsDefEq.Y_unfold₀ W.wf HA.hasType.2 Hb'.hasType.2).subst' W.wf₀ W.left.toSubstEq
      rw [subst_inst, inst_lift_cons] at h
      exact (HA.subst' W.wf₀ W.left.toSubstEq).symm.defeqDF h
    have unfoldR2 : Γ₀ ⊢ (Term.Y A' b').subst σ' ≡
        b'.subst (σ'.cons ((Term.Y A' b').subst σ')) : A.subst σ := by
      have h := IsDefEq.Y_unfold₀ W.wf HA.hasType.2 Hb'.hasType.2
        |>.subst' W.wf₀ W.symm.left.toSubstEq
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
    have unfoldL : Γ₀ ⊢ (Term.Y A b).subst σ ≡
        b.subst (σ.cons ((Term.Y A b).subst σ)) : A.subst σ := by
      have h := (IsDefEq.Y_unfold₀ W.wf HA.hasType.1 Hb.hasType.1).subst' W.wf₀ W.toSubstEq
      rwa [subst_inst, inst_lift_cons] at h
    have unfoldR : Γ₀ ⊢ (Term.Y A' b').subst σ ≡
        b'.subst (σ.cons ((Term.Y A' b').subst σ)) : A.subst σ := by
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
          WShape.lam', WShape.lam, WShape.bot, Shape.bot, WShape.sigma, WShape.pair,
          WShape.nat, Shape.nat, WShape.zero, Shape.zero, WShape.succ, Shape.succ,
          WShape.unit, WShape.id, WShape.refl, Shape.refl] at h <;>
        first | split at h <;> simp_all only [reduceCtorEq] | simp_all
  | @unit Γ r => exact LR.adequate_unit hM hA hmem
  | @star Γ r =>
    cases hM with
    | bot => exact .bot' .unit hA hmem.isType fun h h' hm => LR.adequate_unit h h' hm
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
        · have ⟨_, _, _, le, le', iB, iv, hmb⟩ := (LE_Interp.sound HBa W.fits).2 hA |>.out
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
    | sort | unit | forallE | sigma | nat | id => exact (TShape.sort_not_le_forallE le).elim
    | pair => exact (TShape.sigma_not_le_forallE le).elim
    | zero | succ => exact (TShape.nat_not_le_forallE le).elim
    | refl => exact (TShape.id_not_le_forallE le).elim
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
        | unit => let .forallE _ _ _ _ le := hA; exact (TShape.unit_not_le_forallE le).elim
        | sigma => let .forallE _ _ _ _ le := hA; exact (TShape.sigma_not_le_forallE le).elim
        | nat => let .forallE _ _ _ _ le := hA; exact (TShape.nat_not_le_forallE le).elim
        | id => let .forallE _ _ _ _ le := hA; exact (TShape.id_not_le_forallE le).elim
      | sort => cases n <;> let .lam _ _ _ h := hTerm <;> cases TShape.sort_not_le_lam' h
      | unit => let .lam _ _ _ h := hTerm <;> cases TShape.unit_not_le_lam' h
      | forallE => let .lam _ _ _ h := hTerm <;> cases TShape.forallE_not_le_lam' h
      | lam => exact this _ _ _ rfl .rfl
      | sigma => let .lam _ _ _ h := hTerm <;> cases TShape.sigma_not_le_lam' h
      | pair => let .lam _ _ _ h := hTerm <;> cases TShape.pair_not_le_lam' h
      | nat => let .lam _ _ _ h := hTerm; exact (TShape.nat_not_le_lam' h).elim
      | zero => let .lam _ _ _ h := hTerm; exact (TShape.zero_not_le_lam' h).elim
      | succ _ => let .lam _ _ _ h := hTerm; exact (TShape.succ_not_le_lam' h).elim
      | id => let .lam _ _ _ h := hTerm <;> cases TShape.id_not_le_lam' h
      | refl => let .lam _ _ _ h := hTerm <;> cases TShape.refl_not_le_lam' h
    rintro k a₁ a₂ rfl ⟨⟩
    have ⟨_, aty, _⟩ := WShape.HasType.forallE_l.1 hmem.isType
    have hTypA : Γ₀ ⊢ A.subst σ : .sort u :=
      HA.hasType.1.subst' W.wf₀ W.left.toSubstEq
    have hΓS : ⊢ A.subst σ :: Γ₀ :=
      ⟨W.wf₀, _, hTypA⟩
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
    | nat => have .forallE _ _ _ _ h := hM; exact (TShape.nat_not_le_forallE h).elim
    | zero => have .forallE _ _ _ _ h := hM; exact (TShape.zero_not_le_forallE h).elim
    | succ _ => have .forallE _ _ _ _ h := hM; exact (TShape.succ_not_le_forallE h).elim
    | unit => have .forallE _ _ _ _ h := hM; cases TShape.unit_not_le_forallE h
    | id => have .forallE _ _ _ _ h := hM; cases TShape.id_not_le_forallE h
    | refl => have .forallE _ _ _ _ h := hM; cases TShape.refl_not_le_forallE h
    | @forallE k a₂ a₁ r aty
    refine .wf₀ fun hΓ₀ => ?_
    have aty := WShape.HasTypePi.iff.1 aty
    have hA1 := hM.forallE_inv.1
    have cons := Adequate.cons (hΓ₀ := hΓ₀) ihA HA
    refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩ <;> (
      have ⟨_, a', _, le_n, le_a, hA', hSort, hmem'⟩ :=
        (LE_Interp.sound HA W.left.fits).2 hA1 |>.out
      have HAAσ := HA.subst' W.wf₀ W.left.toSubstEq
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
    | id => let .lam _ _ _ h := hM; cases TShape.id_not_le_lam' h
    | refl => let .lam _ _ _ h := hM; cases TShape.refl_not_le_lam' h
    | bot hm => exact (LR _).bot hm <| (LR _).isType ((ihlam hM hA hmem).2 W)
    | sort => cases n <;> let .lam _ _ _ h := hM <;> cases TShape.sort_not_le_lam' h
    | forallE => let .lam _ _ _ h := hM; cases TShape.forallE_not_le_lam' h
    | sigma => let .lam _ _ _ h := hM <;> cases TShape.sigma_not_le_lam' h
    | pair => let .lam _ _ _ h := hM <;> cases TShape.pair_not_le_lam' h
    | nat => let .lam _ _ _ h := hM; exact (TShape.nat_not_le_lam' h).elim
    | zero => let .lam _ _ _ h := hM; exact (TShape.zero_not_le_lam' h).elim
    | succ _ => let .lam _ _ _ h := hM; exact (TShape.succ_not_le_lam' h).elim
    | unit => let .lam _ _ _ h := hM <;> cases TShape.unit_not_le_lam' h
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
  | @unit_eta Γ e r He ihe =>
    let .bot := hM
    exact .bot' .unit hA hmem.isType fun h h' hm => LR.adequate_unit h h' hm
  | @idDF Γ A A' u a a' b b' HA Ha Hb ihA iha ihb =>
    cases hmem.unfold with
    | bot hm =>
      refine .bot (fun _ _ => ?_) hm
      obtain rfl | rfl := (WShape.le_sort (s := a)).1 <|
        (TShape.LE.lift_r (Nat.zero_le _)).1 hA.le_sort
      · exact (LR _).bot_ty
      · exact .sort
    | sort => cases n <;> have .id _ _ _ h := hM <;> cases TShape.sort_not_le_id h
    | forallE => have .id _ _ _ h := hM; cases TShape.forallE_not_le_id h
    | sigma => have .id _ _ _ h := hM; cases TShape.sigma_not_le_id h
    | pair => have .id _ _ _ h := hM; cases TShape.pair_not_le_id h
    | refl => have .id _ _ _ h := hM; cases TShape.refl_not_le_id h
    | unit => have .id _ _ _ h := hM; cases TShape.unit_not_le_id h
    | nat => have .id _ _ _ h := hM; cases TShape.nat_not_le_id h
    | zero => have .id _ _ _ h := hM; cases TShape.zero_not_le_id h
    | succ _ => have .id _ _ _ h := hM; cases TShape.succ_not_le_id h
    | @lam _ f₀ =>
      revert hM; unfold WShape.lam'
      split <;> [skip; exact fun _ => .bot
        (fun _ _ => (LR _).mono_r_2_ty hA.le_sort' hmem.isType .sort .sort) hmem.isType]
      intro | .id _ _ _ h => cases TShape.lam_not_le_id h
    | @id _ A_v a_v b_v hi
    refine .wf₀ fun hΓ₀ => ?_
    obtain ⟨haV_AV, hbV_AV⟩ : WShape.HasTypeId _ _ _ := hi
    have ⟨hM_AV, hM_aV, hM_bV⟩ := hM.id_inv
    refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · refine ⟨true, ⟨.sort, .rfl⟩, A.subst σ, a.subst σ, b.subst σ,
        A.subst σ', a.subst σ', b.subst σ', u, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact ⟨(HA.hasType.1.idDF Ha.hasType.1 Hb.hasType.1).subst' W.wf₀ W.left.toSubstEq, .rfl⟩
      · exact ⟨(HA.hasType.1.idDF Ha.hasType.1 Hb.hasType.1).subst' W.symm.left.wf₀
          W.symm.left.toSubstEq, .rfl⟩
      · exact HA.hasType.1.subst' W.wf₀ W.toSubstEq
      · exact Ha.hasType.1.subst' W.wf₀ W.toSubstEq
      · exact Hb.hasType.1.subst' W.wf₀ W.toSubstEq
      · have ⟨_, _, _, le_n, le_a, iA, iv, hmA⟩ := (LE_Interp.sound HA W.left.fits).2 hM_AV |>.out
        exact toValTy le_n le_a haV_AV.isType iv hmA ((ihA iA iv hmA).1 W).1
      · exact ((iha hM_aV hM_AV haV_AV).1 W).1
      · exact ((ihb hM_bV hM_AV hbV_AV).1 W).1
    · refine ⟨true, ⟨.sort, .rfl⟩, A'.subst σ, a'.subst σ, b'.subst σ,
        A'.subst σ', a'.subst σ', b'.subst σ', u, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact ⟨(HA.hasType.2.idDF (HA.defeqDF Ha).hasType.2 (HA.defeqDF Hb).hasType.2).subst'
                W.wf₀ W.left.toSubstEq, .rfl⟩
      · exact ⟨(HA.hasType.2.idDF (HA.defeqDF Ha).hasType.2 (HA.defeqDF Hb).hasType.2).subst'
                W.symm.left.wf₀ W.symm.left.toSubstEq, .rfl⟩
      · exact HA.hasType.2.subst' W.wf₀ W.toSubstEq
      · exact (HA.defeqDF Ha).hasType.2.subst' W.wf₀ W.toSubstEq
      · exact (HA.defeqDF Hb).hasType.2.subst' W.wf₀ W.toSubstEq
      · have ⟨_, _, _, le_n, le_a, iA, iv, hmA⟩ := (LE_Interp.sound HA W.left.fits).2 hM_AV |>.out
        exact toValTy le_n le_a haV_AV.isType iv hmA ((ihA iA iv hmA).1 W).2
      · have hTyEq_diag : (LR hΓ₀).TyEq (A.subst σ) (A'.subst σ) A_v := by
          have ⟨_, _, _, le_n, le_a, iA, iv, hmA⟩ := (LE_Interp.sound HA W.left.fits).2 hM_AV |>.out
          exact toValTy le_n le_a haV_AV.isType iv hmA ((ihA iA iv hmA).2 W.left)
        exact (LR _).conv hTyEq_diag ((iha hM_aV hM_AV haV_AV).1 W).2
      · have hTyEq_diag : (LR hΓ₀).TyEq (A.subst σ) (A'.subst σ) A_v := by
          have ⟨_, _, _, le_n, le_a, iA, iv, hmA⟩ := (LE_Interp.sound HA W.left.fits).2 hM_AV |>.out
          exact toValTy le_n le_a haV_AV.isType iv hmA ((ihA iA iv hmA).2 W.left)
        exact (LR _).conv hTyEq_diag ((ihb hM_bV hM_AV hbV_AV).1 W).2
    · refine ⟨true, ⟨.sort, .rfl⟩, A.subst σ, a.subst σ, b.subst σ,
        A'.subst σ, a'.subst σ, b'.subst σ, u, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact ⟨(HA.hasType.1.idDF Ha.hasType.1 Hb.hasType.1).subst' W.wf₀ W.toSubstEq, .rfl⟩
      · exact ⟨(HA.hasType.2.idDF (HA.defeqDF Ha).hasType.2 (HA.defeqDF Hb).hasType.2).subst'
          W.wf₀ W.toSubstEq, .rfl⟩
      · exact HA.subst' W.wf₀ W.toSubstEq
      · exact Ha.subst' W.wf₀ W.toSubstEq
      · exact Hb.subst' W.wf₀ W.toSubstEq
      · have ⟨_, _, _, le_n, le_a, iA, iv, hmA⟩ := (LE_Interp.sound HA W.left.fits).2 hM_AV |>.out
        exact toValTy le_n le_a haV_AV.isType iv hmA ((ihA iA iv hmA).2 W)
      · exact (iha hM_aV hM_AV haV_AV).2 W
      · exact (ihb hM_bV hM_AV hbV_AV).2 W
  | @reflDF Γ A_ty u a_tm a' HA Ha HId ihA iha ihid =>
    cases hmem.unfold with
    | bot _ => exact LR.Adequate.bot' HId hA hmem.isType ihid
    | sort => cases n <;> have .refl _ h := hM <;> cases TShape.sort_not_le_refl h
    | forallE => have .refl _ h := hM; cases TShape.forallE_not_le_refl h
    | sigma => have .refl _ h := hM; cases TShape.sigma_not_le_refl h
    | pair => have .refl _ h := hM; cases TShape.pair_not_le_refl h
    | id => have .refl _ h := hM; cases TShape.id_not_le_refl h
    | unit => have .refl _ h := hM; cases TShape.unit_not_le_refl h
    | nat => have .refl _ h := hM; cases TShape.nat_not_le_refl h
    | zero => have .refl _ h := hM; cases TShape.zero_not_le_refl h
    | succ _ => have .refl _ h := hM; cases TShape.succ_not_le_refl h
    | @lam _ f₀ =>
      revert hM; unfold WShape.lam'
      split <;> [skip; exact fun _ => LR.Adequate.bot' HId hA hmem.isType ihid]
      intro | .refl _ h => exact (TShape.lam_not_le_refl h).elim
    | refl hr
    rename_i v_outer A_v a_v b_v
    refine .wf₀ fun hΓ₀ => ?_
    have ⟨hA_AV, hA_aV, hA_bV⟩ := hA.id_inv
    obtain ⟨⟨haV_AV, hbV_AV⟩, hw_typed, hw_le_a, hw_le_b⟩ := hr
    refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · refine ⟨A_ty.subst σ, a_tm.subst σ, a_tm.subst σ, ?_, ?_, ?_, ?_,
      ⟨⟨haV_AV, hbV_AV⟩, hw_typed, hw_le_a, hw_le_b⟩, ?_⟩
      · exact ⟨HId.subst' W.wf₀ W.left.toSubstEq, .rfl⟩
      · have ⟨_, _, _, le_n, le_a, iA, iv, hmA⟩ := (LE_Interp.sound HA W.left.fits).2 hA_AV |>.out
        exact (LR _).left_ty <| toValTy le_n le_a haV_AV.isType iv hmA ((ihA iA iv hmA).2 W.left)
      · exact (LR _).left ((iha hA_aV hA_AV haV_AV).2 W.left)
      · exact (LR _).left ((iha hA_bV hA_AV hbV_AV).2 W.left)
      refine ⟨a_tm.subst σ, a_tm.subst σ', ?_, ?_,
        Ha.hasType.1.subst' W.wf₀ W.left.toSubstEq,
        Ha.hasType.1.subst' W.wf₀ W.left.toSubstEq,
        Ha.hasType.1.subst' W.wf₀ W.toSubstEq,
        (LR _).mono_l hw_le_a hw_typed haV_AV ((LR _).left ((iha hA_aV hA_AV haV_AV).2 W.left)),
        (LR _).mono_l hw_le_b hw_typed hbV_AV ((LR _).left ((iha hA_bV hA_AV hbV_AV).2 W.left)),
        (LR _).mono_l hw_le_a hw_typed haV_AV ((iha hA_aV hA_AV haV_AV).1 W).1⟩
      · refine ⟨?_, .rfl⟩
        exact (Ha.hasType.1.reflDF₀ W.wf).subst' W.wf₀ W.left.toSubstEq
      · refine ⟨?_, .rfl⟩
        have h_at_σ' : Γ₀ ⊢ (Term.refl a_tm).subst σ' ≡ (Term.refl a_tm).subst σ' :
            (Term.id A_ty a_tm a_tm).subst σ' :=
          (Ha.hasType.1.reflDF₀ W.wf).subst' W.symm.left.wf₀ W.symm.left.toSubstEq
        have h_id_subst : Γ₀ ⊢ (Term.id A_ty a_tm a_tm).subst σ ≡
            (Term.id A_ty a_tm a_tm).subst σ' : .sort true :=
          HId.subst' W.wf₀ W.toSubstEq
        exact h_id_subst.symm.defeqDF h_at_σ'
    · refine ⟨A_ty.subst σ, a_tm.subst σ, a_tm.subst σ, ?_, ?_, ?_, ?_,
      ⟨⟨haV_AV, hbV_AV⟩, hw_typed, hw_le_a, hw_le_b⟩, ?_⟩
      · exact ⟨HId.subst' W.wf₀ W.left.toSubstEq, .rfl⟩
      · have ⟨_, _, _, le_n, le_a, iA, iv, hmA⟩ := (LE_Interp.sound HA W.left.fits).2 hA_AV |>.out
        exact (LR _).left_ty <| toValTy le_n le_a haV_AV.isType iv hmA ((ihA iA iv hmA).2 W.left)
      · exact (LR _).left ((iha hA_aV hA_AV haV_AV).2 W.left)
      · exact (LR _).left ((iha hA_bV hA_AV hbV_AV).2 W.left)
      refine ⟨a'.subst σ, a'.subst σ', ?_, ?_,
        Ha.symm.subst' W.wf₀ W.left.toSubstEq,
        Ha.symm.subst' W.wf₀ W.left.toSubstEq,
        Ha.hasType.2.subst' W.wf₀ W.toSubstEq,
        (LR _).mono_l hw_le_a hw_typed haV_AV (((iha hA_aV hA_AV haV_AV).symm Ha).2 W.left),
        (LR _).mono_l hw_le_b hw_typed hbV_AV (((iha hA_bV hA_AV hbV_AV).symm Ha).2 W.left),
        (LR _).mono_l hw_le_a hw_typed haV_AV ((iha hA_aV hA_AV haV_AV).1 W).2⟩
      · refine ⟨?_, .rfl⟩
        have h_a'_self : Γ ⊢ Term.refl a' ≡ Term.refl a' : Term.id A_ty a' a' :=
          Ha.hasType.2.reflDF₀ W.wf
        have h_id_eq : Γ ⊢ Term.id A_ty a' a' ≡ Term.id A_ty a_tm a_tm : .sort true :=
          HA.hasType.1.idDF Ha.symm Ha.symm
        exact (h_id_eq.defeqDF h_a'_self).subst' W.wf₀ W.left.toSubstEq
      · refine ⟨?_, .rfl⟩
        have h_a'_self : Γ ⊢ Term.refl a' ≡ Term.refl a' : Term.id A_ty a' a' :=
          Ha.hasType.2.reflDF₀ W.wf
        have h_id_eq : Γ ⊢ Term.id A_ty a' a' ≡ Term.id A_ty a_tm a_tm : .sort true :=
          HA.hasType.1.idDF Ha.symm Ha.symm
        have h_at_σ' : Γ₀ ⊢ (Term.refl a').subst σ' ≡ (Term.refl a').subst σ' :
            (Term.id A_ty a_tm a_tm).subst σ' :=
          (h_id_eq.defeqDF h_a'_self).subst' W.symm.left.wf₀ W.symm.left.toSubstEq
        have h_id_subst : Γ₀ ⊢ (Term.id A_ty a_tm a_tm).subst σ ≡
            (Term.id A_ty a_tm a_tm).subst σ' : .sort true :=
          HId.subst' W.wf₀ W.toSubstEq
        exact h_id_subst.symm.defeqDF h_at_σ'
    · refine ⟨A_ty.subst σ, a_tm.subst σ, a_tm.subst σ, ?_, ?_, ?_, ?_,
      ⟨⟨haV_AV, hbV_AV⟩, hw_typed, hw_le_a, hw_le_b⟩, ?_⟩
      · exact ⟨HId.subst' W.wf₀ W.toSubstEq, .rfl⟩
      · have ⟨_, _, _, le_n, le_a, iA, iv, hmA⟩ := (LE_Interp.sound HA W.left.fits).2 hA_AV |>.out
        exact (LR _).left_ty <| toValTy le_n le_a haV_AV.isType iv hmA ((ihA iA iv hmA).2 W.left)
      · exact (LR _).left ((iha hA_aV hA_AV haV_AV).2 W.left)
      · exact (LR _).left ((iha hA_bV hA_AV hbV_AV).2 W.left)
      refine ⟨a_tm.subst σ, a'.subst σ, ?_, ?_,
        Ha.hasType.1.subst' W.wf₀ W.toSubstEq,
        Ha.hasType.1.subst' W.wf₀ W.toSubstEq,
        Ha.subst' W.wf₀ W.toSubstEq,
        (LR _).mono_l hw_le_a hw_typed haV_AV ((LR _).left ((iha hA_aV hA_AV haV_AV).2 W.left)),
        (LR _).mono_l hw_le_b hw_typed hbV_AV ((LR _).left ((iha hA_bV hA_AV hbV_AV).2 W.left)),
        (LR _).mono_l hw_le_a hw_typed haV_AV ((iha hA_aV hA_AV haV_AV).2 W)⟩
      · refine ⟨?_, .rfl⟩
        exact (Ha.hasType.1.reflDF₀ W.wf).subst' W.wf₀ W.toSubstEq
      · refine ⟨?_, .rfl⟩
        have h_a'_self : Γ ⊢ Term.refl a' ≡ Term.refl a' : Term.id A_ty a' a' :=
          Ha.hasType.2.reflDF₀ W.wf
        have h_id_eq : Γ ⊢ Term.id A_ty a' a' ≡ Term.id A_ty a_tm a_tm : .sort true :=
          HA.hasType.1.idDF Ha.symm Ha.symm
        exact (h_id_eq.defeqDF h_a'_self).subst' W.wf₀ W.toSubstEq
  | @trDF Γ T T' u A A' B B' C C' v X X' H H' HT HA HB HC HC' HX HH HCb H_idAab
      ihA iha ihb ihC ihC' ihx ihh ihCb ih_idAab =>
    by_cases hm : m ≤ .bot
    · cases WShape.le_bot.1 hm
      exact .bot' HCb.hasType.1 hA hmem.isType fun hM' hA' hmem' => (ihCb hM' hA' hmem').left
    cases hM with | bot => cases hm .rfl | tr le_m hx_m hva hvb hvA hv_ty_vA hc_C hty hH_refl
    rename_i vb vA m' a_ty
    refine .wf₀ fun hΓ₀ => ?_
    have h_vbvA :=
      (TShape.HasType.def (Nat.le_max_left vb.1 vA.1) (Nat.le_max_right vb.1 vA.1)).1 hv_ty_vA
    have hH_refl' : LE_Interp ρ (WShape.refl (vb.snd.lift (max vb.1 vA.1))).T H :=
      WShape.lift_refl (Nat.le_max_left vb.1 vA.1) ▸
        hH_refl.lift (Nat.succ_le_succ (Nat.le_max_left vb.1 vA.1))
    have aH := ihh hH_refl'
      (.id (hvA.lift (Nat.le_max_right vb.1 vA.1)) (hva.lift (Nat.le_max_left vb.1 vA.1))
        (hvb.lift (Nat.le_max_left vb.1 vA.1)) .rfl)
      (Shape.HasType.refl ⟨⟨h_vbvA, h_vbvA⟩, h_vbvA, Shape.LE.rfl, Shape.LE.rfl⟩)
    have hA_CinstA : LE_Interp ρ _ (C.inst A) := LE_Interp.inst.2 ⟨_, hc_C, hva⟩
    have hAc := hA.compat (LE_Interp.inst.2 ⟨_, hc_C, hvb⟩)
    have aX_wit := ihx (hx_m.lift (Nat.le_max_left m'.1 a_ty.1))
      (hA_CinstA.lift (Nat.le_max_right m'.1 a_ty.1))
      ((TShape.HasType.def (Nat.le_max_left m'.1 a_ty.1) (Nat.le_max_right m'.1 a_ty.1)).1 hty)
    suffices ∀ {T₁ A₁ B₁ C₁ X₁ H₁ T₂ A₂ B₂ C₂ X₂ H₂ σ₁ σ₂},
        Γ ⊢ T ≡ T₁ : .sort u → Γ ⊢ T ≡ T₂ : .sort u →
        Γ ⊢ A ≡ A₁ : T → Γ ⊢ A ≡ A₂ : T →
        Γ ⊢ B ≡ B₁ : T → Γ ⊢ B ≡ B₂ : T →
        T::Γ ⊢ C ≡ C₁ : .sort v → T::Γ ⊢ C ≡ C₂ : .sort v →
        Γ ⊢ X₁ ≡ X₂ : C.inst A →
        Γ ⊢ H₁ ≡ H₂ : T.id A B →
        (W : SubstWF Γ₀ σ₁ σ₂ Γ ρ) →
        (LR hΓ₀).TmEq (X₁.subst σ₁) (X₂.subst σ₂) ((C.inst A).subst σ₁)
          (WShape.lift (max m'.1 a_ty.1) m'.snd) (WShape.lift (max m'.1 a_ty.1) a_ty.snd) →
        (LR hΓ₀).TmEq (H₁.subst σ₁) (H₂.subst σ₂)
          ((T.id A B).subst σ₁) (.refl (vb.snd.lift (max vb.1 vA.1)))
          (.id (vA.snd.lift (max vb.1 vA.1))
            (vb.snd.lift (max vb.1 vA.1)) (vb.snd.lift (max vb.1 vA.1))) →
        (LR hΓ₀).TmEq ((T₁.tr A₁ B₁ C₁ X₁ H₁).subst σ₁) ((T₂.tr A₂ B₂ C₂ X₂ H₂).subst σ₂)
          ((C.inst B).subst σ₁) m a by
      refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
      · exact this HT.hasType.1 HT.hasType.1 HA.hasType.1 HA.hasType.1 HB.hasType.1 HB.hasType.1
          HC.hasType.1 HC.hasType.1 HX.hasType.1 HH.hasType.1 W (aX_wit.1 W).1 (aH.1 W).1
      · exact this HT HT HA HA HB HB HC HC HX.hasType.2 HH.hasType.2 W (aX_wit.1 W).2 (aH.1 W).2
      · exact this HT.hasType.1 HT HA.hasType.1 HA HB.hasType.1 HB HC.hasType.1 HC HX HH W
          (aX_wit.2 W) (aH.2 W)
    intro T₁ A₁ B₁ C₁ X₁ H₁ T₂ A₂ B₂ C₂ X₂ H₂ σ₁ σ₂ HT₁ HT₂ HA₁ HA₂ HB₁ HB₂ HC₁ HC₂ HX HH W tmEqX
      ⟨A_h, a_h_T, b_h_T, hA_h_red, _, _, _, _, a_h_l, a_h_r,
        hH_red_l, hH_red_r, hCa, hCb, hC12, teLa, teLb, _⟩
    cases WHNF.id.whRedS hA_h_red.2
    have hAB_eq_at_σ₁ : Γ₀ ⊢ A.subst σ₁ ≡ B.subst σ₁ : T.subst σ₁ := hCa.symm.trans hCb
    have hT_σ : Γ₀ ⊢ T.subst σ₁ : .sort u := HT.hasType.1.subst' W.wf₀ W.left.toSubstEq
    have hΓ_T : ⊢ T.subst σ₁ :: Γ₀ := ⟨W.wf₀, _, hT_σ⟩
    have W_T : Ctx.SubstEq (T.subst σ₁ :: Γ₀) σ₁.lift σ₁.lift (T :: Γ) :=
      W.left.toSubstEq.lift HT.hasType.1 hT_σ
    have hC_σ : T.subst σ₁ :: Γ₀ ⊢ C.subst σ₁.lift : .sort v :=
      HC.hasType.1.subst hΓ_T W_T
    have hX₁_σ_raw : Γ₀ ⊢ X₁.subst σ₁ : (C.inst A).subst σ₁ :=
      HX.hasType.1.subst' W.wf₀ W.left.toSubstEq
    have hX₁_σ : Γ₀ ⊢ X₁.subst σ₁ : (C.subst σ₁.lift).inst (A.subst σ₁) := by
      rw [show (C.subst σ₁.lift).inst (A.subst σ₁) = (C.inst A).subst σ₁ from subst_inst.symm]
      exact hX₁_σ_raw
    have hTidAB_σ : Γ₀ ⊢ (T.id A B).subst σ₁ : .sort true :=
      H_idAab.subst' W.wf₀ W.left.toSubstEq
    have hCinst_AB_eq : Γ₀ ⊢ (C.inst A).subst σ₁ ≡ (C.inst B).subst σ₁ : .sort v := by
      rw [show (C.inst A).subst σ₁ = (C.subst σ₁.lift).inst (A.subst σ₁) from subst_inst,
          show (C.inst B).subst σ₁ = (C.subst σ₁.lift).inst (B.subst σ₁) from subst_inst]
      exact .instDF W.wf₀ hT_σ .sort hC_σ hAB_eq_at_σ₁
    have hTypedWHRedS_LHS :
        Γ₀ ⊢ (Term.tr T A B C X₁ H₁).subst σ₁ ⤳* X₁.subst σ₁ : (C.inst B).subst σ₁ := by
      refine ⟨subst_inst ▸ .trans ?_ (.defeqDF (.instDF W.wf₀ hT_σ .sort hC_σ hCb)
        (.tr_refl₀ W.wf₀ hCa.hasType.1 hC_σ ?_)), (WHRedS.tr hH_red_l.2).tail .tr_refl⟩
      · refine IsDefEq.trDF hT_σ hCa.symm hCb.symm hC_σ hC_σ hX₁_σ hH_red_l.1 ?_ hTidAB_σ
        exact .instDF W.wf₀ hT_σ .sort hC_σ hCb.symm
      · exact .defeqDF (.instDF W.wf₀ hT_σ .sort hC_σ hCa.symm) hX₁_σ
    have hT_σ_eq : Γ₀ ⊢ T.subst σ₁ ≡ T.subst σ₂ : .sort u :=
      HT.hasType.1.subst' W.wf₀ W.toSubstEq
    have hT_σ₂ : Γ₀ ⊢ T.subst σ₂ : .sort u := hT_σ_eq.hasType.2
    have hA_σ_eq : Γ₀ ⊢ A.subst σ₁ ≡ A.subst σ₂ : T.subst σ₁ :=
      HA.hasType.1.subst' W.wf₀ W.toSubstEq
    have hB_σ_eq : Γ₀ ⊢ B.subst σ₁ ≡ B.subst σ₂ : T.subst σ₁ :=
      HB.hasType.1.subst' W.wf₀ W.toSubstEq
    have hCa_r : Γ₀ ⊢ a_h_r ≡ A.subst σ₂ : T.subst σ₂ :=
      hT_σ_eq.defeqDF ((hC12.symm.trans hCa).trans hA_σ_eq)
    have hCb_r : Γ₀ ⊢ a_h_r ≡ B.subst σ₂ : T.subst σ₂ :=
      hT_σ_eq.defeqDF ((hC12.symm.trans hCb).trans hB_σ_eq)
    have hΓ_T_σ₂ : ⊢ T.subst σ₂ :: Γ₀ := ⟨W.wf₀, _, hT_σ₂⟩
    have W_T_σ₂ : Ctx.SubstEq (T.subst σ₂ :: Γ₀) σ₂.lift σ₂.lift (T :: Γ) :=
      W.symm.left.toSubstEq.lift HT.hasType.1 hT_σ₂
    have hC_σ₂ : T.subst σ₂ :: Γ₀ ⊢ C.subst σ₂.lift : .sort v :=
      HC.hasType.1.subst hΓ_T_σ₂ W_T_σ₂
    have hX₂_σ₂_raw : Γ₀ ⊢ X₂.subst σ₂ : (C.inst A).subst σ₂ :=
      HX.hasType.2.subst' W.wf₀ W.symm.left.toSubstEq
    have hX₂_σ₂ : Γ₀ ⊢ X₂.subst σ₂ : (C.subst σ₂.lift).inst (A.subst σ₂) := by
      rw [show (C.subst σ₂.lift).inst (A.subst σ₂) = (C.inst A).subst σ₂ from subst_inst.symm]
      exact hX₂_σ₂_raw
    have hTidAB_σ₂ : Γ₀ ⊢ (T.id A B).subst σ₂ : .sort true :=
      H_idAab.subst' W.wf₀ W.symm.left.toSubstEq
    have hTidAB_σ_eq : Γ₀ ⊢ (T.id A B).subst σ₁ ≡ (T.id A B).subst σ₂ : .sort true :=
      H_idAab.subst' W.wf₀ W.toSubstEq
    have hH_red_r' : Γ₀ ⊢ H₂.subst σ₂ ≡ Term.refl a_h_r : (T.id A B).subst σ₂ :=
      hTidAB_σ_eq.defeqDF hH_red_r.1
    have hTypedWHRedS_RHS :
        Γ₀ ⊢ (Term.tr T A B C X₂ H₂).subst σ₂ ⤳* X₂.subst σ₂ : (C.inst B).subst σ₁ := by
      refine ⟨(HCb.hasType.1.subst' W.wf₀ W.symm.toSubstEq).defeqDF (subst_inst ▸ ?_),
        (WHRedS.tr hH_red_r.2).tail .tr_refl⟩
      refine .trans ?_ <| .defeqDF (.instDF W.wf₀ hT_σ₂ .sort hC_σ₂ hCb_r) <|
        .tr_refl₀ W.wf₀ hCa_r.hasType.1 hC_σ₂ <|
        .defeqDF (.instDF W.wf₀ hT_σ₂ .sort hC_σ₂ hCa_r.symm) hX₂_σ₂
      refine IsDefEq.trDF hT_σ₂ hCa_r.symm hCb_r.symm hC_σ₂ hC_σ₂ hX₂_σ₂ hH_red_r' ?_ hTidAB_σ₂
      exact .instDF W.wf₀ hT_σ₂ .sort hC_σ₂ hCb_r.symm
    have hT_T₁_σ : Γ₀ ⊢ T.subst σ₁ ≡ T₁.subst σ₁ : .sort u :=
      HT₁.subst' W.wf₀ W.left.toSubstEq
    have hT₁_σ : Γ₀ ⊢ T₁.subst σ₁ : .sort u := hT_T₁_σ.hasType.2
    have hA_A₁_σ : Γ₀ ⊢ A.subst σ₁ ≡ A₁.subst σ₁ : T.subst σ₁ :=
      HA₁.subst' W.wf₀ W.left.toSubstEq
    have hB_B₁_σ : Γ₀ ⊢ B.subst σ₁ ≡ B₁.subst σ₁ : T.subst σ₁ :=
      HB₁.subst' W.wf₀ W.left.toSubstEq
    have hCa_1 : Γ₀ ⊢ A₁.subst σ₁ ≡ a_h_l : T₁.subst σ₁ :=
      hT_T₁_σ.defeqDF (hA_A₁_σ.symm.trans hCa.symm)
    have hCb_1 : Γ₀ ⊢ B₁.subst σ₁ ≡ a_h_l : T₁.subst σ₁ :=
      hT_T₁_σ.defeqDF (hB_B₁_σ.symm.trans hCb.symm)
    have hΓ_T₁_σ : ⊢ T₁.subst σ₁ :: Γ₀ := ⟨W.wf₀, _, hT₁_σ⟩
    have W_T₁ : Ctx.SubstEq (T₁.subst σ₁ :: Γ₀) σ₁.lift σ₁.lift (T :: Γ) :=
      W.left.toSubstEq.lift_at HT.hasType.1 hT₁_σ hT_T₁_σ
    have hC_C₁_σ_at_T₁ :
        T₁.subst σ₁ :: Γ₀ ⊢ C.subst σ₁.lift ≡ C₁.subst σ₁.lift : .sort v :=
      HC₁.subst hΓ_T₁_σ W_T₁
    have hC₁_σ_at_T₁ : T₁.subst σ₁ :: Γ₀ ⊢ C₁.subst σ₁.lift : .sort v := hC_C₁_σ_at_T₁.hasType.2
    have hCA_C₁A₁ : Γ₀ ⊢ (C.subst σ₁.lift).inst (A.subst σ₁) ≡
        (C₁.subst σ₁.lift).inst (A₁.subst σ₁) : .sort v :=
      .instDF W.wf₀ hT₁_σ .sort hC_C₁_σ_at_T₁ (hT_T₁_σ.defeqDF hA_A₁_σ)
    have hX₁_σ_at_C₁A₁ : Γ₀ ⊢ X₁.subst σ₁ : (C₁.subst σ₁.lift).inst (A₁.subst σ₁) :=
      hCA_C₁A₁.defeqDF hX₁_σ
    have hTid_T₁id_σ : Γ₀ ⊢ (T.id A B).subst σ₁ ≡ (T₁.id A₁ B₁).subst σ₁ : .sort true :=
      .idDF hT_T₁_σ hA_A₁_σ hB_B₁_σ
    have hH_red_l_at_T₁ : Γ₀ ⊢ H₁.subst σ₁ ≡ Term.refl a_h_l : (T₁.id A₁ B₁).subst σ₁ :=
      hTid_T₁id_σ.defeqDF hH_red_l.1
    have hTid_T₁id_σ_ty : Γ₀ ⊢ (T₁.id A₁ B₁).subst σ₁ : .sort true := hTid_T₁id_σ.hasType.2
    have hC₁B_C₁ahl : Γ₀ ⊢ (C₁.subst σ₁.lift).inst (B₁.subst σ₁) ≡
        (C₁.subst σ₁.lift).inst a_h_l : .sort v :=
      .instDF W.wf₀ hT₁_σ .sort hC₁_σ_at_T₁ hCb_1
    have hTypedWHRedS_LHS_1 :
        Γ₀ ⊢ (Term.tr T₁ A₁ B₁ C₁ X₁ H₁).subst σ₁ ⤳* X₁.subst σ₁ : (C.inst B).subst σ₁ := by
      refine subst_inst ▸ ⟨?_, (WHRedS.tr hH_red_l.2).tail .tr_refl⟩
      refine .defeqDF (.instDF W.wf₀ hT₁_σ .sort hC_C₁_σ_at_T₁.symm (hT_T₁_σ.defeqDF hB_B₁_σ.symm))
        (.trans ?_ (.defeqDF hC₁B_C₁ahl.symm (.tr_refl₀ W.wf₀ hCa_1.hasType.2 hC₁_σ_at_T₁ ?_)))
      · exact .trDF hT₁_σ hCa_1 hCb_1 hC₁_σ_at_T₁ hC₁_σ_at_T₁ hX₁_σ_at_C₁A₁
          hH_red_l_at_T₁ hC₁B_C₁ahl hTid_T₁id_σ_ty
      · exact .defeqDF (.instDF W.wf₀ hT₁_σ .sort hC₁_σ_at_T₁ hCa_1) hX₁_σ_at_C₁A₁
    have hT_T₂_σ : Γ₀ ⊢ T.subst σ₂ ≡ T₂.subst σ₂ : .sort u :=
      HT₂.subst' W.wf₀ W.symm.left.toSubstEq
    have hT₂_σ : Γ₀ ⊢ T₂.subst σ₂ : .sort u := hT_T₂_σ.hasType.2
    have hA_A₂_σ : Γ₀ ⊢ A.subst σ₂ ≡ A₂.subst σ₂ : T.subst σ₂ :=
      HA₂.subst' W.wf₀ W.symm.left.toSubstEq
    have hB_B₂_σ : Γ₀ ⊢ B.subst σ₂ ≡ B₂.subst σ₂ : T.subst σ₂ :=
      HB₂.subst' W.wf₀ W.symm.left.toSubstEq
    have hCa_2 : Γ₀ ⊢ A₂.subst σ₂ ≡ a_h_r : T₂.subst σ₂ :=
      hT_T₂_σ.defeqDF (hA_A₂_σ.symm.trans hCa_r.symm)
    have hCb_2 : Γ₀ ⊢ B₂.subst σ₂ ≡ a_h_r : T₂.subst σ₂ :=
      hT_T₂_σ.defeqDF (hB_B₂_σ.symm.trans hCb_r.symm)
    have hΓ_T₂_σ : ⊢ T₂.subst σ₂ :: Γ₀ := ⟨W.wf₀, _, hT₂_σ⟩
    have W_T₂ : Ctx.SubstEq (T₂.subst σ₂ :: Γ₀) σ₂.lift σ₂.lift (T :: Γ) :=
      W.symm.left.toSubstEq.lift_at HT.hasType.1 hT₂_σ hT_T₂_σ
    have hC_C₂_σ_at_T₂ :
        T₂.subst σ₂ :: Γ₀ ⊢ C.subst σ₂.lift ≡ C₂.subst σ₂.lift : .sort v :=
      HC₂.subst hΓ_T₂_σ W_T₂
    have hC₂_σ_at_T₂ : T₂.subst σ₂ :: Γ₀ ⊢ C₂.subst σ₂.lift : .sort v := hC_C₂_σ_at_T₂.hasType.2
    have hCA_C₂A₂ : Γ₀ ⊢ (C.subst σ₂.lift).inst (A.subst σ₂) ≡
        (C₂.subst σ₂.lift).inst (A₂.subst σ₂) : .sort v :=
      .instDF W.wf₀ hT₂_σ .sort hC_C₂_σ_at_T₂ (hT_T₂_σ.defeqDF hA_A₂_σ)
    have hX₂_σ_at_C₂A₂ : Γ₀ ⊢ X₂.subst σ₂ : (C₂.subst σ₂.lift).inst (A₂.subst σ₂) :=
      hCA_C₂A₂.defeqDF hX₂_σ₂
    have hTid_T₂id_σ : Γ₀ ⊢ (T.id A B).subst σ₂ ≡ (T₂.id A₂ B₂).subst σ₂ : .sort true :=
      .idDF hT_T₂_σ hA_A₂_σ hB_B₂_σ
    have hH_red_r_at_T₂ : Γ₀ ⊢ H₂.subst σ₂ ≡ Term.refl a_h_r : (T₂.id A₂ B₂).subst σ₂ :=
      hTid_T₂id_σ.defeqDF hH_red_r'
    have hTid_T₂id_σ_ty : Γ₀ ⊢ (T₂.id A₂ B₂).subst σ₂ : .sort true := hTid_T₂id_σ.hasType.2
    have hC₂B_C₂ahr : Γ₀ ⊢ (C₂.subst σ₂.lift).inst (B₂.subst σ₂) ≡
        (C₂.subst σ₂.lift).inst a_h_r : .sort v :=
      .instDF W.wf₀ hT₂_σ .sort hC₂_σ_at_T₂ hCb_2
    have hTypedWHRedS_RHS_1 :
        Γ₀ ⊢ (Term.tr T₂ A₂ B₂ C₂ X₂ H₂).subst σ₂ ⤳* X₂.subst σ₂ : (C.inst B).subst σ₁ := by
      refine ⟨?_, (WHRedS.tr hH_red_r.2).tail .tr_refl⟩
      refine (HCb.hasType.1.subst' W.wf₀ W.symm.toSubstEq).defeqDF (subst_inst ▸ ?_)
      refine .defeqDF (.instDF W.wf₀ hT₂_σ .sort hC_C₂_σ_at_T₂.symm (hT_T₂_σ.defeqDF hB_B₂_σ.symm))
        (.trans ?_ (.defeqDF hC₂B_C₂ahr.symm (.tr_refl₀ W.wf₀ hCa_2.hasType.2 hC₂_σ_at_T₂ ?_)))
      · exact .trDF hT₂_σ hCa_2 hCb_2 hC₂_σ_at_T₂ hC₂_σ_at_T₂ hX₂_σ_at_C₂A₂
          hH_red_r_at_T₂ hC₂B_C₂ahr hTid_T₂id_σ_ty
      · exact .defeqDF (.instDF W.wf₀ hT₂_σ .sort hC₂_σ_at_T₂ hCa_2) hX₂_σ_at_C₂A₂
    have hX_cross : Γ₀ ⊢ X₁.subst σ₁ ≡ X₂.subst σ₂ : (C.inst B).subst σ₁ :=
      hCinst_AB_eq.defeqDF (HX.subst' W.wf₀ W.toSubstEq)
    have hCross : Γ₀ ⊢ (Term.tr T₁ A₁ B₁ C₁ X₁ H₁).subst σ₁ ≡
        (Term.tr T₂ A₂ B₂ C₂ X₂ H₂).subst σ₂ : (C.inst B).subst σ₁ :=
      hTypedWHRedS_LHS_1.1.trans (hX_cross.trans hTypedWHRedS_RHS_1.1.symm)
    have hk1 : m'.1 ≤ max m'.1 a_ty.1 := Nat.le_max_left ..
    have hk2 : a_ty.1 ≤ max m'.1 a_ty.1 := Nat.le_max_right ..
    have hmem'_wit := (TShape.HasType.def hk1 hk2).1 hty
    have hAB_tm := (LR hΓ₀).trans hCa.symm hCb ((LR hΓ₀).symm hCa teLa) teLb
    have W_cons := LR.Adequate.cons ihA HT h_vbvA (hvA.lift (Nat.le_max_right vb.1 vA.1))
      hAB_eq_at_σ₁ hAB_tm W.left
    have tyCAB_wit : (LR hΓ₀).TyEq ((C.inst A).subst σ₁) ((C.inst B).subst σ₁)
        (WShape.lift (max m'.1 a_ty.1) a_ty.snd) := by
      have hc_C' := hc_C.mono_l
        (Valuation.LE.push.2 ⟨.rfl, (TShape.lift_eqv (Nat.le_max_left vb.1 vA.1)).2⟩)
      obtain ⟨_, _, _, le_n, le_a, hC'', hSort_v, hmem_v⟩ :=
        (LE_Interp.sound HC W_cons.fits).2 hc_C' |>.out
      have ha_type : a_ty.snd.HasType .type :=
        (WShape.HasType.lift hk2).1 (WShape.lift_type.symm ▸ hmem'_wit.isType)
      have H := ((ihC hC'' hSort_v hmem_v).1 W_cons).1
      rw [show C.subst (σ₁.cons (A.subst σ₁)) = (C.inst A).subst σ₁ by
            rw [subst_inst, inst_lift_cons],
          show C.subst (σ₁.cons (B.subst σ₁)) = (C.inst B).subst σ₁ by
            rw [subst_inst, inst_lift_cons]] at H
      have tyCAB_at_aty : (LR hΓ₀).TyEq ((C.inst A).subst σ₁) ((C.inst B).subst σ₁) a_ty.snd :=
        LR.toValTy le_n le_a ha_type hSort_v hmem_v H
      exact (LR.TyEq.lift hk2 ha_type).2 tyCAB_at_aty
    have hAty_CB : (LR hΓ₀).TyEq ((C.inst B).subst σ₁) ((C.inst B).subst σ₁) a := by
      have ⟨_, _, _, le_n, le_a, hCB', hSort, hmem'⟩ := (LE_Interp.sound HCb W.fits).2 hA |>.out
      exact LR.toValTy le_n le_a hmem.isType hSort hmem' ((ihCb hCB' hSort hmem').1 W.left).1
    have tmEqX_CB := (LR hΓ₀).conv tyCAB_wit tmEqX
    have hc_wit : a.T.Compat (WShape.lift (max m'.1 a_ty.1) a_ty.snd).T :=
      have ⟨z, ha_z, haty_z⟩ := TShape.Compat.def'.1 hAc
      TShape.Compat.def'.2 ⟨z, ha_z, (TShape.lift_eqv hk2).1.trans haty_z⟩
    exact ((LR hΓ₀).whr hTypedWHRedS_LHS_1 hTypedWHRedS_RHS_1 hCross).2 <|
      LR.TmEq.mono_r (le_m.trans (TShape.lift_eqv hk1).2) hmem hmem'_wit
        hc_wit hAty_CB tmEqX_CB
  | @tr_refl Γ A_ty u a_tm C v x _HA Ha HC Hx H_tr ihA iha ihC ihx ih_tr =>
    refine ⟨fun _ _ W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · exact ((ih_tr hM hA hmem).1 W).1
    · refine ((ihx ?_ hA hmem).1 W).2
      exact (LE_Interp.sound (.tr_refl₀ W.wf Ha HC Hx) W.fits).1.1 hM
    · have hMeq : Γ₀ ⊢ (Term.tr A_ty a_tm a_tm C x (Term.refl a_tm)).subst σ ≡ x.subst σ :
          (C.inst a_tm).subst σ := IsDefEq.tr_refl₀ W.wf Ha HC Hx |>.subst' W.wf₀ W.toSubstEq
      have Hx_σ := Hx.subst' W.wf₀ W.toSubstEq
      have hwh_M : Γ₀ ⊢ (Term.tr A_ty a_tm a_tm C x (Term.refl a_tm)).subst σ ⤳* x.subst σ :
          (C.inst a_tm).subst σ := ⟨hMeq, .tail .rfl WHRed.tr_refl⟩
      have hMrefl : Γ₀ ⊢ x.subst σ ⤳* x.subst σ : (C.inst a_tm).subst σ :=
        ⟨Hx_σ, .rfl⟩
      have hM_x : LE_Interp ρ m.T x :=
        (LE_Interp.sound (.tr_refl₀ W.wf Ha HC Hx) W.fits).1.1 hM
      exact ((LR _).whr hwh_M hMrefl hMeq).2 ((ihx hM_x hA hmem).2 W)
  | proofIrrel Hp _ _ ihp =>
    refine .wf fun hΓ => .fits fun W => ?_
    have ⟨_, _, s, le_n, le_a, _, hSort, hmem'⟩ := (LE_Interp.sound Hp W).2 hA |>.out
    have hS := WShape.HasType.mono_r hSort.le_sort' .sort hmem'; simp at hS
    have ha' := hS.mono_r ((TShape.LE.lift_l le_n).1 le_a) ((WShape.HasType.lift le_n).2 hmem)
    cases (WShape.lift_eq_bot le_n).1 (hS.proofIrrel ha')
    exact .bot' Hp hA hmem.isType ihp
  | @sigmaDF Γ A A' u B B' v HA HB HB' ihA ihB =>
    cases hmem.unfold with
    | id => have .sigma _ _ _ _ h := hM; cases TShape.id_not_le_sigma h
    | refl => have .sigma _ _ _ _ h := hM; cases TShape.refl_not_le_sigma h
    | bot hm =>
      cases hm.unfold with
      | bot _ => exact .bot (fun _ _ => (LR _).bot_ty) hm
      | sort => exact .bot (fun _ _ => LogRelBase.TyEq.sort) hm
      | forallE | sigma | nat | unit | id =>
        let .sort h := hA; cases (TShape.LE.lift_r (by simp [TShape.sort])).1 h
    | sort => cases n <;> have .sigma _ _ _ _ h := hM <;> cases TShape.sort_not_le_sigma h
    | unit => have .sigma _ _ _ _ h := hM; cases TShape.unit_not_le_sigma h
    | @lam _ f₀ =>
      revert hM; unfold WShape.lam'
      split <;> [skip; exact fun _ => .bot
        (fun _ _ => (LR _).mono_r_2_ty hA.le_sort' hmem.isType .sort LogRelBase.TyEq.sort)
        hmem.isType]
      intro | .sigma _ _ _ _ h => cases TShape.lam_not_le_sigma h
    | forallE => have .sigma _ _ _ _ h := hM; cases TShape.forallE_not_le_sigma h
    | pair => have .sigma _ _ _ _ h := hM; cases TShape.pair_not_le_sigma h
    | nat => have .sigma _ _ _ _ h := hM; exact (TShape.nat_not_le_sigma h).elim
    | zero => have .sigma _ _ _ _ h := hM; exact (TShape.zero_not_le_sigma h).elim
    | succ _ => have .sigma _ _ _ _ h := hM; exact (TShape.succ_not_le_sigma h).elim
    | @sigma k a₂ a₁ aty
    refine .wf₀ fun hΓ₀ => ?_
    have aty := WShape.HasTypePi.iff.1 (aty : WShape.HasTypePi a₂ a₁ true)
    have hA1 := hM.sigma_inv.1
    have cons := Adequate.cons (hΓ₀ := hΓ₀) ihA HA
    refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩ <;> (
      have ⟨_, a', _, le_n, le_a, hA', hSort, hmem'⟩ :=
        (LE_Interp.sound HA W.left.fits).2 hA1 |>.out
      have HAAσ := HA.subst' W.wf₀ W.left.toSubstEq
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
  | @pairDF Γ A A' u B B' v x x' y y' HA HB HB' Hx Hy HBxx' HSigmaTy
      ihA ihB ihB' ihx ihy ihBa ihAB =>
    cases hmem.unfold with
    | id => have .pair _ _ h := hM; cases TShape.id_not_le_pair' h
    | refl => have .pair _ _ h := hM; cases TShape.refl_not_le_pair' h
    | bot hm =>
      cases hm.unfold with
      | bot _ => exact .bot (fun _ _ => (LR _).bot_ty) hm
      | sort => cases n <;> let .sigma _ _ _ _ le := hA <;> exact (TShape.sort_not_le_sigma le).elim
      | unit => let .sigma _ _ _ _ le := hA; exact (TShape.unit_not_le_sigma le).elim
      | forallE => let .sigma _ _ _ _ le := hA; exact (TShape.forallE_not_le_sigma le).elim
      | sigma => exact LR.Adequate.bot' HSigmaTy hA hmem.isType ihAB
      | nat => let .sigma _ _ _ _ le := hA; exact (TShape.nat_not_le_sigma le).elim
      | id => let .sigma _ _ _ _ le := hA; exact (TShape.id_not_le_sigma le).elim
    | sort => cases n <;> have .pair _ _ h := hM <;> cases TShape.sort_not_le_pair' h
    | unit => have .pair _ _ h := hM; cases TShape.unit_not_le_pair' h
    | @lam k f₀ =>
      revert hM; unfold WShape.lam'
      split <;> [skip; exact fun _ => LR.Adequate.bot' HSigmaTy hA hmem.isType ihAB]
      intro | .pair _ _ h => cases TShape.lam_not_le_pair' h
    | forallE => have .pair _ _ h := hM; cases TShape.forallE_not_le_pair' h
    | sigma => have .pair _ _ h := hM; cases TShape.sigma_not_le_pair' h
    | nat => have .pair _ _ h := hM; exact (TShape.nat_not_le_pair' h).elim
    | zero => have .pair _ _ h := hM; exact (TShape.zero_not_le_pair' h).elim
    | succ _ => have .pair _ _ h := hM; exact (TShape.succ_not_le_pair' h).elim
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
        (HA.hasType.1.subst' W.wf₀ W.left.toSubstEq).hasType.1
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
        hP.hasType.1.subst' W.wf₀ W.left.toSubstEq
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
          (HA_L_to_A.hasType.1.subst' W.wf₀ W.left.toSubstEq).hasType.1
        have hΓA_L : ⊢ A_L :: Γ := ⟨W.wf, _, HA_L_to_A.hasType.1⟩
        have hΓA_LS_L : ⊢ A_L.subst σ_L :: Γ₀ := ⟨W.wf₀, _, HA_Lσ⟩
        have HB_Lσ : A_L.subst σ_L :: Γ₀ ⊢ B_L.subst σ_L.lift : .sort v :=
          (HB_L_R_at_A_L.hasType.1.subst hΓA_LS_L
            (W.left.toSubstEq.lift HA_L_to_A.hasType.1 HA_Lσ)).hasType.1
        have hx_LσTy : Γ₀ ⊢ x_L.subst σ_L : A_L.subst σ_L :=
          (Hx_L_R.hasType.1.subst' W.wf₀ W.left.toSubstEq).hasType.1
        have hy_LσTy : Γ₀ ⊢ y_L.subst σ_L : (B_L.subst σ_L.lift).inst (x_L.subst σ_L) := by
          have := (Hy_L_R.hasType.1.subst' W.wf₀ W.left.toSubstEq).hasType.1
          rwa [subst_inst] at this
        -- Conversion A_L.σ_L ≡ A.σ_L (diagonal at σ_L)
        have HA_L_to_A_σL : Γ₀ ⊢ A_L.subst σ_L ≡ A.subst σ_L : .sort u :=
          HA_L_to_A.subst' W.wf₀ W.left.toSubstEq
        -- Natural LHS pair eq at sigma A_L B_L
        have hPair_natural_eq : Γ ⊢
            Term.pair A_L B_L x_L y_L ≡ Term.pair A_R B_R x_R y_R : Term.sigma A_L B_L :=
          .pairDF₀ W.wf HA_L_R HB_L_R_at_A_L Hx_L_R Hy_L_R
        have hPair_L_natural_σL : Γ₀ ⊢
            (Term.pair A_L B_L x_L y_L).subst σ_L ≡
            (Term.pair A_L B_L x_L y_L).subst σ_L :
            (Term.sigma A_L B_L).subst σ_L :=
          hPair_natural_eq.hasType.1.subst' W.wf₀ W.left.toSubstEq
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
              (B_L.subst σ_L.lift).inst (Term.fst
                ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L))) ≡
              (B_L.subst σ_L.lift).inst (Term.fst
                ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L))) :
              .sort v :=
            IsDefEq.instDF hΓ₀ HA_Lσ .sort HB_Lσ hFst_L_natural_Ty
          have hSnd_L_at_Fst_L : Γ₀ ⊢
              Term.snd ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L)) :
              (B_L.subst σ_L.lift).inst (Term.fst
                ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L))) :=
            (hPair_L_natural_σL.sndDF₀ W.wf₀).hasType.1
          have hBx_L_to_BFst_L : Γ₀ ⊢
              (B_L.subst σ_L.lift).inst (x_L.subst σ_L) ≡
              (B_L.subst σ_L.lift).inst (Term.fst
                ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L))) :
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
            Hx_x_L.subst' W.wf₀ W.left.toSubstEq
          have hxσL_to_FstL : Γ₀ ⊢ x.subst σ_L ≡
              Term.fst ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L)) :
              A.subst σ_L := hx_x_L_σL.trans hFst_L_eq.symm
          have hBxFstL : Γ₀ ⊢
              (B.subst σ_L.lift).inst (x.subst σ_L) ≡
              (B.subst σ_L.lift).inst (Term.fst
                ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L))) :
              .sort v :=
            IsDefEq.instDF hΓ₀ HAσL .sort HBσL hxσL_to_FstL
          have hSnd_L_eq : Γ₀ ⊢
              Term.snd ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L)) ≡
              y_L.subst σ_L : (B.subst σ_L.lift).inst (Term.fst
                ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L))) :=
            hBxFstL.defeqDF hSnd_L_eq_at_outer_x
          -- ===== RHS .snd: build at NATURAL (A_R, B_R, x_R, σ_R), bridge to outer =====
          have hBFst_R_self : Γ₀ ⊢
              (B_R.subst σ_R.lift).inst (Term.fst
                ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R))) ≡
              (B_R.subst σ_R.lift).inst (Term.fst
                ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R))) :
              .sort v :=
            IsDefEq.instDF hΓ₀ HA_Rσ .sort HB_Rσ hFst_R_natural_Ty
          have hSnd_R_at_Fst_R : Γ₀ ⊢
              Term.snd ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R)) :
              (B_R.subst σ_R.lift).inst (Term.fst
                ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R))) :=
            (hPair_R_natural_σR.sndDF₀ W.wf₀).hasType.1
          have hBx_R_to_BFst_R : Γ₀ ⊢
              (B_R.subst σ_R.lift).inst (x_R.subst σ_R) ≡
              (B_R.subst σ_R.lift).inst (Term.fst
                ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R))) :
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
              y_R.subst σ_R : (B.subst σ_L.lift).inst (Term.fst
                ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L))) :=
            hBxFstL.defeqDF hSnd_R_eq_at_outer_x_σL
          -- ===== Source: .snd pair_L ≡ .snd pair_R at outer type =====
          have hBFstLR_self_at_outer : Γ₀ ⊢
              (B.subst σ_L.lift).inst (Term.fst
                ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L))) ≡
              (B.subst σ_L.lift).inst (Term.fst
                ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R))) :
              .sort v :=
            IsDefEq.instDF hΓ₀ HAσL .sort HBσL hFst_LR_src
          have hSnd_LR_src : Γ₀ ⊢
              Term.snd ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L)) ≡
              Term.snd ((A_R.subst σ_R).pair (B_R.subst σ_R.lift) (x_R.subst σ_R) (y_R.subst σ_R)) :
              (B.subst σ_L.lift).inst (Term.fst
                ((A_L.subst σ_L).pair (B_L.subst σ_L.lift) (x_L.subst σ_L) (y_L.subst σ_L))) :=
            hMNσσ.sndDF₀ W.wf₀
          -- whr discharge + conv ihTmy
          refine ((LR _).whr ⟨hSnd_L_eq, snd_pair⟩ ⟨hSnd_R_eq, snd_pair⟩ hSnd_LR_src).2 ?_
          -- Build hxFst: TmEq x.σ_L (.fst pair_L.σ_L) A.σ_L ms at_ via whr from ihTm_x_to_x_L
          have hxσTy_outer : Γ₀ ⊢ x.subst σ_L : A.subst σ_L :=
            (Hx.hasType.1.subst' W.wf₀ W.left.toSubstEq).hasType.1
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
      have HAAσ := HA.subst' W.wf₀ W.left.toSubstEq
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
    | sort | unit | sigma | forallE => exact (TShape.sort_not_le_sigma le).elim
    | lam => exact (TShape.forallE_not_le_sigma le).elim
    | nat => exact (TShape.sort_not_le_sigma le).elim
    | zero => exact (TShape.nat_not_le_sigma le).elim
    | succ => exact (TShape.nat_not_le_sigma le).elim
    | id => exact (TShape.sort_not_le_sigma le).elim
    | refl => exact (TShape.id_not_le_sigma le).elim
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
    | sort | unit | sigma | forallE | nat => exact (TShape.sort_not_le_sigma le).elim
    | lam => exact (TShape.forallE_not_le_sigma le).elim
    | zero | succ => exact (TShape.nat_not_le_sigma le).elim
    | id => exact (TShape.sort_not_le_sigma le).elim
    | refl => exact (TShape.id_not_le_sigma le).elim
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
          (hRule.subst' W.wf₀ W.left.toSubstEq)
          (HA_σσ'.symm.defeqDF (hRule.subst' W.symm.left.wf₀ W.symm.left.toSubstEq))
          (.tail .rfl .pair_fst) (.tail .rfl .pair_fst)
          (Hfst.subst' W.wf₀ W.toSubstEq)
          (((iha hpa_LE hA hmem).1 W).1)
      · -- N-validity: M = N = pa
        have hpa_LE := (LE_Interp.sound hRule W.fits).1.1 hM
        have HA_σσ' := HA.hasType.1.subst' W.wf₀ W.toSubstEq
        exact this W
          (Ha.subst' W.wf₀ W.left.toSubstEq)
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
          (hRule.subst' W.wf₀ W.left.toSubstEq)
          (HBinst_σσ'.symm.defeqDF (hRule.subst' W.symm.left.wf₀ W.symm.left.toSubstEq))
          (.tail .rfl .pair_snd) (.tail .rfl .pair_snd)
          (Hsnd.subst' W.wf₀ W.toSubstEq)
          (((ihb hpb_LE hA hmem).1 W).1)
      · -- N-validity: M = N = pb
        have hpb_LE := (LE_Interp.sound hRule W.fits).1.1 hM
        have HBinst_σσ' := (IsDefEq.inst0 W.wf Ha HB).subst' W.wf₀ W.toSubstEq
        exact this W
          (Hb.subst' W.wf₀ W.left.toSubstEq)
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
    | unit => have .pair _ _ h := hM; cases TShape.unit_not_le_pair' h
    | forallE => have .pair _ _ h := hM; cases TShape.forallE_not_le_pair' h
    | lam =>
      revert hM; unfold WShape.lam'; split <;> [skip; exact fun _ => (LR _).bot hmem.isType hTyEq]
      intro | .pair _ _ h => cases TShape.lam_not_le_pair' h
    | sigma => have .pair _ _ h := hM; cases TShape.sigma_not_le_pair' h
    | nat => have .pair _ _ h := hM; cases TShape.nat_not_le_pair' h
    | zero => have .pair _ _ h := hM; cases TShape.zero_not_le_pair' h
    | succ => have .pair _ _ h := hM; cases TShape.succ_not_le_pair' h
    | id => have .pair _ _ h := hM; cases TShape.id_not_le_pair' h
    | refl => have .pair _ _ h := hM; cases TShape.refl_not_le_pair' h
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
  | nat => exact .nat hM hA hmem
  | zero =>
    refine .wf₀ fun hΓ₀ => ?_
    suffices (LR hΓ₀).TmEq .zero .zero .nat m a from
      ⟨fun _ _ _ => ⟨this, this⟩, fun _ _ => this⟩
    cases hmem.unfold with
    | bot hm =>
      apply (LR _).bot hm
      cases hm.unfold with
      | bot => exact (LR _).bot_ty
      | sort => cases n <;> (have .nat h := hA; exact (TShape.sort_not_le_nat h).elim)
      | unit => have .nat h := hA; exact (TShape.unit_not_le_nat h).elim
      | forallE _ => have .nat h := hA; exact (TShape.forallE_not_le_nat h).elim
      | sigma _ => have .nat h := hA; exact (TShape.sigma_not_le_nat h).elim
      | id => have .nat h := hA; exact (TShape.id_not_le_nat h).elim
      | nat => exact ⟨⟨.nat, .rfl⟩, ⟨.nat, .rfl⟩⟩
    | sort => cases n <;> (have .nat h := hA; exact (TShape.sort_not_le_nat h).elim)
    | unit => have .zero h := hM; exact (TShape.unit_not_le_zero h).elim
    | forallE => have .nat h := hA; exact (TShape.sort_not_le_nat h).elim
    | lam => have .nat h := hA; exact (TShape.forallE_not_le_nat h).elim
    | sigma => have .nat h := hA; exact (TShape.sort_not_le_nat h).elim
    | pair => have .nat h := hA; exact (TShape.sigma_not_le_nat h).elim
    | nat => have .zero h := hM; exact (TShape.nat_not_le_zero h).elim
    | zero => exact ⟨⟨.nat, .rfl⟩, ⟨.zero, .rfl⟩, ⟨.zero, .rfl⟩⟩
    | succ => have .zero h := hM; exact (TShape.succ_not_le_zero h).elim
    | id => have .zero h := hM; exact (TShape.id_not_le_zero h).elim
    | refl => have .zero h := hM; exact (TShape.refl_not_le_zero h).elim
  | @succDF Γ nTm nTm' hnEq ihn =>
    cases hmem.unfold with
    | bot hm =>
      refine .bot (fun _ W => ?_) hm
      cases hA with | bot => exact (LR _).bot_ty | nat h
      cases hm.unfold with
      | bot => exact (LR _).bot_ty
      | sort => exact (TShape.sort_not_le_nat h).elim
      | unit => exact (TShape.unit_not_le_nat h).elim
      | forallE => exact (TShape.forallE_not_le_nat h).elim
      | sigma => exact (TShape.sigma_not_le_nat h).elim
      | id => exact (TShape.id_not_le_nat h).elim
      | nat => exact ⟨⟨.nat, .rfl⟩, ⟨.nat, .rfl⟩⟩
    | sort => cases n <;> (have .nat h := hA; exact (TShape.sort_not_le_nat h).elim)
    | unit => have .succ _ h := hM; exact (TShape.unit_not_le_succ h).elim
    | forallE => have .nat h := hA; exact (TShape.sort_not_le_nat h).elim
    | lam => have .nat h := hA; exact (TShape.forallE_not_le_nat h).elim
    | sigma => have .nat h := hA; exact (TShape.sort_not_le_nat h).elim
    | pair => have .nat h := hA; exact (TShape.sigma_not_le_nat h).elim
    | nat => have .succ _ h := hM; exact (TShape.nat_not_le_succ h).elim
    | zero => have .succ _ h := hM; exact (TShape.zero_not_le_succ h).elim
    | id => have .succ _ h := hM; exact (TShape.id_not_le_succ h).elim
    | refl => have .succ _ h := hM; exact (TShape.refl_not_le_succ h).elim
    | @succ k v' hv'_succ
    refine .wf₀ fun hΓ₀ => .fits fun hFits => ?_
    obtain ⟨n_x, m_x, a_x, hle_nx, hle_m, LE_mx, LE_ax, hty_mx⟩ :=
      (LE_Interp.sound hnEq.succDF hFits).2 hM |>.out
    obtain ⟨n_a, ha_nat⟩ := LE_ax.le_nat
    let k'' := max n_x n_a
    have hkx : n_x ≤ k''+1 := Nat.le_succ_of_le (Nat.le_max_left _ _)
    have hka : n_a+1 ≤ k''+1 := Nat.succ_le_succ (Nat.le_max_right _ _)
    have hty_mx_nat : (m_x.lift (k''+1)).HasType .nat := by
      refine .mono_r ?_ .nat <| (WShape.HasType.lift hkx).2 hty_mx
      exact WShape.lift_nat (Nat.le_max_right _ _) ▸ (TShape.LE.def hkx hka).1 ha_nat
    have hm_le_lift := hle_m.trans (TShape.lift_eqv (a := m_x.T) hkx).2
    obtain hbot | hzero | ⟨v_p, heq_succ, hv_p_ts⟩ := hty_mx_nat.nat_r
    · cases TShape.succ_not_le_bot (hbot ▸ hm_le_lift)
    · cases TShape.succ_not_le_zero (hzero ▸ hm_le_lift)
    have hvp_ty : (v_p.lift (k''+1)).HasType .nat := by
      match k'', v_p, hv_p_ts with
      | 0, ⟨.bot, _⟩, _ => exact .bot' .nat
      | k'''+1, v_p_pat, hv_p_pat =>
        rw [← WShape.lift_nat (Nat.le_succ k''')]
        exact (WShape.HasType.lift (Nat.le_succ _)).2 hv_p_pat
    suffices ∀ {tmA tmB : Term},
        Γ₀ ⊢ tmA ≡ tmB : Term.nat →
        (LR (n := k''+1) hΓ₀).TmEq tmA tmB .nat
          (v_p.lift (k''+1) : WShape (k''+1)) (WShape.nat : WShape (k''+1)) →
        (LR hΓ₀).TmEq (Term.succ tmA) (Term.succ tmB) Term.nat (.succ v') WShape.nat by
      have .succ LE_vx h_le_x := heq_succ ▸ LE_mx.lift hkx
      have LE_vp := LE_vx.mono (TShape.succ_le_succ.1 h_le_x)
      have Ad_inner := ihn (LE_vp.lift (Nat.le_succ _)) .nat' hvp_ty
      refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
      · exact this (hnEq.hasType.1.subst' W.wf₀ W.toSubstEq) (Ad_inner.1 W).1
      · exact this (hnEq.hasType.2.subst' W.wf₀ W.toSubstEq) (Ad_inner.1 W).2
      · exact this (hnEq.subst' W.wf₀ W.toSubstEq) (Ad_inner.2 W)
    intro tmA tmB hnEq h_inner
    refine (LRS.TmEq.succ_nat (v := v')).mpr ⟨⟨.nat, .rfl⟩, ?_⟩
    refine ⟨_, _, ⟨hnEq.succDF.hasType.1, .rfl⟩, ⟨hnEq.succDF.hasType.2, .rfl⟩, hnEq, ?_⟩
    cases k with | zero => trivial | succ k'
    change v'.HasType .nat at hv'_succ
    let K := max k' k'' + 1
    have le1 : k''+1 ≤ K := Nat.succ_le_succ (Nat.le_max_right _ _)
    have le2 : k'+1 ≤ K := Nat.succ_le_succ (Nat.le_max_left _ _)
    have hnat_K1 := WShape.lift_nat (Nat.le_max_left k' k'')
    have hnat_K2 := WShape.lift_nat (Nat.le_max_right k' k'')
    refine (LR.TmEq.lift le2 hv'_succ).mp (hnat_K1 ▸ ?_)
    have hvp_ll := WShape.lift_lift (s := v_p) (n₃ := K) (.inl (Nat.le_succ k''))
    have hle_v' := TShape.succ_le_succ.1 (heq_succ ▸ hm_le_lift)
    refine (LR (n := K) hΓ₀).mono_l ((TShape.LE.def le2 (Nat.le_of_succ_le le1)).1 hle_v') ?_ ?_ ?_
    · have h := (WShape.HasType.lift le2).2 hv'_succ; rwa [hnat_K1] at h
    · have h := (WShape.HasType.lift le1).2 hvp_ty; rwa [hvp_ll, hnat_K2] at h
    · have h := (LR.TmEq.lift le1 hvp_ty).mpr h_inner; rwa [hvp_ll, hnat_K2] at h
  | @natCaseDF Γ C C' v M M' aTm aTm' b b' hCC' hMM' haa' hbb' hCMinst ihC ihM iha ihb ihCM =>
    refine .wf fun hΓ => .wf₀ fun hΓ₀ => ?_
    have hΓ₀_nat : ⊢ Term.nat :: Γ₀ := ⟨hΓ₀, _, .nat⟩
    have hΓ_nat : ⊢ Term.nat :: Γ := ⟨hΓ, _, .nat⟩
    have cons_nat := LR.Adequate.cons (hΓ₀ := hΓ₀) (Γ := Γ) .nat .nat
    suffices ∀ {C_L C_R M_L M_R aTm_L aTm_R b_L b_R : Term} {σ σ' : Subst}
        (W : SubstWF Γ₀ σ σ' Γ ρ)
        (hCC' : .nat :: Γ ⊢ C_L ≡ C_R : .sort v)
        (hMM' : Γ ⊢ M_L ≡ M_R : .nat)
        (haa' : Γ ⊢ aTm_L ≡ aTm_R : C.inst .zero)
        (hbb' : .nat :: Γ ⊢ b_L ≡ b_R : (C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0)))
        (hCMinst : Γ ⊢ C_L.inst M_L ≡ C_R.inst M_R : .sort v)
        (hX : LE_Interp ρ m.T (C_L.natCase M_L aTm_L b_L))
        (hA : LE_Interp ρ a.T (C_L.inst M_L))
        (hM : Γ ⊢ M ≡ M_L : .nat)
        (hC : .nat :: Γ ⊢ C ≡ C_L : .sort v)
        (ihM : ∀ {n'} {mM aM : WShape n'}, LE_Interp ρ mM.T M_L →
          LE_Interp ρ aM.T .nat → mM.HasType aM →
          Adequate Γ₀ Γ ρ M_L M_R .nat mM aM ∧
          Adequate Γ₀ Γ ρ M_L M .nat mM aM)
        (iha : ∀ {n'} {ma' aa : WShape n'}, LE_Interp ρ ma'.T aTm_L →
          LE_Interp ρ aa.T (C.inst .zero) → ma'.HasType aa →
          Adequate Γ₀ Γ ρ aTm_L aTm_R (C.inst .zero) ma' aa)
        (ihb : ∀ {ρ' : Valuation} {n'} {mb ab : WShape n'} (_ : ρ'.Fits Γ₀ (.nat :: Γ)),
          LE_Interp ρ' mb.T b_L →
          LE_Interp ρ' ab.T ((C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0))) →
          mb.HasType ab →
          Adequate Γ₀ (.nat :: Γ) ρ' b_L b_R
            ((C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0))) mb ab),
        (LR hΓ₀).TmEq
          ((Term.natCase C_L M_L aTm_L b_L).subst σ)
          ((Term.natCase C_R M_R aTm_R b_R).subst σ')
          ((C.inst M).subst σ) m a by
      refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
      · exact this W hCC'.hasType.1 hMM'.hasType.1 haa'.hasType.1 hbb'.hasType.1 hCMinst.hasType.1
          hM hA hMM'.hasType.1 hCC'.hasType.1
          (fun h1 h2 h3 => ⟨(ihM h1 h2 h3).left, (ihM h1 h2 h3).left⟩)
          (fun h1 h2 h3 => (iha h1 h2 h3).left)
          (fun _ h1 h2 h3 => (ihb h1 h2 h3).left)
      · exact this W hCC'.hasType.2 hMM'.hasType.2 haa'.hasType.2 hbb'.hasType.2 hCMinst.hasType.2
          ((LE_Interp.sound (.natCaseDF₀ W.wf hCC' hMM' haa' hbb') W.fits).1.1 hM)
          ((LE_Interp.sound hCMinst W.fits).1.1 hA)
          hMM' hCC'
          (fun h1 h2 h3 =>
            have H := (ihM ((LE_Interp.sound hMM' W.fits).1.2 h1) h2 h3).symm hMM'; ⟨H.left, H⟩)
          (fun h1 h2 h3 => ((iha ((LE_Interp.sound haa' W.fits).1.2 h1) h2 h3).symm haa').left)
          (fun hρ' h1 h2 h3 =>
            ((ihb ((LE_Interp.sound hbb' hρ').1.2 h1) h2 h3).symm hbb').left)
      · exact this W hCC' hMM' haa' hbb' hCMinst hM hA hMM'.hasType.1 hCC'.hasType.1
          (fun h1 h2 h3 => ⟨ihM h1 h2 h3, (ihM h1 h2 h3).left⟩) iha (fun _ => ihb)
    clear hM; intro C_L C_R M_L M_R aTm_L aTm_R b_L b_R σ σ' W
      hCC' hMM' haa' hbb' hCMinst hX hA hM hC ihM' iha ihb
    have Wf_cons {x a} := W.fits.cons
      (InterpTyped.hsort (LE_Interp.sound .nat W.fits).2) (x := x) (a := a)
    cases hX with
    | bot =>
      refine (LR _).bot hmem.isType ?_
      have ⟨_, _, _, h1, h2, h3, h4, h5⟩ := (LE_Interp.sound hCMinst W.fits).2 hA |>.out
      refine toValTy h1 h2 hmem.isType h4 h5 ((ihCM ?_ h4 h5).1 W.left).1
      have ⟨_, a1, a2⟩ := LE_Interp.inst.1 h3
      have ⟨_, _, _, b1, b2, b3, b4, b5⟩ := (LE_Interp.sound hMM' W.fits).2 a2 |>.out
      exact LE_Interp.inst.2 ⟨_, (LE_Interp.sound hC (Wf_cons b4 b5.T)).1.2
        (a1.mono_l (Valuation.LE.push.2 ⟨.rfl, b2⟩)), (LE_Interp.sound hM W.fits).1.2 b3⟩
    | @natCase_zero _ n_z _ _ _ _ _ hM_z ha_z =>
      have Ad_M := (ihM' hM_z (.nat' (n := n_z)) .zero).1
      obtain ⟨a_M, hCa_M, hM_a⟩ := LE_Interp.inst.1 hA
      obtain ⟨n_x, m_x, a_x, _, hle_am, LE_mx, LE_ax, hty_mx⟩ :=
        (LE_Interp.sound hMM' W.fits).2 hM_a |>.out
      obtain ⟨n_a, ha_nat⟩ := LE_ax.le_nat
      let k := max n_x n_a
      have hnk_k1 : n_x ≤ k+1 := Nat.le_succ_of_le (Nat.le_max_left _ _)
      have hna_k1 : n_a + 1 ≤ k+1 := Nat.succ_le_succ (Nat.le_max_right _ _)
      have hCa0 := (LE_Interp.sound hC (Wf_cons (.nat' (n := n_z)) WShape.HasType.zero.T)).1.2 <| by
        refine hCa_M.mono_l (Valuation.LE.push.2 ⟨.rfl, hle_am.trans ?_⟩)
        refine (TShape.lift_eqv hnk_k1).2.trans <| (WShape.LE.T ?_).trans TShape.zero_eqv
        have : (m_x.lift (k+1) : WShape (k+1)).HasType .nat := by
          refine .mono_r ?_ .nat ((WShape.HasType.lift hnk_k1).2 hty_mx)
          exact WShape.lift_nat (Nat.le_max_right ..) ▸ (TShape.LE.def hnk_k1 hna_k1).1 ha_nat
        obtain h_bot | h_zero | ⟨v_x, h_succ, _⟩ := this.nat_r
        · exact h_bot ▸ WShape.bot_le
        · exact h_zero ▸ .rfl
        · cases WShape.Compat.T_iff.2 <|
            (h_succ ▸ LE_mx.lift hnk_k1).compat (hM_z.mono TShape.zero_eqv)
      have ⟨⟨_, hM_L_σ_z, _⟩, ⟨_, _, hM_R_σ'_z⟩⟩ := Ad_M.1 W
      specialize iha ha_z (LE_Interp.inst.2 ⟨_, hCa0, .zero'⟩) hmem
      have hCM := IsDefEq.instDF W.wf .nat .sort hC hM
      have haa'_L := IsDefEq.instDF W.wf .nat .sort hC .zero |>.defeqDF haa'
      have hbb'_L := IsDefEq.instDF hΓ_nat .nat .sort (hC.weak' (.cons (.skip .refl)))
        (.succDF (.bvar₀ hΓ_nat .zero)) |>.defeqDF hbb'
      refine ((LR hΓ₀).whr ?_ ?_ ?_).2 <| (LR hΓ₀).conv ?_ <|
        (LR hΓ₀).trans (haa'.subst' W.wf₀ W.left.toSubstEq)
          (haa'.hasType.2.subst' W.wf₀ W.toSubstEq) (iha.2 W.left) (iha.1 W).2
      · have hC1 := hCC'.hasType.1.subst' hΓ₀_nat (W.left.toSubstEq.lift .nat .nat)
        have ha1 := subst_inst ▸ haa'_L.hasType.1.subst' W.wf₀ W.left.toSubstEq
        have hb1 := hbb'_L.hasType.1.subst' hΓ₀_nat (W.left.toSubstEq.lift .nat .nat)
        rw [subst_succ_branch_swap] at hb1
        refine ⟨?_, hM_L_σ_z.2.natCase.tail .natCase_zero⟩
        refine (hCM.subst' W.wf₀ W.left.toSubstEq).symm.defeqDF <|
          subst_inst ▸ (hC1.natCaseDF₀ hΓ₀ hM_L_σ_z.1 ha1 hb1).trans ?_
        refine .defeqDF (.instDF hΓ₀ .nat .sort hC1 hM_L_σ_z.1.symm) ?_
        exact .natCase_zero₀ hΓ₀ hC1 ha1 hb1
      · have hC1 := hCC'.subst' hΓ₀_nat (W.symm.left.toSubstEq.lift .nat .nat)
        have ha1 := IsDefEq.instDF hΓ₀ .nat .sort hC1 .zero
          |>.defeqDF (subst_inst ▸ haa'_L.hasType.2.subst' W.wf₀ W.symm.left.toSubstEq)
        have hb1 := IsDefEq.instDF hΓ₀_nat .nat .sort (hC1.weak' (.cons (.skip .refl))) <|
          .succDF (IsDefEq.bvar₀ hΓ₀_nat Lookup.zero)
        rw [← subst_succ_branch_swap] at hb1
        have hb2 := hb1.defeqDF <|
          hbb'_L.hasType.2.subst' hΓ₀_nat (W.symm.left.toSubstEq.lift .nat .nat)
        have hNC1 := hC1.hasType.2.natCaseDF₀ hΓ₀ hM_R_σ'_z.1 ha1 hb2
        refine ⟨?_, hM_R_σ'_z.2.natCase.tail .natCase_zero⟩
        refine (hCM.hasType.1.subst' W.wf₀ W.toSubstEq).symm.defeqDF ?_
        refine .defeqDF (u := v) ?_ (hNC1.trans ?_)
        · exact subst_inst ▸ ((hCM.trans hCMinst).subst' W.wf₀ W.symm.left.toSubstEq).symm
        · refine (IsDefEq.instDF hΓ₀ .nat .sort hC1.hasType.2 hM_R_σ'_z.1.symm).defeqDF ?_
          exact hC1.hasType.2.natCase_zero₀ hΓ₀ ha1 hb2
      · refine (hCM.subst' W.wf₀ W.left.toSubstEq).symm.defeqDF ?_
        exact (hCC'.natCaseDF hMM' haa'_L hbb'_L hCMinst).subst' W.wf₀ W.toSubstEq
      · have hMσ_z := ((ihM ((LE_Interp.sound hM W.fits).1.2 hM_z) .nat' .zero).1 W).1.2.1
        have hv_zero_Mσ : (LR hΓ₀).TmEq (n := n_z+1) .zero (M.subst σ) .nat .zero .nat :=
          LRS.TmEq.zero_nat (IH := LR (n := n_z) hΓ₀).2 ⟨⟨.nat, .rfl⟩, ⟨.zero, .rfl⟩, hMσ_z⟩
        have W_conv := cons_nat .zero .nat' hMσ_z.1.symm hv_zero_Mσ W.left
        obtain ⟨_, _, _, le_lvl, le_aT_mCT, iC, iv, hmC⟩ :=
          (LE_Interp.sound hC.hasType.1 W_conv.fits).2 hCa0 |>.out
        rw [subst_inst, subst_inst, Term.subst, inst_lift_cons, inst_lift_cons]
        exact LR.toValTy le_lvl le_aT_mCT hmem.isType iv hmC ((ihC iC iv hmC).1 W_conv).1
    | @natCase_succ _ n_s v_pred _ _ _ _ _ hM_s hb_s =>
      obtain ⟨a_M, hCa_M, hM_a⟩ := LE_Interp.inst.1 hA
      obtain ⟨n_x, m_x, a_x, _, hle_join, LE_mx, LE_ax, hty_mx⟩ :=
        (LE_Interp.sound hMM' W.fits).2 (hM_s.join' hM_a) |>.out
      obtain ⟨n_a, ha_nat⟩ := LE_ax.le_nat
      let k := max n_x n_a
      have hkx : n_x ≤ k+1 := Nat.le_succ_of_le (Nat.le_max_left _ _)
      have hka : n_a+1 ≤ k+1 := Nat.succ_le_succ (Nat.le_max_right _ _)
      have hty_mx_nat : (m_x.lift (k+1)).HasType .nat := by
        refine .mono_r ?_ .nat ((WShape.HasType.lift hkx).2 hty_mx)
        exact WShape.lift_nat (Nat.le_max_right _ _) ▸ (TShape.LE.def hkx hka).1 ha_nat
      have hJ := (TShape.Join.mk (hM_s.compat hM_a)).le
      have hle_succ_lift := (hJ.1.trans hle_join).trans (TShape.lift_eqv hkx).2
      have hle_aM_lift := (hJ.2.trans hle_join).trans (TShape.lift_eqv hkx).2
      obtain hbot | hzero | ⟨v_p, heq_succ, hv_p_ts⟩ := hty_mx_nat.nat_r
      · cases congrArg (·.1) <| TShape.le_bot.mp ((hbot ▸ hle_succ_lift).trans TShape.bot_eqv.1)
      · cases TShape.succ_not_le_zero (hzero ▸ hle_succ_lift)
      have hvp_succ_ty := WShape.HasType.succ hv_p_ts
      have hvp_ty : (v_p.lift (k+1)).HasType .nat := by
        match k, v_p, hv_p_ts with
        | 0, ⟨.bot, _⟩, _ => exact WShape.HasType.bot' WShape.HasType.nat
        | k'+1, v_p_pat, hv_p_pat =>
          rw [← WShape.lift_nat (Nat.le_succ k')]
          exact (WShape.HasType.lift (Nat.le_succ _)).2 hv_p_pat
      have Ad_M := ihM' (heq_succ ▸ LE_mx.lift hkx) (.nat' (n := k)) hvp_succ_ty
      have hCa_succ := (LE_Interp.sound hC (Wf_cons (.nat' (n := k)) hvp_succ_ty.T)).1.2 <|
        hCa_M.mono_l (Valuation.LE.push.2 ⟨.rfl, heq_succ ▸ hle_aM_lift⟩)
      have ihb := by
        refine ihb (Wf_cons (.nat' (n := k)) hvp_ty.T) ?_ ?_ hmem
        · refine hb_s.mono_l (Valuation.LE.push.2 ⟨.rfl, ?_⟩)
          have := TShape.succ_le_succ.1 (heq_succ ▸ hle_succ_lift)
          exact this.trans (TShape.lift_eqv (Nat.le_succ k)).2
        · refine LE_Interp.inst.2 ⟨_, ?_, LE_Interp.succ' <|
            LE_Interp.bvar0.mono (TShape.lift_eqv (Nat.le_succ k)).2⟩
          exact (LE_Interp.weak'_iff (l := .cons (.skip .refl)) (by rintro ⟨⟩ <;> rfl)).2 hCa_succ
      have ⟨_, Mσ_pred, M'σ_pred, hMσ_red, hM'σ'_red, hMσ_pred_eq, hTmEqNat_pred⟩ :=
        (LRS.TmEq.succ_nat (v := v_p)).1 <| (LR hΓ₀).trans (hMM'.subst' W.wf₀ W.left.toSubstEq)
          (hMM'.hasType.2.subst' W.wf₀ W.toSubstEq) (Ad_M.1.2 W.left) (Ad_M.1.1 W).2
      have : (LR (n := k+1) hΓ₀).TmEq Mσ_pred M'σ_pred Term.nat (v_p.lift (k+1)) .nat := by
        match k, v_p, hv_p_ts, hTmEqNat_pred with
        | 0, ⟨.bot, _⟩, _, _ =>
          show (LR (n := 0+1) hΓ₀).TmEq Mσ_pred M'σ_pred Term.nat
            (WShape.lift (0+1) (⟨Shape.bot, trivial⟩ : WShape 0)) (WShape.nat : WShape (0+1))
          exact ⟨⟨.nat, .rfl⟩, trivial⟩
        | k'+1, v_p_pat, hv_p_pat, h =>
          have hma : v_p_pat.HasType (WShape.nat : WShape (k'+1)) := by
            simp only [WShape.HasTypeSucc, WShape.HasType, WShape.nat] at hv_p_pat ⊢
            exact hv_p_pat
          exact (LR.TmEq.lift (Nat.le_succ _) hma).mpr h
      have W_ext := cons_nat hvp_ty (.nat' (n := k)) hMσ_pred_eq this W
      have hCM := IsDefEq.instDF W.wf .nat .sort hC hM
      have haa'_L := IsDefEq.instDF W.wf .nat .sort hC .zero |>.defeqDF haa'
      have hbb'_L := IsDefEq.instDF hΓ_nat .nat .sort (hC.weak' (.cons (.skip .refl)))
        (.succDF (.bvar₀ hΓ_nat .zero)) |>.defeqDF hbb'
      have := (LR hΓ₀).trans (hbb'.subst' W_ext.left.wf₀ W_ext.left.toSubstEq)
        (hbb'.hasType.2.subst' W_ext.wf₀ W_ext.toSubstEq)
        (ihb.2 W_ext.left) (ihb.1 W_ext).2
      rw [← inst_lift_cons, ← inst_lift_cons, ← inst_lift_cons, subst_succ_branch_swap,
        lift_cons_skip_inst_succ_inst] at this
      refine ((LR hΓ₀).whr ?_ ?_ ?_).2 <| (LR hΓ₀).conv ?_ this
      · have hC1 := hCC'.hasType.1.subst' hΓ₀_nat (W.left.toSubstEq.lift .nat .nat)
        have ha1 := subst_inst ▸ haa'_L.hasType.1.subst' W.wf₀ W.left.toSubstEq
        have hb1 := hbb'_L.hasType.1.subst' hΓ₀_nat (W.left.toSubstEq.lift .nat .nat)
        rw [subst_succ_branch_swap] at hb1
        refine ⟨?_, hMσ_red.2.natCase.tail .natCase_succ⟩
        refine (hCM.subst' W.wf₀ W.left.toSubstEq).symm.defeqDF <|
          subst_inst ▸ (hC1.natCaseDF₀ hΓ₀ hMσ_red.1 ha1 hb1).trans ?_
        refine .defeqDF (.instDF hΓ₀ .nat .sort hC1 hMσ_red.1.symm) ?_
        exact .natCase_succ₀ hΓ₀ hC1 hMσ_pred_eq.hasType.1 ha1 hb1
      · have hC1 := hCC'.subst' hΓ₀_nat (W.symm.left.toSubstEq.lift .nat .nat)
        have ha1 := IsDefEq.instDF hΓ₀ .nat .sort hC1 .zero
          |>.defeqDF (subst_inst ▸ haa'_L.hasType.2.subst' W.wf₀ W.symm.left.toSubstEq)
        have hb1 := IsDefEq.instDF hΓ₀_nat .nat .sort (hC1.weak' (.cons (.skip .refl))) <|
          .succDF (IsDefEq.bvar₀ hΓ₀_nat .zero)
        rw [← subst_succ_branch_swap] at hb1
        have hb2 := hb1.defeqDF <|
          hbb'_L.hasType.2.subst' hΓ₀_nat (W.symm.left.toSubstEq.lift .nat .nat)
        have hNC1 := hC1.hasType.2.natCaseDF₀ hΓ₀ hM'σ'_red.1 ha1 hb2
        refine ⟨?_, hM'σ'_red.2.natCase.tail .natCase_succ⟩
        refine (hCM.hasType.1.subst' W.wf₀ W.toSubstEq).symm.defeqDF ?_
        refine .defeqDF (u := v) ?_ (hNC1.trans ?_)
        · exact subst_inst ▸ ((hCM.trans hCMinst).subst' W.wf₀ W.symm.left.toSubstEq).symm
        · refine (IsDefEq.instDF hΓ₀ .nat .sort hC1.hasType.2 hM'σ'_red.1.symm).defeqDF ?_
          exact hC1.hasType.2.natCase_succ₀ hΓ₀ hMσ_pred_eq.hasType.2 ha1 hb2
      · refine (hCM.subst' W.wf₀ W.left.toSubstEq).symm.defeqDF ?_
        exact (hCC'.natCaseDF hMM' haa'_L hbb'_L hCMinst).subst' W.wf₀ W.toSubstEq
      · have MLσ := hM.symm.subst' W.wf₀ W.left.toSubstEq
        have := ((LR _).whr hMσ_red ⟨MLσ.hasType.2, .rfl⟩ MLσ).1 <| Ad_M.2.2 W.left
        have W_conv := cons_nat hvp_succ_ty .nat' (hMσ_red.1.symm.trans MLσ) this W.left
        rw [subst_inst, inst_lift_cons, inst_lift_cons]
        have ⟨_, _, _, le_lvl, le_aT_mCT, iC, iv, hmC⟩ :=
          (LE_Interp.sound hC.hasType.1 W_conv.fits).2 hCa_succ |>.out
        exact LR.toValTy le_lvl le_aT_mCT hmem.isType iv hmC ((ihC iC iv hmC).1 W_conv).1
  | @natCase_zero Γ C v aTm bTm HC Ha Hb _HLHS ihC iha ihb ih_LHS =>
    refine ⟨fun _ _ W => ⟨((ih_LHS hM hA hmem).1 W).1, ((iha ?_ hA hmem).1 W).2⟩, fun σ W => ?_⟩
    · exact (LE_Interp.sound (.natCase_zero₀ W.wf HC Ha Hb) W.fits).1.1 hM
    have hMeq := HC.natCase_zero₀ W.wf Ha Hb |>.subst' W.wf₀ W.toSubstEq
    refine ((LR _).whr ⟨hMeq, .tail .rfl .natCase_zero⟩ ⟨?_, .rfl⟩ hMeq).2 ((iha ?_ hA hmem).2 W)
    · exact Ha.subst' W.wf₀ W.toSubstEq
    · exact (LE_Interp.sound (.natCase_zero₀ W.wf HC Ha Hb) W.fits).1.1 hM
  | @natCase_succ Γ C v nTm aTm bTm HC Hn Ha Hb _ Hbn _ ihn _ _ ih_LHS ih_bn =>
    refine ⟨fun _ _ W => ⟨((ih_LHS hM hA hmem).1 W).1, ((ih_bn ?_ hA hmem).1 W).2⟩, fun σ W => ?_⟩
    · exact (LE_Interp.sound (.natCase_succ₀ W.wf HC Hn Ha Hb) W.fits).1.1 hM
    have hMeq := HC.natCase_succ₀ W.wf Hn Ha Hb |>.subst' W.wf₀ W.toSubstEq
    refine ((LR _).whr ⟨hMeq, ?_⟩ ⟨?_, .rfl⟩ hMeq).2 ((ih_bn ?_ hA hmem).2 W)
    · exact subst_inst ▸ .tail .rfl .natCase_succ
    · exact Hbn.subst' W.wf₀ W.toSubstEq
    · exact (LE_Interp.sound (.natCase_succ₀ W.wf HC Hn Ha Hb) W.fits).1.1 hM
  | @YDF _ A A' u b b' HA Hb Hb' ihA ihb ihb' =>
    refine .fits fun W => ?_
    obtain ⟨_, m', a', le, _, ha', hmem', adq⟩ := LR.adequacy_Y W HA Hb Hb' ihA ihb hM
    refine adq.mono_r le hmem hmem' (hA.compat ha') (fun {σ σ'} W' => ?_)
    have ⟨_, _, _, le_n, le_a, hA0, hSort, hmem0⟩ :=
      (LE_Interp.sound HA.hasType.1 W'.fits).2 hA |>.out
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

/-- Unit/Π disjointness: a unit type is never definitionally equal to a Π-type
(hence, symmetrically, no Π-type is a unit type). Proved from the Π side:
`.unit r` is already a WHNF, so it cannot weak-head-reduce to a `forallE`. -/
theorem forallE_unit_inv (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.unit r ≡ Term.forallE A B : .sort s :=
  fun H => have ⟨_, _, red, _⟩ := forallE_whRed_l hΓ H; nomatch WHNF.unit.whRedS red

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

/-- Unit/Σ disjointness: a unit type is never definitionally equal to a Σ-type. -/
theorem sigma_unit_inv (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.unit r ≡ Term.sigma A B : .sort true :=
  fun H => have ⟨_, _, red, _⟩ := sigma_whRed_l hΓ H; nomatch WHNF.unit.whRedS red

/-- Π/Σ disjointness: a Π-type is never definitionally equal to a Σ-type. -/
theorem forallE_sigma_inv (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.forallE A B ≡ Term.sigma A₁ B₁ : .sort true :=
  fun H => have ⟨_, _, H, _⟩ := sigma_whRed_l hΓ H; nomatch WHNF.forallE.whRedS H

/-- Nat-type whr-inversion -/
theorem nat_whRed_l (hΓ : ⊢ Γ) (d : Γ ⊢ A ≡ Term.nat : .sort true) :
    A ⤳* .nat := by
  have hNat : LE_Interp .nil (WShape.T (n := 1) WShape.nat) .nat := .nat' (n := 0)
  have hmem : WShape.HasType (n := 1) WShape.nat WShape.type := WShape.HasType.nat
  have h := LR.adequacy d ((LE_Interp.sound d .nil).1.2 hNat) (.sort TShape.sort_eqv.1) hmem
    |>.2 (.id hΓ)
  -- TmEq A .nat (.sort true) WShape.nat (.sort true)
  -- At type-shape (.sort true), unfolds to ∃ u, .sort true ⤳* .sort u ∧ TyEq A .nat WShape.nat,
  -- which at element-shape WShape.nat unfolds to ValTyNat2 = ⟨A ⤳* .nat, .nat ⤳* .nat⟩.
  obtain ⟨_, _, redA, _⟩ := subst_id ▸ subst_id ▸ subst_id ▸ h
  exact redA.2

/-- Sort/Nat disjointness: a sort is never definitionally equal to `.nat`. -/
theorem sort_nat_inv (hΓ : ⊢ Γ) : ¬ Γ ⊢ Term.sort u ≡ Term.nat : .sort true :=
  fun H => nomatch WHNF.sort.whRedS (nat_whRed_l hΓ H)

/-- Unit/Nat disjointness: a unit type is never definitionally equal to `.nat`. -/
theorem nat_unit_inv (hΓ : ⊢ Γ) : ¬ Γ ⊢ Term.unit r ≡ Term.nat : .sort true :=
  fun H => nomatch WHNF.unit.whRedS (nat_whRed_l hΓ H)

/-- Π/Nat disjointness: a Π-type is never definitionally equal to `.nat`. -/
theorem forallE_nat_inv (hΓ : ⊢ Γ) :
    ¬ Γ ⊢ Term.forallE A B ≡ Term.nat : .sort true :=
  fun H => nomatch WHNF.forallE.whRedS (nat_whRed_l hΓ H)

/-- Σ/Nat disjointness: a Σ-type is never definitionally equal to `.nat`. -/
theorem sigma_nat_inv (hΓ : ⊢ Γ) :
    ¬ Γ ⊢ Term.sigma A B ≡ Term.nat : .sort true :=
  fun H => nomatch WHNF.sigma.whRedS (nat_whRed_l hΓ H)

/-- Id-type whr-inversion -/
theorem id_whRed_l (hΓ : ⊢ Γ) (d : Γ ⊢ A₀ ≡ Term.id A₁ a₁ b₁ : .sort true) :
    ∃ A₀_inner a₀ b₀, A₀ ⤳* .id A₀_inner a₀ b₀ ∧
      ∃ u, Γ ⊢ A₀_inner ≡ A₁ : .sort u ∧
        Γ ⊢ a₀ ≡ a₁ : A₀_inner ∧ Γ ⊢ b₀ ≡ b₁ : A₀_inner := by
  have hId : LE_Interp .nil (WShape.T (n := 1) (.id .bot .bot .bot)) (.id A₁ a₁ b₁) :=
    .id .bot .bot .bot .rfl
  have hmem : WShape.HasType (n := 1) (.id .bot .bot .bot) .type := by
    refine WShape.HasType.id_l.2 ⟨WShape.HasTypeId.def.2 ?_, rfl⟩
    exact ⟨.bot' (.bot' .sort), .bot' (.bot' .sort)⟩
  have := LR.adequacy d ((LE_Interp.sound d .nil).1.2 hId) (.sort TShape.sort_eqv.1) hmem
    |>.2 (.id hΓ)
  obtain ⟨_, _, _, _, _, _, _, _, _, redA₀, redId, convA, conva, convb, _, _, _⟩ :=
    subst_id ▸ subst_id ▸ subst_id ▸ this
  cases WHNF.id.whRedS redId.2
  exact ⟨_, _, _, redA₀.2, _, convA, conva, convb⟩

/-- Id–Id injectivity: if two Id types are definitionally equal,
their carrier and endpoints are each definitionally equal. -/
theorem id_inv (hΓ : ⊢ Γ)
    (H : Γ ⊢ Term.id A₀ a₀ b₀ ≡ Term.id A₁ a₁ b₁ : .sort true) :
    ∃ u, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ Γ ⊢ a₀ ≡ a₁ : A₀ ∧ Γ ⊢ b₀ ≡ b₁ : A₀ := by
  have ⟨_, _, _, red, H⟩ := id_whRed_l hΓ H
  cases WHNF.id.whRedS red; exact H

/-- Sort/Id disjointness: a sort is never definitionally equal to an Id-type. -/
theorem sort_id_inv (hΓ : ⊢ Γ) : ¬Γ ⊢ .sort u ≡ Term.id A₁ a₁ b₁ : .sort true :=
  fun H => have ⟨_, _, _, H, _⟩ := id_whRed_l hΓ H; nomatch WHNF.sort.whRedS H

/-- Π/Id disjointness: a Π-type is never definitionally equal to an Id-type. -/
theorem forallE_id_inv (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.forallE A B ≡ Term.id A₁ a₁ b₁ : .sort true :=
  fun H => have ⟨_, _, _, H, _⟩ := id_whRed_l hΓ H; nomatch WHNF.forallE.whRedS H

/-- Σ/Id disjointness: a Σ-type is never definitionally equal to an Id-type. -/
theorem sigma_id_inv (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.sigma A B ≡ Term.id A₁ a₁ b₁ : .sort true :=
  fun H => have ⟨_, _, _, H, _⟩ := id_whRed_l hΓ H; nomatch WHNF.sigma.whRedS H

/-- Unit/Id disjointness: a unit type is never definitionally equal to an Id-type. -/
theorem unit_id_inv (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.unit r ≡ Term.id A₁ a₁ b₁ : .sort true :=
  fun H => have ⟨_, _, _, H, _⟩ := id_whRed_l hΓ H; nomatch WHNF.unit.whRedS H

/-- Nat/Id disjointness: `.nat` is never definitionally equal to an Id-type. -/
theorem nat_id_inv (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.nat ≡ Term.id A₁ a₁ b₁ : .sort true :=
  fun H => have ⟨_, _, _, H, _⟩ := id_whRed_l hΓ H; nomatch WHNF.nat.whRedS H
