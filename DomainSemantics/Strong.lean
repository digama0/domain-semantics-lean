import DomainSemantics.TypingLemmas

namespace DomainSemantics
namespace VEnv

open VExpr

section
set_option hygiene false
section
local notation:65 Γ " ⊢ " e " : " A:30 => IsDefEqStrong env uvars Γ e e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:30 => IsDefEqStrong env uvars Γ e1 e2 A

inductive IsDefEqStrong (env : VEnv) (uvars : Nat) : List VExpr → VExpr → VExpr → VExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ A : .sort u → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  | sortDF : Γ ⊢ .sort l : .sort true
  | appDF :
    Γ ⊢ A : .sort u →
    Γ ⊢ f ≡ f' : .forallE A B →
    Γ ⊢ a ≡ a' : A →
    Γ ⊢ B.inst a ≡ B.inst a' : .sort v →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | lamDF :
    Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ B : .sort v →
    A::Γ ⊢ body ≡ body' : B →
    A'::Γ ⊢ body ≡ body' : B →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF :
    Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : .sort v →
    A'::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort v
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B
  | beta :
    Γ ⊢ A : .sort u → A::Γ ⊢ e : B → Γ ⊢ e' : A →
    Γ ⊢ .app (.lam A e) e' : B.inst e' →
    Γ ⊢ e.inst e' : B.inst e' →
    Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta :
    Γ ⊢ e : .forallE A B →
    Γ ⊢ .lam A (.app e.lift (.bvar 0)) : .forallE A B →
    Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel :
    Γ ⊢ p : .sort false → Γ ⊢ h : p → Γ ⊢ h' : p →
    Γ ⊢ h ≡ h' : p

end

end

theorem IsDefEqStrong.hasType {env : VEnv}
    (H : env.IsDefEqStrong U Γ e1 e2 A) :
    env.IsDefEqStrong U Γ e1 e1 A ∧ env.IsDefEqStrong U Γ e2 e2 A :=
  ⟨H.trans H.symm, H.symm.trans H⟩

variable! {env : VEnv} in
theorem IsDefEqStrong.weakN (W : Ctx.LiftN n k Γ Γ') (H : env.IsDefEqStrong U Γ e1 e2 A) :
    env.IsDefEqStrong U Γ' (e1.liftN n k) (e2.liftN n k) (A.liftN n k) := by
  induction H generalizing k Γ' with
  | bvar h1 _ ih3 => refine .bvar (h1.weakN W) (ih3 W)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | sortDF => exact .sortDF
  | appDF _ _ _ _ ih1 ih2 ih3 ih4 =>
    exact liftN_inst_hi .. ▸ .appDF (ih1 W) (ih2 W) (ih3 W)
      (liftN_inst_hi .. ▸ liftN_inst_hi .. ▸ ih4 W)
  | lamDF _ _ _ _ ih1 ih2 ih3 ih4 =>
    exact .lamDF (ih1 W) (ih2 W.succ) (ih3 W.succ) (ih4 W.succ)
  | forallEDF _ _ _ ih1 ih2 ih3 => exact .forallEDF (ih1 W) (ih2 W.succ) (ih3 W.succ)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  | beta _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    refine liftN_inst_hi .. ▸ liftN_instN_hi .. ▸ .beta
      (ih1 W) (ih2 W.succ) (ih3 W)
      (liftN_instN_hi .. ▸ ih4 W :)
      (liftN_instN_hi .. ▸ liftN_instN_hi .. ▸ ih5 W :)
  | @eta Γ e A B _ _ ih2 ih3 =>
    have := IsDefEqStrong.eta (ih2 W) ?_
    · simp [liftN]; rwa [← lift_liftN']
    · specialize ih3 W; simp [liftN] at ih3; rwa [← lift_liftN'] at ih3
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)

theorem IsDefEqStrong.defeq (H : IsDefEqStrong env U Γ e1 e2 A) : env.IsDefEq U Γ e1 e2 A := by
  induction H with
  | bvar h => exact .bvar h
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF => exact .sortDF
  | appDF _ _ _ _ _ ih1 ih2 _ => exact .appDF ih1 ih2
  | lamDF _ _ _ _ ih1 _ ih2 _ => exact .lamDF ih1 ih2
  | forallEDF _ _ _ ih1 ih2 _ => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ _ _ _ _ ih1 ih2 _ _ => exact .beta ih1 ih2
  | eta  _ _ ih => exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3

variable! {env env' : VEnv} (henv : env ≤ env') in
theorem IsDefEqStrong.mono
    (H : env.IsDefEqStrong U Γ e1 e2 A) : env'.IsDefEqStrong U Γ e1 e2 A := by
  induction H with
  | bvar h1 _ ih => exact .bvar h1 ih
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF => exact .sortDF
  | appDF _ _ _ _ ih1 ih2 ih3 ih4 => exact .appDF ih1 ih2 ih3 ih4
  | lamDF _ _ _ _ ih1 ih2 ih3 ih4 => exact .lamDF ih1 ih2 ih3 ih4
  | forallEDF _ _ _ ih1 ih2 ih3 => exact .forallEDF ih1 ih2 ih3
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 => exact .beta ih1 ih2 ih3 ih4 ih5
  | eta _ _ ih1 ih2 => exact .eta ih1 ih2
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3

variable! {env : VEnv} in
theorem IsDefEqStrong.weak0 (H : env.IsDefEqStrong U [] e1 e2 A) :
    env.IsDefEqStrong U Γ e1 e2 A := by
  have ⟨h1, h2, h3⟩ := H.defeq.closedN' ⟨⟩
  simpa [h1.liftN_eq (Nat.zero_le _), h2.liftN_eq (Nat.zero_le _),
    h3.liftN_eq (Nat.zero_le _)] using H.weakN (.zero Γ rfl)

def CtxStrong (env : VEnv) (U Γ) :=
  OnCtx Γ fun Γ A => ∃ u, env.IsDefEqStrong U Γ A A (.sort u)

nonrec theorem CtxStrong.lookup {Γ} (H : CtxStrong env U Γ) (h : Lookup Γ i A) :
    ∃ u, env.IsDefEqStrong U Γ A A (.sort u) :=
  H.lookup h fun ⟨_, h⟩ => ⟨_, h.weakN .one⟩

theorem CtxStrong.defeq {Γ} (H : CtxStrong env U Γ) : OnCtx Γ (env.IsType U) :=
  H.mono fun ⟨_, h⟩ => ⟨_, h.defeq⟩

variable! {env : VEnv} (h₀ : env.IsDefEqStrong U Γ₀ e₀ e₀ A₀) (hΓ₀ : CtxStrong env U Γ₀) in
theorem IsDefEqStrong.instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : env.IsDefEqStrong U Γ₁ e1 e2 A)
    (hΓ : CtxStrong env U Γ) :
    env.IsDefEqStrong U Γ (e1.inst e₀ k) (e2.inst e₀ k) (A.inst e₀ k) := by
  induction H generalizing Γ k with
  | @bvar _ i ty _ h h2 ih =>
    dsimp [inst]; clear h2 ih
    induction W generalizing i ty with
    | zero =>
      cases h with simp [inst_lift]
      | zero => exact h₀
      | succ h =>
        let ⟨u, hty⟩ := hΓ₀.lookup h
        exact .bvar h hty
    | succ _ ih =>
      cases h with (simp; rw [Nat.add_comm, ← liftN_instN_lo (hj := Nat.zero_le _)])
      | zero =>
        let ⟨u, hty⟩ := hΓ.lookup .zero
        exact .bvar .zero hty
      | succ h => exact (ih h hΓ.1).weakN .one
  | symm _ ih => exact .symm (ih W hΓ)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W hΓ) (ih2 W hΓ)
  | sortDF => exact .sortDF
  | appDF _ _ _ _ ih1 ih2 ih3 ih4 =>
    exact inst0_inst_hi .. ▸ .appDF
      (ih1 W hΓ) (ih2 W hΓ) (ih3 W hΓ)
      (inst0_inst_hi .. ▸ inst0_inst_hi .. ▸ ih4 W hΓ)
  | lamDF _ _ _ _ ih1 ih2 ih3 ih4 =>
    exact
      have hΓ' := ⟨hΓ, _, (ih1 W hΓ).hasType.1⟩
      have hΓ'' := ⟨hΓ, _, (ih1 W hΓ).hasType.2⟩
      .lamDF (ih1 W hΓ) (ih2 W.succ hΓ') (ih3 W.succ hΓ') (ih4 W.succ hΓ'')
  | forallEDF _ _ _ ih1 ih2 ih3 =>
    exact .forallEDF (ih1 W hΓ)
      (ih2 W.succ ⟨hΓ, _, (ih1 W hΓ).hasType.1⟩) (ih3 W.succ ⟨hΓ, _, (ih1 W hΓ).hasType.2⟩)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W hΓ) (ih2 W hΓ)
  | beta _ _ _ _ _ ih1 ih3 ih4 ih5 ih6 =>
    rw [inst0_inst_hi, inst0_inst_hi]; exact
      have hΓ' := ⟨hΓ, _, ih1 W hΓ⟩
      .beta (ih1 W hΓ) (ih3 W.succ hΓ') (ih4 W hΓ)
        (inst0_inst_hi .. ▸ ih5 W hΓ) (inst0_inst_hi .. ▸ inst0_inst_hi .. ▸ ih6 W hΓ)
  | eta _ _ ih1 ih2 =>
    have := IsDefEqStrong.eta (ih1 W hΓ)
      (by simpa [inst, ← lift_instN_lo] using ih2 W hΓ)
    rw [lift, liftN_instN_lo (hj := Nat.zero_le _), Nat.add_comm] at this
    simpa [inst]
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W hΓ) (ih2 W hΓ) (ih3 W hΓ)

theorem IsDefEqStrong.defeqDF_l {env : VEnv} (hΓ : CtxStrong env U Γ)
    (h1 : env.IsDefEqStrong U Γ A A' (.sort u))
    (h2 : env.IsDefEqStrong U (A::Γ) e1 e2 B) : env.IsDefEqStrong U (A'::Γ) e1 e2 B := by
  simpa [instN_bvar0] using
    have hΓ' := ⟨hΓ, _, h1.hasType.2⟩
    h1.weakN (.one (A := A'))
      |>.symm.defeqDF (.bvar .zero (h1.hasType.2.weakN .one))
      |>.instN hΓ' .zero (h2.weakN (.succ (.one (A := A')))) hΓ'

variable! {env : VEnv} in
theorem IsDefEqStrong.forallE_inv' (hΓ : CtxStrong env U Γ)
    (H : env.IsDefEqStrong U Γ e1 e2 V) (eq : e1 = A.forallE B ∨ e2 = A.forallE B) :
    (∃ u, env.IsDefEqStrong U Γ A A (.sort u)) ∧ ∃ v, env.IsDefEqStrong U (A::Γ) B B (.sort v) := by
  induction H generalizing A B with
  | symm _ ih => exact ih hΓ eq.symm
  | trans _ _ ih1 ih2
  | proofIrrel _ _ _ _ ih1 ih2 =>
    obtain eq | eq := eq
    · exact ih1 hΓ (.inl eq)
    · exact ih2 hΓ (.inr eq)
  | forallEDF h1 h2 _ =>
    obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := eq
    · exact ⟨⟨_, h1.hasType.1⟩, _, h2.hasType.1⟩
    · exact ⟨⟨_, h1.hasType.2⟩, _, h1.defeqDF_l hΓ h2.hasType.2⟩
  | defeqDF _ _ _ ih2 => exact ih2 hΓ eq
  | @beta _ _ _ e _ _ h1 _ he' _ _ _ ih3 ih4 _ _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    cases e with
    | bvar i =>
      cases i with simp [inst] at eq
      | zero => exact ih4 hΓ (.inl eq)
    | forallE A B =>
      cases eq
      let ⟨⟨_, A1⟩, _, A2⟩ := ih3 ⟨hΓ, _, h1⟩ (.inl rfl)
      refine ⟨⟨_, he'.instN hΓ .zero A1 hΓ⟩, _, he'.instN hΓ (.succ .zero) A2 ?_⟩
      exact ⟨hΓ, _, he'.instN hΓ .zero A1 hΓ⟩
    | _ => cases eq
  | eta _ _ ih _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih hΓ (.inr eq)
  | _ => nomatch eq

variable! {env : VEnv} in
theorem IsDefEqStrong.isType' (hΓ : CtxStrong env U Γ) (H : env.IsDefEqStrong U Γ e1 e2 A) :
    ∃ u, env.IsDefEqStrong U Γ A A (.sort u) := by
  induction H with
  | bvar h _ => exact hΓ.lookup h
  | symm _ ih => exact ih hΓ
  | trans _ _ ih1 _ => exact ih1 hΓ
  | sortDF => exact ⟨_, .sortDF⟩
  | appDF _ _ _ h4 _ _ _ _ => exact ⟨_, h4.hasType.1⟩
  | lamDF h1 h2 _ _ => exact ⟨_, .forallEDF h1.hasType.1 h2 h2⟩
  | forallEDF => exact ⟨_, .sortDF⟩
  | defeqDF h1 _ _ _ => exact ⟨_, h1.hasType.2⟩
  | beta _ _ _ _ _ _ _ _ ih
  | eta _ _ ih => exact ih hΓ
  | proofIrrel h1 _ _ _ _ _ => exact ⟨_, h1⟩

theorem IsDefEqStrong.instDF {env : VEnv} (hΓ : CtxStrong env U Γ)
    (hA : env.IsDefEqStrong U Γ A A (.sort u))
    (hB : env.IsDefEqStrong U (A::Γ) B B (.sort v))
    (hf : env.IsDefEqStrong U (A::Γ) f f' B)
    (ha : env.IsDefEqStrong U Γ a a' A) :
    env.IsDefEqStrong U Γ (f.inst a) (f'.inst a') (B.inst a) :=
  have H2 {f f' B v}
      (hB : env.IsDefEqStrong U (A::Γ) B B (.sort v))
      (hf : env.IsDefEqStrong U (A::Γ) f f' B)
      (hi : IsDefEqStrong env U Γ (inst B a) (inst B a') (sort v)) :
      env.IsDefEqStrong U Γ (f.inst a) (f'.inst a') (B.inst a) :=
    have H1 {a f}
        (hf : env.IsDefEqStrong U (A::Γ) f f' B)
        (ha : IsDefEqStrong env U Γ a a A) :
        env.IsDefEqStrong U Γ (.app (.lam A f) a) (f.inst a) (B.inst a) :=
      IsDefEqStrong.beta hA hf.hasType.1 ha
        (.appDF hA (.lamDF hA hB hf.hasType.1 hf.hasType.1) ha
          (ha.hasType.1.instN hΓ .zero hB hΓ))
        (ha.hasType.1.instN hΓ .zero hf.hasType.1 hΓ)
    (H1 hf ha.hasType.1).symm.trans <|
      .trans (.appDF hA (.lamDF hA hB hf hf) ha hi) <|
      .defeqDF (.symm hi) (H1 hf.hasType.2 ha.hasType.2)
  H2 hB hf <| H2 .sortDF hB .sortDF

variable! {env : VEnv} in
theorem IsDefEq.strong' (hΓ : CtxStrong env U Γ)
    (H : env.IsDefEq U Γ e1 e2 A) : env.IsDefEqStrong U Γ e1 e2 A := by
  induction H with
  | bvar h =>
    let ⟨u, hA⟩ := hΓ.lookup h
    exact .bvar h hA
  | symm _ ih => exact (ih hΓ).symm
  | trans _ _ ih1 ih2 => exact (ih1 hΓ).trans (ih2 hΓ)
  | sortDF => exact .sortDF
  | appDF _ _ ih1 ih2 =>
    let ⟨_, h3⟩ := (ih1 hΓ).isType' hΓ
    let ⟨⟨u, hA⟩, ⟨v, hB⟩⟩ := h3.forallE_inv' hΓ (.inl rfl)
    exact .appDF hA (ih1 hΓ) (ih2 hΓ) <|
      .instDF hΓ hA .sortDF hB (ih2 hΓ)
  | lamDF _ _ ih1 ih2 =>
    have hΓ' : CtxStrong env U (_::_) := ⟨hΓ, _, (ih1 hΓ).hasType.1⟩
    let ⟨_, hB⟩ := (ih2 hΓ').isType' hΓ'
    exact .lamDF (ih1 hΓ) hB (ih2 hΓ') ((ih1 hΓ).defeqDF_l hΓ (ih2 hΓ'))
  | forallEDF _ _ ih1 ih2 =>
    have hΓ' : CtxStrong env U (_::_) := ⟨hΓ, _, (ih1 hΓ).hasType.1⟩
    exact .forallEDF (ih1 hΓ) (ih2 hΓ') ((ih1 hΓ).defeqDF_l hΓ (ih2 hΓ'))
  | defeqDF _ _ ih1 ih2 =>
    exact .defeqDF (ih1 hΓ) (ih2 hΓ)
  | beta _ _ ih1 ih2 =>
    have he' := ih2 hΓ
    have ⟨_, hA⟩ := he'.isType' hΓ
    have hΓ' : CtxStrong env U (_::_) := ⟨hΓ, _, hA⟩
    have he := ih1 hΓ'
    have ⟨_, hB⟩ := he.isType' hΓ'
    exact .beta hA he he'
      (.appDF hA (.lamDF hA hB he he) he' (he'.instN hΓ .zero hB hΓ))
      (he'.instN hΓ .zero he hΓ)
  | eta _ ih =>
    have he := ih hΓ
    let ⟨_, hAB⟩ := he.isType' hΓ
    let ⟨⟨u, hA⟩, ⟨v, hB⟩⟩ := hAB.forallE_inv' hΓ (.inl rfl)
    have := have hA' := hA.weakN .one
      hA'.appDF (he.weakN .one) (.bvar .zero hA') (by rwa [instN_bvar0])
    rw [instN_bvar0] at this
    exact .eta he (.lamDF hA hB this this)
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 hΓ) (ih2 hΓ) (ih3 hΓ)

theorem CtxStrong.strong' (hΓ : OnCtx Γ (env.IsType U)) : CtxStrong env U Γ := by
  induction Γ with
  | nil => trivial
  | cons _ _ ih => let ⟨hΓ, _, hA⟩ := hΓ; exact ⟨ih hΓ, _, hA.strong' (ih hΓ)⟩


theorem CtxStrong.strong {env : VEnv} (hΓ : OnCtx Γ (env.IsType U)) : CtxStrong env U Γ :=
  .strong' hΓ

theorem IsDefEq.strong {env : VEnv} (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEq U Γ e1 e2 A) : env.IsDefEqStrong U Γ e1 e2 A :=
  H.strong' (.strong hΓ)

variable! {env : VEnv} (hΓ : OnCtx Γ (env.IsType U)) in
theorem HasType.app_inv (H : env.HasType U Γ (.app f a) V) :
    ∃ A B, env.HasType U Γ f (.forallE A B) ∧ env.HasType U Γ a A := by
  stop
  replace H := (H.strong hΓ).hasType'.1
  generalize eq : true = b, eq' : f.app a = e' at H
  induction H with cases eq
  | defeq _ _ _ _ _ _ _ ih => exact ih hΓ rfl eq'
  | base H =>
    subst eq'; let .app _ _ _ _ _ h1 h2 _ := H; exact ⟨_, _, h1.hasType, h2.hasType⟩

variable! {env : VEnv} (hΓ : OnCtx Γ (env.IsType U)) in
theorem _root_.DomainSemantics.VExpr.WF.app_inv (H : VExpr.WF env U Γ (.app f a)) :
    ∃ A B, env.HasType U Γ f (.forallE A B) ∧ env.HasType U Γ a A :=
  let ⟨_, H⟩ := H; HasType.app_inv hΓ H

variable! {env : VEnv} (hΓ : OnCtx Γ (env.IsType U)) in
theorem HasType.lam_inv (H : env.HasType U Γ (.lam A body) V) :
    env.IsType U Γ A ∧ body.WF env U (A::Γ) := by
  stop
  replace H := (H.strong hΓ).hasType'.1
  generalize eq : true = b, eq' : A.lam body = e' at H
  induction H with cases eq
  | defeq _ _ _ _ _ _ _ ih => exact ih hΓ rfl eq'
  | base H => subst eq'; let .lam _ _ h1 _ h2 _ := H; exact ⟨⟨_, h1.hasType⟩, _, h2.hasType⟩

variable! {env : VEnv} (hΓ : OnCtx Γ (env.IsType U)) in
theorem _root_.DomainSemantics.VExpr.WF.lam_inv (H : VExpr.WF env U Γ (.lam A body)) :
    env.IsType U Γ A ∧ body.WF env U (A::Γ) :=
  let ⟨_, H⟩ := H; HasType.lam_inv hΓ H

variable! {env : VEnv} (hΓ : OnCtx Γ (env.IsType U)) in
theorem HasType.bvar_inv (H : env.HasType U Γ (.bvar i) V) : ∃ A, Lookup Γ i A := by
  stop
  replace H := (H.strong hΓ).hasType'.1
  generalize eq : true = b, eq' : VExpr.bvar i = e' at H
  induction H with cases eq
  | defeq _ _ _ _ _ _ _ ih => exact ih hΓ rfl eq'
  | base H => subst eq'; let .bvar h1 .. := H; exact ⟨_, h1⟩
