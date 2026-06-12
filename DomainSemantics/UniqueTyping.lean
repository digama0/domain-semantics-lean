import DomainSemantics.Adequacy

/-! # Unique typing over the SExpr weak defeq.

We work over `SExpr.IsDefEq` (a.k.a. `=W`), which has a heterogeneous
transitivity rule `trans'` allowing the middle term to live at a different
sort. Using `sort_inv` and `forallE_inv` from `ShapeLogRelAdequacy`, we
prove type uniqueness up to defeq, without needing stratified judgments.

From this we derive `uniq_sort` and admit a no-`trans'` variant `IsDefEq'`. -/

namespace DomainSemantics

section
set_option hygiene false
local notation:65 Γ " ⊨ " e " : " A:36 => HasTypeS Γ e A true
local notation:65 Γ " ⊨ " e " :! " A:36 => HasTypeS Γ e A false

/--
Bundled SExpr typing judgment. `Γ ⊨ e : A` (`b = true`) allows definitional
equality coercion; `Γ ⊨ e :! A` (`b = false`) is structural-only. This is
the SExpr analog of `HasTypeStrong` from the VEnv side, stripped of the
stratification index. Sort witnesses are carried at each constructor so
that type inversion is a direct structural property.
-/
inductive HasTypeS : List SExpr → SExpr → SExpr → Bool → Prop where
  | bvar : Lookup Γ i A → Γ ⊨ A : .sort u → Γ ⊨ .bvar i :! A
  | sort' : Γ ⊨ .sort l :! .sort true
  | app :
    Γ ⊨ f : .forallE A B → Γ ⊨ a : A →
    Γ ⊨ .app f a :! B.inst a
  | lam :
    Γ ⊨ A : .sort u → A::Γ ⊨ body : B →
    Γ ⊨ .lam A body :! .forallE A B
  | forallE :
    Γ ⊨ A : .sort u → A::Γ ⊨ body : .sort v →
    Γ ⊨ .forallE A body :! .sort v
  | base : Γ ⊨ e :! A → Γ ⊨ e : A
  | defeq :
    Γ ⊢ A ≡ B : .sort u → Γ ⊨ e : A → Γ ⊨ e : B

end

scoped notation:65 Γ " ⊨ " e " : " A:36 => HasTypeS Γ e A true
scoped notation:65 Γ " ⊨ " e " :! " A:36 => HasTypeS Γ e A false

/-- A bundled `HasTypeS` derivation can be projected back to a plain
`IsDefEq` derivation of reflexivity at the given type. -/
theorem HasTypeS.hasType : HasTypeS Γ e A b → Γ ⊢ e : A := by
  intro h
  induction h with
  | bvar h _ _ => exact .bvar h
  | sort' => exact .sort
  | app _ _ ihf iha => exact .appDF ihf iha
  | lam _ _ ihA ihbody => exact ihA.lamDF ihbody
  | forallE _ _ ihA ihbody => exact .forallEDF ihA ihbody
  | base _ ih => exact ih
  | defeq d _ ihe => exact d.defeqDF ihe

/-- Every `b = true` derivation unfolds to a `b = false` (structural) derivation
together with a transport: any defeq involving the structural type can be
re-targeted at the original type. -/
theorem HasTypeS.unfold (h : Γ ⊨ e : A) :
    ∃ A', (Γ ⊨ e :! A') ∧
      ∀ {C u}, Γ ⊢ C ≡ A' : .sort u → ∃ u', Γ ⊢ C ≡ A : .sort u' := by
  generalize hb : true = b at h
  induction h with cases hb
  | base h_s => exact ⟨_, h_s, fun input => ⟨_, input⟩⟩
  | defeq d _ ihe =>
    obtain ⟨A', h_s, chain⟩ := ihe rfl
    exact ⟨A', h_s, fun input => let ⟨_, eq⟩ := chain input; ⟨_, eq.trans' d⟩⟩

/-- Reduce any `HasTypeS` derivation (at either `b`) to a structural one with
a transport function. -/
theorem HasTypeS.toStructural (h : HasTypeS Γ e A b) :
    ∃ A', (Γ ⊨ e :! A') ∧
      ∀ {C u}, Γ ⊢ C ≡ A' : .sort u → ∃ u', Γ ⊢ C ≡ A : .sort u' := by
  cases b
  · exact ⟨_, h, fun input => ⟨_, input⟩⟩
  · exact h.unfold

/-- Type uniqueness up to defeq: any two derivations of `e` give defeq-equivalent
types. The middle `b` parameters are arbitrary. -/
theorem HasTypeS.uniq {Γ : List SExpr} {e A B : SExpr} {b₁ b₂ : Bool}
    (hΓ : ⊢ Γ) (H1 : HasTypeS Γ e A b₁) (H2 : HasTypeS Γ e B b₂) :
    ∃ u, Γ ⊢ A ≡ B : .sort u := by
  induction H1 generalizing B b₂ with
  | bvar h_l h_t _ =>
    obtain ⟨_, H2_s, transport⟩ := H2.toStructural
    let .bvar h_l' _ := H2_s
    obtain rfl := Lookup.determ h_l h_l'
    exact transport h_t.hasType
  | sort' =>
    obtain ⟨_, H2_s, transport⟩ := H2.toStructural
    let .sort' := H2_s
    exact transport .sort
  | @app Γ' _ A _ a _ h_a ih_f _ =>
    obtain ⟨_, H2_s, transport⟩ := H2.toStructural
    let .app h_f' _ := H2_s
    obtain ⟨_, h_pi_eq⟩ := ih_f hΓ h_f'
    obtain ⟨_, _, h_A_eq, h_B_eq⟩ := forallE_inv hΓ h_pi_eq
    have W : Ctx.SubstEq Γ' (.one a) (.one a) (A :: Γ') :=
      .cons (Ctx.SubstEq.id hΓ.strong) (h_A_eq.hasType.1.strong' hΓ.strong)
        (by simpa using h_a.hasType.strong' hΓ.strong)
    exact transport (h_B_eq.subst hΓ W)
  | @lam _ _ _ _ body h_A _ _ ih_body =>
    obtain ⟨_, H2_s, transport⟩ := H2.toStructural
    let .lam _ h_body' := H2_s
    have hΓ' : ⊢ (_::_) := ⟨hΓ, _, h_A.hasType⟩
    obtain ⟨_, h_B_eq⟩ := ih_body hΓ' h_body'
    exact transport (.forallEDF h_A.hasType h_B_eq)
  | forallE h_A h_b ih_A ih_b =>
    obtain ⟨_, H2_s, transport⟩ := H2.toStructural
    let .forallE h_A' h_b' := H2_s
    have hΓ' : ⊢ (_::_) := ⟨hΓ, _, h_A.hasType⟩
    obtain ⟨_, h_A_eq⟩ := ih_A hΓ h_A'
    obtain ⟨_, h_b_eq⟩ := ih_b hΓ' h_b'
    cases sort_inv hΓ h_A_eq
    cases sort_inv hΓ' h_b_eq
    exact transport .sort
  | base _ ih_s => exact ih_s hΓ H2
  | defeq d _ ihe =>
    obtain ⟨_, eq⟩ := ihe hΓ H2
    exact ⟨_, d.symm.trans' eq⟩

theorem IsDefEq.toHasTypeS {Γ : List SExpr} {e₁ e₂ A : SExpr}
    (hΓ : ⊢ Γ) (h : Γ ⊢ e₁ ≡ e₂ : A) : Γ ⊨ e₁ : A ∧ Γ ⊨ e₂ : A := by
  replace h := h.strong hΓ
  induction h with
  | bvar h_l _ ih_A => exact and_self_iff.2 <| .base <| .bvar h_l (ih_A hΓ).1
  | symm _ ih => exact ⟨(ih hΓ).2, (ih hΓ).1⟩
  | trans _ _ ih1 ih2 => exact ⟨(ih1 hΓ).1, (ih2 hΓ).2⟩
  | trans' _ _ ih1 ih2 =>
    obtain ⟨_, eq⟩ := (ih1 hΓ).2.uniq hΓ (ih2 hΓ).1
    cases sort_inv hΓ eq
    exact ⟨(ih1 hΓ).1, (ih2 hΓ).2⟩
  | sort => exact ⟨.base .sort', .base .sort'⟩
  | appDF _ _ _ _ h_Ba _ _ ih_f ih_a ih_Ba =>
    exact ⟨.base (.app (ih_f hΓ).1 (ih_a hΓ).1),
      .defeq h_Ba.symm.defeq (.base (.app (ih_f hΓ).2 (ih_a hΓ).2))⟩
  | lamDF h_A _ _ _ ih_A ih_B ih_body ih_body' =>
    refine have hΓ' := ⟨hΓ, _, h_A.hasType.1.defeq⟩; ⟨.base (.lam (ih_A hΓ).1 (ih_body hΓ').1), ?_⟩
    exact .defeq (.symm <| .forallEDF h_A.defeq (ih_B hΓ').1.hasType)
      (.base (.lam (ih_A hΓ).2 (ih_body' ⟨hΓ, _, h_A.hasType.2.defeq⟩).2))
  | forallEDF h_A _ _ ih_A ih_body ih_body' =>
    exact ⟨.base (.forallE (ih_A hΓ).1 (ih_body ⟨hΓ, _, h_A.hasType.1.defeq⟩).1),
      .base (.forallE (ih_A hΓ).2 (ih_body' ⟨hΓ, _, h_A.hasType.2.defeq⟩).2)⟩
  | defeqDF d _ _ ih2 => exact ⟨.defeq d.defeq (ih2 hΓ).1, .defeq d.defeq (ih2 hΓ).2⟩
  | beta _ _ _ _ _ _ _ _ ih_app ih_inst => exact ⟨(ih_app hΓ).1, (ih_inst hΓ).1⟩
  | eta _ _ ih_e ih_lam => exact ⟨(ih_lam hΓ).1, (ih_e hΓ).1⟩
  | proofIrrel _ _ _ _ ih_h ih_h' => exact ⟨(ih_h hΓ).1, (ih_h' hΓ).1⟩

/-- Sort uniqueness: if a middle term has two `sort`-types via defeq witnesses,
the two sort levels coincide. -/
theorem IsDefEq.uniq_sort {Γ : List SExpr} {e₁ e₂ e₃ : SExpr} {u v : Bool}
    (hΓ : ⊢ Γ) (h1 : Γ ⊢ e₁ ≡ e₂ : .sort u) (h2 : Γ ⊢ e₂ ≡ e₃ : .sort v) : u = v := by
  have ⟨_, h_e2_u⟩ := h1.toHasTypeS hΓ
  have ⟨h_e2_v, _⟩ := h2.toHasTypeS hΓ
  obtain ⟨_, eq⟩ := h_e2_u.uniq hΓ h_e2_v
  exact sort_inv hΓ eq

/-! ## `IsDefEq'`: defeq without heterogeneous `trans'`

We show that the `trans'` rule is admissible (via `uniq_sort`), so the
trans'-free system is equivalent to `IsDefEq`. -/

section
set_option hygiene false
local notation:65 Γ " ⊢' " e " : " A:36 => IsDefEq' Γ e e A
local notation:65 Γ " ⊢' " e1 " ≡ " e2 " : " A:36 => IsDefEq' Γ e1 e2 A

/--
The no-`trans'` variant of `IsDefEq`. Same constructors except the
heterogeneous transitivity is omitted; it becomes admissible via `uniq_sort`.
-/
inductive IsDefEq' : List SExpr → SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢' .bvar i : A
  | symm : Γ ⊢' e ≡ e' : A → Γ ⊢' e' ≡ e : A
  | trans : Γ ⊢' e₁ ≡ e₂ : A → Γ ⊢' e₂ ≡ e₃ : A → Γ ⊢' e₁ ≡ e₃ : A
  | sort : Γ ⊢' .sort l : .sort true
  | appDF : Γ ⊢' f ≡ f' : .forallE A B → Γ ⊢' a ≡ a' : A →
    Γ ⊢' .app f a ≡ .app f' a' : B.inst a
  | lamDF : Γ ⊢' A ≡ A' : .sort u → A::Γ ⊢' body ≡ body' : B →
    Γ ⊢' .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF : Γ ⊢' A ≡ A' : .sort u → A::Γ ⊢' body ≡ body' : .sort v →
    Γ ⊢' .forallE A body ≡ .forallE A' body' : .sort v
  | defeqDF : Γ ⊢' A ≡ B : .sort u → Γ ⊢' e1 ≡ e2 : A → Γ ⊢' e1 ≡ e2 : B
  | beta : A::Γ ⊢' e : B → Γ ⊢' e' : A →
    Γ ⊢' .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta : Γ ⊢' e : .forallE A B →
    Γ ⊢' .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel : Γ ⊢' p : .sort false → Γ ⊢' h : p → Γ ⊢' h' : p → Γ ⊢' h ≡ h' : p

end

scoped notation:65 Γ " ⊢' " e " : " A:36 => IsDefEq' Γ e e A
scoped notation:65 Γ " ⊢' " e1 " ≡ " e2 " : " A:36 => IsDefEq' Γ e1 e2 A

/-- Forward direction: every `IsDefEq'` derivation embeds into `IsDefEq`. -/
theorem IsDefEq'.toIsDefEq {Γ : List SExpr} {e₁ e₂ A : SExpr}
    (h : Γ ⊢' e₁ ≡ e₂ : A) : Γ ⊢ e₁ ≡ e₂ : A := by
  induction h with
  | bvar h => exact .bvar h
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sort => exact .sort
  | appDF _ _ ih1 ih2 => exact .appDF ih1 ih2
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ ih1 ih2 => exact .beta ih1 ih2
  | eta _ ih => exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3

theorem IsDefEq.toIsDefEq' {Γ : List SExpr} {e₁ e₂ A : SExpr}
    (hΓ : ⊢ Γ) (h : Γ ⊢ e₁ ≡ e₂ : A) : Γ ⊢' e₁ ≡ e₂ : A := by
  replace h := h.strong hΓ
  induction h with
  | bvar h _ _ => exact .bvar h
  | symm _ ih => exact .symm (ih hΓ)
  | trans _ _ ih1 ih2 => exact .trans (ih1 hΓ) (ih2 hΓ)
  | trans' h1 h2 ih1 ih2 =>
    cases h1.defeq.uniq_sort hΓ h2.defeq; exact .trans (ih1 hΓ) (ih2 hΓ)
  | sort => exact .sort
  | appDF _ _ _ _ _ _ _ ih2 ih3 _ => exact .appDF (ih2 hΓ) (ih3 hΓ)
  | lamDF h1 _ _ _ ih1 _ ih2 _ =>
    have hΓ' : ⊢ (_::_) := ⟨hΓ, _, h1.hasType.1.defeq⟩
    exact .lamDF (ih1 hΓ) (ih2 hΓ')
  | forallEDF h1 _ _ ih1 ih2 _ =>
    have hΓ' : ⊢ (_::_) := ⟨hΓ, _, h1.hasType.1.defeq⟩
    exact .forallEDF (ih1 hΓ) (ih2 hΓ')
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 hΓ) (ih2 hΓ)
  | beta h1 _ _ _ _ _ ih2 ih3 _ _ =>
    have hΓ' : ⊢ (_::_) := ⟨hΓ, _, h1.defeq⟩
    exact .beta (ih2 hΓ') (ih3 hΓ)
  | eta _ _ ih _ => exact .eta (ih hΓ)
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 hΓ) (ih2 hΓ) (ih3 hΓ)

def Ctx.WF' : List SExpr → Prop
  | [] => True
  | A::Γ => WF' Γ ∧ ∃ u, Γ ⊢' A : .sort u
scoped notation:65 "⊢' " Γ:36 => Ctx.WF' Γ

theorem Ctx.WF.toWF' : ∀ {Γ}, ⊢ Γ → ⊢' Γ
  | [], _ => trivial
  | _::_, ⟨hΓ, _, hA⟩ => ⟨hΓ.toWF', _, hA.toIsDefEq' hΓ⟩

theorem Ctx.WF'.toWF : ∀ {Γ}, ⊢' Γ → ⊢ Γ
  | [], _ => trivial
  | _::_, ⟨hΓ, _, hA⟩ => ⟨hΓ.toWF, _, hA.toIsDefEq⟩

theorem Ctx.WF.iff {Γ : List SExpr} : ⊢ Γ ↔ ⊢' Γ := ⟨toWF', WF'.toWF⟩

/-- `IsDefEq` and `IsDefEq'` are equivalent. -/
theorem IsDefEq.iff_isDefEq' {Γ : List SExpr} {e₁ e₂ A : SExpr} (hΓ : ⊢' Γ) :
    Γ ⊢ e₁ ≡ e₂ : A ↔ Γ ⊢' e₁ ≡ e₂ : A :=
  ⟨IsDefEq.toIsDefEq' hΓ.toWF, IsDefEq'.toIsDefEq⟩
