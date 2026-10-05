import DomainSemantics.Regular

/-! # Unique typing, and discharging the `IsDefEq` scaffolding

The "real" defeq judgment for the project is `IsDefEq₀`, defined in
`Term.lean`. Internally we work with the instrumented variant `IsDefEq`,
which carries explicit sort-typing premises at every congruence rule
and has a heterogeneous transitivity rule `trans'` whose middle term
may live at a different sort. This file ties the two together.

Using `sort_inv` and `forallE_inv` from `Adequacy.lean` we first prove
type uniqueness for `IsDefEq`, and then show that the `trans'` rule and
the extra sort proofs are admissible — so the working judgment really
is equivalent to the standard one.

* `HasType Γ e A b` is a bundled typing judgment carrying sort proofs
  at every constructor, used as the inductive scaffold for the type
  uniqueness theorem `HasType.uniq`.
* `IsDefEq.uniq_sort` derives sort uniqueness from `uniq`: heterogeneous
  transitivity on sort-typed equalities is in fact homogeneous.
* `IsDefEq.iff` is the headline result: on well-formed contexts the
  scaffolded `IsDefEq` and the standard `IsDefEq₀` derive the same
  equalities. After this point clients are free to think of `IsDefEq`
  as `IsDefEq₀`. -/

namespace DomainSemantics

section
set_option hygiene false
local notation:65 Γ " ⊨ " e " : " A:36 => HasType Γ e A true
local notation:65 Γ " ⊨ " e " :! " A:36 => HasType Γ e A false

/--
Bundled typing judgment over `IsDefEq`. `Γ ⊨ e : A` (`b = true`) allows
definitional equality coercion; `Γ ⊨ e :! A` (`b = false`) is
structural-only. Sort witnesses are carried at each constructor so that
type inversion is a direct structural property — the scaffolding used to
prove `HasType.uniq` and ultimately `IsDefEq.uniq_sort`.
-/
inductive HasType : List Term → Term → Term → Bool → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ A : .sort u → Γ ⊨ .bvar i :! A
  | sort' : Γ ⊨ .sort l :! .type
  | unit : Γ ⊨ .unit r :! .sort r
  | star : Γ ⊨ .star r :! .unit r
  | app :
    Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v → Γ ⊢ B.inst a : .sort v →
    Γ ⊨ f : .forallE A B → Γ ⊨ a : A →
    Γ ⊨ .app f a :! B.inst a
  | lam :
    Γ ⊨ A : .sort u → A::Γ ⊢ B : .sort v →
    A::Γ ⊨ body : B → Γ ⊨ .lam A body :! .forallE A B
  | forallE :
    Γ ⊨ A : .sort u → A::Γ ⊨ body : .sort v →
    Γ ⊨ .forallE A body :! .sort v
  | sigma :
    Γ ⊨ A : .sort u → A::Γ ⊨ body : .sort v →
    Γ ⊨ .sigma A body :! .type
  | pair :
    Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v →
    Γ ⊢ B.inst a : .sort v →
    Γ ⊨ a : A → Γ ⊨ b : B.inst a →
    Γ ⊨ .pair A B a b :! .sigma A B
  | fst :
    Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v →
    Γ ⊨ p : .sigma A B →
    Γ ⊨ .fst p :! A
  | snd :
    Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v →
    Γ ⊢ B.inst (.fst p) : .sort v →
    Γ ⊨ p : .sigma A B →
    Γ ⊨ .snd p :! B.inst (.fst p)
  | nat : Γ ⊨ .nat :! .type
  | zero : Γ ⊨ .zero :! .nat
  | succ : Γ ⊨ n : .nat → Γ ⊨ .succ n :! .nat
  | natCase :
    .nat::Γ ⊢ C : .sort v → Γ ⊢ C.inst M : .sort v →
    Γ ⊨ M : .nat → Γ ⊨ a : C.inst .zero →
    .nat::Γ ⊨ b : (C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0)) →
    Γ ⊨ .natCase C M a b :! C.inst M
  | Y : Γ ⊨ A : .sort u → A::Γ ⊨ body : A.lift → Γ ⊨ .Y A body :! A
  | id :
    Γ ⊨ A : .sort u → Γ ⊨ a : A → Γ ⊨ b : A →
    Γ ⊨ .id r A a b :! .sort r
  | refl :
    Γ ⊨ A : .sort u → Γ ⊨ a : A →
    Γ ⊨ .refl r a :! .id r A a a
  | tr :
    Γ ⊨ A : .sort u → Γ ⊨ a : A → Γ ⊨ b : A →
    A::Γ ⊢ C : .sort v → Γ ⊢ C.inst b : .sort v →
    Γ ⊨ x : C.inst a → Γ ⊨ h : .id r A a b →
    Γ ⊨ .tr r A a b C x h :! C.inst b
  | base : Γ ⊨ e :! A → Γ ⊨ e : A
  | defeq : Γ ⊢ A ≡ B : .sort u → Γ ⊨ e : A → Γ ⊨ e : B

end

scoped notation:65 Γ " ⊨ " e " : " A:36 => HasType Γ e A true
scoped notation:65 Γ " ⊨ " e " :! " A:36 => HasType Γ e A false

/-- A bundled `HasType` derivation can be projected back to a plain
`IsDefEq` derivation of reflexivity at the given type. -/
theorem HasType.hasType : HasType Γ e A b → Γ ⊢ e : A
  | .bvar h hA => .bvar h hA
  | .sort' => .sort
  | .unit => .unit
  | .star => .star
  | .app hA hB hBa ihf iha => .appDF hA hB ihf.hasType iha.hasType hBa
  | .lam ihA hB ihbody => .lamDF ihA.hasType hB ihbody.hasType ihbody.hasType
      (.forallEDF ihA.hasType hB hB)
  | .forallE ihA ihbody => .forallEDF ihA.hasType ihbody.hasType ihbody.hasType
  | .sigma ihA ihbody => .sigmaDF ihA.hasType ihbody.hasType ihbody.hasType
  | .pair hA hB hBa iha ihb => .pairDF hA hB hB iha.hasType ihb.hasType hBa (.sigmaDF hA hB hB)
  | .fst hA hB ihp => .fstDF hA hB ihp.hasType
  | .snd hA hB hBfst ihp => .sndDF hA hB ihp.hasType hBfst
  | .nat => .nat
  | .zero => .zero
  | .succ ihn => .succDF ihn.hasType
  | .natCase hC hCM ihM iha ihb =>
    .natCaseDF hC ihM.hasType iha.hasType ihb.hasType hCM
  | .Y ihA ihbody => .YDF ihA.hasType ihbody.hasType ihbody.hasType
  | .id ihA iha ihb => .idDF ihA.hasType iha.hasType ihb.hasType
  | .refl ihA iha => .reflDF ihA.hasType iha.hasType
      (.idDF ihA.hasType iha.hasType iha.hasType)
  | .tr ihA iha ihb hC hCb ihx ihh =>
      .trDF ihA.hasType iha.hasType ihb.hasType hC hC
        ihx.hasType ihh.hasType hCb
        (.idDF ihA.hasType iha.hasType ihb.hasType)
  | .base ih => ih.hasType
  | .defeq d ihe => d.defeqDF ihe.hasType

/-- Every `b = true` derivation unfolds to a `b = false` (structural) derivation
together with a transport: any defeq involving the structural type can be
re-targeted at the original type. -/
theorem HasType.unfold (h : Γ ⊨ e : A) :
    ∃ A', Γ ⊨ e :! A' ∧ ∀ {C u}, Γ ⊢ C ≡ A' : .sort u → ∃ u', Γ ⊢ C ≡ A : .sort u' := by
  generalize hb : true = b at h
  induction h with cases hb
  | base h_s => exact ⟨_, h_s, fun input => ⟨_, input⟩⟩
  | defeq d _ ihe =>
    obtain ⟨A', h_s, chain⟩ := ihe rfl
    exact ⟨A', h_s, fun input => let ⟨_, eq⟩ := chain input; ⟨_, eq.trans' d⟩⟩

/-- Reduce any `HasType` derivation (at either `b`) to a structural one with
a transport function. -/
theorem HasType.toStructural (h : HasType Γ e A b) :
    ∃ A', (Γ ⊨ e :! A') ∧
      ∀ {C u}, Γ ⊢ C ≡ A' : .sort u → ∃ u', Γ ⊢ C ≡ A : .sort u' := by
  cases b
  · exact ⟨_, h, fun input => ⟨_, input⟩⟩
  · exact h.unfold

/-- Type uniqueness up to defeq: any two derivations of `e` give defeq-equivalent
types. The middle `b` parameters are arbitrary. -/
theorem HasType.uniq {Γ : List Term} {e A B : Term} {b₁ b₂ : Bool}
    (hΓ : ⊢ Γ) (H1 : HasType Γ e A b₁) (H2 : HasType Γ e B b₂) :
    ∃ u, Γ ⊢ A ≡ B : .sort u := by
  induction H1 generalizing B b₂ with
  | bvar h_l h_t =>
    obtain ⟨_, H2_s, transport⟩ := H2.toStructural
    let .bvar h_l' _ := H2_s
    obtain rfl := Lookup.determ h_l h_l'
    exact transport h_t
  | sort' =>
    obtain ⟨_, H2_s, transport⟩ := H2.toStructural
    let .sort' := H2_s
    exact transport .sort
  | unit =>
    obtain ⟨_, H2_s, transport⟩ := H2.toStructural
    let .unit := H2_s
    exact transport .sort
  | star =>
    obtain ⟨_, H2_s, transport⟩ := H2.toStructural
    let .star := H2_s
    exact transport .unit
  | @app Γ' A _ _ _ a _ _ _ _ h_f h_a ih_f ih_a =>
    obtain ⟨_, H2_s, transport⟩ := H2.toStructural
    let .app _ _ _ h_f' _ := H2_s
    obtain ⟨_, h_pi_eq⟩ := ih_f hΓ h_f'
    obtain ⟨_, _, h_A_eq, h_B_eq⟩ := forallE_inv hΓ h_pi_eq
    have W : Ctx.SubstEq Γ' (.one a) (.one a) (A :: Γ') :=
      .cons (Ctx.SubstEq.id hΓ) h_A_eq.hasType.1
        (by simpa using h_a.hasType)
    exact transport (h_B_eq.subst hΓ W)
  | lam h_A _ h_body ih_A ih_body =>
    obtain ⟨_, H2_s, transport⟩ := H2.toStructural
    let .lam _ _ h_body' := H2_s
    have hΓ' : ⊢ (_::_) := ⟨hΓ, _, h_A.hasType⟩
    obtain ⟨_, h_B_eq⟩ := ih_body hΓ' h_body'
    exact transport (.forallEDF₀ hΓ h_A.hasType h_B_eq)
  | forallE h_A h_b ih_A ih_b =>
    obtain ⟨_, H2_s, transport⟩ := H2.toStructural
    let .forallE h_A' h_b' := H2_s
    have hΓ' : ⊢ (_::_) := ⟨hΓ, _, h_A.hasType⟩
    obtain ⟨_, h_A_eq⟩ := ih_A hΓ h_A'
    obtain ⟨_, h_b_eq⟩ := ih_b hΓ' h_b'
    cases sort_inv hΓ h_A_eq
    cases sort_inv hΓ' h_b_eq
    exact transport .sort
  | sigma h_A h_b ih_A ih_b =>
    obtain ⟨_, H2_s, transport⟩ := H2.toStructural
    let .sigma _ _ := H2_s
    exact transport .sort
  | pair h_A h_B _ _ _ =>
    obtain ⟨_, H2_s, transport⟩ := H2.toStructural
    let .pair _ _ _ _ _ := H2_s
    exact transport (.sigmaDF₀ hΓ h_A h_B)
  | fst h_A h_B h_p ih_p =>
    obtain ⟨_, H2_s, transport⟩ := H2.toStructural
    let .fst _ _ h_p' := H2_s
    obtain ⟨_, h_sig_eq⟩ := ih_p hΓ h_p'
    obtain ⟨_, _, h_A_eq, _⟩ := sigma_inv hΓ <| (IsDefEq.sigmaDF₀ hΓ h_A h_B).symm.trans' h_sig_eq
    exact transport h_A_eq
  | snd h_A h_B _ h_p ih_p =>
    obtain ⟨_, H2_s, transport⟩ := H2.toStructural
    let .snd _ _ _ h_p' := H2_s
    obtain ⟨_, h_sig_eq⟩ := ih_p hΓ h_p'
    obtain ⟨_, _, _, h_B_eq⟩ := sigma_inv hΓ <| (IsDefEq.sigmaDF₀ hΓ h_A h_B).symm.trans' h_sig_eq
    refine transport (h_B_eq.subst hΓ ?_)
    exact .cons (Ctx.SubstEq.id hΓ) h_A.hasType.1 (by simpa using h_p.hasType.fstDF₀ hΓ)
  | nat =>
    obtain ⟨_, H2_s, transport⟩ := H2.toStructural
    let .nat := H2_s
    exact transport .sort
  | zero =>
    obtain ⟨_, H2_s, transport⟩ := H2.toStructural
    let .zero := H2_s
    exact transport .nat
  | succ _ _ =>
    obtain ⟨_, H2_s, transport⟩ := H2.toStructural
    let .succ _ := H2_s
    exact transport .nat
  | natCase _ h_CM _ _ _ _ _ _ =>
    obtain ⟨_, H2_s, transport⟩ := H2.toStructural
    let .natCase _ _ _ _ _ := H2_s
    exact transport h_CM
  | id _ _ _ _ _ _ =>
    let ⟨_, .id _ _ _, transport⟩ := H2.toStructural
    exact transport .sort
  | refl _ h_a _ ih_a =>
    let ⟨_, .refl _ h_a_2, transport⟩ := H2.toStructural
    obtain ⟨u, h_A_eq⟩ := ih_a hΓ h_a_2
    exact transport (IsDefEq.idDF (u := u) h_A_eq h_a.hasType h_a.hasType)
  | tr _ _ _ _ hCb =>
    let ⟨_, .tr .., transport⟩ := H2.toStructural
    exact transport hCb
  | base _ ih_s => exact ih_s hΓ H2
  | defeq d _ ihe =>
    obtain ⟨_, eq⟩ := ihe hΓ H2
    exact ⟨_, d.symm.trans' eq⟩
  | Y h_A _ =>
    obtain ⟨_, H2_s, transport⟩ := H2.toStructural
    let .Y _ _ := H2_s
    exact transport h_A.hasType

/-- Every `IsDefEq` derivation projects to a pair of `HasType` derivations
on the two sides. The `trans'` case is the only one that needs work: it
uses `HasType.uniq` on the middle term plus `sort_inv` to collapse the
heterogeneous step. -/
theorem IsDefEq.toHasType {Γ : List Term} {e₁ e₂ A : Term}
    (hΓ : ⊢ Γ) (h : Γ ⊢ e₁ ≡ e₂ : A) : Γ ⊨ e₁ : A ∧ Γ ⊨ e₂ : A := by
  induction h with
  | bvar h_l h_t => exact and_self_iff.2 <| .base <| .bvar h_l h_t
  | symm _ ih => exact ⟨(ih hΓ).2, (ih hΓ).1⟩
  | trans _ _ ih1 ih2 => exact ⟨(ih1 hΓ).1, (ih2 hΓ).2⟩
  | trans' _ _ ih1 ih2 =>
    obtain ⟨_, eq⟩ := (ih1 hΓ).2.uniq hΓ (ih2 hΓ).1
    cases sort_inv hΓ eq
    exact ⟨(ih1 hΓ).1, (ih2 hΓ).2⟩
  | sort => exact ⟨.base .sort', .base .sort'⟩
  | unit => exact ⟨.base .unit, .base .unit⟩
  | star => exact ⟨.base .star, .base .star⟩
  | appDF hA hB _ _ h_Ba _ _ ih_f ih_a _ =>
    exact ⟨.base (.app hA hB h_Ba.hasType.1 (ih_f hΓ).1 (ih_a hΓ).1),
      .defeq h_Ba.symm
        (.base (.app hA hB h_Ba.hasType.2 (ih_f hΓ).2 (ih_a hΓ).2))⟩
  | lamDF h_A hB hbody hbody' _ ih_A _ ih_body ih_body' =>
    have hB' := h_A.defeqDF_l hΓ hB
    have hΓ' : ⊢ _ :: _ := ⟨hΓ, _, h_A.hasType.1⟩
    have hΓ_A' : ⊢ _ :: _ := ⟨hΓ, _, h_A.hasType.2⟩
    refine ⟨.base (.lam (ih_A hΓ).1 hB (ih_body hΓ').1), ?_⟩
    exact .defeq (.symm <| .forallEDF h_A hB hB')
      (.base (.lam (ih_A hΓ).2 hB' (ih_body' hΓ_A').2))
  | forallEDF h_A _ _ ih_A ih_body ih_body' =>
    exact ⟨.base (.forallE (ih_A hΓ).1 (ih_body ⟨hΓ, _, h_A.hasType.1⟩).1),
      .base (.forallE (ih_A hΓ).2 (ih_body' ⟨hΓ, _, h_A.hasType.2⟩).2)⟩
  | defeqDF d _ _ ih2 => exact ⟨.defeq d (ih2 hΓ).1, .defeq d (ih2 hΓ).2⟩
  | beta _ _ _ _ _ _ _ _ ih_app ih_inst => exact ⟨(ih_app hΓ).1, (ih_inst hΓ).1⟩
  | eta _ _ ih_e ih_lam => exact ⟨(ih_lam hΓ).1, (ih_e hΓ).1⟩
  | unit_eta _ ih => exact ⟨.base .star, (ih hΓ).1⟩
  | sigmaDF h_A _ _ ih_A ih_body ih_body' =>
    exact ⟨.base (.sigma (ih_A hΓ).1 (ih_body ⟨hΓ, _, h_A.hasType.1⟩).1),
      .base (.sigma (ih_A hΓ).2 (ih_body' ⟨hΓ, _, h_A.hasType.2⟩).2)⟩
  | pairDF h_A h_B h_B' _ _ h_Bin _ ih_A ih_B _ ih_a ih_b _ _ =>
    refine ⟨.base (.pair h_A.hasType.1 h_B.hasType.1 h_Bin.hasType.1
      (ih_a hΓ).1 (ih_b hΓ).1), ?_⟩
    exact .defeq (.symm <| .sigmaDF₀ hΓ h_A h_B)
      (.base (.pair h_A.hasType.2 h_B'.hasType.2 h_Bin.hasType.2
        (.defeq h_A (ih_a hΓ).2) (.defeq h_Bin (ih_b hΓ).2)))
  | fstDF h_A h_B _ _ _ ih_p =>
    exact ⟨.base (.fst h_A h_B (ih_p hΓ).1), .base (.fst h_A h_B (ih_p hΓ).2)⟩
  | sndDF h_A h_B _ h_Bfst _ _ ih_p _ =>
    refine ⟨.base (.snd h_A h_B h_Bfst.hasType.1 (ih_p hΓ).1), ?_⟩
    exact .defeq h_Bfst.symm (.base (.snd h_A h_B h_Bfst.hasType.2 (ih_p hΓ).2))
  | pair_fst h_A h_B h_a h_b _ _ _ ih_a ih_b _ =>
    refine ⟨?_, (ih_a hΓ).1⟩
    have h_Bin := IsDefEq.inst0 hΓ h_a h_B
    exact .base (.fst h_A h_B (.base (.pair h_A h_B h_Bin (ih_a hΓ).1 (ih_b hΓ).1)))
  | pair_snd h_A h_B h_a h_b _ _ _ ih_a ih_b _ =>
    refine ⟨?_, (ih_b hΓ).1⟩
    have h_Bin := IsDefEq.inst0 hΓ h_a h_B
    have h_pair_typing :=
      (HasType.base (.pair h_A h_B h_Bin (ih_a hΓ).1 (ih_b hΓ).1)).hasType
    have h_fst_eq := h_B.pair_fst₀ hΓ h_a h_b
    have h_B_eq := IsDefEq.instDF hΓ h_A .sort h_B h_fst_eq
    refine .defeq h_B_eq ?_
    exact .base (.snd h_A h_B h_B_eq.hasType.1
      (.base (.pair h_A h_B h_Bin (ih_a hΓ).1 (ih_b hΓ).1)))
  | fst_snd _ _ ih_p ih_pair => exact ⟨(ih_pair hΓ).1, (ih_p hΓ).1⟩
  | nat => exact ⟨.base .nat, .base .nat⟩
  | zero => exact ⟨.base .zero, .base .zero⟩
  | succDF _ ih => exact ⟨.base (.succ (ih hΓ).1), .base (.succ (ih hΓ).2)⟩
  | natCaseDF h_C _ _ _ h_CM _ ih_M ih_a ih_b _ =>
    have hΓ' : ⊢ .nat::_ := ⟨hΓ, _, .nat⟩
    refine ⟨.base (.natCase h_C.hasType.1 h_CM.hasType.1 (ih_M hΓ).1 (ih_a hΓ).1 (ih_b hΓ').1), ?_⟩
    refine .defeq h_CM.symm <| .base <| .natCase h_C.hasType.2 h_CM.hasType.2 (ih_M hΓ).2 ?_ ?_
    · exact .defeq (.instDF hΓ .nat .sort h_C .zero) (ih_a hΓ).2
    refine .defeq (.inst0 hΓ' ?_ (h_C.weak' (.cons (.skip .refl)))) (ih_b hΓ').2
    exact .succDF (.bvar .zero .nat)
  | natCase_zero h_C _ _ _ _ ih_a ih_b _ =>
    have hΓ' : ⊢ .nat::_ := ⟨hΓ, _, .nat⟩
    have hCM := IsDefEq.instDF hΓ .nat .sort h_C .zero
    exact ⟨.base (.natCase h_C hCM (.base .zero) (ih_a hΓ).1 (ih_b hΓ').1), (ih_a hΓ).1⟩
  | natCase_succ h_C h_n _ _ _ _ _ ih_n ih_a ih_b _ ih_bn =>
    have hΓ' : ⊢ .nat::_ := ⟨hΓ, _, .nat⟩
    have hCM := IsDefEq.instDF hΓ .nat .sort h_C (.succDF h_n)
    refine ⟨.base ?_, (ih_bn hΓ).1⟩
    exact .natCase h_C hCM (.base (.succ (ih_n hΓ).1)) (ih_a hΓ).1 (ih_b hΓ').1
  | idDF HA _ _ ih_A ih_a ih_b =>
    refine ⟨.base (.id (ih_A hΓ).1 (ih_a hΓ).1 (ih_b hΓ).1), ?_⟩
    refine .base (.id (ih_A hΓ).2 (.defeq HA (ih_a hΓ).2) (.defeq HA (ih_b hΓ).2))
  | @reflDF Γ A u a a' r HA Ha HId ih_A ih_a ih_Id =>
    refine ⟨.base (.refl (ih_A hΓ).1 (ih_a hΓ).1), ?_⟩
    have h_Aa_eq_Aa' : Γ ⊢ Term.id r A a a ≡ Term.id r A a' a' : .sort r :=
      .idDF HA.hasType.1 Ha Ha
    exact .defeq h_Aa_eq_Aa'.symm (.base (.refl (ih_A hΓ).1 (ih_a hΓ).2))
  | @trDF Γ A A' u a a' b b' C C' v x x' h h' r HA Ha Hb HC HC' Hx Hh HCb H_id
      ih_A ih_a ih_b ih_C ih_C' ih_x ih_h ih_Cb ih_id =>
    refine ⟨.base ?_, .defeq HCb.symm (.base ?_)⟩
    · exact .tr (ih_A hΓ).1 (ih_a hΓ).1 (ih_b hΓ).1 HC.hasType.1
        (.inst0 hΓ Hb.hasType.1 HC.hasType.1) (ih_x hΓ).1 (ih_h hΓ).1
    · refine .tr (ih_A hΓ).2 ((ih_a hΓ).2.defeq HA) ((ih_b hΓ).2.defeq HA)
        HC'.hasType.2 HCb.hasType.2 ?_ ((ih_h hΓ).2.defeq (HA.idDF Ha Hb))
      exact (ih_x hΓ).2.defeq (HA.hasType.1.instDF hΓ .sort HC Ha)
  | @tr_refl Γ A u a C v x r HA Ha HC Hx H_tr ih_A ih_a ih_C ih_x ih_tr =>
    refine ⟨.base ?_, (ih_x hΓ).1⟩
    exact .tr (ih_A hΓ).1 (ih_a hΓ).1 (ih_a hΓ).1 HC (.inst0 hΓ Ha HC)
      (ih_x hΓ).1 (.base (.refl (ih_A hΓ).1 (ih_a hΓ).1))
  | proofIrrel _ _ _ _ ih_h ih_h' => exact ⟨(ih_h hΓ).1, (ih_h' hΓ).1⟩
  | YDF h_A h_b h_b' ih_A ih_b ih_b' =>
    refine ⟨.base (.Y (ih_A hΓ).1 (ih_b ⟨hΓ, _, h_A.hasType.1⟩).1), ?_⟩
    exact .defeq h_A.symm (.base (.Y (ih_A hΓ).2 (ih_b' ⟨hΓ, _, h_A.hasType.2⟩).2))
  | Y_unfold _ _ _ _ _ _ ih_y ih_binst => exact ⟨(ih_y hΓ).1, (ih_binst hΓ).1⟩

/-- Sort uniqueness: if a middle term has two `sort`-types via defeq witnesses,
the two sort levels coincide. -/
theorem IsDefEq.uniq_sort {Γ : List Term} {e₁ e₂ e₃ : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (h1 : Γ ⊢ e₁ ≡ e₂ : .sort u) (h2 : Γ ⊢ e₂ ≡ e₃ : .sort v) : u = v := by
  have ⟨_, h_e2_u⟩ := h1.toHasType hΓ
  have ⟨h_e2_v, _⟩ := h2.toHasType hΓ
  obtain ⟨_, eq⟩ := h_e2_u.uniq hΓ h_e2_v
  exact sort_inv hΓ eq

/-- The instrumented judgment `IsDefEq` proves exactly the same equalities
as the standard judgment `IsDefEq₀` on well-formed contexts.

Forward: every `IsDefEq₀` derivation lifts to `IsDefEq` by inserting the
missing sort proofs (recovered from `⊢ Γ` via `.bvar₀`, `.appDF₀`,
`.lamDF₀`, …). Backward: every `IsDefEq` derivation collapses to
`IsDefEq₀` by dropping the sort premises and discharging `trans'` via
`IsDefEq.uniq_sort` (the two sort levels coincide, so heterogeneous
