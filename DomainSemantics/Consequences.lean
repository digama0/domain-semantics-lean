import DomainSemantics.Adequacy

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
  | sort' : Γ ⊨ .sort l :! .sort true
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
    Γ ⊨ .sigma A body :! .sort true
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
  | nat : Γ ⊨ .nat :! .sort true
  | zero : Γ ⊨ .zero :! .nat
  | succ : Γ ⊨ n : .nat → Γ ⊨ .succ n :! .nat
  | natCase :
    .nat::Γ ⊢ C : .sort v → Γ ⊢ C.inst M : .sort v →
    Γ ⊨ M : .nat → Γ ⊨ a : C.inst .zero →
    .nat::Γ ⊨ b : (C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0)) →
    Γ ⊨ .natCase C M a b :! C.inst M
  | Y : Γ ⊨ A : .sort u → A::Γ ⊨ body : A.lift → Γ ⊨ .Y A body :! A
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
transitivity is in fact homogeneous). -/
theorem IsDefEq₀.iff' {Γ : List Term} {e₁ e₂ A : Term}
    (hΓ : ⊢ Γ) : Γ ⊢₀ e₁ ≡ e₂ : A ↔ Γ ⊢ e₁ ≡ e₂ : A := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · induction h with
    | bvar h => exact .bvar₀ hΓ h
    | symm _ ih => exact .symm (ih hΓ)
    | trans _ _ ih1 ih2 => exact .trans (ih1 hΓ) (ih2 hΓ)
    | sort => exact .sort
    | unit => exact .unit
    | star => exact .star
    | appDF _ _ ih1 ih2 => exact .appDF₀ hΓ (ih1 hΓ) (ih2 hΓ)
    | lamDF _ _ ih1 ih2 => exact .lamDF₀ hΓ (ih1 hΓ) (ih2 ⟨hΓ, _, (ih1 hΓ).hasType.1⟩)
    | forallEDF _ _ ih1 ih2 => exact .forallEDF₀ hΓ (ih1 hΓ) (ih2 ⟨hΓ, _, (ih1 hΓ).hasType.1⟩)
    | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 hΓ) (ih2 hΓ)
    | beta _ _ ih1 ih2 => exact .beta₀ hΓ (ih1 ⟨hΓ, (ih2 hΓ).isType hΓ⟩) (ih2 hΓ)
    | eta _ ih => exact .eta₀ hΓ (ih hΓ)
    | unit_eta _ ih => exact .unit_eta (ih hΓ)
    | sigmaDF _ _ ih1 ih2 => exact .sigmaDF₀ hΓ (ih1 hΓ) (ih2 ⟨hΓ, _, (ih1 hΓ).hasType.1⟩)
    | pairDF _ _ _ _ ihA ihB ih1 ih2 =>
      exact .pairDF₀ hΓ (ihA hΓ) (ihB ⟨hΓ, _, (ihA hΓ).hasType.1⟩) (ih1 hΓ) (ih2 hΓ)
    | fstDF _ ih => exact .fstDF₀ hΓ (ih hΓ)
    | sndDF _ ih => exact .sndDF₀ hΓ (ih hΓ)
    | pair_fst h_B _ _ ihB ih1 ih2 =>
      let ⟨_, hA⟩ := (ih1 hΓ).isType hΓ
      exact .pair_fst₀ hΓ (ihB ⟨hΓ, _, hA⟩) (ih1 hΓ) (ih2 hΓ)
    | pair_snd h_B _ _ ihB ih1 ih2 =>
      let ⟨_, hA⟩ := (ih1 hΓ).isType hΓ
      exact .pair_snd₀ hΓ (ihB ⟨hΓ, _, hA⟩) (ih1 hΓ) (ih2 hΓ)
    | fst_snd _ ih_p => exact .fst_snd₀ hΓ (ih_p hΓ)
    | nat => exact .nat
    | zero => exact .zero
    | succDF _ ih => exact .succDF (ih hΓ)
    | natCaseDF _ _ _ _ ihC ihM iha ihb =>
      exact .natCaseDF₀ hΓ (ihC ⟨hΓ, _, .nat⟩) (ihM hΓ) (iha hΓ) (ihb ⟨hΓ, _, .nat⟩)
    | natCase_zero _ _ _ ihC iha ihb =>
      exact .natCase_zero₀ hΓ (ihC ⟨hΓ, _, .nat⟩) (iha hΓ) (ihb ⟨hΓ, _, .nat⟩)
    | natCase_succ _ _ _ _ ihC ihn iha ihb =>
      exact .natCase_succ₀ hΓ (ihC ⟨hΓ, _, .nat⟩) (ihn hΓ) (iha hΓ) (ihb ⟨hΓ, _, .nat⟩)
    | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 hΓ) (ih2 hΓ) (ih3 hΓ)
    | YDF _ _ ih1 ih2 => exact .YDF₀ hΓ (ih1 hΓ) (ih2 ⟨hΓ, _, (ih1 hΓ).hasType.1⟩)
    | Y_unfold _ _ ih1 ih2 => exact .Y_unfold₀ hΓ (ih1 hΓ) (ih2 ⟨hΓ, _, (ih1 hΓ).hasType.1⟩)
  · induction h with
    | bvar h _ => exact .bvar h
    | symm _ ih => exact .symm (ih hΓ)
    | trans _ _ ih1 ih2 => exact .trans (ih1 hΓ) (ih2 hΓ)
    | trans' h1 h2 ih1 ih2 => cases h1.uniq_sort hΓ h2; exact .trans (ih1 hΓ) (ih2 hΓ)
    | sort => exact .sort
    | unit => exact .unit
    | star => exact .star
    | appDF _ _ _ _ _ _ _ ih2 ih3 => exact .appDF (ih2 hΓ) (ih3 hΓ)
    | lamDF h1 _ _ _ _ ih1 _ ih2 => exact .lamDF (ih1 hΓ) (ih2 ⟨hΓ, _, h1.hasType.1⟩)
    | forallEDF h1 _ _ ih1 ih2 => exact .forallEDF (ih1 hΓ) (ih2 ⟨hΓ, _, h1.hasType.1⟩)
    | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 hΓ) (ih2 hΓ)
    | beta h1 _ _ _ _ _ ih1 ih2 => exact .beta (ih1 ⟨hΓ, _, h1⟩) (ih2 hΓ)
    | eta _ _ ih => exact .eta (ih hΓ)
    | unit_eta _ ih => exact .unit_eta (ih hΓ)
    | sigmaDF h_A _ _ ih_A ih_B _ =>
      exact .sigmaDF (ih_A hΓ) (ih_B ⟨hΓ, _, h_A.hasType.1⟩)
    | pairDF h_A _ _ _ _ _ _ ih_A ih_B _ ih_a ih_b _ _ =>
      exact .pairDF (ih_A hΓ) (ih_B ⟨hΓ, _, h_A.hasType.1⟩) (ih_a hΓ) (ih_b hΓ)
    | fstDF _ _ _ _ _ ih_p => exact .fstDF (ih_p hΓ)
    | sndDF _ _ _ _ _ _ ih_p _ => exact .sndDF (ih_p hΓ)
    | pair_fst h_A _ _ _ _ _ ih_B ih_a ih_b _ =>
      exact .pair_fst (ih_B ⟨hΓ, _, h_A.hasType.1⟩) (ih_a hΓ) (ih_b hΓ)
    | pair_snd h_A _ _ _ _ _ ih_B ih_a ih_b _ =>
      exact .pair_snd (ih_B ⟨hΓ, _, h_A.hasType.1⟩) (ih_a hΓ) (ih_b hΓ)
    | fst_snd _ _ ih_p _ => exact .fst_snd (ih_p hΓ)
    | nat => exact .nat
    | zero => exact .zero
    | succDF _ ih => exact .succDF (ih hΓ)
    | natCaseDF _ _ _ _ _ ihC ihM iha ihb _ =>
      exact .natCaseDF (ihC ⟨hΓ, _, .nat⟩) (ihM hΓ) (iha hΓ) (ihb ⟨hΓ, _, .nat⟩)
    | natCase_zero _ _ _ _ ihC iha ihb _ =>
      exact .natCase_zero (ihC ⟨hΓ, _, .nat⟩) (iha hΓ) (ihb ⟨hΓ, _, .nat⟩)
    | natCase_succ _ _ _ _ _ _ ihC ihn iha ihb _ _ =>
      exact .natCase_succ (ihC ⟨hΓ, _, .nat⟩) (ihn hΓ) (iha hΓ) (ihb ⟨hΓ, _, .nat⟩)
    | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 hΓ) (ih2 hΓ) (ih3 hΓ)
    | YDF h1 _ _ ih1 ih2 ih3 => exact .YDF (ih1 hΓ) (ih2 ⟨hΓ, _, h1.hasType.1⟩)
    | Y_unfold h1 _ _ _ ih1 ih2 => exact .Y_unfold (ih1 hΓ) (ih2 ⟨hΓ, _, h1.hasType.1⟩)

/-- Well-formed context relative to `IsDefEq₀`: each entry has a sort
typing in the `trans'`-free judgment. Equivalent to `Ctx.WF` on
well-formed contexts via `Ctx.WF.iff`. -/
def Ctx.WF' : List Term → Prop
  | [] => True
  | A::Γ => WF' Γ ∧ ∃ u, Γ ⊢₀ A : .sort u
scoped notation:65 "⊢₀ " Γ:36 => Ctx.WF' Γ

/-- Well-formedness of contexts is invariant under the two judgment systems:
`⊢ Γ` (using `IsDefEq` sort proofs) and `⊢₀ Γ` (using `IsDefEq₀`) are
mutually derivable, by induction on `Γ` calling `IsDefEq₀.iff'` on the
head sort proof. -/
theorem Ctx.WF.iff : ∀ {Γ}, ⊢ Γ ↔ ⊢₀ Γ
  | [] => .rfl
  | _::_ => ⟨
    fun ⟨hΓ, _, hA⟩ => ⟨iff.1 hΓ, _, (IsDefEq₀.iff' hΓ).2 hA⟩,
    fun ⟨hΓ, _, hA⟩ => ⟨iff.2 hΓ, _, (IsDefEq₀.iff' (iff.2 hΓ)).1 hA⟩⟩

/-! ### Discharging the scaffolding -/

/-- On any well-formed context (in either formulation, via `Ctx.WF.iff`),
the instrumented `IsDefEq` proves the same equalities as the standard `IsDefEq₀`.
After this point clients are free to treat the two notations as interchangeable,
and the choice of `IsDefEq` over `IsDefEq₀` inside the project
is purely a matter of proof ergonomics. -/
theorem IsDefEq.iff {Γ : List Term} {e₁ e₂ A : Term} (hΓ : ⊢₀ Γ) :
    Γ ⊢ e₁ ≡ e₂ : A ↔ Γ ⊢₀ e₁ ≡ e₂ : A := (IsDefEq₀.iff' (Ctx.WF.iff.2 hΓ)).symm

/-- Pi–Pi injectivity: if two Pi types are definitionally equal,
their domains and codomains are each definitionally equal. -/
theorem forallE_inv' (hΓ : ⊢₀ Γ)
    (H : Γ ⊢₀ Term.forallE A₀ B₀ ≡ Term.forallE A₁ B₁ : .sort s) :
    ∃ u v, Γ ⊢₀ A₀ ≡ A₁ : .sort u ∧ A₀::Γ ⊢₀ B₀ ≡ B₁ : .sort v := by
  have hΓs : ⊢ Γ := Ctx.WF.iff.2 hΓ
  have ⟨u, v, hA, hB⟩ := forallE_inv hΓs ((IsDefEq.iff hΓ).2 H)
  have hΓA : ⊢₀ A₀ :: Γ := Ctx.WF.iff.1 ⟨hΓs, _, hA.hasType.1⟩
  exact ⟨u, v, (IsDefEq.iff hΓ).1 hA, (IsDefEq.iff hΓA).1 hB⟩

/-- Sort/Pi disjointness: a sort is never definitionally equal to a Pi-type.
A consequence of weak-head determinacy and the fact that `.sort u` is
already in WHNF. -/
theorem sort_forallE_inv' (hΓ : ⊢₀ Γ) : ¬Γ ⊢₀ .sort u ≡ Term.forallE A₁ B₁ : .sort s :=
  fun H => sort_forallE_inv (Ctx.WF.iff.2 hΓ) ((IsDefEq.iff hΓ).2 H)

/-- Sort injectivity: if two sorts are definitionally equal, their levels are equal. -/
theorem sort_inv' (hΓ : ⊢₀ Γ) (d : Γ ⊢₀ Term.sort u ≡ Term.sort v : V) : u = v :=
  sort_inv (Ctx.WF.iff.2 hΓ) ((IsDefEq.iff hΓ).2 d)

/-! ### Subject reduction (subject conversion)

A single weak-head reduction step is a definitional equality *at the
reducing term's type*: if `Γ ⊢ M : A` and `M ⤳ N` then `Γ ⊢ M ≡ N : A`.
This mirrors the Agda `subject-conv1` / `subject-red1` development. The
only nontrivial step is β: there we invert the `lam` typing through
type uniqueness (`HasType.uniq`) and Pi-injectivity (`forallE_inv`) to
recover the body typing at the function's actual domain, then build the
β-equation with `IsDefEq.beta₀`. Ordinary subject reduction
(`Γ ⊢ N : A`) is the immediate corollary, since `Γ ⊢ N : A` is just
reflexive defeq `Γ ⊢ N ≡ N : A`. -/

/-- Subject conversion for instrumented `IsDefEq`: one weak-head step is
a definitional equality at the term's type. -/
theorem WHRed.subject_conv (hΓ : ⊢ Γ) (hr : M ⤳ N) {A} (hM : Γ ⊢ M : A) : Γ ⊢ M ≡ N : A := by
  induction hr generalizing A with
  | @app f f' a hf ih =>
    obtain ⟨H, _⟩ := hM.toHasType hΓ
    obtain ⟨_, Hs, transport⟩ := H.toStructural
    let .app _ _ hBa h_f h_a := Hs
    obtain ⟨_, eqA⟩ := transport hBa
    exact eqA.defeqDF (.appDF₀ hΓ (ih h_f.hasType) h_a.hasType)
  | @beta Al e a =>
    obtain ⟨H, _⟩ := hM.toHasType hΓ
    obtain ⟨_, Hs, transport⟩ := H.toStructural
    let .app _ _ hBa h_f h_a := Hs
    -- invert the `lam` typing: extract its native codomain `B'` and body typing
    obtain ⟨_, hfs, _⟩ := h_f.toStructural
    let .lam ihA hB' hbody := hfs
    obtain ⟨_, hpi⟩ := h_f.uniq hΓ (.base (.lam ihA hB' hbody))
    obtain ⟨_, _, hAeq, hBeq⟩ := forallE_inv hΓ hpi
    -- `a` typed at the lam's annotation domain `Al`, and the β-equation there
    have betaConv := IsDefEq.beta₀ hΓ hbody.hasType (hAeq.defeqDF h_a.hasType)
    -- re-target the codomain `B'.inst a` back to the app's type `B.inst a`, then `A`
    have hBeqInst := h_a.hasType.inst0 hΓ hBeq.symm
    obtain ⟨_, eqA⟩ := transport hBa
    exact eqA.defeqDF (hBeqInst.defeqDF betaConv)
  | @fst p p' hp ih =>
    obtain ⟨H, _⟩ := hM.toHasType hΓ
    obtain ⟨_, Hs, _⟩ := H.toStructural
    let .fst _ _ h_p := Hs
    have fConv := IsDefEq.fstDF₀ hΓ (ih h_p.hasType)
    obtain ⟨_, hTe⟩ := H.uniq hΓ (fConv.toHasType hΓ).1
    exact hTe.symm.defeqDF fConv
  | @snd p p' hp ih =>
    obtain ⟨H, _⟩ := hM.toHasType hΓ
    obtain ⟨_, Hs, _⟩ := H.toStructural
    let .snd _ _ _ h_p := Hs
    have sConv := IsDefEq.sndDF₀ hΓ (ih h_p.hasType)
    obtain ⟨_, hTe⟩ := H.uniq hΓ (sConv.toHasType hΓ).1
    exact hTe.symm.defeqDF sConv
  | @pair_fst A B a b =>
    obtain ⟨H, _⟩ := hM.toHasType hΓ
    obtain ⟨_, Hs, _⟩ := H.toStructural
    let .fst _ _ h_p := Hs
    obtain ⟨_, hps, _⟩ := h_p.toStructural
    let .pair _ hB _ iha ihb := hps
    have pfConv := IsDefEq.pair_fst₀ hΓ hB iha.hasType ihb.hasType
    obtain ⟨_, hTe⟩ := H.uniq hΓ (pfConv.toHasType hΓ).1
    exact hTe.symm.defeqDF pfConv
  | @pair_snd A B a b =>
    obtain ⟨H, _⟩ := hM.toHasType hΓ
    obtain ⟨_, Hs, _⟩ := H.toStructural
    let .snd _ _ _ h_p := Hs
    obtain ⟨_, hps, _⟩ := h_p.toStructural
    let .pair _ hB _ iha ihb := hps
    have psConv := IsDefEq.pair_snd₀ hΓ hB iha.hasType ihb.hasType
    obtain ⟨_, hTe⟩ := H.uniq hΓ (psConv.toHasType hΓ).1
    exact hTe.symm.defeqDF psConv
  | natCase hp ih =>
    obtain ⟨H, _⟩ := hM.toHasType hΓ
    let ⟨_, .natCase hC _ hM ha hb, _⟩ := H.toStructural
    have fConv := IsDefEq.natCaseDF₀ hΓ hC (ih hM.hasType) ha.hasType hb.hasType
    obtain ⟨_, hTe⟩ := H.uniq hΓ (fConv.toHasType hΓ).1
    exact hTe.symm.defeqDF fConv
  | natCase_zero =>
    obtain ⟨H, _⟩ := hM.toHasType hΓ
    let ⟨_, .natCase hC _ _ ha hb, _⟩ := H.toStructural
    have fConv := IsDefEq.natCase_zero₀ hΓ hC ha.hasType hb.hasType
    obtain ⟨_, hTe⟩ := H.uniq hΓ (fConv.toHasType hΓ).1
    exact hTe.symm.defeqDF fConv
  | natCase_succ =>
    obtain ⟨H, _⟩ := hM.toHasType hΓ
    let ⟨_, .natCase hC _ hn ha hb, _⟩ := H.toStructural
    let ⟨_, .succ hn, _⟩ := hn.toStructural
    have fConv := IsDefEq.natCase_succ₀ hΓ hC hn.hasType ha.hasType hb.hasType
    obtain ⟨_, hTe⟩ := H.uniq hΓ (fConv.toHasType hΓ).1
    exact hTe.symm.defeqDF fConv
  | @Y B b =>
    obtain ⟨H, _⟩ := hM.toHasType hΓ
    obtain ⟨_, Hs, transport⟩ := H.toStructural
    let .Y hB hb := Hs
    have ⟨_, eq⟩ := transport hB.hasType
    exact eq.defeqDF <| .Y_unfold₀ hΓ hB.hasType hb.hasType

/-- Subject reduction for instrumented `IsDefEq`: a weak-head step
preserves the type. -/
theorem WHRed.subject_red (hΓ : ⊢ Γ) (hr : M ⤳ N) (hM : Γ ⊢ M : A) : Γ ⊢ N : A :=
  (subject_conv hΓ hr hM).hasType.2

/-- Subject conversion for the standard judgment `IsDefEq₀`. -/
theorem WHRed.subject_conv' (hΓ : ⊢₀ Γ) (hr : M ⤳ N) (hM : Γ ⊢₀ M : A) : Γ ⊢₀ M ≡ N : A :=
  (IsDefEq.iff hΓ).1 (subject_conv (Ctx.WF.iff.2 hΓ) hr ((IsDefEq.iff hΓ).2 hM))

/-- Subject reduction for the standard judgment `IsDefEq₀`. -/
theorem WHRed.subject_red' (hΓ : ⊢₀ Γ) (hr : M ⤳ N) (hM : Γ ⊢₀ M : A) : Γ ⊢₀ N : A :=
  have := subject_conv' hΓ hr hM; this.symm.trans this

/-! ### Progress

A *value* is a weak-head-canonical form: a sort, a `lam`, or a `forallE`.
These are exactly the closed weak-head normal forms — the only other
heads (`bvar`, `app`) are respectively untypable in the empty context
and always reducible there. Progress states that a closed well-typed
term is either a value or takes a weak-head step; equivalently, no
closed well-typed term is stuck. The crux is the canonical-forms lemma
`Value.forallE_r`: a value of function type must be a `lam` (a sort or
`forallE` would have a sort type, contradicting `sort_forallE_inv`), so
a closed application always β-reduces. -/

/-- Weak-head canonical forms: the closed normal forms of the core theory. -/
inductive Value : Term → Prop where
  | sort : Value (.sort u)
  | unit : Value (.unit r)
  | star : Value (.star r)
  | lam : Value (.lam A e)
  | forallE : Value (.forallE A B)
  | sigma : Value (.sigma A B)
  | pair : Value (.pair A B a b)
  | nat : Value .nat
  | zero : Value .zero
  | succ : Value (.succ n)

theorem IsDefEq.trans_r (hΓ : ⊢ Γ)
    (H : Γ ⊢ M ≡ N : A) (h2 : Γ ⊢ N ≡ P : B) : Γ ⊢ M ≡ P : B := by
  have ⟨_, eq⟩ := (H.toHasType hΓ).2.uniq hΓ (h2.toHasType hΓ).1
  exact eq.defeqDF H |>.trans h2

theorem IsDefEq.to_sigma_type (hΓ : ⊢ Γ)
    (H : Γ ⊢ e ≡ Term.sigma A B : .sort w) : Γ ⊢ e ≡ Term.sigma A B : .sort true := by
  have ⟨⟨_, h1⟩, _, h2⟩ := H.sigma_inv' hΓ (.inr rfl)
  exact H.trans_r hΓ (h1.sigmaDF₀ hΓ h2)

/-- Canonical forms at function type: a value typed by a `forallE` is a `lam`.
A sort or a `forallE` would be typed by a `sort`, which is never
definitionally equal to a function type. -/
theorem Value.forallE_r (hΓ : ⊢ Γ) (hv : Value f) (h : Γ ⊢ f : .forallE A B) :
    ∃ A' e, f = .lam A' e := by
  cases hv with
  | lam => exact ⟨_, _, rfl⟩
  | sort =>
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base .sort')
    cases sort_forallE_inv hΓ eq.symm
  | unit =>
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base .unit)
    cases sort_forallE_inv hΓ eq.symm
  | star =>
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base .star)
    cases forallE_unit_inv hΓ eq.symm
  | forallE =>
    obtain ⟨_, hfs, _⟩ := (h.toHasType hΓ).1.toStructural
    let .forallE hC hD := hfs
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base (.forallE hC hD))
    cases sort_forallE_inv hΓ eq.symm
  | sigma =>
    obtain ⟨_, hfs, _⟩ := (h.toHasType hΓ).1.toStructural
    let .sigma hC hD := hfs
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base (.sigma hC hD))
    cases sort_forallE_inv hΓ eq.symm
  | pair =>
    obtain ⟨_, hfs, _⟩ := (h.toHasType hΓ).1.toStructural
    let .pair hC hD hE hF hG := hfs
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base (.pair hC hD hE hF hG))
    cases forallE_sigma_inv hΓ (eq.to_sigma_type hΓ)
  | nat =>
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base .nat)
    cases sort_forallE_inv hΓ eq.symm
  | zero =>
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base .zero)
    cases forallE_nat_inv hΓ (eq.trans_r hΓ .nat)
  | succ =>
    obtain ⟨_, hfs, _⟩ := (h.toHasType hΓ).1.toStructural
    let .succ hn := hfs
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base (.succ hn))
    cases forallE_nat_inv hΓ (eq.trans_r hΓ .nat)

/-- Canonical forms at Σ-type: a value typed by a `sigma` is a `pair`.
Any other value (`sort`, `forallE`, `sigma`) is typed by a `sort`, and a
`lam` is typed by a `forallE`; none is definitionally equal to a Σ-type. -/
theorem Value.sigma_r (hΓ : ⊢ Γ) (hv : Value f) (h : Γ ⊢ f : .sigma A B) :
    ∃ A' B' a b, f = .pair A' B' a b := by
  cases hv with
  | pair => exact ⟨_, _, _, _, rfl⟩
  | sort =>
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base .sort')
    cases sort_sigma_inv hΓ (eq.symm.to_sigma_type hΓ)
  | unit =>
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base .unit)
    cases sort_sigma_inv hΓ (eq.symm.to_sigma_type hΓ)
  | star =>
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base .star)
    cases sigma_unit_inv hΓ (eq.symm.to_sigma_type hΓ)
  | lam =>
    obtain ⟨_, hfs, _⟩ := (h.toHasType hΓ).1.toStructural
    let .lam hC hD hE := hfs
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base (.lam hC hD hE))
    cases forallE_sigma_inv hΓ (eq.symm.to_sigma_type hΓ)
  | forallE =>
    obtain ⟨_, hfs, _⟩ := (h.toHasType hΓ).1.toStructural
    let .forallE hC hD := hfs
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base (.forallE hC hD))
    cases sort_sigma_inv hΓ (eq.symm.to_sigma_type hΓ)
  | sigma =>
    obtain ⟨_, hfs, _⟩ := (h.toHasType hΓ).1.toStructural
    let .sigma hC hD := hfs
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base (.sigma hC hD))
    cases sort_sigma_inv hΓ (eq.symm.to_sigma_type hΓ)
  | nat =>
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base .nat)
    cases sort_sigma_inv hΓ (eq.symm.to_sigma_type hΓ)
  | zero =>
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base .zero)
    cases sigma_nat_inv hΓ (eq.trans_r hΓ .nat)
  | succ =>
    obtain ⟨_, hfs, _⟩ := (h.toHasType hΓ).1.toStructural
    let .succ hn := hfs
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base (.succ hn))
    cases sigma_nat_inv hΓ (eq.trans_r hΓ .nat)

/-- Canonical forms at ℕ-type: a value typed by `Nat` is `zero` or `succ`. -/
theorem Value.nat_r (hΓ : ⊢ Γ) (hv : Value n) (h : Γ ⊢ n : .nat) :
    n = .zero ∨ ∃ n', n = .succ n' := by
  cases hv with
  | zero => exact .inl rfl
  | succ => exact .inr ⟨_, rfl⟩
  | sort =>
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base .sort')
    cases sort_nat_inv hΓ (eq.symm.trans_r hΓ .nat)
  | unit =>
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base .unit)
    cases sort_nat_inv hΓ (eq.symm.trans_r hΓ .nat)
  | star =>
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base .star)
    cases nat_unit_inv hΓ (eq.symm.trans_r hΓ .nat)
  | lam =>
    obtain ⟨_, hfs, _⟩ := (h.toHasType hΓ).1.toStructural
    let .lam hC hD hE := hfs
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base (.lam hC hD hE))
    cases forallE_nat_inv hΓ (eq.symm.trans_r hΓ .nat)
  | forallE =>
    obtain ⟨_, hfs, _⟩ := (h.toHasType hΓ).1.toStructural
    let .forallE hC hD := hfs
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base (.forallE hC hD))
    cases sort_nat_inv hΓ (eq.symm.trans_r hΓ .nat)
  | sigma =>
    obtain ⟨_, hfs, _⟩ := (h.toHasType hΓ).1.toStructural
    let .sigma hC hD := hfs
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base (.sigma hC hD))
    cases sort_nat_inv hΓ (eq.symm.trans_r hΓ .nat)
  | pair =>
    obtain ⟨_, hfs, _⟩ := (h.toHasType hΓ).1.toStructural
    let .pair hC hD hE hF hG := hfs
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base (.pair hC hD hE hF hG))
    cases sigma_nat_inv hΓ (eq.symm.trans_r hΓ .nat)
  | nat =>
    obtain ⟨_, eq⟩ := (h.toHasType hΓ).1.uniq hΓ (.base .nat)
    cases sort_nat_inv hΓ (eq.symm.trans_r hΓ .nat)

/-- Progress for instrumented `IsDefEq`: a closed well-typed term is either a
value or takes a weak-head step. -/
theorem progress {e : Term} : ∀ {A}, [] ⊢ e : A → Value e ∨ ∃ e', e ⤳ e' := by
  induction e with
  | bvar =>
    intro A h
    obtain ⟨_, Hs, _⟩ := (h.toHasType (Γ := []) trivial).1.toStructural
    let .bvar h_l _ := Hs
    nomatch h_l
  | sort => intro A _; exact .inl .sort
  | unit => intro A _; exact .inl .unit
  | star => intro A _; exact .inl .star
  | app _ _ ih_f =>
    intro A h
    obtain ⟨_, Hs, _⟩ := (h.toHasType (Γ := []) trivial).1.toStructural
    let .app _ _ _ h_f _ := Hs
    rcases ih_f h_f.hasType with hv | ⟨f', hstep⟩
    · obtain ⟨_, _, rfl⟩ := hv.forallE_r (Γ := []) trivial h_f.hasType
      exact .inr ⟨_, .beta⟩
    · exact .inr ⟨_, .app hstep⟩
  | lam => intro A _; exact .inl .lam
  | forallE => intro A _; exact .inl .forallE
  | sigma => intro A _; exact .inl .sigma
  | pair => intro A _; exact .inl .pair
  | fst _ ih_p =>
    intro A h
    obtain ⟨_, Hs, _⟩ := (h.toHasType (Γ := []) trivial).1.toStructural
    let .fst _ _ h_p := Hs
    rcases ih_p h_p.hasType with hv | ⟨p', hstep⟩
    · obtain ⟨_, _, _, _, rfl⟩ := hv.sigma_r (Γ := []) trivial h_p.hasType
      exact .inr ⟨_, .pair_fst⟩
    · exact .inr ⟨_, .fst hstep⟩
  | snd _ ih_p =>
    intro A h
    obtain ⟨_, Hs, _⟩ := (h.toHasType (Γ := []) trivial).1.toStructural
    let .snd _ _ _ h_p := Hs
    rcases ih_p h_p.hasType with hv | ⟨p', hstep⟩
    · obtain ⟨_, _, _, _, rfl⟩ := hv.sigma_r (Γ := []) trivial h_p.hasType
      exact .inr ⟨_, .pair_snd⟩
    · exact .inr ⟨_, .snd hstep⟩
  | nat => intro A _; exact .inl .nat
  | zero => intro A _; exact .inl .zero
  | succ => intro A _; exact .inl .succ
  | natCase _ _ _ _ _ ih_M =>
    intro A h
    let ⟨_, .natCase _ _ hM _ _, _⟩ := (h.toHasType (Γ := []) trivial).1.toStructural
    rcases ih_M hM.hasType with hv | ⟨M', hstep⟩
    · rcases hv.nat_r (Γ := []) trivial hM.hasType with rfl | ⟨n', rfl⟩
      · exact .inr ⟨_, .natCase_zero⟩
      · exact .inr ⟨_, .natCase_succ⟩
    · exact .inr ⟨_, .natCase hstep⟩
  | Y => intro A _; exact .inr ⟨_, .Y⟩

/-- Progress for the standard judgment `IsDefEq₀`. -/
theorem progress' {e A : Term} (h : [] ⊢₀ e : A) : Value e ∨ ∃ e', e ⤳ e' :=
  progress ((IsDefEq.iff (Γ := []) trivial).2 h)
