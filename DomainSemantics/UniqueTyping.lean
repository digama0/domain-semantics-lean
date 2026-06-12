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
  | base : Γ ⊨ e :! A → Γ ⊨ e : A
  | defeq :
    Γ ⊢ A ≡ B : .sort u → Γ ⊨ e : A → Γ ⊨ e : B

end

scoped notation:65 Γ " ⊨ " e " : " A:36 => HasType Γ e A true
scoped notation:65 Γ " ⊨ " e " :! " A:36 => HasType Γ e A false

/-- A bundled `HasType` derivation can be projected back to a plain
`IsDefEq` derivation of reflexivity at the given type. -/
theorem HasType.hasType : HasType Γ e A b → Γ ⊢ e : A
  | .bvar h hA => .bvar h hA
  | .sort' => .sort
  | .app hA hB hBa ihf iha => .appDF hA hB ihf.hasType iha.hasType hBa
  | .lam ihA hB ihbody => .lamDF ihA.hasType hB ihbody.hasType ihbody.hasType
  | .forallE ihA ihbody => .forallEDF ihA.hasType ihbody.hasType ihbody.hasType
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
  | @app Γ' A _ _ _ a _ _ _ _ h_f h_a ih_f ih_a =>
    obtain ⟨_, H2_s, transport⟩ := H2.toStructural
    let .app _ _ _ h_f' _ := H2_s
    obtain ⟨_, h_pi_eq⟩ := ih_f hΓ h_f'
    obtain ⟨_, _, h_A_eq, h_B_eq⟩ := forallE_inv hΓ h_pi_eq
    have hΓA : ⊢ A :: Γ' := ⟨hΓ, _, h_A_eq.hasType.1⟩
    have W : Ctx.SubstEq Γ' (.one a) (.one a) (A :: Γ') :=
      .cons (Ctx.SubstEq.id hΓ) h_A_eq.hasType.1
        (by simpa using h_a.hasType)
    exact transport (h_B_eq.subst hΓ hΓA W)
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
  | base _ ih_s => exact ih_s hΓ H2
  | defeq d _ ihe =>
    obtain ⟨_, eq⟩ := ihe hΓ H2
    exact ⟨_, d.symm.trans' eq⟩

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
  | appDF hA hB _ _ h_Ba _ _ ih_f ih_a _ =>
    exact ⟨.base (.app hA hB h_Ba.hasType.1 (ih_f hΓ).1 (ih_a hΓ).1),
      .defeq h_Ba.symm
        (.base (.app hA hB h_Ba.hasType.2 (ih_f hΓ).2 (ih_a hΓ).2))⟩
  | lamDF h_A hB hbody hbody' ih_A _ ih_body ih_body' =>
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
  | proofIrrel _ _ _ _ ih_h ih_h' => exact ⟨(ih_h hΓ).1, (ih_h' hΓ).1⟩

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
    | appDF _ _ ih1 ih2 => exact .appDF₀ hΓ (ih1 hΓ) (ih2 hΓ)
    | lamDF _ _ ih1 ih2 => exact .lamDF₀ hΓ (ih1 hΓ) (ih2 ⟨hΓ, _, (ih1 hΓ).hasType.1⟩)
    | forallEDF _ _ ih1 ih2 => exact .forallEDF₀ hΓ (ih1 hΓ) (ih2 ⟨hΓ, _, (ih1 hΓ).hasType.1⟩)
    | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 hΓ) (ih2 hΓ)
    | beta _ _ ih1 ih2 => exact .beta₀ hΓ (ih1 ⟨hΓ, (ih2 hΓ).isType hΓ⟩) (ih2 hΓ)
    | eta _ ih => exact .eta₀ hΓ (ih hΓ)
    | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 hΓ) (ih2 hΓ) (ih3 hΓ)
  · induction h with
    | bvar h _ => exact .bvar h
    | symm _ ih => exact .symm (ih hΓ)
    | trans _ _ ih1 ih2 => exact .trans (ih1 hΓ) (ih2 hΓ)
    | trans' h1 h2 ih1 ih2 => cases h1.uniq_sort hΓ h2; exact .trans (ih1 hΓ) (ih2 hΓ)
    | sort => exact .sort
    | appDF _ _ _ _ _ _ _ ih2 ih3 _ => exact .appDF (ih2 hΓ) (ih3 hΓ)
    | lamDF h1 _ _ _ ih1 _ ih2 _ => exact .lamDF (ih1 hΓ) (ih2 ⟨hΓ, _, h1.hasType.1⟩)
    | forallEDF h1 _ _ ih1 ih2 _ => exact .forallEDF (ih1 hΓ) (ih2 ⟨hΓ, _, h1.hasType.1⟩)
    | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 hΓ) (ih2 hΓ)
    | beta h1 _ _ _ _ _ ih1 ih2 => exact .beta (ih1 ⟨hΓ, _, h1⟩) (ih2 hΓ)
    | eta _ _ ih => exact .eta (ih hΓ)
    | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 hΓ) (ih2 hΓ) (ih3 hΓ)

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
