import DomainSemantics.Interp

/-! # Directedness

Two approximants of a term have a common upper bound that is again an
approximant.  This is the other repo's `HasIdeality`, and it is what lets
the approximant set be read as an ideal.

It is a separate induction on typing, before soundness and independent of
it, and this file is that induction and nothing else.  `SoundDir`'s own
docstring, just below, says why it cannot be a lemma about `Interp` alone
and why it must not travel with `SoundEq`/`SoundTy`.

Because it stands alone, directedness holds of every well-typed term
before anything downstream runs — so nothing downstream carries a
directedness premise, and `SoundDir` is not mentioned outside this file.
A lemma that needs two approximants joined takes a *typing* and reads
`IsDefEq.dir`; a substitution's in-range slots go through
`Ctx.SubstEq.dir`, and nothing asks about the others. -/

namespace DomainSemantics

/-- Directedness of the approximant set: his `HasIdeality`.

**Not** a conclusion of `IsDefEq.sound`, and not a lemma about `Interp`
alone either — it is `IsDefEq.dir`, its own induction on *typing*.  Two
things decide that.

It cannot be about raw terms, because joining two λ-shapes appends their
graphs and the `lam` rule demands the result well formed, whose coherence
conjunct includes the cross pairs: entries of the two graphs whose labels
become definitionally equal at a later stage must have compatible outputs
there.  Discharging that moves both bodies to one stage along the label
equation, and the hypothesis of `IsDefEq.stage` is a *typed* substitution
equality — so the binder's annotation has to be typed, which a raw term
does not say.  That is the whole residue of the other repo's quotient,
where a stage is a morphism and carries its typing.

But it need not travel with `SoundEq`/`SoundTy` either, and it should not:
the hypothesis here is `Valuation.WF`, not `Adm`, so the recursive call
under a binder — at the joined argument slot — has nothing to type.  With
`Adm` it would need the joined slot typed at an approximant of `⟦A⟧`,
which is `SoundJoin` and, at Σ, unproved.  His `IsIdealValued` is likewise
directedness at *every* shape, and master's `compat_join` takes no `Fits`.
His bundling into `RawTermProperties` is forced only because his
application is a sup over `sourceQuery` and needs `PiReady` plus
fixedness to collapse; ours names the label and looks up once.

The conclusion is his `IsDirected` — a common upper bound *in the set* —
rather than master's `Compat ∧ join`, which is `SoundDir.join`. -/
def SoundDir (Γ : List Term) (t : Term) : Prop :=
  ∀ {{Δ : List Term}} {σ ρ}, ⊢ Δ → Ctx.SubstEq Δ σ σ Γ → Valuation.WF Δ Γ ρ →
    ∀ {{m₁ m₂}}, Interp Δ Γ t σ ρ m₁ → Interp Δ Γ t σ ρ m₂ →
      ∃ s, TShape.WF Δ s ∧ Interp Δ Γ t σ ρ s ∧ TShape.LE Δ m₁ s ∧ TShape.LE Δ m₂ s

/-- Directedness gives compatibility and the join, master's form. -/
theorem SoundDir.join {Γ : List Term} {t} (h : SoundDir Γ t) {Δ σ ρ} (hΔ : ⊢ Δ)
    (W : Ctx.SubstEq Δ σ σ Γ) (hρ : Valuation.WF Δ Γ ρ) {m₁ m₂}
    (h₁ : Interp Δ Γ t σ ρ m₁) (h₂ : Interp Δ Γ t σ ρ m₂) :
    TShape.Compat Δ m₁ m₂ ∧ Interp Δ Γ t σ ρ (m₁.join m₂) := by
  obtain ⟨s, hws, hs, hle₁, hle₂⟩ := h hΔ W hρ h₁ h₂
  have hc := TShape.Compat.of_common_upper hΔ hws hle₁ hle₂
  exact ⟨hc, hs.mono hΔ (TShape.join_le hΔ hle₁ hle₂)⟩

/-- Directedness for such a term: `⊥` is its own upper bound. -/
theorem dir_of_bot {Γ : List Term} {t : Term}
    (h : ∀ {Δ Γ' σ ρ m}, Interp Δ Γ' t σ ρ m → m.2 = Shape.bot) : SoundDir Γ t := by
  intro _ _ _ _ _ _ _ _ hm₁ hm₂
  exact ⟨.bot, trivial, .of_bot rfl, TShape.bot_le' (h hm₁), TShape.bot_le' (h hm₂)⟩

/-- Directedness for a variable: its slot bounds everything. -/
theorem dir_bvar {Γ : List Term} {i : Nat} {A : Term} (hlk : Lookup Γ i A) :
    SoundDir Γ (.bvar i) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  refine ⟨ρ i, hwρ hlk, .bvar hlk (TShape.LE.refl (hwρ hlk)), ?_, ?_⟩
  · cases h₁ with
    | bot => exact TShape.bot_le' rfl
    | bvar _ hle => exact hle
  · cases h₂ with
    | bot => exact TShape.bot_le' rfl
    | bvar _ hle => exact hle

/-- Directedness for such a term: the canonical shape bounds everything. -/
theorem dir_atom {Γ : List Term} {t : Term} {s : TShape}
    (hle : ∀ {Δ Γ' σ ρ m}, Interp Δ Γ' t σ ρ m → TShape.LE Δ m s)
    (hmk : ∀ {Δ Γ' σ ρ m}, TShape.LE Δ m s → Interp Δ Γ' t σ ρ m)
    (hws : ∀ {Δ : List Term}, TShape.WF Δ s) : SoundDir Γ t := by
  intro _ _ _ _ _ _ _ _ hm₁ hm₂
  exact ⟨s, hws, hmk (TShape.LE.refl hws), hle hm₁, hle hm₂⟩

theorem IsDefEq.stage {Γ : List Term} {t t' A : Term} (hΓ : ⊢ Γ)
    (H : Γ ⊢ t ≡ t' : A) {Δ : List Term} {σ σ' : Subst} (hΔ : ⊢ Δ)
    (W : Ctx.SubstEq Δ σ σ' Γ) {ρ m} :
    Interp Δ Γ t σ ρ m → Interp Δ Γ t σ' ρ m :=
  Interp.stage hΔ hΓ H.annot.1 W

/-! ## Directedness

Directedness is always established through a **common upper bound**: that
is the whole content of `SoundDir`, and compatibility and the join come
off it by `SoundDir.join`.  `Compat` has no introduction rule of its
own, so there is no other way.

The Π case is the other repo's `BasisAction.pi_isDirected` — bound the two
domain shapes inside `⟦A⟧`, append the two graphs, and the generator is
monotone in both — resting on his `GraphValid.internallyCompatible` for
the appended graph's cross pairs.  That argument transfers step for step,
with `IsDefEq.stage` doing the work his quotient does for free:

| his | ours |
|---|---|
| the label equation puts both memberships in one lower set | `IsDefEq.stage` |
| `Compatible.upper` | the join of the two inputs |
| monotonicity of the codomain family in its argument | `Interp.mono_val` |
| `IsIdealValued` at that upper bound | the codomain's own `SoundDir` |
| `Compatible.of_common_upper` | ours, same name |

His `IsIdealValued` is directedness at *every* argument shape, with no
"the argument is in `⟦A⟧`" side condition, because his body action coerces
its argument through `rawExtend ⟦A⟧` first.  Ours is `SoundDir` under a
`Valuation.WF` hypothesis, which asks nothing of the slot either — and
that is what keeps `SoundJoin` out of this proof. -/

/-- Directedness of a Π-type's interpretation: the `forallEDF` case of
`IsDefEq.dir`. -/
theorem sound_forallE_dir {Γ : List Term} {A B : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B ≡ B : .sort v)
    (ihAdir : SoundDir Γ A) (ihBdir : SoundDir (A :: Γ) B) :
    SoundDir Γ (.forallE A B) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | @forallE _ _ _ _ n₁ g₁ d₁ _ _ hA₁ hd₁ hwf₁ hNV₁ hbody₁ hle₁ hAt hBt
  cases h₂ with
  | bot =>
    refine ⟨_, ?_, ?_, hle₁, TShape.bot_le' rfl⟩
    · exact hwf₁
    · exact .forallE hA₁ hd₁  hwf₁ hNV₁ hbody₁ (TShape.LE.refl hwf₁) hAt hBt
  | @forallE _ _ _ _ n₂ g₂ d₂ _ _ hA₂ hd₂ hwf₂ hNV₂ hbody₂ hle₂ _ _
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hAty⟩
  have k₁ : n₁ ≤ max n₁ n₂ := Nat.le_max_left ..
  have k₂ : n₂ ≤ max n₁ n₂ := Nat.le_max_right ..
  -- the joined domain, from `A`'s own directedness
  have ⟨hcd, hdj⟩ := ihAdir.join hΔ W hwρ hA₁ hA₂
  have hcd' : Shape.Compat Δ (d₁.lift (max n₁ n₂)) (d₂.lift (max n₁ n₂)) :=
    (TShape.Compat.def k₁ k₂).1 hcd
  have hwd₁ : Shape.WF Δ d₁ := Shape.WF.forget hwf₁.2.2.1
  have hwd₂ : Shape.WF Δ d₂ := Shape.WF.forget hwf₂.2.2.1
  have hwdj : Shape.WF Δ ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂))) :=
    Shape.WF.join hΔ hcd' ((Shape.lift_wf k₁).2 hwd₁) ((Shape.lift_wf k₂).2 hwd₂)
  have hdj' : Interp Δ Γ A σ ρ
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) := hdj
  -- and its typing, from the two domains' own, joined at a *sort*
  have hdjty : TShape.HasType Δ
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) TShape.type :=
    TShape.HasType.join_sort hΔ rfl (hd₁.lift_subject hΔ k₁) (hd₂.lift_subject hΔ k₂) hcd'
  have hled₁ : TShape.LE Δ (Shape.T d₁)
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) :=
    (TShape.LE.def hΔ k₁ (Nat.le_refl _)).2 <| by
      rw [Shape.lift_self]
      exact (Shape.le_join hΔ ((Shape.lift_wf k₁).2 hwd₁)
        ((Shape.lift_wf k₂).2 hwd₂) hcd').1
  have hled₂ : TShape.LE Δ (Shape.T d₂)
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) :=
    (TShape.LE.def hΔ k₂ (Nat.le_refl _)).2 <| by
      rw [Shape.lift_self]
      exact (Shape.le_join hΔ ((Shape.lift_wf k₁).2 hwd₁)
        ((Shape.lift_wf k₂).2 hwd₂) hcd').2
  -- each graph entry's input, typed at the joined domain
  have hdomj₁ : ∀ e ∈ g₁, TShape.Named Δ (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) (Shape.T e.inp) e.tm :=
    fun e he =>
    TShape.Named.mono_r hΔ (hNV₁ e he) hled₁ hdjty
  have hdomj₂ : ∀ e ∈ g₂, TShape.Named Δ (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) (Shape.T e.inp) e.tm :=
    fun e he =>
    TShape.Named.mono_r hΔ (hNV₂ e he) hled₂ hdjty
  -- **the cross pairs**
  have hcross : ShapeFun.Compat Shape.Compat Δ (A.subst σ)
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁)
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂) := by
    intro e he e' he' Θ τ hΘ Wτ hlab hin
    obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
    obtain ⟨b, hb, rfl⟩ := ShapeFun.mem_lift.1 he'
    have hwa := hwf₁.2.2.2.1.1 a ha
    have hwb := hwf₂.2.2.2.1.1 b hb
    have Wc : Ctx.SubstEq Θ (σ.comp τ) (σ.comp τ) Γ := Ctx.SubstEq.comp hΘ Wτ W
    have hwρτ : Valuation.WF Θ Γ (ρ.subst τ) := Valuation.WF.subst hΘ Wτ hwρ
    -- the two inputs, read at the common level, and their join
    rw [← Shape.lift_subst, ← Shape.lift_subst] at hin
    have hwx₁ : TShape.WF Θ (Shape.T ((a.inp.subst τ).lift (max n₁ n₂))) :=
      (Shape.lift_wf k₁).2 (Shape.WF.subst hΘ Wτ hwa.2.2.1)
    have hwx₂ : TShape.WF Θ (Shape.T ((b.inp.subst τ).lift (max n₁ n₂))) :=
      (Shape.lift_wf k₂).2 (Shape.WF.subst hΘ Wτ hwb.2.2.1)
    have hcx : TShape.Compat Θ (Shape.T ((a.inp.subst τ).lift (max n₁ n₂)))
        (Shape.T ((b.inp.subst τ).lift (max n₁ n₂))) := TShape.Compat.T.2 hin
    have hwxj := TShape.WF.join hΘ hcx hwx₁ hwx₂
    have ⟨hjx₁, hjx₂⟩ := TShape.le_join hΘ hwx₁ hwx₂ hcx
    -- the label equation, which is what puts the two bodies at one stage
    have heq : Θ ⊢ b.tm.subst τ ≡ a.tm.subst τ : (A.subst σ).subst τ := hlab.2.symm
    rw [subst_subst] at heq
    have Wcons : Ctx.SubstEq Θ ((σ.comp τ).cons (b.tm.subst τ))
        ((σ.comp τ).cons (a.tm.subst τ)) (A :: Γ) := .cons Wc hAty heq
    have Wdiag : Ctx.SubstEq Θ ((σ.comp τ).cons (a.tm.subst τ))
        ((σ.comp τ).cons (a.tm.subst τ)) (A :: Γ) := .cons Wc hAty heq.hasType.2
    -- the two bodies, at that one stage and above that one slot
    have hb₁ := (hbody₁ a ha).subst hΘ Wτ
    have hb₂0 := (hbody₂ b hb).subst hΘ Wτ
    rw [Subst.cons_comp, Valuation.subst_push] at hb₁ hb₂0
    have hb₂ := IsDefEq.stage hΓA hB hΘ Wcons hb₂0
    have hB₁ := Interp.mono_val hΘ (Valuation.LE.push.2
      ⟨Valuation.LE.refl hwρτ,
        TShape.LE.trans hΘ (TShape.LE.le_lift hΘ (m := Shape.T (a.inp.subst τ)) k₁
          (Shape.WF.subst hΘ Wτ hwa.2.2.1)) hjx₁⟩) hb₁
    have hB₂ := Interp.mono_val hΘ (Valuation.LE.push.2
      ⟨Valuation.LE.refl hwρτ,
        TShape.LE.trans hΘ (TShape.LE.le_lift hΘ (m := Shape.T (b.inp.subst τ)) k₂
          (Shape.WF.subst hΘ Wτ hwb.2.2.1)) hjx₂⟩) hb₂
    obtain ⟨_, _, _, hs₁, hs₂⟩ :=
      ihBdir hΘ Wdiag (Valuation.WF.push hwρτ hwxj) hB₁ hB₂
    rw [← Shape.lift_subst, ← Shape.lift_subst]
    exact (TShape.Compat.def k₁ k₂).1
      (TShape.Compat.of_common_upper hΘ (by assumption) hs₁ hs₂)
  -- the two Π-shapes are compatible, so their join is well formed
  obtain ⟨_, hAσ⟩ := hwf₁.1
  obtain ⟨_, hBσ⟩ := hwf₁.2.1
  have hcS : Shape.Compat (n := max n₁ n₂ + 1) Δ
      (.forallE (A.subst σ) (B.subst σ.lift) (d₁.lift (max n₁ n₂))
        (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁))
      (.forallE (A.subst σ) (B.subst σ.lift) (d₂.lift (max n₁ n₂))
        (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂)) :=
    ⟨PiLabelEq.refl hAσ hBσ, hcd', hcross⟩
  have hwS₁ : Shape.WF Δ (Shape.lift (n := n₁+1) (max n₁ n₂ + 1)
      (.forallE (A.subst σ) (B.subst σ.lift) d₁ g₁)) :=
    (Shape.lift_wf (Nat.succ_le_succ k₁)).2 hwf₁
  have hwS₂ : Shape.WF Δ (Shape.lift (n := n₂+1) (max n₁ n₂ + 1)
      (.forallE (A.subst σ) (B.subst σ.lift) d₂ g₂)) :=
    (Shape.lift_wf (Nat.succ_le_succ k₂)).2 hwf₂
  have hwSJ : Shape.WF (n := max n₁ n₂ + 1) Δ
      (.forallE (A.subst σ) (B.subst σ.lift)
        ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))
        (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁ ++
          ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂)) :=
    Shape.WF.join hΔ hcS hwS₁ hwS₂
  refine ⟨Shape.T (n := max n₁ n₂ + 1) (.forallE (A.subst σ) (B.subst σ.lift)
      ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁ ++ ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂)),
    hwSJ, .forallE hdj' hdjty hwSJ ?_ ?_ (TShape.LE.refl hwSJ) ⟨u, hAty⟩ ⟨v, hB⟩,
    TShape.LE.trans hΔ hle₁ ((TShape.LE.def hΔ (Nat.succ_le_succ k₁) (Nat.le_refl _)).2 ?_),
    TShape.LE.trans hΔ hle₂ ((TShape.LE.def hΔ (Nat.succ_le_succ k₂) (Nat.le_refl _)).2 ?_)⟩
  · -- inputs typed at the joined domain, with their names
    intro e he
    match List.mem_append.1 he with
    | .inl he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact TShape.Named.lift_subject hΔ (hdomj₁ a ha) (by omega)
    | .inr he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact TShape.Named.lift_subject hΔ (hdomj₂ a ha) (by omega)
  · -- bodies
    intro e he
    match List.mem_append.1 he with
    | .inl he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact Interp.lift hΔ k₁ (Interp.mono_val hΔ (Valuation.LE.push.2
        ⟨Valuation.LE.refl hwρ,
          TShape.LE.le_lift hΔ (m := Shape.T a.inp) k₁ (hwf₁.2.2.2.1.1 a ha).2.2.1⟩)
        (hbody₁ a ha))
    | .inr he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact Interp.lift hΔ k₂ (Interp.mono_val hΔ (Valuation.LE.push.2
        ⟨Valuation.LE.refl hwρ,
          TShape.LE.le_lift hΔ (m := Shape.T a.inp) k₂ (hwf₂.2.2.2.1.1 a ha).2.2.1⟩)
        (hbody₂ a ha))
  · rw [Shape.lift_self]; exact (Shape.le_join hΔ hwS₁ hwS₂ hcS).1
  · rw [Shape.lift_self]; exact (Shape.le_join hΔ hwS₁ hwS₂ hcS).2

/-- Directedness of a Σ-type's interpretation: the `sigmaDF` case of
`IsDefEq.dir`.

The upper bound of two Σ-shapes has the same labels (both come from the
same term at the same stage), the domains joined by `A`'s directedness,
and the graphs appended.  All the content is the appended graph's
coherence, and there the cross pairs; see the section comment.  The
domain of the joined shape is a type because each domain is — the
`Interp.sigma` premise added for exactly this — and `HasType.join` at a
*sort* is available. -/
theorem sound_sigma_dir {Γ : List Term} {A B : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B ≡ B : .sort v)
    (ihAdir : SoundDir Γ A) (ihBdir : SoundDir (A :: Γ) B) :
    SoundDir Γ (.sigma A B) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | @sigma _ _ _ _ n₁ g₁ d₁ _ _ hA₁ hd₁ hwf₁ hNV₁ hbody₁ hle₁ hAt hBt
  cases h₂ with
  | bot =>
    refine ⟨_, ?_, ?_, hle₁, TShape.bot_le' rfl⟩
    · exact hwf₁
    · exact .sigma hA₁ hd₁  hwf₁ hNV₁ hbody₁ (TShape.LE.refl hwf₁) hAt hBt
  | @sigma _ _ _ _ n₂ g₂ d₂ _ _ hA₂ hd₂ hwf₂ hNV₂ hbody₂ hle₂ _ _
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hAty⟩
  have k₁ : n₁ ≤ max n₁ n₂ := Nat.le_max_left ..
  have k₂ : n₂ ≤ max n₁ n₂ := Nat.le_max_right ..
  -- the joined domain, from `A`'s own directedness
  have ⟨hcd, hdj⟩ := ihAdir.join hΔ W hwρ hA₁ hA₂
  have hcd' : Shape.Compat Δ (d₁.lift (max n₁ n₂)) (d₂.lift (max n₁ n₂)) :=
    (TShape.Compat.def k₁ k₂).1 hcd
  have hwd₁ : Shape.WF Δ d₁ := Shape.WF.forget hwf₁.2.2.1
  have hwd₂ : Shape.WF Δ d₂ := Shape.WF.forget hwf₂.2.2.1
  have hwdj : Shape.WF Δ ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂))) :=
    Shape.WF.join hΔ hcd' ((Shape.lift_wf k₁).2 hwd₁) ((Shape.lift_wf k₂).2 hwd₂)
  have hdj' : Interp Δ Γ A σ ρ
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) := hdj
  -- and its typing, from the two domains' own, joined at a *sort*
  have hdjty : TShape.HasType Δ
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) TShape.type :=
    TShape.HasType.join_sort hΔ rfl (hd₁.lift_subject hΔ k₁) (hd₂.lift_subject hΔ k₂) hcd'
  have hled₁ : TShape.LE Δ (Shape.T d₁)
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) :=
    (TShape.LE.def hΔ k₁ (Nat.le_refl _)).2 <| by
      rw [Shape.lift_self]
      exact (Shape.le_join hΔ ((Shape.lift_wf k₁).2 hwd₁)
        ((Shape.lift_wf k₂).2 hwd₂) hcd').1
  have hled₂ : TShape.LE Δ (Shape.T d₂)
      (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) :=
    (TShape.LE.def hΔ k₂ (Nat.le_refl _)).2 <| by
      rw [Shape.lift_self]
      exact (Shape.le_join hΔ ((Shape.lift_wf k₁).2 hwd₁)
        ((Shape.lift_wf k₂).2 hwd₂) hcd').2
  -- each graph entry's input, typed at the joined domain
  have hdomj₁ : ∀ e ∈ g₁, TShape.Named Δ (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) (Shape.T e.inp) e.tm :=
    fun e he =>
    TShape.Named.mono_r hΔ (hNV₁ e he) hled₁ hdjty
  have hdomj₂ : ∀ e ∈ g₂, TShape.Named Δ (Shape.T ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))) (Shape.T e.inp) e.tm :=
    fun e he =>
    TShape.Named.mono_r hΔ (hNV₂ e he) hled₂ hdjty
  -- **the cross pairs**
  have hcross : ShapeFun.Compat Shape.Compat Δ (A.subst σ)
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁)
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂) := by
    intro e he e' he' Θ τ hΘ Wτ hlab hin
    obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
    obtain ⟨b, hb, rfl⟩ := ShapeFun.mem_lift.1 he'
    have hwa := hwf₁.2.2.2.1.1 a ha
    have hwb := hwf₂.2.2.2.1.1 b hb
    have Wc : Ctx.SubstEq Θ (σ.comp τ) (σ.comp τ) Γ := Ctx.SubstEq.comp hΘ Wτ W
    have hwρτ : Valuation.WF Θ Γ (ρ.subst τ) := Valuation.WF.subst hΘ Wτ hwρ
    -- the two inputs, read at the common level, and their join
    rw [← Shape.lift_subst, ← Shape.lift_subst] at hin
    have hwx₁ : TShape.WF Θ (Shape.T ((a.inp.subst τ).lift (max n₁ n₂))) :=
      (Shape.lift_wf k₁).2 (Shape.WF.subst hΘ Wτ hwa.2.2.1)
    have hwx₂ : TShape.WF Θ (Shape.T ((b.inp.subst τ).lift (max n₁ n₂))) :=
      (Shape.lift_wf k₂).2 (Shape.WF.subst hΘ Wτ hwb.2.2.1)
    have hcx : TShape.Compat Θ (Shape.T ((a.inp.subst τ).lift (max n₁ n₂)))
        (Shape.T ((b.inp.subst τ).lift (max n₁ n₂))) := TShape.Compat.T.2 hin
    have hwxj := TShape.WF.join hΘ hcx hwx₁ hwx₂
    have ⟨hjx₁, hjx₂⟩ := TShape.le_join hΘ hwx₁ hwx₂ hcx
    -- the label equation, which is what puts the two bodies at one stage
    have heq : Θ ⊢ b.tm.subst τ ≡ a.tm.subst τ : (A.subst σ).subst τ := hlab.2.symm
    rw [subst_subst] at heq
    have Wcons : Ctx.SubstEq Θ ((σ.comp τ).cons (b.tm.subst τ))
        ((σ.comp τ).cons (a.tm.subst τ)) (A :: Γ) := .cons Wc hAty heq
    have Wdiag : Ctx.SubstEq Θ ((σ.comp τ).cons (a.tm.subst τ))
        ((σ.comp τ).cons (a.tm.subst τ)) (A :: Γ) := .cons Wc hAty heq.hasType.2
    -- the two bodies, at that one stage and above that one slot
    have hb₁ := (hbody₁ a ha).subst hΘ Wτ
    have hb₂0 := (hbody₂ b hb).subst hΘ Wτ
    rw [Subst.cons_comp, Valuation.subst_push] at hb₁ hb₂0
    have hb₂ := IsDefEq.stage hΓA hB hΘ Wcons hb₂0
    have hB₁ := Interp.mono_val hΘ (Valuation.LE.push.2
      ⟨Valuation.LE.refl hwρτ,
        TShape.LE.trans hΘ (TShape.LE.le_lift hΘ (m := Shape.T (a.inp.subst τ)) k₁
          (Shape.WF.subst hΘ Wτ hwa.2.2.1)) hjx₁⟩) hb₁
    have hB₂ := Interp.mono_val hΘ (Valuation.LE.push.2
      ⟨Valuation.LE.refl hwρτ,
        TShape.LE.trans hΘ (TShape.LE.le_lift hΘ (m := Shape.T (b.inp.subst τ)) k₂
          (Shape.WF.subst hΘ Wτ hwb.2.2.1)) hjx₂⟩) hb₂
    obtain ⟨_, _, _, hs₁, hs₂⟩ :=
      ihBdir hΘ Wdiag (Valuation.WF.push hwρτ hwxj) hB₁ hB₂
    rw [← Shape.lift_subst, ← Shape.lift_subst]
    exact (TShape.Compat.def k₁ k₂).1
      (TShape.Compat.of_common_upper hΘ (by assumption) hs₁ hs₂)
  -- the two Σ-shapes are compatible, so their join is well formed
  obtain ⟨_, hAσ⟩ := hwf₁.1
  obtain ⟨_, hBσ⟩ := hwf₁.2.1
  have hcS : Shape.Compat (n := max n₁ n₂ + 1) Δ
      (.sigma (A.subst σ) (B.subst σ.lift) (d₁.lift (max n₁ n₂))
        (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁))
      (.sigma (A.subst σ) (B.subst σ.lift) (d₂.lift (max n₁ n₂))
        (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂)) :=
    ⟨PiLabelEq.refl hAσ hBσ, hcd', hcross⟩
  have hwS₁ : Shape.WF Δ (Shape.lift (n := n₁+1) (max n₁ n₂ + 1)
      (.sigma (A.subst σ) (B.subst σ.lift) d₁ g₁)) :=
    (Shape.lift_wf (Nat.succ_le_succ k₁)).2 hwf₁
  have hwS₂ : Shape.WF Δ (Shape.lift (n := n₂+1) (max n₁ n₂ + 1)
      (.sigma (A.subst σ) (B.subst σ.lift) d₂ g₂)) :=
    (Shape.lift_wf (Nat.succ_le_succ k₂)).2 hwf₂
  have hwSJ : Shape.WF (n := max n₁ n₂ + 1) Δ
      (.sigma (A.subst σ) (B.subst σ.lift)
        ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))
        (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁ ++
          ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂)) :=
    Shape.WF.join hΔ hcS hwS₁ hwS₂
  refine ⟨Shape.T (n := max n₁ n₂ + 1) (.sigma (A.subst σ) (B.subst σ.lift)
      ((d₁.lift (max n₁ n₂)).join (d₂.lift (max n₁ n₂)))
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁ ++ ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂)),
    hwSJ, .sigma hdj' hdjty hwSJ ?_ ?_ (TShape.LE.refl hwSJ) ⟨u, hAty⟩ ⟨v, hB⟩,
    TShape.LE.trans hΔ hle₁ ((TShape.LE.def hΔ (Nat.succ_le_succ k₁) (Nat.le_refl _)).2 ?_),
    TShape.LE.trans hΔ hle₂ ((TShape.LE.def hΔ (Nat.succ_le_succ k₂) (Nat.le_refl _)).2 ?_)⟩
  · -- inputs typed at the joined domain, with their names
    intro e he
    match List.mem_append.1 he with
    | .inl he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact TShape.Named.lift_subject hΔ (hdomj₁ a ha) (by omega)
    | .inr he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact TShape.Named.lift_subject hΔ (hdomj₂ a ha) (by omega)
  · -- bodies
    intro e he
    match List.mem_append.1 he with
    | .inl he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact Interp.lift hΔ k₁ (Interp.mono_val hΔ (Valuation.LE.push.2
        ⟨Valuation.LE.refl hwρ,
          TShape.LE.le_lift hΔ (m := Shape.T a.inp) k₁ (hwf₁.2.2.2.1.1 a ha).2.2.1⟩)
        (hbody₁ a ha))
    | .inr he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact Interp.lift hΔ k₂ (Interp.mono_val hΔ (Valuation.LE.push.2
        ⟨Valuation.LE.refl hwρ,
          TShape.LE.le_lift hΔ (m := Shape.T a.inp) k₂ (hwf₂.2.2.2.1.1 a ha).2.2.1⟩)
        (hbody₂ a ha))
  · rw [Shape.lift_self]; exact (Shape.le_join hΔ hwS₁ hwS₂ hcS).1
  · rw [Shape.lift_self]; exact (Shape.le_join hΔ hwS₁ hwS₂ hcS).2

/-- Directedness of a λ: the `lamDF` case of `IsDefEq.dir`.

The upper bound of two λ-shapes has one label (both come from the same
term at the same stage) and the graphs appended. -/
theorem sound_lam_dir {Γ : List Term} {A B b : Term} {u : Bool}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hb : A :: Γ ⊢ b : B)
    (ihAdir : SoundDir Γ A) (ihbdir : SoundDir (A :: Γ) b) :
    SoundDir Γ (.lam A b) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | @lam _ _ _ _ n₁ g₁ d₁ _ _ hA₁ hd₁ hwf₁ hNV₁ hbody₁ hle₁ hAt
  cases h₂ with
  | bot =>
    refine ⟨_, ?_, ?_, hle₁, TShape.bot_le' rfl⟩
    · exact hwf₁
    · exact .lam hA₁ hd₁ hwf₁ hNV₁ hbody₁ (TShape.LE.refl hwf₁) hAt
  | @lam _ _ _ _ n₂ g₂ d₂ _ _ hA₂ hd₂ hwf₂ hNV₂ hbody₂ hle₂ _
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hAty⟩
  have k₁ : n₁ ≤ max n₁ n₂ := Nat.le_max_left ..
  have k₂ : n₂ ≤ max n₁ n₂ := Nat.le_max_right ..
  -- the joined domain shape, from `A`'s own directedness
  have ⟨hcd, hdj⟩ := ihAdir.join hΔ W hwρ hA₁ hA₂
  have hdjty : TShape.HasType Δ (d₁.join d₂) TShape.type :=
    TShape.HasType.join_sort' hΔ rfl hd₁ hd₂ hcd
  have ⟨hled₁, hled₂⟩ := TShape.le_join hΔ hA₁.wf hA₂.wf hcd
  have hdomj₁ : ∀ e ∈ g₁, TShape.Named Δ (d₁.join d₂) e.inp.T e.tm := fun e he =>
    TShape.Named.mono_r hΔ (hNV₁ e he) hled₁ hdjty
  have hdomj₂ : ∀ e ∈ g₂, TShape.Named Δ (d₁.join d₂) e.inp.T e.tm := fun e he =>
    TShape.Named.mono_r hΔ (hNV₂ e he) hled₂ hdjty
  -- **the cross pairs**: the body at the join of two entries' inputs, a
  -- valuation that is well formed but not admissible
  have hcross : ShapeFun.Compat Shape.Compat Δ (A.subst σ)
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁)
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂) := by
    intro e he e' he' Θ τ hΘ Wτ hlab hin
    obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
    obtain ⟨c, hc, rfl⟩ := ShapeFun.mem_lift.1 he'
    have hwa := hwf₁.2.2.1.1 a ha
    have hwc := hwf₂.2.2.1.1 c hc
    have Wc : Ctx.SubstEq Θ (σ.comp τ) (σ.comp τ) Γ := Ctx.SubstEq.comp hΘ Wτ W
    have hwρτ : Valuation.WF Θ Γ (ρ.subst τ) := Valuation.WF.subst hΘ Wτ hwρ
    rw [← Shape.lift_subst, ← Shape.lift_subst] at hin
    have hwx₁ : TShape.WF Θ (Shape.T ((a.inp.subst τ).lift (max n₁ n₂))) :=
      (Shape.lift_wf k₁).2 (Shape.WF.subst hΘ Wτ hwa.2.2.1)
    have hwx₂ : TShape.WF Θ (Shape.T ((c.inp.subst τ).lift (max n₁ n₂))) :=
      (Shape.lift_wf k₂).2 (Shape.WF.subst hΘ Wτ hwc.2.2.1)
    have hcx : TShape.Compat Θ (Shape.T ((a.inp.subst τ).lift (max n₁ n₂)))
        (Shape.T ((c.inp.subst τ).lift (max n₁ n₂))) := TShape.Compat.T.2 hin
    have hwxj := TShape.WF.join hΘ hcx hwx₁ hwx₂
    have ⟨hjx₁, hjx₂⟩ := TShape.le_join hΘ hwx₁ hwx₂ hcx
    -- the label equation, which puts the two bodies at one stage.  It is
    -- read at the domain label, the graph's type: this is what the
    -- λ-shape's label buys, and it holds at this non-admissible stage
    have heq : Θ ⊢ c.tm.subst τ ≡ a.tm.subst τ : (A.subst σ).subst τ := hlab.2.symm
    rw [subst_subst] at heq
    have Wcons : Ctx.SubstEq Θ ((σ.comp τ).cons (c.tm.subst τ))
        ((σ.comp τ).cons (a.tm.subst τ)) (A :: Γ) := .cons Wc hAty heq
    have Wdiag : Ctx.SubstEq Θ ((σ.comp τ).cons (a.tm.subst τ))
        ((σ.comp τ).cons (a.tm.subst τ)) (A :: Γ) := .cons Wc hAty heq.hasType.2
    have hb₁ := (hbody₁ a ha).subst hΘ Wτ
    have hb₂0 := (hbody₂ c hc).subst hΘ Wτ
    rw [Subst.cons_comp, Valuation.subst_push] at hb₁ hb₂0
    have hb₂ := IsDefEq.stage hΓA hb hΘ Wcons hb₂0
    have hB₁ := Interp.mono_val hΘ (Valuation.LE.push.2
      ⟨Valuation.LE.refl hwρτ,
        TShape.LE.trans hΘ (TShape.LE.le_lift hΘ (m := Shape.T (a.inp.subst τ)) k₁
          (Shape.WF.subst hΘ Wτ hwa.2.2.1)) hjx₁⟩) hb₁
    have hB₂ := Interp.mono_val hΘ (Valuation.LE.push.2
      ⟨Valuation.LE.refl hwρτ,
        TShape.LE.trans hΘ (TShape.LE.le_lift hΘ (m := Shape.T (c.inp.subst τ)) k₂
          (Shape.WF.subst hΘ Wτ hwc.2.2.1)) hjx₂⟩) hb₂
    obtain ⟨_, _, _, hs₁, hs₂⟩ :=
      ihbdir hΘ Wdiag (Valuation.WF.push hwρτ hwxj) hB₁ hB₂
    rw [← Shape.lift_subst, ← Shape.lift_subst]
    exact (TShape.Compat.def k₁ k₂).1
      (TShape.Compat.of_common_upper hΘ (by assumption) hs₁ hs₂)
  -- the two λ-shapes are compatible, so their join is well formed
  have hcS : Shape.Compat (n := max n₁ n₂ + 1) Δ
      (.lam (A.subst σ) (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁))
      (.lam (A.subst σ) (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂)) :=
    ⟨hwf₁.dom, hcross⟩
  have hwS₁ : Shape.WF Δ (Shape.lift (n := n₁+1) (max n₁ n₂ + 1) (.lam (A.subst σ) g₁)) :=
    (Shape.lift_wf (Nat.succ_le_succ k₁)).2 hwf₁
  have hwS₂ : Shape.WF Δ (Shape.lift (n := n₂+1) (max n₁ n₂ + 1) (.lam (A.subst σ) g₂)) :=
    (Shape.lift_wf (Nat.succ_le_succ k₂)).2 hwf₂
  have hwSJ : Shape.WF (n := max n₁ n₂ + 1) Δ
      (.lam (A.subst σ) (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁ ++
        ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂)) :=
    Shape.WF.join hΔ hcS hwS₁ hwS₂
  refine ⟨Shape.T (n := max n₁ n₂ + 1) (.lam (A.subst σ)
      (ShapeFun.lift (Shape.lift (max n₁ n₂)) g₁ ++ ShapeFun.lift (Shape.lift (max n₁ n₂)) g₂)),
    hwSJ, .lam hdj hdjty hwSJ ?_ ?_ (TShape.LE.refl hwSJ) ⟨u, hAty⟩,
    TShape.LE.trans hΔ hle₁ ((TShape.LE.def hΔ (Nat.succ_le_succ k₁) (Nat.le_refl _)).2 ?_),
    TShape.LE.trans hΔ hle₂ ((TShape.LE.def hΔ (Nat.succ_le_succ k₂) (Nat.le_refl _)).2 ?_)⟩
  · -- inputs typed at the joined domain, with their names
    intro e he
    match List.mem_append.1 he with
    | .inl he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact TShape.Named.lift_subject hΔ (hdomj₁ a ha) (by omega)
    | .inr he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact TShape.Named.lift_subject hΔ (hdomj₂ a ha) (by omega)
  · -- bodies
    intro e he
    match List.mem_append.1 he with
    | .inl he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact Interp.lift hΔ k₁ (Interp.mono_val hΔ (Valuation.LE.push.2
        ⟨Valuation.LE.refl hwρ,
          TShape.LE.le_lift hΔ (m := Shape.T a.inp) k₁ (hwf₁.2.2.1.1 a ha).2.2.1⟩)
        (hbody₁ a ha))
    | .inr he =>
      obtain ⟨a, ha, rfl⟩ := ShapeFun.mem_lift.1 he
      exact Interp.lift hΔ k₂ (Interp.mono_val hΔ (Valuation.LE.push.2
        ⟨Valuation.LE.refl hwρ,
          TShape.LE.le_lift hΔ (m := Shape.T a.inp) k₂ (hwf₂.2.2.1.1 a ha).2.2.1⟩)
        (hbody₂ a ha))
  · rw [Shape.lift_self]; exact (Shape.le_join hΔ hwS₁ hwS₂ hcS).1
  · rw [Shape.lift_self]; exact (Shape.le_join hΔ hwS₁ hwS₂ hcS).2

/-- Directedness of a pair: the `pairDF` case of `IsDefEq.dir`.

The upper bound has the components joined by their own directedness, the
name shared (the clause reads it off the term), and the codomain code
joined by the body's.  With the graph gone this is shorter than the λ
case: there are no entries to merge and no stage to move. -/
theorem dir_pair {Γ : List Term} {A B a b : Term}
    (ihA : SoundDir Γ A) (ihB : SoundDir (A :: Γ) B)
    (iha : SoundDir Γ a) (ihb : SoundDir Γ b) :
    SoundDir Γ (.pair A B a b) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | @pair _ _ _ _ n₁ x₁ y₁ d₁ c₁ _ _ _ _ ha₁ hb₁ hA₁ hd₁ hNV₁ hdc₁ hwf₁ hcode₁ hcty₁
      hlm₁ hAt hat
  cases h₂ with
  | bot =>
    exact ⟨_, hlm₁.wf, .pair ha₁ hb₁ hA₁ hd₁ hNV₁ hdc₁ hwf₁ hcode₁ hcty₁ hlm₁ hAt hat,
      TShape.LE.refl hlm₁.wf, TShape.bot_le' rfl⟩
  | @pair _ _ _ _ n₂ x₂ y₂ d₂ c₂ _ _ _ _ ha₂ hb₂ hA₂ hd₂ hNV₂ hdc₂ hwf₂ hcode₂ hcty₂
      hlm₂ _ _
  have k₁ : n₁ ≤ max n₁ n₂ := Nat.le_max_left ..
  have k₂ : n₂ ≤ max n₁ n₂ := Nat.le_max_right ..
  -- the components and the domain join, by their own directedness
  obtain ⟨hcx, hjx⟩ := iha.join hΔ W hwρ ha₁ ha₂
  obtain ⟨hcy, hjy⟩ := ihb.join hΔ W hwρ hb₁ hb₂
  obtain ⟨hcd, hjd⟩ := ihA.join hΔ W hwρ hA₁ hA₂
  have hdjty : TShape.HasType Δ (d₁.join d₂) TShape.type :=
    TShape.HasType.join_sort' hΔ rfl hd₁ hd₂ hcd
  have ⟨hled₁, hled₂⟩ := TShape.le_join hΔ hA₁.wf hA₂.wf hcd
  obtain ⟨uA, hAσ⟩ := hwf₁.2.2.1
  -- the first components, lifted to the common level and joined
  have hcxl : TShape.Compat Δ (Shape.T (x₁.lift (max n₁ n₂)))
      (Shape.T (x₂.lift (max n₁ n₂))) :=
    TShape.Compat.T.2 ((TShape.Compat.def k₁ k₂).1 hcx)
  have hcyl : TShape.Compat Δ (Shape.T (y₁.lift (max n₁ n₂)))
      (Shape.T (y₂.lift (max n₁ n₂))) :=
    TShape.Compat.T.2 ((TShape.Compat.def k₁ k₂).1 hcy)
  have hwx₁ : TShape.WF Δ (Shape.T x₁) := TShape.WF.T.2 hwf₁.2.2.2.1
  have hwx₂ : TShape.WF Δ (Shape.T x₂) := TShape.WF.T.2 hwf₂.2.2.2.1
  -- the codes, read at the joined slot and joined there
  have hle₁ : Valuation.LE Δ (A :: Γ) (ρ.push (Shape.T x₁)) (ρ.push (Shape.T x₁ |>.join (Shape.T x₂))) :=
    Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, (TShape.le_join hΔ hwx₁ hwx₂ hcx).1⟩
  have hle₂ : Valuation.LE Δ (A :: Γ) (ρ.push (Shape.T x₂)) (ρ.push (Shape.T x₁ |>.join (Shape.T x₂))) :=
    Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, (TShape.le_join hΔ hwx₁ hwx₂ hcx).2⟩
  have hcode₁' := Interp.mono_val hΔ hle₁ hcode₁
  have hcode₂' := Interp.mono_val hΔ hle₂ hcode₂
  have Wcons : Ctx.SubstEq Δ (σ.cons (a.subst σ)) (σ.cons (a.subst σ)) (A :: Γ) := by
    obtain ⟨_, hAt⟩ := hAt
    exact .cons W hAt (IsDefEq.subst hΔ W hat)
  obtain ⟨hcc, hjc⟩ :=
    ihB.join hΔ Wcons (Valuation.WF.push hwρ (TShape.WF.join hΔ hcx hwx₁ hwx₂))
      hcode₁' hcode₂'
  have hwS : Shape.WF (n := max n₁ n₂ + 1) Δ
      (.pair (A.subst σ) (a.subst σ) (x₁.lift (max n₁ n₂) |>.join (x₂.lift (max n₁ n₂)))
        (y₁.lift (max n₁ n₂) |>.join (y₂.lift (max n₁ n₂)))) := by
    refine ⟨?_, hwf₁.2.1, hwf₁.2.2.1, ?_, ?_⟩
    · intro hb
      exact hwf₁.1 ⟨(Shape.lift_isBot k₁).1 (Shape.IsBot.of_join_left hb.1),
        (Shape.lift_isBot k₁).1 (Shape.IsBot.of_join_left hb.2)⟩
    · exact Shape.WF.join hΔ ((TShape.Compat.def k₁ k₂).1 hcx)
        ((Shape.lift_wf k₁).2 hwf₁.2.2.2.1) ((Shape.lift_wf k₂).2 hwf₂.2.2.2.1)
    · exact Shape.WF.join hΔ ((TShape.Compat.def k₁ k₂).1 hcy)
        ((Shape.lift_wf k₁).2 hwf₁.2.2.2.2) ((Shape.lift_wf k₂).2 hwf₂.2.2.2.2)
  have hwS' : TShape.WF Δ (Shape.T (n := max n₁ n₂ + 1) _) := TShape.WF.T.2 hwS
  refine ⟨_, hwS', ?_, ?_, ?_⟩
  · have hjx' : Interp Δ Γ a σ ρ
        (Shape.T ((x₁.lift (max n₁ n₂)).join (x₂.lift (max n₁ n₂)))) := by
      simpa [TShape.join_T] using hjx
    have hjy' : Interp Δ Γ b σ ρ
        (Shape.T ((y₁.lift (max n₁ n₂)).join (y₂.lift (max n₁ n₂)))) := by
      simpa [TShape.join_T] using hjy
    have hdomj : TShape.Named Δ (d₁.join d₂)
        (Shape.T ((x₁.lift (max n₁ n₂)).join (x₂.lift (max n₁ n₂)))) (a.subst σ) := by
      have hj := TShape.Named.join hΔ hcxl
        (TShape.Named.mono_r hΔ (TShape.Named.lift_subject hΔ hNV₁ k₁) hled₁ hdjty)
        (TShape.Named.mono_r hΔ (TShape.Named.lift_subject hΔ hNV₂ k₂) hled₂ hdjty)
      simpa [TShape.join_T] using hj
    have hjc' : Interp Δ (A :: Γ) B (σ.cons (a.subst σ))
        (ρ.push (Shape.T ((x₁.lift (max n₁ n₂)).join (x₂.lift (max n₁ n₂))))) (c₁.join c₂) := by
      have heq : Shape.T ((x₁.lift (max n₁ n₂)).join (x₂.lift (max n₁ n₂)))
          = (Shape.T x₁).join (Shape.T x₂) := rfl
      rw [heq]; exact hjc
    have hctyj : TShape.Named Δ (c₁.join c₂) (Shape.T ((y₁.lift (max n₁ n₂)).join (y₂.lift (max n₁ n₂)))) none := by
      have hjcc := TShape.le_join hΔ hcode₁'.wf hcode₂'.wf hcc
      have hcj : TShape.HasType Δ (c₁.join c₂) TShape.type :=
        TShape.HasType.join_sort' hΔ rfl (TShape.Named.hasType hcty₁).isType
          (TShape.Named.hasType hcty₂).isType hcc
      have hj := TShape.Named.join hΔ hcyl
        (TShape.Named.mono_r hΔ (TShape.Named.lift_subject hΔ hcty₁ k₁) hjcc.1 hcj)
        (TShape.Named.mono_r hΔ (TShape.Named.lift_subject hΔ hcty₂ k₂) hjcc.2 hcj)
      simpa [TShape.join_T] using hj
    -- the code and the first component keep their names through the join
    have hdcj : TShape.WF Δ (d₁.join d₂) (A.subst σ) :=
      TShape.WF.join hΔ hcd hdc₁ hdc₂
    exact Interp.pair hjx' hjy' hjd hdjty hdomj hdcj hwS hjc' hctyj
      (TShape.LE.refl hwS') hAt hat
  · refine TShape.LE.trans hΔ hlm₁
      ((TShape.LE.def hΔ (Nat.succ_le_succ k₁) (Nat.le_refl _)).2 ?_)
    rw [Shape.lift_self]
    exact ⟨(Shape.le_join hΔ ((Shape.lift_wf k₁).2 hwf₁.2.2.2.1)
        ((Shape.lift_wf k₂).2 hwf₂.2.2.2.1) ((TShape.Compat.def k₁ k₂).1 hcx)).1,
      (Shape.le_join hΔ ((Shape.lift_wf k₁).2 hwf₁.2.2.2.2)
        ((Shape.lift_wf k₂).2 hwf₂.2.2.2.2) ((TShape.Compat.def k₁ k₂).1 hcy)).1,
      (Shape.lift_wf (s := ShapeS.pair ..) (Nat.succ_le_succ k₁)).2 hwf₁ |>.1,
      ((Shape.lift_wf (s := ShapeS.pair ..) (Nat.succ_le_succ k₁)).2 hwf₁).2.2.1,
      ((Shape.lift_wf (s := ShapeS.pair ..) (Nat.succ_le_succ k₁)).2 hwf₁).2.1⟩
  · refine TShape.LE.trans hΔ hlm₂
      ((TShape.LE.def hΔ (Nat.succ_le_succ k₂) (Nat.le_refl _)).2 ?_)
    rw [Shape.lift_self]
    exact ⟨(Shape.le_join hΔ ((Shape.lift_wf k₁).2 hwf₁.2.2.2.1)
        ((Shape.lift_wf k₂).2 hwf₂.2.2.2.1) ((TShape.Compat.def k₁ k₂).1 hcx)).2,
      (Shape.le_join hΔ ((Shape.lift_wf k₁).2 hwf₁.2.2.2.2)
        ((Shape.lift_wf k₂).2 hwf₂.2.2.2.2) ((TShape.Compat.def k₁ k₂).1 hcy)).2,
      ((Shape.lift_wf (s := ShapeS.pair ..) (Nat.succ_le_succ k₂)).2 hwf₂).1,
      ((Shape.lift_wf (s := ShapeS.pair ..) (Nat.succ_le_succ k₂)).2 hwf₂).2.2.1,
      ((Shape.lift_wf (s := ShapeS.pair ..) (Nat.succ_le_succ k₂)).2 hwf₂).2.1⟩

/-- Above a λ-shape there is only a λ-shape. -/
theorem TShape.LE.lam_ub {Δ : List Term} {n} {A : Term} {g : ShapeFun n} {z : TShape}
    (h : TShape.LE Δ (Shape.T (n := n+1) (ShapeS.lam A g)) z) :
    ∃ (k : Nat) (A' : Term) (g' : ShapeFun k),
      z = Shape.T (n := k+1) (ShapeS.lam A' g') := by
  obtain ⟨j, t⟩ := z
  obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ h
  cases j with
  | zero => cases t <;> exact absurd h2 (fun x => x)
  | succ j =>
    cases t with
    | lam A' g' => exact ⟨j, A', g', rfl⟩
    | _ => exact absurd h2 (fun x => x)

/-- And its domain label is the same one. -/
theorem TShape.LE.lam_dom {Δ : List Term} {n k} {A A' : Term}
    {g : ShapeFun n} {g' : ShapeFun k}
    (h : TShape.LE Δ (Shape.T (n := n+1) (ShapeS.lam A g))
      (Shape.T (n := k+1) (ShapeS.lam A' g'))) : TyEq Δ A A' := by
  obtain ⟨M, _, _, h2⟩ := TShape.LE.at_succ h
  exact h2.2.2.2.1

/-- Directedness for `.app`: the `appDF` case of `IsDefEq.dir`. -/
theorem dir_app {Γ : List Term} {F a : Term}
    (ihF : SoundDir Γ F) (iha : SoundDir Γ a) : SoundDir Γ (.app F a) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | app hF₁ ha₁ hev₁ hle₁ hty₁
  cases h₂ with
  | bot =>
    exact ⟨_, hle₁.wf, .app hF₁ ha₁ hev₁ hle₁ hty₁, TShape.LE.refl hle₁.wf, TShape.bot_le' rfl⟩
  | app hF₂ ha₂ hev₂ hle₂ _
  -- one λ-shape above both, and one shape above both arguments
  obtain ⟨z, hwz, hz, hz₁, hz₂⟩ := ihF hΔ W hwρ hF₁ hF₂
  obtain ⟨k, A, g, rfl⟩ := TShape.LE.lam_ub hz₁
  obtain ⟨x, hwx, hx, hx₁, hx₂⟩ := iha hΔ W hwρ ha₁ ha₂
  have hwg := ShapeFun.WF.forget hwz.2.2.1
  have hout : ∀ e ∈ g, TShape.WF Δ e.out.T := fun e he => (hwg.1 e he).2.2.2
  -- both lookups move into the big graph, at its label and its input
  have hmove {n'} {A' : Term} {g' : ShapeFun n'} {x' y' : TShape}
      (hF' : Interp Δ Γ F σ ρ (Shape.T (n := n'+1) (ShapeS.lam A' g')))
      (hz' : TShape.LE Δ (Shape.T (n := n'+1) (ShapeS.lam A' g'))
        (Shape.T (n := k+1) (ShapeS.lam A g)))
      (hx' : TShape.LE Δ x' x)
      (hev : TEvaluates Δ g' A' (a.subst σ) x' y') :
      TEvaluates Δ g A (a.subst σ) x y' :=
    TEvaluates.mono_inp hΔ hx' <| (TEvaluates.trans hΔ
      (TShape.LE.lam_decomp hΔ hz' hwz (TEvaluates.refl hwg)) hev).retype
      (TShape.LE.lam_dom hz')
  have hev₁' := hmove hF₁ hz₁ hx₁ hev₁
  have hev₂' := hmove hF₂ hz₂ hx₂ hev₂
  have hc := TEvaluates.compat hΔ hwg.2 hwx hev₁' hev₂'
  have hwy := TShape.WF.join hΔ hc (TEvaluates.wf hΔ hout hev₁')
    (TEvaluates.wf hΔ hout hev₂')
  refine ⟨_, hwy, .app hz hx (.join hc hev₁' hev₂') (TShape.LE.refl hwy)
      (hty₁.retype (TShape.LE.lam_dom hz₁)),
    hle₁.trans hΔ ?_, hle₂.trans hΔ ?_⟩
  · exact (TShape.le_join hΔ (TEvaluates.wf hΔ hout hev₁')
      (TEvaluates.wf hΔ hout hev₂') hc).1
  · exact (TShape.le_join hΔ (TEvaluates.wf hΔ hout hev₁')
      (TEvaluates.wf hΔ hout hev₂') hc).2

/-- Above a pair shape there is only a pair shape. -/
theorem TShape.LE.pair_ub {Δ : List Term} {n} {A a : Term} {x y : Shape n}
    {z : TShape} (h : TShape.LE Δ (Shape.T (n := n+1) (ShapeS.pair A a x y)) z) :
    ∃ (k : Nat) (A' a' : Term) (x' y' : Shape k),
      z = Shape.T (n := k+1) (ShapeS.pair A' a' x' y') := by
  obtain ⟨j, t⟩ := z
  obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ h
  cases j with | zero => cases t <;> cases h2 | succ j
  cases t with | pair A' a' x' y' => exact ⟨j, A', a', x', y', rfl⟩ | _ => cases h2

/-- And its domain label is the same one. -/
theorem TShape.LE.pair_dom {Δ : List Term} {n k} {A A' a a' : Term} {x y : Shape n}
    {x' y' : Shape k}
    (h : TShape.LE Δ (Shape.T (n := n+1) (ShapeS.pair A a x y))
      (Shape.T (n := k+1) (ShapeS.pair A' a' x' y'))) : TyEq Δ A A' := by
  obtain ⟨M, _, _, h2⟩ := TShape.LE.at_succ h
  exact h2.2.2.2.1

/-- Directedness for `.fst`: the first component of the argument's own
upper bound, which is a pair shape because it is above one. -/
theorem dir_fst {Γ : List Term} {p : Term} (h : SoundDir Γ p) : SoundDir Γ (.fst p) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | fst hp₁ hle₁
  cases h₂ with
  | bot => exact ⟨_, hle₁.wf, .fst hp₁ hle₁, TShape.LE.refl hle₁.wf, TShape.bot_le' rfl⟩
  | fst hp₂ hle₂
  obtain ⟨z, hwz, hz, hz₁, hz₂⟩ := h hΔ W hwρ hp₁ hp₂
  obtain ⟨k, A', a', x', y', rfl⟩ := TShape.LE.pair_ub hz₁
  obtain ⟨_, _, hx₁, _⟩ := TShape.LE.pair_decomp hΔ hz₁
  obtain ⟨_, _, hx₂, _⟩ := TShape.LE.pair_decomp hΔ hz₂
  exact ⟨Shape.T x', TShape.WF.T.2 hwz.2.2.2.1,
    .fst hz (TShape.LE.refl (TShape.WF.T.2 hwz.2.2.2.1)),
    hle₁.trans hΔ hx₁, hle₂.trans hΔ hx₂⟩

/-- Directedness for `.snd`: with the second component unconditional
this is `dir_fst`'s twin — the upper bound's own second component, with
the name moved to it by the order. -/
theorem dir_snd {Γ : List Term} {p : Term} (h : SoundDir Γ p) : SoundDir Γ (.snd p) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | snd hp₁ hlab₁ hle₁ hty₁
  cases h₂ with
  | bot =>
    exact ⟨_, hle₁.wf, .snd hp₁ hlab₁ hle₁ hty₁, TShape.LE.refl hle₁.wf, TShape.bot_le' rfl⟩
  | snd hp₂ hlab₂ hle₂ _
  obtain ⟨z, hwz, hz, hz₁, hz₂⟩ := h hΔ W hwρ hp₁ hp₂
  obtain ⟨k, A', a', x', y', rfl⟩ := TShape.LE.pair_ub hz₁
  obtain ⟨hA₁, ha₁, _, hy₁⟩ := TShape.LE.pair_decomp hΔ hz₁
  obtain ⟨_, _, _, hy₂⟩ := TShape.LE.pair_decomp hΔ hz₂
  have hwy : TShape.WF Δ (Shape.T y') := TShape.WF.T.2 hwz.2.2.2.2
  refine ⟨Shape.T y', hwy, .snd hz ?_ (TShape.LE.refl hwy)
      (hty₁.retype (TShape.LE.pair_dom hz₁)),
    hle₁.trans hΔ hy₁, hle₂.trans hΔ hy₂⟩
  exact hA₁.defeqDF (ha₁.symm.trans hlab₁)

/-- The canonical `id`-shape at a stage, and its well-formedness. -/
theorem Shape.WF.id_of {Γ Δ : List Term} {σ} {A a b : Term} {u : Bool} {r : Bool}
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ)
    (hA : Γ ⊢ A : .sort u) (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : A) :
    Shape.WF (n := 1) Δ (ShapeS.id r (A.subst σ) (a.subst σ) (b.subst σ)) :=
  ⟨⟨u, hA.subst hΔ W⟩, ha.subst hΔ W, hb.subst hΔ W, trivial⟩

/-- Directedness for `.id`: the canonical shape bounds everything. -/
theorem dir_id {Γ : List Term} {A a b : Term} {u r : Bool}
    (hA : Γ ⊢ A : .sort u) (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : A) :
    SoundDir Γ (.id r A a b) := by
  intro Δ σ ρ hΔ W _ m₁ m₂ h₁ h₂
  have hw : TShape.WF Δ (Shape.T (n := 1) (ShapeS.id r (A.subst σ) (a.subst σ) (b.subst σ))) :=
    Shape.WF.id_of hΔ W hA ha hb
  refine ⟨_, hw, .id (TShape.LE.refl hw) ⟨u, hA⟩ ha hb, ?_, ?_⟩
  · cases h₁ with
    | bot => exact TShape.bot_le' rfl
    | id hle => exact hle
  · cases h₂ with
    | bot => exact TShape.bot_le' rfl
    | id hle => exact hle

/-- Directedness for `.succ`: the other repo's `succ_isDirected`. -/
theorem dir_succ {Γ : List Term} {N : Term} (h : SoundDir Γ N) : SoundDir Γ (.succ N) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | succ hv₁ hle₁
  cases h₂ with
  | bot =>
    refine ⟨_, ?_, ?_, hle₁, TShape.bot_le' rfl⟩
    · exact hv₁.wf
    · exact .succ hv₁ (TShape.LE.refl hv₁.wf)
  | succ hv₂ hle₂
  obtain ⟨z, hwz, hz, hz₁, hz₂⟩ := h hΔ W hwρ hv₁ hv₂
  refine ⟨_, ?_, ?_, hle₁.trans hΔ (TShape.LE.succ_of hΔ hz₁),
    hle₂.trans hΔ (TShape.LE.succ_of hΔ hz₂)⟩
  · exact hwz
  · exact .succ hz (TShape.LE.refl hwz)

/-- Above a `succ`-shape there is only a `succ`-shape. -/
theorem TShape.LE.succ_ub {Δ : List Term} {n} {v : Shape n} {z : TShape}
    (h : TShape.LE Δ (Shape.T (n := n+1) (ShapeS.succ v)) z) :
    ∃ (k : Nat) (w : Shape k), z = Shape.T (n := k+1) (ShapeS.succ w) := by
  obtain ⟨j, t⟩ := z
  obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ h
  cases j with | zero => cases t <;> cases h2 | succ j
  cases t with | succ w => exact ⟨j, w, rfl⟩ | _ => cases h2

/-- And the order between two of them is the order between their
predecessors: the converse of `TShape.LE.succ_of`. -/
theorem TShape.LE.succ_decomp {Δ : List Term} (hΔ : ⊢ Δ) {n k} {v : Shape n} {w : Shape k}
    (h : TShape.LE Δ (Shape.T (n := n+1) (ShapeS.succ v))
      (Shape.T (n := k+1) (ShapeS.succ w))) : TShape.LE Δ v.T w.T := by
  obtain ⟨M, hkM, hnM, h2⟩ := TShape.LE.at_succ h
  exact (TShape.LE.def hΔ (Nat.le_of_succ_le_succ hnM) hkM).2 h2

/-- No shape is above both `zero` and a `succ`. -/
theorem TShape.LE.zero_succ_absurd {Δ : List Term} {n} {v : Shape n} {z : TShape}
    (h₁ : TShape.LE Δ TShape.zero z)
    (h₂ : TShape.LE Δ (Shape.T (n := n+1) (ShapeS.succ v)) z) : False := by
  obtain ⟨j, t⟩ := z
  obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ h₁
  obtain ⟨M', _, _, h2'⟩ := TShape.LE.src_succ h₂
  cases j with
  | zero => cases t <;> exact absurd h2 (fun x => x)
  | succ j => cases t <;> first | exact h2.elim | cases h2'

/-- Directedness for `.natCase`.

Three cases have content.  Two `zero` branches join by `a`'s
directedness; a `zero` branch against a `succ` branch is impossible,
since `M` would have two incompatible interpretations (`zero_succ_absurd`)
and its own directedness says it does not; and two `succ` branches carry
two label terms for the body's binder, each `M[σ]`'s predecessor, which
`IsDefEq.succ_inj` identifies — that is the one place this needs a
syntactic inversion, and it is a syntactic theorem, not a consequence of
soundness. -/
theorem dir_natCase {Γ : List Term} {C M a b B : Term} (hΓ : ⊢ Γ)
    (hb : Term.nat :: Γ ⊢ b : B)
    (ihM : SoundDir Γ M) (iha : SoundDir Γ a) (ihb : SoundDir (Term.nat :: Γ) b) :
    SoundDir Γ (.natCase C M a b) := by
  have hΓN : ⊢ (Term.nat :: Γ) := ⟨hΓ, _, .nat⟩
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | natCase_zero hM₁ hz₁ ha₁ hMt =>
    cases h₂ with
    | bot => exact ⟨_, ha₁.wf, .natCase_zero hM₁ hz₁ ha₁ hMt, .refl ha₁.wf, TShape.bot_le' rfl⟩
    | natCase_zero _ _ ha₂ _ =>
      obtain ⟨s, hws, hs, hs₁, hs₂⟩ := iha hΔ W hwρ ha₁ ha₂
      exact ⟨s, hws, .natCase_zero hM₁ hz₁ hs hMt, hs₁, hs₂⟩
    | natCase_succ hM₂ _ _ _ _ =>
      obtain ⟨_, hwz, _, hz₁, hz₂⟩ := ihM hΔ W hwρ hM₁ hM₂
      cases TShape.LE.zero_succ_absurd hz₁ hz₂
  | @natCase_succ _ _ _ _ _ _ _ _ n₁ v₁ t₁ hM₁ hwv₁ heq₁ hbody₁ hMt =>
    cases h₂ with
    | bot => exact ⟨_, hbody₁.wf, .natCase_succ hM₁ hwv₁ heq₁ hbody₁ hMt,
        TShape.LE.refl hbody₁.wf, TShape.bot_le' rfl⟩
    | natCase_zero hM₂ _ _ _ =>
      obtain ⟨_, hwz, _, hz₁, hz₂⟩ := ihM hΔ W hwρ hM₁ hM₂
      cases TShape.LE.zero_succ_absurd hz₂ hz₁
    | @natCase_succ _ _ _ _ _ _ _ _ n₂ v₂ t₂ hM₂ hwv₂ heq₂ hbody₂ _ =>
      -- one `succ`-shape above both, so one slot above both predecessors
      obtain ⟨z, hwz, hz, hz₁, hz₂⟩ := ihM hΔ W hwρ hM₁ hM₂
      obtain ⟨k, w, rfl⟩ := TShape.LE.succ_ub hz₁
      have hv₁ := TShape.LE.succ_decomp hΔ hz₁
      have hv₂ := TShape.LE.succ_decomp hΔ hz₂
      -- the two label terms are one, by `succ` injectivity
      have ht : Δ ⊢ t₂ ≡ t₁ : Term.nat := IsDefEq.succ_inj hΔ (heq₁.symm.trans heq₂).symm
      have Wcons : Ctx.SubstEq Δ (σ.cons t₂) (σ.cons t₁) (Term.nat :: Γ) :=
        .cons W .nat ht
      have Wdiag : Ctx.SubstEq Δ (σ.cons t₁) (σ.cons t₁) (Term.nat :: Γ) :=
        .cons W .nat ht.hasType.2
      have hbody₂' := IsDefEq.stage hΓN hb hΔ Wcons hbody₂
      -- both bodies at that one slot, and joined there
      have hB₁ := Interp.mono_val hΔ (Valuation.LE.push.2
        ⟨Valuation.LE.refl hwρ, hv₁⟩) hbody₁
      have hB₂ := Interp.mono_val hΔ (Valuation.LE.push.2
        ⟨Valuation.LE.refl hwρ, hv₂⟩) hbody₂'
      have hww : TShape.WF Δ w.T := hwz
      obtain ⟨s, hws, hs, hs₁, hs₂⟩ :=
        ihb hΔ Wdiag (Valuation.WF.push hwρ hww) hB₁ hB₂
      exact ⟨s, hws, .natCase_succ hz hww heq₁ hs hMt, hs₁, hs₂⟩

/-- Directedness for `.Y`.

The fixed point's rule refers to the relation it is defining, so the two
derivations are two towers of unfoldings and the argument is an induction
on the first one: its own sub-derivation's induction hypothesis, applied
to the second derivation's sub-derivation, gives a slot above both, and
the two bodies — which sit at those two slots and at *one* stage, since
the label term `(Y A b)[σ]` is the term itself and not a probe — join
there by the body's directedness.

No typing of the tower is used: `Interp.Y` carries none.  The two typing
hypotheses here are only to name the stage `σ.cons ((Y A b)[σ])` as a
substitution into `A :: Γ`, which is what lets the body's `SoundDir` be
applied at all. -/
theorem dir_Y_aux {Δ : List Term} (hΔ : ⊢ Δ) {Γ : List Term} {t : Term} {σ ρ} {m₁ : TShape}
    (h₁ : Interp Δ Γ t σ ρ m₁) :
    ∀ {A b : Term}, t = .Y A b → Valuation.WF Δ Γ ρ → Ctx.SubstEq Δ σ σ Γ →
      Ctx.SubstEq Δ (σ.cons ((A.Y b).subst σ)) (σ.cons ((A.Y b).subst σ)) (A :: Γ) →
      SoundDir Γ A → SoundDir (A :: Γ) b → ∀ {m₂}, Interp Δ Γ t σ ρ m₂ →
        ∃ s, TShape.WF Δ s ∧ Interp Δ Γ t σ ρ s ∧ TShape.LE Δ m₁ s ∧ TShape.LE Δ m₂ s := by
  induction h₁ with
  | bot => exact fun _ _ _ _ _ _ _ h₂ => ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, .refl h₂.wf⟩
  | @Y _ _ _ _ _ _ _ _ hx₁ hwx₁ hA₁ hdty₁ hNVY hcc₁ hbody₁ hAt hYt ihx₁ ihA₁ _ => ?_
  | _ => nofun
  rintro A b ⟨⟩ hwρ WΓ WY ihA ihb m₂ h₂
  cases h₂ with
  | bot =>
    exact ⟨_, hbody₁.wf, .Y hx₁ hwx₁ hA₁ hdty₁ hNVY hcc₁ hbody₁ hAt hYt,
      .refl hbody₁.wf, TShape.bot_le' rfl⟩
  | @Y _ _ _ _ _ _ x₂ d₂ hx₂ hwx₂ hA₂ hdty₂ hNVY₂ hcc₂ hbody₂ _ _
  -- one tower above both, by the first derivation's own induction
  obtain ⟨z, hwz, hz, hz₁, hz₂⟩ := ihx₁ rfl hwρ WΓ WY ihA ihb hx₂
  -- the slot is their *join*: it is below that bound, so it is an
  -- approximant too, and `Named` is closed under the join — which the
  -- clause needs, since `Adm` reads the slot hereditarily
  have hcj := TShape.Compat.of_common_upper hΔ hwz hz₁ hz₂
  have hwj := TShape.WF.join hΔ hcj hwx₁ hwx₂
  have hjx := Interp.mono hΔ (TShape.join_le hΔ hz₁ hz₂) hz
  -- and their *codes* join too, by the annotation's own directedness
  obtain ⟨dc, hwdc, hdc, hdc₁, hdc₂⟩ := ihA hΔ WΓ hwρ hA₁ hA₂
  have hcd := TShape.Compat.of_common_upper hΔ hwdc hdc₁ hdc₂
  have hdcty := TShape.HasType.join_sort' hΔ rfl hdty₁ hdty₂ hcd
  have hdcI := Interp.mono hΔ 
    (TShape.join_le hΔ hdc₁ hdc₂) hdc
  obtain ⟨c₁, c₂⟩ := TShape.le_join hΔ hdty₁.wf.1 hdty₂.wf.1 hcd
  have hjd := TShape.Named.join hΔ hcj (TShape.Named.mono_r hΔ hNVY c₁ hdcty)
    (TShape.Named.mono_r hΔ hNVY₂ c₂ hdcty)
  obtain ⟨j₁, j₂⟩ := TShape.le_join hΔ hwx₁ hwx₂ hcj
  obtain ⟨s, hws, hs, hs₁, hs₂⟩ := ihb hΔ WY (Valuation.WF.push hwρ hwj)
    (Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, j₁⟩) hbody₁)
    (Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, j₂⟩) hbody₂)
  -- the slot and the code keep their names through the join
  have hjc := TShape.WF.join hΔ hcd hcc₁ hcc₂
  exact ⟨s, hws, .Y hjx hwj hdcI hdcty hjd hjc hs hAt hYt, hs₁, hs₂⟩

theorem dir_Y {Γ : List Term} {A b : Term} {u : Bool} (hA : Γ ⊢ A : .sort u)
    (hY : Γ ⊢ .Y A b : A) (ihA : SoundDir Γ A) (ihb : SoundDir (A :: Γ) b) :
    SoundDir Γ (.Y A b) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  exact dir_Y_aux hΔ h₁ rfl hwρ W (.cons W hA (hY.subst hΔ W)) ihA ihb h₂

/-- Directedness for `.refl`: every `refl`-approximant is below the one
`refl`-shape.  At `r = false` there is no `refl` rule and `cases` leaves
only `bot`. -/
theorem dir_refl {Γ : List Term} {a : Term} {r : Bool} : SoundDir Γ (.refl r a) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  have hwz : TShape.WF Δ (Shape.T (n := 1) ShapeS.refl) := TShape.WF.T.2 trivial
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | refl hle₁
  cases h₂ with
  | bot => exact ⟨_, hle₁.wf, .refl hle₁, TShape.LE.refl hle₁.wf, TShape.bot_le' rfl⟩
  | refl hle₂
  exact ⟨_, hwz, .refl (TShape.LE.refl hwz),
    hle₁.trans hΔ (TShape.LE.refl_of hΔ), hle₂.trans hΔ (TShape.LE.refl_of hΔ)⟩

/-- **Directedness for `.tr`** — the case the plan called open, and the
case `SoundJoin` was meant for.  In the event it goes through
`TShape.HasType.join` directly, which is `SoundJoin`'s own ingredient, so
join-closure of a type's *extension* is never needed.

Everything in the `tr` clause is joined slotwise: the witness shape `v`
(which interprets both endpoints, so it is the *join*, not an upper
bound, taken twice), the type `vA`, the motive's value `cb` at the joined
slot, and the transported shape `m'`.  Three of the clause's premises are
typings, and each is a subject join at one type: `v` at `vA₁ ⊔ vA₂`, `cb`
at `type`, `m'` at `cb₁ ⊔ cb₂` — `TShape.HasType.join`, which is why this
case waited for it.  The proof premise is moved by `H`'s own
directedness: a shape above two `refl`s is a `refl`, above both
witnesses. -/
theorem dir_tr {Γ : List Term} {r : Bool} {A a b C X H : Term} {u : Bool}
    (hA : Γ ⊢ A : .sort u) (hb : Γ ⊢ b : A)
    (ihA : SoundDir Γ A) (iha : SoundDir Γ a) (ihb : SoundDir Γ b)
    (ihC : SoundDir (A :: Γ) C) (ihX : SoundDir Γ X) :
    SoundDir Γ (.tr r A a b C X H) := by
  intro Δ σ ρ hΔ W hwρ m₁ m₂ h₁ h₂
  cases h₁ with
  | bot => exact ⟨_, h₂.wf, h₂, TShape.bot_le' rfl, TShape.LE.refl h₂.wf⟩
  | tr hle₁ hX₁ ha₁ hb₁ hA₁ hwv₁ hNVb₁ hvc₁ hC₁ hcb₁ hNV2b₁ hcbc₁ hH₁ heq₁ hAt hat hbt
  cases h₂ with
  | bot =>
    exact ⟨_, hX₁.wf, .tr (TShape.LE.refl hX₁.wf) hX₁ ha₁ hb₁ hA₁ hwv₁ hNVb₁
      hvc₁ hC₁ hcb₁ hNV2b₁ hcbc₁ hH₁ heq₁ hAt hat hbt, hle₁, TShape.bot_le' rfl⟩
  | tr hle₂ hX₂ ha₂ hb₂ hA₂ hwv₂ hNVb₂ hvc₂ hC₂ hcb₂ hNV2b₂ hcbc₂ hH₂ _ _ _ _
  -- the witness: the join interprets both endpoints
  have ⟨hcv, hav⟩ := iha.join hΔ W hwρ ha₁ ha₂
  have ⟨_, hbv⟩ := ihb.join hΔ W hwρ hb₁ hb₂
  have hwv := TShape.WF.join hΔ hcv hwv₁ hwv₂
  have hvle := TShape.le_join hΔ hwv₁ hwv₂ hcv
  -- its type
  have ⟨hcA, hAv⟩ := ihA.join hΔ W hwρ hA₁ hA₂
  have hvAty := TShape.HasType.join hΔ hcA (TShape.Named.of_isType hNVb₁.hasType.isType)
    (TShape.Named.of_isType hNVb₂.hasType.isType)
  have hvAle := TShape.le_join hΔ hNVb₁.hasType.isType.wf.1 hNVb₂.hasType.isType.wf.1 hcA
  have hty := TShape.Named.join hΔ hcv
    (TShape.Named.mono_r hΔ hNVb₁ hvAle.1 hvAty) (TShape.Named.mono_r hΔ hNVb₂ hvAle.2 hvAty)
  -- the motive, at the joined slot
  have WA : Ctx.SubstEq Δ (σ.cons (b.subst σ)) (σ.cons (b.subst σ)) (A :: Γ) :=
    .cons W hA (hb.subst hΔ W)
  have hC₁' := Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hvle.1⟩) hC₁
  have hC₂' := Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hvle.2⟩) hC₂
  have ⟨hccb, hcbv⟩ :=
    ihC.join hΔ WA (Valuation.WF.push hwρ hwv) hC₁' hC₂'
  have hcbty := TShape.HasType.join hΔ hccb (TShape.Named.of_isType hcb₁)
    (TShape.Named.of_isType hcb₂)
  have hcble := TShape.le_join hΔ hcb₁.wf.1 hcb₂.wf.1 hccb
  -- the transported shape
  have ⟨hcm, hXv⟩ := ihX.join hΔ W hwρ hX₁ hX₂
  have hm'ty := TShape.Named.join hΔ hcm
    (TShape.Named.mono_r hΔ hNV2b₁ hcble.1 hcbty) (TShape.Named.mono_r hΔ hNV2b₂ hcble.2 hcbty)
  have hm'le := TShape.le_join hΔ hNV2b₁.hasType.wf.1 hNV2b₂.hasType.wf.1 hcm
  -- and the proof premise, by `H`'s own directedness
  have hwm' := TShape.WF.join hΔ hcm hNV2b₁.hasType.wf.1 hNV2b₂.hasType.wf.1
  -- the slot and its type keep their names through the joins
  have hvcj := TShape.WF.join hΔ hcA hvc₁ hvc₂
  have hcbcj := TShape.WF.join hΔ hccb hcbc₁ hcbc₂
  exact ⟨_, hwm', .tr (TShape.LE.refl hwm')
      hXv hav hbv hAv hwv hty hvcj hcbv hcbty hm'ty hcbcj hH₁ heq₁ hAt hat hbt,
    hle₁.trans hΔ hm'le.1, hle₂.trans hΔ hm'le.2⟩

/-- **Directedness**, its own induction on typing.

Every non-congruence rule is an identity on the two conclusions: the
structural rules permute them, `defeqDF` changes only the type, and the
computation rules carry typings of both sides (the other repo's
`of_typings` observation), so their conclusions are their premises'.  Only
one case per term former has content, and each is the corresponding
`isDirected` lemma of the other repo. -/
theorem IsDefEq.dir {Γ : List Term} {t t' A : Term}
    (hΓ : ⊢ Γ) (H : Γ ⊢ t ≡ t' : A) : SoundDir Γ t ∧ SoundDir Γ t' := by
  induction H with
  -- structural: pure bookkeeping
  | symm _ ih => exact ⟨(ih hΓ).2, (ih hΓ).1⟩
  | trans _ _ ih₁ ih₂ => exact ⟨(ih₁ hΓ).1, (ih₂ hΓ).2⟩
  | trans' _ _ ih₁ ih₂ => exact ⟨(ih₁ hΓ).1, (ih₂ hΓ).2⟩
  | defeqDF _ _ _ ih => exact ih hΓ
  -- atoms: the canonical shape bounds everything
  | sort => exact and_self_iff.2 <| dir_atom Interp.le_sort (fun h => .sort h) trivial
  | unit => exact and_self_iff.2 <| dir_atom Interp.le_unit (fun h => .unit h) trivial
  | nat => exact and_self_iff.2 <| dir_atom Interp.le_nat (fun h => .nat h) trivial
  | zero => exact and_self_iff.2 <| dir_atom Interp.le_zero (fun h => .zero h) trivial
  | star => exact and_self_iff.2 <| dir_of_bot fun .bot => rfl
  -- Π: the other repo's `pi_isDirected`, with `IsDefEq.stage` for the
  -- cross pairs of the appended graph
  | forallEDF hAA' hB hB' ihA ihB ihB' =>
    exact ⟨
      sound_forallE_dir hΓ hAA'.hasType.1 hB.hasType.1 (ihA hΓ).1 (ihB ⟨hΓ, _, hAA'.hasType.1⟩).1,
      sound_forallE_dir hΓ hAA'.hasType.2 hB'.hasType.2 (ihA hΓ).2 (ihB' ⟨hΓ, _, hAA'.hasType.2⟩).2⟩
  -- `bvar` reads the slot's well-formedness off `Valuation.WF`; the rest
  -- are one per term former, each the other repo's `*_isDirected`
  | bvar h => exact and_self_iff.2 (dir_bvar h)
  -- the λ-shape's domain label is what makes this one standalone (§5.5b)
  | appDF _ _ _ _ _ _ _ ihf iha _ =>
    exact ⟨dir_app (ihf hΓ).1 (iha hΓ).1, dir_app (ihf hΓ).2 (iha hΓ).2⟩
  -- λ: Π's argument, with the body in place of the codomain
  | lamDF hAA' hB hbody hbody' _ ihA _ ihb ihb' _ =>
    exact ⟨
      sound_lam_dir hΓ hAA'.hasType.1 hbody.hasType.1 (ihA hΓ).1 (ihb ⟨hΓ, _, hAA'.hasType.1⟩).1,
      sound_lam_dir hΓ hAA'.hasType.2 hbody'.hasType.2 (ihA hΓ).2 (ihb' ⟨hΓ, _, hAA'.hasType.2⟩).2⟩
  | sigmaDF hAA' hB hB' ihA ihB ihB' =>
    exact ⟨
      sound_sigma_dir hΓ hAA'.hasType.1 hB.hasType.1 (ihA hΓ).1 (ihB ⟨hΓ, _, hAA'.hasType.1⟩).1,
      sound_sigma_dir hΓ hAA'.hasType.2 hB'.hasType.2 (ihA hΓ).2 (ihB' ⟨hΓ, _, hAA'.hasType.2⟩).2⟩
  | pairDF hAA' hB hB' _ _ _ _ ihA ihB ihB' iha ihb _ _ =>
    exact ⟨
      dir_pair (ihA hΓ).1 (ihB ⟨hΓ, _, hAA'.hasType.1⟩).1 (iha hΓ).1 (ihb hΓ).1,
      dir_pair (ihA hΓ).2 (ihB' ⟨hΓ, _, hAA'.hasType.2⟩).2 (iha hΓ).2 (ihb hΓ).2⟩
  | fstDF _ _ _ _ _ ih => exact ⟨dir_fst (ih hΓ).1, dir_fst (ih hΓ).2⟩
  | sndDF _ _ _ _ _ _ ih _ => exact ⟨dir_snd (ih hΓ).1, dir_snd (ih hΓ).2⟩
  | succDF _ ih => exact ⟨dir_succ (ih hΓ).1, dir_succ (ih hΓ).2⟩
  | natCaseDF _ _ _ hbb' _ _ ihM iha ihb _ =>
    exact ⟨
      dir_natCase hΓ hbb'.hasType.1 (ihM hΓ).1 (iha hΓ).1 (ihb ⟨hΓ, _, .nat⟩).1,
      dir_natCase hΓ hbb'.hasType.2 (ihM hΓ).2 (iha hΓ).2 (ihb ⟨hΓ, _, .nat⟩).2⟩
  | idDF hAA' haa' hbb' ihA iha ihb =>
    exact ⟨dir_id hAA'.hasType.1 haa'.hasType.1 hbb'.hasType.1,
      dir_id hAA'.hasType.2 (hAA'.defeqDF haa'.hasType.2) (hAA'.defeqDF hbb'.hasType.2)⟩
  | reflDF => exact ⟨dir_refl, dir_refl⟩
  -- the case `SoundJoin` was meant for: two transports are typed at two
  -- approximants of the motive, and the witness above both has to be
  -- typed at the motive above both (`dir_tr does this with the subject
  -- join).  Every other case is an upper bound
  -- with no typing to preserve, which is why they run under
  -- `Valuation.WF` with no admissibility in sight
  | trDF hAA' haa' hbb' hC hC' hxx' hhh' _ _ ihA iha ihb ihC ihC' ihx ihh =>
    constructor
    · exact dir_tr hAA'.hasType.1 hbb'.hasType.1 (ihA hΓ).1 (iha hΓ).1 (ihb hΓ).1
        (ihC ⟨hΓ, _, hAA'.hasType.1⟩).1 (ihx hΓ).1
    · exact dir_tr hAA'.hasType.2 (hAA'.defeqDF hbb'.hasType.2) (ihA hΓ).2 (iha hΓ).2 (ihb hΓ).2
        (ihC' ⟨hΓ, _, hAA'.hasType.2⟩).2 (ihx hΓ).2
  -- the fixed point: an induction on the tower of unfoldings, inside
  | YDF h1 h2 h3 ihA ihb ihb' =>
    have hY := IsDefEq.YDF h1 h2 h3
    exact ⟨dir_Y h1.hasType.1 hY.hasType.1 (ihA hΓ).1 (ihb ⟨hΓ, _, h1.hasType.1⟩).1,
      dir_Y h1.hasType.2 (h1.defeqDF hY.hasType.2) (ihA hΓ).2
        (ihb' ⟨hΓ, _, h1.hasType.2⟩).2⟩
  -- the computation rules are padded with typings of both sides, so each
  -- of these is its two premises' conclusions
  | beta _ _ _ _ _ _ _ _ ih₃ ih₄ => exact ⟨(ih₃ hΓ).1, (ih₄ hΓ).1⟩
  | eta _ _ ih₁ ih₂ => exact ⟨(ih₂ hΓ).1, (ih₁ hΓ).1⟩
  | unit_eta _ ih => exact ⟨dir_of_bot fun .bot => rfl, (ih hΓ).1⟩
  | pair_fst _ _ _ _ _ _ _ ih₃ _ ih₅ => exact ⟨(ih₅ hΓ).1, (ih₃ hΓ).1⟩
  | pair_snd _ _ _ _ _ _ _ _ ih₄ ih₅ => exact ⟨(ih₅ hΓ).1, (ih₄ hΓ).1⟩
  | fst_snd _ _ ih₁ ih₂ => exact ⟨(ih₂ hΓ).1, (ih₁ hΓ).1⟩
  | natCase_zero _ _ _ _ _ ih₂ _ ih₄ => exact ⟨(ih₄ hΓ).1, (ih₂ hΓ).1⟩
  | natCase_succ _ _ _ _ _ _ _ _ _ _ ih₅ ih₆ => exact ⟨(ih₅ hΓ).1, (ih₆ hΓ).1⟩
  | Y_unfold _ _ _ _ _ _ ih₃ ih₄ => exact ⟨(ih₃ hΓ).1, (ih₄ hΓ).1⟩
  | tr_refl _ _ _ _ _ _ _ _ ih₄ ih₅ => exact ⟨(ih₅ hΓ).1, (ih₄ hΓ).1⟩
  | proofIrrel _ _ _ _ ih₂ ih₃ => exact ⟨(ih₂ hΓ).1, (ih₃ hΓ).1⟩

/-- **Every in-range slot of a typed substitution is directed.**  The
stage types the slot, so `IsDefEq.dir` applies.  Out of range there is
nothing to say and nothing asks, which is why none of the substitution
lemmas carries a directedness premise: the stage's typing is already on
all of them. -/
theorem Ctx.SubstEq.dir {Γ Γ' : List Term} {θ : Subst} (hΓ' : ⊢ Γ')
    (Wθ : Ctx.SubstEq Γ' θ θ Γ) {i A} (hlk : Lookup Γ i A) : SoundDir Γ' (θ i) :=
  (IsDefEq.dir hΓ' (Wθ.lookup hlk)).1

theorem Valuation.Approx.join {Δ Γ Γ' : List Term} {θ σ ρ ρ₁ ρ₂} (hΔ : ⊢ Δ)
    (W : Ctx.SubstEq Δ σ σ Γ') (hwρ : Valuation.WF Δ Γ' ρ) (hΓ' : ⊢ Γ')
    (Wθ : Ctx.SubstEq Γ' θ θ Γ)
    (h₁ : Valuation.Approx Δ Γ' Γ θ σ ρ ρ₁) (h₂ : Valuation.Approx Δ Γ' Γ θ σ ρ ρ₂) :
    Valuation.Approx Δ Γ' Γ θ σ ρ (ρ₁.join ρ₂) ∧
      Valuation.LE Δ Γ ρ₁ (ρ₁.join ρ₂) ∧ Valuation.LE Δ Γ ρ₂ (ρ₁.join ρ₂) :=
  have key : ∀ {{i A}}, Lookup Γ i A → Interp Δ Γ' (θ i) σ ρ ((ρ₁.join ρ₂) i) ∧
      TShape.LE Δ (ρ₁ i) ((ρ₁.join ρ₂) i) ∧ TShape.LE Δ (ρ₂ i) ((ρ₁.join ρ₂) i) := by
    intro i A hlk
    obtain ⟨hc, hj⟩ := (Wθ.dir hΓ' hlk).join hΔ W hwρ (h₁ hlk) (h₂ hlk)
    obtain ⟨hl₁, hl₂⟩ := TShape.le_join hΔ (h₁ hlk).wf (h₂ hlk).wf hc
    exact ⟨hj, hl₁, hl₂⟩
  ⟨fun {_ _} hlk => (key hlk).1, fun {_ _} hlk => (key hlk).2.1,
    fun {_ _} hlk => (key hlk).2.2⟩

/-- And a list of them folds to one. -/
theorem Valuation.Approx.foldr {Δ Γ Γ' : List Term} {θ σ ρ} (hΔ : ⊢ Δ)
    (W : Ctx.SubstEq Δ σ σ Γ') (hwρ : Valuation.WF Δ Γ' ρ) (hΓ' : ⊢ Γ')
    (Wθ : Ctx.SubstEq Γ' θ θ Γ) :
    ∀ {l : List Valuation}, (∀ ρ' ∈ l, Valuation.Approx Δ Γ' Γ θ σ ρ ρ') →
      Valuation.Approx Δ Γ' Γ θ σ ρ (l.foldr Valuation.join Valuation.nil) ∧
        ∀ ρ' ∈ l, Valuation.LE Δ Γ ρ' (l.foldr Valuation.join Valuation.nil)
  | [], _ => ⟨Valuation.Approx.nil, by simp⟩
  | ρ₀ :: l, h => by
    obtain ⟨hrest, hle⟩ := Valuation.Approx.foldr (l := l) hΔ W hwρ hΓ' Wθ
      (fun ρ' hρ' => h ρ' (by simp [hρ']))
    obtain ⟨hj, hl₁, hl₂⟩ :=
      Valuation.Approx.join hΔ W hwρ hΓ' Wθ (h ρ₀ (by simp)) hrest
    refine ⟨hj, fun ρ' hρ' => ?_⟩
    match List.mem_cons.1 hρ' with
    | .inl rfl => exact hl₁
    | .inr hm => exact fun {_ _} hlk => TShape.LE.trans hΔ (hle ρ' hm hlk) (hl₂ hlk)

/-- Directedness over a list: finitely many approximants of one term have
one above them all.  `SoundDir.join` iterated, with `⊥` at the empty
list — what η needs, since the expansion's graph is finite.

Takes the term's typing rather than its directedness, so that callers
outside this file never have to name `SoundDir`. -/
theorem Interp.list_ub {Δ Γ : List Term} {t T σ ρ} (hΓ : ⊢ Γ) (ht : Γ ⊢ t : T)
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hρ : Valuation.WF Δ Γ ρ)
    {α : Type} {ms : α → TShape} : ∀ (l : List α), (∀ a ∈ l, Interp Δ Γ t σ ρ (ms a)) →
      ∃ s, TShape.WF Δ s ∧ Interp Δ Γ t σ ρ s ∧ ∀ a ∈ l, TShape.LE Δ (ms a) s
  | [], _ => ⟨TShape.bot, trivial, .bot, fun _ h => absurd h (by simp)⟩
  | a :: l, hl => by
    obtain ⟨s, hws, hs, hle⟩ :=
      Interp.list_ub hΓ ht hΔ W hρ l (fun b hb => hl b (.tail _ hb))
    have ha := hl a (.head _)
    obtain ⟨hc, hj⟩ := (IsDefEq.dir hΓ ht).1.join hΔ W hρ ha hs
    obtain ⟨hla, hls⟩ := TShape.le_join hΔ ha.wf hws hc
    refine ⟨_, TShape.WF.join hΔ hc ha.wf hws, hj, fun b hb => ?_⟩
    cases hb with
    | head => exact hla
    | tail _ hb => exact TShape.LE.trans hΔ (hle b hb) hls
