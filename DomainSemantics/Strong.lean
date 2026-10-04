import DomainSemantics.Presheaf

/-! # Strong soundness

`SoundTy Γ t A` and `SoundEq Γ t t'` are flat: neither lets you recover
anything about the subterms of `t`.  Master's answer, ported here, is a
second judgment that does — a **syntax-directed** typing relation
recording each subterm's type, wrapped around the two semantic ones:

* `StrongSoundCore Γ t A` — one clause per term former, each carrying
  `StrongSound` (or `SoundTy`) for the subterms at the types the
  corresponding `IsDefEq` rule gives them;
* `StrongSound Γ t A` — `SoundTy Γ t A` together with such a core at some
  `A'` that is `SoundEq` to `A`;
* `StrongSoundEq Γ t t' A` — `SoundEq Γ t t'` with both sides
  `StrongSound` at `A`.

The point is `StrongSound.uniq`: two strong typings of one term have
`SoundEq` types.  In this design that is not weaker than the syntactic
equation — `Inversion.lean` reads syntactic definitional equalities back
out of `SoundEq` by probing with a type's own label-only approximant — so
the inversion principles come with it rather than being extra work.

Nothing here changes the soundness proof: `IsDefEq.sound`'s cases already
produce exactly the `SoundTy`/`SoundEq` facts the core's clauses ask for.
This file only wraps them. -/

namespace DomainSemantics

mutual
/-- `StrongSound Γ t A`: `t` is semantically typed at `A`, *and* there is a
structural derivation at some `A'` semantically equal to `A`.  The
intermediate `A'` lets each clause use whatever Π/Σ/sort form is natural
while still concluding at the type the judgment wants. -/
inductive StrongSound : List Term → Term → Term → Prop where
  | mk : SoundTy Γ t A →
    StrongSoundCore Γ t A' → SoundEq Γ A' A → (∃ u, Γ ⊢ A' ≡ A : .sort u) →
    StrongSound Γ t A

/-- The structural typing relation, one constructor per term former.
Mutually recursive with `StrongSound`, which is what each subderivation
produces. -/
inductive StrongSoundCore : List Term → Term → Term → Prop where
  | bvar : Lookup Γ i A → StrongSoundCore Γ (.bvar i) A
  | sort : StrongSoundCore Γ (.sort r) .type
  | unit : StrongSoundCore Γ (.unit r) (.sort r)
  | star : StrongSoundCore Γ (.star r) (.unit r)
  | lam : SoundTy Γ A (.sort u) →
    StrongSound (A::Γ) e B → StrongSoundCore Γ (.lam A e) (.forallE A B)
  | app : SoundTy Γ A (.sort u) →
    StrongSound Γ f (.forallE A B) → StrongSound Γ a A →
    StrongSoundCore Γ (.app f a) (B.inst a)
  | forallE : StrongSound Γ A (.sort u) → StrongSound (A::Γ) B (.sort v) →
    StrongSoundCore Γ (.forallE A B) (.sort v)
  | sigma : StrongSound Γ A (.sort u) → StrongSound (A::Γ) B (.sort v) →
    StrongSoundCore Γ (.sigma A B) .type
  | pair : SoundTy Γ A (.sort u) → SoundTy (A::Γ) B (.sort v) →
    StrongSound Γ a A → StrongSound Γ b (B.inst a) →
    StrongSoundCore Γ (.pair A B a b) (.sigma A B)
  | fst : SoundTy Γ A (.sort u) → SoundTy (A::Γ) B (.sort v) →
    StrongSound Γ p (.sigma A B) → StrongSoundCore Γ (.fst p) A
  | snd : SoundTy Γ A (.sort u) → SoundTy (A::Γ) B (.sort v) →
    StrongSound Γ p (.sigma A B) →
    StrongSoundCore Γ (.snd p) (B.inst (.fst p))
  | nat : StrongSoundCore Γ .nat .type
  | zero : StrongSoundCore Γ .zero .nat
  | succ : StrongSound Γ n .nat → StrongSoundCore Γ (.succ n) .nat
  | natCase : StrongSound (.nat::Γ) C (.sort v) →
    StrongSound Γ M .nat →
    StrongSound Γ a (C.inst .zero) →
    StrongSound (.nat::Γ) b ((C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0))) →
    StrongSoundCore Γ (.natCase C M a b) (C.inst M)
  | Y : SoundTy Γ A (.sort u) → StrongSound (A::Γ) b A.lift →
    StrongSoundCore Γ (.Y A b) A
  | id : StrongSound Γ A (.sort u) →
    StrongSound Γ a A → StrongSound Γ b A →
    StrongSoundCore Γ (.id r A a b) (.sort r)
  | refl : SoundTy Γ A (.sort u) → StrongSound Γ a A →
    StrongSoundCore Γ (.refl r a) (.id r A a a)
  | tr : SoundTy Γ A (.sort u) → SoundTy Γ a A → SoundTy Γ b A →
    StrongSound (A::Γ) C (.sort v) →
    StrongSound Γ x (C.inst a) → StrongSound Γ h (.id r A a b) →
    StrongSoundCore Γ (.tr r A a b C x h) (C.inst b)
end

/-- Strong soundness for an equality judgment: both sides are individually
`StrongSound` at `A`, and they are semantically equal. -/
structure StrongSoundEq (Γ : List Term) (t t' A : Term) : Prop where
  sound : SoundEq Γ t t'
  left : StrongSound Γ t A
  right : StrongSound Γ t' A

/-! ## The algebra of the three predicates

All of it is bookkeeping; `SoundEq`'s own `rfl`/`symm`/`trans` are in
`Presheaf.lean`. -/

theorem StrongSound.sound : StrongSound Γ t A → SoundTy Γ t A
  | ⟨h, _, _, _⟩ => h

/-- The judgment's type is a type, syntactically: the link to the core's
type is a definitional equality, so its right-hand typing is the answer. -/
theorem StrongSound.isType : StrongSound Γ t A → ∃ u, Γ ⊢ A : .sort u
  | ⟨_, _, _, ⟨u, h⟩⟩ => ⟨u, h.hasType.2⟩

theorem StrongSoundEq.symm : StrongSoundEq Γ t t' A → StrongSoundEq Γ t' t A
  | ⟨h1, h2, h3⟩ => ⟨h1.symm, h3, h2⟩

theorem StrongSoundEq.rfl' (H : StrongSound Γ t A) : StrongSoundEq Γ t t A :=
  ⟨SoundEq.refl, H, H⟩

theorem StrongSoundEq.trans :
    StrongSoundEq Γ t t' A → StrongSoundEq Γ t' t'' A → StrongSoundEq Γ t t'' A
  | ⟨a1, a2, _⟩, ⟨b1, _, b3⟩ => ⟨a1.trans b1, a2, b3⟩

/-- The type of a `SoundTy` moves along a semantic equality of types. -/
theorem SoundTy.defeq_r {u} (H0 : Γ ⊢ A ≡ B : .sort u) (H1 : SoundEq Γ A B)
    (H : SoundTy Γ t A) : SoundTy Γ t B := by
  refine ⟨H0.defeqDF H.typed, ?_⟩
  intro Δ Γ₀ σ ρ hΔ W hAdm m h
  have ⟨a, ha, hty⟩ := H.approx hΔ W hAdm h
  exact ⟨a, (H1 hΔ W hAdm).1 ha, hty⟩

theorem StrongSound.defeq_r {u} (H1 : SoundEq Γ A B) (H1' : Γ ⊢ A ≡ B : .sort u) :
    StrongSound Γ t A → StrongSound Γ t B
  | ⟨sound, core, eq, ⟨_, eq'⟩⟩ =>
    ⟨sound.defeq_r H1' H1, core, eq.trans H1, ⟨_, eq'.trans' H1'⟩⟩

/-- The way each soundness case will build its `StrongSoundEq`: the two
structural derivations, and the pair of semantic facts `IsDefEq.sound`
already produces. -/
theorem StrongSoundEq.mk' {u₁ u₂}
    (hs : Γ ⊢ t ≡ t' : A)
    (h2 : StrongSoundCore Γ t A₁) (h2' : SoundEq Γ A₁ A) (h2'' : Γ ⊢ A₁ ≡ A : .sort u₁)
    (h3 : StrongSoundCore Γ t' A₂) (h3' : SoundEq Γ A₂ A) (h3'' : Γ ⊢ A₂ ≡ A : .sort u₂)
    (h4 : SoundEq Γ t t' ∧ SoundTy Γ t A) :
    StrongSoundEq Γ t t' A :=
  ⟨h4.1, ⟨h4.2, h2, h2', ⟨_, h2''⟩⟩, ⟨SoundTy.of_eq hs h4.1 h4.2, h3, h3', ⟨_, h3''⟩⟩⟩

/-- **Semantic uniqueness of types**, given it for the structural
relation.  Master's `uniq_of_core`. -/
theorem StrongSound.uniq_of_core
    (H : ∀ {A B}, StrongSoundCore Γ t A → StrongSoundCore Γ t B → SoundEq Γ A B) :
    StrongSound Γ t A → StrongSound Γ t B → SoundEq Γ A B
  | ⟨_, a2, a3, _⟩, ⟨_, b2, b3, _⟩ => a3.symm.trans ((H a2 b2).trans b3)

/-- And syntactically.  `H` is handed the two core types' own typings,
which the `StrongSound`s carry: the clauses whose two cores agree on the
nose still have to produce a *reflexivity*, and that needs a typing. -/
theorem StrongSound.uniq_of_core'
    (H : ∀ {A B}, (∃ u, Γ ⊢ A : .sort u) → (∃ u, Γ ⊢ B : .sort u) →
      StrongSoundCore Γ t A → StrongSoundCore Γ t B →
      SoundEq Γ A B ∧ ∃ u, Γ ⊢ A ≡ B : .sort u) :
    StrongSound Γ t A → StrongSound Γ t B → SoundEq Γ A B ∧ ∃ u, Γ ⊢ A ≡ B : .sort u
  | ⟨_, a2, a3, ⟨_, a4⟩⟩, ⟨_, b2, b3, ⟨_, b4⟩⟩ =>
    have ⟨hs, _, h⟩ := H ⟨_, a4.hasType.1⟩ ⟨_, b4.hasType.1⟩ a2 b2
    ⟨a3.symm.trans (hs.trans b3), _, a4.symm.trans' (h.trans' b4)⟩

/-! ## Uniqueness of types

`StrongSound` assumptions give both equalities at once, and each half needs
the other's induction hypothesis: the syntactic half at `app`/`fst`/`snd`
inverts a Π/Σ, which the `SoundEq`-level inversions do given the *semantic*
equality of the two Π/Σ types; the semantic half at `lam` builds a Π
congruence, which (the labels being in the shapes) needs the *syntactic*
equality of the codomains.  So one induction, two conclusions.

Nothing here goes through `IsDefEq.sound`.  Regularity — the typings the
label probes are built from — is purely syntactic (`Regular.lean`), and the
inversions take `SoundEq` directly.  That is what lets `uniq` be used
*inside* the soundness induction, whose hypotheses are `StrongSound`; the
plain-typing inversions of `Inversion.lean` are corollaries at the end.

Where the two cores agree on the type on the nose — most clauses — the
answer is reflexivity: `SoundEq.refl`, and the type's own typing, which
`uniq_of_core'` hands in. -/

theorem StrongSound.uniq : ∀ {t : Term} {Γ : List Term} {A B : Term}, ⊢ Γ →
    StrongSound Γ t A → StrongSound Γ t B → SoundEq Γ A B ∧ ∃ u, Γ ⊢ A ≡ B : .sort u := by
  intro t
  induction t with
  | bvar i =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} hTA _ H1 H2 => ?_
    cases H1 with | bvar a1 => cases H2 with | bvar b1 =>
    cases a1.uniq b1
    exact ⟨SoundEq.refl, hTA⟩
  | sort r =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} hTA _ H1 H2 => ?_
    cases H1; cases H2; exact ⟨SoundEq.refl, hTA⟩
  | unit r =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} hTA _ H1 H2 => ?_
    cases H1; cases H2; exact ⟨SoundEq.refl, hTA⟩
  | star r =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} hTA _ H1 H2 => ?_
    cases H1; cases H2; exact ⟨SoundEq.refl, hTA⟩
  | nat =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} hTA _ H1 H2 => ?_
    cases H1; cases H2; exact ⟨SoundEq.refl, hTA⟩
  | zero =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} hTA _ H1 H2 => ?_
    cases H1; cases H2; exact ⟨SoundEq.refl, hTA⟩
  | succ n _ =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} hTA _ H1 H2 => ?_
    cases H1; cases H2; exact ⟨SoundEq.refl, hTA⟩
  | sigma A₀ B₀ _ _ =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} hTA _ H1 H2 => ?_
    cases H1; cases H2; exact ⟨SoundEq.refl, hTA⟩
  | pair A₀ B₀ a₀ b₀ _ _ _ _ =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} hTA _ H1 H2 => ?_
    cases H1; cases H2; exact ⟨SoundEq.refl, hTA⟩
  | natCase C M a b _ _ _ _ =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} hTA _ H1 H2 => ?_
    cases H1; cases H2; exact ⟨SoundEq.refl, hTA⟩
  | Y A₀ b₀ _ _ =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} hTA _ H1 H2 => ?_
    cases H1; cases H2; exact ⟨SoundEq.refl, hTA⟩
  | id r A₀ a₀ b₀ _ _ _ =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} hTA _ H1 H2 => ?_
    cases H1; cases H2; exact ⟨SoundEq.refl, hTA⟩
  -- every component is in the term, so the two cores' types agree
  | tr r A₀ a₀ b₀ C x h _ _ _ _ _ _ =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} hTA _ H1 H2 => ?_
    cases H1; cases H2; exact ⟨SoundEq.refl, hTA⟩
  | forallE A₀ B₀ _ ihB =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} hTA _ H1 H2 => ?_
    cases H1 with | forallE a1 a2 => cases H2 with | forallE b1 b2 =>
    have hΓA : ⊢ (A₀ :: Γ) := ⟨hΓ, _, a1.sound.typed⟩
    have ⟨hs, _⟩ := ihB hΓA a2 b2
    cases SoundEq.sort_inv hΓA hs
    exact ⟨SoundEq.refl, hTA⟩
  | lam A₀ e _ ihe =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} _ _ H1 H2 => ?_
    cases H1 with | lam a1 a2 => cases H2 with | lam b1 b2 =>
    have ⟨hs, _, h⟩ := ihe (show ⊢ (A₀ :: Γ) from ⟨hΓ, _, a1.typed⟩) a2 b2
    exact ⟨sound_forallE_eq a1.typed h h SoundEq.refl a1 hs hs, _, .forallEDF a1.typed h h⟩
  | app f a ihf _ =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} _ _ H1 H2 => ?_
    cases H1 with | app a1 a2 a3 => cases H2 with | app b1 b2 b3 =>
    have ⟨hs, _, hpi⟩ := ihf hΓ a2 b2
    have ⟨_, hB₀⟩ := hpi.forallE_cod
    have ⟨_, hB₁⟩ := hpi.symm.forallE_cod
    have ⟨_, _, _, hcod⟩ := SoundEq.forallE_inv hΓ a1.typed hB₀ hs
    -- the semantic half: `Interp.inst` splits `B[a]` at a slot, `SoundTy a A`
    -- types the slot, and `SoundEq.forallE_cod` moves it to the other codomain
    have hΓA₀ : ⊢ (_ :: Γ) := ⟨hΓ, _, a1.typed⟩
    have hΓA₁ : ⊢ (_ :: Γ) := ⟨hΓ, _, b1.typed⟩
    exact ⟨SoundEq.inst_cod (IsDefEq.pinned hΓA₀ hB₀) (IsDefEq.pinned hΓA₁ hB₁)
        hΓ a1.typed hB₀ b1.typed hB₁
        (IsDefEq.dir hΓA₀ hB₀).1 (IsDefEq.dir hΓA₁ hB₁).1
        a3.sound b3.sound (IsDefEq.dir hΓ a3.sound.typed).1 a1 b1 hs,
      _, IsDefEq.inst_cod hΓ a1.typed a3.sound.typed hcod⟩
  | fst p ihp =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} _ _ H1 H2 => ?_
    cases H1 with | fst a1 a2 a3 => cases H2 with | fst b1 b2 b3 =>
    have ⟨hs, _, _⟩ := ihp hΓ a3 b3
    have ⟨_, _, hdom, _⟩ := SoundEq.sigma_inv hΓ a1.typed a2.typed hs
    exact ⟨SoundEq.sigma_dom a1 a2.typed b1 b2.typed hs, _, hdom⟩
  | snd p ihp =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} _ _ H1 H2 => ?_
    cases H1 with | snd a1 a2 a3 => cases H2 with | snd b1 b2 b3 =>
    have ⟨hs, _, _⟩ := ihp hΓ a3 b3
    have ⟨_, _, _, hcod⟩ := SoundEq.sigma_inv hΓ a1.typed a2.typed hs
    -- as at `app`, with the Σ probe and the first projection as the argument
    have hfst := IsDefEq.fstDF a1.typed a2.typed a3.sound.typed
    have hfst' := IsDefEq.fstDF b1.typed b2.typed b3.sound.typed
    have hΓA₀ : ⊢ (_ :: Γ) := ⟨hΓ, _, a1.typed⟩
    have hΓA₁ : ⊢ (_ :: Γ) := ⟨hΓ, _, b1.typed⟩
    exact ⟨SoundEq.inst_cod_sigma (IsDefEq.pinned hΓA₀ a2.typed)
        (IsDefEq.pinned hΓA₁ b2.typed) hΓ a1.typed a2.typed b1.typed b2.typed
        (IsDefEq.dir hΓA₀ a2.typed).1 (IsDefEq.dir hΓA₁ b2.typed).1
        (sound_fst a1.typed a2.typed SoundEq.refl a3.sound).2
        (sound_fst b1.typed b2.typed SoundEq.refl b3.sound).2
        (IsDefEq.dir hΓ hfst).1 a1 b1 hs,
      _, IsDefEq.inst_cod hΓ a1.typed hfst hcod⟩
  | refl r a iha =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} _ _ H1 H2 => ?_
    cases H1 with | refl a1 a2 => cases H2 with | refl b1 b2 =>
    have ⟨_, _, h⟩ := iha hΓ a2 b2
    exact ⟨(sound_id h a2.sound.typed a2.sound.typed).1, _,
      .idDF h a2.sound.typed a2.sound.typed⟩
