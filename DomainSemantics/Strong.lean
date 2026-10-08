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
  `A'` that is `SoundEq` to `A`.

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
  | mk : (Γ ⊢ t : A) → Sound Γ t t A →
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
  | lam : (Γ ⊢ A : .sort u) →
    StrongSound (A::Γ) e B → StrongSoundCore Γ (.lam A e) (.forallE A B)
  | app : (Γ ⊢ A : .sort u) →
    StrongSound Γ f (.forallE A B) → StrongSound Γ a A →
    StrongSoundCore Γ (.app f a) (B.inst a)
  | forallE : StrongSound Γ A (.sort u) → StrongSound (A::Γ) B (.sort v) →
    StrongSoundCore Γ (.forallE A B) (.sort v)
  | sigma : StrongSound Γ A (.sort u) → StrongSound (A::Γ) B (.sort v) →
    StrongSoundCore Γ (.sigma A B) .type
  | pair : (Γ ⊢ A : .sort u) → (A::Γ) ⊢ B : (.sort v) →
    StrongSound Γ a A → StrongSound Γ b (B.inst a) →
    StrongSoundCore Γ (.pair A B a b) (.sigma A B)
  | fst : (Γ ⊢ A : .sort u) → (A::Γ) ⊢ B : (.sort v) →
    StrongSound Γ p (.sigma A B) → StrongSoundCore Γ (.fst p) A
  | snd : (Γ ⊢ A : .sort u) → (A::Γ) ⊢ B : (.sort v) →
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
  | Y : (Γ ⊢ A : .sort u) → StrongSound (A::Γ) b A.lift →
    StrongSoundCore Γ (.Y A b) A
  | id : StrongSound Γ A (.sort u) →
    StrongSound Γ a A → StrongSound Γ b A →
    StrongSoundCore Γ (.id r A a b) (.sort r)
  | refl : (Γ ⊢ A : .sort u) → StrongSound Γ a A →
    StrongSoundCore Γ (.refl r a) (.id r A a a)
  | tr : (Γ ⊢ A : .sort u) → Γ ⊢ a : A → Γ ⊢ b : A →
    StrongSound (A::Γ) C (.sort v) →
    StrongSound Γ x (C.inst a) → StrongSound Γ h (.id r A a b) →
    StrongSoundCore Γ (.tr r A a b C x h) (C.inst b)
end

theorem StrongSound.typed : StrongSound Γ t A → Γ ⊢ t : A
  | ⟨h, _, _, _, _⟩ => h

theorem StrongSound.sound : StrongSound Γ t A → Sound Γ t t A
  | ⟨_, h, _, _, _⟩ => h

theorem StrongSound.uniq_of_core'
    (H : ∀ {A B}, (∃ u, Γ ⊢ A : .sort u) → (∃ u, Γ ⊢ B : .sort u) →
      StrongSoundCore Γ t A → StrongSoundCore Γ t B →
      SoundEq Γ A B ∧ ∃ u, Γ ⊢ A ≡ B : .sort u) :
    StrongSound Γ t A → StrongSound Γ t B → SoundEq Γ A B ∧ ∃ u, Γ ⊢ A ≡ B : .sort u
  | ⟨_, _, a2, a3, ⟨_, a4⟩⟩, ⟨_, _, b2, b3, ⟨_, b4⟩⟩ =>
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
    have hΓA : ⊢ (A₀ :: Γ) := ⟨hΓ, _, a1.typed⟩
    have ⟨hs, _⟩ := ihB hΓA a2 b2
    cases SoundEq.sort_inv hΓA hs
    exact ⟨SoundEq.refl, hTA⟩
  | lam A₀ e _ ihe =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} _ _ H1 H2 => ?_
    cases H1 with | lam a1 a2 => cases H2 with | lam b1 b2 =>
    have ⟨hs, _, h⟩ := ihe (show ⊢ (A₀ :: Γ) from ⟨hΓ, _, a1⟩) a2 b2
    exact ⟨sound_forallE_eq a1 h h SoundEq.refl (IsDefEq.soundTy hΓ a1) hs hs, _, .forallEDF a1 h h⟩
  | app f a ihf _ =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} _ _ H1 H2 => ?_
    cases H1 with | app a1 a2 a3 => cases H2 with | app b1 b2 b3 =>
    have ⟨hs, _, hpi⟩ := ihf hΓ a2 b2
    have ⟨_, hB₀⟩ := hpi.forallE_cod
    have ⟨_, hB₁⟩ := hpi.symm.forallE_cod
    have ⟨_, _, _, hcod⟩ := SoundEq.forallE_inv hΓ a1 hB₀ hs
    -- the semantic half: `Interp.inst` splits `B[a]` at a slot, `SoundTy a A`
    -- types the slot, and `SoundEq.forallE_cod` moves it to the other codomain
    have hΓA₀ : ⊢ (_ :: Γ) := ⟨hΓ, _, a1⟩
    have hΓA₁ : ⊢ (_ :: Γ) := ⟨hΓ, _, b1⟩
    exact ⟨SoundEq.inst_cod (IsDefEq.pinned hΓA₀ hB₀) (IsDefEq.pinned hΓA₁ hB₁)
        hΓ a1 hB₀ b1 hB₁
        a3.typed b3.typed a3.sound.ty b3.sound.ty
        (IsDefEq.soundTy hΓ a1) (IsDefEq.soundTy hΓ b1)
        (IsDefEq.soundTy hΓA₀ hB₀).codeAt (IsDefEq.soundTy hΓA₁ hB₁).codeAt hs,
      _, IsDefEq.inst_cod hΓ a1 a3.typed hcod⟩
  | fst p ihp =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} _ _ H1 H2 => ?_
    cases H1 with | fst a1 a2 a3 => cases H2 with | fst b1 b2 b3 =>
    have ⟨hs, _, _⟩ := ihp hΓ a3 b3
    have ⟨_, _, hdom, _⟩ := SoundEq.sigma_inv hΓ a1 a2 hs
    exact ⟨SoundEq.sigma_dom a1 b1 (IsDefEq.soundTy hΓ a1) a2
      (IsDefEq.soundTy hΓ a1).codeAt (IsDefEq.soundTy hΓ b1) b2
      (IsDefEq.soundTy hΓ b1).codeAt hs, _, hdom⟩
  | snd p ihp =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} _ _ H1 H2 => ?_
    cases H1 with | snd a1 a2 a3 => cases H2 with | snd b1 b2 b3 =>
    have ⟨hs, _, _⟩ := ihp hΓ a3 b3
    have ⟨_, _, _, hcod⟩ := SoundEq.sigma_inv hΓ a1 a2 hs
    -- as at `app`, with the Σ probe and the first projection as the argument
    have hfst := IsDefEq.fstDF a1 a2 a3.typed
    have hfst' := IsDefEq.fstDF b1 b2 b3.typed
    have hΓA₀ : ⊢ (_ :: Γ) := ⟨hΓ, _, a1⟩
    have hΓA₁ : ⊢ (_ :: Γ) := ⟨hΓ, _, b1⟩
    exact ⟨SoundEq.inst_cod_sigma (IsDefEq.pinned hΓA₀ a2)
        (IsDefEq.pinned hΓA₁ b2) hΓ a1 a2 b1 b2
        hfst hfst' (IsDefEq.soundTy hΓ hfst) (IsDefEq.soundTy hΓ hfst')
        (IsDefEq.soundTy hΓ a1) (IsDefEq.soundTy hΓ b1)
        (IsDefEq.soundTy hΓA₀ a2).codeAt (IsDefEq.soundTy hΓA₁ b2).codeAt hs,
      _, IsDefEq.inst_cod hΓ a1 hfst hcod⟩
  | refl r a iha =>
    intro Γ A B hΓ
    refine uniq_of_core' fun {A B} _ _ H1 H2 => ?_
    cases H1 with | refl a1 a2 => cases H2 with | refl b1 b2 =>
    have ⟨_, _, h⟩ := iha hΓ a2 b2
    exact ⟨(sound_id h a2.typed a2.typed).1, _,
      .idDF h a2.typed a2.typed⟩
