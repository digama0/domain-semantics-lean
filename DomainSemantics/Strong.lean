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
    StrongSoundCore Γ t A' → SoundEq Γ A' A → StrongSound Γ t A

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
  | ⟨h, _, _⟩ => h

theorem StrongSoundEq.symm : StrongSoundEq Γ t t' A → StrongSoundEq Γ t' t A
  | ⟨h1, h2, h3⟩ => ⟨h1.symm, h3, h2⟩

theorem StrongSoundEq.rfl' (H : StrongSound Γ t A) : StrongSoundEq Γ t t A :=
  ⟨SoundEq.refl, H, H⟩

theorem StrongSoundEq.trans :
    StrongSoundEq Γ t t' A → StrongSoundEq Γ t' t'' A → StrongSoundEq Γ t t'' A
  | ⟨a1, a2, _⟩, ⟨b1, _, b3⟩ => ⟨a1.trans b1, a2, b3⟩

/-- The type of a `SoundTy` moves along a semantic equality of types. -/
theorem SoundTy.defeq_r (H1 : SoundEq Γ A B) (H : SoundTy Γ t A) : SoundTy Γ t B := by
  intro Δ Γ₀ σ ρ hΔ W hAdm m h
  have ⟨a, ha, hty⟩ := H hΔ W hAdm h
  exact ⟨a, (H1 hΔ W hAdm).1 ha, hty⟩

theorem StrongSound.defeq_r (H1 : SoundEq Γ A B) : StrongSound Γ t A → StrongSound Γ t B
  | ⟨sound, core, eq⟩ => ⟨sound.defeq_r H1, core, eq.trans H1⟩

/-- The way each soundness case will build its `StrongSoundEq`: the two
structural derivations, and the pair of semantic facts `IsDefEq.sound`
already produces. -/
theorem StrongSoundEq.mk'
    (h2 : StrongSoundCore Γ t A₁) (h2' : SoundEq Γ A₁ A)
    (h3 : StrongSoundCore Γ t' A₂) (h3' : SoundEq Γ A₂ A)
    (h4 : SoundEq Γ t t' ∧ SoundTy Γ t A) :
    StrongSoundEq Γ t t' A :=
  ⟨h4.1, ⟨h4.2, h2, h2'⟩, ⟨SoundTy.of_eq h4.1 h4.2, h3, h3'⟩⟩

/-- **Semantic uniqueness of types**, given it for the structural
relation.  Master's `uniq_of_core`. -/
theorem StrongSound.uniq_of_core
    (H : ∀ {A B}, StrongSoundCore Γ t A → StrongSoundCore Γ t B → SoundEq Γ A B) :
    StrongSound Γ t A → StrongSound Γ t B → SoundEq Γ A B
  | ⟨_, a2, a3⟩, ⟨_, b2, b3⟩ => a3.symm.trans ((H a2 b2).trans b3)
