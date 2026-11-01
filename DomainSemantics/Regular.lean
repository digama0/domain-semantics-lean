import DomainSemantics.DefEq

/-! # Regularity and shallow inversion

Purely syntactic lemmas, each reading one layer off a definitional
equality: the subject's own premises, and typings for its subterms in the
contexts they live in.  For `forallE` that says the domain is a type and
the codomain is a type over the domain.

`popl27` gets those two facts out of `forallE_inv`, which comes out of
adequacy.  Here Π-injectivity comes *from* soundness instead, and
the semantic probe that reads the Π label back (`Interp.piAtom`) needs
exactly these two facts to be built.  So they have to be recovered here,
by induction on the derivation, before inversion can run.  The remaining
formers follow under "Shallow inversion" below, where strengthening is
what reads them.

Every statement is **two-sided** — `e` or `e'` is the subject — and that
is forced, in two separate ways.

* `symm` and `trans` move a subject from one side to the other, so a
  one-sided statement has no induction hypothesis to appeal to.
* The computation rules produce a Π on the *right* out of a subject that
  is not one syntactically: `beta` concludes at `e.inst e'`, which is a Π
  whenever `e` is `bvar 0` and `e'` is a Π.  Each such rule carries a
  reflexive premise typing its own right-hand side, and that premise's
  induction hypothesis is what discharges the case.  The same premise
  covers `eta`, `unit_eta`, `natCase_zero`, `natCase_succ`, `Y_unfold`,
  `tr_refl`, `pair_fst`, `pair_snd` and `fst_snd`. -/

namespace DomainSemantics

theorem IsDefEq.forallE_regular {Γ : List Term} {e e' X : Term} (H : Γ ⊢ e ≡ e' : X)
    {A B : Term} (h : e = .forallE A B ∨ e' = .forallE A B) :
    (∃ u, Γ ⊢ A : .sort u) ∧ ∃ v, A :: Γ ⊢ B : .sort v := by
  induction H with
  | forallEDF hA hb hb' => ?_
  | _ => rcases h with h | h <;> first | (cases h; done) | solve_by_elim [Or.inl, Or.inr]
  rcases h with h | h <;> cases h
  · exact ⟨⟨_, hA.hasType.1⟩, _, hb.hasType.1⟩
  · exact ⟨⟨_, hA.hasType.2⟩, _, hb'.hasType.2⟩

/-- The domain of a Π-type that is definitionally equal to anything is a
type. -/
theorem IsDefEq.forallE_dom {Γ : List Term} {A B e X : Term}
    (H : Γ ⊢ .forallE A B ≡ e : X) : ∃ u, Γ ⊢ A : .sort u :=
  (H.forallE_regular (.inl rfl)).1

/-- And its codomain is a type over the domain. -/
theorem IsDefEq.forallE_cod {Γ : List Term} {A B e X : Term}
    (H : Γ ⊢ .forallE A B ≡ e : X) : ∃ v, A :: Γ ⊢ B : .sort v :=
  (H.forallE_regular (.inl rfl)).2

/-- The same for `id`: its three components are typed wherever it occurs
in a definitional equality.  Same induction as `forallE_regular`, and the
`idDF` case is the only one with content. -/
theorem IsDefEq.id_regular {Γ : List Term} {e e' X : Term} (H : Γ ⊢ e ≡ e' : X)
    {r} {A a b : Term} (h : e = .id r A a b ∨ e' = .id r A a b) :
    (∃ u, Γ ⊢ A : .sort u) ∧ Γ ⊢ a : A ∧ Γ ⊢ b : A := by
  induction H with
  | idDF hA ha hb => ?_
  | _ => rcases h with h | h <;> first | (cases h; done) | solve_by_elim [Or.inl, Or.inr]
  rcases h with h | h <;> cases h
  · exact ⟨⟨_, hA.hasType.1⟩, ha.hasType.1, hb.hasType.1⟩
  · exact ⟨⟨_, hA.hasType.2⟩, hA.defeqDF ha.hasType.2, hA.defeqDF hb.hasType.2⟩

/-- The components of an `id` that is definitionally equal to anything. -/
theorem IsDefEq.id_dom {Γ : List Term} {r} {A a b e X : Term}
    (H : Γ ⊢ .id r A a b ≡ e : X) :
    (∃ u, Γ ⊢ A : .sort u) ∧ Γ ⊢ a : A ∧ Γ ⊢ b : A :=
  H.id_regular (.inl rfl)

/-- The same for Σ; `sigmaDF` is the only case with content. -/
theorem IsDefEq.sigma_regular {Γ : List Term} {e e' X : Term} (H : Γ ⊢ e ≡ e' : X)
    {A B : Term} (h : e = .sigma A B ∨ e' = .sigma A B) :
    (∃ u, Γ ⊢ A : .sort u) ∧ ∃ v, A :: Γ ⊢ B : .sort v := by
  induction H with
  | sigmaDF hA hb hb' => ?_
  | _ => rcases h with h | h <;> first | (cases h; done) | solve_by_elim [Or.inl, Or.inr]
  rcases h with h | h <;> cases h
  · exact ⟨⟨_, hA.hasType.1⟩, _, hb.hasType.1⟩
  · exact ⟨⟨_, hA.hasType.2⟩, _, hb'.hasType.2⟩

/-- Instantiating a definitional equality of codomains at an argument.
`IsDefEq.subst` at `Subst.one a`, which is what `Term.inst` unfolds to. -/
theorem IsDefEq.inst_cod {Γ : List Term} {A B B' a : Term} {u v : Bool} (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A : .sort u) (ha : Γ ⊢ a : A) (h : A :: Γ ⊢ B ≡ B' : .sort v) :
    Γ ⊢ B.inst a ≡ B'.inst a : .sort v := by
  refine subst hΓ ?_ h
  exact .cons (.id hΓ) hA (by simpa using ha)

/-- The same for `succ`: its argument is a numeral wherever it occurs in a
definitional equality.  `succDF` is the only case with content; the
computation rules are covered by the reflexive premise typing their own
right-hand side, as in `forallE_regular`. -/
theorem IsDefEq.succ_regular {Γ : List Term} {e e' X : Term} (H : Γ ⊢ e ≡ e' : X)
    {t : Term} (h : e = .succ t ∨ e' = .succ t) : Γ ⊢ t : .nat := by
  induction H with
  | succDF ht => ?_
  | _ => rcases h with h | h <;> first | (cases h; done) | solve_by_elim [Or.inl, Or.inr]
  rcases h with h | h <;> cases h
  · exact ht.hasType.1
  · exact ht.hasType.2

theorem IsDefEq.succ_inj {Γ : List Term} {t t' : Term} (hΓ : ⊢ Γ)
    (H : Γ ⊢ .succ t ≡ .succ t' : .nat) : Γ ⊢ t ≡ t' : .nat := by
  have ht : Γ ⊢ t : .nat := H.succ_regular (.inl rfl)
  have ht' : Γ ⊢ t' : .nat := H.succ_regular (.inr rfl)
  have hΓN : ⊢ (.nat :: Γ) := ⟨hΓ, _, .nat⟩
  have hC : .nat :: Γ ⊢ .nat : .sort true := .nat
  have hz : Γ ⊢ .zero : .nat := .zero
  have hb : .nat :: Γ ⊢ .bvar 0 : .nat := .bvar .zero .nat
  -- the predecessor of a numeral, computed
  have hpred {s : Term} (hs : Γ ⊢ s : .nat) :
      Γ ⊢ .natCase .nat (.succ s) .zero (.bvar 0) ≡ s : .nat :=
    .natCase_succ hC hs hz hb (.natCaseDF hC (.succDF hs) hz hb .nat) hs
  exact ((hpred ht).symm.trans (.natCaseDF hC H hz hb .nat)).trans (hpred ht')

theorem IsDefEq.sigma_dom {Γ : List Term} {A B e X : Term}
    (H : Γ ⊢ .sigma A B ≡ e : X) : ∃ u, Γ ⊢ A : .sort u :=
  (H.sigma_regular (.inl rfl)).1

theorem IsDefEq.sigma_cod {Γ : List Term} {A B e X : Term}
    (H : Γ ⊢ .sigma A B ≡ e : X) : ∃ v, A :: Γ ⊢ B : .sort v :=
  (H.sigma_regular (.inl rfl)).2

/-! ## Shallow inversion, former by former

Together these are what `Term.Annot` carried as a predicate before it was
deleted, and the induction is the same in each — the former's congruence
rule is the only case with content, the computation rules go through their
reflexive premise's induction hypothesis, and everything else is
`noConfusion`.

They are two-sided (`e = … ∨ e' = …`) because `symm` and `trans` demand
it: proving the left side for `symm H` is proving the right side for `H`. -/

theorem IsDefEq.app_regular {Γ : List Term} {e e' X : Term} (H : Γ ⊢ e ≡ e' : X)
    {F a : Term} (h : e = .app F a ∨ e' = .app F a) :
    (∃ A B, Γ ⊢ F : .forallE A B) ∧ ∃ A₀, Γ ⊢ a : A₀ := by
  induction H with
  | appDF _ _ hf ha => ?_
  | _ => rcases h with h | h <;> first | (cases h; done) | solve_by_elim [Or.inl, Or.inr]
  rcases h with h | h <;> cases h
  · exact ⟨⟨_, _, hf.hasType.1⟩, _, ha.hasType.1⟩
  · exact ⟨⟨_, _, hf.hasType.2⟩, _, ha.hasType.2⟩

theorem IsDefEq.lam_regular {Γ : List Term} {e e' X : Term} (H : Γ ⊢ e ≡ e' : X)
    {A b : Term} (h : e = .lam A b ∨ e' = .lam A b) :
    (∃ u, Γ ⊢ A : .sort u) ∧ ∃ B, A :: Γ ⊢ b : B := by
  induction H with
  | lamDF hA _ hb hb' => ?_
  | _ => rcases h with h | h <;> first | (cases h; done) | solve_by_elim [Or.inl, Or.inr]
  rcases h with h | h <;> cases h
  · exact ⟨⟨_, hA.hasType.1⟩, _, hb.hasType.1⟩
  · exact ⟨⟨_, hA.hasType.2⟩, _, hb'.hasType.2⟩

theorem IsDefEq.bvar_regular {Γ : List Term} {e e' X : Term} (H : Γ ⊢ e ≡ e' : X)
    {i : Nat} (h : e = .bvar i ∨ e' = .bvar i) : ∃ A, Lookup Γ i A := by
  induction H with
  | bvar hlk => rcases h with h | h <;> cases h <;> exact ⟨_, hlk⟩
  | _ => rcases h with h | h <;> first | (cases h; done) | solve_by_elim [Or.inl, Or.inr]

theorem IsDefEq.fst_regular {Γ : List Term} {e e' X : Term} (H : Γ ⊢ e ≡ e' : X)
    {p : Term} (h : e = .fst p ∨ e' = .fst p) : ∃ A B, Γ ⊢ p : .sigma A B := by
  induction H with
  | fstDF _ _ hp => ?_
  | _ => rcases h with h | h <;> first | (cases h; done) | solve_by_elim [Or.inl, Or.inr]
  rcases h with h | h <;> cases h
  · exact ⟨_, _, hp.hasType.1⟩
  · exact ⟨_, _, hp.hasType.2⟩

theorem IsDefEq.snd_regular {Γ : List Term} {e e' X : Term} (H : Γ ⊢ e ≡ e' : X)
    {p : Term} (h : e = .snd p ∨ e' = .snd p) : ∃ A B, Γ ⊢ p : .sigma A B := by
  induction H with
  | sndDF _ _ hp => ?_
  | _ => rcases h with h | h <;> first | (cases h; done) | solve_by_elim [Or.inl, Or.inr]
  rcases h with h | h <;> cases h
  · exact ⟨_, _, hp.hasType.1⟩
  · exact ⟨_, _, hp.hasType.2⟩

theorem IsDefEq.pair_regular {Γ : List Term} {e e' X : Term} (H : Γ ⊢ e ≡ e' : X)
    {A B a b : Term} (h : e = .pair A B a b ∨ e' = .pair A B a b) :
    (∃ u, Γ ⊢ A : .sort u) ∧ (∃ v, A :: Γ ⊢ B : .sort v) ∧ (Γ ⊢ a : A) ∧ ∃ T, Γ ⊢ b : T := by
  induction H with
  | pairDF hA hB hB' ha hb => ?_
  | _ => rcases h with h | h <;> first | (cases h; done) | solve_by_elim [Or.inl, Or.inr]
  rcases h with h | h <;> cases h
  · exact ⟨⟨_, hA.hasType.1⟩, ⟨_, hB.hasType.1⟩, ha.hasType.1, _, hb.hasType.1⟩
  · exact ⟨⟨_, hA.hasType.2⟩, ⟨_, hB'.hasType.2⟩, hA.defeqDF ha.hasType.2, _, hb.hasType.2⟩

theorem IsDefEq.natCase_regular {Γ : List Term} {e e' X : Term} (H : Γ ⊢ e ≡ e' : X)
    {C M a b : Term} (h : e = .natCase C M a b ∨ e' = .natCase C M a b) :
    (Γ ⊢ M : .nat) ∧ (∃ T, Γ ⊢ a : T) ∧ ∃ T, .nat :: Γ ⊢ b : T := by
  induction H with
  | natCaseDF _ hM ha hb => ?_
  | _ => rcases h with h | h <;> first | (cases h; done) | solve_by_elim [Or.inl, Or.inr]
  rcases h with h | h <;> cases h
  · exact ⟨hM.hasType.1, ⟨_, ha.hasType.1⟩, _, hb.hasType.1⟩
  · exact ⟨hM.hasType.2, ⟨_, ha.hasType.2⟩, _, hb.hasType.2⟩

theorem IsDefEq.Y_regular {Γ : List Term} {e e' X : Term} (H : Γ ⊢ e ≡ e' : X)
    {A b : Term} (h : e = .Y A b ∨ e' = .Y A b) :
    (∃ u, Γ ⊢ A : .sort u) ∧ (Γ ⊢ .Y A b : A) ∧ ∃ T, A :: Γ ⊢ b : T := by
  induction H with
  | YDF hA hb hb' => ?_
  | _ => rcases h with h | h <;> first | (cases h; done) | solve_by_elim [Or.inl, Or.inr]
  rcases h with h | h <;> cases h
  · exact ⟨⟨_, hA.hasType.1⟩, (YDF hA hb hb').hasType.1, _, hb.hasType.1⟩
  · exact ⟨⟨_, hA.hasType.2⟩, hA.defeqDF (YDF hA hb hb').hasType.2, _, hb'.hasType.2⟩

/-- The widest of these: `tr` carries the motive's instance at the *source*
point, which is what the slot rebuild reads, so the witness is existential
in the point and the motive rather than fixed at `a` and `C`. -/
theorem IsDefEq.tr_regular {Γ : List Term} {e e' X : Term} (H : Γ ⊢ e ≡ e' : X)
    {r} {A a b C x h : Term} (he : e = .tr r A a b C x h ∨ e' = .tr r A a b C x h) :
    (∃ u, Γ ⊢ A : .sort u) ∧ (Γ ⊢ a : A) ∧ (Γ ⊢ b : A) ∧ (Γ ⊢ h : .id r A a b) ∧
      (∃ a₀ C₀ v, (Γ ⊢ x : C₀.inst a₀) ∧ (Γ ⊢ a₀ ≡ a : A) ∧
        (A :: Γ ⊢ C₀ ≡ C : .sort v)) ∧ (∃ v, A :: Γ ⊢ C : .sort v) := by
  induction H with
  | trDF hA ha hb hC hC' hx hh => ?_
  | _ => rcases he with he | he <;> first | (cases he; done) | solve_by_elim [Or.inl, Or.inr]
  rcases he with he | he <;> cases he
  · refine ⟨⟨_, hA.hasType.1⟩, ha.hasType.1, hb.hasType.1, hh.hasType.1, ?_, _, hC.hasType.1⟩
    exact ⟨_, _, _, hx.hasType.1, ha.hasType.1, hC.hasType.1⟩
  · refine ⟨⟨_, hA.hasType.2⟩, hA.defeqDF ha.hasType.2, hA.defeqDF hb.hasType.2, ?_, ?_, ?_⟩
    · exact (idDF hA ha hb).defeqDF hh.hasType.2
    · exact ⟨_, _, _, hx.hasType.2, hA.defeqDF ha, hC'⟩
    · exact ⟨_, hC'.hasType.2⟩
