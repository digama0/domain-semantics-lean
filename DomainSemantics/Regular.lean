import DomainSemantics.Term

/-! # Regularity for `forallE`

A purely syntactic lemma: if a Π-type appears as either side of a
definitional equality, its domain is a type and its codomain is a type
over the domain.

Master gets these two facts out of `forallE_inv`, which comes out of
adequacy.  This branch proves Π-injectivity *from* soundness instead, and
the semantic probe that reads the Π label back (`Interp.piAtom`) needs
exactly these two facts to be built.  So they have to be recovered here,
by induction on the derivation, before inversion can run.

The statement is **two-sided** — `e` or `e'` is the Π — and that is
forced, in two separate ways.

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

theorem IsDefEq.forallE_regular {Γ : List Term} {e e' X : Term} (H : Γ ⊢ e ≡ e' : X) :
    ∀ {A B : Term}, e = .forallE A B ∨ e' = .forallE A B →
      (∃ u, Γ ⊢ A : .sort u) ∧ ∃ v, A :: Γ ⊢ B : .sort v := by
  induction H with
  | forallEDF hA hb hb' _ _ _ =>
    intro A B h
    match h with
    | .inl h =>
      injection h with h1 h2
      subst h1; subst h2
      exact ⟨⟨_, hA.hasType.1⟩, _, hb.hasType.1⟩
    | .inr h =>
      injection h with h1 h2
      subst h1; subst h2
      exact ⟨⟨_, hA.hasType.2⟩, _, hb'.hasType.2⟩
  | _ =>
    intro A B h
    rcases h with h | h <;>
      first
        | exact Term.noConfusion h
        | solve_by_elim [Or.inl, Or.inr]

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
theorem IsDefEq.id_regular {Γ : List Term} {e e' X : Term} (H : Γ ⊢ e ≡ e' : X) :
    ∀ {r} {A a b : Term}, e = .id r A a b ∨ e' = .id r A a b →
      (∃ u, Γ ⊢ A : .sort u) ∧ Γ ⊢ a : A ∧ Γ ⊢ b : A := by
  induction H with
  | idDF hA ha hb _ _ _ =>
    intro r A a b h
    match h with
    | .inl h =>
      injection h with _ h1 h2 h3
      subst h1; subst h2; subst h3
      exact ⟨⟨_, hA.hasType.1⟩, ha.hasType.1, hb.hasType.1⟩
    | .inr h =>
      injection h with _ h1 h2 h3
      subst h1; subst h2; subst h3
      exact ⟨⟨_, hA.hasType.2⟩, hA.defeqDF ha.hasType.2, hA.defeqDF hb.hasType.2⟩
  | _ =>
    intro r A a b h
    rcases h with h | h <;>
      first
        | exact Term.noConfusion h
        | solve_by_elim [Or.inl, Or.inr]

/-- The components of an `id` that is definitionally equal to anything. -/
theorem IsDefEq.id_dom {Γ : List Term} {r} {A a b e X : Term}
    (H : Γ ⊢ .id r A a b ≡ e : X) :
    (∃ u, Γ ⊢ A : .sort u) ∧ Γ ⊢ a : A ∧ Γ ⊢ b : A :=
  H.id_regular (.inl rfl)
