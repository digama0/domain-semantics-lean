import DomainSemantics.Presheaf
import DomainSemantics.Regular

/-! # Inversion from soundness

Π-injectivity, straight out of soundness.  Master gets it from adequacy:
`LogRel.lean` plus `Adequacy.lean`, 4.9k lines, to relate the semantics to
weak-head reduction and read the head former off a normal form.  Here the
head former never leaves the shape, so the argument is four steps:

1. the Π is regular (`IsDefEq.forallE_regular`, purely syntactic);
2. so it has a label-only approximant, its own `piAtom`
   (`Interp.piAtom`);
3. soundness moves that approximant to the other side (`SoundEq`), at the
   identity stage and the `⊥` valuation, which is admissible for free
   (`Adm.bot`);
4. reading the label back off it is a projection out of the order
   (`Interp.le_piAtom`), and the label *is* the pair of definitional
   equalities wanted.

The only input beyond the syntax is `IsDefEq.sound`. -/

namespace DomainSemantics

@[simp] theorem Subst.lift_id : Subst.id.lift = Subst.id := by
  funext i; cases i <;> rfl

/-- **Π-injectivity.**  Master's `forallE_inv`, with the same statement,
proved from soundness instead of adequacy. -/
theorem forallE_inv {Γ : List Term} {A₀ B₀ A₁ B₁ : Term} {s : Bool}
    (hΓ : ⊢ Γ) (H : Γ ⊢ Term.forallE A₀ B₀ ≡ Term.forallE A₁ B₁ : .sort s) :
    ∃ u v, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ A₀ :: Γ ⊢ B₀ ≡ B₁ : .sort v := by
  have ⟨u, hA₀⟩ := H.forallE_dom
  have ⟨v, hB₀⟩ := H.forallE_cod
  -- the probe: the Π's own label, with nothing else in it
  have hprobe : Interp Γ Γ (.forallE A₀ B₀) Subst.id Valuation.nil
      (Shape.T (n := 1) (Shape.piAtom (A₀.subst Subst.id) (B₀.subst Subst.id.lift))) := by
    refine Interp.piAtom (u := u) (v := v) ?_ ?_
    · simpa using hA₀
    · simpa using hB₀
  -- soundness moves it across, at the identity stage and the `⊥` valuation
  have hmove := ((IsDefEq.sound hΓ H).1 hΓ (Ctx.SubstEq.id hΓ) Adm.bot).1 hprobe
  simp only [subst_id, Subst.lift_id] at hmove
  -- and the label reads back off it
  have hlab := Interp.le_piAtom hmove
  simp only [subst_id, Subst.lift_id] at hlab
  obtain ⟨u', hu⟩ := hlab.1
  obtain ⟨v', hv⟩ := hlab.2
  exact ⟨u', v', hu, hv⟩

/-! ## The rest of the inversion principles

`Consequences.lean` consumes eighteen of these from `Adequacy.lean`.  Each
is the same four-step argument as `forallE_inv`: regularity gives a
label-only probe, soundness moves it to the other side at the identity
stage and the `⊥` valuation, and the order reads the label back.  For the
no-confusion family the last step is trivial, since the order between two
different heads is `False`; those need no regularity lemma either, only a
probe for one of the two heads.

They are stated here so the endpoint of the branch is explicit.  Once they
are proved, `Consequences.lean` can be re-pointed at this file and
`Adequacy.lean`, `LogRel.lean` and `Sound.lean` deleted. -/

theorem sort_inv {Γ : List Term} {u v : Bool} {V : Term}
    (hΓ : ⊢ Γ) (H : Γ ⊢ Term.sort u ≡ Term.sort v : V) : u = v := by
  sorry

theorem sigma_inv {Γ : List Term} {A₀ B₀ A₁ B₁ : Term}
    (hΓ : ⊢ Γ) (H : Γ ⊢ Term.sigma A₀ B₀ ≡ Term.sigma A₁ B₁ : .type) :
    ∃ u v, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ A₀ :: Γ ⊢ B₀ ≡ B₁ : .sort v := by
  sorry

theorem id_inv {Γ : List Term} {r : Bool} {A₀ a₀ b₀ A₁ a₁ b₁ : Term}
    (hΓ : ⊢ Γ) (H : Γ ⊢ Term.id r A₀ a₀ b₀ ≡ Term.id r A₁ a₁ b₁ : .sort r) :
    ∃ u, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ Γ ⊢ a₀ ≡ a₁ : A₀ ∧ Γ ⊢ b₀ ≡ b₁ : A₀ := by
  sorry

/-! The no-confusion family: two distinct heads are never definitionally
equal.  Fifteen statements, one argument. -/

theorem sort_forallE_inv {Γ : List Term} {u s : Bool} {A₁ B₁ : Term} :
    ¬Γ ⊢ Term.sort u ≡ Term.forallE A₁ B₁ : .sort s := by sorry

theorem sort_sigma_inv {Γ : List Term} {u s : Bool} {A₁ B₁ : Term} :
    ¬Γ ⊢ Term.sort u ≡ Term.sigma A₁ B₁ : .sort s := by sorry

theorem sort_nat_inv {Γ : List Term} {u s : Bool} :
    ¬Γ ⊢ Term.sort u ≡ Term.nat : .sort s := by sorry

theorem sort_unit_inv {Γ : List Term} {u s : Bool} {r : Bool} :
    ¬Γ ⊢ Term.sort u ≡ Term.unit r : .sort s := by sorry

theorem sort_id_inv {Γ : List Term} {u s : Bool} {r : Bool} {A a b : Term} :
    ¬Γ ⊢ Term.sort u ≡ Term.id r A a b : .sort s := by sorry

theorem forallE_sigma_inv {Γ : List Term} {s : Bool} {A₀ B₀ A₁ B₁ : Term} :
    ¬Γ ⊢ Term.forallE A₀ B₀ ≡ Term.sigma A₁ B₁ : .sort s := by sorry

theorem forallE_nat_inv {Γ : List Term} {s : Bool} {A₀ B₀ : Term} :
    ¬Γ ⊢ Term.forallE A₀ B₀ ≡ Term.nat : .sort s := by sorry

theorem forallE_unit_inv {Γ : List Term} {s r : Bool} {A₀ B₀ : Term} :
    ¬Γ ⊢ Term.forallE A₀ B₀ ≡ Term.unit r : .sort s := by sorry

theorem forallE_id_inv {Γ : List Term} {s r : Bool} {A₀ B₀ A a b : Term} :
    ¬Γ ⊢ Term.forallE A₀ B₀ ≡ Term.id r A a b : .sort s := by sorry

theorem sigma_nat_inv {Γ : List Term} {s : Bool} {A₀ B₀ : Term} :
    ¬Γ ⊢ Term.sigma A₀ B₀ ≡ Term.nat : .sort s := by sorry

theorem sigma_unit_inv {Γ : List Term} {s r : Bool} {A₀ B₀ : Term} :
    ¬Γ ⊢ Term.sigma A₀ B₀ ≡ Term.unit r : .sort s := by sorry

theorem sigma_id_inv {Γ : List Term} {s r : Bool} {A₀ B₀ A a b : Term} :
    ¬Γ ⊢ Term.sigma A₀ B₀ ≡ Term.id r A a b : .sort s := by sorry

theorem nat_unit_inv {Γ : List Term} {s r : Bool} :
    ¬Γ ⊢ Term.nat ≡ Term.unit r : .sort s := by sorry

theorem nat_id_inv {Γ : List Term} {s r : Bool} {A a b : Term} :
    ¬Γ ⊢ Term.nat ≡ Term.id r A a b : .sort s := by sorry

theorem unit_id_inv {Γ : List Term} {s r r' : Bool} {A a b : Term} :
    ¬Γ ⊢ Term.unit r' ≡ Term.id r A a b : .sort s := by sorry

end DomainSemantics
