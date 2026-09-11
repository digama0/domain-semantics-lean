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
  have hprobe : Interp (.forallE A₀ B₀) Γ Subst.id Valuation.nil
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

end DomainSemantics
