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

/-- Two sorts that are definitionally equal are the same sort.  The probe
is the sort shape itself, and the order between two sort shapes *is* the
equation. -/
theorem sort_inv {Γ : List Term} {u v : Bool} {V : Term}
    (hΓ : ⊢ Γ) (H : Γ ⊢ Term.sort u ≡ Term.sort v : V) : u = v := by
  have h := ((IsDefEq.sound hΓ H).1 hΓ (Ctx.SubstEq.id hΓ) Adm.bot).1 Interp.sort'
  have hle := Interp.le_sort h
  exact (TShape.LE.def (Nat.le_refl 0) (Nat.le_refl 0)).1 hle

/-! ### No confusion

Fifteen statements, one argument: put a non-`⊥` probe on whichever side
has one for free, move it across with soundness at the identity stage and
the `⊥` valuation, and read the head off the order — where two different
heads are `False`.

`sort`, `nat` and `unit` have hypothesis-free probes.  `forallE` needs its
regularity lemma first, to build the label-only atom; that is only used
where neither side is one of the three. -/

private theorem not_le_of_head {Δ : List Term} {a b : TShape}
    (hb : ¬ a.2 = Shape.bot)
    (hne : ∀ k, ¬ Shape.LE Δ (a.2.lift k) (b.2.lift k)) :
    ¬ TShape.LE Δ a b := fun h =>
  hne _ ((TShape.LE.def (Nat.le_max_left ..) (Nat.le_max_right ..)).1 h)

theorem sort_forallE_inv {Γ : List Term} {u s : Bool} {A₁ B₁ : Term}
    (hΓ : ⊢ Γ) : ¬Γ ⊢ Term.sort u ≡ Term.forallE A₁ B₁ : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).1 hΓ (Ctx.SubstEq.id hΓ) Adm.bot).1 Interp.sort'
  rcases Interp.le_forallE h with hb | ⟨n, d, g, hle⟩
  · exact Shape0.noConfusion hb
  · exact absurd ((TShape.LE.def (Nat.zero_le _) (Nat.le_refl _)).1 hle)
      (by simp only [Shape.lift_sort]; exact id)

theorem sort_sigma_inv {Γ : List Term} {u s : Bool} {A₁ B₁ : Term}
    (hΓ : ⊢ Γ) : ¬Γ ⊢ Term.sort u ≡ Term.sigma A₁ B₁ : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).1 hΓ (Ctx.SubstEq.id hΓ) Adm.bot).1 Interp.sort'
  rcases Interp.le_sigma h with hb | ⟨n, d, g, hle⟩
  · exact Shape0.noConfusion hb
  · exact absurd ((TShape.LE.def (Nat.zero_le _) (Nat.le_refl _)).1 hle)
      (by simp only [Shape.lift_sort]; exact id)

theorem sort_nat_inv {Γ : List Term} {u s : Bool} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.sort u ≡ Term.nat : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).1 hΓ (Ctx.SubstEq.id hΓ) Adm.bot).1 Interp.sort'
  exact absurd ((TShape.LE.def (Nat.zero_le 1) (Nat.le_refl 1)).1 (Interp.le_nat h))
    (by simp only [Shape.lift_sort]; exact id)

theorem sort_unit_inv {Γ : List Term} {u s r : Bool} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.sort u ≡ Term.unit r : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).1 hΓ (Ctx.SubstEq.id hΓ) Adm.bot).1 Interp.sort'
  exact absurd ((TShape.LE.def (Nat.zero_le 1) (Nat.le_refl 1)).1 (Interp.le_unit h))
    (by simp only [Shape.lift_sort]; exact id)

theorem sort_id_inv {Γ : List Term} {u s r : Bool} {A a b : Term} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.sort u ≡ Term.id r A a b : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).1 hΓ (Ctx.SubstEq.id hΓ) Adm.bot).1 Interp.sort'
  exact absurd ((TShape.LE.def (Nat.zero_le 1) (Nat.le_refl 1)).1 (Interp.le_id h))
    (by simp only [Shape.lift_sort]; exact id)

theorem forallE_nat_inv {Γ : List Term} {s : Bool} {A₀ B₀ : Term} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.forallE A₀ B₀ ≡ Term.nat : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).1 hΓ (Ctx.SubstEq.id hΓ) Adm.bot).2 Interp.nat'
  rcases Interp.le_forallE h with hb | ⟨n, d, g, hle⟩
  · nomatch hb
  · exact absurd ((TShape.LE.def (Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_refl _)).1 hle)
      (by simp only [Shape.lift_self]; exact id)

theorem forallE_unit_inv {Γ : List Term} {s r : Bool} {A₀ B₀ : Term} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.forallE A₀ B₀ ≡ Term.unit r : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).1 hΓ (Ctx.SubstEq.id hΓ) Adm.bot).2 Interp.unit'
  rcases Interp.le_forallE h with hb | ⟨n, d, g, hle⟩
  · nomatch hb
  · exact absurd ((TShape.LE.def (Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_refl _)).1 hle)
      (by simp only [Shape.lift_self]; exact id)

theorem sigma_nat_inv {Γ : List Term} {s : Bool} {A₀ B₀ : Term} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.sigma A₀ B₀ ≡ Term.nat : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).1 hΓ (Ctx.SubstEq.id hΓ) Adm.bot).2 Interp.nat'
  rcases Interp.le_sigma h with hb | ⟨n, d, g, hle⟩
  · nomatch hb
  · exact absurd ((TShape.LE.def (Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_refl _)).1 hle)
      (by simp only [Shape.lift_self]; exact id)

theorem sigma_unit_inv {Γ : List Term} {s r : Bool} {A₀ B₀ : Term} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.sigma A₀ B₀ ≡ Term.unit r : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).1 hΓ (Ctx.SubstEq.id hΓ) Adm.bot).2 Interp.unit'
  rcases Interp.le_sigma h with hb | ⟨n, d, g, hle⟩
  · nomatch hb
  · exact absurd ((TShape.LE.def (Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_refl _)).1 hle)
      (by simp only [Shape.lift_self]; exact id)

theorem nat_unit_inv {Γ : List Term} {s r : Bool} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.nat ≡ Term.unit r : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).1 hΓ (Ctx.SubstEq.id hΓ) Adm.bot).1 Interp.nat'
  exact absurd ((TShape.LE.def (Nat.le_refl 1) (Nat.le_refl 1)).1 (Interp.le_unit h))
    (by simp only [Shape.lift_self]; exact id)

theorem nat_id_inv {Γ : List Term} {s r : Bool} {A a b : Term} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.nat ≡ Term.id r A a b : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).1 hΓ (Ctx.SubstEq.id hΓ) Adm.bot).1 Interp.nat'
  exact absurd ((TShape.LE.def (Nat.le_refl 1) (Nat.le_refl 1)).1 (Interp.le_id h))
    (by simp only [Shape.lift_self]; exact id)

theorem unit_id_inv {Γ : List Term} {s r r' : Bool} {A a b : Term} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.unit r' ≡ Term.id r A a b : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).1 hΓ (Ctx.SubstEq.id hΓ) Adm.bot).1 Interp.unit'
  exact absurd ((TShape.LE.def (Nat.le_refl 1) (Nat.le_refl 1)).1 (Interp.le_id h))
    (by simp only [Shape.lift_self]; exact id)

/-! The three that need a Π or Σ probe, and so a regularity lemma first. -/

theorem forallE_sigma_inv {Γ : List Term} {s : Bool} {A₀ B₀ A₁ B₁ : Term}
    (hΓ : ⊢ Γ) : ¬Γ ⊢ Term.forallE A₀ B₀ ≡ Term.sigma A₁ B₁ : .sort s := by
  intro H
  have ⟨u, hA₀⟩ := H.forallE_dom
  have ⟨v, hB₀⟩ := H.forallE_cod
  have hprobe : Interp Γ Γ (.forallE A₀ B₀) Subst.id Valuation.nil
      (Shape.T (n := 1) (Shape.piAtom (A₀.subst Subst.id) (B₀.subst Subst.id.lift))) :=
    Interp.piAtom (u := u) (v := v) (by simpa using hA₀) (by simpa using hB₀)
  have h := ((IsDefEq.sound hΓ H).1 hΓ (Ctx.SubstEq.id hΓ) Adm.bot).1 hprobe
  rcases Interp.le_sigma h with hb | ⟨n, d, g, hle⟩
  · nomatch hb
  · exact absurd ((TShape.LE.def (Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_refl _)).1 hle)
      (by simp only [Shape.lift_piAtom, Shape.lift_self]; exact id)

theorem forallE_id_inv {Γ : List Term} {s r : Bool} {A₀ B₀ A a b : Term}
    (hΓ : ⊢ Γ) : ¬Γ ⊢ Term.forallE A₀ B₀ ≡ Term.id r A a b : .sort s := by
  intro H
  have ⟨u, hA₀⟩ := H.forallE_dom
  have ⟨v, hB₀⟩ := H.forallE_cod
  have hprobe : Interp Γ Γ (.forallE A₀ B₀) Subst.id Valuation.nil
      (Shape.T (n := 1) (Shape.piAtom (A₀.subst Subst.id) (B₀.subst Subst.id.lift))) :=
    Interp.piAtom (u := u) (v := v) (by simpa using hA₀) (by simpa using hB₀)
  have h := ((IsDefEq.sound hΓ H).1 hΓ (Ctx.SubstEq.id hΓ) Adm.bot).1 hprobe
  exact absurd ((TShape.LE.def (Nat.le_refl 1) (Nat.le_refl 1)).1 (Interp.le_id h))
    (by simp only [Shape.lift_piAtom, Shape.lift_self]; exact id)

theorem sigma_id_inv {Γ : List Term} {s r : Bool} {A₀ B₀ A a b : Term} :
    ¬Γ ⊢ Term.sigma A₀ B₀ ≡ Term.id r A a b : .sort s := by sorry

/-! ### The remaining label inversions -/

theorem sigma_inv {Γ : List Term} {A₀ B₀ A₁ B₁ : Term}
    (hΓ : ⊢ Γ) (H : Γ ⊢ Term.sigma A₀ B₀ ≡ Term.sigma A₁ B₁ : .type) :
    ∃ u v, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ A₀ :: Γ ⊢ B₀ ≡ B₁ : .sort v := by
  sorry

theorem id_inv {Γ : List Term} {r : Bool} {A₀ a₀ b₀ A₁ a₁ b₁ : Term}
    (hΓ : ⊢ Γ) (H : Γ ⊢ Term.id r A₀ a₀ b₀ ≡ Term.id r A₁ a₁ b₁ : .sort r) :
    ∃ u, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ Γ ⊢ a₀ ≡ a₁ : A₀ ∧ Γ ⊢ b₀ ≡ b₁ : A₀ := by
  sorry

end DomainSemantics
