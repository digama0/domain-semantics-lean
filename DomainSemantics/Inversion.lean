import DomainSemantics.Sound
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
   (`Adm.bot hΓ (Ctx.SubstEq.id hΓ)`);
4. reading the label back off it is a projection out of the order
   (`Interp.le_piAtom`), and the label *is* the pair of definitional
   equalities wanted.

The only input beyond the syntax is `IsDefEq.sound`. -/

namespace DomainSemantics

/-- **Π-injectivity.**  Master's `forallE_inv`, with the same statement,
proved from soundness instead of adequacy. -/
theorem forallE_inv {Γ : List Term} {A₀ B₀ A₁ B₁ : Term} {s : Bool}
    (hΓ : ⊢ Γ) (H : Γ ⊢ Term.forallE A₀ B₀ ≡ Term.forallE A₁ B₁ : .sort s) :
    ∃ u v, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ A₀ :: Γ ⊢ B₀ ≡ B₁ : .sort v :=
  have ⟨_, hA₀⟩ := H.forallE_dom
  have ⟨_, hB₀⟩ := H.forallE_cod
  SoundEq.forallE_inv hΓ hA₀ hB₀ (IsDefEq.sound hΓ H).eq

/-! ## The rest of the inversion principles

`Consequences.lean` is built on these.  Each is the same four-step argument as
`forallE_inv`: regularity gives a label-only probe, soundness moves it to the
other side at the identity stage and the `⊥` valuation, and the order reads the
label back.  For the no-confusion family the last step is trivial, since the order
between two different heads is `False`; those need no regularity lemma either, only a
probe for one of the two heads. -/

/-- Two sorts that are definitionally equal are the same sort.  The probe
is the sort shape itself, and the order between two sort shapes *is* the
equation. -/
theorem sort_inv {Γ : List Term} {u v : Bool} {V : Term}
    (hΓ : ⊢ Γ) (H : Γ ⊢ Term.sort u ≡ Term.sort v : V) : u = v :=
  SoundEq.sort_inv hΓ (IsDefEq.sound hΓ H).eq

/-! ### No confusion

Fifteen statements, one argument: put a non-`⊥` probe on whichever side
has one for free, move it across with soundness at the identity stage and
the `⊥` valuation, and read the head off the order — where two different
heads are `False`.

`sort`, `nat` and `unit` have hypothesis-free probes.  `forallE` needs its
regularity lemma first, to build the label-only atom; that is only used
where neither side is one of the three. -/

theorem sort_forallE_inv {Γ : List Term} {u s : Bool} {A₁ B₁ : Term}
    (hΓ : ⊢ Γ) : ¬Γ ⊢ Term.sort u ≡ Term.forallE A₁ B₁ : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).eq hΓ (Ctx.SubstEq.id hΓ) (Adm.bot hΓ (Ctx.SubstEq.id hΓ))).1 Interp.sort'
  rcases Interp.le_forallE h with hb | ⟨n, d, g, hle⟩
  · exact Shape0.noConfusion hb
  · exact absurd ((TShape.LE.def_mp (Nat.zero_le _) (Nat.le_refl _)) hle)
      id

theorem sort_sigma_inv {Γ : List Term} {u s : Bool} {A₁ B₁ : Term}
    (hΓ : ⊢ Γ) : ¬Γ ⊢ Term.sort u ≡ Term.sigma A₁ B₁ : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).eq hΓ (Ctx.SubstEq.id hΓ) (Adm.bot hΓ (Ctx.SubstEq.id hΓ))).1 Interp.sort'
  rcases Interp.le_sigma h with hb | ⟨n, d, g, hle⟩
  · exact Shape0.noConfusion hb
  · exact absurd ((TShape.LE.def_mp (Nat.zero_le _) (Nat.le_refl _)) hle)
      id

theorem sort_nat_inv {Γ : List Term} {u s : Bool} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.sort u ≡ Term.nat : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).eq hΓ (Ctx.SubstEq.id hΓ) (Adm.bot hΓ (Ctx.SubstEq.id hΓ))).1 Interp.sort'
  exact absurd ((TShape.LE.def_mp (Nat.zero_le 1) (Nat.le_refl 1)) (Interp.le_nat h))
    id

theorem sort_unit_inv {Γ : List Term} {u s r : Bool} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.sort u ≡ Term.unit r : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).eq hΓ (Ctx.SubstEq.id hΓ) (Adm.bot hΓ (Ctx.SubstEq.id hΓ))).1 Interp.sort'
  exact absurd ((TShape.LE.def_mp (Nat.zero_le 1) (Nat.le_refl 1)) (Interp.le_unit h))
    id

theorem sort_id_inv {Γ : List Term} {u s r : Bool} {A a b : Term} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.sort u ≡ Term.id r A a b : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).eq hΓ (Ctx.SubstEq.id hΓ) (Adm.bot hΓ (Ctx.SubstEq.id hΓ))).1 Interp.sort'
  exact absurd ((TShape.LE.def_mp (Nat.zero_le 1) (Nat.le_refl 1)) (Interp.le_id h))
    id

theorem forallE_nat_inv {Γ : List Term} {s : Bool} {A₀ B₀ : Term} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.forallE A₀ B₀ ≡ Term.nat : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).eq hΓ (Ctx.SubstEq.id hΓ) (Adm.bot hΓ (Ctx.SubstEq.id hΓ))).2 Interp.nat'
  rcases Interp.le_forallE h with hb | ⟨n, d, g, hle⟩
  · nomatch hb
  · exact absurd ((TShape.LE.def_mp (Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_refl _)) hle)
      (by simp only [Shape.lift_self]; exact id)

theorem forallE_unit_inv {Γ : List Term} {s r : Bool} {A₀ B₀ : Term} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.forallE A₀ B₀ ≡ Term.unit r : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).eq hΓ (Ctx.SubstEq.id hΓ) (Adm.bot hΓ (Ctx.SubstEq.id hΓ))).2 Interp.unit'
  rcases Interp.le_forallE h with hb | ⟨n, d, g, hle⟩
  · nomatch hb
  · exact absurd ((TShape.LE.def_mp (Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_refl _)) hle)
      (by simp only [Shape.lift_self]; exact id)

theorem sigma_nat_inv {Γ : List Term} {s : Bool} {A₀ B₀ : Term} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.sigma A₀ B₀ ≡ Term.nat : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).eq hΓ (Ctx.SubstEq.id hΓ) (Adm.bot hΓ (Ctx.SubstEq.id hΓ))).2 Interp.nat'
  rcases Interp.le_sigma h with hb | ⟨n, d, g, hle⟩
  · nomatch hb
  · exact absurd ((TShape.LE.def_mp (Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_refl _)) hle)
      (by simp only [Shape.lift_self]; exact id)

theorem sigma_unit_inv {Γ : List Term} {s r : Bool} {A₀ B₀ : Term} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.sigma A₀ B₀ ≡ Term.unit r : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).eq hΓ (Ctx.SubstEq.id hΓ) (Adm.bot hΓ (Ctx.SubstEq.id hΓ))).2 Interp.unit'
  rcases Interp.le_sigma h with hb | ⟨n, d, g, hle⟩
  · nomatch hb
  · exact absurd ((TShape.LE.def_mp (Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_refl _)) hle)
      (by simp only [Shape.lift_self]; exact id)

theorem nat_unit_inv {Γ : List Term} {s r : Bool} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.nat ≡ Term.unit r : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).eq hΓ (Ctx.SubstEq.id hΓ) (Adm.bot hΓ (Ctx.SubstEq.id hΓ))).1 Interp.nat'
  exact absurd ((TShape.LE.def_mp (Nat.le_refl 1) (Nat.le_refl 1)) (Interp.le_unit h))
    (by simp only [Shape.lift_self]; exact id)

theorem nat_id_inv {Γ : List Term} {s r : Bool} {A a b : Term} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.nat ≡ Term.id r A a b : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).eq hΓ (Ctx.SubstEq.id hΓ) (Adm.bot hΓ (Ctx.SubstEq.id hΓ))).1 Interp.nat'
  exact absurd ((TShape.LE.def_mp (Nat.le_refl 1) (Nat.le_refl 1)) (Interp.le_id h))
    (by simp only [Shape.lift_self]; exact id)

theorem unit_id_inv {Γ : List Term} {s r r' : Bool} {A a b : Term} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ Term.unit r' ≡ Term.id r A a b : .sort s := by
  intro H
  have h := ((IsDefEq.sound hΓ H).eq hΓ (Ctx.SubstEq.id hΓ) (Adm.bot hΓ (Ctx.SubstEq.id hΓ))).1 Interp.unit'
  exact absurd ((TShape.LE.def_mp (Nat.le_refl 1) (Nat.le_refl 1)) (Interp.le_id h))
    (by simp only [Shape.lift_self]; exact id)

/-! The three that need a Π or Σ probe, and so a regularity lemma first. -/

theorem forallE_sigma_inv {Γ : List Term} {s : Bool} {A₀ B₀ A₁ B₁ : Term}
    (hΓ : ⊢ Γ) : ¬Γ ⊢ Term.forallE A₀ B₀ ≡ Term.sigma A₁ B₁ : .sort s := by
  intro H
  have ⟨u, hA₀⟩ := H.forallE_dom
  have ⟨v, hB₀⟩ := H.forallE_cod
  have hprobe : Interp Γ Γ (.forallE A₀ B₀) Subst.id Valuation.nil
      (Shape.T (n := 1) (Shape.piAtom (A₀.subst Subst.id) (B₀.subst Subst.id.lift))) :=
    Interp.piAtom (u := u) (v := v) (by simpa using hA₀) (by simpa using hB₀) hA₀ hB₀
  have h := ((IsDefEq.sound hΓ H).eq hΓ (Ctx.SubstEq.id hΓ) (Adm.bot hΓ (Ctx.SubstEq.id hΓ))).1 hprobe
  rcases Interp.le_sigma h with hb | ⟨n, d, g, hle⟩
  · nomatch hb
  · exact absurd ((TShape.LE.def_mp (Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_refl _)) hle)
      (by simp only [Shape.lift_piAtom, Shape.lift_self]; exact id)

theorem forallE_id_inv {Γ : List Term} {s r : Bool} {A₀ B₀ A a b : Term}
    (hΓ : ⊢ Γ) : ¬Γ ⊢ Term.forallE A₀ B₀ ≡ Term.id r A a b : .sort s := by
  intro H
  have ⟨u, hA₀⟩ := H.forallE_dom
  have ⟨v, hB₀⟩ := H.forallE_cod
  have hprobe : Interp Γ Γ (.forallE A₀ B₀) Subst.id Valuation.nil
      (Shape.T (n := 1) (Shape.piAtom (A₀.subst Subst.id) (B₀.subst Subst.id.lift))) :=
    Interp.piAtom (u := u) (v := v) (by simpa using hA₀) (by simpa using hB₀) hA₀ hB₀
  have h := ((IsDefEq.sound hΓ H).eq hΓ (Ctx.SubstEq.id hΓ) (Adm.bot hΓ (Ctx.SubstEq.id hΓ))).1 hprobe
  exact absurd ((TShape.LE.def_mp (Nat.le_refl 1) (Nat.le_refl 1)) (Interp.le_id h))
    (by simp only [Shape.lift_self]; exact id)

theorem sigma_id_inv {Γ : List Term} {s r : Bool} {A₀ B₀ A a b : Term}
    (hΓ : ⊢ Γ) : ¬Γ ⊢ Term.sigma A₀ B₀ ≡ Term.id r A a b : .sort s := by
  intro H
  have ⟨u, hA₀⟩ := H.sigma_dom
  have ⟨v, hB₀⟩ := H.sigma_cod
  have hprobe : Interp Γ Γ (.sigma A₀ B₀) Subst.id Valuation.nil
      (Shape.T (n := 1) (Shape.sigmaAtom (A₀.subst Subst.id) (B₀.subst Subst.id.lift))) :=
    Interp.sigmaAtom (u := u) (v := v) (by simpa using hA₀) (by simpa using hB₀) hA₀ hB₀
  have h := ((IsDefEq.sound hΓ H).eq hΓ (Ctx.SubstEq.id hΓ) (Adm.bot hΓ (Ctx.SubstEq.id hΓ))).1 hprobe
  exact absurd ((TShape.LE.def_mp (Nat.le_refl 1) (Nat.le_refl 1)) (Interp.le_id h))
    (by simp only [Shape.lift_self]; exact id)

/-! ### The remaining label inversions -/

theorem sigma_inv {Γ : List Term} {A₀ B₀ A₁ B₁ : Term} {s : Bool}
    (hΓ : ⊢ Γ) (H : Γ ⊢ Term.sigma A₀ B₀ ≡ Term.sigma A₁ B₁ : .sort s) :
    ∃ u v, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ A₀ :: Γ ⊢ B₀ ≡ B₁ : .sort v :=
  have ⟨_, hA₀⟩ := H.sigma_dom
  have ⟨_, hB₀⟩ := H.sigma_cod
  SoundEq.sigma_inv hΓ hA₀ hB₀ (IsDefEq.sound hΓ H).eq

theorem id_inv {Γ : List Term} {r : Bool} {A₀ a₀ b₀ A₁ a₁ b₁ : Term}
    (hΓ : ⊢ Γ) (H : Γ ⊢ Term.id r A₀ a₀ b₀ ≡ Term.id r A₁ a₁ b₁ : .sort r) :
    ∃ u, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ Γ ⊢ a₀ ≡ a₁ : A₀ ∧ Γ ⊢ b₀ ≡ b₁ : A₀ :=
  have ⟨⟨_, hA₀⟩, ha₀, hb₀⟩ := H.id_dom
  SoundEq.id_inv hΓ hA₀ ha₀ hb₀ (IsDefEq.sound hΓ H).eq

/-- Two definitionally equal identity types are in the same sort: the
relevance flag is part of the `id`-shape's head, and the order compares
it.  (`id_inv` assumes it; this is where it comes from.) -/
theorem id_rel_inv {Γ : List Term} {r r' s : Bool} {A₀ a₀ b₀ A₁ a₁ b₁ : Term}
    (hΓ : ⊢ Γ) (H : Γ ⊢ Term.id r A₀ a₀ b₀ ≡ Term.id r' A₁ a₁ b₁ : .sort s) : r = r' := by
  have ⟨⟨u, hA₀⟩, ha₀, hb₀⟩ := H.id_dom
  have hw : TShape.WF Γ (Shape.T (n := 1)
      (ShapeS.id r (A₀.subst Subst.id) (a₀.subst Subst.id) (b₀.subst Subst.id))) :=
    Shape.WF.id_of hΓ (Ctx.SubstEq.id hΓ) hA₀ ha₀ hb₀
  have hmove := ((IsDefEq.sound hΓ H).eq hΓ (Ctx.SubstEq.id hΓ) (Adm.bot hΓ (Ctx.SubstEq.id hΓ))).1
    (.id hw (TShape.LE.refl hw) ⟨u, hA₀⟩ ha₀ hb₀)
  cases hmove with
  | id _ hle _ _ _ =>
    obtain ⟨M, _, _, h2⟩ := TShape.LE.at_succ hle
    exact h2.1

/-! ## Non-degeneracy on closed terms

The no-confusion family above separates *types*.  This separates two
closed *terms* of one type, which is what says the equational theory is
not the total relation on well-typed terms.  (`not_UIP` also separates
two terms, but in a non-empty context, so it does not rule out the
theory collapsing on closed terms.) -/

/-- **`zero` and `succ zero` are not definitionally equal.**  The
`succ`-shape approximates `succ zero` at the empty stage; if the two
terms were equal it would approximate `zero`, whose approximants are all
below the `zero`-shape, and a `succ`-shape is not. -/
theorem zero_ne_succ {Γ : List Term} (hΓ : ⊢ Γ) :
    ¬ (Γ ⊢ Term.zero ≡ Term.succ .zero : .nat) := by
  intro h
  have hwz : TShape.WF Γ (Shape.T (n := 1) Shape.zero) := TShape.WF.T.2 trivial
  have hws : TShape.WF Γ (Shape.T (n := 2) (Shape.succ Shape.zero)) := TShape.WF.T.2 trivial
  have hs : Interp Γ Γ (.succ .zero) Subst.id Valuation.nil
      (Shape.T (n := 2) (Shape.succ Shape.zero)) :=
    .succ (.zero hwz (TShape.LE.refl hwz)) hws (TShape.LE.refl hws)
  have hle := Interp.le_zero
    (((IsDefEq.sound hΓ h).eq hΓ (Ctx.SubstEq.id hΓ) (Adm.bot hΓ (Ctx.SubstEq.id hΓ))).2 hs)
  obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ hle
  exact absurd h2 (fun x => x)

/-- The closed instance, which is the one that says the equational theory
is not the total relation. -/
theorem zero_ne_succ_zero : ¬ ([] ⊢ Term.zero ≡ Term.succ .zero : .nat) :=
  zero_ne_succ trivial

/-- **A stuck transport has no information.**  `tr false nat zero (succ
zero) nat zero h` is a transport no rule computes, because its endpoints
are not equal, and the `tr` clause now *asks* for them to be equal at the
stage.  The hypothesis this used to take, that `zero ≢ succ zero`, is
`zero_ne_succ`; before the model could separate two closed terms it had
to be assumed. -/
theorem Interp.tr_stuck_bot {Δ Γ : List Term} {σ ρ m H} (hΔ : ⊢ Δ)
    (h : Interp Δ Γ (.tr false .nat .zero (.succ .zero) .nat .zero H) σ ρ m) :
    m.2 = Shape.bot :=
  Interp.tr_bot_of_ne h (by simpa using zero_ne_succ hΔ)
