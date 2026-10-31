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
    (hΓ : ⊢ Γ) (H : Γ ⊢ .forallE A₀ B₀ ≡ .forallE A₁ B₁ : .sort s) :
    ∃ u v, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ A₀ :: Γ ⊢ B₀ ≡ B₁ : .sort v :=
  have ⟨_, hA₀⟩ := H.forallE_dom
  have ⟨_, hB₀⟩ := H.forallE_cod
  SoundEq.forallE_inv hΓ hA₀ hB₀ (H.sound hΓ).eq

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
    (hΓ : ⊢ Γ) (H : Γ ⊢ .sort u ≡ .sort v : V) : u = v :=
  (H.sound hΓ).eq.sort_inv hΓ

/-! ### No confusion

Fifteen statements, one argument: put a non-`⊥` probe on whichever side
has one for free, move it across with soundness at the identity stage and
the `⊥` valuation, and read the head off the order — where two different
heads are `False`.

`sort`, `nat` and `unit` have hypothesis-free probes.  `forallE` needs its
regularity lemma first, to build the label-only atom; that is only used
where neither side is one of the three. -/

theorem sort_forallE_inv {Γ : List Term} {u s : Bool} {A₁ B₁ : Term}
    (hΓ : ⊢ Γ) : ¬Γ ⊢ .sort u ≡ .forallE A₁ B₁ : .sort s := by
  intro H
  have h := ((H.sound hΓ).eq (.bot hΓ (.id hΓ))).1 .sort'
  rcases h.le_forallE with hb | ⟨n, d, g, hle⟩
  · cases hb
  cases hle.def_mp (Nat.zero_le _) (Nat.le_refl _)

theorem sort_sigma_inv {Γ : List Term} {u s : Bool} {A₁ B₁ : Term}
    (hΓ : ⊢ Γ) : ¬Γ ⊢ .sort u ≡ .sigma A₁ B₁ : .sort s := by
  intro H
  have h := ((H.sound hΓ).eq (.bot hΓ (.id hΓ))).1 .sort'
  rcases h.le_sigma with hb | ⟨n, d, g, hle⟩
  · cases hb
  cases hle.def_mp (Nat.zero_le _) (Nat.le_refl _)

theorem sort_nat_inv {Γ : List Term} {u s : Bool} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ .sort u ≡ .nat : .sort s := by
  intro H
  have h := ((H.sound hΓ).eq (.bot hΓ (.id hΓ))).1 .sort'
  cases h.le_nat.def_mp (Nat.zero_le 1) (Nat.le_refl 1)

theorem sort_unit_inv {Γ : List Term} {u s r : Bool} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ .sort u ≡ .unit r : .sort s := by
  intro H
  have h := ((H.sound hΓ).eq (.bot hΓ (.id hΓ))).1 .sort'
  cases h.le_unit.def_mp (Nat.zero_le 1) (Nat.le_refl 1)

theorem sort_id_inv {Γ : List Term} {u s r : Bool} {A a b : Term} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ .sort u ≡ .id r A a b : .sort s := by
  intro H
  have h := ((H.sound hΓ).eq (.bot hΓ (.id hΓ))).1 .sort'
  cases h.le_id.def_mp (Nat.zero_le 1) (Nat.le_refl 1)

theorem forallE_nat_inv {Γ : List Term} {s : Bool} {A₀ B₀ : Term} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ .forallE A₀ B₀ ≡ .nat : .sort s := by
  intro H
  have h := ((H.sound hΓ).eq (.bot hΓ (.id hΓ))).2 .nat'
  rcases h.le_forallE with hb | ⟨n, d, g, hle⟩
  · cases hb
  cases hle.def_mp (Nat.succ_le_succ n.zero_le) (Nat.le_refl _)

theorem forallE_unit_inv {Γ : List Term} {s r : Bool} {A₀ B₀ : Term} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ .forallE A₀ B₀ ≡ .unit r : .sort s := by
  intro H
  have h := ((H.sound hΓ).eq (.bot hΓ (.id hΓ))).2 .unit'
  rcases h.le_forallE with hb | ⟨n, d, g, hle⟩
  · cases hb
  cases hle.def_mp (Nat.succ_le_succ n.zero_le) (Nat.le_refl _)

theorem sigma_nat_inv {Γ : List Term} {s : Bool} {A₀ B₀ : Term} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ .sigma A₀ B₀ ≡ .nat : .sort s := by
  intro H
  have h := ((H.sound hΓ).eq (.bot hΓ (.id hΓ))).2 .nat'
  rcases h.le_sigma with hb | ⟨n, d, g, hle⟩
  · cases hb
  cases hle.def_mp (Nat.succ_le_succ n.zero_le) (Nat.le_refl _)

theorem sigma_unit_inv {Γ : List Term} {s r : Bool} {A₀ B₀ : Term} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ .sigma A₀ B₀ ≡ .unit r : .sort s := by
  intro H
  have h := ((H.sound hΓ).eq (.bot hΓ (.id hΓ))).2 .unit'
  rcases h.le_sigma with hb | ⟨n, d, g, hle⟩
  · cases hb
  cases hle.def_mp (Nat.succ_le_succ n.zero_le) (Nat.le_refl _)

theorem nat_unit_inv {Γ : List Term} {s r : Bool} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ .nat ≡ .unit r : .sort s := by
  intro H
  have h := ((H.sound hΓ).eq (.bot hΓ (.id hΓ))).1 .nat'
  cases h.le_unit.def_mp (Nat.le_refl 1) (Nat.le_refl 1)

theorem nat_id_inv {Γ : List Term} {s r : Bool} {A a b : Term} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ .nat ≡ .id r A a b : .sort s := by
  intro H
  have h := ((H.sound hΓ).eq (.bot hΓ (.id hΓ))).1 .nat'
  cases h.le_id.def_mp (Nat.le_refl 1) (Nat.le_refl 1)

theorem unit_id_inv {Γ : List Term} {s r r' : Bool} {A a b : Term} (hΓ : ⊢ Γ) :
    ¬Γ ⊢ .unit r' ≡ .id r A a b : .sort s := by
  intro H
  have h := ((H.sound hΓ).eq (.bot hΓ (.id hΓ))).1 .unit'
  cases h.le_id.def_mp (Nat.le_refl 1) (Nat.le_refl 1)

/-! The three that need a Π or Σ probe, and so a regularity lemma first. -/

theorem forallE_sigma_inv {Γ : List Term} {s : Bool} {A₀ B₀ A₁ B₁ : Term}
    (hΓ : ⊢ Γ) : ¬Γ ⊢ .forallE A₀ B₀ ≡ .sigma A₁ B₁ : .sort s := by
  intro H
  have ⟨u, hA₀⟩ := H.forallE_dom
  have ⟨v, hB₀⟩ := H.forallE_cod
  have hprobe : Interp Γ Γ (.forallE A₀ B₀) .id .nil
      (Shape.T (n := 1) (.piAtom (A₀.subst .id) (B₀.subst Subst.id.lift))) :=
    .piAtom (u := u) (v := v) (by simpa using hA₀) (by simpa using hB₀) hA₀ hB₀
  have h := ((H.sound hΓ).eq (.bot hΓ (.id hΓ))).1 hprobe
  rcases h.le_sigma with hb | ⟨n, d, g, hle⟩
  · cases hb
  cases hle.def_mp (Nat.succ_le_succ n.zero_le) (Nat.le_refl _)

theorem forallE_id_inv {Γ : List Term} {s r : Bool} {A₀ B₀ A a b : Term}
    (hΓ : ⊢ Γ) : ¬Γ ⊢ .forallE A₀ B₀ ≡ .id r A a b : .sort s := by
  intro H
  have ⟨u, hA₀⟩ := H.forallE_dom
  have ⟨v, hB₀⟩ := H.forallE_cod
  have hprobe : Interp Γ Γ (.forallE A₀ B₀) .id .nil
      (Shape.T (n := 1) (.piAtom (A₀.subst .id) (B₀.subst Subst.id.lift))) :=
    .piAtom (u := u) (v := v) (by simpa using hA₀) (by simpa using hB₀) hA₀ hB₀
  have h := ((H.sound hΓ).eq (.bot hΓ (.id hΓ))).1 hprobe
  cases h.le_id.def_mp (Nat.le_refl 1) (Nat.le_refl 1)

theorem sigma_id_inv {Γ : List Term} {s r : Bool} {A₀ B₀ A a b : Term}
    (hΓ : ⊢ Γ) : ¬Γ ⊢ .sigma A₀ B₀ ≡ .id r A a b : .sort s := by
  intro H
  have ⟨u, hA₀⟩ := H.sigma_dom
  have ⟨v, hB₀⟩ := H.sigma_cod
  have hprobe : Interp Γ Γ (.sigma A₀ B₀) .id .nil
      (Shape.T (n := 1) (.sigmaAtom (A₀.subst .id) (B₀.subst Subst.id.lift))) :=
    .sigmaAtom (u := u) (v := v) (by simpa using hA₀) (by simpa using hB₀) hA₀ hB₀
  have h := ((H.sound hΓ).eq (.bot hΓ (.id hΓ))).1 hprobe
  cases h.le_id.def_mp (Nat.le_refl 1) (Nat.le_refl 1)

/-! ### The remaining label inversions -/

theorem sigma_inv {Γ : List Term} {A₀ B₀ A₁ B₁ : Term} {s : Bool}
    (hΓ : ⊢ Γ) (H : Γ ⊢ .sigma A₀ B₀ ≡ .sigma A₁ B₁ : .sort s) :
    ∃ u v, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ A₀ :: Γ ⊢ B₀ ≡ B₁ : .sort v :=
  have ⟨_, hA₀⟩ := H.sigma_dom
  have ⟨_, hB₀⟩ := H.sigma_cod
  SoundEq.sigma_inv hΓ hA₀ hB₀ (H.sound hΓ).eq

theorem id_inv {Γ : List Term} {r : Bool} {A₀ a₀ b₀ A₁ a₁ b₁ : Term}
    (hΓ : ⊢ Γ) (H : Γ ⊢ .id r A₀ a₀ b₀ ≡ .id r A₁ a₁ b₁ : .sort r) :
    ∃ u, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ Γ ⊢ a₀ ≡ a₁ : A₀ ∧ Γ ⊢ b₀ ≡ b₁ : A₀ :=
  have ⟨⟨_, hA₀⟩, ha₀, hb₀⟩ := H.id_dom
  SoundEq.id_inv hΓ hA₀ ha₀ hb₀ (H.sound hΓ).eq

/-- Two definitionally equal identity types are in the same sort: the
relevance flag is part of the `id`-shape's head, and the order compares
it.  (`id_inv` assumes it; this is where it comes from.) -/
theorem id_rel_inv {Γ : List Term} {r r' s : Bool} {A₀ a₀ b₀ A₁ a₁ b₁ : Term}
    (hΓ : ⊢ Γ) (H : Γ ⊢ .id r A₀ a₀ b₀ ≡ .id r' A₁ a₁ b₁ : .sort s) : r = r' := by
  have ⟨⟨u, hA₀⟩, ha₀, hb₀⟩ := H.id_dom
  have hw : (Shape.T (n := 1) (.id r (A₀.subst .id) (a₀.subst .id) (b₀.subst .id))).WF Γ :=
    .id_of hΓ (.id hΓ) hA₀ ha₀ hb₀
  have hmove := ((H.sound hΓ).eq (.bot hΓ (.id hΓ))).1 (.id (.refl hw) ⟨u, hA₀⟩ ha₀ hb₀)
  cases hmove with | id hle
  obtain ⟨M, _, _, h2⟩ := hle.at_succ
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
    ¬ (Γ ⊢ .zero ≡ .succ .zero : .nat) := by
  intro h
  have hwz : (Shape.T (n := 1) .zero).WF Γ := TShape.WF.T.2 trivial
  have hws : (Shape.T (n := 2) Shape.zero.succ).WF Γ := TShape.WF.T.2 trivial
  have hs : Interp Γ Γ (.succ .zero) .id .nil (Shape.T (n := 2) Shape.zero.succ) :=
    .succ (.zero (.refl hwz)) (.refl hws)
  have hle := (((h.sound hΓ).eq (.bot hΓ (.id hΓ))).2 hs).le_zero
  obtain ⟨M, _, _, h2⟩ := hle.src_succ
  cases h2

/-- The closed instance, which is the one that says the equational theory
is not the total relation. -/
theorem zero_ne_succ_zero : ¬ ([] ⊢ .zero ≡ .succ .zero : .nat) :=
  zero_ne_succ trivial
