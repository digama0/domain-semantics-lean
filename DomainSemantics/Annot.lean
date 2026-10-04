import DomainSemantics.Term

/-! # Well-annotated terms

`Interp`'s clauses carry the typings that make them stage-invariant: a
λ-shape's label is a type, a pair's first component is typed at the
annotation, a `natCase`'s scrutinee is a numeral.  Those are statements
about the term's *context*, and moving an interpretation into a smaller
context (`Interp.unweak`) has to produce them there — which strengthening
a typing cannot do, and which uniqueness of types could do only by
circularity, uniqueness being downstream of all this.

So the strengthening lemmas are indexed by this predicate instead: `t` is
**well-annotated** in `Γ` when every annotation in it is typed in the
context it occurs in.  It is syntax-directed, so it decomposes without
inversion; it holds of any term that occurs in a derivation
(`IsDefEq.annot`), because the judgement is the instrumented one, whose
congruence rules carry their subterms' sort proofs and whose computation
rules carry both sides as typings.

This is the extrinsic stand-in for an intrinsically typed syntax: the
annotations travel with the term, and the lemmas that need them say so.
-/

namespace DomainSemantics

/-- Every annotation of `t` is typed in the context it occurs in: exactly
what `Interp`'s clauses ask for, as a structural predicate. -/
def Term.Annot : Term → List Term → Prop
  | .bvar _, _ => True
  | .sort _, _ => True
  | .unit _, _ => True
  | .star _, _ => True
  | .app f a, Γ => (∃ A₀, Γ ⊢ a : A₀) ∧ f.Annot Γ ∧ a.Annot Γ
  | .lam A b, Γ => (∃ u, Γ ⊢ A : .sort u) ∧ A.Annot Γ ∧ b.Annot (A :: Γ)
  | .forallE A B, Γ =>
    (∃ u, Γ ⊢ A : .sort u) ∧ (∃ v, A :: Γ ⊢ B : .sort v) ∧ A.Annot Γ ∧ B.Annot (A :: Γ)
  | .sigma A B, Γ =>
    (∃ u, Γ ⊢ A : .sort u) ∧ (∃ v, A :: Γ ⊢ B : .sort v) ∧ A.Annot Γ ∧ B.Annot (A :: Γ)
  | .pair A B a b, Γ =>
    (∃ u, Γ ⊢ A : .sort u) ∧ (∃ v, A :: Γ ⊢ B : .sort v) ∧ (Γ ⊢ a : A) ∧
      A.Annot Γ ∧ B.Annot (A :: Γ) ∧ a.Annot Γ ∧ b.Annot Γ
  | .fst p, Γ => p.Annot Γ
  | .snd p, Γ => (∃ A₀, Γ ⊢ Term.fst p : A₀) ∧ p.Annot Γ
  | .nat, _ => True
  | .zero, _ => True
  | .succ n, Γ => n.Annot Γ
  | .natCase C M a b, Γ =>
    (Γ ⊢ M : .nat) ∧ C.Annot (.nat :: Γ) ∧ M.Annot Γ ∧ a.Annot Γ ∧ b.Annot (.nat :: Γ)
  | .Y A b, Γ =>
    (∃ u, Γ ⊢ A : .sort u) ∧ (Γ ⊢ .Y A b : A) ∧ A.Annot Γ ∧ b.Annot (A :: Γ)
  | .id _ A a b, Γ =>
    (∃ u, Γ ⊢ A : .sort u) ∧ (Γ ⊢ a : A) ∧ (Γ ⊢ b : A) ∧
      A.Annot Γ ∧ a.Annot Γ ∧ b.Annot Γ
  | .refl _ a, Γ => a.Annot Γ
  | .tr _ A a b C x h, Γ =>
    (∃ u, Γ ⊢ A : .sort u) ∧ (Γ ⊢ a : A) ∧ (Γ ⊢ b : A) ∧
      A.Annot Γ ∧ a.Annot Γ ∧ b.Annot Γ ∧ C.Annot (A :: Γ) ∧ x.Annot Γ ∧ h.Annot Γ

/-- **Every term in a derivation is well-annotated.**  One case per rule:
a congruence has its subterms' sort proofs as premises (this is what the
instrumented judgement is for), and a computation rule has both of its
sides as typing premises, so the induction hypothesis covers them. -/
theorem IsDefEq.annot {Γ : List Term} {e1 e2 T : Term} (H : Γ ⊢ e1 ≡ e2 : T) :
    e1.Annot Γ ∧ e2.Annot Γ := by
  induction H with
  | bvar | sort | unit | star | nat | zero => exact ⟨trivial, trivial⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | trans' _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | defeqDF _ _ _ ih => exact ih
  | appDF _ _ _ haa' _ _ _ ihf iha =>
    exact ⟨⟨⟨_, haa'.hasType.1⟩, ihf.1, iha.1⟩, ⟨_, haa'.hasType.2⟩, ihf.2, iha.2⟩
  | lamDF hAA' _ _ _ _ ihA _ ihb ihb' _ =>
    exact ⟨⟨⟨_, hAA'.hasType.1⟩, ihA.1, ihb.1⟩, ⟨_, hAA'.hasType.2⟩, ihA.2, ihb'.2⟩
  | forallEDF hAA' hB hB' ihA ihb ihb' =>
    exact ⟨⟨⟨_, hAA'.hasType.1⟩, ⟨_, hB.hasType.1⟩, ihA.1, ihb.1⟩,
      ⟨_, hAA'.hasType.2⟩, ⟨_, hB'.hasType.2⟩, ihA.2, ihb'.2⟩
  | sigmaDF hAA' hB hB' ihA ihb ihb' =>
    exact ⟨⟨⟨_, hAA'.hasType.1⟩, ⟨_, hB.hasType.1⟩, ihA.1, ihb.1⟩,
      ⟨_, hAA'.hasType.2⟩, ⟨_, hB'.hasType.2⟩, ihA.2, ihb'.2⟩
  | pairDF hAA' hB hB' haa' _ _ _ ihA ihB ihB' iha ihb _ _ =>
    refine ⟨⟨⟨_, hAA'.hasType.1⟩, ⟨_, hB.hasType.1⟩, haa'.hasType.1,
      ihA.1, ihB.1, iha.1, ihb.1⟩, ?_⟩
    exact ⟨⟨_, hAA'.hasType.2⟩, ⟨_, hB'.hasType.2⟩, hAA'.defeqDF haa'.hasType.2,
      ihA.2, ihB'.2, iha.2, ihb.2⟩
  | fstDF _ _ _ _ _ ihp => exact ⟨ihp.1, ihp.2⟩
  | @sndDF _ A u B v p p' hA hB hpp' _ _ _ ihp _ =>
    exact ⟨⟨⟨A, IsDefEq.fstDF hA hB hpp'.hasType.1⟩, ihp.1⟩,
      ⟨A, IsDefEq.fstDF hA hB hpp'.hasType.2⟩, ihp.2⟩
  | succDF _ ih => exact ⟨ih.1, ih.2⟩
  | natCaseDF _ hMM' _ _ _ ihC ihM iha ihb _ =>
    exact ⟨⟨hMM'.hasType.1, ihC.1, ihM.1, iha.1, ihb.1⟩,
      hMM'.hasType.2, ihC.2, ihM.2, iha.2, ihb.2⟩
  | YDF hAA' _ _ ihA ihb ihb' =>
    refine ⟨⟨⟨_, hAA'.hasType.1⟩, ?_, ihA.1, ihb.1⟩,
      ⟨_, hAA'.hasType.2⟩, ?_, ihA.2, ihb'.2⟩
    · exact (IsDefEq.YDF hAA' ‹_› ‹_›).hasType.1
    · exact hAA'.defeqDF (IsDefEq.YDF hAA' ‹_› ‹_›).hasType.2
  | idDF hAA' haa' hbb' ihA iha ihb =>
    exact ⟨⟨⟨_, hAA'.hasType.1⟩, haa'.hasType.1, hbb'.hasType.1, ihA.1, iha.1, ihb.1⟩,
      ⟨_, hAA'.hasType.2⟩, hAA'.defeqDF haa'.hasType.2, hAA'.defeqDF hbb'.hasType.2,
      ihA.2, iha.2, ihb.2⟩
  | reflDF _ _ _ _ iha _ => exact ⟨iha.1, iha.2⟩
  | trDF hAA' haa' hbb' _ _ _ _ _ _ ihA iha ihb ihC ihC' ihx ihh _ _ =>
    exact ⟨⟨⟨_, hAA'.hasType.1⟩, haa'.hasType.1, hbb'.hasType.1,
        ihA.1, iha.1, ihb.1, ihC.1, ihx.1, ihh.1⟩,
      ⟨_, hAA'.hasType.2⟩, hAA'.defeqDF haa'.hasType.2, hAA'.defeqDF hbb'.hasType.2,
      ihA.2, iha.2, ihb.2, ihC'.2, ihx.2, ihh.2⟩
  -- the computation rules: both sides are typing premises
  | beta _ _ he' _ _ _ _ _ ihl ihr => exact ⟨ihl.1, ihr.1⟩
  | eta _ _ ih₁ ih₂ => exact ⟨ih₂.1, ih₁.1⟩
  | unit_eta _ ih => exact ⟨trivial, ih.1⟩
  | pair_fst _ _ _ _ _ _ _ iha _ ihl => exact ⟨ihl.1, iha.1⟩
  | pair_snd _ _ _ _ _ _ _ _ ihb ihl => exact ⟨ihl.1, ihb.1⟩
  | fst_snd _ _ ih₁ ih₂ => exact ⟨ih₂.1, ih₁.1⟩
  | natCase_zero _ _ _ _ _ iha _ ihl => exact ⟨ihl.1, iha.1⟩
  | natCase_succ _ _ _ _ _ _ _ _ _ _ ihl ihr => exact ⟨ihl.1, ihr.1⟩
  | Y_unfold _ _ _ _ _ _ ihl ihr => exact ⟨ihl.1, ihr.1⟩
  | tr_refl _ _ _ _ _ _ _ _ ihx ihl => exact ⟨ihl.1, ihx.1⟩
  | proofIrrel _ _ _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.1⟩

/-- Well-annotatedness weakens: the annotations' typings do. -/
theorem Term.Annot.weak' : ∀ {t : Term} {Γ Γ' : List Term} {l : Lift},
    Ctx.Lift' l Γ Γ' → t.Annot Γ → (t.lift' l).Annot Γ' := by
  intro t
  induction t with
  | bvar | sort | unit | star | nat | zero => exact fun _ _ => trivial
  | succ _ ih => exact fun W h => ih W h
  | app _ a ihf iha =>
    rintro Γ Γ' l W ⟨⟨A₀, hat⟩, hAf, hAa⟩
    exact ⟨⟨A₀.lift' l, hat.weak' W⟩, ihf W hAf, iha W hAa⟩
  | fst _ ih | refl _ _ ih => exact fun W h => ih W h
  | snd p ih =>
    rintro Γ Γ' l W ⟨⟨A₀, hft⟩, hAp⟩
    exact ⟨⟨A₀.lift' l, by simpa using hft.weak' W⟩, ih W hAp⟩
  | lam A b ihA ihb =>
    rintro Γ Γ' l W ⟨⟨u, hA⟩, hAA, hAb⟩
    exact ⟨⟨u, hA.weak' W⟩, ihA W hAA, ihb W.cons hAb⟩
  | forallE A B ihA ihB =>
    rintro Γ Γ' l W ⟨⟨u, hA⟩, ⟨v, hB⟩, hAA, hAB⟩
    exact ⟨⟨u, hA.weak' W⟩, ⟨v, hB.weak' W.cons⟩, ihA W hAA, ihB W.cons hAB⟩
  | sigma A B ihA ihB =>
    rintro Γ Γ' l W ⟨⟨u, hA⟩, ⟨v, hB⟩, hAA, hAB⟩
    exact ⟨⟨u, hA.weak' W⟩, ⟨v, hB.weak' W.cons⟩, ihA W hAA, ihB W.cons hAB⟩
  | pair A B a b ihA ihB iha ihb =>
    rintro Γ Γ' l W ⟨⟨u, hA⟩, ⟨v, hB⟩, hat, hAA, hAB, hAa, hAb⟩
    exact ⟨⟨u, hA.weak' W⟩, ⟨v, hB.weak' W.cons⟩, hat.weak' W,
      ihA W hAA, ihB W.cons hAB, iha W hAa, ihb W hAb⟩
  | natCase C M a b ihC ihM iha ihb =>
    rintro Γ Γ' l W ⟨hMt, hAC, hAM, hAa, hAb⟩
    refine ⟨by simpa using hMt.weak' W, ihC ?_ hAC, ihM W hAM, iha W hAa, ihb ?_ hAb⟩
    · exact (by simpa using W.cons (A := Term.nat))
    · exact (by simpa using W.cons (A := Term.nat))
  | Y A b ihA ihb =>
    rintro Γ Γ' l W ⟨⟨u, hA⟩, hYt, hAA, hAb⟩
    exact ⟨⟨u, hA.weak' W⟩, by simpa using hYt.weak' W, ihA W hAA, ihb W.cons hAb⟩
  | id r A a b ihA iha ihb =>
    rintro Γ Γ' l W ⟨⟨u, hA⟩, hat, hbt, hAA, hAa, hAb⟩
    exact ⟨⟨u, hA.weak' W⟩, hat.weak' W, hbt.weak' W, ihA W hAA, iha W hAa, ihb W hAb⟩
  | tr r A a b C X Hp ihA iha ihb ihC ihX ihH =>
    rintro Γ Γ' l W ⟨⟨u, hA⟩, hat, hbt, hAA, hAa, hAb, hAC, hAX, hAH⟩
    exact ⟨⟨u, hA.weak' W⟩, hat.weak' W, hbt.weak' W, ihA W hAA, iha W hAa, ihb W hAb,
      ihC W.cons hAC, ihX W hAX, ihH W hAH⟩
