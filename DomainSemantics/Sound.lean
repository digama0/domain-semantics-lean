import DomainSemantics.Directed
import DomainSemantics.HasType
import DomainSemantics.Regular

/-! # Admissibility and the soundness statement

`Interp` is the core definition; everything else about it is a lemma.
This file adds the two things that are genuinely *new data* rather than
properties of `Interp` — admissibility of a valuation, and the saturated
form of typing — and then states what soundness says.

The other repo bundles its properties into `RawTermProperties` and
`RawJudgment`, because they are established simultaneously by one
induction over a structure that also carries category-theoretic data.  We
do not need the bundle: directedness, naturality and the substitution
lemma are unconditional facts about `Interp`, so they are lemmas in
`Interp.lean`, and only the two judgment-indexed properties — `SoundEq`
and `SoundTy` — are stated here.

| his | here |
|---|---|
| `SourceAdmissible σ ρ` | `Adm` |
| `HasIdeality Γ t` | `SoundDir`, proved *with* soundness (§4.5) |
| `HasRenaming` + `HasSubstitution` | a lemma: `Interp.subst` |
| reindexing along `σ` (functoriality, free) | a lemma: `Interp.subst` |
| `HasEquality Γ t t'` | `SoundEq` |
| `HasFixedness Γ t A` | `SoundTy` |
| `PiReady Γ A B` | absent; it collapses into directedness |
| `RawJudgment` (6 fields) | `SoundEq` and `SoundTy`, proved together |

Two of his notions have no counterpart because they are artefacts of the
ideal-theoretic setting rather than content: `RawValue = ΩLower` (a value
is a single shape here, and the lower set is `Interp`'s own downward
closure) and the `rank`/`piStage`/`piLimit` fixed point (the level index
does that work). -/

namespace DomainSemantics

/-! ## Substitution and the merges, which need directedness

These are lemmas about `Interp` alone, but every one of them needs two
approximants of a substituted slot to have a common upper bound, so they
sit after `IsDefEq.dir` rather than beside the rest of `Interp`'s theory.
None of them carries a directedness premise: directedness comes from the
stage's typing (`Ctx.SubstEq.dir`), which they carry anyway, for the
strengthening and for knowing where the substitution ends. -/

/-- The merge under a binder, shared by every clause that has one: each
element of the list contributes a valuation whose slot `0` is the
binder's own and whose tail approximates `θ`, and the tails fold to one
valuation that serves them all. -/
theorem Interp.body_merge {Δ Γ₀ Γ' Γ'' : List Term} {A₀ : Term} {α : Type} {b : Term}
    {θ σ ρ} (hΔ : ⊢ Δ)
    (hΓ' : ⊢ Γ') (Wθ : Ctx.SubstEq Γ' θ θ Γ₀) (WΓ : Ctx.Lift' (.skip .refl) Γ' Γ'')
    (W : Ctx.SubstEq Δ σ σ Γ') (hwρ : Valuation.WF Δ Γ' ρ)
    {l : List α} {tm : α → Term} {inp out : α → TShape}
    (hdcons : ∀ e ∈ l, Ctx.SubstEq Δ (σ.cons (tm e)) (σ.cons (tm e)) Γ'')
    (ih : ∀ {e : α}, e ∈ l → ∀ {m₂},
      Interp Δ Γ'' (b.subst θ.lift) (σ.cons (tm e)) (ρ.push (inp e)) m₂ →
      ∃ ρ', Interp Δ (A₀ :: Γ₀) b (θ.lift.comp (σ.cons (tm e))) ρ' m₂ ∧
        Valuation.Approx Δ Γ'' (A₀ :: Γ₀) θ.lift (σ.cons (tm e)) (ρ.push (inp e)) ρ')
    (hbody : ∀ e ∈ l, Interp Δ Γ'' (b.subst θ.lift) (σ.cons (tm e)) (ρ.push (inp e)) (out e)) :
    ∃ ρ', Valuation.Approx Δ Γ' Γ₀ θ σ ρ ρ' ∧
      ∀ e ∈ l, Interp Δ (A₀ :: Γ₀) b ((θ.comp σ).cons (tm e)) (ρ'.push (inp e)) (out e) := by
  -- one valuation per element, by the induction hypothesis
  obtain ⟨ps, hps, hall⟩ := List.exists_pairs (β := Valuation)
    (P := fun e ρ'' => Interp Δ (A₀ :: Γ₀) b ((θ.lift).comp (σ.cons (tm e))) ρ'' (out e) ∧
      Valuation.Approx Δ Γ'' (A₀ :: Γ₀) θ.lift (σ.cons (tm e)) (ρ.push (inp e)) ρ'')
    (fun e he => ih he (hbody e he))
  -- their tails approximate `θ` at the outer stage, and fold to one
  have htail : ∀ ρ'' ∈ ps.map (fun p => Valuation.tail p.2),
      Valuation.Approx Δ Γ' Γ₀ θ σ ρ ρ'' := by
    intro ρ'' hρ''
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hρ''
    exact fun {_ _} hlk =>
      Interp.unweak_slot hΔ hΓ' WΓ ((Wθ.lookup hlk).annot.1)
        (hdcons p.1 (hps ▸ List.mem_map.2 ⟨p, hp, rfl⟩))
        ((hall p hp).2 (.succ hlk))
  obtain ⟨hAj, hles⟩ := Valuation.Approx.foldr hΔ W hwρ hΓ' Wθ htail
  refine ⟨_, hAj, fun e he => ?_⟩
  -- the element's own valuation is below the fold, slot by slot
  obtain ⟨p, hp, rfl⟩ : ∃ p ∈ ps, p.1 = e := by
    have : e ∈ ps.map Prod.fst := hps ▸ he
    obtain ⟨p, hp, hpe⟩ := List.mem_map.1 this
    exact ⟨p, hp, hpe⟩
  have hzero : TShape.LE Δ (p.2 0) (inp p.1) :=
    Interp.le_bvar (Γ := Γ'') (i := 0) (σ := σ.cons (tm p.1)) ((hall p hp).2 .zero)
  refine Interp.mono_val hΔ (fun {_ _} hlk => ?_)
    (Subst.lift_comp_cons (θ := θ) (σ := σ) (e := tm p.1) ▸ (hall p hp).1)
  cases hlk with
  | zero => exact hzero
  | succ hlk => exact hles _ (List.mem_map.2 ⟨p, hp, rfl⟩) hlk

/-- **Saturation carries under a binder.**  The binder's own slot `y` is
kept, and the tail is saturated by the hypothesis — so the valuation
never grows except where the substitution's own argument lives, which is
why this closes instead of cascading.

`hd` is what the binder costs: *somewhere* among the valuations
approximating `θ`, the annotation has an approximant typing `y`.  At a
graph entry that is the clause's own `hdom` transported; at `natCase` and
`Y` it is the scrutinee's — resp. the tower's — `TypedAt`. -/
theorem Subst.Saturates.lift {Δ Γ Γ' : List Term} {A : Term} {u : Bool} {θ σ ρ : _} {e y}
    (hΔ : ⊢ Δ) (hΓ : ⊢ Γ) (hΓ' : ⊢ Γ')
    (Wθ : Ctx.SubstEq Γ' θ θ Γ) (Wσ : Ctx.SubstEq Δ σ σ Γ')
    (hwρ : Valuation.WF Δ Γ' ρ)
    (hcons : Ctx.SubstEq Δ (σ.cons e) (σ.cons e) (A.subst θ :: Γ'))
    (hwy : TShape.WF Δ y) (hAt : Γ ⊢ A : .sort u) (hAty : IsTypeAt Γ A)
    (hd : ∃ ρ_d d, Valuation.Approx Δ Γ' Γ θ σ ρ ρ_d ∧
      Interp Δ Γ A (θ.comp σ) ρ_d d ∧ TShape.Named Δ d y e)
    (hSat : Subst.Saturates Δ Γ Γ' θ σ ρ) :
    Subst.Saturates Δ (A :: Γ) (A.subst θ :: Γ') θ.lift (σ.cons e) (ρ.push y) := by
  intro ρ' hρ'
  obtain ⟨ρ_d, d, hApd, hdI, hyd⟩ := hd
  -- the tail approximates `θ` one context down
  have htail : Valuation.Approx Δ Γ' Γ θ σ ρ (Valuation.tail ρ') := by
    intro i A' hlk
    exact Interp.unweak_slot hΔ hΓ' (.skip .refl) ((Wθ.lookup hlk).annot.1) hcons
      (hρ' (.succ hlk))
  -- saturate the tail together with the annotation's witness
  obtain ⟨hApj, hlj₁, hlj₂⟩ := Valuation.Approx.join hΔ Wσ hwρ hΓ' Wθ htail hApd
  obtain ⟨ρ'', hle, hAp, hAdm⟩ := hSat hApj
  refine ⟨ρ''.push y, fun {_ _} hlk => ?_, fun {_ _} hlk => ?_, ?_⟩
  · cases hlk with
    | zero => exact Interp.le_bvar (i := 0) (ρ := ρ.push y) (hρ' .zero)
    | succ hlk => exact TShape.LE.trans hΔ (hlj₁ hlk) (hle hlk)
  · cases hlk with
    | zero => exact .bvar .zero (TShape.LE.refl hwy)
    | succ hlk =>
      have hAi : Interp Δ Γ' (θ _) (Subst.lift_l Lift.refl.skip (σ.cons e)) ρ (ρ'' _) :=
        hAp hlk
      have := Interp.weak' (Γ' := A.subst θ :: Γ') (ρ' := ρ.push y) hΓ' hAi
        (.skip .refl) (fun _ => rfl)
      simpa using this
  · -- and the extended valuation is admissible, by `Adm.cons`
    have hdI' : Interp Δ Γ A (θ.comp σ) ρ'' d :=
      Interp.mono_val hΔ (fun {_ _} hlk => TShape.LE.trans hΔ (hlj₂ hlk) (hle hlk)) hdI
    have hstage : (θ.lift).comp (σ.cons e) = (θ.comp σ).cons e := by
      funext i; cases i with
      | zero => rfl
      | succ i => exact lift_subst_cons
    rw [hstage]
    have Wcomp : Ctx.SubstEq Δ ((θ.comp σ).cons e) ((θ.comp σ).cons e) (A :: Γ) := by
      refine .cons (Ctx.SubstEq.comp hΔ Wσ Wθ) hAt ?_
      cases hcons with
      | cons _ _ hhd =>
        show Δ ⊢ e ≡ e : A.subst (θ.comp σ)
        rw [← subst_subst]
        exact hhd
    exact Adm.cons hAdm Wcomp hΓ hdI' ⟨hyd, (hAty hAdm hdI').2⟩

/-! ### Weakening the clause conditions

These restrict along a context lift, and what restricts with them is the
*stage*: `Ctx.SubstEq.lift_l` for the substitution and `Adm.unlift` for
the valuation.  Only `natCase` needs them, for the motive it reads one
context deeper. -/

/-- **Substitution in the term, the analytic direction.**  An approximant
of `t[θ]` is an approximant of `t` at the composed stage, under *some*
valuation whose slots approximate the `θ i`.

The clauses' `Γ`-level premises come back from `Term.Annot`, and their
semantic ones — a binder's annotation being a type, an eliminator's label
being the subject's own — from `Term.Pinned`, which is the original's
`HasFixedness` threaded structurally.  The `bvar` case is where the
valuation is built (slot `i` holds the approximant, every other slot
`⊥`), the merges are `Valuation.Approx.foldr` through
`body_merge`/`list_merge` under binders, and `Y` runs on the tower. -/
theorem Interp.to_substTerm {Δ : List Term} (hΔ : ⊢ Δ) :
    ∀ {t : Term} {Γ Γ' : List Term} {θ σ ρ m}, ⊢ Γ → t.Annot Γ → t.Pinned Γ → ⊢ Γ' →
      Ctx.SubstEq Γ' θ θ Γ → Ctx.SubstEq Δ σ σ Γ' →
      Adm Δ Γ' σ ρ → Subst.Saturates Δ Γ Γ' θ σ ρ →
      Interp Δ Γ' (t.subst θ) σ ρ m →
      ∃ ρ', Interp Δ Γ t (θ.comp σ) ρ' m ∧ Valuation.Approx Δ Γ' Γ θ σ ρ ρ' := by
  intro t
  induction t with
  | bvar i =>
    intro Γ Γ' θ σ ρ m _ hAnn _ _ _ _ _ _ H
    obtain ⟨A, hlk⟩ := hAnn
    refine ⟨fun j => if j = i then m else TShape.bot, .bvar hlk ?_,
      fun {j _} _ => ?_⟩
    · simp only [if_pos]; exact TShape.LE.refl H.wf
    · by_cases hj : j = i
      · subst hj; simpa using H
      · simp only [if_neg hj]; exact .bot
  | sort u =>
    intro Γ Γ' θ σ ρ m _ _ _ _ _ _ _ _ H
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | sort hle => exact ⟨Valuation.nil, .sort hle, .nil⟩
  | unit r =>
    intro Γ Γ' θ σ ρ m _ _ _ _ _ _ _ _ H
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | unit hle => exact ⟨Valuation.nil, .unit hle, .nil⟩
  | star r =>
    intro Γ Γ' θ σ ρ m _ _ _ _ _ _ _ _ H
    cases H with | bot => exact ⟨Valuation.nil, .bot, .nil⟩
  | nat =>
    intro Γ Γ' θ σ ρ m _ _ _ _ _ _ _ _ H
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | nat hle => exact ⟨Valuation.nil, .nat hle, .nil⟩
  | zero =>
    intro Γ Γ' θ σ ρ m _ _ _ _ _ _ _ _ H
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | zero hle => exact ⟨Valuation.nil, .zero hle, .nil⟩
  | succ N ih =>
    intro Γ Γ' θ σ ρ m hΓ hAnn hPin hΓ' Wθ Wσ hAdm hSat H
    have hΔ := hAdm.ctx
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | succ hv hle =>
      obtain ⟨ρ', hv', hA⟩ := ih hΓ hAnn hPin hΓ' Wθ Wσ hAdm hSat hv
      exact ⟨ρ', .succ hv' hle, hA⟩
  | app F a ihF iha =>
    intro Γ Γ' θ σ ρ m hΓ hAnn hPin hΓ' Wθ Wσ hAdm hSat H
    obtain ⟨⟨T, hat⟩, hAF, hAa⟩ := hAnn
    obtain ⟨hpin, hPF, hPa⟩ := hPin
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | app hF hx hev hle hty =>
      obtain ⟨ρ₁, hF', hA₁⟩ := ihF hΓ hAF hPF hΓ' Wθ Wσ hAdm hSat hF
      obtain ⟨ρ₂, hx', hA₂⟩ := iha hΓ hAa hPa hΓ' Wθ Wσ hAdm hSat hx
      obtain ⟨hAj, hl₁, hl₂⟩ := Valuation.Approx.join hΔ Wσ hAdm.wf hΓ' Wθ hA₁ hA₂
      obtain ⟨ρ₃, hle₃, hAp₃, hAdm₃⟩ := hSat hAj
      rw [subst_subst] at hev
      have hF₃ := Interp.mono_val hΔ (fun {_ _} hlk => (hl₁ hlk).trans hΔ (hle₃ hlk)) hF'
      refine ⟨ρ₃, .app hF₃
        (Interp.mono_val hΔ (fun {_ _} hlk => (hl₂ hlk).trans hΔ (hle₃ hlk)) hx') hev hle ?_, hAp₃⟩
      exact hpin hAdm₃ hF₃
  | fst p ih =>
    intro Γ Γ' θ σ ρ m hΓ hAnn hPin hΓ' Wθ Wσ hAdm hSat H
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | fst hp hle =>
      obtain ⟨ρ', hp', hA⟩ := ih hΓ hAnn hPin hΓ' Wθ Wσ hAdm hSat hp
      exact ⟨ρ', .fst hp' hle, hA⟩
  | snd p ih =>
    intro Γ Γ' θ σ ρ m hΓ hAnn hPin hΓ' Wθ Wσ hAdm hSat H
    obtain ⟨⟨T, hft⟩, hAp⟩ := hAnn
    obtain ⟨hpin, hPp⟩ := hPin
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | snd hp hev hle hty =>
      obtain ⟨ρ', hp', hA⟩ := ih hΓ hAp hPp hΓ' Wθ Wσ hAdm hSat hp
      obtain ⟨ρ₃, hle₃, hAp₃, hAdm₃⟩ := hSat hA
      simp only [Term.subst, subst_subst] at hev
      have hp₃ := Interp.mono_val hΔ hle₃ hp'
      exact ⟨ρ₃, .snd hp₃ hev hle
        (hpin hAdm₃ hp₃), hAp₃⟩
  | refl r a ih =>
    intro Γ Γ' θ σ ρ m hΓ hAnn hPin hΓ' Wθ Wσ hAdm hSat H
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | refl hle => exact ⟨Valuation.nil, .refl hle, .nil⟩
  | id r A a b ihA iha ihb =>
    intro Γ Γ' θ σ ρ m hΓ hAnn hPin hΓ' Wθ Wσ hAdm hSat H
    obtain ⟨⟨u, hA⟩, hat, hbt, hAA, hAa, hAb⟩ := hAnn
    obtain ⟨hPA, hPa, hPb⟩ := hPin
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | id hle _ _ _ =>
      simp only [subst_subst] at hle
      exact ⟨Valuation.nil, .id hle ⟨u, hA⟩ hat hbt, .nil⟩
  | lam A b ihA ihb =>
    intro Γ Γ' θ σ ρ m hΓ hAnn hPin hΓ' Wθ Wσ hAdm hSat H
    obtain ⟨⟨u, hA⟩, hAA, hAb⟩ := hAnn
    obtain ⟨hAty, hPA, hPb⟩ := hPin
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hA.subst hΓ' Wθ
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | @lam _ _ _ _ n g d _ _ hAint hdty hwf hNV hbody hle _ =>
      simp only [subst_subst] at hwf hle
      -- the entries' label terms are typed at the annotation, so each
      -- extends the stage
      have hcons : ∀ e ∈ g, Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A.subst θ :: Γ') := by
        intro e he
        refine .cons Wσ hAθ ?_
        show Δ ⊢ e.tm ≡ e.tm : (A.subst θ).subst σ
        rw [subst_subst]
        exact (hwf.2.2.1.1 e he).2.1
      -- the source-side `isType`, through the `Γ`-side one
      have hisTypeSrc' : ∀ b, Interp Δ Γ' (A.subst θ) σ ρ b →
          TShape.HasType Δ b TShape.type ∧ TShape.WF Δ b ((A.subst θ).subst σ) := by
        intro b hb
        obtain ⟨ρ_b, hb', hApb⟩ := ihA hΓ hAA hPA hΓ' Wθ Wσ hAdm hSat hb
        obtain ⟨ρ_s, hles, hAps, hAdms⟩ := hSat hApb
        rw [subst_subst]
        exact hAty hAdms (Interp.mono_val hΔ hles hb')
      have hisTypeSrc := fun b hb => (hisTypeSrc' b hb).1
      have hAdmE : ∀ e ∈ g, Adm Δ (A.subst θ :: Γ') (σ.cons e.tm) (ρ.push e.inp.T) :=
        fun e he => Adm.cons hAdm (hcons e he) hΓ' hAint ⟨hNV e he, (hisTypeSrc' _ hAint).2⟩
      have hSatE : ∀ e ∈ g, Subst.Saturates Δ (A :: Γ) (A.subst θ :: Γ')
          θ.lift (σ.cons e.tm) (ρ.push e.inp.T) := by
        intro e he
        obtain ⟨ρ_d, hd', hApd⟩ := ihA hΓ hAA hPA hΓ' Wθ Wσ hAdm hSat hAint
        exact Subst.Saturates.lift hΔ hΓ hΓ' Wθ Wσ hAdm.wf (hcons e he)
          (TShape.WF.T.2 (hwf.2.2.1.1 e he).2.2.1) hA hAty
          ⟨ρ_d, _, hApd, hd', hNV e he⟩ hSat
      obtain ⟨ρ₁, hA', hAp₁⟩ := ihA hΓ hAA hPA hΓ' Wθ Wσ hAdm hSat hAint
      obtain ⟨ρ₂, hAp₂, hbody'⟩ :=
        Interp.body_merge (Γ₀ := Γ) (A₀ := A) (b := b) hΔ hΓ' Wθ (.skip .refl) Wσ hAdm.wf
          (l := g) (tm := fun e => e.tm) (inp := fun e => e.inp.T)
          (out := fun e => e.out.T) hcons
          (fun {e} he {m₂} hb₂ =>
            ihb ⟨hΓ, _, hA⟩ hAb hPb ⟨hΓ', _, hAθ⟩ (Wθ.lift hA hAθ) (hcons e he)
              (hAdmE e he) (hSatE e he)
              hb₂)
          hbody
      obtain ⟨hAj, hl₁, hl₂⟩ := Valuation.Approx.join hΔ Wσ hAdm.wf hΓ' Wθ hAp₁ hAp₂
      refine ⟨_, .lam (Interp.mono_val hΔ hl₁ hA') hdty hwf hNV (fun e he => ?_) hle
        ⟨u, hA⟩, hAj⟩
      exact Interp.mono_val hΔ (fun {_ _} hlk => by
        cases hlk with
        | zero => exact TShape.LE.refl (hwf.2.2.1.1 e he).2.2.1
        | succ hlk => exact hl₂ hlk) (hbody' e he)
  | forallE A B ihA ihB =>
    intro Γ Γ' θ σ ρ m hΓ hAnn hPin hΓ' Wθ Wσ hAdm hSat H
    obtain ⟨⟨u, hA⟩, ⟨v, hB⟩, hAA, hAB⟩ := hAnn
    obtain ⟨hAty, hPA, hPB⟩ := hPin
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hA.subst hΓ' Wθ
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | @forallE _ _ _ _ n g d _ _ hAint hdty hwf hNV hbody hle _ _ =>
      simp only [subst_subst, ← Subst.comp_lift] at hwf hle
      have hcons : ∀ e ∈ g, Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A.subst θ :: Γ') := by
        intro e he
        refine .cons Wσ hAθ ?_
        show Δ ⊢ e.tm ≡ e.tm : (A.subst θ).subst σ
        rw [subst_subst]
        exact (hwf.2.2.2.1.1 e he).2.1
      have hisTypeSrc' : ∀ b, Interp Δ Γ' (A.subst θ) σ ρ b →
          TShape.HasType Δ b TShape.type ∧ TShape.WF Δ b ((A.subst θ).subst σ) := by
        intro b hb
        obtain ⟨ρ_b, hb', hApb⟩ := ihA hΓ hAA hPA hΓ' Wθ Wσ hAdm hSat hb
        obtain ⟨ρ_s, hles, hAps, hAdms⟩ := hSat hApb
        rw [subst_subst]
        exact hAty hAdms (Interp.mono_val hΔ hles hb')
      have hisTypeSrc := fun b hb => (hisTypeSrc' b hb).1
      have hAdmE : ∀ e ∈ g, Adm Δ (A.subst θ :: Γ') (σ.cons e.tm) (ρ.push e.inp.T) :=
        fun e he => Adm.cons hAdm (hcons e he) hΓ' hAint ⟨hNV e he, (hisTypeSrc' _ hAint).2⟩
      have hSatE : ∀ e ∈ g, Subst.Saturates Δ (A :: Γ) (A.subst θ :: Γ')
          θ.lift (σ.cons e.tm) (ρ.push e.inp.T) := by
        intro e he
        obtain ⟨ρ_d, hd', hApd⟩ := ihA hΓ hAA hPA hΓ' Wθ Wσ hAdm hSat hAint
        exact Subst.Saturates.lift hΔ hΓ hΓ' Wθ Wσ hAdm.wf (hcons e he)
          (TShape.WF.T.2 (hwf.2.2.2.1.1 e he).2.2.1) hA hAty
          ⟨ρ_d, _, hApd, hd', hNV e he⟩ hSat
      obtain ⟨ρ₁, hA', hAp₁⟩ := ihA hΓ hAA hPA hΓ' Wθ Wσ hAdm hSat hAint
      obtain ⟨ρ₂, hAp₂, hbody'⟩ :=
        Interp.body_merge (Γ₀ := Γ) (A₀ := A) (b := B) hΔ hΓ' Wθ (.skip .refl) Wσ hAdm.wf
          (l := g) (tm := fun e => e.tm) (inp := fun e => e.inp.T)
          (out := fun e => e.out.T) hcons
          (fun {e} he {m₂} hb₂ =>
            ihB ⟨hΓ, _, hA⟩ hAB hPB ⟨hΓ', _, hAθ⟩ (Wθ.lift hA hAθ) (hcons e he)
              (hAdmE e he) (hSatE e he)
              hb₂)
          hbody
      obtain ⟨hAj, hl₁, hl₂⟩ := Valuation.Approx.join hΔ Wσ hAdm.wf hΓ' Wθ hAp₁ hAp₂
      refine ⟨_, .forallE (Interp.mono_val hΔ hl₁ hA') hdty  hwf hNV
        (fun e he => ?_) hle ⟨u, hA⟩ ⟨v, hB⟩, hAj⟩
      exact Interp.mono_val hΔ (fun {_ _} hlk => by
        cases hlk with
        | zero => exact TShape.LE.refl (hwf.2.2.2.1.1 e he).2.2.1
        | succ hlk => exact hl₂ hlk) (hbody' e he)
  | sigma A B ihA ihB =>
    intro Γ Γ' θ σ ρ m hΓ hAnn hPin hΓ' Wθ Wσ hAdm hSat H
    obtain ⟨⟨u, hA⟩, ⟨v, hB⟩, hAA, hAB⟩ := hAnn
    obtain ⟨hAty, hPA, hPB⟩ := hPin
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hA.subst hΓ' Wθ
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | @sigma _ _ _ _ n g d _ _ hAint hdty hwf hNV hbody hle _ _ =>
      simp only [subst_subst, ← Subst.comp_lift] at hwf hle
      have hcons : ∀ e ∈ g, Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A.subst θ :: Γ') := by
        intro e he
        refine .cons Wσ hAθ ?_
        show Δ ⊢ e.tm ≡ e.tm : (A.subst θ).subst σ
        rw [subst_subst]
        exact (hwf.2.2.2.1.1 e he).2.1
      have hisTypeSrc' : ∀ b, Interp Δ Γ' (A.subst θ) σ ρ b →
          TShape.HasType Δ b TShape.type ∧ TShape.WF Δ b ((A.subst θ).subst σ) := by
        intro b hb
        obtain ⟨ρ_b, hb', hApb⟩ := ihA hΓ hAA hPA hΓ' Wθ Wσ hAdm hSat hb
        obtain ⟨ρ_s, hles, hAps, hAdms⟩ := hSat hApb
        rw [subst_subst]
        exact hAty hAdms (Interp.mono_val hΔ hles hb')
      have hisTypeSrc := fun b hb => (hisTypeSrc' b hb).1
      have hAdmE : ∀ e ∈ g, Adm Δ (A.subst θ :: Γ') (σ.cons e.tm) (ρ.push e.inp.T) :=
        fun e he => Adm.cons hAdm (hcons e he) hΓ' hAint ⟨hNV e he, (hisTypeSrc' _ hAint).2⟩
      have hSatE : ∀ e ∈ g, Subst.Saturates Δ (A :: Γ) (A.subst θ :: Γ')
          θ.lift (σ.cons e.tm) (ρ.push e.inp.T) := by
        intro e he
        obtain ⟨ρ_d, hd', hApd⟩ := ihA hΓ hAA hPA hΓ' Wθ Wσ hAdm hSat hAint
        exact Subst.Saturates.lift hΔ hΓ hΓ' Wθ Wσ hAdm.wf (hcons e he)
          (TShape.WF.T.2 (hwf.2.2.2.1.1 e he).2.2.1) hA hAty
          ⟨ρ_d, _, hApd, hd', hNV e he⟩ hSat
      obtain ⟨ρ₁, hA', hAp₁⟩ := ihA hΓ hAA hPA hΓ' Wθ Wσ hAdm hSat hAint
      obtain ⟨ρ₂, hAp₂, hbody'⟩ :=
        Interp.body_merge (Γ₀ := Γ) (A₀ := A) (b := B) hΔ hΓ' Wθ (.skip .refl) Wσ hAdm.wf
          (l := g) (tm := fun e => e.tm) (inp := fun e => e.inp.T)
          (out := fun e => e.out.T) hcons
          (fun {e} he {m₂} hb₂ =>
            ihB ⟨hΓ, _, hA⟩ hAB hPB ⟨hΓ', _, hAθ⟩ (Wθ.lift hA hAθ) (hcons e he)
              (hAdmE e he) (hSatE e he)
              hb₂)
          hbody
      obtain ⟨hAj, hl₁, hl₂⟩ := Valuation.Approx.join hΔ Wσ hAdm.wf hΓ' Wθ hAp₁ hAp₂
      refine ⟨_, .sigma (Interp.mono_val hΔ hl₁ hA') hdty  hwf hNV
        (fun e he => ?_) hle ⟨u, hA⟩ ⟨v, hB⟩, hAj⟩
      exact Interp.mono_val hΔ (fun {_ _} hlk => by
        cases hlk with
        | zero => exact TShape.LE.refl (hwf.2.2.2.1.1 e he).2.2.1
        | succ hlk => exact hl₂ hlk) (hbody' e he)
  | pair A B a b ihA ihB iha ihb =>
    intro Γ Γ' θ σ ρ m hΓ hAnn hPin hΓ' Wθ Wσ hAdm hSat H
    obtain ⟨⟨u, hA⟩, ⟨v, hB⟩, hat, hAA, hAB, hAa, hAb⟩ := hAnn
    obtain ⟨hAty, hPA, hPB, hPa, hPb⟩ := hPin
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hA.subst hΓ' Wθ
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | @pair _ _ _ _ n x y d c _ _ _ _ hainp hbout hAint hdty hslot hwf hcode hcty
        hle _ _ =>
      simp only [subst_subst] at hwf hle
      have htm : Δ ⊢ (a.subst θ).subst σ ≡ (a.subst θ).subst σ : (A.subst θ).subst σ := by
        rw [subst_subst, subst_subst]
        exact IsDefEq.subst hΔ (Ctx.SubstEq.comp hΔ Wσ Wθ) hat
      have hcons : Ctx.SubstEq Δ (σ.cons ((a.subst θ).subst σ))
          (σ.cons ((a.subst θ).subst σ)) (A.subst θ :: Γ') := .cons Wσ hAθ htm
      have hisTypeSrc' : ∀ b, Interp Δ Γ' (A.subst θ) σ ρ b →
          TShape.HasType Δ b TShape.type ∧ TShape.WF Δ b ((A.subst θ).subst σ) := by
        intro b hb
        obtain ⟨ρ_b, hb', hApb⟩ := ihA hΓ hAA hPA hΓ' Wθ Wσ hAdm hSat hb
        obtain ⟨ρ_s, hles, hAps, hAdms⟩ := hSat hApb
        rw [subst_subst]
        exact hAty hAdms (Interp.mono_val hΔ hles hb')
      have hisTypeSrc := fun b hb => (hisTypeSrc' b hb).1
      have hAdmE : Adm Δ (A.subst θ :: Γ') (σ.cons ((a.subst θ).subst σ)) (ρ.push x.T) :=
        Adm.cons hAdm hcons hΓ' hAint hslot
      have hSatE :
          Subst.Saturates Δ (A :: Γ) (A.subst θ :: Γ') θ.lift
            (σ.cons ((a.subst θ).subst σ)) (ρ.push x.T) := by
        obtain ⟨ρ_d, hd', hApd⟩ := ihA hΓ hAA hPA hΓ' Wθ Wσ hAdm hSat hAint
        exact Subst.Saturates.lift hΔ hΓ hΓ' Wθ Wσ hAdm.wf hcons
          (TShape.WF.T.2 hwf.2.2.2.1) hA hAty ⟨ρ_d, _, hApd, hd', hslot.1⟩ hSat
      obtain ⟨ρ₁, hA', hAp₁⟩ := ihA hΓ hAA hPA hΓ' Wθ Wσ hAdm hSat hAint
      obtain ⟨ρ₂, ha', hAp₂⟩ := iha hΓ hAa hPa hΓ' Wθ Wσ hAdm hSat hainp
      obtain ⟨ρ₃, hb', hAp₃⟩ := ihb hΓ hAb hPb hΓ' Wθ Wσ hAdm hSat hbout
      obtain ⟨ρ₄, hAp₄, hcode'⟩ :=
        Interp.body_merge (Γ₀ := Γ) (A₀ := A) (b := B) hΔ hΓ' Wθ (.skip .refl) Wσ hAdm.wf
          (l := [()]) (tm := fun _ => (a.subst θ).subst σ) (inp := fun _ => x.T)
          (out := fun _ => c) (fun _ _ => hcons)
          (fun {_} _ {m₂} hb₂ =>
            ihB ⟨hΓ, _, hA⟩ hAB hPB ⟨hΓ', _, hAθ⟩ (Wθ.lift hA hAθ) hcons
              hAdmE hSatE
              hb₂)
          (fun _ _ => hcode)
      obtain ⟨hAj₁, hl₁, hl₂⟩ := Valuation.Approx.join hΔ Wσ hAdm.wf hΓ' Wθ hAp₁ hAp₂
      obtain ⟨hAj₂, hl₃, hl₄⟩ := Valuation.Approx.join hΔ Wσ hAdm.wf hΓ' Wθ hAp₃ hAp₄
      obtain ⟨hAj, hl₅, hl₆⟩ := Valuation.Approx.join hΔ Wσ hAdm.wf hΓ' Wθ hAj₁ hAj₂
      refine ⟨_, .pair
        (Interp.mono_val hΔ (fun {_ _} hlk => (hl₂ hlk).trans hΔ (hl₅ hlk)) ha')
        (Interp.mono_val hΔ (fun {_ _} hlk => (hl₃ hlk).trans hΔ (hl₆ hlk)) hb')
        (Interp.mono_val hΔ (fun {_ _} hlk => (hl₁ hlk).trans hΔ (hl₅ hlk)) hA')
        hdty (by simpa only [subst_subst] using hslot)
        hwf ?_ hcty hle ⟨u, hA⟩ hat, hAj⟩
      have hcode'' := hcode' () (by simp)
      rw [subst_subst] at hcode''
      exact Interp.mono_val hΔ (fun {_ _} hlk => by
        cases hlk with
        | zero => exact TShape.LE.refl (TShape.WF.T.2 hwf.2.2.2.1)
        | succ hlk => exact TShape.LE.trans hΔ (hl₄ hlk) (hl₆ hlk)) hcode''
  | natCase C M a b ihC ihM iha ihb =>
    intro Γ Γ' θ σ ρ m hΓ hAnn hPin hΓ' Wθ Wσ hAdm hSat H
    obtain ⟨hMt, hAC, hAM, hAa, hAb⟩ := hAnn
    obtain ⟨hMty, hPC, hPM, hPa, hPb⟩ := hPin
    have hΓN : ⊢ (Term.nat :: Γ) := ⟨hΓ, _, .nat⟩
    have hΓN' : ⊢ (Term.nat :: Γ') := ⟨hΓ', _, .nat⟩
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | natCase_zero hM hz ha _ =>
      rw [subst_subst] at hz
      obtain ⟨ρ₁, hM', hAp₁⟩ := ihM hΓ hAM hPM hΓ' Wθ Wσ hAdm hSat hM
      obtain ⟨ρ₂, ha', hAp₂⟩ := iha hΓ hAa hPa hΓ' Wθ Wσ hAdm hSat ha
      obtain ⟨hAj, hl₁, hl₂⟩ := Valuation.Approx.join hΔ Wσ hAdm.wf hΓ' Wθ hAp₁ hAp₂
      exact ⟨_, .natCase_zero (Interp.mono_val hΔ hl₁ hM') hz
        (Interp.mono_val hΔ hl₂ ha') hMt, hAj⟩
    | @natCase_succ _ _ _ _ _ _ _ _ n v t hM heq hbody _ =>
      rw [subst_subst] at heq
      have hcons : Ctx.SubstEq Δ (σ.cons t) (σ.cons t) (Term.nat :: Γ') :=
        .cons Wσ .nat (heq.succ_regular (.inr rfl))
      -- the slot is the scrutinee's predecessor, hence a numeral: read the
      -- scrutinee's own typing on the `Γ` side, where it is provable
      obtain ⟨ρ_M, hM₀, hApM⟩ := ihM hΓ hAM hPM hΓ' Wθ Wσ hAdm hSat hM
      obtain ⟨ρ_s, hles, hAps, hAdms⟩ := hSat hApM
      have hvnat : TShape.HasType Δ v.T TShape.nat := by
        obtain ⟨c, hc, hty⟩ := hMty hAdms
          (Interp.mono_val hΔ hles hM₀)
        exact (TShape.HasType.isNumeral hΔ (Interp.le_nat hc) hty).pred.hasType
      have hisTypeNat : ∀ b, Interp Δ Γ' Term.nat σ ρ b → TShape.HasType Δ b TShape.type :=
        fun _ hb => TShape.HasType.mono_l hΔ .nat (Interp.le_nat hb)
      have hAdmE : Adm Δ (Term.nat :: Γ') (σ.cons t) (ρ.push v.T) :=
        Adm.cons hAdm hcons hΓ' Interp.nat'
          ⟨.base id hvnat
            (Shape.WF.numeral_mem
              (TShape.HasType.isNumeral hΔ (TShape.LE.refl (a := TShape.nat) trivial) hvnat)
              hvnat.wf.1),
            TyEq.refl .nat⟩
      have hSatE : Subst.Saturates Δ (Term.nat :: Γ) (Term.nat :: Γ')
          θ.lift (σ.cons t) (ρ.push v.T) := by
        refine Subst.Saturates.lift (A := Term.nat) hΔ hΓ hΓ' Wθ Wσ hAdm.wf
          (by simpa using hcons) (TShape.WF.T.2 hM₀.wf)
          .nat IsTypeAt.nat ?_ hSat
        exact ⟨ρ_s, TShape.nat, hAps, Interp.nat',
          .base id hvnat
            (Shape.WF.numeral_mem
              (TShape.HasType.isNumeral hΔ (TShape.LE.refl (a := TShape.nat) trivial) hvnat)
              hvnat.wf.1)⟩
      obtain ⟨ρ₁, hM', hAp₁⟩ := ihM hΓ hAM hPM hΓ' Wθ Wσ hAdm hSat hM
      obtain ⟨ρ₂, hAp₂, hbody'⟩ :=
        Interp.body_merge (Γ₀ := Γ) (A₀ := Term.nat) (b := b) (Γ'' := Term.nat :: Γ')
          hΔ hΓ' Wθ (by simpa using Ctx.Lift'.skip (A := Term.nat) (.refl (Γ := Γ'))) Wσ
          hAdm.wf
          (l := [()]) (tm := fun _ => t) (inp := fun _ => v.T) (out := fun _ => m)
          (fun _ _ => hcons)
          (fun {_} _ {m₂} hb₂ =>
            ihb hΓN hAb hPb hΓN' (by simpa using Wθ.lift (.nat) (.nat)) hcons
              hAdmE hSatE
              hb₂)
          (fun _ _ => hbody)
      obtain ⟨hAj, hl₁, hl₂⟩ := Valuation.Approx.join hΔ Wσ hAdm.wf hΓ' Wθ hAp₁ hAp₂
      refine ⟨_, .natCase_succ (Interp.mono_val hΔ hl₁ hM') heq ?_ hMt, hAj⟩
      exact Interp.mono_val hΔ (fun {_ _} hlk => by
        cases hlk with
        | zero => exact TShape.LE.refl (TShape.WF.T.2 hM₀.wf)
        | succ hlk => exact hl₂ hlk) (hbody' () (by simp))
  | Y A b ihA ihb =>
    intro Γ Γ' θ σ ρ m hΓ hAnn hPin hΓ' Wθ Wσ hAdm hSat H
    obtain ⟨⟨u, hA⟩, hYt, hAA, hAb⟩ := hAnn
    obtain ⟨hAty, hYty, hPA, hPb⟩ := hPin
    -- the tower is not structural in the term, so this case runs on the
    -- derivation, each level's self-premise being the level below
    have key : ∀ {Γ₂ : List Term} {t' σ₂ ρ₂ m}, Interp Δ Γ₂ t' σ₂ ρ₂ m →
        t' = (Term.Y A b).subst θ → ⊢ Γ₂ → Ctx.SubstEq Γ₂ θ θ Γ →
        Ctx.SubstEq Δ σ₂ σ₂ Γ₂ → Adm Δ Γ₂ σ₂ ρ₂ → Subst.Saturates Δ Γ Γ₂ θ σ₂ ρ₂ →
        ∃ ρ', Interp Δ Γ (Term.Y A b) (θ.comp σ₂) ρ' m ∧
          Valuation.Approx Δ Γ₂ Γ θ σ₂ ρ₂ ρ' := by
      intro Γ₂ t' σ₂ ρ₂ m H
      induction H with
      | bot => exact fun _ _ _ _ _ _ => ⟨Valuation.nil, .bot, .nil⟩
      | @Y Γ₂ σ₂ ρ₂ m A₂ b₂ x d hx hAd hdty hslot hbody _ _ ihx _ _ =>
        intro ht' hΓ₂ Wθ₂ Wσ₂ hAdm₂ hSat₂
        cases ht'
        have hAθ : Γ₂ ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hA.subst hΓ₂ Wθ₂
        have hcons : Ctx.SubstEq Δ (σ₂.cons (((Term.Y A b).subst θ).subst σ₂))
            (σ₂.cons (((Term.Y A b).subst θ).subst σ₂)) (A.subst θ :: Γ₂) :=
          .cons Wσ₂ hAθ (IsDefEq.subst hΔ Wσ₂ (IsDefEq.subst hΓ₂ Wθ₂ hYt))
        -- the slot's own hereditary typing is a premise of the clause, so
        -- the extended stage needs only the annotation moved to `Γ`
        obtain ⟨ρ₁, hx', hAp₁⟩ := ihx rfl hΓ₂ Wθ₂ Wσ₂ hAdm₂ hSat₂
        obtain ⟨ρ_d, hd', hApd⟩ := ihA hΓ hAA hPA hΓ₂ Wθ₂ Wσ₂ hAdm₂ hSat₂ hAd
        have hisTypeSrc' : ∀ c, Interp Δ Γ₂ (A.subst θ) σ₂ ρ₂ c →
            TShape.HasType Δ c TShape.type ∧ TShape.WF Δ c ((A.subst θ).subst σ₂) := by
          intro c hc
          obtain ⟨ρ_c, hc', hApc⟩ := ihA hΓ hAA hPA hΓ₂ Wθ₂ Wσ₂ hAdm₂ hSat₂ hc
          obtain ⟨ρ_t, hlet, hApt, hAdmt⟩ := hSat₂ hApc
          rw [subst_subst]
          exact hAty hAdmt (Interp.mono_val hΔ hlet hc')
        have hisTypeSrc := fun c hc => (hisTypeSrc' c hc).1
        have hAdmE : Adm Δ (A.subst θ :: Γ₂)
            (σ₂.cons (((Term.Y A b).subst θ).subst σ₂)) (ρ₂.push x) :=
          Adm.cons hAdm₂ hcons hΓ₂ hAd hslot
        have hSatE : Subst.Saturates Δ (A :: Γ) (A.subst θ :: Γ₂) θ.lift
            (σ₂.cons (((Term.Y A b).subst θ).subst σ₂)) (ρ₂.push x) :=
          Subst.Saturates.lift hΔ hΓ hΓ₂ Wθ₂ Wσ₂ hAdm₂.wf hcons (Shape.WF.forget hslot.1.wf) hA hAty
            ⟨ρ_d, d, hApd, hd', hslot.1⟩ hSat₂
        obtain ⟨ρ₂, hAp₂, hbody'⟩ :=
          Interp.body_merge (Γ₀ := Γ) (A₀ := A) (b := b) hΔ hΓ₂ Wθ₂ (.skip .refl) Wσ₂ hAdm₂.wf
            (l := [()]) (tm := fun _ => ((Term.Y A b).subst θ).subst σ₂)
            (inp := fun _ => x) (out := fun _ => m)
            (fun _ _ => hcons)
            (fun {_} _ {m₂} hb₂ =>
              ihb ⟨hΓ, _, hA⟩ hAb hPb ⟨hΓ₂, _, hAθ⟩ (Wθ₂.lift hA hAθ) hcons
                hAdmE hSatE
                hb₂)
            (fun _ _ => hbody)
        obtain ⟨hAj₀, hl₁, hl₂⟩ := Valuation.Approx.join hΔ Wσ₂ hAdm₂.wf hΓ₂ Wθ₂ hAp₁ hAp₂
        obtain ⟨hAj, hlj, hld⟩ := Valuation.Approx.join hΔ Wσ₂ hAdm₂.wf hΓ₂ Wθ₂ hAj₀ hApd
        refine ⟨_, .Y (Interp.mono_val hΔ (fun {_ _} hlk => (hl₁ hlk).trans hΔ (hlj hlk)) hx') 
          (Interp.mono_val hΔ hld hd') hdty
          (by simpa only [← subst_subst] using hslot) ?_ ⟨u, hA⟩ hYt, hAj⟩
        have hb' := hbody' () (by simp)
        rw [show ((Term.Y A b).subst θ).subst σ₂ = (Term.Y A b).subst (θ.comp σ₂) from
          subst_subst] at hb'
        exact Interp.mono_val hΔ (fun {_ _} hlk => by
          cases hlk with
          | zero => exact TShape.LE.refl (Shape.WF.forget hslot.1.wf)
          | succ hlk => exact (hl₂ hlk).trans hΔ (hlj hlk)) hb'
      | _ => intro ht' _ _ _ _ _; cases ht'
    exact key H rfl hΓ' Wθ Wσ hAdm hSat
  | tr r A a b C X Hp ihA iha ihb ihC ihX ihH =>
    intro Γ Γ' θ σ ρ m hΓ hAnn hPin hΓ' Wθ Wσ hAdm hSat H
    obtain ⟨⟨u, hA⟩, hat, hbt, hht, _, hAA, hAa, hAb, hAC, hAX, hAH⟩ := hAnn
    obtain ⟨hAty, hPA, hPa, hPb, hPC, hPX, hPH⟩ := hPin
    have hAθ : Γ' ⊢ A.subst θ ≡ A.subst θ : Term.sort u := hA.subst hΓ' Wθ
    have hbθ : Δ ⊢ (b.subst θ).subst σ ≡ (b.subst θ).subst σ : (A.subst θ).subst σ :=
      IsDefEq.subst hΔ Wσ (IsDefEq.subst hΓ' Wθ hbt)
    have hcons : Ctx.SubstEq Δ (σ.cons ((b.subst θ).subst σ))
        (σ.cons ((b.subst θ).subst σ)) (A.subst θ :: Γ') := .cons Wσ hAθ hbθ
    cases H with
    | bot => exact ⟨Valuation.nil, .bot, .nil⟩
    | @tr _ _ _ _ v vA m' cb _ _ _ _ _ _ _ hle hX ha hb hAint hslotv hC hcb hslotc
        hH heq _ _ _ =>
      have hm' := hslotc.1.forget
      simp only [subst_subst] at heq
      obtain ⟨ρ₁, hX', hAp₁⟩ := ihX hΓ hAX hPX hΓ' Wθ Wσ hAdm hSat hX
      obtain ⟨ρ₂, ha', hAp₂⟩ := iha hΓ hAa hPa hΓ' Wθ Wσ hAdm hSat ha
      obtain ⟨ρ₃, hb', hAp₃⟩ := ihb hΓ hAb hPb hΓ' Wθ Wσ hAdm hSat hb
      obtain ⟨ρ₄, hA', hAp₄⟩ := ihA hΓ hAA hPA hΓ' Wθ Wσ hAdm hSat hAint
      have hisTypeSrc' : ∀ c, Interp Δ Γ' (A.subst θ) σ ρ c →
          TShape.HasType Δ c TShape.type ∧ TShape.WF Δ c ((A.subst θ).subst σ) := by
        intro c hc
        obtain ⟨ρ_c, hc', hApc⟩ := ihA hΓ hAA hPA hΓ' Wθ Wσ hAdm hSat hc
        obtain ⟨ρ_t, hlet, hApt, hAdmt⟩ := hSat hApc
        rw [subst_subst]
        exact hAty hAdmt (Interp.mono_val hΔ hlet hc')
      have hisTypeSrc := fun c hc => (hisTypeSrc' c hc).1
      have hAdmE : Adm Δ (A.subst θ :: Γ') (σ.cons ((b.subst θ).subst σ)) (ρ.push v) :=
        Adm.cons hAdm hcons hΓ' hAint hslotv
      have hSatE : Subst.Saturates Δ (A :: Γ) (A.subst θ :: Γ') θ.lift
          (σ.cons ((b.subst θ).subst σ)) (ρ.push v) :=
        Subst.Saturates.lift hΔ hΓ hΓ' Wθ Wσ hAdm.wf hcons (Shape.WF.forget hslotv.1.wf) hA hAty
          ⟨ρ₄, _, hAp₄, hA', hslotv.1⟩ hSat
      obtain ⟨ρ₅, hAp₅, hC'⟩ :=
        Interp.body_merge (Γ₀ := Γ) (A₀ := A) (b := C) hΔ hΓ' Wθ (.skip .refl) Wσ hAdm.wf
          (l := [()]) (tm := fun _ => (b.subst θ).subst σ) (inp := fun _ => v)
          (out := fun _ => cb)
          (fun _ _ => hcons)
          (fun {_} _ {m₂} hb₂ =>
            ihC ⟨hΓ, _, hA⟩ hAC hPC ⟨hΓ', _, hAθ⟩ (Wθ.lift hA hAθ) hcons
              hAdmE hSatE
              hb₂)
          (fun _ _ => hC)
      obtain ⟨hAj₁, hl₁, hl₂⟩ := Valuation.Approx.join hΔ Wσ hAdm.wf hΓ' Wθ hAp₁ hAp₂
      obtain ⟨hAj₂, hl₃, hl₄⟩ := Valuation.Approx.join hΔ Wσ hAdm.wf hΓ' Wθ hAp₃ hAp₄
      obtain ⟨hAj₄, hl₇, hl₈⟩ := Valuation.Approx.join hΔ Wσ hAdm.wf hΓ' Wθ hAj₁ hAj₂
      obtain ⟨hAj, hl₉, hl₁₀⟩ := Valuation.Approx.join hΔ Wσ hAdm.wf hΓ' Wθ hAj₄ hAp₅
      have hCb := hC' () (by simp)
      rw [show (b.subst θ).subst σ = b.subst (θ.comp σ) from subst_subst] at hCb
      refine ⟨_, .tr hle
        (Interp.mono_val hΔ (fun {_ _} hlk => (hl₁ hlk).trans hΔ ((hl₇ hlk).trans hΔ (hl₉ hlk))) hX')
        (Interp.mono_val hΔ (fun {_ _} hlk => (hl₂ hlk).trans hΔ ((hl₇ hlk).trans hΔ (hl₉ hlk))) ha')
        (Interp.mono_val hΔ (fun {_ _} hlk => (hl₃ hlk).trans hΔ ((hl₈ hlk).trans hΔ (hl₉ hlk))) hb')
        (Interp.mono_val hΔ (fun {_ _} hlk => (hl₄ hlk).trans hΔ ((hl₈ hlk).trans hΔ (hl₉ hlk))) hA')
        (by simpa only [subst_subst] using hslotv)
        ?_ hcb (by simpa only [subst_subst, Subst.lift_comp_cons] using hslotc)
        (fun hr => by simpa only [subst_subst] using hH hr)
        heq ⟨u, hA⟩ hat hbt, hAj⟩
      exact Interp.mono_val hΔ (fun {_ _} hlk => by
        cases hlk with
        | zero => exact TShape.LE.refl (Shape.WF.forget hslotv.1.wf)
        | succ hlk => exact hl₁₀ hlk) hCb

/-- Substitution in the **term**, in master's `∃ ρ'` form.  A substitution
`θ` from `Γ` into `Γ'` turns an approximant of `t[θ]` into an approximant
of `t` under a valuation whose slots approximate the `θ i`, with the stage
moving from `σ` to `θ.comp σ` — the one place the two kinds of
substitution meet.

The `←` direction needs `Interp.weak'` (the `lam` case gains a valuation
slot) and none of the hypotheses.  The `→` direction merges the valuations
that several subderivations return, one slot at a time.  Master uses its
global `compat_join` there; we read directedness of each in-range `θ i`
off `Ctx.SubstEq.dir`, which is why this lemma sits after `IsDefEq.dir`
and carries no premise of its own for it.  Labels need no stage lemma: `A[θ ∘ σ]` and
`A[θ][σ]` are equal on the nose (`subst_subst`). -/
theorem Interp.substTerm {T : Term} (hΔ : ⊢ Δ) {θ : Subst} (hΓ : ⊢ Γ)
    (ht : Γ ⊢ t : T) (hPin : t.Pinned Γ)
    (hΓ' : ⊢ Γ') (Wθ : Ctx.SubstEq Γ' θ θ Γ)
    (Wσ : Ctx.SubstEq Δ σ σ Γ') (hAdm : Adm Δ Γ' σ ρ)
    (hSat : Subst.Saturates Δ Γ Γ' θ σ ρ)
    :
    Interp Δ Γ' (t.subst θ) σ ρ m ↔
    ∃ ρ', Interp Δ Γ t (θ.comp σ) ρ' m ∧ Valuation.Approx Δ Γ' Γ θ σ ρ ρ' :=
  ⟨Interp.to_substTerm hΔ hΓ ht.annot.1 hPin hΓ' Wθ Wσ hAdm hSat,
    fun ⟨_, h, hs⟩ => Interp.of_substTerm hΔ h hΓ' Wθ rfl hs⟩

/-- The single-substitution form, which is what `beta` uses: `b[a]` at
stage `σ` is `b` at the stage extended by `a[σ]`, under the valuation
extended by an approximant of `a`.  Master's `LE_Interp.inst`. -/
theorem Interp.inst {B : Term} (hΔ : ⊢ Δ) (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A : .sort u) (hat : Γ ⊢ a : A) (hb : A :: Γ ⊢ b : B)
    (hPin : b.Pinned (A :: Γ)) (Wσ : Ctx.SubstEq Δ σ σ Γ) (hAdm : Adm Δ Γ σ ρ)
    (hSat : Subst.Saturates Δ (A :: Γ) Γ (Subst.one a) σ ρ)
    (hρ : Valuation.WF Δ Γ ρ) :
    Interp Δ Γ (b.inst a) σ ρ m ↔
    ∃ x, Interp Δ (A :: Γ) b ((Subst.one a).comp σ) (ρ.push x) m ∧ Interp Δ Γ a σ ρ x :=
  -- at `θ = one a`: slot `0` holds the argument's approximant and slot
  -- `i+1` the valuation's own; the stage types slot `0` and nothing asks
  -- about the rest
  have Wθ : Ctx.SubstEq Γ (Subst.one a) (Subst.one a) (A :: Γ) := by
    refine .cons ?_ hA ?_
    · simpa [Subst.one] using Ctx.SubstEq.id hΓ
    · simpa [Subst.one, subst_id] using hat
  ⟨fun h => by
    obtain ⟨ρ', hb', hs⟩ := Interp.to_substTerm (Γ := A :: Γ) hΔ ⟨hΓ, _, hA⟩ hb.annot.1
      hPin hΓ Wθ Wσ hAdm hSat
      h
    refine ⟨ρ' 0, Interp.mono_val hΔ (fun {_ _} hlk => ?_) hb', hs .zero⟩
    cases hlk with
    | zero => exact TShape.LE.refl (hs .zero).wf
    | succ hlk => exact Interp.le_bvar (Γ := Γ) (σ := σ) (ρ := ρ) (hs (Lookup.succ hlk))
  , fun ⟨x, hb', hx⟩ => Interp.of_substTerm hΔ hb' hΓ Wθ rfl (fun {_ _} hlk => by
    cases hlk with
    | zero => exact hx
    | succ hlk => exact .bvar hlk (TShape.LE.refl (hρ hlk)))⟩

-- Stage invariance under a definitionally equal stage is **not** a lemma
-- about `Interp`: for a raw `t` it is false.  Take `t = .forallE A B` with
-- `A` ill-typed in `Γ` but `A[σ]` typed in `Δ`; the `forallE` rule holds
-- with label `A[σ]`, and nothing relates `A[σ']` to it, because no rule
-- types a label in `Γ` -- `hlab` types it in `Δ`.  So the statement has to
-- be indexed by a typing derivation of `t`, and it lives with soundness as
-- `IsDefEq.stage` (`Sound.lean`).

/-- The stage an instantiation is read at: `(one a).comp σ` is `σ`
extended by `a[σ]`. -/
theorem Subst.one_comp {a : Term} {σ : Subst} :
    (Subst.one a).comp σ = σ.cons (a.subst σ) := by
  rw [Subst.cons_comp, Subst.id_comp]

/-! ## What soundness says

Each is quantified over a **stage**: a context to live in, a typed
substitution into it, and an admissible valuation.  His stage is only the
substitution, because his contexts are well formed by construction and his
substitutions are morphisms; ours has to carry both facts explicitly,
which is the "no quotient, preservation lemmas instead" policy applied to
the presheaf structure. -/

/-- The two terms have the same approximants at every stage: master's
`SoundEq`, his `HasEquality`, and the semantic content of a definitional
equality. -/
def SoundEq (Γ : List Term) (t t' : Term) : Prop :=
  ∀ {{Δ σ ρ}}, Adm Δ Γ σ ρ →
    ∀ {m}, Interp Δ Γ t σ ρ m ↔ Interp Δ Γ t' σ ρ m

/-- **Semantic typing, in its saturating form**: every approximant of `t`
is below an approximant that is *hereditarily* typed at an approximant of
`A`.

This is the original's `HasFixedness` — `rawExtend ⟦A⟧ ⟦t⟧ = ⟦t⟧` — read
through "ideal = set of approximants".  Hereditary typing is not itself
downward closed, and this form is: it is what every slot in the model
needs (`Adm`), and what η reads its typed inputs off (§4.5g). -/
def SoundTy (Γ : List Term) (t A : Term) : Prop :=
  ∀ {{Δ : List Term}} {{σ ρ}}, Adm Δ Γ σ ρ →
    ∀ {m}, Interp Δ Γ t σ ρ m →
      ∃ m' a, Interp Δ Γ t σ ρ m' ∧ TShape.LE Δ m m' ∧
        Interp Δ Γ A σ ρ a ∧ TShape.Slot Δ (A.subst σ) a (t.subst σ) m'

/-- **And so every approximant is typed at an approximant of `A`.**  The
old `SoundTy`'s second field, now derived: typing is lower-closed
(`TShape.HasType.mono_l`), so the saturating witness can be discarded. -/
theorem SoundTy.approx {Γ : List Term} {t A : Term} (h : SoundTy Γ t A) :
    ∀ {{Δ σ ρ}}, Adm Δ Γ σ ρ →
      ∀ {m}, Interp Δ Γ t σ ρ m → ∃ a, Interp Δ Γ A σ ρ a ∧ TShape.HasType Δ m a := by
  intro Δ σ ρ hAdm m hm
  have hΔ := hAdm.ctx
  obtain ⟨_, a, _, hle, ha, hdom, _⟩ := h hAdm hm
  exact ⟨a, ha, TShape.HasType.mono_l hΔ hdom.hasType hle⟩

/-- Every approximant of `t`, read as a code, names `t`: what saturation
at a sort says, and what an atom's top shape gives by downward closure. -/
def CodeAt (Γ : List Term) (t : Term) : Prop :=
  ∀ {{Δ : List Term}} {{σ ρ}}, Adm Δ Γ σ ρ →
    ∀ {m}, Interp Δ Γ t σ ρ m → TShape.WF Δ m (t.subst σ)

/-- At `nat` (and any other filtering code) saturation is just typing:
nothing below such a code binds, so `Named` is `HasType` there, and the
names are read as codes, where they are downward closed. -/
theorem SoundTy.of_typedAt {Γ : List Term} {t A : Term}
    (hnb : ∀ {Δ : List Term} {σ ρ : _} {a : TShape}, Interp Δ Γ A σ ρ a → ¬ a.IsBinder)
    (h : TypedAt Γ t A) (hct : CodeAt Γ t) (hcA : CodeAt Γ A) : SoundTy Γ t A := by
  intro Δ σ ρ hAdm m hm
  obtain ⟨a, ha, hty⟩ := h hAdm hm
  exact ⟨m, a, hm, TShape.LE.refl hty.wf.1, ha, .base (hnb ha) hty (hct hAdm hm),
    hcA hAdm ha⟩

/-- An atom's approximants are below one canonical top shape. -/
theorem CodeAt.of_top {Γ : List Term} {t : Term} {s : TShape}
    (hle : ∀ {Δ Γ' σ ρ m}, Interp Δ Γ' t σ ρ m → TShape.LE Δ m s)
    (hs : ∀ {Δ : List Term} {σ}, ⊢ Δ → Ctx.SubstEq Δ σ σ Γ → TShape.WF Δ s (t.subst σ)) :
    CodeAt Γ t := by
  intro Δ σ ρ hAdm m hm
  exact TShape.WF.mono hAdm.ctx (hle hm) (hs hAdm.ctx hAdm.stage)

theorem CodeAt.nat {Γ : List Term} : CodeAt Γ Term.nat :=
  CodeAt.of_top Interp.le_nat (s := TShape.nat)
    (fun _ _ => show TyEq _ _ _ from TyEq.refl .nat)

theorem CodeAt.sort {Γ : List Term} {r : Bool} : CodeAt Γ (Term.sort r) :=
  CodeAt.of_top Interp.le_sort (s := TShape.sort r)
    (fun _ _ => (TShape.WF.sort_iff (k := 0)).2 (TyEq.refl .sort))

/-- So a term of type `nat` names itself, read as a code. -/
theorem CodeAt.of_nat {Γ : List Term} {t : Term} (h : TypedAt Γ t Term.nat) : CodeAt Γ t := by
  intro Δ σ ρ hAdm m hm
  have hΔ := hAdm.ctx
  obtain ⟨c, hc, hty⟩ := h hAdm hm
  exact Shape.WF.numeral_mem (TShape.HasType.isNumeral hΔ (Interp.le_nat hc) hty)
    (TShape.HasType.wf hty).1

/-- `nat`'s approximants are `⊥` or `nat`. -/
theorem SoundTy.nat {Γ : List Term} {t : Term} (h : TypedAt Γ t Term.nat) :
    SoundTy Γ t Term.nat :=
  SoundTy.of_typedAt (fun ha => TShape.not_binder_of_le (Interp.le_nat ha) id) h
    (CodeAt.of_nat h) CodeAt.nat

/-- At a sort the code only filters. -/
theorem SoundTy.of_sort {Γ : List Term} {t : Term} {r : Bool} (h : TypedAt Γ t (.sort r))
    (hct : CodeAt Γ t) : SoundTy Γ t (.sort r) :=
  SoundTy.of_typedAt (fun ha => TShape.not_binder_of_le (Interp.le_sort ha) id) h
    hct CodeAt.sort

theorem SoundTy.codeAt {Γ : List Term} {T : Term} {u : Bool} (h : SoundTy Γ T (.sort u)) :
    CodeAt Γ T := by
  intro Δ σ ρ hAdm m hm
  have hΔ := hAdm.ctx
  obtain ⟨m', _, hm', hle, _, hNV, _⟩ := h hAdm hm
  exact TShape.WF.mono hΔ hle hNV.wf

/-- Saturation transports along an equality of terms, both sides being
the same set of approximants; the slot carries its own code, so moving
the name along the equation takes nothing extra (`Slot.defeq`). -/
theorem SoundTy.of_eq {Γ : List Term} {t t' A : Term} (hs : Γ ⊢ t ≡ t' : A)
    (he : SoundEq Γ t t') (h : SoundTy Γ t A) : SoundTy Γ t' A := by
  intro Δ σ ρ hAdm m hm
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  obtain ⟨m', c, hm', hle, hc, hslot⟩ := h hAdm ((he hAdm).2 hm)
  exact ⟨m', c, (he hAdm).1 hm', hle, hc, hslot.defeq hΔ (hs.subst hΔ W)⟩

/-- And along an equality of *types*, which is what `defeqDF` moves. -/
theorem SoundTy.of_tyEq {Γ : List Term} {t A B : Term} {u : Bool} (hs : Γ ⊢ A ≡ B : .sort u)
    (hAB : SoundEq Γ A B) (h : SoundTy Γ t A) : SoundTy Γ t B := by
  intro Δ σ ρ hAdm m hm
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  obtain ⟨m', c, hm', hle, hc, hslot⟩ := h hAdm hm
  exact ⟨m', c, hm', hle, (hAB hAdm).1 hc,
    hslot.conv (TyEq.symm ⟨u, hs.subst hΔ W⟩)⟩

/-- **A variable's slot is hereditarily typed and names the variable** —
that is what `Adm` says, and it is the base case of saturation. -/
theorem SoundTy.bvar {Γ : List Term} {i : Nat} {A : Term} (hl : Lookup Γ i A) :
    SoundTy Γ (.bvar i) A := by
  intro Δ σ ρ hAdm m hm
  obtain ⟨a, ha, hn, hac⟩ := hAdm.lookupCanon hl
  exact ⟨ρ i, a, .bvar hl (TShape.LE.refl (hAdm.wf hl)),
    Interp.le_bvar hm, ha, hn, hac⟩

theorem SoundEq.refl {Γ : List Term} {t : Term} : SoundEq Γ t t :=
  fun _ _ _ _ _ => Iff.rfl

theorem SoundEq.symm {Γ : List Term} {t t' : Term} (h : SoundEq Γ t t') : SoundEq Γ t' t :=
  fun _ _ _ hA => (h hA).symm

theorem SoundEq.trans {Γ : List Term} {t t' t'' : Term}
    (h : SoundEq Γ t t') (h' : SoundEq Γ t' t'') : SoundEq Γ t t'' :=
  fun _ _ _ hA => (h hA).trans (h' hA)

-- There is no `Adm.subst`.  Moving a judgment to a later stage is only
-- ever needed inside directedness, whose hypothesis is `Valuation.WF`, and
-- that moves by `TShape.WF.subst` slotwise (`Valuation.WF.subst`).  The
-- other repo needs `SourceAdmissible.pullback` because its admissibility
-- carries the decoder fixed-point condition on every slot.

/-! ## Terms with no rule but `bot`

`star` is interpreted by `⊥` and nothing else — that is what makes
`unit_eta` sound — so soundness is automatic for any congruence relating
two such terms, and these three facts are all it takes. -/

/-- Soundness for a congruence between two terms that only `⊥` approximates. -/
theorem sound_of_bot {Γ : List Term} {t t' A : Term}
    (h : ∀ {Δ Γ' σ ρ m}, Interp Δ Γ' t σ ρ m → m.2 = Shape.bot)
    (h' : ∀ {Δ Γ' σ ρ m}, Interp Δ Γ' t' σ ρ m → m.2 = Shape.bot) :
    SoundEq Γ t t' ∧ TypedAt Γ t A :=
  ⟨fun _ _ _ _ _ =>
      ⟨fun hm => Interp.of_bot (h hm), fun hm => Interp.of_bot (h' hm)⟩,
    fun _ _ _ _ _ hm =>
      ⟨TShape.bot, Interp.of_bot rfl, TShape.HasType.bot_bot (h hm)⟩⟩

/-! ## Proof irrelevance

Everything typed at a proposition collapses to `⊥`, which is what makes
the `proofIrrel` rule sound: the two proofs have the same approximants
because both have only `⊥`.

The proof is `TShape.HasType.proofIrrel`, applied directly: with typing
over `TShape` there is nothing to normalise, since both `mono_r` and the
order are level-free. -/

theorem Interp.eq_bot_of_prop {Γ : List Term} {p t : Term}
    (hp : SoundTy Γ p .prop) (ht : SoundTy Γ t p)
    {Δ : List Term} {σ ρ} (hAdm : Adm Δ Γ σ ρ) {m} (H : Interp Δ Γ t σ ρ m) : m.2 = Shape.bot := by
  have hΔ := hAdm.ctx
  obtain ⟨a, ha, hty⟩ := ht.approx hAdm H
  obtain ⟨b, hb, htya⟩ := hp.approx hAdm ha
  rcases TShape.le_prop_cases (Interp.le_sort hb) with hbb | hbb
  · -- the type's type is `⊥`, so everything below it collapses outright
    exact TShape.HasType.bot_r hΔ (TShape.HasType.bot_r hΔ hbb htya) hty
  · -- the type is a proposition, so its inhabitants are `⊥`
    exact TShape.HasType.proofIrrel hΔ hty (htya.sort_level hbb (k' := 0))

/-- **A unit type is inhabited only by `⊥`.**  The `bot` clause is the only
one whose type can be a `unit` shape; `mono_r` first moves the type up to
the canonical one, which is where `cases` can see that. -/
theorem TShape.HasType.unit_r {Δ : List Term} (hΔ : ⊢ Δ) {m a : TShape} {r : Bool}
    (ha : TShape.LE Δ a (TShape.unit r)) (h : TShape.HasType Δ m a) :
    m.2 = Shape.bot := by
  cases TShape.HasType.mono_r hΔ h (TShape.unit r) ha (.unit (Bool.le_true' r)) with
  | bot _ => rfl
  | refl hc _ =>
    obtain ⟨M, _, _, h2⟩ := TShape.LE.at_succ hc
    exact absurd h2 (fun x => x)

/-- Everything typed at the unit type collapses, which is what makes
`unit_eta` sound: both sides have only `⊥`. -/
theorem Interp.eq_bot_of_unit {Γ : List Term} {e : Term} {r : Bool}
    (ht : SoundTy Γ e (.unit r))
    {Δ : List Term} {σ ρ} (hAdm : Adm Δ Γ σ ρ) {m} (H : Interp Δ Γ e σ ρ m) : m.2 = Shape.bot :=
  have ⟨_, ha, hty⟩ := ht.approx hAdm H
  TShape.HasType.unit_r hAdm.ctx (Interp.le_unit ha) hty

/-- Soundness for a congruence whose two sides both collapse to `⊥` at
every stage.  `sound_of_bot`, with the collapse allowed to depend on the
stage — which is what proof irrelevance needs, since the collapse is a
consequence of typing rather than of the term's shape. -/
theorem sound_of_bot_at {Γ : List Term} {t t' A : Term}
    (hty : TypedAt Γ t A)
    (h : ∀ {Δ : List Term} {σ ρ}, Adm Δ Γ σ ρ →
      ∀ {m}, Interp Δ Γ t σ ρ m → m.2 = Shape.bot)
    (h' : ∀ {Δ : List Term} {σ ρ}, Adm Δ Γ σ ρ →
      ∀ {m}, Interp Δ Γ t' σ ρ m → m.2 = Shape.bot) :
    SoundEq Γ t t' ∧ TypedAt Γ t A :=
  ⟨fun _ _ _ hA _ =>
      ⟨fun hm => Interp.of_bot (h hA hm), fun hm => Interp.of_bot (h' hA hm)⟩, hty⟩

/-- When every approximant is `⊥` there is nothing to saturate: `⊥` is
hereditarily typed at `⊥`, which approximates every type. -/
theorem SoundTy.of_bot {Γ : List Term} {t A : Term}
    (h : ∀ {Δ : List Term} {σ ρ}, Adm Δ Γ σ ρ →
      ∀ {m}, Interp Δ Γ t σ ρ m → m.2 = Shape.bot) :
    SoundTy Γ t A := by
  intro Δ σ ρ hAdm m hm
  obtain ⟨n, s'⟩ := m
  have hb : s' = Shape.bot := h hAdm hm
  subst hb
  exact ⟨_, TShape.bot, hm, TShape.LE.refl hm.wf, .bot, (TShape.Named.bot (n := n) (.bot (.bot .sort))), TShape.WF.bot⟩

/-! ## Atoms

`sort`, `unit`, `nat` and `zero` are interpreted by the shapes below one
fixed shape, so both conclusions come from three facts about that shape
and its type: everything is below it, the type has a canonical
interpretation, and the shape is typed at it.  No case analysis on the
approximant is needed — `mono_l` brings the canonical typing down to it. -/

theorem sound_atom {Γ : List Term} {t A : Term} {s a : TShape}
    (hle : ∀ {Δ Γ' σ ρ m}, Interp Δ Γ' t σ ρ m → TShape.LE Δ m s)
    (ha : ∀ {Δ Γ' σ ρ}, Interp Δ Γ' A σ ρ a)
    (hsa : ∀ {Δ : List Term}, TShape.HasType Δ s a) :
    SoundEq Γ t t ∧ TypedAt Γ t A :=
  ⟨fun _ _ _ _ _ => Iff.rfl,
    fun _ _ _ hAdm _ hm =>
      ⟨a, ha, TShape.HasType.mono_l hAdm.ctx hsa (hle hm)⟩⟩

/-- `SoundTy` at a sort, as a typing of the approximant *itself*.

`SoundTy` only says that an approximant is *below* a typed shape, and the
step that brings the typing back down is `mono_l` -- so this is exactly
the lemma that was out of reach before types became lower sets.  `mono_r`
first moves the type from whatever approximates the sort up to the sort
itself, along `Interp.le_sort`. -/
theorem SoundTy.hasType {Γ : List Term} {A : Term} {u : Bool} (h : SoundTy Γ A (.sort u))
    {Δ : List Term} {σ ρ} (hAdm : Adm Δ Γ σ ρ)
    {b : TShape} (hb : Interp Δ Γ A σ ρ b) : TShape.HasType Δ b (TShape.sort u) := by
  have hΔ := hAdm.ctx
  have ⟨a, ha, hty⟩ := h.approx hAdm hb
  exact TShape.HasType.mono_r hΔ hty _ (Interp.le_sort ha) .sort

/-- `SoundTy` at a sort, as the `Adm.cons` field wants it: every
approximant of `A` is a *type*.  `cumul` moves the sort up to `.type`. -/
theorem SoundTy.isType {Γ : List Term} {A : Term} {u : Bool} (h : SoundTy Γ A (.sort u))
    {Δ : List Term} {σ ρ} (hAdm : Adm Δ Γ σ ρ)
    {b : TShape} (hb : Interp Δ Γ A σ ρ b) : TShape.HasType Δ b TShape.type :=
  (h.hasType hAdm hb).cumul rfl (Bool.le_true' u)

/-- `SoundTy`'s two halves as the predicates `Interp.lean` states them:
`Term.Pinned`'s conditions are these, at the subterm they belong to. -/
theorem SoundTy.typedAt {Γ : List Term} {t A : Term} (h : SoundTy Γ t A) :
    TypedAt Γ t A := by
  intro _ _ _ hAdm _ hm; exact h.approx hAdm hm

theorem SoundTy.isTypeAt {Γ : List Term} {A : Term} {u : Bool}
    (h : SoundTy Γ A (.sort u)) : IsTypeAt Γ A := by
  intro _ _ _ hAdm _ hb; exact ⟨h.isType hAdm hb, h.codeAt hAdm hb⟩

/-! ### The canonical valuation at a single substitution

`Interp.to_substTerm` returns *some* valuation approximating `θ`, and
`SoundTy` is read at admissible ones — so to use a subterm's `SoundTy`
after a substitution one needs the returned valuation to be admissible,
which it need not be (admissibility is not upward closed, §3.1d).

At a **single** substitution it is, and the valuation is canonical: the
source valuation with the argument's approximant pushed on.  This is the
depth-0 case of the original's `SingleSubstitution`, and it is the level
`Interp.inst` itself works at. -/

/-- The valuation `to_substTerm` returns at `Subst.one a` is below the
canonical `ρ.push (ρ' 0)`, which approximates `one a` and is admissible.
No join is needed and nothing grows: slot `0` is already an approximant
of `a`, so `SoundTy a A` types it, and the type `A` lives *below* the
substituted variable, so its own approximant does not move. -/
theorem Valuation.Approx.canon_one {Γ Δ : List Term} {A a : Term} {u : Bool} {σ ρ ρ'}
    (hΓ : ⊢ Γ) (hAdm : Adm Δ Γ σ ρ)
    (hAt : Γ ⊢ A : .sort u) (hat : Γ ⊢ a : A) (hadom : SoundTy Γ a A)
    (hρ' : Valuation.Approx Δ Γ (A :: Γ) (Subst.one a) σ ρ ρ') :
    ∃ x, Valuation.LE Δ (A :: Γ) ρ' (ρ.push x) ∧
      Valuation.Approx Δ Γ (A :: Γ) (Subst.one a) σ ρ (ρ.push x) ∧
      Adm Δ (A :: Γ) ((Subst.one a).comp σ) (ρ.push x) := by
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have hwρ : Valuation.WF Δ Γ ρ := hAdm.wf
  -- the slot is the argument's approximant, enlarged until it is
  -- hereditarily typed — which is all the extended stage asks of it
  obtain ⟨x, α, hx, hlex, hα, hNV, hαc⟩ := hadom hAdm (hρ' .zero)
  refine ⟨x, fun {_ _} hlk => ?_, fun {_ _} hlk => ?_, ?_⟩
  · cases hlk with
    | zero => exact hlex
    | succ hlk => exact Interp.le_bvar (Γ := Γ) (σ := σ) (ρ := ρ) (hρ' (Lookup.succ hlk))
  · cases hlk with
    | zero => exact hx
    | succ hlk => exact .bvar hlk (TShape.LE.refl (hwρ hlk))
  · rw [Subst.one_comp]
    exact Adm.cons hAdm (.cons W hAt (hat.subst hΔ W)) hΓ hα ⟨hNV, hαc⟩

/-- `canon_one` packaged as `Subst.Saturates`: a single substitution
saturates, which is the hypothesis `Interp.to_substTerm` reads its
clause conditions under. -/
theorem Subst.Saturates.one {Γ Δ : List Term} {A a : Term} {u : Bool} {σ ρ}
    (hΓ : ⊢ Γ) (hAdm : Adm Δ Γ σ ρ)
    (hAt : Γ ⊢ A : .sort u) (hat : Γ ⊢ a : A) (hadom : SoundTy Γ a A) :
    Subst.Saturates Δ (A :: Γ) Γ (Subst.one a) σ ρ := fun _ hρ' =>
  match Valuation.Approx.canon_one hΓ hAdm hAt hat hadom hρ' with
  | ⟨_, h1, h2, h3⟩ => ⟨_, h1, h2, h3⟩

theorem sound_forallE_typedAt {Γ : List Term} {A B : Term} {u v : Bool} (ihAd : SoundTy Γ A (.sort u))
    (ihB : SoundTy (A :: Γ) B (.sort v))
    (hAty : Γ ⊢ A : .sort u) :
    TypedAt Γ (.forallE A B) (.sort v) := by
  intro Δ σ ρ hAdm m hm
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  cases hm with
  | bot =>
    exact ⟨TShape.sort v, Interp.sort', .bot .sort⟩
  | forallE hA hd hwf hNV hbody hle =>
    refine ⟨TShape.sort v, Interp.sort', TShape.HasType.mono_l hΔ ?_ hle⟩
    -- the domain half is now the constructor's own premise; only the
    -- codomain runs an induction hypothesis
    refine .forallE hd (fun e he => ?_) hwf
    -- the codomain, at the stage extended by the entry's label: the
    -- entry's own data is exactly what `Adm.cons` and `SubstEq.cons` ask for
    have hwe := hwf.2.2.2.1.1 e he
    have W' : Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A :: Γ) :=
      .cons W hAty hwe.2.1
    have hAdm' : Adm Δ (A :: Γ) (σ.cons e.tm) (ρ.push (Shape.T e.inp)) :=
      .cons hAdm W' W.wf hA
        ⟨hNV e he, ihAd.codeAt hAdm hA⟩
    exact ihB.hasType hAdm' (hbody e he)

/-- One direction of the `SoundEq` half of `forallEDF`.

A Π-shape carries the *syntax* `(A[σ], B[σ.lift])` as its label, so the
two sides of the congruence do not produce the same shapes on the nose --
`⟦∀ A B⟧` is built over one label and `⟦∀ A' B'⟧` over another.  What
saves the statement is that `Shape.LE` compares labels up to definitional
equality: the two Π-shapes are `≈`-equivalent, and an approximant of one
is an approximant of the other by `LE.trans` alone.  Everything else in
the constructor -- the domain shape, the graph, the `HasDom` premises --
is reused verbatim.

The context of the body's interpretation changes from `A :: Γ` to
`A' :: Γ`, and that is free: `Interp` never looks at its context index
(`Interp.ctx`).  It is the *stage* that carries the content, and the
stage is untouched. -/
theorem sound_forallE_eq_of {Γ : List Term} {A A' B B' : Term} {u v : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (hBB' : A :: Γ ⊢ B ≡ B' : .sort v)
    (ihA : SoundEq Γ A A') (ihAtyD : SoundTy Γ A (.sort u))
    (ihB : SoundEq (A :: Γ) B B')
    {Δ : List Term} {σ ρ} (hAdm : Adm Δ Γ σ ρ)
    {m : TShape} (H : Interp Δ Γ (.forallE A B) σ ρ m) :
    Interp Δ Γ (.forallE A' B') σ ρ m := by
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have ⟨⟨_, hAσ⟩, _, hBσ⟩ :
      PiLabelEq Δ (A.subst σ) (B.subst σ.lift) (A'.subst σ) (B'.subst σ.lift) :=
    PiLabelEq.subst hΔ W ⟨⟨u, hAA'⟩, v, hBB'⟩
  have hΓA' : ⊢ (A' :: Γ) := ⟨W.wf, _, hAA'.hasType.2⟩
  cases H with
  | bot => exact .bot
  | forallE hA hd hwf hNV hbody hle hAt hBt
  refine .forallE ((ihA hAdm).1 hA) hd
    ⟨⟨_, hAσ.hasType.2⟩, ⟨_, (hAσ.defeqDF_l hΔ hBσ).hasType.2⟩,
      Shape.WF.conv hwf.2.2.1 ⟨_, hAσ.symm⟩,
      ShapeFun.WF.name ((ShapeFun.WF.forget hwf.2.2.2.1).retype ⟨_, hAσ⟩)
        (fun e he => (ShapeFun.WF.canon hwf.2.2.2.1 e he).conv
          ⟨_, (hAσ.hasType.2).instDF hΔ .sort (hAσ.defeqDF_l hΔ hBσ).symm
            (hAσ.defeqDF ((hwf.2.2.2.1.1 e he).2.1))⟩), trivial⟩
    hNV (fun e he => ?_) 
    (hle.trans hΔ (TShape.LE.T.2
      ⟨⟨⟨_, hAσ⟩, _, hBσ⟩, .refl (Shape.WF.forget hwf.2.2.1),
        .refl (ShapeFun.WF.forget hwf.2.2.2.1),
        hwf.2.2.1, ShapeFun.WF.canon hwf.2.2.2.1⟩))
    ⟨u, hAA'.hasType.2⟩ ⟨v, IsDefEq.ctx_id hΓA' (Ctx.SubstEq.defeqHead W.wf hAA')
      hBB'.hasType.2⟩
  · -- the body, at the stage extended by the entry's label
    have hwe := hwf.2.2.2.1.1 e he
    have W' : Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A :: Γ) :=
      .cons W hAA'.hasType.1 hwe.2.1
    have hAdm' : Adm Δ (A :: Γ) (σ.cons e.tm) (ρ.push (Shape.T e.inp)) :=
      .cons hAdm W' W.wf hA
        ⟨hNV e he, ihAtyD.codeAt hAdm hA⟩
    exact Interp.ctx ((ihB hAdm').1 (hbody e he)) hΓA'
      (Ctx.SubstEq.defeqHead W.wf hAA') Lookup.cons_head

/-- The `SoundEq` half of `forallEDF`: the two Π-types have the same
approximants at every stage.

Both directions are the same argument, run on the mirrored data -- which
is exactly why the rule carries its codomain premise twice, once over
each domain.  Without the `A' :: Γ` copy the backward direction would
have no induction hypothesis to run. -/
theorem sound_forallE_eq {Γ : List Term} {A A' B B' : Term} {u v : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u)
    (hB : A :: Γ ⊢ B ≡ B' : .sort v) (hB' : A' :: Γ ⊢ B ≡ B' : .sort v)
    (ihA : SoundEq Γ A A') (ihAtyD : SoundTy Γ A (.sort u))
    (ihB : SoundEq (A :: Γ) B B') (ihB' : SoundEq (A' :: Γ) B B') :
    SoundEq Γ (.forallE A B) (.forallE A' B') := by
  intro Δ σ ρ hAdm m
  exact ⟨sound_forallE_eq_of hAA' hB ihA ihAtyD ihB hAdm,
    sound_forallE_eq_of hAA'.symm hB'.symm ihA.symm
      (SoundTy.of_eq hAA' ihA ihAtyD) ihB'.symm
      hAdm⟩

/-! ## Σ, which mirrors Π

`Interp.sigma`'s clauses are `Interp.forallE`'s with the head changed, so
these two are `sound_forallE_typedAt and `sound_forallE_eq` with the head  The one real difference is the sort: the `TShape.HasType.sigma`
clause types its outputs at `.type` where `forallE` types them at the
same sort as the Π, so the codomain's typing needs `cumul` on the way in
— which is `SoundTy.isType` rather than `SoundTy.hasType`. -/

/-- The `SoundTy` half of `sigmaDF`. -/
theorem sound_sigma_typedAt {Γ : List Term} {A B : Term} {u v : Bool} (ihAd : SoundTy Γ A (.sort u))
    (ihB : SoundTy (A :: Γ) B (.sort v))
    (hAty : Γ ⊢ A : .sort u) :
    TypedAt Γ (.sigma A B) .type := by
  intro Δ σ ρ hAdm m hm
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  cases hm with
  | bot => exact ⟨TShape.type, Interp.sort', .bot .sort⟩
  | sigma hA hd hwf hNV hbody hle
  refine ⟨TShape.type, Interp.sort', TShape.HasType.mono_l hΔ ?_ hle⟩
  refine .sigma hd (fun e he => ?_) hwf
  have hwe := hwf.2.2.2.1.1 e he
  have W' : Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A :: Γ) :=
    .cons W hAty hwe.2.1
  have hAdm' : Adm Δ (A :: Γ) (σ.cons e.tm) (ρ.push (Shape.T e.inp)) :=
    .cons hAdm W' W.wf hA
      ⟨hNV e he, ihAd.codeAt hAdm hA⟩
  exact ihB.isType hAdm' (hbody e he)

/-- **A forallE-type names itself**: its labels are its own, its domain
is an approximant of `A`, and its codomain entries are approximants of `B`
at stages extended by their labels, each of which names itself by its
own saturation. -/
theorem CodeAt.forallE {Γ : List Term} {A B : Term} {u v : Bool}
    (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) :
    CodeAt Γ (.forallE A B) := by
  intro Δ σ ρ hAdm m hm
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  cases hm with | bot => exact .bot | forallE hA hd hwf hNV hbody hle
  exact TShape.WF.mono hΔ hle
    ⟨hwf.1, hwf.2.1, hwf.2.2.1, hwf.2.2.2.1,
      ⟨v, (IsDefEq.forallEDF hAty hB hB).subst hΔ W⟩⟩

/-- **A sigma-type names itself**: its labels are its own, its domain
is an approximant of `A`, and its codomain entries are approximants of `B`
at stages extended by their labels, each of which names itself by its
own saturation. -/
theorem CodeAt.sigma {Γ : List Term} {A B : Term} {u v : Bool}
    (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) :
    CodeAt Γ (.sigma A B) := by
  intro Δ σ ρ hAdm m hm
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  cases hm with | bot => exact .bot | sigma hA hd hwf hNV hbody hle
  exact TShape.WF.mono hΔ hle
    ⟨hwf.1, hwf.2.1, hwf.2.2.1, hwf.2.2.2.1,
      ⟨true, (IsDefEq.sigmaDF hAty hB hB).subst hΔ W⟩⟩

/-- One direction of the `SoundEq` half of `sigmaDF`; see
`sound_forallE_eq_of` for what it. -/
theorem sound_sigma_eq_of {Γ : List Term} {A A' B B' : Term} {u v : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (hBB' : A :: Γ ⊢ B ≡ B' : .sort v)
    (ihA : SoundEq Γ A A') (ihAtyD : SoundTy Γ A (.sort u))
    (ihB : SoundEq (A :: Γ) B B')
    {Δ : List Term} {σ ρ} (hAdm : Adm Δ Γ σ ρ)
    {m : TShape} (H : Interp Δ Γ (.sigma A B) σ ρ m) :
    Interp Δ Γ (.sigma A' B') σ ρ m := by
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have ⟨⟨_, hAσ⟩, _, hBσ⟩ :
      PiLabelEq Δ (A.subst σ) (B.subst σ.lift) (A'.subst σ) (B'.subst σ.lift) :=
    PiLabelEq.subst hΔ W ⟨⟨u, hAA'⟩, v, hBB'⟩
  have hΓA' : ⊢ (A' :: Γ) := ⟨W.wf, _, hAA'.hasType.2⟩
  cases H with | bot => exact .bot | sigma hA hd hwf hNV hbody hle hAt hBt
  refine .sigma ((ihA hAdm).1 hA) hd
    ⟨⟨_, hAσ.hasType.2⟩, ⟨_, (hAσ.defeqDF_l hΔ hBσ).hasType.2⟩,
      Shape.WF.conv hwf.2.2.1 ⟨_, hAσ.symm⟩,
      ShapeFun.WF.name ((ShapeFun.WF.forget hwf.2.2.2.1).retype ⟨_, hAσ⟩)
        (fun e he => (ShapeFun.WF.canon hwf.2.2.2.1 e he).conv
          ⟨_, (hAσ.hasType.2).instDF hΔ .sort (hAσ.defeqDF_l hΔ hBσ).symm
            (hAσ.defeqDF ((hwf.2.2.2.1.1 e he).2.1))⟩), trivial⟩
    hNV (fun e he => ?_) 
    (hle.trans hΔ (TShape.LE.T.2
      ⟨⟨⟨_, hAσ⟩, _, hBσ⟩, .refl (Shape.WF.forget hwf.2.2.1),
        .refl (ShapeFun.WF.forget hwf.2.2.2.1),
        hwf.2.2.1, ShapeFun.WF.canon hwf.2.2.2.1⟩))
    ⟨u, hAA'.hasType.2⟩ ⟨v, IsDefEq.ctx_id hΓA' (Ctx.SubstEq.defeqHead W.wf hAA')
      hBB'.hasType.2⟩
  · have hwe := hwf.2.2.2.1.1 e he
    have W' : Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A :: Γ) :=
      .cons W hAA'.hasType.1 hwe.2.1
    have hAdm' : Adm Δ (A :: Γ) (σ.cons e.tm) (ρ.push (Shape.T e.inp)) :=
      .cons hAdm W' W.wf hA
        ⟨hNV e he, ihAtyD.codeAt hAdm hA⟩
    exact Interp.ctx ((ihB hAdm').1 (hbody e he)) hΓA'
      (Ctx.SubstEq.defeqHead W.wf hAA') Lookup.cons_head

/-- The `SoundEq` half of `sigmaDF`. -/
theorem sound_sigma_eq {Γ : List Term} {A A' B B' : Term} {u v : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u)
    (hB : A :: Γ ⊢ B ≡ B' : .sort v) (hB' : A' :: Γ ⊢ B ≡ B' : .sort v)
    (ihA : SoundEq Γ A A') (ihAtyD : SoundTy Γ A (.sort u))
    (ihB : SoundEq (A :: Γ) B B') (ihB' : SoundEq (A' :: Γ) B B') :
    SoundEq Γ (.sigma A B) (.sigma A' B') := by
  intro Δ σ ρ hAdm m
  exact ⟨sound_sigma_eq_of hAA' hB ihA ihAtyD ihB hAdm,
    sound_sigma_eq_of hAA'.symm hB'.symm ihA.symm
      (SoundTy.of_eq hAA' ihA ihAtyD) ihB'.symm
      hAdm⟩

/-! ## Stage invariance

The interpretation depends on its stage only up to definitional equality.
Master needs no such lemma, its shapes carrying no labels; the other repo
gets it from the quotient, two definitionally equal substitutions being
the *same* morphism of `Ctx`.  Here it is a theorem, and — this is the
point — a theorem about a **typed** term, not about `Interp` alone.

For a raw `t` the statement is false.  Take `t = .forallE A B` with `A`
ill-typed in `Γ` but `A[σ]` typed in `Δ`: the `forallE` rule holds with
label `A[σ]`, and nothing relates it to `A[σ']`, because no rule types a
label in `Γ` — `hlab` types labels in `Δ`.  So the induction is on a
typing derivation, which is exactly what supplies `Δ ⊢ A[σ] ≡ A[σ'] : sort u`
for each label, by `IsDefEq.subst'`. -/

/-- **Directedness of a type's extension**: two compatible shapes typed at
an approximant of `⟦A⟧` have a *typed upper bound* there.

The elementary shadow of the other repo's
`CodeAssignment.rawExtend_isDirected`.  There a value is an *ideal* and
semantic typing is the fixed point `rawExtend ⟦A⟧ x = x`, so the shape
this asks for is literally `rawExtend ⟦A⟧ (x ⊔ y)`: it dominates both
because both are already fixed points below the join, it is typed by
idempotence, and it is directed because `rawExtend` is a `bind₂` of
ideals — three facts free from the ideal structure, none an induction.  A
value here is a *single shape*, so there is no retraction to appeal to and
the fact is content.

Upper-bound form, to match his `IsDirected`, which never mentions the
join.  The join form is out of reach anyway: the `pair` clause of
`HasType` types a pair at a *dominating* first component, and two
compatible pairs can carry incompatible dominators, so there need be no
code to read at `x ⊔ y`.  He never meets this, having no Σ-types.

**Its one consumer is `tr`** (`IsDefEq.dir`), where two approximants are
typed at two approximants of the motive and the joined witness has to be
typed at the joined motive; master does it with `TShape.HasType.join'` at
an arbitrary type, which is the lemma this branch removed.  Π and λ do not
need it, now that directedness runs under `Valuation.WF`. -/
def SoundJoin (Γ : List Term) (A : Term) : Prop :=
  ∀ {{Δ : List Term}} {σ ρ}, Adm Δ Γ σ ρ →
    ∀ {a x y}, Interp Δ Γ A σ ρ a → TShape.WF Δ x → TShape.WF Δ y →
      TShape.Named Δ a x none → TShape.Named Δ a y none → TShape.Compat Δ x y →
      ∃ z, TShape.WF Δ z ∧ TShape.LE Δ x z ∧ TShape.LE Δ y z ∧ TShape.Named Δ a z none

/-- **`SoundJoin` holds, for every type.**  The subject join is
`TShape.Named.join`: no `Interp`, no `Adm`, no induction on `A`.  It is
stated with `Named` rather than `HasType` because that is what survives
the graph-free Σ-value (§4.7e): `HasType` reads the second component's
code at a *dominator* of the first, and two dominators need not be
compatible, while `Named` reads it at the first component itself, which
the shapes' own compatibility covers. -/
theorem sound_join {Γ : List Term} {A : Term} : SoundJoin Γ A := by
  intro Δ σ ρ hAdm a x y _ hx hy hxa hya hc
  have hΔ := hAdm.ctx
  exact ⟨x.join y, TShape.WF.join hΔ hc hx hy, (TShape.le_join hΔ hx hy hc).1,
    (TShape.le_join hΔ hx hy hc).2, TShape.Named.join hΔ hc hxa hya⟩

/-! ## λ

The λ analogue of the Π case above, with the domain *label* in place of
the Π label and the body in place of the codomain.  The one structural
difference is that the λ-shape's domain shape is not part of the shape:
`Interp.lam`'s `d` is a `TShape` beside it, so the join of the two `d`s
needs no level bookkeeping. -/

/-! ### Choosing a code for every entry

The λ's own typing is built from the *bodies'* types: one code per entry
of the graph, each an approximant of `B` at that entry's slot.  The
soundness hypothesis delivers them one at a time (`∃ c, …`), so they have
to be collected into a list — and then brought to one level, since a
graph is a list at one level.  These two utilities are that, and nothing
about this model. -/

/-- The maximum of a list of levels, above a floor. -/
def levelMax {α : Type _} (f : α → Nat) (k : Nat) : List α → Nat
  | [] => k
  | e :: g => max (f e) (levelMax f k g)

theorem le_levelMax {α : Type _} {f : α → Nat} {k : Nat} :
    ∀ {g : List α}, k ≤ levelMax f k g
  | [] => Nat.le_refl _
  | _ :: g => Nat.le_trans (le_levelMax (g := g)) (Nat.le_max_right ..)

theorem mem_le_levelMax {α : Type _} {f : α → Nat} {k : Nat} :
    ∀ {g : List α} {e}, e ∈ g → f e ≤ levelMax f k g
  | _ :: g, e, he => by
    match List.mem_cons.1 he with
    | .inl h => exact h ▸ Nat.le_max_left ..
    | .inr h => exact Nat.le_trans (mem_le_levelMax (g := g) h) (Nat.le_max_right ..)

/-- **A graph of a family's values is coherent.**  Two entries whose
labels become definitionally equal at a later stage name one slot of the
family, their inputs join there, and the family's directedness puts both
values under one shape — the λ case's cross-pair argument, with the
*codomain* in place of the body.  It is what makes the Π-shape
built below well formed. -/
theorem graph_coherent {Γ Δ : List Term} {A C t : Term} {σ ρ} {u : Bool}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ t : C) (W : Ctx.SubstEq Δ σ σ Γ) (hwρ : Valuation.WF Δ Γ ρ)
     {k} {f : ShapeFun k}
    (hent : ∀ e ∈ f, Shape.WF Δ e.inp)
    (hbody : ∀ e ∈ f, Interp Δ (A :: Γ) t (σ.cons e.tm) (ρ.push e.inp.T) e.out.T) :
    ShapeFun.Compat Shape.Compat Δ (A.subst σ) f f := by
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hAty⟩
  have ihBdir := (IsDefEq.dir hΓA hB).1
  intro e he e' he' Θ τ hΘ Wτ hlabq hin
  have Wc : Ctx.SubstEq Θ (σ.comp τ) (σ.comp τ) Γ := Ctx.SubstEq.comp hΘ Wτ W
  have hwρτ : Valuation.WF Θ Γ (ρ.subst τ) := Valuation.WF.subst hΘ Wτ hwρ
  have hwx₁ : TShape.WF Θ (Shape.T (e.inp.subst τ)) := Shape.WF.subst hΘ Wτ (hent e he)
  have hwx₂ : TShape.WF Θ (Shape.T (e'.inp.subst τ)) := Shape.WF.subst hΘ Wτ (hent e' he')
  have hcx : TShape.Compat Θ (Shape.T (e.inp.subst τ)) (Shape.T (e'.inp.subst τ)) :=
    TShape.Compat.T.2 hin
  have hwxj := TShape.WF.join hΘ hcx hwx₁ hwx₂
  have ⟨hjx₁, hjx₂⟩ := TShape.le_join hΘ hwx₁ hwx₂ hcx
  -- the label equation puts the two bodies at one stage
  have heq : Θ ⊢ e'.tm.subst τ ≡ e.tm.subst τ : (A.subst σ).subst τ := hlabq.2.symm
  rw [subst_subst] at heq
  have Wcons : Ctx.SubstEq Θ ((σ.comp τ).cons (e'.tm.subst τ))
      ((σ.comp τ).cons (e.tm.subst τ)) (A :: Γ) := .cons Wc hAty heq
  have Wdiag : Ctx.SubstEq Θ ((σ.comp τ).cons (e.tm.subst τ))
      ((σ.comp τ).cons (e.tm.subst τ)) (A :: Γ) := .cons Wc hAty heq.hasType.2
  have hb₁ := (hbody e he).subst hΘ Wτ
  have hb₂0 := (hbody e' he').subst hΘ Wτ
  rw [Subst.cons_comp, Valuation.subst_push] at hb₁ hb₂0
  have hb₂ := IsDefEq.stage hΓA hB hΘ Wcons hb₂0
  obtain ⟨_, _, _, hs₁, hs₂⟩ := ihBdir hΘ Wdiag (Valuation.WF.push hwρτ hwxj)
    (Interp.mono_val hΘ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρτ, hjx₁⟩) hb₁)
    (Interp.mono_val hΘ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρτ, hjx₂⟩) hb₂)
  exact TShape.Compat.T.1 (TShape.Compat.of_common_upper hΘ (by assumption) hs₁ hs₂)

/-- Each entry of a λ-approximant is an admissible stage: its label is
typed at the domain, and the slot it opens is hereditarily typed there
because `Interp.lam` demands that. -/
theorem lam_stage {Γ Δ : List Term} {A : Term} {u : Bool} {σ ρ}
    (hAty : Γ ⊢ A : .sort u) (ihAd : SoundTy Γ A (.sort u))
    (hAdm : Adm Δ Γ σ ρ)
    {n} {g : ShapeFun n} {d : TShape} (hA : Interp Δ Γ A σ ρ d)
    (hwf : Shape.WF (n := n+1) Δ (.lam (A.subst σ) g))
    (hNV : ∀ e ∈ g, TShape.Named Δ d e.inp.T e.tm) :
    ∀ e ∈ g, Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A :: Γ) ∧
      Adm Δ (A :: Γ) (σ.cons e.tm) (ρ.push e.inp.T) := by
  have W := hAdm.stage
  intro e he
  have hwe := hwf.2.2.1.1 e he
  exact ⟨.cons W hAty hwe.2.1,
    .cons hAdm (.cons W hAty hwe.2.1) W.wf hA
      ⟨hNV e he, ihAd.codeAt hAdm hA⟩⟩

/-- **The Π-approximant read off a λ-approximant.**  Given a code for
every entry's body, this is the Π-shape whose domain is the λ's own
domain slot and whose codomain graph has one entry per code: it
interprets `Π A B`, it types the λ-shape, and its graph looks up each
entry's code.  `sound_lam_dom` instantiates the codes with the body's
own saturation. -/
theorem lam_pi_code {Γ Δ : List Term} {A B : Term} {u v : Bool} {σ ρ}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) (ihAd : SoundTy Γ A (.sort u))
    (ihBty : SoundTy (A :: Γ) B (.sort v))
    (hAdm : Adm Δ Γ σ ρ)
    {n} {g : ShapeFun n} {d : TShape}
    (hA : Interp Δ Γ A σ ρ d) (hd : TShape.HasType Δ d TShape.type)
    (hwf : Shape.WF (n := n+1) Δ (.lam (A.subst σ) g))
    (hNV : ∀ e ∈ g, TShape.Named Δ d e.inp.T e.tm)
    {Q : Entry (Shape n) → TShape → Prop}
    (hQmono : ∀ {e : Entry (Shape n)} {c c' : TShape}, TShape.LE Δ c c' →
      TShape.HasType Δ c' TShape.type → Q e c → Q e c')
    (hcodes : ∀ e ∈ g, ∃ c, Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push e.inp.T) c ∧
      TShape.HasType Δ e.out.T c ∧ Q e c) :
    ∃ (k : Nat) (dk : Shape k) (f : ShapeFun k),
      Interp Δ Γ (.forallE A B) σ ρ
        (Shape.T (n := k+1) (.forallE (A.subst σ) (B.subst σ.lift) dk f)) ∧
      TShape.HasType Δ (Shape.T (n := n+1) (.lam (A.subst σ) g))
        (Shape.T (n := k+1) (.forallE (A.subst σ) (B.subst σ.lift) dk f)) ∧
      TShape.HasType Δ (Shape.T dk) TShape.type ∧
      (∀ e ∈ g, TShape.Named Δ (Shape.T dk) e.inp.T e.tm) ∧
      (∀ e ∈ g, ∃ c, TEvaluates Δ f (A.subst σ) e.tm e.inp.T c ∧
        TShape.HasType Δ c TShape.type ∧ Q e c) ∧
      TShape.WF Δ (Shape.T (n := k+1) (.forallE (A.subst σ) (B.subst σ.lift) dk f)) ((Term.forallE A B).subst σ) := by
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have ihBc := ihBty.codeAt
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hAty⟩
  have ihBdir := (IsDefEq.dir hΓA hB).1
  have hwρ := hAdm.wf
  have hstage := lam_stage hAty ihAd hAdm hA hwf hNV
  -- the codes, collected and brought to one level
  obtain ⟨g₀, hmap, hall⟩ := List.exists_pairs (β := TShape) hcodes
  obtain ⟨k, hkn, hkd, hkc⟩ : ∃ k, n ≤ k ∧ d.1 ≤ k ∧ ∀ p ∈ g₀, (Prod.snd p : TShape).1 ≤ k :=
    ⟨levelMax (fun p => (Prod.snd p : TShape).1) (max n d.1) g₀,
      Nat.le_trans (Nat.le_max_left ..) le_levelMax,
      Nat.le_trans (Nat.le_max_right ..) le_levelMax,
      fun p hp => mem_le_levelMax (f := fun p => (Prod.snd p : TShape).1) hp⟩
  -- the codomain graph, one entry per entry of the λ's
  obtain ⟨f, hf⟩ : ∃ f : ShapeFun k, ∀ e, e ∈ f ↔ ∃ p ∈ g₀,
      e = ⟨p.1.tm, p.1.inp.lift k, (Prod.snd p : TShape).2.lift k⟩ :=
    ⟨g₀.map fun p => ⟨p.1.tm, p.1.inp.lift k, (Prod.snd p : TShape).2.lift k⟩,
      fun e => by simp [List.mem_map, eq_comm]⟩
  have hg₀g : ∀ p ∈ g₀, p.1 ∈ g := fun p hp => hmap ▸ List.mem_map.2 ⟨p, hp, rfl⟩
  have hpwf : ∀ p ∈ g₀, TShape.WF Δ (Prod.snd p : TShape) := fun p hp => (hall p hp).1.wf
  have hdty : TShape.HasType Δ (Shape.T (d.2.lift k)) TShape.type :=
    hd.lift_subject hΔ hkd
  have hdle : TShape.LE Δ d (Shape.T (d.2.lift k)) :=
    TShape.LE.le_lift hΔ (m := d) hkd hd.wf.1
  -- the Π-shape's premises, entry by entry
  have hfent : ∀ e ∈ f, (∃ u, Δ ⊢ A.subst σ : .sort u) ∧ Δ ⊢ e.tm : A.subst σ ∧
      Shape.WF Δ e.inp ∧ Shape.WF Δ e.out := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := (hf e).1 he
    have hwe := hwf.2.2.1.1 p.1 (hg₀g p hp)
    exact ⟨hwe.1, hwe.2.1, (Shape.lift_wf hkn).2 hwe.2.2.1,
      (Shape.lift_wf (hkc p hp)).2 (hpwf p hp)⟩
  have hfdom : ∀ e ∈ f, TShape.Named Δ (Shape.T (d.2.lift k)) e.inp.T e.tm := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := (hf e).1 he
    exact TShape.Named.mono_r hΔ
      (TShape.Named.lift_subject hΔ (hNV p.1 (hg₀g p hp)) hkn) hdle hdty
  have hfbody : ∀ e ∈ f,
      Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push e.inp.T) e.out.T := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := (hf e).1 he
    have hwe := hwf.2.2.1.1 p.1 (hg₀g p hp)
    refine Interp.mono hΔ 
      (TShape.LE.lift_le hΔ (m := (Prod.snd p : TShape)) (hkc p hp) (hpwf p hp)) ?_
    exact Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
      TShape.LE.le_lift hΔ (m := p.1.inp.T) hkn hwe.2.2.1⟩) (hall p hp).1
  -- so the Π-shape is well formed and interprets `Π A B`
  have hAσ : Δ ⊢ A.subst σ : .sort u := hAty.subst hΔ W
  have hΔA : ⊢ (A.subst σ :: Δ) := ⟨hΔ, _, hAσ⟩
  have hcdPi : Shape.WF Δ (d.2.lift k) (A.subst σ) :=
    (Shape.lift_wf hkd).2 (ihAd.codeAt hAdm hA)
  have hcfPi : ∀ e ∈ f, Shape.WF Δ e.out ((B.subst σ.lift).inst e.tm) := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := (hf e).1 he
    have hc := ihBc (hstage p.1 (hg₀g p hp)).2 (hall p hp).1
    rw [← inst_lift_cons] at hc
    exact (Shape.lift_wf (hkc p hp)).2 hc
  have hwfPi : Shape.WF (n := k+1) Δ
      (.forallE (A.subst σ) (B.subst σ.lift) (d.2.lift k) f) :=
    ⟨⟨u, hAσ⟩, ⟨v, hB.subst hΔA (W.lift hAty hAσ)⟩,
      hcdPi,
      ShapeFun.WF.name
        ⟨fun e he => hfent e he,
          graph_coherent hΓ hAty hB W hwρ (fun e he => (hfent e he).2.2.1)
            hfbody⟩ hcfPi, trivial⟩
  have hPi : Interp Δ Γ (.forallE A B) σ ρ
      (Shape.T (n := k+1) (.forallE (A.subst σ) (B.subst σ.lift) (d.2.lift k) f)) :=
    .forallE (Interp.mono hΔ 
        (TShape.LE.lift_le hΔ (m := d) hkd hd.wf.1) hA)
      hdty hwfPi
      (fun e he => by
        obtain ⟨p, hp, rfl⟩ := (hf e).1 he
        exact hfdom _ he)
      hfbody (TShape.LE.refl hwfPi) ⟨u, hAty⟩ ⟨v, hB⟩
  -- the typing codes are the Π-entries, so the λ-shape is typed by it
  have hcty : ∀ p ∈ g₀, TShape.HasType Δ (Shape.T ((Prod.snd p : TShape).2.lift k))
      TShape.type := by
    intro p hp
    exact (ihBty.isType (hstage p.1 (hg₀g p hp)).2
      (hall p hp).1).lift_subject hΔ (hkc p hp)
  -- each code is looked up in the Π's graph at its own entry
  have hlook : ∀ p ∈ g₀, TEvaluates Δ f (A.subst σ) p.1.tm p.1.inp.T
      (Shape.T ((Prod.snd p : TShape).2.lift k)) := by
    intro p hp
    refine TEvaluates.entry _ ((hf _).2 ⟨p, hp, rfl⟩)
      ⟨hwf.2.2.2, (hwf.2.2.1.1 p.1 (hg₀g p hp)).2.1⟩ ?_
    exact TShape.LE.lift_le hΔ (m := p.1.inp.T) hkn (hwf.2.2.1.1 p.1 (hg₀g p hp)).2.2.1
  refine ⟨k, d.2.lift k, f, hPi, TShape.HasType.lam (g₀ := g₀)
    hdty (fun e he => ?_) hwf hwfPi (fun e he => ?_) (fun e he => ?_)
    (fun p hp => ?_) (fun p hp => (hall p hp).2.1) (TyEq.refl hAσ),
    hdty, fun e he => ?_, fun e he => ?_, ?_⟩
  · -- the Π-entries are types
    obtain ⟨p, hp, rfl⟩ := (hf e).1 he
    exact hcty p hp
  · -- the generator's entries are well formed
    rw [hmap] at he
    exact ⟨(hwf.2.2.1.1 e he).2.2.1, (hwf.2.2.1.1 e he).2.2.2⟩
  · -- every entry of `g` is covered by the generator, namely by itself
    rw [hmap]
    exact TEvaluates.refl hwf.2.2.1 e he
  · -- and each generator code is the Π-entry built from it
    exact TEvaluates.lower
      (TShape.LE.le_lift hΔ (m := (Prod.snd p : TShape)) (hkc p hp) (hpwf p hp))
      (hlook p hp)
  · -- the inputs are hereditarily typed at the lifted domain, and named
    exact TShape.Named.mono_r hΔ (hNV e he) hdle hdty
  · -- and the code of each entry is looked up at it
    obtain ⟨p, hp, rfl⟩ : ∃ p ∈ g₀, p.1 = e := by
      rw [← hmap, List.mem_map] at he
      obtain ⟨p, hp, heq⟩ := he
      exact ⟨p, hp, heq⟩
    exact ⟨_, hlook p hp, hcty p hp,
      hQmono (TShape.LE.le_lift hΔ (m := (Prod.snd p : TShape)) (hkc p hp) (hpwf p hp))
        (hcty p hp) (hall p hp).2.2⟩
  · -- the Π-code names `Π A B`: its labels are the type's, its domain is
    -- an approximant of `A`, and its codomain entries approximate `B`
    exact ⟨hwfPi.1, hwfPi.2.1, hwfPi.2.2.1, hwfPi.2.2.2.1,
      ⟨v, (IsDefEq.forallEDF hAty hB hB).subst hΔ W⟩⟩

/-- **Saturation at a λ.**  The body's own saturation enlarges every
entry's output to a hereditarily typed one -- the enlarged graph is
still a λ-approximant, by the same coherence argument (`graph_coherent`)
that `Interp.lam` wanted in the first place -- and then the codomain
codes of `lam_pi_code` are exactly codes `Named` asks for. -/
theorem sound_lam_dom {Γ : List Term} {A B b : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v)
    (hb : A :: Γ ⊢ b : B) (ihAd : SoundTy Γ A (.sort u))
    (ihBty : SoundTy (A :: Γ) B (.sort v))
    (ihbdom : SoundTy (A :: Γ) b B)
     :
    SoundTy Γ (.lam A b) (.forallE A B) := by
  have ihBc := ihBty.codeAt
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hAty⟩
  have ihbdir := (IsDefEq.dir hΓA hb).1
  have ihBdir := (IsDefEq.dir hΓA hB).1
  intro Δ σ ρ hAdm m hm
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have hwρ := hAdm.wf
  cases hm with
  | bot => exact ⟨TShape.bot, TShape.bot, .bot, TShape.bot_le' rfl, .bot, (TShape.Named.bot (.bot (.bot .sort))), TShape.WF.bot⟩
  | @lam _ _ _ _ n g d _ _ hA hd hwf hNV hbody hle hAt =>
    have hstage := lam_stage hAty ihAd hAdm hA hwf hNV
    -- saturate every body, and bring the enlarged outputs to one level
    obtain ⟨gs, hmap, hall⟩ := List.exists_pairs (β := TShape × TShape)
      (P := fun (e : Entry (Shape n)) (p : TShape × TShape) =>
        Interp Δ (A :: Γ) b (σ.cons e.tm) (ρ.push e.inp.T) p.1 ∧
        TShape.LE Δ e.out.T p.1 ∧
        Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push e.inp.T) p.2 ∧
        TShape.Named Δ p.2 p.1 (b.subst (σ.cons e.tm)) ∧
        TShape.WF Δ p.2 (B.subst (σ.cons e.tm)))
      (fun e he => by
        obtain ⟨m', c, hm', hle', hc, hNV, hcc⟩ :=
          ihbdom (hstage e he).2 (hbody e he)
        exact ⟨(m', c), hm', hle', hc, hNV, hcc⟩)
    -- the enlarged graph, at one level
    obtain ⟨k, hkn, hkc⟩ : ∃ k, n ≤ k ∧ ∀ p ∈ gs, ((Prod.snd p).1 : TShape).1 ≤ k :=
      ⟨levelMax (fun p => ((Prod.snd p).1 : TShape).1) n gs, le_levelMax,
        fun p hp => mem_le_levelMax (f := fun p => ((Prod.snd p).1 : TShape).1) hp⟩
    obtain ⟨g', hg'⟩ : ∃ g' : ShapeFun k, ∀ e, e ∈ g' ↔ ∃ p ∈ gs,
        e = ⟨p.1.tm, p.1.inp.lift k, ((Prod.snd p).1 : TShape).2.lift k⟩ :=
      ⟨gs.map fun p => ⟨p.1.tm, p.1.inp.lift k, ((Prod.snd p).1 : TShape).2.lift k⟩,
        fun e => by simp [List.mem_map, eq_comm]⟩
    have hgsg : ∀ p ∈ gs, p.1 ∈ g := fun p hp => hmap ▸ List.mem_map.2 ⟨p, hp, rfl⟩
    have hswf : ∀ p ∈ gs, TShape.WF Δ ((Prod.snd p).1 : TShape) :=
      fun p hp => (hall p hp).1.wf
    -- its entries are well formed, and still carry information
    have hent' : ∀ e ∈ g', (∃ u, Δ ⊢ A.subst σ : .sort u) ∧ Δ ⊢ e.tm : A.subst σ ∧
        Shape.WF Δ e.inp ∧ Shape.WF Δ e.out := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := (hg' e).1 he
      have hwe := hwf.2.2.1.1 p.1 (hgsg p hp)
      exact ⟨hwe.1, hwe.2.1, (Shape.lift_wf hkn).2 hwe.2.2.1,
        (Shape.lift_wf (hkc p hp)).2 (hswf p hp)⟩
    have hbody' : ∀ e ∈ g',
        Interp Δ (A :: Γ) b (σ.cons e.tm) (ρ.push e.inp.T) e.out.T := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := (hg' e).1 he
      have hwe := hwf.2.2.1.1 p.1 (hgsg p hp)
      refine Interp.mono hΔ 
        (TShape.LE.lift_le hΔ (m := ((Prod.snd p).1 : TShape)) (hkc p hp) (hswf p hp)) ?_
      exact Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
        TShape.LE.le_lift hΔ (m := p.1.inp.T) hkn hwe.2.2.1⟩) (hall p hp).1
    have hnotbot : ∀ e ∈ g', ¬ e.out.IsBot := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := (hg' e).1 he
      intro hbot
      refine hwf.2.1 p.1 (hgsg p hp) ?_
      have : ((Prod.snd p).1 : TShape).2 = Shape.bot :=
        (hswf p hp).eq_bot_of_isBot ((Shape.lift_isBot (hkc p hp)).1 hbot)
      have hbb : p.1.out = Shape.bot := TShape.le_bot hΔ this (hall p hp).2.1
      exact hbb ▸ Shape.isBot_bot
    have hwf' : Shape.WF (n := k+1) Δ (.lam (A.subst σ) g') := by
      refine ⟨?_, hnotbot, ⟨hent', graph_coherent hΓ hAty hb W hwρ
        (fun e he => (hent' e he).2.2.1) hbody'⟩, hwf.2.2.2⟩
      intro hnil
      refine hwf.1 ?_
      rw [← hmap]
      have : gs = [] := by
        cases hgs : gs with
        | nil => rfl
        | cons q qs =>
          exact absurd ((hg' _).2 ⟨q, by simp [hgs], rfl⟩) (by simp [hnil])
      simp [this]
    -- the enlarged λ-shape is still an approximant of the λ
    have hlamI : Interp Δ Γ (.lam A b) σ ρ (Shape.T (n := k+1) (.lam (A.subst σ) g')) := by
      refine .lam hA hd hwf' (fun e he => ?_) hbody'
        (TShape.LE.refl (TShape.WF.T.2 hwf')) hAt
      · obtain ⟨p, hp, rfl⟩ := (hg' e).1 he
        exact TShape.Named.lift_subject hΔ (hNV p.1 (hgsg p hp)) hkn
    -- and it dominates the given one: same entries, bigger outputs
    have hlamle : TShape.LE Δ (Shape.T (n := n+1) (.lam (A.subst σ) g))
        (Shape.T (n := k+1) (.lam (A.subst σ) g')) := by
      refine (TShape.LE.def hΔ (k := k+1) (Nat.succ_le_succ hkn) (Nat.le_refl _)).2 ?_
      show Shape.LE Δ (.lam (A.subst σ) (ShapeFun.lift (Shape.lift k) g))
        (.lam (A.subst σ) (ShapeFun.lift (Shape.lift k) g'))
      rw [show ShapeFun.lift (Shape.lift k) g' = g' from by
        simp [ShapeFun.lift, Shape.lift_self]]
      have hwfl : Shape.WF (n := k+1) Δ
          (.lam (A.subst σ) (ShapeFun.lift (Shape.lift k) g)) :=
        (Shape.lift_wf (Nat.succ_le_succ hkn)).2 hwf
      refine ⟨⟨fun e he => ?_, hwfl.2.2.1, hwf'.2.2.1⟩, hwfl.1, hwfl.2.1,
        ⟨u, hAty.subst hΔ W⟩, hwfl.2.2.2⟩
      -- every lifted entry is covered by its enlarged copy
      obtain ⟨q, hq, rfl⟩ := ShapeFun.mem_lift.1 he
      obtain ⟨p, hp, rfl⟩ : ∃ p ∈ gs, p.1 = q := by
        rw [← hmap, List.mem_map] at hq
        obtain ⟨p, hp, heq⟩ := hq
        exact ⟨p, hp, heq⟩
      refine ShapeFun.Eval.lower
        (TShape.LE.def_mp (a := p.1.out.T) (b := ((Prod.snd p).1 : TShape))
          hkn (hkc p hp) (hall p hp).2.1) ?_
      exact ShapeFun.Eval.entry _ ((hg' _).2 ⟨p, hp, rfl⟩)
        ⟨hwf.2.2.2, (hwf.2.2.1.1 p.1 (hgsg p hp)).2.1⟩
        (Shape.LE.refl ((Shape.lift_wf hkn).2 (hwf.2.2.1.1 p.1 (hgsg p hp)).2.2.1))
    -- the Π-approximant, with the saturation's codes
    obtain ⟨kP, dP, f, hPi, hty, hdtyP, hinP, hcodes, hcanPi⟩ :=
      lam_pi_code (Q := fun e c =>
          TShape.Named Δ c e.out.T (Term.app ((Term.lam A b).subst σ) e.tm))
        hΓ hAty hB ihAd ihBty hAdm hA hd hwf'
        (fun e he => by
          obtain ⟨p, hp, rfl⟩ := (hg' e).1 he
          exact TShape.Named.lift_subject hΔ (hNV p.1 (hgsg p hp)) hkn)
        (fun hle' hty' hQ => TShape.Named.mono_r hΔ hQ hle' hty')
        (fun e he => by
          obtain ⟨p, hp, rfl⟩ := (hg' e).1 he
          refine ⟨(Prod.snd p).2, ?_, ?_, ?_⟩
          · exact Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
              TShape.LE.le_lift hΔ (m := p.1.inp.T) hkn
                (hwf.2.2.1.1 p.1 (hgsg p hp)).2.2.1⟩) (hall p hp).2.2.1
          · exact TShape.HasType.mono_l hΔ (hall p hp).2.2.2.1.hasType
              (TShape.LE.lift_le hΔ (m := ((Prod.snd p).1 : TShape)) (hkc p hp)
                (hswf p hp))
          · have hAσ : Δ ⊢ A.subst σ : .sort u := hAty.subst hΔ W
            have hbσ : A.subst σ :: Δ ⊢ b.subst σ.lift : B.subst σ.lift :=
              hb.subst ⟨hΔ, _, hAσ⟩ (W.lift hAty hAσ)
            have htm : Δ ⊢ p.1.tm : A.subst σ := (hwf.2.2.1.1 p.1 (hgsg p hp)).2.1
            have hβ := IsDefEq.beta₀ hΔ hbσ htm
            rw [inst_lift_cons, inst_lift_cons] at hβ
            exact (((hall p hp).2.2.2.1.defeq hΔ (hall p hp).2.2.2.2
              hβ.symm).lift_subject hΔ (hkc p hp)))
    -- and the codes, entry by entry, are what `Named` asks for
    obtain ⟨cs₀, hcsmap, hcsall⟩ := List.exists_pairs (β := TShape)
      (P := fun (e : Entry (Shape k)) (c : TShape) =>
        TEvaluates Δ f (A.subst σ) e.tm e.inp.T c ∧
          TShape.Named Δ c e.out.T (Term.app ((Term.lam A b).subst σ) e.tm))
      (fun e he => by
        obtain ⟨c, hc, _, hdc⟩ := hcodes e he
        exact ⟨c, hc, hdc⟩)
    have hcsg : ∀ p ∈ cs₀, p.1 ∈ g' := fun p hp => hcsmap ▸ List.mem_map.2 ⟨p, hp, rfl⟩
    refine ⟨Shape.T (n := k+1) (.lam (A.subst σ) g'), _, hlamI,
      TShape.LE.trans hΔ hle hlamle, hPi,
      .pi (cs := cs₀.map (fun p => ((⟨p.1.tm, p.1.inp.T, p.1.out.T⟩ : Entry TShape),
        p.2))) hty ?_ (fun p hp => ?_) (fun p hp => ?_) (fun p hp => ?_), hcanPi⟩
    · show g'.map (fun e => (⟨e.tm, e.inp.T, e.out.T⟩ : Entry TShape)) = _
      rw [← hcsmap]
      simp [List.map_map, Function.comp_def]
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact hinP q.1 (hcsg q hq)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact (hcsall q hq).1
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact (hcsall q hq).2

/-- One direction of the `SoundEq` half of `lamDF`.

A λ-shape carries only its *domain* label, so the two sides differ in
that one term — and `Shape.LE` compares it up to definitional equality,
so one λ-shape is below the other with the same graph.  The bodies move
by their own `SoundEq` at each entry's stage (which is unchanged: the
stage term is the entry's label, not the binder's annotation) and then
`Interp.ctx` for the context whose head changed. -/
theorem sound_lam_eq_of {Γ : List Term} {A A' b b' : Term} {u : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u)
    (ihA : SoundEq Γ A A') (ihAd : SoundTy Γ A (.sort u))
    (ihb : SoundEq (A :: Γ) b b')
    {Δ : List Term} {σ ρ} (hAdm : Adm Δ Γ σ ρ)
    {m : TShape} (H : Interp Δ Γ (.lam A b) σ ρ m) :
    Interp Δ Γ (.lam A' b') σ ρ m := by
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have hAσ : TyEq Δ (A.subst σ) (A'.subst σ) := ⟨u, hAA'.subst hΔ W⟩
  cases H with
  | @lam _ _ _ _ _ _ _ _ _ hA hd hwf hNV hbody hle hAt =>
    have hwf' : Shape.WF Δ (Shape.lam (A'.subst σ) _) :=
      ⟨hwf.1, hwf.2.1, hwf.2.2.1.retype hAσ, hAσ.refl_r⟩
    refine .lam ((ihA hAdm).1 hA) hd hwf' hNV (fun e he => ?_) 
      (hle.trans hΔ (TShape.LE.T.2
        ⟨ShapeFun.LE.refl hwf.2.2.1, hwf.1, hwf.2.1, hAσ, hwf.2.2.2⟩))
      ⟨u, hAA'.hasType.2⟩
    -- the body, at the stage extended by the entry's label
    have hwe := hwf.2.2.1.1 e he
    have W' : Ctx.SubstEq Δ (σ.cons e.tm) (σ.cons e.tm) (A :: Γ) :=
      .cons W hAA'.hasType.1 hwe.2.1
    have hAdm' : Adm Δ (A :: Γ) (σ.cons e.tm) (ρ.push (Shape.T e.inp)) :=
      .cons hAdm W' W.wf hA
        ⟨hNV e he, ihAd.codeAt hAdm hA⟩
    exact Interp.ctx ((ihb hAdm').1 (hbody e he)) ⟨W.wf, _, hAA'.hasType.2⟩
      (Ctx.SubstEq.defeqHead W.wf hAA') Lookup.cons_head
  | bot => exact .bot

/-- The `SoundEq` half of `lamDF`, both directions on the mirrored data —
which is why the rule carries its body premise twice, once over each
domain. -/
theorem sound_lam_eq {Γ : List Term} {A A' b b' : Term} {u : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u)
    (ihA : SoundEq Γ A A') (ihAd : SoundTy Γ A (.sort u))
    (ihb : SoundEq (A :: Γ) b b') (ihb' : SoundEq (A' :: Γ) b b') :
    SoundEq Γ (.lam A b) (.lam A' b') := by
  intro Δ σ ρ hAdm m
  exact ⟨sound_lam_eq_of hAA' ihA ihAd ihb hAdm,
    sound_lam_eq_of hAA'.symm ihA.symm
      (SoundTy.of_eq hAA' ihA ihAd) ihb'.symm hAdm⟩

/-! ## Pairs

A pair shape's components are the two arguments' own, so the common upper
bound is componentwise: the labels agree (both come from the same term at
the same stage), and each component joins by its argument's directedness.
The non-degeneracy conjunct of `WF` comes for free from `Shape.WF.join`,
which is why the bound is taken as the *join of the two lifted shapes*
rather than assembled from the two component bounds. -/

/-! ## Application

Directedness at `app` is where the λ-shape's domain label pays for itself
(§5.5b).  Two `app` derivations for the same term look their arguments up
in two λ-shapes of `F`, at those shapes' own labels `A₁`, `A₂`.  A common
upper bound of the two λ-shapes is a λ-shape, its graph covers both, and
the order on λ-shapes makes its label definitionally equal to both — so
the two lookups become lookups in *one* graph at *one* query, whose
outputs the graph's coherence makes joinable.  No typing of `F` or of the
argument is used, which is what lets `SoundDir` stay over `Valuation.WF`
and be proved before soundness. -/

/-! ## The first projection

`Interp.fst` reads the first component off a pair shape, so both halves
are the pair's: `SoundEq` is the argument's clause by clause, and for
`SoundTy` the component's typing is the `HasType.pair` clause's own
`hxd`, brought down by `mono_l` and retyped at the Σ's domain by
`mono_r`.  The second projection is not here: its type is `B[fst p]`, and
relating that to the Σ's codomain graph needs `Interp.inst`. -/

/-! ## The β-rules of Σ

A projection of a pair has the component's approximants.  `fst` is two
inversions and a one-entry-free pair (the graph may be empty, so the
backward direction builds `pair A[σ] m []`).  `snd` is the lookup
unfolded, exactly as `beta` is for Π: forward, every entry's output is an
approximant of `b` and the joins go by `b`'s directedness; backward, the
single entry `(A[σ], a[σ], x, m)` carries the type witness that
`SoundTy b (B[a])` and `Interp.inst` supply. -/

/-- The first projection of a pair: the `pair_fst` case. -/
theorem sound_pair_fst {Γ : List Term} {A B a b : Term} {u : Bool}
    (hA : Γ ⊢ A : .sort u) (ha : Γ ⊢ a : A)
    (ihAty : SoundTy Γ A (.sort u)) (ihadom : SoundTy Γ a A) :
    SoundEq Γ (.fst (.pair A B a b)) a := by
  intro Δ σ ρ hAdm m
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  obtain ⟨n, s⟩ := m
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  constructor
  · intro h
    cases h with
    | bot => exact .bot
    | fst hp hle =>
      cases hp with
      | pair ha _ _ _ _ hwf' _ _ hle' =>
        exact ha.mono hΔ (hle.trans hΔ (TShape.LE.pair_decomp hΔ hle').2.2.1)
  · intro h
    -- the first component has to be hereditarily typed, so saturate it
    obtain ⟨⟨k, s'⟩, d, hs', hle', hd, hNV, hdc'⟩ := ihadom hAdm h
    by_cases hb : s'.IsBot
    · rw [show s = Shape.bot from
        TShape.le_bot hΔ (Shape.WF.eq_bot_of_isBot hs'.wf hb) hle']
      exact .bot
    · have hwf : Shape.WF (n := k+1) Δ
          (ShapeS.pair (A.subst σ) (a.subst σ) s' Shape.bot) :=
        ⟨fun hbb => hb hbb.1, IsDefEq.subst hΔ W ha, TyEq.refl hAσ, hs'.wf, Shape.WF.bot⟩
      exact .fst (.pair (c := TShape.bot) hs' .bot hd (ihAty.isType hAdm hd) ⟨hNV, hdc'⟩
        hwf
        .bot (TShape.Named.bot (TShape.HasType.bot_bot rfl)) (TShape.LE.refl hwf) ⟨u, hA⟩ ha)
        hle'

/-- The second projection of a pair: the `pair_snd` case. -/
theorem sound_pair_snd {Γ : List Term} {A B a b : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) (ha : Γ ⊢ a : A)
    (hPB : B.Pinned (A :: Γ))
    (hfst : Γ ⊢ .fst (.pair A B a b) ≡ a : A)
    (ihAty : SoundTy Γ A (.sort u)) (ihadom : SoundTy Γ a A)
    (ihbdom : SoundTy Γ b (B.inst a))
     :
    SoundEq Γ (.snd (.pair A B a b)) b := by
  have ihadir := (IsDefEq.dir hΓ ha).1
  intro Δ σ ρ hAdm m
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  obtain ⟨n, s⟩ := m
  have hwρ := hAdm.wf
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  have haσ : Δ ⊢ a.subst σ : A.subst σ := ha.subst hΔ W
  constructor
  · intro h
    cases h with
    | bot => exact .bot
    | snd hp _ hle =>
      -- the second component *is* an approximant of `b`
      cases hp with
      | pair _ hb _ _ _ _ _ _ hle' =>
        exact hb.mono hΔ (hle.trans hΔ (TShape.LE.pair_decomp hΔ hle').2.2.2)
  · intro h
    by_cases hb : s.IsBot
    · rw [Shape.WF.eq_bot_of_isBot (s := s) h.wf hb]; exact .bot
    · -- the first component is enlarged until it is hereditarily typed,
      -- which is what the clause's slot asks of it, and the second
      -- component comes with the code that types it
      obtain ⟨⟨nb, sb⟩, c, hmb, hmle, hc, hNV, _⟩ := ihbdom hAdm h
      have hdc := hNV.forget
      obtain ⟨x₀, hbody₀, hx₀⟩ :=
        (Interp.inst (A := A) (b := B) hΔ hΓ hA ha hB hPB W hAdm
          (Subst.Saturates.one hΓ hAdm hA ha ihadom)
          hwρ).1 hc
      obtain ⟨x, d, hx, hlex, hd, hNV, hdcx⟩ := ihadom hAdm hx₀
      have hbody : Interp Δ (A :: Γ) B ((Subst.one a).comp σ) (ρ.push x) c :=
        Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hlex⟩) hbody₀
      obtain ⟨k, hkx, hkn⟩ : ∃ k, x.1 ≤ k ∧ nb ≤ k :=
        ⟨max x.1 nb, Nat.le_max_left .., Nat.le_max_right ..⟩
      have hwx : Shape.WF Δ (x.2.lift k) := (Shape.lift_wf hkx).2 hx.wf
      have hws : Shape.WF Δ (sb.lift k) := (Shape.lift_wf hkn).2 hmb.wf
      have hnb : ¬ (sb.lift k).IsBot := fun hbb => hb (by
        rw [show s = Shape.bot from TShape.le_bot hΔ
          (Shape.WF.eq_bot_of_isBot hmb.wf ((Shape.lift_isBot hkn).1 hbb)) hmle]
        exact Shape.isBot_bot)
      have hwf : Shape.WF (n := k+1) Δ (ShapeS.pair (A.subst σ)
          (a.subst σ) (x.2.lift k) (sb.lift k)) :=
        ⟨fun hbb => hnb hbb.2, haσ, TyEq.refl hAσ, hwx, hws⟩
      have hbody' : Interp Δ (A :: Γ) B (σ.cons (a.subst σ))
          (ρ.push (Shape.T (x.2.lift k))) c := by
        refine Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
          TShape.LE.le_lift hΔ hkx hx.wf⟩) ?_
        rw [← Subst.one_comp]; exact hbody
      exact .snd (.pair (c := c) (Interp.lift hΔ hkx hx)
          (Interp.lift (m := ⟨nb, sb⟩) hΔ hkn hmb) hd (ihAty.isType hAdm hd)
          ⟨TShape.Named.lift_subject hΔ hNV hkx, hdcx⟩
          hwf hbody'
          (TShape.Named.lift_subject hΔ hdc hkn) (TShape.LE.refl hwf) ⟨u, hA⟩ ha)
        (IsDefEq.subst hΔ W hfst.symm)
        (TShape.LE.trans hΔ hmle (TShape.LE.le_lift (m := ⟨nb, sb⟩) hΔ hkn hmb.wf))
        (Stable.of_typed hfst.hasType.1 (TyEq.refl hAσ))

/-- **Saturation at a first projection.**  The pair's own saturation
puts its first component in `Named`'s Σ clause, and the projection reads
exactly that component. -/
theorem sound_fst_dom {Γ : List Term} {A B p : Term}
    (hpdom : SoundTy Γ p (.sigma A B)) : SoundTy Γ (.fst p) A := by
  intro Δ σ ρ hAdm m hm
  have hΔ := hAdm.ctx
  cases hm with
  | bot =>
    exact ⟨TShape.bot, TShape.bot, .bot, TShape.bot_le' rfl, .bot, (TShape.Named.bot (.bot (.bot .sort))), TShape.WF.bot⟩
  | fst hp hle =>
    obtain ⟨P', S, hP', hPle, hS, hNV, hScan⟩ := hpdom hAdm hp
    -- the code is a Σ-shape, since `P'` dominates a pair
    have hSsg : S.IsSigma := by
      rcases (show S.2 = Shape.bot ∨ S.IsSigma from by
          cases hS with
          | bot => exact .inl rfl
          | sigma _ _ _ _ _ hles _ _ => exact TShape.isSigma_or_bot_of_le hles trivial)
        with hb | h
      · exact absurd (TShape.le_bot hΔ (TShape.HasType.bot_r hΔ hb hNV.hasType) hPle)
          (by simp [Shape.bot])
      · exact h
    cases hNV with
    | base hnb _ _ => exact absurd hSsg.isBinder hnb
    | pi _ _ _ _ _ => exact absurd hSsg (TShape.IsPi.not_sigma trivial)
    | @sg _ nS A' B' dS fS _ ps cc hty hps _ hxd' hevc hout =>
      -- `P'` is a pair-shape; its first component is the projection's
      -- value, and `Named`'s Σ clause has it
      cases hty with
      | bot hb => exact absurd (TShape.le_bot hΔ rfl hPle) (by simp [Shape.bot])
      | refl hleid hAty' =>
        exact absurd hleid (by
          intro h
          obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ h
          exact absurd h2 (fun x => x))
      | @pair nP _ A₀' a₀' x' y' _ _ _ _ _ _ hd hfo hwP hwSg hxd hxle' hev' hyty hlabP =>
        obtain ⟨_, _, hxle, _⟩ := TShape.LE.pair_decomp hΔ hPle
        refine ⟨Shape.T x', dS.T, .fst hP'
            (TShape.LE.refl (TShape.WF.T.2 hwP.2.2.2.1)),
          TShape.LE.trans hΔ hle hxle, ?_, ?_, ?_⟩
        · -- the domain is an approximant of `A`
          cases hS with
          | @sigma _ _ _ _ nc gc dc _ _ hAint hdty hwfc _ hbodyc hleSg =>
            obtain ⟨_, hdle, _⟩ :=
              TShape.LE.sigma_decomp hΔ hleSg hwfc (TEvaluates.refl hwfc.2.2.2.1)
            exact Interp.mono hΔ hdle hAint
        · exact hxd' _ (by rw [← hps]; rfl)
        · -- and names `A`: the code names its own domain label, which the
          -- order identifies with the syntactic one
          cases hS with
          | @sigma _ _ _ _ nc gc dc _ _ hAint hdty hwfc _ hbodyc hleSg =>
            obtain ⟨hPL, _, _⟩ :=
              TShape.LE.sigma_decomp hΔ hleSg hwfc (TEvaluates.refl hwfc.2.2.2.1)
            exact Shape.WF.conv hwSg.2.2.1 (TyEq.symm hPL.1)

/-- Soundness for `fstDF`. -/
theorem sound_fst {Γ : List Term} {A B p p' : Term}
    (ihe : SoundEq Γ p p') (ihty : SoundTy Γ p (.sigma A B)) :
    SoundEq Γ (.fst p) (.fst p') ∧ TypedAt Γ (.fst p) A := by
  constructor
  · intro Δ σ ρ hAdm m
    have hΔ := hAdm.ctx
    have W := hAdm.stage
    constructor
    · intro h
      cases h with
      | bot => exact .bot
      | fst hp hle => exact .fst ((ihe hAdm).1 hp) hle
    · intro h
      cases h with
      | bot => exact .bot
      | fst hp hle => exact .fst ((ihe hAdm).2 hp) hle
  · intro Δ σ ρ hAdm m hm
    have hΔ := hAdm.ctx
    cases hm with
    | bot => exact ⟨TShape.bot, .bot, .bot (.bot .sort)⟩
    | fst hp hle =>
      obtain ⟨s, hs, hty⟩ := ihty.approx hAdm hp
      cases hty with
      | pair _ _ _ hwSg hxd _ _ _ _ =>
        cases hs with
        | sigma hA hd₀ hwf _ _ hleS =>
          obtain ⟨_, hdd, _⟩ :=
            TShape.LE.sigma_decomp hΔ hleS hwf (TEvaluates.refl hwf.2.2.2.1)
          exact ⟨_, hA, TShape.HasType.mono_r hΔ
            (TShape.HasType.mono_l hΔ hxd hle) _ hdd hd₀⟩

/-- **The Σ-approximant read off a pair-approximant.**  Unlike the λ
case there is no graph to rebuild: `Interp.pair` already carries a code
for every entry.  This is the Σ-shape whose domain is the clause's own
domain slot joined with a code for `a`, and whose graph has one entry
per code; `sound_pair_ty` reads the typing off it, `sound_pair_dom` the
hereditary typing. -/
theorem pair_sigma_code {Γ Δ : List Term} {A B a : Term} {u v : Bool} {σ ρ}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v)
    (ihAty : SoundTy Γ A (.sort u))
    (ihaty : SoundTy Γ a A)
    (ihBty : SoundTy (A :: Γ) B (.sort v))
    (hAdm : Adm Δ Γ σ ρ)
    {n} {x y : Shape n} {d c : TShape}
    (ha : Interp Δ Γ a σ ρ (Shape.T x)) (hA : Interp Δ Γ A σ ρ d)
    (hd : TShape.HasType Δ d TShape.type)
    (hNV : TShape.Named Δ d (Shape.T x) (a.subst σ))
    (hdc : TShape.WF Δ d (A.subst σ))
    (hwp : Shape.WF (n := n+1) Δ (.pair (A.subst σ) (a.subst σ) x y))
    (hcode : Interp Δ (A :: Γ) B (σ.cons (a.subst σ)) (ρ.push (Shape.T x)) c)
    (hcty : TShape.Named Δ c (Shape.T y) ob) :
    ∃ (k : Nat) (dk : Shape k) (f : ShapeFun k),
      Interp Δ Γ (.sigma A B) σ ρ
        (Shape.T (n := k+1) (.sigma (A.subst σ) (B.subst σ.lift) dk f)) ∧
      TShape.HasType Δ (Shape.T (n := n+1) (.pair (A.subst σ) (a.subst σ) x y))
        (Shape.T (n := k+1) (.sigma (A.subst σ) (B.subst σ.lift) dk f)) ∧
      TShape.HasType Δ (Shape.T dk) TShape.type ∧
      TShape.Named Δ (Shape.T dk) (Shape.T x) (a.subst σ) ∧
      (∃ cc, TEvaluates Δ f (A.subst σ) (a.subst σ) (Shape.T x) cc ∧
        TShape.HasType Δ cc TShape.type ∧ TShape.Named Δ cc (Shape.T y) ob) ∧
      TShape.WF Δ (Shape.T (n := k+1) (.sigma (A.subst σ) (B.subst σ.lift) dk f)) ((Term.sigma A B).subst σ) := by
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have ihAc := ihAty.codeAt
  have ihBc := ihBty.codeAt
  have ihAdir := (IsDefEq.dir hΓ hAty).1
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hAty⟩
  have ihBdir := (IsDefEq.dir hΓA hB).1
  have hwρ := hAdm.wf
  have hAσ : Δ ⊢ A.subst σ : .sort u := hAty.subst hΔ W
  have hΔA : ⊢ (A.subst σ :: Δ) := ⟨hΔ, _, hAσ⟩
  -- the pair's own stage is admissible
  have hstage : Ctx.SubstEq Δ (σ.cons (a.subst σ)) (σ.cons (a.subst σ)) (A :: Γ) ∧
      Adm Δ (A :: Γ) (σ.cons (a.subst σ)) (ρ.push (Shape.T x)) :=
    ⟨.cons W hAty hwp.2.1,
      .cons hAdm (.cons W hAty hwp.2.1) W.wf hA ⟨hNV, hdc⟩⟩
  -- the first component, typed at a domain shape joined with the clause's
  obtain ⟨c₀, hc₀, hxc₀⟩ := ihaty.approx hAdm ha
  obtain ⟨hcd, hdj⟩ := ihAdir.join hΔ W hwρ hA hc₀
  have hdjty : TShape.HasType Δ (d.join c₀) TShape.type :=
    TShape.HasType.join_sort' hΔ rfl hd (ihAty.isType hAdm hc₀) hcd
  obtain ⟨hled, hlec⟩ := TShape.le_join hΔ hA.wf hc₀.wf hcd
  -- one level for the code, the joined domain and the single entry
  obtain ⟨k, hkn, hkd, hkc⟩ : ∃ k, n ≤ k ∧ (d.join c₀).1 ≤ k ∧ c.1 ≤ k :=
    ⟨max n (max (d.join c₀).1 c.1), Nat.le_max_left ..,
      Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..),
      Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..)⟩
  have hcwf : TShape.WF Δ c := hcode.wf
  -- the Σ-code's graph: the pair's own name, first component and code
  let f : ShapeFun k := [⟨a.subst σ, x.lift k, c.2.lift k⟩]
  have hfmem : ∀ e ∈ f, e = (⟨a.subst σ, x.lift k, c.2.lift k⟩ :
      Entry (Shape k)) := by
    intro e he
    simpa [f] using he
  have hdty : TShape.HasType Δ (Shape.T ((d.join c₀).2.lift k)) TShape.type :=
    hdjty.lift_subject hΔ hkd
  have hdle : TShape.LE Δ (d.join c₀) (Shape.T ((d.join c₀).2.lift k)) :=
    TShape.LE.le_lift hΔ (m := d.join c₀) hkd hdjty.wf.1
  have hcodety : TShape.HasType Δ c TShape.type :=
    ihBty.isType hstage.2 hcode
  have hcodety' : TShape.HasType Δ (Shape.T (c.2.lift k)) TShape.type :=
    hcodety.lift_subject hΔ hkc
  have hfent : ∀ e ∈ f, (∃ u, Δ ⊢ A.subst σ : .sort u) ∧ Δ ⊢ e.tm : A.subst σ ∧
      Shape.WF Δ e.inp ∧ Shape.WF Δ e.out := by
    intro e he
    rw [hfmem e he]
    exact ⟨⟨u, hAσ⟩, hwp.2.1, (Shape.lift_wf hkn).2 hwp.2.2.2.1,
      (Shape.lift_wf hkc).2 hcwf⟩
  have hfdom : ∀ e ∈ f,
      TShape.Named Δ (Shape.T ((d.join c₀).2.lift k)) e.inp.T e.tm := by
    intro e he
    rw [hfmem e he]
    exact TShape.Named.mono_r hΔ
      (TShape.Named.lift_subject hΔ (TShape.Named.mono_r hΔ hNV hled hdjty) hkn) hdle hdty
  have hfbody : ∀ e ∈ f,
      Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push e.inp.T) e.out.T := by
    intro e he
    rw [hfmem e he]
    refine Interp.mono hΔ 
      (TShape.LE.lift_le hΔ (m := c) hkc hcwf) ?_
    exact Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
      TShape.LE.le_lift hΔ (m := Shape.T x) hkn (TShape.WF.T.2 hwp.2.2.2.1)⟩) hcode
  have hcdSg : Shape.WF Δ ((d.join c₀).2.lift k) (A.subst σ) :=
    (Shape.lift_wf hkd).2
      (TShape.WF.join hΔ hcd hdc (ihAc hAdm hc₀))
  have hcfSg : ∀ e ∈ f, Shape.WF Δ e.out ((B.subst σ.lift).inst e.tm) := by
    intro e he
    rw [hfmem e he]
    have hcc := ihBc hstage.2 hcode
    rw [← inst_lift_cons] at hcc
    exact (Shape.lift_wf hkc).2 hcc
  have hwfSg : Shape.WF (n := k+1) Δ
      (.sigma (A.subst σ) (B.subst σ.lift) ((d.join c₀).2.lift k) f) :=
    ⟨⟨u, hAσ⟩, ⟨v, hB.subst hΔA (W.lift hAty hAσ)⟩,
      hcdSg,
      ShapeFun.WF.name
        ⟨fun e he => hfent e he,
         graph_coherent hΓ hAty hB W hwρ (fun e he => (hfent e he).2.2.1)
           hfbody⟩ hcfSg, trivial⟩
  have hSg : Interp Δ Γ (.sigma A B) σ ρ
      (Shape.T (n := k+1) (.sigma (A.subst σ) (B.subst σ.lift) ((d.join c₀).2.lift k) f)) :=
    .sigma (Interp.mono hΔ 
        (TShape.LE.lift_le hΔ (m := d.join c₀) hkd hdjty.wf.1) hdj)
      hdty hwfSg
      (fun e he => by
        exact hfdom _ he)
      hfbody (TShape.LE.refl hwfSg) ⟨u, hAty⟩ ⟨v, hB⟩
  -- the code is the lookup at the pair's own name and first component
  have hlook : TEvaluates Δ f (A.subst σ) (a.subst σ) (Shape.T x)
      (Shape.T (c.2.lift k)) :=
    TEvaluates.entry _ (List.mem_cons_self) ⟨TyEq.refl hAσ, hwp.2.1⟩
      (TShape.LE.lift_le hΔ (m := Shape.T x) hkn (TShape.WF.T.2 hwp.2.2.2.1))
  refine ⟨k, (d.join c₀).2.lift k, f, hSg,
    TShape.HasType.pair hdty (fun e he => by rw [hfmem e he]; exact hcodety') hwp hwfSg
      (TShape.HasType.mono_r hΔ (TShape.HasType.mono_r hΔ hxc₀ _ hlec hdjty) _ hdle hdty)
      (TShape.LE.refl (TShape.WF.T.2 hwp.2.2.2.1)) hlook
      (TShape.HasType.mono_r hΔ (TShape.Named.hasType hcty) _
        (TShape.LE.le_lift hΔ (m := c) hkc hcwf) hcodety')
      (TyEq.refl hAσ),
    hdty,
    TShape.Named.mono_r hΔ (TShape.Named.mono_r hΔ hNV hled hdjty) hdle hdty,
    ⟨_, hlook, hcodety',
      TShape.Named.mono_r hΔ hcty (TShape.LE.le_lift hΔ (m := c) hkc hcwf) hcodety'⟩, ?_⟩
  -- the Σ-code names `Σ A B`: its domain joins two approximants of `A`,
  -- and its one entry is an approximant of `B` at the pair's own name
  exact ⟨hwfSg.1, hwfSg.2.1, hwfSg.2.2.1, hwfSg.2.2.2.1,
    ⟨true, (IsDefEq.sigmaDF hAty hB hB).subst hΔ W⟩⟩

/-- Building a `TShape.LE` between two pair shapes at different levels. -/
theorem TShape.LE.pair_mk {Δ : List Term} {n k} {A a A' a' : Term}
    {x y : Shape n} {x' y' : Shape k} (hΔ : ⊢ Δ)
    (hx : TShape.LE Δ (Shape.T x) (Shape.T x')) (hy : TShape.LE Δ (Shape.T y) (Shape.T y'))
    (hnd : ¬ (x.IsBot ∧ y.IsBot)) (hA : TyEq Δ A A') (ha : Δ ⊢ a ≡ a' : A) :
    TShape.LE Δ (Shape.T (n := n+1) (ShapeS.pair A a x y))
      (Shape.T (n := k+1) (ShapeS.pair A' a' x' y')) := by
  refine (TShape.LE.def hΔ (Nat.succ_le_succ (Nat.le_max_left n k))
    (Nat.succ_le_succ (Nat.le_max_right n k))).2 ?_
  refine ⟨(TShape.LE.def hΔ (Nat.le_max_left n k) (Nat.le_max_right n k)).1 hx,
    (TShape.LE.def hΔ (Nat.le_max_left n k) (Nat.le_max_right n k)).1 hy, ?_, hA, ha⟩
  exact fun hb => hnd ⟨(Shape.lift_isBot (Nat.le_max_left n k)).1 hb.1,
    (Shape.lift_isBot (Nat.le_max_left n k)).1 hb.2⟩

/-- **Saturation at a pair.**  A pair-approximant's second component is
an arbitrary approximant of `b`, so the dominator is rebuilt: `b`'s own
saturation enlarges it, `Interp.inst` reads its code as `B` at a slot
approximating `a`, that slot is joined with the given first component,
and `a`'s saturation enlarges the join.  The rebuilt pair names its own
projections because both components do, moved along `pair_fst`/`pair_snd`;
its code is `pair_sigma_code`'s. -/
theorem sound_pair_dom {Γ : List Term} {A B a b : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hAty : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v)
    (hat : Γ ⊢ a : A) (hbt : Γ ⊢ b : B.inst a) (hPB : B.Pinned (A :: Γ))
    (ihAty : SoundTy Γ A (.sort u))
    (ihaty : SoundTy Γ a A)
    (ihbdom : SoundTy Γ b (B.inst a))
    (ihBty : SoundTy (A :: Γ) B (.sort v))
     :
    SoundTy Γ (.pair A B a b) (.sigma A B) := by
  have ihBc := ihBty.codeAt
  have ihAdir := (IsDefEq.dir hΓ hAty).1
  have ihadir := (IsDefEq.dir hΓ hat).1
  have ihBdir := (IsDefEq.dir (show ⊢ (A :: Γ) from ⟨hΓ, _, hAty⟩) hB).1
  intro Δ σ ρ hAdm m hm
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have hwρ := hAdm.wf
  have hAσ : Δ ⊢ A.subst σ : .sort u := hAty.subst hΔ W
  cases hm with
  | bot => exact ⟨TShape.bot, TShape.bot, .bot, TShape.bot_le' rfl, .bot, (TShape.Named.bot (.bot (.bot .sort))), TShape.WF.bot⟩
  | @pair _ _ _ _ n x y d c _ _ _ _ ha hb hA hd hslotp hwp hcode hcty hle hAt hat' =>
    -- the second component, saturated, with its code
    obtain ⟨y', cb, hy', hyle, hcb, hNV, hcbc⟩ := ihbdom hAdm hb
    have hdy' := hNV
    -- that code is `B` read at a slot approximating `a`
    obtain ⟨x₀, hbody₀, hx₀⟩ :=
      (Interp.inst (A := A) (b := B) hΔ hΓ hAty hat hB hPB W hAdm
        (Subst.Saturates.one hΓ hAdm hAty hat ihaty)
        hwρ).1 hcb
    -- joined with the given first component, then saturated
    obtain ⟨x₁, _, hx₁, hxx₁, hx₀x₁⟩ := ihadir hΔ W hwρ ha hx₀
    obtain ⟨x', d', hx', hx₁x', hd', hNV, hd'c⟩ := ihaty hAdm hx₁
    have hdx' := hNV
    have hd'ty : TShape.HasType Δ d' TShape.type := ihAty.isType hAdm hd'
    -- one level for both components
    obtain ⟨k, hkx, hky⟩ : ∃ k, x'.1 ≤ k ∧ y'.1 ≤ k :=
      ⟨max x'.1 y'.1, Nat.le_max_left .., Nat.le_max_right ..⟩
    have hwx' : Shape.WF Δ (x'.2.lift k) := (Shape.lift_wf hkx).2 hx'.wf
    have hwy' : Shape.WF Δ (y'.2.lift k) := (Shape.lift_wf hky).2 hy'.wf
    have hxle : TShape.LE Δ (Shape.T x) (Shape.T (x'.2.lift k)) :=
      (hxx₁.trans hΔ hx₁x').trans hΔ (TShape.LE.le_lift hΔ hkx hx'.wf)
    have hyle' : TShape.LE Δ (Shape.T y) (Shape.T (y'.2.lift k)) :=
      hyle.trans hΔ (TShape.LE.le_lift hΔ hky hy'.wf)
    -- the rebuilt pair is not information-free, since the given one is not
    have hnb : ¬ ((x'.2.lift k).IsBot ∧ (y'.2.lift k).IsBot) := by
      rintro ⟨hbx, hby⟩
      refine hwp.1 ⟨?_, ?_⟩
      · have hx0 : x = Shape.bot := TShape.le_bot hΔ (Shape.WF.eq_bot_of_isBot hwx' hbx) hxle
        rw [hx0]; exact Shape.isBot_bot
      · have hy0 : y = Shape.bot := TShape.le_bot hΔ (Shape.WF.eq_bot_of_isBot hwy' hby) hyle'
        rw [hy0]; exact Shape.isBot_bot
    have hwP : Shape.WF (n := k+1) Δ
        (ShapeS.pair (A.subst σ) (a.subst σ) (x'.2.lift k) (y'.2.lift k)) :=
      ⟨hnb, hwp.2.1, hwp.2.2.1, hwx', hwy'⟩
    have hcodeL : Interp Δ (A :: Γ) B (σ.cons (a.subst σ))
        (ρ.push (Shape.T (x'.2.lift k))) cb := by
      have h := Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
        (hx₀x₁.trans hΔ hx₁x').trans hΔ (TShape.LE.le_lift hΔ hkx hx'.wf)⟩) hbody₀
      rwa [Subst.one_comp] at h
    have hdxL : TShape.Named Δ d' (Shape.T (x'.2.lift k)) (a.subst σ) :=
      TShape.Named.lift_subject hΔ hdx' hkx
    have hdyL : TShape.Named Δ cb (Shape.T (y'.2.lift k)) (b.subst σ) :=
      TShape.Named.lift_subject hΔ hdy' hky
    have hP : Interp Δ Γ (.pair A B a b) σ ρ
        (Shape.T (n := k+1) (ShapeS.pair (A.subst σ) (a.subst σ) (x'.2.lift k) (y'.2.lift k))) :=
      .pair (Interp.lift hΔ hkx hx') (Interp.lift hΔ hky hy') hd' hd'ty ⟨hdxL, hd'c⟩ hwP
        hcodeL hdyL.forget (TShape.LE.refl (TShape.WF.T.2 hwP)) hAt hat'
    have hPle := TShape.LE.pair_mk hΔ hxle hyle' hwp.1 (TyEq.refl hAσ) hwp.2.1
    obtain ⟨kS, dS, fS, hSg, hty, _, hdfst, ⟨cc, hlook, _, hccdom⟩, hScan⟩ :=
      pair_sigma_code hΓ hAty hB ihAty ihaty ihBty hAdm
        (Interp.lift hΔ hkx hx') hd' hd'ty hdxL hd'c hwP hcodeL hdyL
    -- the two β-rules, at the stage
    have hfst : Δ ⊢ (Term.fst (.pair A B a b)).subst σ ≡ a.subst σ : A.subst σ :=
      (IsDefEq.pair_fst₀ hΓ hB hat hbt).subst hΔ W
    have hsnd : Δ ⊢ (Term.snd (.pair A B a b)).subst σ ≡ b.subst σ : (B.inst a).subst σ :=
      (IsDefEq.pair_snd₀ hΓ hB hat hbt).subst hΔ W
    exact ⟨_, _, hP, hle.trans hΔ hPle, hSg,
      .sg (ps := some (a.subst σ, Shape.T (x'.2.lift k), Shape.T (y'.2.lift k)))
        (c := cc) hty rfl
        (fun p hp u hu => by
          cases hp
          simp only [Option.mem_def, Option.some.injEq] at hu
          subst hu; exact hfst.symm)
        (fun p hp => by
          cases hp
          simpa using hdfst.defeq hΔ hScan.2.2.1 hfst.symm)
        (fun p hp => by cases hp; exact hlook)
        (fun p hp => by
          cases hp
          have hlk : TShape.WF Δ cc ((B.subst σ.lift).inst (a.subst σ)) :=
            have ⟨_, hBσ'⟩ := hScan.2.1
            TShape.WF.lookup hΔ hScan.2.2.2.1 (ShapeFun.WF.canon hScan.2.2.2.1)
              hAσ hBσ' hlook
          have h := hccdom.defeq hΔ hlk (by simpa [subst_inst] using hsnd.symm)
          simpa using h),
      hScan⟩

/-- One direction of the `SoundEq` half of `pairDF`.  A pair-shape's only
label is its domain, and its entries' label terms name the *first
component*, so the two things that move are that label (up to `TyEq`, as
at λ) and those terms (along `a ≡ a'`, at the entry's own type).  The
codomain's values do not move at all: their stage is the entry's label
term, which is unchanged. -/
theorem sound_pair_eq_of {Γ : List Term} {A A' B B' a a' b b' : Term} {u v : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (haa' : Γ ⊢ a ≡ a' : A)
    (hB'ty : A' :: Γ ⊢ B' ≡ B' : .sort v)
    (ihA : SoundEq Γ A A')
    (iha : SoundEq Γ a a') (ihb : SoundEq Γ b b') (ihB : SoundEq (A :: Γ) B B')
    {Δ : List Term} {σ ρ} (hAdm : Adm Δ Γ σ ρ)
    {m : TShape} (H : Interp Δ Γ (.pair A B a b) σ ρ m) :
    Interp Δ Γ (.pair A' B' a' b') σ ρ m := by
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have hAσ : TyEq Δ (A.subst σ) (A'.subst σ) := ⟨u, hAA'.subst hΔ W⟩
  have haσ : Δ ⊢ a.subst σ ≡ a'.subst σ : A.subst σ := haa'.subst hΔ W
  cases H with
  | bot => exact .bot
  | @pair _ _ _ _ n x y d c _ _ _ _ ha hb hA hd hslot hwp hcode hcty hle hAt hat =>
    have hwp' : Shape.WF (n := n+1) Δ
        (ShapeS.pair (A'.subst σ) (a'.subst σ) x y) :=
      ⟨hwp.1, hAσ.defeqDF (haσ.symm.trans haσ), TyEq.refl_r hAσ,
        hwp.2.2.2.1, hwp.2.2.2.2⟩
    have W' : Ctx.SubstEq Δ (σ.cons (a.subst σ)) (σ.cons (a.subst σ)) (A :: Γ) :=
      .cons W hAA'.hasType.1 hwp.2.1
    have hAdm' : Adm Δ (A :: Γ) (σ.cons (a.subst σ)) (ρ.push (Shape.T x)) :=
      .cons hAdm W' W.wf hA
        hslot
    -- the codomain's value, at the pair's own name moved along `a ≡ a'`
    have hcode' : Interp Δ (A' :: Γ) B' (σ.cons (a.subst σ)) (ρ.push (Shape.T x)) c :=
      Interp.ctx ((ihB hAdm').1 hcode)
        (show ⊢ (A' :: Γ) from ⟨W.wf, _, hAA'.hasType.2⟩)
        (Ctx.SubstEq.defeqHead W.wf hAA') Lookup.cons_head
    have hcode'' : Interp Δ (A' :: Γ) B' (σ.cons (a'.subst σ)) (ρ.push (Shape.T x)) c :=
      IsDefEq.stage (show ⊢ (A' :: Γ) from ⟨W.wf, _, hAA'.hasType.2⟩) hB'ty hΔ
        (Ctx.SubstEq.cons (σ := σ.cons (a.subst σ)) (σ' := σ.cons (a'.subst σ)) W
          hAA'.hasType.2 (hAσ.defeqDF haσ)) hcode'
    exact .pair ((iha hAdm).1 ha) ((ihb hAdm).1 hb) ((ihA hAdm).1 hA)
      hd ((hslot.defeq hΔ haσ).conv (TyEq.symm hAσ)) hwp' hcode'' hcty 
      (hle.trans hΔ (TShape.LE.T.2 (show Shape.LE (n := n+1) Δ (ShapeS.pair ..)
        (ShapeS.pair ..) from
        ⟨Shape.LE.refl hwp.2.2.2.1, Shape.LE.refl hwp.2.2.2.2, hwp.1, hAσ, haσ⟩)))
      ⟨u, hAA'.hasType.2⟩ (hAA'.defeqDF (haa'.hasType.2))

/-- The `SoundEq` half of `pairDF`. -/
theorem sound_pair_eq {Γ : List Term} {A A' B B' a a' b b' : Term} {u v : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (haa' : Γ ⊢ a ≡ a' : A)
    (hBty : A :: Γ ⊢ B ≡ B : .sort v) (hB'ty : A' :: Γ ⊢ B' ≡ B' : .sort v)
    (ihA : SoundEq Γ A A')
    (iha : SoundEq Γ a a') (ihb : SoundEq Γ b b')
    (ihB : SoundEq (A :: Γ) B B') (ihB' : SoundEq (A' :: Γ) B B') :
    SoundEq Γ (.pair A B a b) (.pair A' B' a' b') := by
  intro Δ σ ρ hAdm m
  exact ⟨sound_pair_eq_of hAA' haa' hB'ty ihA iha ihb ihB hAdm,
    sound_pair_eq_of hAA'.symm (hAA'.defeqDF haa'.symm)
      hBty
      ihA.symm iha.symm ihb.symm ihB'.symm hAdm⟩

/-! ## The second projection

`Interp.snd` is a query at `fst p` (§4.7a), so the codomain family's
lookup that types the second component is at that label, and the value
read off is an approximant of `B[fst p]` — provided the query's *type* is
the Σ's domain.  That is what the typed approximant gives: the Σ-shape's
graph labels are all `≡ A[σ]`, and a lookup that reaches a non-`⊥` output
went through one of them.

`sound_graph_lookup` is `sound_beta_lookup` for a codomain graph, Π's or
Σ's: every lookup in it at a label of the domain's type is an approximant
of the codomain at that label, each entry moved there by `IsDefEq.stage`
along its own label equation and the joins by the codomain's
directedness. -/
theorem sound_graph_lookup {Γ Δ : List Term} {A B : Term} {σ ρ} {u : Bool}
    (hΓA : ⊢ (A :: Γ)) (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v)
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ)
    {n} {g : ShapeFun n}
    (hbody : ∀ e ∈ g, Interp Δ (A :: Γ) B (σ.cons e.tm) (ρ.push e.inp.T) e.out.T)
    {ty tm : Term} {x : TShape} (hx : TShape.WF Δ x)
     (hwρ : Valuation.WF Δ Γ ρ)
    (hq : Δ ⊢ tm : ty) (hty : TyEq Δ ty (A.subst σ)) :
    ∀ {c : TShape}, TEvaluates Δ g ty tm x c →
      Interp Δ (A :: Γ) B (σ.cons tm) (ρ.push x) c := by
  have hdir := (IsDefEq.dir hΓA hB).1
  have Wtm : Ctx.SubstEq Δ (σ.cons tm) (σ.cons tm) (A :: Γ) :=
    .cons W hA (hty.defeqDF hq)
  intro c hc
  induction hc with
  | bot => exact .bot
  | @entry ej hej hlabj hin =>
    obtain ⟨_, htmj⟩ := hlabj
    have Wcons : Ctx.SubstEq Δ (σ.cons ej.tm) (σ.cons tm) (A :: Γ) :=
      .cons W hA (hty.defeqDF htmj)
    exact Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hin⟩)
      (IsDefEq.stage hΓA hB hΔ Wcons (hbody ej hej))
  | lower hle' _ ih => exact ih.mono hΔ hle'
  | join _ _ _ ih₁ ih₂ =>
    exact (hdir.join hΔ Wtm (Valuation.WF.push hwρ hx) ih₁ ih₂).2

/-- Directedness of an instantiation, from the two terms' own.

`Interp.inst` reads an approximant of `b[a]` as an approximant of `b` at a
slot approximating `a`, so two of them go to one slot by `a`'s
directedness and then to one shape by `b`'s.  Needed at `beta` (the
lookup's `join` rule lands on two approximants of `b[a]`) and at
`Y_unfold`. -/
theorem dir_inst {Γ Δ : List Term} {A a b B : Term} {u : Bool} {σ ρ}
    (hA : Γ ⊢ A : .sort u) (ha : Γ ⊢ a : A) (hb : A :: Γ ⊢ b : B)
    (hPb : b.Pinned (A :: Γ)) (hAdm : Adm Δ Γ σ ρ) (hΓ : ⊢ Γ) (hadom : SoundTy Γ a A)
      :
    -- `SoundDir` is out of reach here: `Interp.inst` needs `Subst.Saturates`,
    -- which needs `Adm` at the stage, and `SoundDir` offers only
    -- `Valuation.WF` at an arbitrary one.  So this is `SoundDir`'s body at
    -- the one stage we have.
    ∀ {{m₁ m₂}}, Interp Δ Γ (b.inst a) σ ρ m₁ → Interp Δ Γ (b.inst a) σ ρ m₂ →
      ∃ s, TShape.WF Δ s ∧ Interp Δ Γ (b.inst a) σ ρ s ∧
        TShape.LE Δ m₁ s ∧ TShape.LE Δ m₂ s := by
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have iha := (IsDefEq.dir hΓ ha).1
  have ihb := (IsDefEq.dir (show ⊢ (A :: Γ) from ⟨hΓ, _, hA⟩) hb).1
  have hwρ : Valuation.WF Δ Γ ρ := hAdm.wf
  intro m₁ m₂ h₁ h₂
  have hinst : ∀ {m : TShape}, Interp Δ Γ (b.inst a) σ ρ m ↔
      ∃ x, Interp Δ (A :: Γ) b ((Subst.one a).comp σ) (ρ.push x) m ∧
        Interp Δ Γ a σ ρ x := fun {_} =>
    Interp.inst hΔ W.wf hA ha hb hPb W hAdm
      (Subst.Saturates.one hΓ hAdm hA ha hadom) hwρ
  obtain ⟨x₁, hb₁, hx₁⟩ := hinst.1 h₁
  obtain ⟨x₂, hb₂, hx₂⟩ := hinst.1 h₂
  obtain ⟨x, hwx, hx, hxle₁, hxle₂⟩ := iha hΔ W hwρ hx₁ hx₂
  have W' : Ctx.SubstEq Δ ((Subst.one a).comp σ) ((Subst.one a).comp σ) (A :: Γ) := by
    rw [Subst.one_comp]; exact .cons W hA (ha.subst hΔ W)
  obtain ⟨s, hws, hs, hs₁, hs₂⟩ := ihb hΔ W' (Valuation.WF.push hwρ hwx)
    (Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hxle₁⟩) hb₁)
    (Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hxle₂⟩) hb₂)
  exact ⟨s, hws, hinst.2 ⟨x, hs, hx⟩, hs₁, hs₂⟩

/-! ## The type of an application

An approximant of `app f a` is below a lookup in the function's λ-shape at
the argument's label; `HasType.lam` covers that graph by its generator
`g₀`, whose entries' codes are lookups in the Π-shape's graph; and that
graph is covered by the canonical Π-shape's, whose outputs are the
codomain's interpretations.  So each code is a lookup in the canonical
graph at the canonical query, which `sound_graph_lookup` turns into an
approximant of `B` at the stage extended by `a[σ]`, and `Interp.inst`
into one of `B[a]`.

The slot works out, and this is where Π differs from Σ (§4.7b): the
generator sits *below* the λ-entry's input — coverage is a lookup at the
entry's own input — and that input is below the argument's shape, so the
slot the code is read at approximates `a`.  The `pair` clause's dominator
sits above, which is why the same argument does not run at `snd`.

The `join` rule of the lookup lands on two typed shapes, and typing their
join is exactly `SoundJoin` (§5.1) — not only `tr`'s business, as the plan
had it, but every consumer's of a relational lookup.  It is `sound_join`,
proved once and for all. -/

/-! ## The `app` label

`Interp.app` looks the argument up at the λ-shape's own domain label, so
the query type is pinned at every well-formed valuation: every entry's type
is that label, by `Shape.WF`.  What typing adds, at an admissible stage, is
that the label is the *syntactic* domain `A[σ]` of the function's Π-type:
`HasType.lam` requires the label to agree with the Π-shape's domain, and
the Π-shape approximating `Π A B` is labelled by `A[σ]`.  This is the η
condition of §4.5: a slot of type `Π A B` holds only λ-shapes labelled by
(something definitionally equal to) `A[σ]`, as `λ A (f↑ 0)` is. -/
theorem Interp.lam_label_ty {Γ Δ : List Term} {f A B : Term} {σ ρ}
    (hAdm : Adm Δ Γ σ ρ)
    (hty : SoundTy Γ f (.forallE A B))
    {n} {A' : Term} {g : ShapeFun n}
    (hf : Interp Δ Γ f σ ρ (Shape.T (n := n+1) (ShapeS.lam A' g))) :
    TyEq Δ A' (A.subst σ) := by
  have hΔ := hAdm.ctx
  obtain ⟨s, hs, hsty⟩ := hty.approx hAdm hf
  cases hsty with
  | lam _ _ _ hwPi _ _ _ _ hdom =>
    cases hs with
    | forallE _ _ hwf _ _ hle =>
      obtain ⟨hPi, _, _⟩ :=
        TShape.LE.forallE_decomp hΔ hle hwf (TEvaluates.refl hwf.2.2.2.1)
      exact TyEq.trans hdom hPi.1

/-- `Term.Pinned`'s `app` condition, from the function's own typing: the
λ-shape's label is the Π's domain, and the argument is typed there. -/
theorem PinApp.of_sound {Γ : List Term} {A B f a : Term}
    (hf : SoundTy Γ f (.forallE A B)) (ha : Γ ⊢ a : A) : PinApp Γ f a := by
  intro Δ σ ρ n A' g hAdm hF
  exact Stable.of_typed ha (Interp.lam_label_ty hAdm hf hF)

/-- **Saturation at an application.**  The function's own saturation
gives a λ-approximant whose entries' *outputs* are hereditarily typed at
the codomain read there — `Named`'s second Π condition, and the reason it
is there — so the lookup's value is below one that is, the `lower` rule
being why this is up to the order and the `join` rule why the codes have
to join (`SoundJoin`, `dir_inst`). -/
theorem sound_app_dom {Γ : List Term} {A B f a : Term} {u v : Bool}
    (hPB : B.Pinned (A :: Γ))
    (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) (ha : Γ ⊢ a : A) (hadom : SoundTy Γ a A)
    (hft : Γ ⊢ f : .forallE A B) (hfty : SoundTy Γ f (.forallE A B))
    (hBaty : SoundTy Γ (B.inst a) (.sort v))
      :
    SoundTy Γ (.app f a) (B.inst a) := by
  have hadir := (IsDefEq.dir hΓ ha).1
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
  have hBdir := (IsDefEq.dir hΓA hB).1
  intro Δ σ ρ hAdm m hm
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have hwρ := hAdm.wf
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  have haσ : Δ ⊢ a.subst σ : A.subst σ := ha.subst hΔ W
  cases hm with
  | bot => exact ⟨TShape.bot, TShape.bot, .bot, TShape.bot_le' rfl, .bot, (TShape.Named.bot (.bot (.bot .sort))), TShape.WF.bot⟩
  | @app _ _ _ _ _ _ n g x y A₁ hF hx hev hle hst =>
    -- saturate the function
    obtain ⟨F', P, hF', hFle, hP, hNV, hPc⟩ := hfty hAdm hF
    -- its code is a Π-shape: `F'` dominates a λ-shape, so neither is `⊥`
    have hPpi : P.IsPi := by
      rcases (show P.2 = Shape.bot ∨ P.IsPi from by
          cases hP with
          | bot => exact .inl rfl
          | forallE _ _ _ _ _ hlep _ _ => exact TShape.isPi_or_bot_of_le hlep trivial)
        with hb | h
      · exact absurd (TShape.le_bot hΔ (TShape.HasType.bot_r hΔ hb hNV.hasType) hFle)
          (by simp [Shape.bot])
      · exact h
    cases hNV with
    | base hnb _ => exact absurd hPpi.isBinder hnb
    | sg _ _ _ _ _ => exact absurd trivial hPpi.not_sigma
    | @pi _ nP A' B' dP fP _ cs hty hent hin hevc hout =>
      -- the saturated function is a λ-shape, and the code's codomain
      -- graph is covered by the canonical one
      cases hty with
      | bot hb =>
        exact absurd (TShape.le_bot hΔ rfl hFle) (by simp [Shape.bot])
      | refl hleid hAty' =>
        exact absurd hleid (by
          intro h
          obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ h
          exact absurd h2 (fun x => x))
      | @lam nF _ _ A'' G _ _ _ _ G₀ hd hfo hwG hwPi hwG₀ hgG hG₀ev hG₀ty hlabG =>
        cases hP with
        | @forallE _ _ _ _ nc gc dc _ _ hAint hdty hwfc _ hbodyc hlePi =>
          obtain ⟨hPiLab, _, hcovc⟩ :=
            TShape.LE.forallE_decomp hΔ hlePi hwfc (TEvaluates.refl hwfc.2.2.2.1)
          -- the λ-shape's label is the domain
          have hA₁ : TyEq Δ A₁ (A.subst σ) :=
            Interp.lam_label_ty hAdm hfty hF
          -- a lookup in the code's codomain graph, at the canonical query,
          -- is an approximant of `B[a]`
          have toI : ∀ {c : TShape},
              TEvaluates Δ fP (A.subst σ) (a.subst σ) x c →
              Interp Δ Γ (B.inst a) σ ρ c := by
            intro c hc
            refine (Interp.inst (A := A) (b := B) hΔ hΓ hA ha hB hPB W hAdm
              (Subst.Saturates.one hΓ hAdm hA ha hadom)
              hwρ).2 ⟨x, ?_, hx⟩
            rw [Subst.one_comp]
            exact sound_graph_lookup hΓA hA hB hΔ W hbodyc hx.wf hwρ haσ
              (TyEq.refl hAσ) (TEvaluates.trans hΔ (fun e he => (hcovc e he).retype hPiLab.1) hc)
          -- the λ-shape's own lookup is covered by the saturated one
          have hcovG : ∀ e ∈ g, TEvaluates Δ G A₁ e.tm e.inp.T e.out.T :=
            TShape.LE.lam_decomp hΔ hFle hwG (TEvaluates.refl hwG.2.2.1)
          have hevG : TEvaluates Δ G A₁ (a.subst σ) x y :=
            TEvaluates.trans hΔ hcovG hev
          -- every value of that lookup is below one that is hereditarily
          -- typed, and still a value of it
          have hwout : ∀ e ∈ G, TShape.WF Δ e.out.T := fun e he =>
            TShape.WF.T.2 (hwG.2.2.1.1 e he).2.2.2
          -- the code's labels are the type's, by the order
          have hfσ : Δ ⊢ f.subst σ : (Term.forallE A B).subst σ := hft.subst hΔ W
          obtain ⟨_, hA'ty⟩ := hwPi.1
          obtain ⟨_, hB'ty⟩ := hwPi.2.1
          have key : ∀ {w : TShape}, TEvaluates Δ G A₁ (a.subst σ) x w →
              ∃ w' c, TEvaluates Δ G A₁ (a.subst σ) x w' ∧ TShape.LE Δ w w' ∧
                Interp Δ Γ (B.inst a) σ ρ c ∧
                TShape.Named Δ c w' ((Term.app f a).subst σ) := by
            intro w hw'
            induction hw' with
            | bot =>
              exact ⟨TShape.bot, TShape.bot, .bot, TShape.LE.refl trivial, .bot,
                TShape.Named.bot (.bot (.bot .sort))⟩
            | @entry q hq hlabq hinq =>
              -- the entry's output is `Named` at its code, which is an
              -- approximant of `B[a]` once moved to the canonical query
              obtain ⟨pc, hpc, hpceq⟩ : ∃ pc ∈ cs,
                  pc.1 = ⟨q.tm, q.inp.T, q.out.T⟩ := by
                have : (⟨q.tm, q.inp.T, q.out.T⟩ : Entry TShape) ∈
                    (Shape.T (n := nF+1) (ShapeS.lam A'' G)).entries :=
                  List.mem_map_of_mem
                    (f := fun e => (⟨e.tm, e.inp.T, e.out.T⟩ : Entry TShape)) hq
                rw [hent, List.mem_map] at this
                obtain ⟨pc, hpc, heq⟩ := this
                exact ⟨pc, hpc, heq⟩
              have hcode := hevc pc hpc
              have hdomq := hout pc hpc
              rw [hpceq] at hcode hdomq
              have hqA' : TyEq Δ A₁ A' := hA₁.trans (TyEq.symm hPiLab.1)
              refine ⟨q.out.T, pc.2, .entry q hq hlabq hinq, TShape.LE.refl
                (TShape.WF.T.2 (hwG.2.2.1.1 q hq).2.2.2), ?_, ?_⟩
              · refine toI (TEvaluates.mono hΔ ?_ hinq hcode)
                exact ⟨hPiLab.1, hqA'.defeqDF hlabq.2⟩
              · -- the entry's output names `app f q.tm`, which the label
                -- equation moves to `app f a`, through the entry's own code
                have hwq := (hwG.2.2.1.1 q hq)
                have hqtm : Δ ⊢ q.tm : A' := hlabG.defeqDF hwq.2.1
                have hcc : TShape.WF Δ pc.2 (B'.inst q.tm) :=
                  TShape.WF.lookup hΔ hwPi.2.2.2.1 (ShapeFun.WF.canon hwPi.2.2.2.1)
                    hA'ty hB'ty hcode
                have hcc' : TShape.WF Δ pc.2 ((B.subst σ.lift).inst q.tm) :=
                  hcc.conv (TyEq.inst' hΔ hA'ty hPiLab.2 (hqtm.symm.trans hqtm)).symm
                have hqa : Δ ⊢ q.tm ≡ a.subst σ : A.subst σ :=
                  hA₁.defeqDF hlabq.2
                have happ := IsDefEq.appDF₀ hΔ hfσ hqa
                exact hdomq.defeq hΔ hcc' happ
            | lower hle' _ ih =>
              obtain ⟨w', c, hw'', hlew, hIc, hdc⟩ := ih
              exact ⟨w', c, hw'', TShape.LE.trans hΔ hle' hlew, hIc, hdc⟩
            | @join w₁ w₂ hcj hv₁ hv₂ ih₁ ih₂ =>
              obtain ⟨w₁', c₁, hv₁', hle₁, hI₁, hd₁⟩ := ih₁
              obtain ⟨w₂', c₂, hv₂', hle₂, hI₂, hd₂⟩ := ih₂
              -- the two values join, being lookups in one coherent graph
              have hcw : TShape.Compat Δ w₁' w₂' :=
                TEvaluates.compat hΔ (hwG.2.2.1.2.retype (TyEq.symm (TShape.LE.lam_dom hFle)))
                  hx.wf hv₁' hv₂'
              -- and so do their codes, inside `B[a]`'s extension
              obtain ⟨c, hwc, hIc, hlc₁, hlc₂⟩ :=
                dir_inst (b := B) hA ha hB hPB hAdm hΓ hadom hI₁ hI₂
              have hcty := hBaty.isType hAdm hIc
              refine ⟨w₁'.join w₂', c, .join hcw hv₁' hv₂',
                TShape.join_le hΔ (TShape.LE.trans hΔ hle₁
                  (TShape.le_join hΔ (TEvaluates.wf hΔ hwout hv₁')
                    (TEvaluates.wf hΔ hwout hv₂') hcw).1) ?_, hIc, ?_⟩
              · exact TShape.LE.trans hΔ hle₂
                  (TShape.le_join hΔ (TEvaluates.wf hΔ hwout hv₁')
                    (TEvaluates.wf hΔ hwout hv₂') hcw).2
              · exact TShape.Named.join hΔ hcw (TShape.Named.mono_r hΔ hd₁ hlc₁ hcty)
                  (TShape.Named.mono_r hΔ hd₂ hlc₂ hcty)
          obtain ⟨y', c, hy', hyle, hIc, hdc⟩ := key hevG
          -- the saturated function's own label, which the clause reads at
          have hA'' : TyEq Δ A₁ A'' :=
            hA₁.trans (Interp.lam_label_ty hAdm hfty hF').symm
          have hwy' := TEvaluates.wf hΔ hwout hy'
          exact ⟨y', c,
            .app hF' hx
              (TEvaluates.label ⟨hA'', hA₁.symm.defeqDF haσ⟩ hy')
              (TShape.LE.refl hwy') (hst.retype hA''),
            TShape.LE.trans hΔ hle hyle, hIc, hdc,
            hBaty.codeAt hAdm hIc⟩

/-- The `SoundEq` half of `appDF`: the same shape is read out of the same
graph, at a query whose term has moved along `a ≡ a'`.  The query's *type*
is the λ-shape's label, so the equation has to be transported there, and
`Interp.lam_label_ty` is what says the label is `A[σ]`. -/
theorem sound_app_eq_of {Γ : List Term} {A B f f' a a' : Term}
    (haa' : Γ ⊢ a ≡ a' : A) (hfty : SoundTy Γ f (.forallE A B))
    (ihf : SoundEq Γ f f') (iha : SoundEq Γ a a')
    {Δ : List Term} {σ ρ} (hAdm : Adm Δ Γ σ ρ)
    {m : TShape} (H : Interp Δ Γ (.app f a) σ ρ m) :
    Interp Δ Γ (.app f' a') σ ρ m := by
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  cases H with
  | bot => exact .bot
  | app hF hx hev hle hty =>
    have hA₁ := Interp.lam_label_ty hAdm hfty hF
    refine .app ((ihf hAdm).1 hF) ((iha hAdm).1 hx) ?_ hle
      (Stable.of_typed haa'.hasType.2 hA₁)
    exact TEvaluates.mono hΔ
      ⟨hA₁.refl_l, hA₁.symm.defeqDF (haa'.subst hΔ W)⟩
      (TShape.LE.refl hx.wf) hev

/-- The `SoundEq` half of `appDF`. -/
theorem sound_app_eq {Γ : List Term} {A B f f' a a' : Term}
    (hff' : Γ ⊢ f ≡ f' : .forallE A B) (haa' : Γ ⊢ a ≡ a' : A)
    (hfty : SoundTy Γ f (.forallE A B))
    (ihf : SoundEq Γ f f') (iha : SoundEq Γ a a') :
    SoundEq Γ (.app f a) (.app f' a') := by
  intro Δ σ ρ hAdm m
  exact ⟨sound_app_eq_of haa' hfty ihf iha hAdm,
    sound_app_eq_of haa'.symm (SoundTy.of_eq hff' ihf hfty) ihf.symm iha.symm hAdm⟩

/-- The Σ analogue of `Interp.lam_label_ty`: a typed approximant of a
Σ-typed term is labelled by the syntactic domain. -/
theorem Interp.pair_label_ty {Γ Δ : List Term} {p A B : Term} {σ ρ}
    (hAdm : Adm Δ Γ σ ρ)
    (hty : SoundTy Γ p (.sigma A B))
    {n} {A₀ a₀ : Term} {x y : Shape n}
    (hp : Interp Δ Γ p σ ρ (Shape.T (n := n+1) (ShapeS.pair A₀ a₀ x y))) :
    TyEq Δ A₀ (A.subst σ) := by
  have hΔ := hAdm.ctx
  obtain ⟨s, hs, hsty⟩ := hty.approx hAdm hp
  cases hsty with
  | pair _ _ _ hwSg _ _ _ _ hdom =>
    cases hs with
    | sigma _ _ hwf _ _ hle =>
      obtain ⟨hSg, _, _⟩ :=
        TShape.LE.sigma_decomp hΔ hle hwf (TEvaluates.refl hwf.2.2.2.1)
      exact hdom.trans hSg.1

/-- **Saturation at a second projection.**  The Σ twin of
`sound_app_dom`: the pair's own saturation pair-approximant
whose entries' outputs are hereditarily typed at the codomain read
there, and the projection is a lookup in that graph. -/
theorem sound_snd_dom {Γ : List Term} {A B p : Term} {u v : Bool}
    (hPB : B.Pinned (A :: Γ))
    (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v)
    (hfst : Γ ⊢ .fst p : A)
    (hfdom : SoundTy Γ (.fst p) A)
    (hpty : SoundTy Γ p (.sigma A B))  (hBfd : SoundTy Γ (B.inst (.fst p)) (.sort v))
      :
    SoundTy Γ (.snd p) (B.inst (.fst p)) := by
  have hfdir := (IsDefEq.dir hΓ hfst).1
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
  have hBdir := (IsDefEq.dir hΓA hB).1
  intro Δ σ ρ hAdm m hm
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have hwρ := hAdm.wf
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  have hfσ : Δ ⊢ (Term.fst p).subst σ : A.subst σ := hfst.subst hΔ W
  cases hm with
  | bot => exact ⟨TShape.bot, TShape.bot, .bot, TShape.bot_le' rfl, .bot, (TShape.Named.bot (.bot (.bot .sort))), TShape.WF.bot⟩
  | @snd _ _ _ _ _ n A₀ a₀ x y hp hlab hle hst =>
    -- saturate the pair; its second component is the projection's
    obtain ⟨P', S, hP', hPle, hS, hNV, _⟩ := hpty hAdm hp
    have hSsg : S.IsSigma := by
      rcases (show S.2 = Shape.bot ∨ S.IsSigma from by
          cases hS with
          | bot => exact .inl rfl
          | sigma _ _ _ _ _ hles _ _ => exact TShape.isSigma_or_bot_of_le hles trivial)
        with hb | h
      · exact absurd (TShape.le_bot hΔ (TShape.HasType.bot_r hΔ hb hNV.hasType) hPle)
          (by simp [Shape.bot])
      · exact h
    cases hNV with
    | base hnb _ _ => exact absurd hSsg.isBinder hnb
    | pi _ _ _ _ _ => exact absurd hSsg (TShape.IsPi.not_sigma trivial)
    | @sg _ nS A' B' dS fS _ ps cc hty hps _ hxd' hevc hout =>
      cases hty with
      | bot hb => exact absurd (TShape.le_bot hΔ rfl hPle) (by simp [Shape.bot])
      | refl hleid hAty' =>
        exact absurd hleid (by
          intro h
          obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ h
          exact absurd h2 (fun x => x))
      | @pair nP _ A₀' a₀' x' y' _ _ _ _ _ _ hd hfo hwP hwSg hxd hxle' hev' hyty hlabP =>
        cases hS with
        | @sigma _ _ _ _ nc gc dc _ _ hAint hdty hwfc _ hbodyc hleSg =>
          obtain ⟨hSgLab, _, hcovc⟩ :=
            TShape.LE.sigma_decomp hΔ hleSg hwfc (TEvaluates.refl hwfc.2.2.2.1)
          -- the saturated pair's first component is an approximant of `fst p`
          have hx'w : TShape.WF Δ (Shape.T x') := TShape.WF.T.2 hwP.2.2.2.1
          have hx'I : Interp Δ Γ (.fst p) σ ρ (Shape.T x') :=
            .fst hP' (TShape.LE.refl hx'w)
          -- the two names, and the dominator's own equation to `fst p`
          have hA₀ : TyEq Δ A₀ (A.subst σ) := Interp.pair_label_ty hAdm hpty hp
          have hA₀' : TyEq Δ A₀' (A.subst σ) := Interp.pair_label_ty hAdm hpty hP'
          obtain ⟨hAle, hale, hxle, hyle⟩ := TShape.LE.pair_decomp hΔ hPle
          have hlab' : Δ ⊢ a₀' ≡ (Term.fst p).subst σ : A₀' :=
            hAle.defeqDF (hale.symm.trans hlab)
          -- the code that types the dominator's second component is a
          -- lookup at that name, hence an approximant of `B[fst p]`
          have hcode : TEvaluates Δ fS A' a₀' (Shape.T x') cc := hevc _ (by rw [← hps]; rfl)
          have hdomy : TShape.Named Δ cc (Shape.T y') (Term.snd (p.subst σ)) := by
            simpa using hout _ (show _ ∈ _ by rw [← hps]; rfl)
          have hIc : Interp Δ Γ (B.inst (.fst p)) σ ρ cc := by
            refine (Interp.inst (A := A) (b := B) hΔ hΓ hA hfst hB hPB W hAdm
              (Subst.Saturates.one hΓ hAdm hA hfst hfdom)
              hwρ).2 ⟨Shape.T x', ?_, hx'I⟩
            rw [Subst.one_comp]
            refine sound_graph_lookup hΓA hA hB hΔ W hbodyc hx'w hwρ
              ((TyEq.symm hSgLab.1).defeqDF hfσ) hSgLab.1 ?_
            refine TEvaluates.label (A := A') (a := a₀')
              ⟨TyEq.refl_l hSgLab.1,
                (TyEq.trans hA₀' (TyEq.symm hSgLab.1)).defeqDF hlab'⟩ ?_
            exact TEvaluates.trans hΔ hcovc hcode
          exact ⟨Shape.T y', cc,
            .snd hP' hlab'
              (TShape.LE.refl (TShape.WF.T.2 hwP.2.2.2.2))
              (hst.retype (hA₀.trans hA₀'.symm)),
            TShape.LE.trans hΔ hle hyle, hIc, hdomy, hBfd.codeAt hAdm hIc⟩

/-- The Σ twin: `Term.Pinned`'s `snd` condition, from the pair's typing. -/
theorem PinSnd.of_sound {Γ : List Term} {A B p : Term}
    (hp : SoundTy Γ p (.sigma A B)) (hfst : Γ ⊢ Term.fst p : A) : PinSnd Γ p := by
  intro Δ σ ρ n A' a₀ x y hAdm hP
  exact Stable.of_typed hfst (Interp.pair_label_ty hAdm hp hP)

/-- The `SoundEq` half of `sndDF`: the same shape is read out of the same
graph, at a query whose term has moved along `fst p ≡ fst p'`.  As at
`app`, the query's *type* is the pair's own label, so the equation is
transported there by `Interp.pair_label_ty`. -/
theorem sound_snd_eq_of {Γ : List Term} {A B p p' : Term} {u v : Bool}
    (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) (hpp' : Γ ⊢ p ≡ p' : .sigma A B)
    (hpty : SoundTy Γ p (.sigma A B)) (ihp : SoundEq Γ p p')
    {Δ : List Term} {σ ρ} (hAdm : Adm Δ Γ σ ρ)
    {m : TShape} (H : Interp Δ Γ (.snd p) σ ρ m) :
    Interp Δ Γ (.snd p') σ ρ m := by
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  cases H with
  | bot => exact .bot
  | snd hp hlab hle hty =>
    have hA₀ := Interp.pair_label_ty hAdm hpty hp
    refine .snd ((ihp hAdm).1 hp) ?_ hle
      (Stable.of_typed (IsDefEq.fstDF hA hB hpp').hasType.2 hA₀)
    -- the name now points at `fst p'`, along `fst p ≡ fst p'`
    exact hlab.trans (hA₀.symm.defeqDF
      ((IsDefEq.fstDF hA hB hpp').subst hΔ W))

/-- The `SoundEq` half of `sndDF`. -/
theorem sound_snd_eq {Γ : List Term} {A B p p' : Term} {u v : Bool}
    (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) (hpp' : Γ ⊢ p ≡ p' : .sigma A B)
    (hpty : SoundTy Γ p (.sigma A B)) (ihp : SoundEq Γ p p') :
    SoundEq Γ (.snd p) (.snd p') := by
  intro Δ σ ρ hAdm m
  exact ⟨sound_snd_eq_of hA hB hpp' hpty ihp hAdm,
    sound_snd_eq_of hA hB hpp'.symm (SoundTy.of_eq hpp' ihp hpty) ihp.symm hAdm⟩

/-! ## The identity type

`Interp.id` is **label-only**: the interpretation of `.id r A a b` is the
set of shapes below one fixed `id`-shape, whose label is the stage's
substitution instance of `(A, a, b)`.  So all three conclusions come from
that one shape, as for the atoms — the difference is only that the shape
depends on the stage, which `sound_atom`/`dir_atom` do not allow. -/

/-- The two `id`-shapes of a congruence are order-equivalent: the clause
compares their labels up to definitional equality, which is exactly what
the premises give. -/
theorem TShape.LE.id_of {Γ Δ : List Term} {σ} {A A' a a' b b' : Term} {u r : Bool}
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ)
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (haa' : Γ ⊢ a ≡ a' : A) (hbb' : Γ ⊢ b ≡ b' : A) :
    TShape.LE Δ (Shape.T (n := 1) (ShapeS.id r (A.subst σ) (a.subst σ) (b.subst σ)))
      (Shape.T (n := 1) (ShapeS.id r (A'.subst σ) (a'.subst σ) (b'.subst σ))) :=
  TShape.LE.T.2 ⟨rfl, ⟨u, hAA'.subst hΔ W⟩, haa'.subst hΔ W, hbb'.subst hΔ W⟩

/-- Soundness for `idDF`.  Both directions of `SoundEq` are the same
`LE.trans`, run on the mirrored premises. -/
theorem sound_id {Γ : List Term} {A A' a a' b b' : Term} {u r : Bool}
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (haa' : Γ ⊢ a ≡ a' : A) (hbb' : Γ ⊢ b ≡ b' : A) :
    SoundEq Γ (.id r A a b) (.id r A' a' b') ∧ TypedAt Γ (.id r A a b) (.sort r) := by
  have hAA'' : Γ ⊢ A' ≡ A : .sort u := hAA'.symm
  have haa'' : Γ ⊢ a' ≡ a : A' := hAA'.defeqDF haa'.symm
  have hbb'' : Γ ⊢ b' ≡ b : A' := hAA'.defeqDF hbb'.symm
  constructor
  · intro Δ σ ρ hAdm m
    have hΔ := hAdm.ctx
    have W := hAdm.stage
    constructor
    · intro h
      cases h with
      | bot => exact .bot
      | id hle hAt hat hbt =>
        exact .id (hle.trans hΔ (TShape.LE.id_of hΔ W hAA' haa' hbb'))
          ⟨u, hAA'.hasType.2⟩ (hAA'.defeqDF haa'.hasType.2) (hAA'.defeqDF hbb'.hasType.2)
    · intro h
      cases h with
      | bot => exact .bot
      | id hle hAt hat hbt =>
        exact .id (hle.trans hΔ (TShape.LE.id_of hΔ W hAA'' haa'' hbb''))
          ⟨u, hAA'.hasType.1⟩ haa'.hasType.1 hbb'.hasType.1
  · intro Δ σ ρ hAdm m h
    have hΔ := hAdm.ctx
    have W := hAdm.stage
    refine ⟨TShape.sort r, Interp.sort', ?_⟩
    cases h with
    | bot => exact .bot .sort
    | id hle =>
      exact TShape.HasType.mono_l hΔ
        (.id (by cases r <;> decide)
          (Shape.WF.id_of hΔ W hAA'.hasType.1 haa'.hasType.1 hbb'.hasType.1)) hle

/-! ## The two unary formers

`.succ N` wraps its argument's shape, so directedness is its argument's:
the bound is the wrapper applied to the argument's bound, and
`TShape.LE.succ_of` carries the order through.  `.refl a` carries nothing,
so its approximants are `⊥` and the one `refl`-shape. -/

/-- Soundness for `succDF`.  `SoundEq` is the argument's, clause by
clause; `SoundTy` needs the argument's shape to be a numeral, which is
`TShape.HasType.isNumeral` applied to its own typing at `nat`. -/
theorem sound_succ {Γ : List Term} {N N' : Term}
    (ihe : SoundEq Γ N N') (ihty : SoundTy Γ N .nat) :
    SoundEq Γ (.succ N) (.succ N') ∧ TypedAt Γ (.succ N) .nat := by
  constructor
  · intro Δ σ ρ hAdm m
    have hΔ := hAdm.ctx
    have W := hAdm.stage
    constructor
    · intro h
      cases h with
      | bot => exact .bot
      | succ hv hle => exact .succ ((ihe hAdm).1 hv) hle
    · intro h
      cases h with
      | bot => exact .bot
      | succ hv hle => exact .succ ((ihe hAdm).2 hv) hle
  · intro Δ σ ρ hAdm m hm
    have hΔ := hAdm.ctx
    refine ⟨TShape.nat, Interp.nat', ?_⟩
    cases hm with
    | bot => exact .bot .nat
    | succ hv hle =>
      obtain ⟨c, hc, hvc⟩ := ihty.approx hAdm hv
      exact TShape.HasType.mono_l hΔ
        (.succ (TShape.HasType.isNumeral hΔ (Interp.le_nat hc) hvc)) hle

/-- Soundness for `reflDF`.  At `r = false` only `bot` interprets `.refl`,
and `bot` is typed at anything that is a type; at `r = true` the `refl`
clause's bound is the `id`-shape itself. -/
theorem sound_refl {Γ : List Term} {A a a' : Term} {u r : Bool}
    (hA : Γ ⊢ A : .sort u) (haa' : Γ ⊢ a ≡ a' : A)
    (hid : Γ ⊢ Term.id r A a a : .sort r) :
    SoundEq Γ (.refl r a) (.refl r a') ∧ TypedAt Γ (.refl r a) (.id r A a a) := by
  constructor
  · intro Δ σ ρ hAdm m
    have hΔ := hAdm.ctx
    have W := hAdm.stage
    constructor
    · intro h
      cases h with
      | bot => exact .bot
      | refl hle => exact .refl hle
    · intro h
      cases h with
      | bot => exact .bot
      | refl hle => exact .refl hle
  · intro Δ σ ρ hAdm m hm
    have hΔ := hAdm.ctx
    have W := hAdm.stage
    have hwid : TShape.WF Δ
        (Shape.T (n := 1) (ShapeS.id r (A.subst σ) (a.subst σ) (a.subst σ))) :=
      Shape.WF.id_of hΔ W hA haa'.hasType.1 haa'.hasType.1
    have hidty : TShape.HasType Δ
        (Shape.T (n := 1) (ShapeS.id r (A.subst σ) (a.subst σ) (a.subst σ))) TShape.type :=
      .id (Bool.le_true' r) hwid
    refine ⟨_, .id (TShape.LE.refl hwid) ⟨u, hA⟩ haa'.hasType.1 haa'.hasType.1, ?_⟩
    cases hm with
    | bot => exact .bot hidty
    | refl hle =>
      exact TShape.HasType.mono_l hΔ (.refl (TShape.LE.refl hwid) hidty) hle

/-- A `succ`-shape is not below `zero`. -/
theorem TShape.LE.succ_zero_absurd {Δ : List Term} {n} {v : Shape n}
    (h : TShape.LE Δ (Shape.T (n := n+1) (ShapeS.succ v)) TShape.zero) : False := by
  obtain ⟨_, _, _, h2⟩ := TShape.LE.src_succ h
  exact absurd h2 (fun x => x)

/-- Nor is `zero` below a `succ`-shape. -/
theorem TShape.LE.zero_succ_absurd' {Δ : List Term} {n} {v : Shape n}
    (h : TShape.LE Δ TShape.zero (Shape.T (n := n+1) (ShapeS.succ v))) : False := by
  obtain ⟨_, _, _, h2⟩ := TShape.LE.src_succ h
  exact absurd h2 (fun x => x)

/-! ## β

The rule is padded with typings of both sides, so only `SoundEq` has
content (the other repo's `of_typings` observation).

`→` is the graph lookup unfolded: the function's λ-shape is covered by the
rule's own graph, each of whose entries carries the body at the entry's
label and input, and the entry's label is definitionally the argument, so
`IsDefEq.stage` puts the body at the argument's stage and `Interp.inst`
reads it as an approximant of `e[e']`.  The lookup's `join` rule lands on
two of those, which is why `dir_inst` is needed.  No typing of the input the body is evaluated at the entry's own input.

`←` builds the one-entry λ-shape `[(A[σ], e'[σ], x, m)]` and looks `m` up
in it.  The input is typed because `SoundTy e' A` types *every*
approximant of `e'`, so nothing has to be enlarged. -/

/-- Every lookup in a λ-shape of `lam A e`, at the argument's label, is an
approximant of `e[e']`.  The `→` half of β, with the graph as a
parameter so that the induction on the lookup has something to name. -/
theorem sound_beta_lookup {Γ Δ : List Term} {A B e e' : Term} {σ ρ} {u : Bool}
    (hΓA : ⊢ (A :: Γ)) (hA : Γ ⊢ A : .sort u) (hbe : A :: Γ ⊢ e : B)
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ)
    {n} {g : ShapeFun n} (hwf : Shape.WF (n := n+1) Δ (.lam (A.subst σ) g))
    (hbody : ∀ e₀ ∈ g, Interp Δ (A :: Γ) e (σ.cons e₀.tm) (ρ.push e₀.inp.T) e₀.out.T)
    {x : TShape} (hx : Interp Δ Γ e' σ ρ x)
    (hdir : ∀ {{m₁ m₂}}, Interp Δ Γ (e.inst e') σ ρ m₁ → Interp Δ Γ (e.inst e') σ ρ m₂ →
      ∃ s, TShape.WF Δ s ∧ Interp Δ Γ (e.inst e') σ ρ s ∧
        TShape.LE Δ m₁ s ∧ TShape.LE Δ m₂ s)
    (hinst : ∀ {m : TShape}, Interp Δ Γ (e.inst e') σ ρ m ↔
      ∃ x, Interp Δ (A :: Γ) e ((Subst.one e').comp σ) (ρ.push x) m ∧ Interp Δ Γ e' σ ρ x) :
    ∀ {c : TShape}, TEvaluates Δ g (A.subst σ) (e'.subst σ) x c →
      Interp Δ Γ (e.inst e') σ ρ c := by
  intro c hc
  induction hc with
  | bot => exact .bot
  | @entry ej hej hlab hin =>
    have hwe := hwf.2.2.1.1 ej hej
    obtain ⟨⟨_, hty⟩, htm⟩ := hlab
    have Wcons : Ctx.SubstEq Δ (σ.cons ej.tm) (σ.cons (e'.subst σ)) (A :: Γ) :=
      .cons W hA (hty.defeqDF htm)
    refine hinst.2 ⟨ej.inp.T, ?_, hx.mono hΔ hin⟩
    rw [Subst.one_comp]
    exact IsDefEq.stage hΓA hbe hΔ Wcons (hbody ej hej)
  | lower hle' _ ih => exact ih.mono hΔ hle'
  | join _ _ _ ih₁ ih₂ =>
    obtain ⟨s, hws, hs, hle₁, hle₂⟩ := hdir ih₁ ih₂
    exact hs.mono hΔ (TShape.join_le hΔ hle₁ hle₂)

theorem sound_beta {Γ : List Term} {A B e e' : Term} {u : Bool}
    (hPe : e.Pinned (A :: Γ))
    (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u) (hbe : A :: Γ ⊢ e : B) (he' : Γ ⊢ e' : A)
    (ihA : SoundTy Γ A (.sort u)) (ihe'dom : SoundTy Γ e' A)
      :
    SoundEq Γ (.app (.lam A e) e') (e.inst e') := by
  have ihe'dir := (IsDefEq.dir hΓ he').1
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
  have ihedir := (IsDefEq.dir hΓA hbe).1
  intro Δ σ ρ hAdm m
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have hwρ : Valuation.WF Δ Γ ρ := hAdm.wf
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  have he'σ : Δ ⊢ e'.subst σ : A.subst σ := he'.subst hΔ W
  have hinst : ∀ {m : TShape}, Interp Δ Γ (e.inst e') σ ρ m ↔
      ∃ x, Interp Δ (A :: Γ) e ((Subst.one e').comp σ) (ρ.push x) m ∧
        Interp Δ Γ e' σ ρ x := fun {_} =>
    Interp.inst hΔ hΓ hA he' hbe hPe W hAdm
      (Subst.Saturates.one hΓ hAdm hA he' ihe'dom) hwρ
  have hdir := dir_inst (b := e) hA he' hbe hPe hAdm hΓ ihe'dom
  constructor
  · intro h
    cases h with
    | bot => exact .bot
    | app hF hx hev hle =>
      cases hF with
      | lam hAint hd hwf _ hbody hlelam _ =>
        -- the function's λ-shape is covered by the rule's own graph, and
        -- the order makes its label the domain, so the lookup moves there
        have hev' := (TEvaluates.trans hΔ
          (TShape.LE.lam_decomp hΔ hlelam hwf (TEvaluates.refl hwf.2.2.1)) hev).retype
          (TShape.LE.lam_dom hlelam)
        exact (sound_beta_lookup hΓA hA hbe hΔ W hwf hbody hx hdir hinst hev').mono hΔ hle
  · intro h
    obtain ⟨n, s⟩ := m
    by_cases hb : s.IsBot
    · rw [Shape.WF.eq_bot_of_isBot (s := s) h.wf hb]; exact .bot
    · obtain ⟨x₀, hbody₀, hx₀⟩ := hinst.1 h
      -- the argument's approximant, enlarged until hereditarily typed:
      -- that is what the λ-clause's slot asks of it
      obtain ⟨x, d, hx, hlex, hd, hNV, _⟩ := ihe'dom hAdm hx₀
      have hbody : Interp Δ (A :: Γ) e ((Subst.one e').comp σ) (ρ.push x) ⟨n, s⟩ :=
        Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hlex⟩) hbody₀
      -- one entry, at a level above both the argument's shape and the value
      obtain ⟨k, hkx, hkn⟩ : ∃ k, x.1 ≤ k ∧ n ≤ k :=
        ⟨max x.1 n, Nat.le_max_left .., Nat.le_max_right ..⟩
      have hwx : Shape.WF Δ (x.2.lift k) := (Shape.lift_wf hkx).2 hx.wf
      have hws : Shape.WF Δ (s.lift k) := (Shape.lift_wf hkn).2 h.wf
      have hnb : ¬ (s.lift k).IsBot := fun hbb => hb ((Shape.lift_isBot hkn).1 hbb)
      have hwg : Shape.WF (n := k+1) Δ (.lam (A.subst σ)
          [⟨e'.subst σ, x.2.lift k, s.lift k⟩]) := by
        refine ⟨by simp, ?_, ⟨?_, ?_⟩, ?_⟩
        · intro e₀ he₀; cases he₀ with | head => exact hnb | tail _ h => nomatch h
        · intro e₀ he₀
          cases he₀ with
          | head => exact ⟨⟨u, hAσ⟩, he'σ, hwx, hws⟩
          | tail _ h => nomatch h
        · intro e₀ he₀ e₁ he₁ Θ τ hΘ Wτ _ _
          cases he₀ with
          | tail _ h => nomatch h
          | head =>
            cases he₁ with
            | tail _ h => nomatch h
            | head => exact (Shape.WF.subst hΘ Wτ hws).coherent
        · exact TyEq.refl hAσ
      have hlam : Interp Δ Γ (.lam A e) σ ρ (Shape.T (n := k+1)
          (.lam (A.subst σ)
            [⟨e'.subst σ, x.2.lift k, s.lift k⟩])) := by
        refine .lam hd (ihA.isType hAdm hd) hwg ?_ ?_ (TShape.LE.refl hwg) ⟨u, hA⟩
        · intro e₀ he₀
          cases he₀ with
          | head =>
            exact TShape.Named.lift_subject hΔ hNV hkx
          | tail _ h => nomatch h
        · intro e₀ he₀
          cases he₀ with
          | tail _ h => nomatch h
          | head =>
            refine Interp.lift (m := ⟨n, s⟩) hΔ hkn ?_
            refine Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
              TShape.LE.le_lift hΔ hkx hx.wf⟩) ?_
            rw [← Subst.one_comp]; exact hbody
      exact .app hlam (Interp.lift hΔ hkx hx)
        (.entry ⟨e'.subst σ, x.2.lift k, s.lift k⟩ (.head _)
          (LabelEq.refl hAσ he'σ) (TShape.LE.refl hwx))
        (TShape.LE.le_lift (m := ⟨n, s⟩) hΔ hkn h.wf)
        (Stable.of_typed he' (TyEq.refl hAσ))

/-! ## The remaining computation rules

`natCase` on a numeral, and the fixed point's unfolding.  Each is padded
with typings of both sides, so only `SoundEq` has content, and in each the
two `Interp` rules line up on the nose: the mismatched pairs are ruled out
because `zero` and a `succ`-shape have no order between them, and the
matching pair is the rule's own premise, modulo the stage move that the
label term forces. -/

/-- `natCase C zero a b` and `a`. -/
theorem sound_natCase_zero {Γ : List Term} {C a b : Term} :
    SoundEq Γ (.natCase C .zero a b) a := by
  intro Δ σ ρ hAdm m
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h with
    | bot => exact .bot
    | natCase_zero _ _ ha _ => exact ha
    | natCase_succ hM _ _ _ =>
      cases hM with
      | zero hle => exact absurd (TShape.LE.succ_zero_absurd hle) not_false
  · have hz : TShape.WF Δ TShape.zero := trivial
    exact .natCase_zero (.zero (TShape.LE.refl hz)) .zero h .zero

/-- `natCase C (succ n) a b` and `b[n]`. -/
theorem sound_natCase_succ {Γ : List Term} {C a b n : Term}
    (hPb : b.Pinned (Term.nat :: Γ))
    (hΓ : ⊢ Γ) (hn : Γ ⊢ n : .nat) (hb : Term.nat :: Γ ⊢ b : B) (ihndom : SoundTy Γ n .nat)  : SoundEq Γ (.natCase C (.succ n) a b) (b.inst n) := by
  have ihndir := (IsDefEq.dir hΓ hn).1
  have hΓN : ⊢ (Term.nat :: Γ) := ⟨hΓ, _, .nat⟩
  intro Δ σ ρ hAdm m
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have hwρ : Valuation.WF Δ Γ ρ := hAdm.wf
  have hnσ : Δ ⊢ n.subst σ : Term.nat := hn.subst hΔ W
  have hinst : ∀ {m : TShape}, Interp Δ Γ (b.inst n) σ ρ m ↔
      ∃ x, Interp Δ (Term.nat :: Γ) b ((Subst.one n).comp σ) (ρ.push x) m ∧
        Interp Δ Γ n σ ρ x := fun {_} =>
    Interp.inst hΔ hΓ .nat hn hb hPb W hAdm
      (Subst.Saturates.one hΓ hAdm .nat hn ihndom) hwρ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h with
    | bot => exact .bot
    | natCase_zero hM _ _ _ =>
      cases hM with
      | succ _ hle => exact absurd (TShape.LE.zero_succ_absurd' hle) not_false
    | natCase_succ hM heq hbody _ =>
      -- the two labels for the binder are one, by `succ` injectivity
      have ht : Δ ⊢ n.subst σ ≡ _ : Term.nat := IsDefEq.succ_inj hΔ heq
      cases hM with
      | succ hv hle =>
        refine hinst.2 ⟨_, ?_, hv.mono hΔ (TShape.LE.succ_decomp hΔ hle)⟩
        rw [Subst.one_comp]
        refine IsDefEq.stage hΓN hb hΔ ?_ hbody
        exact .cons W .nat ht.symm
  · obtain ⟨x, hbody, hx⟩ := hinst.1 h
    obtain ⟨k, v⟩ := x
    refine .natCase_succ (.succ hx (TShape.LE.refl hx.wf))
      (.succDF hnσ) ?_ (.succDF hn)
    rw [← Subst.one_comp]; exact hbody

/-- `Y A b` and its unfolding `b[Y A b]`: the fixed point's rule *is* the
instantiation, so both directions are `Interp.inst` at the tower below. -/
theorem sound_Y_unfold {Γ : List Term} {A b : Term} {u : Bool} (hΓ : ⊢ Γ)
    (hPb : b.Pinned (A :: Γ))
    (hA : Γ ⊢ A : .sort u) (hb : A :: Γ ⊢ b : A.lift)
    (hY : Γ ⊢ .Y A b : A) (ihAty : SoundTy Γ A (.sort u)) (ihYdom : SoundTy Γ (.Y A b) A)
     :
    SoundEq Γ (.Y A b) (b.inst (.Y A b)) := by
  have ihYdir := (IsDefEq.dir hΓ hY).1
  intro Δ σ ρ hAdm m
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have hwρ : Valuation.WF Δ Γ ρ := hAdm.wf
  have hinst : ∀ {m : TShape}, Interp Δ Γ (b.inst (.Y A b)) σ ρ m ↔
      ∃ x, Interp Δ (A :: Γ) b ((Subst.one (.Y A b)).comp σ) (ρ.push x) m ∧
        Interp Δ Γ (.Y A b) σ ρ x := fun {_} =>
    Interp.inst hΔ hΓ hA hY hb hPb W hAdm
      (Subst.Saturates.one hΓ hAdm hA hY ihYdom)
      hwρ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h with
    | Y hx hA' hdty _ hbody hAt hYt =>
      refine hinst.2 ⟨_, ?_, hx⟩
      rw [Subst.one_comp]; exact hbody
    | bot => exact .bot
  · obtain ⟨x₀, hbody₀, hx₀⟩ := hinst.1 h
    -- the tower's slot is enlarged until hereditarily typed
    obtain ⟨x, d, hx, hlex, hd, hNV, hdc⟩ := ihYdom hAdm hx₀
    have hxd := hNV
    refine .Y hx hd (ihAty.isType hAdm hd) ⟨hxd, hdc⟩ ?_ ⟨u, hA⟩ hY
    rw [← Subst.one_comp]
    exact Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hlex⟩) hbody₀

/-! ## `natCase`, congruence

The two branches are the two premises', and the only work is at `succ`:
the body lives at the stage extended by the label term `t` and at the slot
`v`, so the body's `SoundEq` needs `(σ.cons t)` to be a substitution into
`nat :: Γ` — which `succ_regular` gives, `t` being a `succ`'s argument —
and needs the slot to be **admissible**, i.e. typed at `nat`.  Nothing in
`Interp.natCase_succ` says so; what does is `SoundTy M nat`, through
`HasType.isNumeral`: the shape `succ v` is typed at an approximant of
`⟦nat⟧`, hence a numeral, hence so is `v`. -/
theorem sound_natCase_of {Γ : List Term} {C C' M M' a a' b b' : Term}
    (hMM' : Γ ⊢ M ≡ M' : Term.nat)
    (ihM : SoundEq Γ M M') (ihMty : SoundTy Γ M Term.nat)
    (iha : SoundEq Γ a a') (ihb : SoundEq (Term.nat :: Γ) b b')
    {Δ : List Term} {σ ρ} (hAdm : Adm Δ Γ σ ρ)
    {m : TShape} (H : Interp Δ Γ (.natCase C M a b) σ ρ m) :
    Interp Δ Γ (.natCase C' M' a' b') σ ρ m := by
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  cases H with
  | bot => exact .bot
  | natCase_zero hM hz ha hMt =>
    exact .natCase_zero ((ihM hAdm).1 hM) (((hMM'.subst hΔ W).symm).trans hz)
      ((iha hAdm).1 ha) hMM'.hasType.2
  | @natCase_succ _ _ _ _ _ _ _ _ n v t hM heq hbody hMt =>
    -- the label term is a numeral's argument, so it is typed
    have ht : Δ ⊢ t : Term.nat := heq.succ_regular (.inr rfl)
    -- and the slot is typed at `nat`, because `M`'s shape is
    obtain ⟨c, hc, hty⟩ := ihMty.approx hAdm hM
    have hvnat : TShape.HasType Δ v.T TShape.nat :=
      (TShape.HasType.isNumeral hΔ (Interp.le_nat hc) hty).pred.hasType
    have Wcons : Ctx.SubstEq Δ (σ.cons t) (σ.cons t) (Term.nat :: Γ) := .cons W .nat ht
    have hAdm' : Adm Δ (Term.nat :: Γ) (σ.cons t) (ρ.push v.T) :=
      .cons hAdm Wcons W.wf
        Interp.nat' ⟨.base id hvnat
          (Shape.WF.numeral_mem (TShape.HasType.isNumeral hΔ (Interp.le_nat hc) hty).pred
            hvnat.wf.1),
        TyEq.refl .nat⟩
    exact .natCase_succ ((ihM hAdm).1 hM) 
      (((hMM'.subst hΔ W).symm).trans heq)
      ((ihb hAdm').1 hbody) hMM'.hasType.2

/-- The `SoundEq` half of `natCaseDF`. -/
theorem sound_natCase {Γ : List Term} {C C' M M' a a' b b' : Term}
    (hMM' : Γ ⊢ M ≡ M' : Term.nat)
    (ihM : SoundEq Γ M M') (ihMty : SoundTy Γ M Term.nat)
    (iha : SoundEq Γ a a') (ihb : SoundEq (Term.nat :: Γ) b b') :
    SoundEq Γ (.natCase C M a b) (.natCase C' M' a' b') := by
  intro Δ σ ρ hAdm m
  exact ⟨sound_natCase_of hMM' ihM ihMty iha ihb hAdm,
    sound_natCase_of hMM'.symm ihM.symm (SoundTy.of_eq hMM' ihM ihMty) iha.symm ihb.symm
      hAdm⟩

/-- A `natCase` computes at a stage where its scrutinee is `zero`: the
congruence moves the scrutinee, and `natCase_zero` fires. -/
theorem IsDefEq.natCase_zero_stage {Γ Δ : List Term} {C M a b : Term} {v : Bool} {σ : Subst}
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hC : Term.nat :: Γ ⊢ C : .sort v)
    (ha : Γ ⊢ a : C.inst .zero)
    (hb : Term.nat :: Γ ⊢ b : (C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0)))
    (hz : Δ ⊢ M.subst σ ≡ .zero : .nat) :
    Δ ⊢ (Term.natCase C M a b).subst σ ≡ a.subst σ : (C.inst M).subst σ := by
  have hΔN : ⊢ (Term.nat :: Δ) := ⟨hΔ, _, .nat⟩
  have WN : Ctx.SubstEq (Term.nat :: Δ) σ.lift σ.lift (Term.nat :: Γ) := W.lift .nat .nat
  have hC1 : Term.nat :: Δ ⊢ C.subst σ.lift : .sort v := hC.subst hΔN WN
  have ha1 : Δ ⊢ a.subst σ : (C.subst σ.lift).inst .zero := by
    have h := ha.subst hΔ W; rwa [subst_inst] at h
  have hb1 := hb.subst hΔN WN
  rw [subst_succ_branch_swap] at hb1
  have h1 := hC1.natCaseDF₀ hΔ hz ha1 hb1
  have h2 := IsDefEq.natCase_zero₀ hΔ hC1 ha1 hb1
  rw [subst_inst]
  exact h1.trans ((IsDefEq.instDF hΔ .nat .sort hC1 hz.symm).defeqDF h2)

/-- And where it is a successor, `natCase_succ`. -/
theorem IsDefEq.natCase_succ_stage {Γ Δ : List Term} {C M a b t : Term} {v : Bool} {σ : Subst}
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hC : Term.nat :: Γ ⊢ C : .sort v)
    (ha : Γ ⊢ a : C.inst .zero)
    (hb : Term.nat :: Γ ⊢ b : (C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0)))
    (hs : Δ ⊢ M.subst σ ≡ .succ t : .nat) :
    Δ ⊢ (Term.natCase C M a b).subst σ ≡ b.subst (σ.cons t) : (C.inst M).subst σ := by
  have hΔN : ⊢ (Term.nat :: Δ) := ⟨hΔ, _, .nat⟩
  have WN : Ctx.SubstEq (Term.nat :: Δ) σ.lift σ.lift (Term.nat :: Γ) := W.lift .nat .nat
  have hC1 : Term.nat :: Δ ⊢ C.subst σ.lift : .sort v := hC.subst hΔN WN
  have ha1 : Δ ⊢ a.subst σ : (C.subst σ.lift).inst .zero := by
    have h := ha.subst hΔ W; rwa [subst_inst] at h
  have hb1 := hb.subst hΔN WN
  rw [subst_succ_branch_swap] at hb1
  have ht : Δ ⊢ t : .nat := hs.succ_regular (.inr rfl)
  have h1 := hC1.natCaseDF₀ hΔ hs ha1 hb1
  have h2 := IsDefEq.natCase_succ₀ hΔ hC1 ht ha1 hb1
  rw [inst_lift_cons] at h2
  rw [subst_inst]
  exact h1.trans ((IsDefEq.instDF hΔ .nat .sort hC1 hs.symm).defeqDF h2)

/-- **Saturation at a `natCase`.**  A `natCase`'s approximant is its
branch's, so the branch's own saturation is the whole content; the code
moves from the branch's type to `C[M]` because `M[σ]` is the branch's
index at the stage. -/
theorem sound_natCase_dom {Γ : List Term} {C M a b : Term} {v : Bool} (hΓ : ⊢ Γ)
    (hPC : C.Pinned (Term.nat :: Γ))
    (hC : Term.nat :: Γ ⊢ C : .sort v)
    (hat : Γ ⊢ a : C.inst .zero)
    (hbt : Term.nat :: Γ ⊢ b : (C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0)))
    (hCMd : SoundTy Γ (C.inst M) (.sort v))
    (ihadom : SoundTy Γ a (C.inst .zero))
    (ihbdom : SoundTy (Term.nat :: Γ) b
      ((C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0))))
    (hMt : Γ ⊢ M : Term.nat) (ihMty : SoundTy Γ M Term.nat)
     :
    SoundTy Γ (.natCase C M a b) (C.inst M) := by
  have ihMdir := (IsDefEq.dir hΓ hMt).1
  have hΓN : ⊢ (Term.nat :: Γ) := ⟨hΓ, _, .nat⟩
  have hzdir :=
    dir_atom (Γ := Γ) (t := Term.zero) Interp.le_zero (fun h => .zero h) trivial
  have hClift : Term.nat :: Term.nat :: Γ ⊢ C.lift' (.cons (.skip .refl)) : .sort v :=
    IsDefEq.weak' (.cons (.skip .refl)) hC
  intro Δ σ ρ hAdm m hm
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have hwρ := hAdm.wf
  cases hm with
  | bot => exact ⟨TShape.bot, TShape.bot, .bot, TShape.bot_le' rfl, .bot, (TShape.Named.bot (.bot (.bot .sort))), TShape.WF.bot⟩
  | natCase_zero hMz hz hma hMt =>
    obtain ⟨ma, c, hma', hmle, hc, hNV, _⟩ := ihadom hAdm hma
    obtain ⟨x, hCx, hxz⟩ :=
      (Interp.inst (A := Term.nat) (b := C) hΔ hΓ .nat .zero hC hPC W hAdm
        (Subst.Saturates.one hΓ hAdm .nat .zero (SoundTy.nat TypedAt.zero))
        hwρ).1 hc
    rw [Subst.one_comp] at hCx
    have W0 : Ctx.SubstEq Δ (σ.cons (Term.zero.subst σ)) (σ.cons (M.subst σ))
        (Term.nat :: Γ) := .cons W .nat hz.symm
    have hIc : Interp Δ Γ (C.inst M) σ ρ c :=
      (Interp.inst (A := Term.nat) (b := C) hΔ hΓ .nat hMt hC hPC W hAdm
        (Subst.Saturates.one hΓ hAdm .nat hMt ihMty)
        hwρ).2
        ⟨x, by rw [Subst.one_comp]; exact IsDefEq.stage hΓN hC hΔ W0 hCx,
          Interp.mono hΔ (Interp.le_zero hxz) hMz⟩
    have hcc := hCMd.codeAt hAdm hIc
    exact ⟨ma, c, .natCase_zero hMz hz hma' hMt, hmle, hIc,
      hNV.defeq hΔ hcc (IsDefEq.natCase_zero_stage hΔ W hC hat hbt hz).symm, hcc⟩
  | @natCase_succ _ _ _ _ _ _ _ _ n w t hMs heq hmb hMt =>
    have ht : Δ ⊢ t : Term.nat := heq.succ_regular (.inr rfl)
    have Wcons : Ctx.SubstEq Δ (σ.cons t) (σ.cons t) (Term.nat :: Γ) := .cons W .nat ht
    obtain ⟨cM, hcM, htyM⟩ := ihMty.approx hAdm hMs
    have hvnat : TShape.HasType Δ w.T TShape.nat :=
      (TShape.HasType.isNumeral hΔ (Interp.le_nat hcM) htyM).pred.hasType
    have hwv' : TShape.WF Δ w.T := TShape.WF.T.2 hMs.wf
    have hAdm' : Adm Δ (Term.nat :: Γ) (σ.cons t) (ρ.push w.T) :=
      .cons hAdm Wcons W.wf
        Interp.nat' ⟨.base id hvnat
          (Shape.WF.numeral_mem (TShape.HasType.isNumeral hΔ (Interp.le_nat hcM) htyM).pred
            hvnat.wf.1),
        TyEq.refl .nat⟩
    obtain ⟨mb, c, hmb', hmle, hc, hNV, _⟩ := ihbdom hAdm' hmb
    obtain ⟨y, hCy, hsy⟩ := (Interp.inst (A := Term.nat) (b := C.lift' (.cons (.skip .refl)))
      hΔ hΓN .nat (.succDF (.bvar .zero .nat)) hClift
      (Term.Pinned.weak' hΓN hC.annot.1 (.cons (.skip .refl)) hPC) Wcons hAdm'
      (Subst.Saturates.one hΓN hAdm' .nat (.succDF (.bvar .zero .nat))
        (SoundTy.nat TypedAt.succ_bvar0))
      (Valuation.WF.push hwρ hwv')).1 hc
    rw [Subst.one_comp] at hCy
    have hCy' : Interp Δ (Term.nat :: Γ) C (σ.cons ((Term.succ (.bvar 0)).subst (σ.cons t)))
        (ρ.push y) c := by
      have h := Interp.unweak (Δ := Δ) hΔ hΓN hC.annot.1 (Γ' := Term.nat :: Term.nat :: Γ)
        (l := .cons (.skip .refl)) (ρ := ρ.push y)
        (.cons (.skip .refl))
        (show Ctx.SubstEq Δ ((σ.cons t).cons ((Term.succ (.bvar 0)).subst (σ.cons t)))
            ((σ.cons t).cons ((Term.succ (.bvar 0)).subst (σ.cons t)))
            (Term.nat :: Term.nat :: Γ) from
          .cons Wcons .nat
            (by simpa using IsDefEq.subst hΔ Wcons (IsDefEq.succDF (.bvar .zero .nat))))
        (fun i => by cases i <;> rfl) hCy
      rwa [← Subst.lift_l_cons, ← Subst.tail_eq_lift_l] at h
    have hyle : TShape.LE Δ y (Shape.T (n := n+1) (ShapeS.succ w)) := by
      cases hsy with
      | bot => exact TShape.bot_le' rfl
      | @succ _ _ _ _ _ n' v' hv hle =>
        refine hle.trans hΔ (TShape.LE.succ_of hΔ (a := v'.T) (b := w.T) ?_)
        cases hv with
        | bot => exact TShape.bot_le' rfl
        | bvar _ h1 => exact h1
    have W1 : Ctx.SubstEq Δ (σ.cons ((Term.succ (.bvar 0)).subst (σ.cons t)))
        (σ.cons (M.subst σ)) (Term.nat :: Γ) := .cons W .nat heq.symm
    have hIc : Interp Δ Γ (C.inst M) σ ρ c :=
      (Interp.inst (A := Term.nat) (b := C) hΔ hΓ .nat hMt hC hPC W hAdm
        (Subst.Saturates.one hΓ hAdm .nat hMt ihMty)
        hwρ).2
        ⟨y, by rw [Subst.one_comp]; exact IsDefEq.stage hΓN hC hΔ W1 hCy',
          Interp.mono hΔ hyle hMs⟩
    have hcc := hCMd.codeAt hAdm hIc
    exact ⟨mb, c, .natCase_succ hMs heq hmb' hMt, hmle, hIc,
      hNV.defeq hΔ hcc (IsDefEq.natCase_succ_stage hΔ W hC hat hbt heq).symm, hcc⟩

/-! ## The fixed point

`Interp.Y` is a tower of unfoldings, so both halves are inductions on the
derivation with the term generalized, as `dir_Y_aux` already is: each
level's induction hypothesis supplies what the next level's stage needs —
for `SoundTy` the typing of the slot (which is what `Adm.cons` asks
for), and for `SoundEq` the inner tower already moved to the other side. -/

/-- The type of a fixed point: the body is typed at `A↑` one slot up, and
`Interp.unweak` brings that back to `A`.  The slot the body is read at is
the previous level of the tower, typed by the induction hypothesis — which
is exactly the `Adm.cons` obligation. -/
theorem sound_Y_typedAt_aux {Δ : List Term} (hΔ : ⊢ Δ) {Γ : List Term} {t : Term} {σ ρ}
    {m : TShape} (H : Interp Δ Γ t σ ρ m) :
    ∀ {A b : Term} {u : Bool}, t = .Y A b → ⊢ Γ →
      Γ ⊢ A : .sort u → Γ ⊢ .Y A b : A →
      Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ σ ρ →
      SoundTy Γ A (.sort u) → SoundTy (A :: Γ) b A.lift →
      ∃ c, Interp Δ Γ A σ ρ c ∧ TShape.HasType Δ m c := by
  induction H with
  | @Y Γ' σ' ρ' m' A b x d hx hd hdty hslotY hbody hAt hYt ihx _ _ =>
    rintro A' b' u ⟨⟩ hΓ hA hY W hAdm ihA ihb
    have WY : Ctx.SubstEq Δ (σ'.cons ((Term.Y A b).subst σ'))
        (σ'.cons ((Term.Y A b).subst σ')) (A :: Γ') := .cons W hA (hY.subst hΔ W)
    have hAdm' : Adm Δ (A :: Γ') (σ'.cons ((Term.Y A b).subst σ')) (ρ'.push _) :=
      .cons hAdm WY W.wf hd hslotY
    obtain ⟨c, hc, hct⟩ := ihb.approx hAdm' hbody
    exact ⟨c, Interp.unweak (Δ := Δ) hΔ hΓ hA.annot.1 (Γ' := A :: Γ') (l := .skip .refl)
      (.skip .refl) WY (fun i => rfl) hc, hct⟩
  | bot => exact fun _ _ _ _ _ _ _ _ => ⟨TShape.bot, .bot, .bot (.bot .sort)⟩
  | _ => intro A b u hne; cases hne

theorem sound_Y_typedAt {Γ : List Term} {A b : Term} {u : Bool} (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A : .sort u) (hY : Γ ⊢ .Y A b : A)
    (ihA : SoundTy Γ A (.sort u)) (ihb : SoundTy (A :: Γ) b A.lift) :
    TypedAt Γ (.Y A b) A := by
  intro Δ σ ρ hAdm m hm
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  exact sound_Y_typedAt_aux hΔ hm rfl hΓ hA hY W hAdm ihA ihb

/-- **Saturation at a fixed point.**  An unfolding's approximant is the
body's at the slot, so the body's own saturation is the whole content:
the enlarged value is still an unfolding at the same slot, and its code
unweakens from `A↑` to `A`. -/
theorem sound_Y_dom_aux {Δ : List Term} (hΔ : ⊢ Δ) {Γ : List Term} {t : Term} {σ ρ}
    {m : TShape} (H : Interp Δ Γ t σ ρ m) :
    ∀ {A b : Term} {u : Bool}, t = .Y A b → ⊢ Γ →
      Γ ⊢ A : .sort u → Γ ⊢ .Y A b : A →
      Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ σ ρ →
      SoundTy Γ A (.sort u) → A :: Γ ⊢ b : A.lift → SoundTy (A :: Γ) b A.lift →
      ∃ m' c, Interp Δ Γ (.Y A b) σ ρ m' ∧ TShape.LE Δ m m' ∧
        Interp Δ Γ A σ ρ c ∧
        TShape.Slot Δ (A.subst σ) c ((Term.Y A b).subst σ) m' := by
  induction H with
  | @Y Γ' σ' ρ' m' A b x d hx hd hdty hslotY hbody hAt hYt _ _ _ =>
    rintro A' b' u ⟨⟩ hΓ hA hY W hAdm ihA hbt ihbdom
    have WY : Ctx.SubstEq Δ (σ'.cons ((Term.Y A b).subst σ'))
        (σ'.cons ((Term.Y A b).subst σ')) (A :: Γ') := .cons W hA (hY.subst hΔ W)
    have hAdm' : Adm Δ (A :: Γ') (σ'.cons ((Term.Y A b).subst σ')) (ρ'.push _) :=
      .cons hAdm WY W.wf hd hslotY
    obtain ⟨mb, c, hmb, hmle, hc, hNV, hcc⟩ := ihbdom hAdm' hbody
    rw [lift_subst_cons] at hcc
    -- the body's value names `b[Y A b]`, which is `Y A b` by unfolding
    have hunf := (IsDefEq.Y_unfold₀ hΓ hA hbt).subst hΔ W
    rw [subst_inst, inst_lift_cons] at hunf
    exact ⟨mb, c, .Y hx hd hdty hslotY hmb hAt hYt, hmle,
      Interp.unweak (Δ := Δ) hΔ hΓ hA.annot.1 (Γ' := A :: Γ') (l := .skip .refl)
        (.skip .refl) WY (fun i => rfl) hc,
      hNV.defeq hΔ hcc hunf.symm, hcc⟩
  | bot =>
    exact fun _ _ _ _ _ _ _ _ _ => ⟨TShape.bot, TShape.bot, .bot, TShape.bot_le' rfl, .bot,
      TShape.Named.bot (.bot (.bot .sort)),
      Shape.WF.bot_mem⟩
  | _ => intro A b u hne; cases hne

theorem sound_Y_dom {Γ : List Term} {A b : Term} {u : Bool} (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A : .sort u) (hY : Γ ⊢ .Y A b : A)
    (ihA : SoundTy Γ A (.sort u)) (hbt : A :: Γ ⊢ b : A.lift)
    (ihbdom : SoundTy (A :: Γ) b A.lift) :
    SoundTy Γ (.Y A b) A := by
  intro Δ σ ρ hAdm m hm
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  exact sound_Y_dom_aux hΔ hm rfl hΓ hA hY W hAdm ihA hbt ihbdom

/-- The congruence: the tower moves one level at a time.  The inner
unfolding is the induction hypothesis, the body moves by its own
`SoundEq` (at the *old* context, then `Interp.ctx` to the new one), and
the stage — which names the fixed point itself — moves by
`IsDefEq.stage` along the congruence being proved. -/
theorem sound_Y_eq_aux {Δ : List Term} (hΔ : ⊢ Δ) {Γ : List Term} {t : Term} {σ ρ}
    {m : TShape} (H : Interp Δ Γ t σ ρ m) :
    ∀ {A A' b b' : Term} {u : Bool}, t = .Y A b → ⊢ Γ →
      Γ ⊢ A ≡ A' : .sort u → Γ ⊢ .Y A b : A → Γ ⊢ .Y A b ≡ .Y A' b' : A →
      A' :: Γ ⊢ b' : A'.lift →
      Ctx.SubstEq Δ σ σ Γ → Adm Δ Γ σ ρ → SoundEq Γ A A' →
      SoundTy Γ A (.sort u) → SoundTy (A :: Γ) b A.lift → SoundEq (A :: Γ) b b' →
      Interp Δ Γ (.Y A' b') σ ρ m := by
  induction H with
  | @Y Γ' σ' ρ' m' A b x d hx hd hdty hslotY hbody hAt hYt ihx _ _ =>
    rintro A₁ A' b₁ b' u ⟨⟩ hΓ hAA' hY hYY' hb' W hAdm ihAeq ihA ihbty ihbeq
    -- the inner tower, already moved
    have hx' := ihx rfl hΓ hAA' hY hYY' hb' W hAdm ihAeq ihA ihbty ihbeq
    have WY : Ctx.SubstEq Δ (σ'.cons ((Term.Y A b).subst σ'))
        (σ'.cons ((Term.Y A b).subst σ')) (A :: Γ') :=
      .cons W hAA'.hasType.1 (hY.subst hΔ W)
    have hAdm' : Adm Δ (A :: Γ') (σ'.cons ((Term.Y A b).subst σ')) (ρ'.push _) :=
      .cons hAdm WY W.wf hd hslotY
    -- the body, at the other side and at the other stage
    have hbody' := (ihbeq hAdm').1 hbody
    have W' : Ctx.SubstEq Δ (σ'.cons ((Term.Y A b).subst σ'))
        (σ'.cons ((Term.Y A' b').subst σ')) (A' :: Γ') :=
      .cons W hAA'.hasType.2 ((hAA'.subst hΔ W).defeqDF (hYY'.subst hΔ W))
    have hΓA' : ⊢ (A' :: Γ') := ⟨hΓ, _, hAA'.hasType.2⟩
    exact .Y hx' ((ihAeq hAdm).1 hd) hdty
      ((hslotY.defeq hΔ (hYY'.subst hΔ W)).conv (TyEq.symm ⟨u, hAA'.subst hΔ W⟩)) (IsDefEq.stage hΓA' hb' hΔ W'
        (hbody'.ctx hΓA' (Ctx.SubstEq.defeqHead hΓ hAA') Lookup.cons_head))
      ⟨u, hAA'.hasType.2⟩ (hAA'.defeqDF hYY'.hasType.2)
  | bot => exact fun _ _ _ _ _ _ _ _ _ _ _ _ => .bot
  | _ => intro A₁ A' b₁ b' u hne; cases hne

/-- The `SoundEq` half of `YDF`. -/
theorem sound_Y_eq {Γ : List Term} {A A' b b' : Term} {u : Bool} (hΓ : ⊢ Γ)
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (hYY' : Γ ⊢ .Y A b ≡ .Y A' b' : A)
    (hb : A :: Γ ⊢ b ≡ b' : A.lift) (hb' : A' :: Γ ⊢ b ≡ b' : A'.lift)
    (ihAeq : SoundEq Γ A A') (ihA : SoundTy Γ A (.sort u))
    (ihbty : SoundTy (A :: Γ) b A.lift) (ihbeq : SoundEq (A :: Γ) b b')
    (ihbty' : SoundTy (A' :: Γ) b' A'.lift) (ihbeq' : SoundEq (A' :: Γ) b' b) :
    SoundEq Γ (.Y A b) (.Y A' b') := by
  intro Δ σ ρ hAdm m
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  refine ⟨fun h => sound_Y_eq_aux hΔ h rfl hΓ hAA' hYY'.hasType.1 hYY' hb'.hasType.2
      W hAdm ihAeq ihA ihbty ihbeq, fun h => ?_⟩
  have hY' : Γ ⊢ .Y A' b' : A' := hAA'.defeqDF hYY'.hasType.2
  exact sound_Y_eq_aux hΔ h rfl hΓ hAA'.symm hY'
    (hAA'.defeqDF hYY'.symm) hb.hasType.1 W hAdm ihAeq.symm
    (SoundTy.of_eq hAA' ihAeq ihA) ihbty' ihbeq'

/-! ## Transport

`Interp.tr` carries its motive's value at the stage extended by `b` —
the term the motive's binder is instantiated with — and the whole of
`SoundTy` is that this *is* `Interp.inst`'s decomposition of `C[b]`, with
the clause's own `v` as the slot.  `SoundEq` moves each premise with its
own induction hypothesis; the motive takes three steps (its `SoundEq`,
then `Interp.ctx` for the domain that changed, then `IsDefEq.stage` for
the stage term that changed), which is the pattern `YDF` already uses. -/

/-- The `refl` equation the `tr` clause carries, moved along congruences
of its proof, endpoints and type. -/
theorem IsDefEq.refl_eq_move {Δ : List Term} {r : Bool} {A A' a a' b b' H H' : Term}
    {u : Bool} (hAA : Δ ⊢ A ≡ A' : .sort u) (haa : Δ ⊢ a ≡ a' : A) (hbb : Δ ⊢ b ≡ b' : A)
    (hHH : Δ ⊢ H ≡ H' : .id r A a b) (heq : Δ ⊢ a ≡ b : A)
    (hH : Δ ⊢ H ≡ .refl r a : .id r A a b) : Δ ⊢ H' ≡ .refl r a' : .id r A' a' b' := by
  have hA := hAA.hasType.1; have ha := haa.hasType.1
  have hrefl : Δ ⊢ Term.refl r a ≡ Term.refl r a' : Term.id r A a b :=
    (IsDefEq.idDF hA ha heq).defeqDF (IsDefEq.reflDF hA haa (IsDefEq.idDF hA ha ha))
  exact (IsDefEq.idDF hAA haa hbb).defeqDF ((hHH.symm.trans hH).trans hrefl)

/-- **A transport computes at a stage where its endpoints agree**: its
proof is `refl` there (as a clause premise at `r = true`, by proof
irrelevance at `r = false`), so `trDF` moves it to `tr_refl`. -/
theorem IsDefEq.tr_stage {Γ Δ : List Term} {r : Bool} {A a b C X H : Term} {u v : Bool}
    {σ : Subst} (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hA : Γ ⊢ A : .sort u)
    (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : A) (hC : A :: Γ ⊢ C : .sort v) (hX : Γ ⊢ X : C.inst a)
    (hH : Γ ⊢ H : .id r A a b) (heq : Δ ⊢ a.subst σ ≡ b.subst σ : A.subst σ)
    (hHr : r = true → Δ ⊢ H.subst σ ≡ .refl true (a.subst σ) :
      .id true (A.subst σ) (a.subst σ) (b.subst σ)) :
    Δ ⊢ (Term.tr r A a b C X H).subst σ ≡ X.subst σ : (C.inst b).subst σ := by
  have hA1 : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  have ha1 : Δ ⊢ a.subst σ : A.subst σ := ha.subst hΔ W
  have hb1 : Δ ⊢ b.subst σ : A.subst σ := hb.subst hΔ W
  have hC1 : A.subst σ :: Δ ⊢ C.subst σ.lift : .sort v :=
    hC.subst (Γ₀ := A.subst σ :: Δ) ⟨hΔ, _, hA1⟩ (W.lift hA hA1)
  have hX1 : Δ ⊢ X.subst σ : (C.subst σ.lift).inst (a.subst σ) := by
    have h := hX.subst hΔ W; rwa [subst_inst] at h
  have hH1 : Δ ⊢ H.subst σ : .id r (A.subst σ) (a.subst σ) (b.subst σ) := hH.subst hΔ W
  have hid : Δ ⊢ Term.id r (A.subst σ) (a.subst σ) (b.subst σ) : .sort r :=
    IsDefEq.idDF hA1 ha1 hb1
  have href : Δ ⊢ H.subst σ ≡ .refl r (a.subst σ) :
      .id r (A.subst σ) (a.subst σ) (b.subst σ) := by
    cases r with
    | true => exact hHr rfl
    | false =>
      refine IsDefEq.proofIrrel hid hH1 ?_
      exact (IsDefEq.idDF hA1 ha1 heq).defeqDF
        (IsDefEq.reflDF hA1 ha1 (IsDefEq.idDF hA1 ha1 ha1))
  have htr := IsDefEq.trDF hA1 ha1 heq.symm hC1 hC1 hX1 href
    (IsDefEq.instDF hΔ hA1 .sort hC1 heq.symm) hid
  have h2 := IsDefEq.tr_refl₀ (r := r) hΔ ha1 hC1 hX1
  rw [subst_inst]
  exact htr.trans ((IsDefEq.instDF hΔ hA1 .sort hC1 heq).defeqDF h2)

theorem sound_tr_eq_of {Γ : List Term} {A A' a a' b b' C C' X X' H H' : Term}
    {u v : Bool} {r : Bool} (hΓ : ⊢ Γ)
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (haa' : Γ ⊢ a ≡ a' : A) (hbb' : Γ ⊢ b ≡ b' : A)
    (hCC : A :: Γ ⊢ C ≡ C' : .sort v) (hCC' : A' :: Γ ⊢ C ≡ C' : .sort v)
    (hXX' : Γ ⊢ X ≡ X' : C.inst a) (hHH' : Γ ⊢ H ≡ H' : .id r A a b)
    (ihAeq : SoundEq Γ A A') (ihaeq : SoundEq Γ a a') (ihbeq : SoundEq Γ b b')
    (ihCeq : SoundEq (A :: Γ) C C') (ihXeq : SoundEq Γ X X')
    {Δ : List Term} {σ ρ} (hAdm : Adm Δ Γ σ ρ)
    {m : TShape} (hm : Interp Δ Γ (.tr r A a b C X H) σ ρ m) :
    Interp Δ Γ (.tr r A' a' b' C' X' H') σ ρ m := by
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  cases hm with
  | bot => exact .bot
  | tr hle hX ha hb hA hslotv hC hcb hslotc hH heq hAt hat hbt =>
    have hm' := hslotc.1.forget
    have hΓA' : ⊢ (A' :: Γ) := ⟨hΓ, _, hAA'.hasType.2⟩
    have WC : Ctx.SubstEq Δ (σ.cons (b.subst σ)) (σ.cons (b.subst σ)) (A :: Γ) :=
      .cons W hAA'.hasType.1 (hbb'.hasType.1.subst hΔ W)
    have hAdm' : Adm Δ (A :: Γ) (σ.cons (b.subst σ)) (ρ.push _) :=
      .cons hAdm WC W.wf hA hslotv
    have WC' : Ctx.SubstEq Δ (σ.cons (b.subst σ)) (σ.cons (b'.subst σ)) (A' :: Γ) :=
      .cons W hAA'.hasType.2 ((hAA'.subst hΔ W).defeqDF (hbb'.subst hΔ W))
    have hAσ : Δ ⊢ A.subst σ ≡ A'.subst σ : .sort u := hAA'.subst hΔ W
    -- the transported value's code names the motive at `b`, hence at `a`
    have hcX :=
      hslotc.2.conv (TyEq.tr_motive hΔ W hAA'.hasType.1 haa'.hasType.1 hCC.hasType.1 heq)
    refine .tr hle ((ihXeq hAdm).1 hX) ((ihaeq hAdm).1 ha)
      ((ihbeq hAdm).1 hb) ((ihAeq hAdm).1 hA) 
      ((hslotv.defeq hΔ (hbb'.subst hΔ W)).conv (TyEq.symm ⟨u, hAσ⟩))
      (IsDefEq.stage hΓA' hCC'.hasType.2 hΔ WC'
        (((ihCeq hAdm').1 hC).ctx hΓA' (Ctx.SubstEq.defeqHead hΓ hAA') Lookup.cons_head))
      hcb ⟨TShape.Named.defeq hΔ hslotc.1 hcX (hXX'.subst hΔ W),
        (hslotc.conv (TyEq.symm ⟨v, IsDefEq.subst' hΔ WC' hCC'⟩)).2⟩
      (fun hr => by
        cases hr
        exact IsDefEq.refl_eq_move hAσ (haa'.subst hΔ W) (hbb'.subst hΔ W) (hHH'.subst hΔ W)
          heq (hH rfl))
      -- the endpoints' equation moves along the congruences
      (((hAA'.subst hΔ W).defeqDF
        (((haa'.subst hΔ W).symm.trans heq).trans (hbb'.subst hΔ W))))
      ⟨u, hAA'.hasType.2⟩ (hAA'.defeqDF haa'.hasType.2) (hAA'.defeqDF hbb'.hasType.2)

/-- The `SoundEq` half of `trDF`. -/
theorem sound_tr_eq {Γ : List Term} {A A' a a' b b' C C' X X' H H' : Term}
    {u v : Bool} {r : Bool} (hΓ : ⊢ Γ)
    (hAA' : Γ ⊢ A ≡ A' : .sort u) (haa' : Γ ⊢ a ≡ a' : A) (hbb' : Γ ⊢ b ≡ b' : A)
    (hC : A :: Γ ⊢ C ≡ C' : .sort v) (hC' : A' :: Γ ⊢ C ≡ C' : .sort v)
    (hXX' : Γ ⊢ X ≡ X' : C.inst a) (hHH' : Γ ⊢ H ≡ H' : .id r A a b)
    (ihAeq : SoundEq Γ A A') (ihaeq : SoundEq Γ a a') (ihbeq : SoundEq Γ b b')
    (ihCeq : SoundEq (A :: Γ) C C') (ihCeq' : SoundEq (A' :: Γ) C C')
    (ihXeq : SoundEq Γ X X') :
    SoundEq Γ (.tr r A a b C X H) (.tr r A' a' b' C' X' H') := by
  intro Δ σ ρ hAdm m
  refine ⟨sound_tr_eq_of hΓ hAA' haa' hbb' hC hC' hXX' hHH' ihAeq ihaeq ihbeq ihCeq
      ihXeq hAdm, ?_⟩
  have hΓA' : ⊢ (A' :: Γ) := ⟨hΓ, _, hAA'.hasType.2⟩
  have hCs : A' :: Γ ⊢ C' ≡ C : .sort v := hC'.symm
  have hCs' : A :: Γ ⊢ C' ≡ C : .sort v := hC.symm
  have hXs : Γ ⊢ X' ≡ X : C'.inst a' :=
    (IsDefEq.instDF hΓ hAA'.hasType.1 .sort hC haa').defeqDF hXX'.symm
  have hHs : Γ ⊢ H' ≡ H : .id r A' a' b' := (IsDefEq.idDF hAA' haa' hbb').defeqDF hHH'.symm
  exact sound_tr_eq_of hΓ hAA'.symm (hAA'.defeqDF haa'.symm) (hAA'.defeqDF hbb'.symm)
    hCs hCs' hXs hHs
    ihAeq.symm ihaeq.symm ihbeq.symm ihCeq'.symm ihXeq.symm hAdm

/-- **Saturation at a transport.**  The clause already says the
transported value is hereditarily typed at the motive read at the slot,
and that it names `X` there; the transport computes to `X` at the stage
(`IsDefEq.tr_stage`), so it names the transport too. -/
theorem sound_tr_dom {Γ : List Term} {A a b C X H : Term} {r u v : Bool} (hΓ : ⊢ Γ)
    (hPC : C.Pinned (A :: Γ))
    (hA : Γ ⊢ A : .sort u) (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : A) (hC : A :: Γ ⊢ C : .sort v)
    (hX : Γ ⊢ X : C.inst a) (hHt : Γ ⊢ H : .id r A a b) (ihbdom : SoundTy Γ b A)
     :
    SoundTy Γ (.tr r A a b C X H) (C.inst b) := by
  have ihbdir := (IsDefEq.dir hΓ hb).1
  intro Δ σ ρ hAdm m hm
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have hwρ := hAdm.wf
  cases hm with
  | bot => exact ⟨TShape.bot, TShape.bot, .bot, TShape.bot_le' rfl, .bot, (TShape.Named.bot (.bot (.bot .sort))), TShape.WF.bot⟩
  | tr hle hX' ha' hbv hAv hslotv hCv hcb hslotc hH heq hAt hat hbt =>
    have hcb' := hslotc.2
    rw [← inst_lift_cons, ← subst_inst] at hcb'
    refine ⟨_, _, .tr (TShape.LE.refl hslotc.1.hasType.wf.1) hX' ha' hbv hAv
        hslotv hCv hcb hslotc hH heq hAt hat hbt, hle,
      (Interp.inst (A := A) (b := C) hΔ hΓ hA hb hC hPC W hAdm
        (Subst.Saturates.one hΓ hAdm hA hb ihbdom)
        hwρ).2 ⟨_, ?_, hbv⟩,
      hslotc.1.defeq hΔ hcb' (IsDefEq.tr_stage hΔ W hA ha hb hC hX hHt heq hH).symm, hcb'⟩
    rw [Subst.one_comp]
    exact hCv

/-- **`tr` at `refl` is the transported value.**  Forward is one `mono`:
the clause's `m'` is an approximant of `X`.  Backward is the clause
rebuilt around the value's own saturation: it gives a canonical code,
`Interp.inst` splits it into the motive at a slot approximating `a`, and
that slot serves as the witness `v`. -/
theorem sound_tr_refl_eq {Γ : List Term} {A a C X : Term} {u v : Bool} {r : Bool}
    (hPC : C.Pinned (A :: Γ))
    (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u) (ha : Γ ⊢ a : A) (hC : A :: Γ ⊢ C : .sort v) (ihadom : SoundTy Γ a A)
    (ihC : SoundTy (A :: Γ) C (.sort v)) (ihxdom : SoundTy Γ X (C.inst a)) :
    SoundEq Γ (.tr r A a a C X (.refl r a)) X := by
  have ihadir := (IsDefEq.dir hΓ ha).1
  intro Δ σ ρ hAdm m
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have hwρ := hAdm.wf
  constructor
  · intro h
    cases h with
    | bot => exact .bot
    | tr hle hX _ _ _ _ _ _ _ _ _ _ _ _ => exact Interp.mono hΔ hle hX
  · intro h
    obtain ⟨mX, c, hmX, hmle, hc, hNVX, hcc⟩ := ihxdom hAdm h
    obtain ⟨x₀, hC₀, ha₀⟩ :=
      (Interp.inst (A := A) (b := C) hΔ hΓ hA ha hC hPC W hAdm
        (Subst.Saturates.one hΓ hAdm hA ha ihadom)
        hwρ).1 hc
    rw [Subst.one_comp] at hC₀
    -- the slot is the argument's approximant, hereditarily typed
    obtain ⟨x, vA, ha', hlex, hvA, hNV, hvAc⟩ := ihadom hAdm ha₀
    have hC : Interp Δ (A :: Γ) C ((Subst.one a).comp σ) (ρ.push x) c :=
      Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ, hlex⟩)
        (by rw [Subst.one_comp]; exact hC₀)
    rw [Subst.one_comp] at hC
    have Wa : Ctx.SubstEq Δ (σ.cons (a.subst σ)) (σ.cons (a.subst σ)) (A :: Γ) :=
      .cons W hA (ha.subst hΔ W)
    have hAdm' : Adm Δ (A :: Γ) (σ.cons (a.subst σ)) (ρ.push x) :=
      .cons hAdm Wa W.wf hvA ⟨hNV, hvAc⟩
    have hcc' : TShape.WF Δ c (C.subst (σ.cons (a.subst σ))) := by
      rw [subst_inst, inst_lift_cons] at hcc; exact hcc
    have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
    have haσ : Δ ⊢ a.subst σ : A.subst σ := ha.subst hΔ W
    refine .tr hmle hmX ha' ha' hvA ⟨hNV, hvAc⟩ hC
      (ihC.isType hAdm' hC) ⟨hNVX, hcc'⟩ ?_ haσ ⟨u, hA⟩ ha ha
    rintro rfl
    exact IsDefEq.reflDF hAσ haσ (IsDefEq.idDF hAσ haσ haσ)

/-! ## Inversion at the level of `SoundEq`

The labels are in the shapes, so a semantic equality of two types yields
the *syntactic* equalities of their labels: probe with the type's own
label-only approximant, move it across with the equality at the identity
stage and the `⊥` valuation (admissible for free, `Adm.bot`), and read the
label back off the order.

These are stated over `SoundEq` rather than over `Γ ⊢ · ≡ · : _` because
that is the form the `eq` conclusion hands over inside the induction.
`Inversion.lean` derives the syntactic corollaries by feeding them
`IsDefEq.sound`. -/

/-- **A one-entry Π-approximant**: a value of the codomain at a typed
slot, packaged as an approximant of the Π-type itself.  Master's
`WShapeFun.single`, and the probe the codomain inversion below needs: it
is how a fact about `B` is pushed into a fact about `Π A B`, where the
semantic equality of two Π-types can see it.

The level bookkeeping is the same as everywhere: the domain shape, the
slot and the value live at three levels and the entry needs one. -/
theorem Interp.forallE_single {Γ Δ : List Term} {A B t : Term} {σ ρ} {u v : Bool}
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hwρ : Valuation.WF Δ Γ ρ)
    (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) (ht : Δ ⊢ t : A.subst σ)
    {d x c : TShape} (hdint : Interp Δ Γ A σ ρ d) (hdty : TShape.HasType Δ d TShape.type)
    (hxd : TShape.Named Δ d x t)
    (hdc : TShape.WF Δ d (A.subst σ))
    (hcc : TShape.WF Δ c ((B.subst σ.lift).inst t))
    (hc : Interp Δ (A :: Γ) B (σ.cons t) (ρ.push x) c) :
    ∃ (k : Nat) (dk xk ck : Shape k),
      Interp Δ Γ (.forallE A B) σ ρ (Shape.T (n := k+1)
        (.forallE (A.subst σ) (B.subst σ.lift) dk [⟨t, xk, ck⟩])) ∧
      TShape.LE Δ c (Shape.T ck) ∧ TShape.LE Δ (Shape.T xk) x := by
  obtain ⟨k, hkd, hkx, hkc⟩ : ∃ k, d.1 ≤ k ∧ x.1 ≤ k ∧ c.1 ≤ k :=
    ⟨max (max d.1 x.1) c.1, Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..),
      Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..), Nat.le_max_right ..⟩
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  have hΔA : ⊢ (A.subst σ :: Δ) := ⟨hΔ, _, hAσ⟩
  have hwd : Shape.WF Δ (d.2.lift k) := (Shape.lift_wf hkd).2 hdty.wf.1
  have hwx : Shape.WF Δ (x.2.lift k) := (Shape.lift_wf hkx).2 hxd.hasType.wf.1
  have hwc : Shape.WF Δ (c.2.lift k) := (Shape.lift_wf hkc).2 hc.wf
  have hwf : Shape.WF (n := k+1) Δ
      (.forallE (A.subst σ) (B.subst σ.lift) (d.2.lift k)
        [⟨t, x.2.lift k, c.2.lift k⟩]) := by
    refine ⟨⟨u, hAσ⟩, ⟨v, hB.subst hΔA (W.lift hA hAσ)⟩,
      (Shape.lift_wf hkd).2 hdc,
      ShapeFun.WF.name ⟨?_, ?_⟩ ?_, trivial⟩
    · intro e he
      cases List.mem_singleton.1 he
      exact ⟨⟨u, hAσ⟩, ht, hwx, hwc⟩
    · intro e he e' he' Θ τ hΘ Wτ _ _
      cases List.mem_singleton.1 he
      cases List.mem_singleton.1 he'
      exact Shape.WF.coherent (Shape.WF.subst hΘ Wτ hwc)
    · intro e he
      cases List.mem_singleton.1 he
      exact (Shape.lift_wf hkc).2 hcc
  refine ⟨k, _, _, _, .forallE ?_ ?_ hwf ?_ ?_ (TShape.LE.refl hwf)
      ⟨u, hA⟩ ⟨v, hB⟩,
    TShape.LE.le_lift hΔ (m := c) hkc hc.wf,
    TShape.LE.lift_le hΔ (m := x) hkx hxd.hasType.wf.1⟩
  · exact Interp.mono hΔ (TShape.LE.lift_le hΔ (m := d) hkd hdty.wf.1) hdint
  · exact hdty.lift_subject hΔ hkd
  · intro e he
    cases List.mem_singleton.1 he
    exact TShape.Named.mono_r hΔ (TShape.Named.lift_subject hΔ hxd hkx)
      (TShape.LE.le_lift hΔ (m := d) hkd hdty.wf.1) (hdty.lift_subject hΔ hkd)
  · intro e he
    cases List.mem_singleton.1 he
    refine Interp.mono hΔ (TShape.LE.lift_le hΔ (m := c) hkc hc.wf) ?_
    exact Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
      TShape.LE.le_lift hΔ (m := x) hkx hxd.hasType.wf.1⟩) hc

/-- The Σ twin of `Interp.forallE_single`. -/
theorem Interp.sigma_single {Γ Δ : List Term} {A B t : Term} {σ ρ} {u v : Bool}
    (hΔ : ⊢ Δ) (W : Ctx.SubstEq Δ σ σ Γ) (hwρ : Valuation.WF Δ Γ ρ)
    (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) (ht : Δ ⊢ t : A.subst σ)
    {d x c : TShape} (hdint : Interp Δ Γ A σ ρ d) (hdty : TShape.HasType Δ d TShape.type)
    (hxd : TShape.Named Δ d x t)
    (hdc : TShape.WF Δ d (A.subst σ))
    (hcc : TShape.WF Δ c ((B.subst σ.lift).inst t))
    (hc : Interp Δ (A :: Γ) B (σ.cons t) (ρ.push x) c) :
    ∃ (k : Nat) (dk xk ck : Shape k),
      Interp Δ Γ (.sigma A B) σ ρ (Shape.T (n := k+1)
        (.sigma (A.subst σ) (B.subst σ.lift) dk [⟨t, xk, ck⟩])) ∧
      TShape.LE Δ c (Shape.T ck) ∧ TShape.LE Δ (Shape.T xk) x := by
  obtain ⟨k, hkd, hkx, hkc⟩ : ∃ k, d.1 ≤ k ∧ x.1 ≤ k ∧ c.1 ≤ k :=
    ⟨max (max d.1 x.1) c.1, Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..),
      Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..), Nat.le_max_right ..⟩
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  have hΔA : ⊢ (A.subst σ :: Δ) := ⟨hΔ, _, hAσ⟩
  have hwd : Shape.WF Δ (d.2.lift k) := (Shape.lift_wf hkd).2 hdty.wf.1
  have hwx : Shape.WF Δ (x.2.lift k) := (Shape.lift_wf hkx).2 hxd.hasType.wf.1
  have hwc : Shape.WF Δ (c.2.lift k) := (Shape.lift_wf hkc).2 hc.wf
  have hwf : Shape.WF (n := k+1) Δ
      (.sigma (A.subst σ) (B.subst σ.lift) (d.2.lift k)
        [⟨t, x.2.lift k, c.2.lift k⟩]) := by
    refine ⟨⟨u, hAσ⟩, ⟨v, hB.subst hΔA (W.lift hA hAσ)⟩,
      (Shape.lift_wf hkd).2 hdc,
      ShapeFun.WF.name ⟨?_, ?_⟩ ?_, trivial⟩
    · intro e he
      cases List.mem_singleton.1 he
      exact ⟨⟨u, hAσ⟩, ht, hwx, hwc⟩
    · intro e he e' he' Θ τ hΘ Wτ _ _
      cases List.mem_singleton.1 he
      cases List.mem_singleton.1 he'
      exact Shape.WF.coherent (Shape.WF.subst hΘ Wτ hwc)
    · intro e he
      cases List.mem_singleton.1 he
      exact (Shape.lift_wf hkc).2 hcc
  refine ⟨k, _, _, _, .sigma ?_ ?_ hwf ?_ ?_ (TShape.LE.refl hwf) ⟨u, hA⟩ ⟨v, hB⟩,
    TShape.LE.le_lift hΔ (m := c) hkc hc.wf,
    TShape.LE.lift_le hΔ (m := x) hkx hxd.hasType.wf.1⟩
  · exact Interp.mono hΔ (TShape.LE.lift_le hΔ (m := d) hkd hdty.wf.1) hdint
  · exact hdty.lift_subject hΔ hkd
  · intro e he
    cases List.mem_singleton.1 he
    exact TShape.Named.mono_r hΔ (TShape.Named.lift_subject hΔ hxd hkx)
      (TShape.LE.le_lift hΔ (m := d) hkd hdty.wf.1) (hdty.lift_subject hΔ hkd)
  · intro e he
    cases List.mem_singleton.1 he
    refine Interp.mono hΔ (TShape.LE.lift_le hΔ (m := c) hkc hc.wf) ?_
    exact Interp.mono_val hΔ (Valuation.LE.push.2 ⟨Valuation.LE.refl hwρ,
      TShape.LE.le_lift hΔ (m := x) hkx hxd.hasType.wf.1⟩) hc

/-- **The codomains of two semantically equal Π-types agree, semantically.**
`forallE_inv` reads the *labels* off the two Π-shapes; this reads the
*graphs*.  A value of the first codomain at a typed slot becomes a
one-entry approximant of the Π-type (`Interp.forallE_single`); the
semantic equality carries it to the other Π-type, whose clause covers
that entry by a lookup in its own graph; and `sound_graph_lookup` turns
that lookup back into a value of the second codomain at the same slot. -/
theorem SoundEq.forallE_cod {Γ : List Term} {A₀ B₀ A₁ B₁ : Term} {u v u' v' : Bool}
    (hΓ : ⊢ Γ) (hA₀ : Γ ⊢ A₀ : .sort u) (hB₀ : A₀ :: Γ ⊢ B₀ : .sort v)
    (hA₁ : Γ ⊢ A₁ : .sort u') (hB₁ : A₁ :: Γ ⊢ B₁ : .sort v')
    (H : SoundEq Γ (.forallE A₀ B₀) (.forallE A₁ B₁))
    {Δ : List Term} {σ ρ} (hAdm : Adm Δ Γ σ ρ)
    {t : Term} (ht : Δ ⊢ t : A₀.subst σ)
    {d x c : TShape} (hdint : Interp Δ Γ A₀ σ ρ d) (hdty : TShape.HasType Δ d TShape.type)
    (hxd : TShape.Named Δ d x t)
    (hdc : TShape.WF Δ d (A₀.subst σ))
    (hcc : TShape.WF Δ c ((B₀.subst σ.lift).inst t))
    (hc : Interp Δ (A₀ :: Γ) B₀ (σ.cons t) (ρ.push x) c) :
    Interp Δ (A₁ :: Γ) B₁ (σ.cons t) (ρ.push x) c := by
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have hB₁dir := (IsDefEq.dir (show ⊢ (A₁ :: Γ) from ⟨hΓ, _, hA₁⟩) hB₁).1
  have hwρ := hAdm.wf
  obtain ⟨k, dk, xk, ck, hprobe, hcle, hxle⟩ :=
    Interp.forallE_single hΔ W hwρ hA₀ hB₀ ht hdint hdty hxd hdc hcc hc
  have hpr := (H hAdm).1 hprobe
  cases hpr with
  | forallE hA₁int hd₁ hwf₁ _ hbody₁ hle₁ =>
    obtain ⟨hPi, _, hcov⟩ :=
      TShape.LE.forallE_decomp hΔ hle₁ hwf₁ (TEvaluates.refl hwf₁.2.2.2.1)
    have hev := hcov ⟨t, xk, ck⟩ (by simp)
    have hB := sound_graph_lookup (B := B₁) ⟨hΓ, _, hA₁⟩ hA₁ hB₁ hΔ W hbody₁
      (TShape.WF.T.2 (hprobe.wf.2.2.2.1.1 _ (by simp)).2.2.1) hwρ ht hPi.1 hev
    exact Interp.mono hΔ hcle (Interp.mono_val hΔ (Valuation.LE.push.2
      ⟨Valuation.LE.refl hwρ, hxle⟩) hB)

/-- The Σ twin of `SoundEq.forallE_cod`. -/
theorem SoundEq.sigma_cod {Γ : List Term} {A₀ B₀ A₁ B₁ : Term} {u v u' v' : Bool}
    (hΓ : ⊢ Γ) (hA₀ : Γ ⊢ A₀ : .sort u) (hB₀ : A₀ :: Γ ⊢ B₀ : .sort v)
    (hA₁ : Γ ⊢ A₁ : .sort u') (hB₁ : A₁ :: Γ ⊢ B₁ : .sort v')
    (H : SoundEq Γ (.sigma A₀ B₀) (.sigma A₁ B₁))
    {Δ : List Term} {σ ρ} (hAdm : Adm Δ Γ σ ρ)
    {t : Term} (ht : Δ ⊢ t : A₀.subst σ)
    {d x c : TShape} (hdint : Interp Δ Γ A₀ σ ρ d) (hdty : TShape.HasType Δ d TShape.type)
    (hxd : TShape.Named Δ d x t)
    (hdc : TShape.WF Δ d (A₀.subst σ))
    (hcc : TShape.WF Δ c ((B₀.subst σ.lift).inst t))
    (hc : Interp Δ (A₀ :: Γ) B₀ (σ.cons t) (ρ.push x) c) :
    Interp Δ (A₁ :: Γ) B₁ (σ.cons t) (ρ.push x) c := by
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have hB₁dir := (IsDefEq.dir (show ⊢ (A₁ :: Γ) from ⟨hΓ, _, hA₁⟩) hB₁).1
  have hwρ := hAdm.wf
  obtain ⟨k, dk, xk, ck, hprobe, hcle, hxle⟩ :=
    Interp.sigma_single hΔ W hwρ hA₀ hB₀ ht hdint hdty hxd hdc hcc hc
  have hpr := (H hAdm).1 hprobe
  cases hpr with
  | sigma hA₁int hd₁ hwf₁ _ hbody₁ hle₁ =>
    obtain ⟨hSg, _, hcov⟩ :=
      TShape.LE.sigma_decomp hΔ hle₁ hwf₁ (TEvaluates.refl hwf₁.2.2.2.1)
    have hev := hcov ⟨t, xk, ck⟩ (by simp)
    have hB := sound_graph_lookup (B := B₁) ⟨hΓ, _, hA₁⟩ hA₁ hB₁ hΔ W hbody₁
      (TShape.WF.T.2 (hprobe.wf.2.2.2.1.1 _ (by simp)).2.2.1) hwρ ht hSg.1 hev
    exact Interp.mono hΔ hcle (Interp.mono_val hΔ (Valuation.LE.push.2
      ⟨Valuation.LE.refl hwρ, hxle⟩) hB)

theorem SoundEq.sort_inv {Γ : List Term} {u v : Bool}
    (hΓ : ⊢ Γ) (H : SoundEq Γ (Term.sort u) (Term.sort v)) : u = v := by
  have h := (H (Adm.bot hΓ (Ctx.SubstEq.id hΓ))).1 Interp.sort'
  have hle := Interp.le_sort h
  exact (TShape.LE.def_mp (Nat.le_refl 0) (Nat.le_refl 0)) hle

theorem SoundEq.forallE_inv {Γ : List Term} {A₀ B₀ A₁ B₁ : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hA₀ : Γ ⊢ A₀ : .sort u) (hB₀ : A₀ :: Γ ⊢ B₀ : .sort v)
    (H : SoundEq Γ (Term.forallE A₀ B₀) (Term.forallE A₁ B₁)) :
    ∃ u v, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ A₀ :: Γ ⊢ B₀ ≡ B₁ : .sort v := by
  -- the probe: the Π's own label, with nothing else in it
  have hprobe : Interp Γ Γ (.forallE A₀ B₀) Subst.id Valuation.nil
      (Shape.T (n := 1) (Shape.piAtom (A₀.subst Subst.id) (B₀.subst Subst.id.lift))) := by
    refine Interp.piAtom (u := u) (v := v) ?_ ?_ hA₀ hB₀
    · simpa using hA₀
    · simpa using hB₀
  -- the equality moves it across, at the identity stage and the `⊥` valuation
  have hmove := (H (Adm.bot hΓ (Ctx.SubstEq.id hΓ))).1 hprobe
  simp only [subst_id, Subst.lift_id] at hmove
  -- and the label reads back off it
  have hlab := Interp.le_piAtom hmove
  simp only [subst_id, Subst.lift_id] at hlab
  obtain ⟨u', hu⟩ := hlab.1
  obtain ⟨v', hv⟩ := hlab.2
  exact ⟨u', v', hu, hv⟩

/-- The same at Σ, with `sigmaAtom` as the probe. -/
theorem SoundEq.sigma_inv {Γ : List Term} {A₀ B₀ A₁ B₁ : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hA₀ : Γ ⊢ A₀ : .sort u) (hB₀ : A₀ :: Γ ⊢ B₀ : .sort v)
    (H : SoundEq Γ (Term.sigma A₀ B₀) (Term.sigma A₁ B₁)) :
    ∃ u v, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ A₀ :: Γ ⊢ B₀ ≡ B₁ : .sort v := by
  have hprobe : Interp Γ Γ (.sigma A₀ B₀) Subst.id Valuation.nil
      (Shape.T (n := 1) (Shape.sigmaAtom (A₀.subst Subst.id) (B₀.subst Subst.id.lift))) := by
    refine Interp.sigmaAtom (u := u) (v := v) ?_ ?_ hA₀ hB₀
    · simpa using hA₀
    · simpa using hB₀
  have hmove := (H (Adm.bot hΓ (Ctx.SubstEq.id hΓ))).1 hprobe
  simp only [subst_id, Subst.lift_id] at hmove
  have hlab := Interp.le_sigmaAtom hmove
  simp only [subst_id, Subst.lift_id] at hlab
  obtain ⟨u', hu⟩ := hlab.1
  obtain ⟨v', hv⟩ := hlab.2
  exact ⟨u', v', hu, hv⟩

/-- The *semantic* half of Σ domain inversion, at every stage: an
approximant of the domain moves across by being wrapped as the domain of
an otherwise empty Σ-shape.  Master's `SoundEq.sigma_inv`, first
component.  The syntactic `sigma_inv` above does not give this — a
definitional equality of domains becomes a `SoundEq` only through
soundness. -/
theorem SoundEq.sigma_dom {Γ : List Term} {A B A' B' : Term} {u u' v v' : Bool}
    (hAt : Γ ⊢ A : .sort u) (hA't : Γ ⊢ A' : .sort u')
    (hA : SoundTy Γ A (.sort u)) (hB : A :: Γ ⊢ B : .sort v)
    (hA' : SoundTy Γ A' (.sort u')) (hB' : A' :: Γ ⊢ B' : .sort v')
    (H : SoundEq Γ (.sigma A B) (.sigma A' B')) : SoundEq Γ A A' := by
  suffices key : ∀ {A B A' B' : Term} {u v : Bool}, (Γ ⊢ A : .sort u) →
      SoundTy Γ A (.sort u) →
      A :: Γ ⊢ B : .sort v → SoundEq Γ (.sigma A B) (.sigma A' B') →
      ∀ {Δ σ ρ}, Adm Δ Γ σ ρ →
      ∀ {m}, Interp Δ Γ A σ ρ m → Interp Δ Γ A' σ ρ m by
    intro Δ σ ρ hAdm m
    have hΔ := hAdm.ctx
    have W := hAdm.stage
    exact ⟨key hAt hA hB H hAdm, key hA't hA' hB' H.symm hAdm⟩
  intro A B A' B' u v hAt hA hB H Δ σ ρ hAdm m hm
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have ⟨⟨_, hAσ⟩, _, hBσ⟩ := PiLabelEq.subst hΔ W ⟨⟨u, hAt⟩, v, hB⟩
  have hw : Shape.WF (n := m.1+1) Δ (ShapeS.sigma (A.subst σ) (B.subst σ.lift) m.2 []) :=
    ⟨⟨_, hAσ.hasType.1⟩, ⟨_, hBσ.hasType.1⟩,
      hA.codeAt hAdm hm,
      ShapeFun.WF.name
        ⟨fun _ he => absurd he List.not_mem_nil, fun _ he => absurd he List.not_mem_nil⟩
        nofun, trivial⟩
  have hprobe : Interp Δ Γ (.sigma A B) σ ρ
      (Shape.T (n := m.1+1) (ShapeS.sigma (A.subst σ) (B.subst σ.lift) m.2 [])) :=
    .sigma hm (hA.isType hAdm hm) hw nofun nofun (TShape.LE.refl hw)
      ⟨u, hAt⟩ ⟨v, hB⟩
  have hmove := (H hAdm).1 hprobe
  cases hmove with
  | sigma hA'' _ hwf _ _ hle _ _ =>
    obtain ⟨_, hdd, _⟩ := TShape.LE.sigma_decomp hΔ hle hwf (TEvaluates.refl hwf.2.2.2.1)
    exact Interp.mono hΔ hdd hA''

/-- Inversion at `id`.  The `id` former is label-only, so it needs no
atom: its own interpretation at the identity stage *is* the probe, and the
order between two `id`-shapes is the triple of equations. -/
theorem SoundEq.id_inv {Γ : List Term} {r : Bool} {A₀ a₀ b₀ A₁ a₁ b₁ : Term} {u : Bool}
    (hΓ : ⊢ Γ) (hA₀ : Γ ⊢ A₀ : .sort u) (ha₀ : Γ ⊢ a₀ : A₀) (hb₀ : Γ ⊢ b₀ : A₀)
    (H : SoundEq Γ (.id r A₀ a₀ b₀) (.id r A₁ a₁ b₁)) :
    ∃ u, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ Γ ⊢ a₀ ≡ a₁ : A₀ ∧ Γ ⊢ b₀ ≡ b₁ : A₀ := by
  have hw : TShape.WF Γ (Shape.T (n := 1)
      (ShapeS.id r (A₀.subst Subst.id) (a₀.subst Subst.id) (b₀.subst Subst.id))) :=
    Shape.WF.id_of hΓ (Ctx.SubstEq.id hΓ) hA₀ ha₀ hb₀
  have hmove := (H (Adm.bot hΓ (Ctx.SubstEq.id hΓ))).1
    (.id (TShape.LE.refl hw) ⟨u, hA₀⟩ ha₀ hb₀)
  cases hmove with
  | id hle _ _ _ =>
    obtain ⟨M, _, _, h2⟩ := TShape.LE.at_succ hle
    obtain ⟨_, ⟨u', hA⟩, ha, hb⟩ := h2
    simp only [subst_id] at hA ha hb
    exact ⟨u', hA, ha, hb⟩

/-! ## The target

The one theorem this branch is for.  Master needs `LogRel.lean` and
`Adequacy.lean` on top of its soundness theorem to get inversion; here the
labels carry the syntax through the model, so the inversion principles of
§6 are corollaries of this statement alone. -/

/-! ## The soundness theorem

Two conclusions, as master's: the terms have the same approximants
(`SoundEq`, his `HasEquality`) and every approximant of the left one is
below a typed one (`SoundTy`, his `HasFixedness`).  Directedness is
`IsDefEq.dir` above; his `HasSubstitution`/`HasRenaming` are
`Interp.substTerm`/`Interp.weak'`; his `PiReady` dissolves into
`IsDefEq.dir` of the domain and the codomain; his `regular` is never
used, here or there. -/

/-- What one derivation yields.  A record rather than a tuple: the
conclusions have grown from two to six, and each addition would
otherwise renumber every projection in the file. -/
structure Sound (Γ : List Term) (t t' A : Term) : Prop where
  /-- The two sides have the same approximants. -/
  eq : SoundEq Γ t t'
  /-- Semantic typing: every approximant is below a hereditarily typed
  one.  The right-hand side needs no field of its own: `SoundTy.of_eq`
  moves this one across `eq`. -/
  ty : SoundTy Γ t A
  /-- The clause conditions `Interp.to_substTerm` reads (§3.1d). -/
  pin : t.Pinned Γ
  /-- And for the right-hand side, which `symm` needs. -/
  pin' : t'.Pinned Γ

/-- Attach the two `Pinned` conclusions to a lemma that proves the other
two, so the atoms and the purely structural rules stay one-liners. -/
theorem and_pinned {Γ : List Term} {t t' A : Term}
    (h : SoundEq Γ t t' ∧ TypedAt Γ t A) (hp : t.Pinned Γ) (hp' : t'.Pinned Γ)
    (hd : SoundTy Γ t A) : Sound Γ t t' A :=
  ⟨h.1, hd, hp, hp'⟩

/-- The same, when the type only *filters* -- its approximants are never
binders, so the typing is already hereditary and saturation is free.
This is every atom and every type former. -/
theorem and_pinned_filter {Γ : List Term} {t t' A : Term} {u : Bool}
    (h : SoundEq Γ t t' ∧ TypedAt Γ t A) (hp : t.Pinned Γ) (hp' : t'.Pinned Γ)
    (hnb : ∀ {Δ : List Term} {σ ρ : _} {a : TShape}, Interp Δ Γ A σ ρ a → ¬ a.IsBinder)
    (hct : CodeAt Γ t) (hcA : SoundTy Γ A (.sort u)) :
    Sound Γ t t' A :=
  ⟨h.1, SoundTy.of_typedAt hnb h.2 hct hcA.codeAt, hp, hp'⟩

/-- The unit type names itself. -/
theorem CodeAt.unit {Γ : List Term} {r : Bool} : CodeAt Γ (Term.unit r) :=
  CodeAt.of_top Interp.le_unit (s := TShape.unit r)
    (fun _ _ => show TyEq _ _ _ from TyEq.refl .unit)

/-- So does an identity type, its label being the stage's instance. -/
theorem CodeAt.id {Γ : List Term} {r u : Bool} {A a b : Term} (hA : Γ ⊢ A : .sort u)
    (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : A) : CodeAt Γ (.id r A a b) := by
  intro Δ σ ρ hAdm m hm

  have hΔ := hAdm.ctx

  have W := hAdm.stage
  exact TShape.WF.mono hΔ (Interp.le_id hm)
    ⟨⟨u, hA.subst hΔ W⟩, ha.subst hΔ W, hb.subst hΔ W,
      (show TyEq _ _ _ from ⟨_, (IsDefEq.idDF (r := r) hA ha hb).subst hΔ W⟩)⟩

/-- A `refl` carries no names. -/
theorem CodeAt.refl {Γ : List Term} {r : Bool} {a : Term} : CodeAt Γ (.refl r a) := by
  intro Δ σ ρ hAdm m hm

  have hΔ := hAdm.ctx

  have W := hAdm.stage
  cases hm with
  | bot => exact TShape.WF.bot
  | refl hle => exact TShape.WF.mono hΔ hle  trivial

/-! ### The atoms' semantic typing, upfront

A sort, `unit`, `nat` and `zero` are each below one canonical shape, and
their types name themselves — so their cases of the induction below use
no induction hypothesis at all, and are theorems in their own right.  They
are also what lets the `CodeAt` premise on a *type* be a `SoundTy`: the
type of an atom is an atom, so the fact asked for is one of these. -/

theorem soundTy_sort {Γ : List Term} {r : Bool} : SoundTy Γ (.sort r) .type :=
  SoundTy.of_typedAt (fun ha => TShape.not_binder_of_le (Interp.le_sort ha) id)
    (sound_atom Interp.le_sort Interp.sort' .sort).2 CodeAt.sort CodeAt.sort

theorem soundTy_unit {Γ : List Term} {r : Bool} : SoundTy Γ (.unit r) (.sort r) :=
  SoundTy.of_typedAt (fun ha => TShape.not_binder_of_le (Interp.le_sort ha) id)
    (sound_atom Interp.le_unit Interp.sort' (.unit (fun x => x))).2 CodeAt.unit CodeAt.sort

theorem soundTy_nat {Γ : List Term} : SoundTy Γ Term.nat .type :=
  SoundTy.of_typedAt (fun ha => TShape.not_binder_of_le (Interp.le_sort ha) id)
    (sound_atom Interp.le_nat Interp.sort' .nat).2 CodeAt.nat CodeAt.sort

theorem soundTy_zero {Γ : List Term} : SoundTy Γ Term.zero Term.nat :=
  SoundTy.of_typedAt (fun ha => TShape.not_binder_of_le (Interp.le_nat ha) id)
    (sound_atom Interp.le_zero Interp.nat' .zero).2 (CodeAt.of_nat TypedAt.zero) CodeAt.nat

/-! ## η

An approximant of `e` is one of its expansion, and that is where the
slot discipline pays: saturation (`SoundTy`) gives a λ-approximant above
it whose entry inputs are *hereditarily* typed, which is exactly what
`Interp.lam`'s slot asks, and the expansion's bodies are then that
approximant's own lookups (`TEvaluates.refl`).  The original gets the
same effect from its λ clause, which reads the body at the input
normalised at the domain (§4.5g). -/

theorem sound_eta_of {Γ : List Term} {A B e : Term} {u : Bool} (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A : .sort u) (ihedom : SoundTy Γ e (.forallE A B))
    {Δ : List Term} {σ ρ} (hAdm : Adm Δ Γ σ ρ)
    {m : TShape} (hm : Interp Δ Γ e σ ρ m) :
    Interp Δ Γ (.lam A (.app e.lift (.bvar 0))) σ ρ m := by
  have hΔ := hAdm.ctx
  obtain ⟨m', p, hm', hle, hp, hNV, _⟩ := ihedom hAdm hm
  have hmbot : m.2 = Shape.bot → Interp Δ Γ (.lam A (.app e.lift (.bvar 0))) σ ρ m := by
    intro hb
    obtain ⟨k, s⟩ := m
    cases k with
    | zero => cases s with
      | bot => exact .bot
      | sort r => exact absurd hb (by simp [Shape.bot])
    | succ k =>
      cases s <;> first | exact .bot | exact absurd hb (by simp [Shape.bot])
  -- the code is an approximant of a Π, so it is `⊥` or a Π-shape
  have hpi : p.2 = Shape.bot ∨ p.IsPi := by
    cases hp with
    | bot => exact .inl rfl
    | forallE _ _ _ _ _ hlep _ _ => exact TShape.isPi_or_bot_of_le hlep trivial
  cases hNV with
  | base hnb hty _ =>
    -- not a Π-shape, so `⊥` — and then so is the subject
    have hb : p.2 = Shape.bot := hpi.resolve_right (fun h => hnb h.isBinder)
    exact hmbot (TShape.le_bot hΔ (TShape.HasType.bot_r hΔ hb hty) hle)
  | @pi _ n A' B' d f _ cs hty hent hin hev hout =>
    -- the dominating approximant is a λ-shape, and its entries' inputs
    -- are hereditarily typed at the Π's domain
    cases hty with
    | bot hb => exact hmbot (TShape.le_bot hΔ rfl hle)
    | refl hleid hAty =>
      -- a `refl`-shape is never typed at a Π code
      exact absurd hleid (by
        intro h
        obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ h
        exact absurd h2 (fun x => x))
    | @lam nm n₀ _ A₀ g _ _ _ _ g₀ hd hfo hwg hwPi hwg₀ hg hg₀ev hg₀ty hlab =>
      -- the Π-code's own label and domain, read off `hp`
      cases hp with
      | @forallE _ _ _ _ k g₁ d₁ _ _ hAint hdty₁ hwf₁ _ hbody₁ hle₁ _ _ =>
        obtain ⟨hPiLab, hdle, _⟩ := TShape.LE.forallE_decomp hΔ hle₁
          hwf₁
          (TEvaluates.refl hwf₁.2.2.2.1)
        have hAσ : TyEq Δ A₀ (A.subst σ) := TyEq.trans hlab hPiLab.1
        have hdA : Interp Δ Γ A σ ρ d.T :=
          Interp.mono hΔ hdle hAint
        -- the λ-shape, relabelled at the syntactic domain
        have hwg' : Shape.WF Δ (Shape.lam (A.subst σ) g) :=
          ⟨hwg.1, hwg.2.1, hwg.2.2.1.retype hAσ, hAσ.refl_r⟩
        refine .lam hdA hd hwg' (fun q hq => ?_) (fun q hq => ?_)
          ?_ ⟨u, hA⟩
        · -- the inputs: saturation put them there
          obtain ⟨pc, hpc, hpceq⟩ : ∃ pc ∈ cs, pc.1 = ⟨q.tm, q.inp.T, q.out.T⟩ := by
            have : (⟨q.tm, q.inp.T, q.out.T⟩ : Entry TShape) ∈
                (Shape.T (n := nm+1) (ShapeS.lam A₀ g)).entries :=
              List.mem_map_of_mem (f := fun e => (⟨e.tm, e.inp.T, e.out.T⟩ : Entry TShape)) hq
            rw [hent, List.mem_map] at this
            obtain ⟨pc, hpc, heq⟩ := this
            exact ⟨pc, hpc, heq⟩
          have := hin pc hpc
          rw [hpceq] at this
          exact this
        · -- the body: a lookup in the same λ-shape, at that entry
          have hwe := hwg.2.2.1.1 q hq
          have hm'' : Interp Δ Γ e (Subst.lift_l Lift.refl.skip (σ.cons q.tm)) ρ
              (Shape.T (n := nm+1) (ShapeS.lam A₀ g)) := hm'
          have hfun : Interp Δ (A :: Γ) e.lift (σ.cons q.tm) (ρ.push q.inp.T)
              (Shape.T (n := nm+1) (ShapeS.lam A₀ g)) :=
            Interp.weak' (Γ' := A :: Γ) (ρ' := ρ.push q.inp.T) hΓ hm'' (.skip .refl)
              (fun _ => rfl)
          have hstable : Stable Δ (A :: Γ) (σ.cons q.tm) (Term.bvar 0) A₀ := by
            refine Stable.of_typed (IsDefEq.bvar₀ ⟨hΓ, _, hA⟩ Lookup.zero) ?_
            show TyEq Δ A₀ ((A.lift).subst (σ.cons q.tm))
            rw [show (A.lift).subst (σ.cons q.tm) = A.subst σ from by
              rw [Term.lift, subst_lift']
              rfl]
            exact hAσ
          exact .app hfun
            (.bvar .zero (TShape.LE.refl (TShape.WF.T.2 hwe.2.2.1)))
            (.entry q hq ⟨hwg.2.2.2, hwe.2.1⟩
              (TShape.LE.refl (TShape.WF.T.2 hwe.2.2.1)))
            (TShape.LE.refl (TShape.WF.T.2 hwe.2.2.2)) hstable
        · -- and it dominates `m`, the labels being definitionally equal
          refine TShape.LE.trans hΔ hle ?_
          exact TShape.LE.T.2 ⟨ShapeFun.LE.refl hwg.2.2.1, hwg.1, hwg.2.1, hAσ, hwg.2.2.2⟩
  | @sg _ n A' B' d f _ cs hty hent hfst hin hev hout =>
    -- an approximant of a Π is never typed at a Σ code
    rcases hpi with hb | hpi'
    · exact absurd hb (TShape.IsSigma.not_bot
        (p := Shape.T (n := n+1) (ShapeS.sigma A' B' d f)) trivial)
    · exact absurd trivial (TShape.IsPi.not_sigma hpi')

/-- **η**, the easy direction: an approximant of the expansion is one of
`e`.  Each entry's body is a lookup in a λ-approximant of `e` one binder
up, `Interp.unweak` brings it down, directedness puts one approximant
above them all, and the lookup-coverage order (§5.2) is what lets the
expansion's graph be covered by it — an entry's output is a *join* of
outputs, which entry-by-entry coverage could not reach. -/
theorem sound_eta_to {Γ : List Term} {A B e : Term} {u : Bool} (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A : .sort u) (he : Γ ⊢ e : .forallE A B)
    (ihety : SoundTy Γ e (.forallE A B))
    {Δ : List Term} {σ ρ} (hAdm : Adm Δ Γ σ ρ)
    {m : TShape} (hm : Interp Δ Γ (.lam A (.app e.lift (.bvar 0))) σ ρ m) :
    Interp Δ Γ e σ ρ m := by
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have ihedir := (IsDefEq.dir hΓ he).1
  have hwρ := hAdm.wf
  cases hm with
  | bot => exact .bot
  | @lam _ _ _ _ n g d _ _ hdA hdty hwf _ hbody hle hAt =>
    -- each entry's body is an application of `e` one binder up
    have hent : ∀ q ∈ g, ∃ (k : Nat) (Aq : Term) (gq : ShapeFun k) (xq : TShape),
        Interp Δ Γ e σ ρ (Shape.T (n := k+1) (ShapeS.lam Aq gq)) ∧
        TShape.LE Δ xq q.inp.T ∧
        TEvaluates Δ gq Aq q.tm xq q.out.T := by
      intro q hq
      have hb := hbody q hq
      generalize hqo : (q.out.T : TShape) = mo at hb
      cases hb with
      | bot =>
        -- a well-formed λ-shape has no `⊥` output
        refine absurd (hwf.2.1 q hq) (fun h => h ?_)
        obtain ⟨qtm, qinp, qout⟩ := q
        cases n with
        | zero => cases qout <;> first | trivial | cases hqo
        | succ n => cases qout <;> first | trivial | cases hqo
      | @app _ _ _ _ _ _ k gq xq y Aq hF hx hev hley hst =>
        refine ⟨k, Aq, gq, xq, ?_, ?_, ?_⟩
        · -- the function, one binder down
          exact Interp.unweak_slot hΔ hΓ (.skip .refl) he.annot.1
            (.cons W hA (hwf.2.2.1.1 q hq).2.1) hF
        · exact Interp.le_bvar (i := 0) (ρ := ρ.push q.inp.T) hx
        · subst hqo
          exact .lower hley (by simpa using hev)
    -- per entry, a λ-approximant of `e` whose lookup covers that entry
    have hent' : ∀ q ∈ g, ∃ E : TShape, Interp Δ Γ e σ ρ E ∧ E.IsLam ∧
        ∀ {k : Nat} {A' : Term} {G : ShapeFun k},
          TShape.LE Δ E (Shape.T (n := k+1) (ShapeS.lam A' G)) →
          Shape.WF (n := k+1) Δ (ShapeS.lam A' G) →
          TEvaluates Δ G (A.subst σ) q.tm q.inp.T q.out.T := by
      intro q hq
      obtain ⟨k, Aq, gq, xq, hEq, hxle, hev⟩ := hent q hq
      refine ⟨_, hEq, trivial, ?_⟩
      intro k' A' G hEle hwG
      have hcov := TShape.LE.lam_decomp hΔ hEle hwG (TEvaluates.refl hwG.2.2.1)
      have h2 := TEvaluates.mono_inp hΔ hxle (TEvaluates.trans hΔ hcov hev)
      refine TEvaluates.label ?_ h2
      have hAq : TyEq Δ Aq (A.subst σ) := Interp.lam_label_ty hAdm ihety hEq
      exact ⟨hAq, hAq.symm.defeqDF (hwf.2.2.1.1 q hq).2.1⟩
    -- one approximant of `e` above all of them
    obtain ⟨g₀, hmap, hall⟩ := List.exists_pairs hent'
    obtain ⟨E, hwE, hE, hleE⟩ :=
      Interp.list_ub hΓ he hΔ W hwρ (ms := Prod.snd) g₀ (fun p hp => (hall p hp).1)
    -- it is a λ-shape, dominating one
    obtain ⟨q₀, hq₀⟩ : ∃ q, q ∈ g := by
      cases g with
      | nil => exact absurd rfl hwf.1
      | cons q g' => exact ⟨q, .head _⟩
    obtain ⟨p₀, hp₀, hp₀eq⟩ : ∃ p ∈ g₀, p.1 = q₀ := by
      have : q₀ ∈ g₀.map Prod.fst := by rw [hmap]; exact hq₀
      obtain ⟨p, hp, heq⟩ := List.mem_map.1 this
      exact ⟨p, hp, heq⟩
    have hLam : E.IsLam := TShape.isLam_of_le (hleE p₀ hp₀) (hall p₀ hp₀).2.1
    -- so it is `lam A' G`, and every entry of `g` is a lookup in `G`
    obtain ⟨kE, sE⟩ := E
    match kE, sE, hLam with
    | kE+1, .lam A' G, _ =>
      have hwE' : Shape.WF (n := kE+1) Δ (ShapeS.lam A' G) := hwE
      have hcov : ∀ q ∈ g, TEvaluates Δ G (A.subst σ) q.tm q.inp.T q.out.T := by
        intro q hq
        obtain ⟨p, hp, hpeq⟩ : ∃ p ∈ g₀, p.1 = q := by
          have : q ∈ g₀.map Prod.fst := by rw [hmap]; exact hq
          obtain ⟨p, hp, heq⟩ := List.mem_map.1 this
          exact ⟨p, hp, heq⟩
        have := (hall p hp).2.2 (hleE p hp) hwE'
        rw [hpeq] at this
        exact this
      refine Interp.mono hΔ (TShape.LE.trans hΔ hle ?_) hE
      -- the comparison, at a level above both graphs
      have hkn : n ≤ max n kE := Nat.le_max_left ..
      have hkE : kE ≤ max n kE := Nat.le_max_right ..
      have hlabE : TyEq Δ A' (A.subst σ) :=
        Interp.lam_label_ty hAdm ihety hE
      refine (TShape.LE.def hΔ (Nat.succ_le_succ hkn) (Nat.succ_le_succ hkE)).2 ?_
      refine ⟨⟨?_, (ShapeFun.lift_wf hkn).2 hwf.2.2.1,
          ((ShapeFun.lift_wf hkE).2 hwE'.2.2.1).retype hlabE⟩, ?_, ?_, hlabE.symm, hwf.2.2.2⟩
      · -- the coverage: each entry's output is a lookup in `G`
        intro e he
        obtain ⟨q, hq, rfl⟩ := ShapeFun.mem_lift.1 he
        have h1 := TEvaluates.lift_graph hΔ hkE
          (fun e he => ⟨(hwE'.2.2.1.1 e he).2.2.1, (hwE'.2.2.1.1 e he).2.2.2⟩) (hcov q hq)
        have h2 : TEvaluates Δ (ShapeFun.lift (Shape.lift (max n kE)) G) (A.subst σ) q.tm
            (Shape.T (q.inp.lift (max n kE))) q.out.T :=
          TEvaluates.mono_inp hΔ
            (TShape.LE.le_lift hΔ (m := q.inp.T) hkn (hwf.2.2.1.1 q hq).2.2.1) h1
        obtain ⟨c', hc', hev'⟩ := TEvaluates.toEval hΔ
          (((ShapeFun.lift_wf hkE).2 hwE'.2.2.1).retype hlabE)
          ((Shape.lift_wf hkn).2 (hwf.2.2.1.1 q hq).2.2.1) h2
        refine .lower ?_ hev'
        exact TShape.LE.T.1 (TShape.LE.trans hΔ
          (TShape.LE.lift_le hΔ (m := q.out.T) hkn (hwf.2.2.1.1 q hq).2.2.2) hc')
      · exact fun h => hwf.1 (by
          cases g with
          | nil => rfl
          | cons q g' => exact absurd h (by simp [ShapeFun.lift]))
      · intro e he
        obtain ⟨q, hq, rfl⟩ := ShapeFun.mem_lift.1 he
        exact fun hb => hwf.2.1 q hq ((Shape.lift_isBot hkn).1 hb)

/-- **The §4.7a label invariant.**  Every pair-approximant of `p` is
named by `p`'s *own* first projection.  It is what Σ's η needs, and it
is false for an admissibility that does not ask slots to name their
terms (§4.7i); with `Adm` asking that, it follows from saturation: the
pair-approximant sits below the saturated one, which names `fst p`, and
the order compares names. -/
theorem SoundTy.pair_name {Γ : List Term} {A B p : Term} (h : SoundTy Γ p (.sigma A B))
    {Δ : List Term} {σ ρ} (hAdm : Adm Δ Γ σ ρ)
    {n} {A₀ a₀ : Term} {x y : Shape n}
    (hP : Interp Δ Γ p σ ρ (Shape.T (n := n+1) (ShapeS.pair A₀ a₀ x y))) :
    Δ ⊢ a₀ ≡ (Term.fst p).subst σ : A₀ := by
  have hΔ := hAdm.ctx
  obtain ⟨P', _, _, hle, _, hNV, _⟩ := h hAdm hP
  obtain ⟨k, A', a', x', y', rfl⟩ := TShape.LE.pair_ub hle
  obtain ⟨hAA, haa, _, _⟩ := TShape.LE.pair_decomp hΔ hle
  -- the saturated pair's own name equation, read off `Named`'s Σ clause;
  -- the other two clauses cannot type a pair
  have hname : Δ ⊢ a' ≡ (Term.fst p).subst σ : A' := by
    cases hNV with
    | base hnb hty _ =>
      cases hty
      exact absurd trivial hnb
    | @pi _ _ _ _ _ _ _ _ hty _ _ _ _ => cases hty
    | @sg _ _ A₁ _ _ _ _ ps _ hty hps hnm _ _ _ =>
      have hlab : TyEq Δ A' A₁ := by
        cases hty
        assumption
      exact hlab.symm.defeqDF
        (hnm _ (show _ ∈ _ by rw [← hps]; rfl) _ rfl)
  exact haa.trans (hAA.symm.defeqDF hname)

/-- **Σ's η, the hard direction**: an approximant of `p` is one of
`⟨fst p, snd p⟩`.  Saturation hands a pair-approximant `P` above it; its
first component is an approximant of `fst p` by the `fst` clause, and its
second is one of `snd p` by the `snd` clause — which fires exactly
because `P`'s *name* is `fst p`.  So the expansion's pair is rebuilt on
`P`'s own components, and it dominates what `P` dominated. -/
theorem sound_fst_snd_of {Γ : List Term} {A B p : Term} {u v : Bool} (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) (hp : Γ ⊢ p : .sigma A B)
    (ihpty : SoundTy Γ p (.sigma A B))
    {Δ : List Term} {σ ρ} (hAdm : Adm Δ Γ σ ρ)
    {m : TShape} (hm : Interp Δ Γ p σ ρ m) :
    Interp Δ Γ (.pair A B (.fst p) (.snd p)) σ ρ m := by
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
  have ihBdir := (IsDefEq.dir hΓA hB).1
  have hwρ := hAdm.wf
  have hfst : Γ ⊢ .fst p : A := .fstDF hA hB hp
  have hAσ : Δ ⊢ A.subst σ : .sort u := hA.subst hΔ W
  have hfσ : Δ ⊢ (Term.fst p).subst σ : A.subst σ := hfst.subst hΔ W
  obtain ⟨P, S, hP, hle, hS, hNV, hScan⟩ := ihpty hAdm hm
  -- `⊥` is an approximant of anything
  have hbot : m.2 = Shape.bot → Interp Δ Γ (.pair A B (.fst p) (.snd p)) σ ρ m := by
    intro hb
    obtain ⟨k, s⟩ := m
    cases k with
    | zero => cases s with
      | bot => exact .bot
      | sort r => exact absurd hb (by simp [Shape.bot])
    | succ k => cases s <;> first | exact .bot | exact absurd hb (by simp [Shape.bot])
  have hSsg : S.2 = Shape.bot ∨ S.IsSigma := by
    cases hS with
    | bot => exact .inl rfl
    | sigma _ _ _ _ _ hles _ _ => exact TShape.isSigma_or_bot_of_le hles trivial
  cases hNV with
  | base hnb hty _ =>
    rcases hSsg with hb | hsg
    · exact hbot (TShape.le_bot hΔ (TShape.HasType.bot_r hΔ hb hty) hle)
    · exact absurd hsg.isBinder hnb
  | pi _ _ _ _ _ =>
    rcases hSsg with hb | hsg
    · exact absurd hb (TShape.IsPi.not_bot (p := Shape.T _) trivial)
    · exact absurd hsg (TShape.IsPi.not_sigma trivial)
  | @sg _ nS A' B' dS fS _ ps cc hty hps hnm hxd' hevc hout =>
    cases hty with
    | bot hb => exact hbot (TShape.le_bot hΔ rfl hle)
    | refl hleid hAty' =>
      exact absurd hleid (by
        intro h
        obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ h
        exact absurd h2 (fun x => x))
    | @pair nP _ A₀ a₀ x y _ _ _ _ _ _ hd hfo hwP hwSg hxd hxle hev hyty hlabP =>
      -- the Σ-code, decomposed
      cases hS with
      | @sigma _ _ _ _ nc gc dc _ _ hAint hdty hwfc _ hbodyc hleSg =>
        obtain ⟨hSgLab, hdle, hcov⟩ :=
          TShape.LE.sigma_decomp hΔ hleSg hwfc (TEvaluates.refl hwfc.2.2.2.1)
        have hxw : TShape.WF Δ (Shape.T x) := TShape.WF.T.2 hwP.2.2.2.1
        have hyw : TShape.WF Δ (Shape.T y) := TShape.WF.T.2 hwP.2.2.2.2
        have hAlab : TyEq Δ A₀ (A.subst σ) := Interp.pair_label_ty hAdm ihpty hP
        -- the name is the subject's own first projection
        have hname : Δ ⊢ a₀ ≡ (Term.fst p).subst σ : A₀ := by
          have h := hSgLab.1.defeqDF
            (hnm _ (show _ ∈ _ by rw [← hps]; rfl) _ rfl)
          simpa using hAlab.symm.defeqDF h
        -- the two components are the projections' approximants
        have hxI : Interp Δ Γ (.fst p) σ ρ (Shape.T x) := .fst hP (TShape.LE.refl hxw)
        have hyI : Interp Δ Γ (.snd p) σ ρ (Shape.T y) :=
          .snd hP hname (TShape.LE.refl hyw) (Stable.of_typed hfst hAlab)
        -- the code for `B[fst p]`, read at the pair's own name
        have hIc : Interp Δ (A :: Γ) B (σ.cons ((Term.fst p).subst σ))
            (ρ.push (Shape.T x)) cc := by
          refine Interp.stage hΔ hΓA hB.annot.1
            (Ctx.SubstEq.cons (σ := σ.cons a₀) W hA ?_) ?_
          · exact hAlab.defeqDF hname
          · refine sound_graph_lookup hΓA hA hB hΔ W hbodyc hxw hwρ
              (show Δ ⊢ a₀ : A' from hlabP.defeqDF hwP.2.1)
              hSgLab.1 (TEvaluates.trans hΔ hcov (hevc _ (by rw [← hps]; rfl)))
        -- the expansion's pair, on the dominator's own components
        have hwf : Shape.WF (n := nP+1) Δ
            (ShapeS.pair (A.subst σ) ((Term.fst p).subst σ) x y) :=
          ⟨hwP.1, hfσ, TyEq.refl hAσ, hwP.2.2.2.1, hwP.2.2.2.2⟩
        have hwf' : TShape.WF Δ (Shape.T (n := nP+1) _) := TShape.WF.T.2 hwf
        refine Interp.pair (c := cc) hxI hyI
          (Interp.mono hΔ hdle hAint)
          (TShape.HasType.mono_l hΔ hdty hdle)
          ⟨by simpa using hxd' _ (show _ ∈ _ by rw [← hps]; rfl),
            Shape.WF.conv hwSg.2.2.1 (TyEq.symm hSgLab.1)⟩
          hwf hIc (by simpa using (hout _ (show _ ∈ _ by rw [← hps]; rfl)).forget)
          ?_ ⟨u, hA⟩ hfst
        · -- and it dominates `m`, the name moved to `fst p`
          refine TShape.LE.trans hΔ hle (TShape.LE.T.2
            (show Shape.LE (n := nP+1) Δ (ShapeS.pair ..) (ShapeS.pair ..) from
              ⟨Shape.LE.refl hwP.2.2.2.1, Shape.LE.refl hwP.2.2.2.2, hwP.1, hAlab, hname⟩))

/-- **Σ's η, the easy direction**: an approximant of `⟨fst p, snd p⟩` is
one of `p`.  With the graph gone this is true, where with it it was not
(§4.7e): the expansion's pair has no inputs to promise a second
component at, so its two components are approximants of the projections
and nothing more.  Each comes from a pair-approximant of `p`; one
directedness step puts both under a single one, whose name is `fst p`
by canonicity, and the order then compares. -/
theorem sound_fst_snd_to {Γ : List Term} {A B p : Term} {u v : Bool}
    (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) (hp : Γ ⊢ p : .sigma A B)
    (ihpty : SoundTy Γ p (.sigma A B))
    {Δ : List Term} {σ ρ} (hAdm : Adm Δ Γ σ ρ)
    {m : TShape} (hm : Interp Δ Γ (.pair A B (.fst p) (.snd p)) σ ρ m) :
    Interp Δ Γ p σ ρ m := by
  have hΔ := hAdm.ctx
  have W := hAdm.stage
  have ihpdir := (IsDefEq.dir W.wf hp).1
  have hwρ := hAdm.wf
  have hfst : Γ ⊢ .fst p : A := .fstDF hA hB hp
  cases hm with
  | bot => exact .bot
  | @pair _ _ _ _ n x y _ _ _ _ _ _ hx hy _ _ _ hwf _ _ hle _ _ =>
    -- the two components come from two pair-approximants of `p`
    cases hx with
    | bot =>
      cases hy with
      | bot => exact absurd ⟨Shape.isBot_bot, Shape.isBot_bot⟩ hwf.1
      | snd hP₂ hlab₂ hle₂ hst₂ =>
        refine Interp.mono hΔ (TShape.LE.trans hΔ hle ?_) hP₂
        have hAP := Interp.pair_label_ty hAdm ihpty hP₂
        exact TShape.LE.pair_mk hΔ (TShape.bot_le' rfl) hle₂ hwf.1 (TyEq.symm hAP)
          (hAP.defeqDF (ihpty.pair_name hAdm hP₂).symm)
    | fst hP₁ hlex =>
      cases hy with
      | bot =>
        refine Interp.mono hΔ (TShape.LE.trans hΔ hle ?_) hP₁
        have hAP := Interp.pair_label_ty hAdm ihpty hP₁
        exact TShape.LE.pair_mk hΔ hlex (TShape.bot_le' rfl) hwf.1 (TyEq.symm hAP)
          (hAP.defeqDF (ihpty.pair_name hAdm hP₁).symm)
      | snd hP₂ hlab₂ hley hst₂ =>
        -- one pair-approximant above both
        obtain ⟨P, hwP, hP, hleP₁, hleP₂⟩ := ihpdir hΔ W hwρ hP₁ hP₂
        obtain ⟨k, A', a', x', y', rfl⟩ := TShape.LE.pair_ub hleP₁
        obtain ⟨_, _, hx₁, _⟩ := TShape.LE.pair_decomp hΔ hleP₁
        obtain ⟨_, _, _, hy₂⟩ := TShape.LE.pair_decomp hΔ hleP₂
        refine Interp.mono hΔ (TShape.LE.trans hΔ hle ?_) hP
        have hAP := Interp.pair_label_ty hAdm ihpty hP
        exact TShape.LE.pair_mk hΔ (TShape.LE.trans hΔ hlex hx₁)
          (TShape.LE.trans hΔ hley hy₂) hwf.1 (TyEq.symm hAP)
          (hAP.defeqDF (ihpty.pair_name hAdm hP).symm)

/-- The four conclusions proved by the induction itself.  `Sound` adds
saturation on top, which is where the remaining work is (§4.5g). -/
theorem IsDefEq.sound {Γ : List Term} {t t' A : Term}
    (hΓ : ⊢ Γ) (H : Γ ⊢ t ≡ t' : A) : Sound Γ t t' A := by
  induction H with
  -- structural rules: no stage or valuation changes, so these are pure
  -- bookkeeping on the two conclusions
  | @symm _ _ _ _ hs ih =>
    have ⟨he, hd, hpL, hpR⟩ := ih hΓ
    exact ⟨he.symm, SoundTy.of_eq hs he hd, hpR, hpL⟩
  | trans _ _ ih₁ ih₂ =>
    have ⟨he₁, hd₁, hp₁, _⟩ := ih₁ hΓ
    have ⟨he₂, _, _, hp₂⟩ := ih₂ hΓ
    exact ⟨he₁.trans he₂, hd₁, hp₁, hp₂⟩
  | trans' _ _ ih₁ ih₂ =>
    have ⟨he₁, hd₁, hp₁, _⟩ := ih₁ hΓ
    have ⟨he₂, _, _, hp₂⟩ := ih₂ hΓ
    exact ⟨he₁.trans he₂, hd₁, hp₁, hp₂⟩
  -- conversion: only the *type*'s interpretation moves, and `SoundEq` of
  -- the two types is exactly what moves it
  | @defeqDF _ _ _ _ _ _ hAB _ ihAB ih =>
    have ⟨heAB, _, _, _⟩ := ihAB hΓ
    have ⟨he, hd, hpL, hpR⟩ := ih hΓ
    exact ⟨he, SoundTy.of_tyEq hAB heAB hd, hpL, hpR⟩
  -- everything below is one rule of the induction, each an independent
  -- obligation; see §4 of `presheaf-proof-strategy.md` for what each needs
  -- the slot's typing is `Adm`'s own, read off at the index by `Adm.lookup`
  | @bvar _ _ _ _ hl hA _ =>
    exact ⟨SoundEq.refl, SoundTy.bvar hl, trivial, trivial⟩
  | sort =>
    exact ⟨(sound_atom Interp.le_sort Interp.sort' .sort).1, soundTy_sort, trivial, trivial⟩
  | @unit _ r =>
    exact ⟨(sound_atom Interp.le_unit Interp.sort' (.unit (fun x => x))).1,
      soundTy_unit, trivial, trivial⟩
  | star =>
    exact and_pinned (sound_of_bot (fun .bot => rfl) (fun .bot => rfl))
      trivial trivial (SoundTy.of_bot (by intro _ _ _ _ _ h; cases h; rfl))
  -- the lookup, typed: `SoundEq` moves the query's term along `a ≡ a'`,
  -- and `SoundTy` walks the generator chain of `HasType.lam`
  | @appDF _ A u B v f f' a a' hA hB hff' haa' hBinst ihA ihB ihf iha ihBinst =>
    have hΓA : ⊢ (A :: _) := ⟨hΓ, _, hA.hasType.1⟩
    have ⟨hef, hd_ihf, hpf, hpf'⟩ := ihf hΓ
    have ⟨hea, hd_iha, hpa, hpa'⟩ := iha hΓ
    exact ⟨sound_app_eq hff' haa' hd_ihf hef hea,
      sound_app_dom (ihB hΓA).pin hΓ hA.hasType.1 hB.hasType.1 haa'.hasType.1 hd_iha
        hff'.hasType.1 hd_ihf (ihBinst hΓ).ty,
      ⟨PinApp.of_sound hd_ihf haa'.hasType.1, hpf, hpa⟩,
      ⟨PinApp.of_sound (SoundTy.of_eq hff' hef hd_ihf) haa'.hasType.2, hpf', hpa'⟩⟩
  | @lamDF _ A A' u B v body body' hAA' hB hbody hbody' hPi ihA ihB ihbody ihbody' ihPi =>
    have hΓA : ⊢ (A :: _) := ⟨hΓ, _, hAA'.hasType.1⟩
    have hΓA' : ⊢ (A' :: _) := ⟨hΓ, _, hAA'.hasType.2⟩
    have ⟨heA, hd_ihA, hpA, hpA'⟩ := ihA hΓ
    exact ⟨sound_lam_eq hAA' heA hd_ihA (ihbody hΓA).eq (ihbody' hΓA').eq,
      sound_lam_dom hΓ hAA'.hasType.1 hB hbody.hasType.1 hd_ihA (ihB hΓA).ty
        (ihbody hΓA).ty,
      ⟨hd_ihA.isTypeAt, hpA, (ihbody hΓA).pin⟩,
      ⟨(SoundTy.of_eq hAA' heA hd_ihA).isTypeAt, hpA',
        (ihbody' hΓA').pin'⟩⟩
  -- the two halves proved above
  | forallEDF hAA' hB hB' ihA ihB ihB' =>
    have ⟨heA, hd_ihA, hpA, hpA'⟩ := ihA hΓ
    have ⟨heB, hd_ihB, hpB, _⟩ := ihB ⟨hΓ, _, hAA'.hasType.1⟩
    have ⟨heB', hd_ihB', _, hpB'⟩ := ihB' ⟨hΓ, _, hAA'.hasType.2⟩
    exact ⟨sound_forallE_eq hAA' hB hB' heA hd_ihA heB heB',
      SoundTy.of_sort (sound_forallE_typedAt hd_ihA hd_ihB hAA'.hasType.1)
        (CodeAt.forallE hAA'.hasType.1 hB.hasType.1),
      ⟨hd_ihA.isTypeAt, hpA, hpB⟩,
      ⟨(SoundTy.of_eq hAA' heA hd_ihA).isTypeAt, hpA', hpB'⟩⟩
  -- Σ now has real rules, mirroring Π, so these are no longer vacuous
  | sigmaDF hAA' hB hB' ihA ihB ihB' =>
    have ⟨heA, hd_ihA, hpA, hpA'⟩ := ihA hΓ
    have ⟨heB, hd_ihB, hpB, _⟩ := ihB ⟨hΓ, _, hAA'.hasType.1⟩
    have ⟨heB', hd_ihB', _, hpB'⟩ := ihB' ⟨hΓ, _, hAA'.hasType.2⟩
    exact ⟨sound_sigma_eq hAA' hB hB' heA hd_ihA heB heB',
      SoundTy.of_sort (sound_sigma_typedAt hd_ihA hd_ihB hAA'.hasType.1)
        (CodeAt.sigma hAA'.hasType.1 hB.hasType.1),
      ⟨hd_ihA.isTypeAt, hpA, hpB⟩,
      ⟨(SoundTy.of_eq hAA' heA hd_ihA).isTypeAt, hpA', hpB'⟩⟩
  | @pairDF _ A A' u B v B' a a' b b' hAA' hB hB' haa' hbb' hBa hSg
      ihA ihB ihB' iha ihb ihBa ihSg =>
    have hΓA : ⊢ (A :: _) := ⟨hΓ, _, hAA'.hasType.1⟩
    have hΓA' : ⊢ (A' :: _) := ⟨hΓ, _, hAA'.hasType.2⟩
    have ⟨heA, hd_ihA, hpA, hpA'⟩ := ihA hΓ
    have ⟨_, hd_ihB, hpB, _⟩ := ihB hΓA
    have ⟨_, hd_ihB', _, hpB'⟩ := ihB' hΓA'
    have ⟨hea, hd_iha, hpa, hpa'⟩ := iha hΓ
    have ⟨_, hd_ihb, hpb, hpb'⟩ := ihb hΓ
    exact ⟨sound_pair_eq hAA' haa' hB.hasType.1 hB'.hasType.2 heA hea (ihb hΓ).eq
        (ihB hΓA).eq (ihB' hΓA').eq,
      sound_pair_dom hΓ hAA'.hasType.1 hB.hasType.1 haa'.hasType.1 hbb'.hasType.1 hpB
        hd_ihA hd_iha hd_ihb (ihB hΓA).ty,
      ⟨hd_ihA.isTypeAt, hpA, hpB, hpa, hpb⟩,
      ⟨(SoundTy.of_eq hAA' heA hd_ihA).isTypeAt, hpA', hpB',
        hpa', hpb'⟩⟩
  | fstDF hA hB _ _ _ ih =>
    have ⟨he, hd, hp, hp'⟩ := ih hΓ
    exact and_pinned (sound_fst he hd) hp hp' (sound_fst_dom hd)
  | @sndDF _ A u B v p p' hA hB hpp' hBfst ihA ihB ihp ihBfst =>
    have hΓA : ⊢ (A :: _) := ⟨hΓ, _, hA.hasType.1⟩
    have hfst := IsDefEq.fstDF hA hB hpp'.hasType.1
    have ⟨hep, hd_ihp, hpp, hpp2⟩ := ihp hΓ
    exact ⟨sound_snd_eq hA hB hpp' hd_ihp hep,
      sound_snd_dom (ihB hΓA).pin hΓ hA hB hfst
        (sound_fst_dom hd_ihp) hd_ihp (ihBfst hΓ).ty,
      ⟨PinSnd.of_sound hd_ihp hfst, hpp⟩,
      ⟨PinSnd.of_sound (SoundTy.of_eq hpp' hep hd_ihp)
        (IsDefEq.fstDF hA hB hpp'.hasType.2), hpp2⟩⟩
  -- padded with typings of both sides, so `SoundTy` is the IH for the
  -- left-hand side and only `SoundEq` has content
  | @beta _ A u e B e' hA hbe he' hredex _ ihA ihe ihe' ihredex ihrhs =>
    have hΓA : ⊢ (A :: _) := ⟨hΓ, _, hA.hasType.1⟩
    exact ⟨sound_beta (ihe hΓA).pin hΓ hA.hasType.1 hbe.hasType.1
        he'.hasType.1 (ihA hΓ).ty (ihe' hΓ).ty, (ihredex hΓ).ty, (ihredex hΓ).pin, (ihrhs hΓ).pin⟩
  | @eta _ A B e he hexp ihe ihexp =>
    obtain ⟨v, hPi⟩ := IsDefEq.isType hΓ he
    obtain ⟨u, hA⟩ := hPi.forallE_dom
    refine ⟨fun Δ σ ρ hAdm m => ?_, (ihexp hΓ).ty, (ihexp hΓ).pin, (ihe hΓ).pin⟩
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact sound_eta_to hΓ hA he.hasType.1 (ihe hΓ).ty hAdm h
    · exact sound_eta_of hΓ hA (ihe hΓ).ty hAdm h
  | @unit_eta _ _ r _ ih =>
    refine and_pinned (sound_of_bot_at
      (sound_of_bot (t := .star r) (t' := .star r) (A := .unit r)
        (fun .bot => rfl) (fun .bot => rfl)).2
      (by intro _ _ _ _ _ h; cases h; rfl)
      (by intro _ _ _ hAdm _ h; exact Interp.eq_bot_of_unit (ih hΓ).ty hAdm h))
      trivial (ih hΓ).pin (SoundTy.of_bot (by intro _ _ _ _ _ h; cases h; rfl))
  -- unblocked by the Σ rules: `fst` now reads the first component off a
  -- pair shape, so the two sides really can have the same approximants
  -- the β-rules of Σ: the projection's approximants are the component's,
  -- and the typing then comes from the component's by `SoundTy.of_eq`
  | @pair_fst _ A u B v a b hA hB ha hb hfst ihA _ iha _ ihlhs =>
    have he := sound_pair_fst (B := B) (b := b) hA.hasType.1 ha.hasType.1
      (ihA hΓ).ty (iha hΓ).ty
    exact ⟨he, (ihlhs hΓ).ty,
      (ihlhs hΓ).pin, (iha hΓ).pin⟩
  | @pair_snd _ A u B v a b hA hB ha hb hsnd ihA ihB iha ihb ihlhs =>
    -- `snd`'s rule is a query at `fst`, so this case needs the β-rule for
    -- `fst` as well, which its own premises give
    have hpair := IsDefEq.pairDF hA hB hB ha hb
      (IsDefEq.inst_cod hΓ hA.hasType.1 ha.hasType.1 hB) (IsDefEq.sigmaDF hA hB hB)
    have hfst := IsDefEq.pair_fst hA.hasType.1 hB.hasType.1 ha.hasType.1 hb.hasType.1
      (IsDefEq.fstDF hA.hasType.1 hB.hasType.1 hpair)
    have he := sound_pair_snd (B := B) (v := v) hΓ hA.hasType.1 hB.hasType.1
      ha.hasType.1 (ihB ⟨hΓ, _, hA.hasType.1⟩).pin hfst (ihA hΓ).ty (iha hΓ).ty (ihb hΓ).ty
    exact ⟨he, (ihlhs hΓ).ty, (ihlhs hΓ).pin, (ihb hΓ).pin⟩
  | @fst_snd Γ p A B hp hpair ihp ihpair =>
    -- both directions of Σ's η, against the one condition the model does
    -- not yet give: a pair-approximant's name is the subject's own first
    -- projection (§4.7a, `SoundTy.pair_name`)
    obtain ⟨hAty, hpb, hpB, hpa⟩ := (ihpair hΓ).pin
    obtain ⟨_, hSg⟩ := (hp.isType hΓ)
    obtain ⟨u, hA⟩ := IsDefEq.sigma_dom hSg
    obtain ⟨v, hB⟩ := IsDefEq.sigma_cod hSg
    have hΓA : ⊢ (A :: Γ) := ⟨hΓ, _, hA⟩
    have he : SoundEq Γ (.pair A B (.fst p) (.snd p)) p := by
      intro Δ σ ρ hAdm m
      -- a pair-approximant's name is the subject's own first projection,
      -- because the saturated one names it (§4.7i)
      exact ⟨sound_fst_snd_to hA hB hp (ihp hΓ).ty hAdm,
        sound_fst_snd_of hΓ hA hB hp (ihp hΓ).ty hAdm⟩
    exact ⟨he, (ihpair hΓ).ty, (ihpair hΓ).pin, (ihp hΓ).pin⟩
  | nat =>
    exact ⟨(sound_atom Interp.le_nat Interp.sort' .nat).1, soundTy_nat, trivial, trivial⟩
  | zero =>
    exact ⟨(sound_atom Interp.le_zero Interp.nat' .zero).1, soundTy_zero, trivial, trivial⟩
  | succDF _ ih =>
    have ⟨he, hd, hp, hp'⟩ := ih hΓ
    exact and_pinned_filter (sound_succ he hd) hp hp'
      (fun ha => TShape.not_binder_of_le (Interp.le_nat ha) id)
      (CodeAt.of_nat (sound_succ he hd).2) soundTy_nat
  | @natCaseDF _ v C C' M M' a a' b b' hCC' hMM' haa' hbb' hCM ihC ihM iha ihb ihCM =>
    have hΓN : ⊢ (Term.nat :: _) := ⟨hΓ, _, .nat⟩
    have ⟨heM, hd_ihM, hpM, hpM'⟩ := ihM hΓ
    have ⟨_, hd_ihC, hpC, hpC'⟩ := ihC hΓN
    have ⟨_, hd_iha, hpa, hpa'⟩ := iha hΓ
    have ⟨_, hd_ihb, hpb, hpb'⟩ := ihb hΓN
    exact ⟨sound_natCase hMM' heM hd_ihM (iha hΓ).eq (ihb hΓN).eq,
      sound_natCase_dom hΓ (ihC hΓN).pin hCC'.hasType.1 haa'.hasType.1 hbb'.hasType.1
        (ihCM hΓ).ty (iha hΓ).ty (ihb hΓN).ty hMM'.hasType.1 hd_ihM,
      ⟨hd_ihM.typedAt, hpC, hpM, hpa, hpb⟩,
      ⟨(SoundTy.of_eq hMM' heM hd_ihM).typedAt, hpC', hpM', hpa', hpb'⟩⟩
  -- the computation rules again: padded, so `SoundTy` is an IH
  | natCase_zero _ _ _ _ _ iha _ ihredex =>
    exact ⟨sound_natCase_zero, (ihredex hΓ).ty,
      (ihredex hΓ).pin, (iha hΓ).pin⟩
  | @natCase_succ _ C v n a b _ hn _ hb _ _ _ ihn _ ihb ihredex ihrhs =>
    exact ⟨sound_natCase_succ (ihb ⟨hΓ, _, .nat⟩).pin hΓ hn.hasType.1 hb.hasType.1 (ihn hΓ).ty,
      (ihredex hΓ).ty, (ihredex hΓ).pin, (ihrhs hΓ).pin⟩
  | @YDF _ A A' u b b' hAA' hb hb' ihA ihb ihb' =>
    have hΓA : ⊢ (A :: _) := ⟨hΓ, _, hAA'.hasType.1⟩
    have hΓA' : ⊢ (A' :: _) := ⟨hΓ, _, hAA'.hasType.2⟩
    have hYY' : _ ⊢ Term.Y A b ≡ Term.Y A' b' : A := .YDF hAA' hb hb'
    have ⟨heA, hd_ihA, hpA, hpA'⟩ := ihA hΓ
    have htyA' := SoundTy.of_eq hAA' heA hd_ihA
    have htyb' := SoundTy.of_eq hb' (ihb' hΓA').eq (ihb' hΓA').ty
    have hYty := sound_Y_typedAt hΓ hAA'.hasType.1 hYY'.hasType.1 hd_ihA (ihb hΓA).ty
    have hYty' := sound_Y_typedAt hΓ hAA'.hasType.2
      (IsDefEq.YDF hAA'.hasType.2 hb'.hasType.2 hb'.hasType.2) htyA' htyb'
    exact ⟨sound_Y_eq hΓ hAA' hYY' hb hb' heA hd_ihA
        (ihb hΓA).ty (ihb hΓA).eq htyb' (ihb' hΓA').eq.symm,
      sound_Y_dom hΓ hAA'.hasType.1 hYY'.hasType.1 hd_ihA hb.hasType.1 (ihb hΓA).ty,
      ⟨hd_ihA.isTypeAt, hYty, hpA, (ihb hΓA).pin⟩,
      ⟨(SoundTy.of_eq hAA' heA hd_ihA).isTypeAt, hYty', hpA', (ihb' hΓA').pin'⟩⟩
  | @Y_unfold _ A u b hA hb hY hunf ihA ihb ihY ihrhs =>
    exact ⟨sound_Y_unfold hΓ (ihb ⟨hΓ, _, hA.hasType.1⟩).pin
        hA.hasType.1 hb.hasType.1 hY.hasType.1 (ihA hΓ).ty
        (ihY hΓ).ty, (ihY hΓ).ty, (ihY hΓ).pin, (ihrhs hΓ).pin⟩
  | idDF hAA' haa' hbb' ihA iha ihb =>
    exact and_pinned_filter (sound_id hAA' haa' hbb')
      ⟨(ihA hΓ).pin, (iha hΓ).pin, (ihb hΓ).pin⟩
      ⟨(ihA hΓ).pin', (iha hΓ).pin', (ihb hΓ).pin'⟩
      (fun ha => TShape.not_binder_of_le (Interp.le_sort ha) id)
      (CodeAt.id hAA'.hasType.1 haa'.hasType.1 hbb'.hasType.1) soundTy_sort
  | reflDF hA haa' hid _ iha _ =>
    exact and_pinned_filter (sound_refl hA haa' hid) (iha hΓ).pin
      (iha hΓ).pin' (fun ha => TShape.not_binder_of_le (Interp.le_id ha) id)
      CodeAt.refl (SoundTy.of_sort (sound_id hA haa' haa').2
        (CodeAt.id hA haa'.hasType.1 haa'.hasType.1))
  | @trDF _ A A' u a a' b b' v C C' X X' r H H' hAA' haa' hbb' hC hC' hXX' hHH' hCb hid
      ihA iha ihb ihC ihC' ihX ihH =>
    have hΓA : ⊢ (A :: _) := ⟨hΓ, _, hAA'.hasType.1⟩
    have hΓA' : ⊢ (A' :: _) := ⟨hΓ, _, hAA'.hasType.2⟩
    have ⟨heA, hd_ihA, hpA, hpA'⟩ := ihA hΓ
    have ⟨_, hd_iha, hpa, hpa'⟩ := iha hΓ
    have ⟨_, hd_ihb, hpb, hpb'⟩ := ihb hΓ
    have ⟨_, hd_ihC, hpC, _⟩ := ihC hΓA
    have ⟨_, hd_ihC', _, hpC'⟩ := ihC' hΓA'
    have ⟨_, hd_ihX, hpX, hpX'⟩ := ihX hΓ
    have ⟨_, hd_ihH, hpH, hpH'⟩ := ihH hΓ
    exact ⟨sound_tr_eq hΓ hAA' haa' hbb' hC hC' hXX' hHH' heA (iha hΓ).eq
        (ihb hΓ).eq (ihC hΓA).eq (ihC' hΓA').eq (ihX hΓ).eq,
      sound_tr_dom hΓ hpC hAA'.hasType.1 haa'.hasType.1 hbb'.hasType.1 hC.hasType.1
        hXX'.hasType.1 hHH'.hasType.1 (ihb hΓ).ty,
      ⟨hd_ihA.isTypeAt, hpA, hpa, hpb, hpC, hpX, hpH⟩,
      ⟨(SoundTy.of_eq hAA' heA hd_ihA).isTypeAt, hpA', hpa',
        hpb', hpC', hpX', hpH'⟩⟩
  | @tr_refl _ A u a v C X r hA ha hC hx htr ihA iha ihC ihx ihtr =>
    exact ⟨sound_tr_refl_eq (ihC ⟨hΓ, _, hA⟩).pin hΓ hA ha hC (iha hΓ).ty
        (ihC ⟨hΓ, _, hA⟩).ty (ihx hΓ).ty, (ihtr hΓ).ty, (ihtr hΓ).pin, (ihx hΓ).pin⟩
  -- both sides are typed at a proposition, so both collapse to `⊥`
  | proofIrrel _ _ _ ih₁ ih₂ ih₃ =>
    refine and_pinned (sound_of_bot_at (ih₂ hΓ).ty.typedAt
      (by intro _ _ _ hAdm _ h
          exact Interp.eq_bot_of_prop (ih₁ hΓ).ty (ih₂ hΓ).ty hAdm h)
      (by intro _ _ _ hAdm _ h
          exact Interp.eq_bot_of_prop (ih₁ hΓ).ty (ih₃ hΓ).ty hAdm h))
      (ih₂ hΓ).pin (ih₃ hΓ).pin
      (SoundTy.of_bot (by
        intro _ _ _ hAdm _ h
        exact Interp.eq_bot_of_prop (ih₁ hΓ).ty (ih₂ hΓ).ty hAdm h))

/-- **Semantic typing.**  Every approximant of a well-typed term is below
one that is hereditarily typed: the original's `HasFixedness`
(`rawExtend ⟦A⟧ ⟦t⟧ = ⟦t⟧`), read through "ideal = set of approximants".
It is a conclusion of the induction above, and it has to be *that* -- not
a theorem of its own -- because the slot discipline makes the other three
depend on it: η needs it at the function, `Interp.lam`'s slot needs it at
the argument, and `Adm` needs it at every variable. -/
theorem IsDefEq.soundTy {Γ : List Term} {t A : Term} (hΓ : ⊢ Γ) (ht : Γ ⊢ t : A) :
    SoundTy Γ t A := (IsDefEq.sound hΓ ht).ty

/-- **Every well-typed term is pinned.**  This was the development's last
assumption before saturation; it is the third conclusion of the induction
above, which is where the original proves its `HasFixedness` too -- a
field of `RawTermProperties`, alongside substitution. -/
theorem IsDefEq.pinned {Γ : List Term} {t T : Term} (hΓ : ⊢ Γ) (ht : Γ ⊢ t : T) :
    t.Pinned Γ := (IsDefEq.sound hΓ ht).pin
