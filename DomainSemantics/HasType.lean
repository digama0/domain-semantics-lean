import DomainSemantics.Shape

/-! # Typing of labelled shapes

`TShape.HasType Δ m a` says the shape `m` is a well-typed inhabitant of
the type-shape `a`.  It is one inductive over `TShape`, the shapes at all
levels; see the section heading below it for why, and §5.5/§5.5a of
`presheaf-proof-strategy.md` for the history.

Before it comes the machinery it is built on: `Evaluates`, the relational
graph lookup at a fixed level (`ShapeOld.lean`'s `ShapeFun.app` was a
function, correct only because graphs were saturated; saturation is gone,
so the codomain type comes from a relation, which is also how the other
repo reads it — `rawExtend T X` quantifies `∃ c ∈ T`), and `TEvaluates`,
the same lookup over `TShape`, which is where all the level bookkeeping
happens once.

Together with `SoundTy` this plays the role of the other repo's decoder:
see §4.2 of `presheaf-plan.md`.  Its fixed-point construction
(`piStep`/`piStage`/`rank`/`piLimit`) is unnecessary here because the
recursion is structural in the level. -/

namespace DomainSemantics

variable {Δ : List Term}

/-- Relational graph lookup: `Evaluates Δ f A a x y` says `y` approximates
the result of applying the graph `f`, at the argument label `(A, a)`, to an
input at least `x`.

It is `ShapeFun.Eval` at `R := Shape.LE Δ` — the *same* relation the order
on graphs is built from (`Shape.lean`), which is why it has to be declared
there, parameterised by the order one level down.  Replacing `ShapeFun.app`
(a function) by this (a relation) is what lets us drop saturation: the join
of several matching entries is available here without having to be stored
in the graph. -/
@[reducible] def Evaluates (Δ : List Term) {n} (f : ShapeFun n) (A a : Term)
    (x c : Shape n) : Prop := ShapeFun.Eval Δ (Shape.LE Δ) f A a x c

namespace Evaluates
variable {Δ : List Term} {n} {f : ShapeFun n} {A a : Term} {x : Shape n}

@[match_pattern] abbrev bot : Evaluates Δ f A a x .bot := ShapeFun.Eval.bot
@[match_pattern] abbrev entry (e : Entry (Shape n)) (he : e ∈ f)
    (hl : LabelEq Δ e.ty e.tm A a) (hin : Shape.LE Δ e.inp x) :
    Evaluates Δ f A a x e.out := ShapeFun.Eval.entry e he hl hin
@[match_pattern] abbrev lower {y z} (hle : Shape.LE Δ y z)
    (h : Evaluates Δ f A a x z) : Evaluates Δ f A a x y := ShapeFun.Eval.lower hle h
@[match_pattern] abbrev join {y z} (hc : Shape.Compat Δ y z)
    (hy : Evaluates Δ f A a x y) (hz : Evaluates Δ f A a x z) :
    Evaluates Δ f A a x (y.join z) := ShapeFun.Eval.join hc hy hz

end Evaluates

/-- The **β-law**, and it is nearly free here: looking a graph up at one of
its own entries returns that entry's output.

The other repo needs a real lemma for this
(`rawApplication_abstraction_eq_value`: applying an abstraction recovers
the action it was built from), because its λ-value is an abstraction
*operator* and recovering the action needs finitarity and
ideal-valuedness.  Our λ-shape carries the graph itself, and the graph is
a `List`, so finitarity is structural and β is one constructor. -/
theorem Evaluates.entry_self {Δ : List Term} {n} {f : ShapeFun n} {e : Entry (Shape n)}
    (hwf : ShapeFun.WF Δ (Shape.WF Δ) f) (he : e ∈ f) :
    Evaluates Δ f e.ty e.tm e.inp e.out :=
  have ⟨⟨_, hty⟩, htm, hin, _⟩ := hwf.1 e he
  .entry e he (LabelEq.refl hty htm) (Shape.LE.refl hin)

/-- Enlarging the graph by more entries preserves a lookup, on the nose.
Much weaker than `mono_graph`, which allows the entries themselves to be
replaced by dominating ones and so only returns a larger result; here the
derivation transfers unchanged. -/
theorem Evaluates.mono_sub {Δ : List Term} {n} {f f' : ShapeFun n} {A a : Term}
    {x c : Shape n} (hsub : ∀ e ∈ f, e ∈ f') (H : Evaluates Δ f A a x c) :
    Evaluates Δ f' A a x c := by
  induction H with
  | bot => exact .bot
  | entry e he hlab hin => exact .entry e (hsub e he) hlab hin
  | lower hle _ ih => exact .lower hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- "is a numeral".  The one condition that cannot be phrased as
`HasType · .nat` uniformly, because `Shape 0` has no `nat`; it is
independent of typing, so it gets its own recursion rather than an
inline match in `HasType`.  `HasType v .nat ↔ IsNumeral v` at positive
level (`Shape.hasType_nat_iff`). -/
inductive Shape.IsNumeral : ∀ {n}, Shape n → Prop
  | bot : IsNumeral .bot
  | zero : IsNumeral (n := n+1) .zero
  | succ : IsNumeral (n := n) w → IsNumeral (.succ w)

/-- A join of compatible numerals is a numeral. -/
theorem Shape.IsNumeral.join {Δ : List Term} : ∀ {n} {v w : Shape n},
    Shape.Compat Δ v w → Shape.IsNumeral v → Shape.IsNumeral w →
      Shape.IsNumeral (v.join w) := by
  intro n
  induction n with
  | zero => intro v w _ hv _; cases hv; simpa using ‹Shape.IsNumeral w›
  | succ n ih =>
    intro v w hc hv hw
    cases hv with
    | bot => simpa using hw
    | zero =>
      cases hw with
      | bot => simpa using Shape.IsNumeral.zero
      | zero => exact .zero
      | succ _ => exact absurd hc (fun x => x)
    | @succ _ v' hv' =>
      cases hw with
      | bot => simpa using Shape.IsNumeral.succ hv'
      | zero => exact absurd hc (fun x => x)
      | succ hw' => exact .succ (ih hc hv' hw')

/-! ## Codes and cumulativity

There is no separate `IsCode` predicate: a shape is a code exactly when it
is a type, `HasType Δ a .type`, because the two universes are **cumulative
in the model** — a proof-irrelevant former is also a proof-relevant type.
Cumulativity is built into the clauses that compare sorts with `≤`
(`unit`, `id`) and is the lemma below for the rest.

(The other repo does keep a separate `IsCode`, because it has no typing
relation on shapes at all and needs a downward-closed predicate for its
universe retraction.  With `HasType` available, master's route is the
right one: the lemma that replaces downward closure is `mono_r`, which
carries the hypothesis that the *larger* type is itself a type, and so
never needs `HasType · (sort r)` to be downward closed.) -/

theorem Bool.eq_true_of_le {r s : Bool} (h : r = true) (hrs : r ≤ s) : s = true := by
  subst h; revert hrs; cases s <;> decide

theorem Bool.le_true' (r : Bool) : r ≤ true := by cases r <;> decide

theorem Bool.le_tr {t r s : Bool} (h₁ : t ≤ r) (h₂ : r ≤ s) : t ≤ s := by
  revert h₁ h₂; cases t <;> cases r <;> cases s <;> decide

/-- The lookup is monotone in the query input: a larger input matches at
least as many entries. -/
theorem Evaluates.mono_input {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a : Term}
    {x x' c : Shape n} (hxx : Shape.LE Δ x x') (H : Evaluates Δ f A a x c) :
    Evaluates Δ f A a x' c := by
  induction H with
  | bot => exact .bot
  | entry e he hlab hin => exact .entry e he hlab (Shape.LE.trans hΔ hin hxx)
  | lower hle _ ih => exact .lower hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- And it only sees the query label up to definitional equality. -/
theorem Evaluates.label {Δ : List Term} {n} {f : ShapeFun n} {A a A' a' : Term}
    {x c : Shape n} (hlab : LabelEq Δ A a A' a') (H : Evaluates Δ f A a x c) :
    Evaluates Δ f A' a' x c := by
  induction H with
  | bot => exact .bot
  | entry e he hl hin => exact .entry e he (hl.trans hlab) hin
  | lower hle _ ih => exact .lower hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- Numerals are downward closed. -/
theorem Shape.IsNumeral.lower {Δ : List Term} {n} {v v' : Shape n}
    (hle : Shape.LE Δ v' v) (h : Shape.IsNumeral v) : Shape.IsNumeral v' := by
  induction h with
  | bot => cases Shape.le_bot_iff.1 hle; exact .bot
  | zero => match v' with | .bot => exact .bot | .zero => exact .zero
  | succ _ ih => match v' with | .bot => exact .bot | .succ w' => exact .succ (ih hle)

theorem Evaluates.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ)
    {n} {f : ShapeFun n} {A a : Term} {x c : Shape n} :
    Evaluates Δ f A a x c →
    Evaluates Θ (ShapeFun.subst (Shape.subst · τ) τ f) (A.subst τ) (a.subst τ)
      (x.subst τ) (c.subst τ) := by
  intro h
  induction h with
  | bot => simp only [Shape.subst_bot]; exact .bot
  | entry e he hlab hin =>
    exact .entry _ (ShapeFun.mem_subst.2 ⟨e, he, rfl⟩) (hlab.subst hΘ W) (hin.subst hΘ W)
  | lower hle _ ih => exact .lower (hle.subst hΘ W) ih
  | join hc _ _ ih₁ ih₂ => exact Shape.join_subst ▸ .join (hc.subst hΘ W) ih₁ ih₂

/-- Numerals are stable under substitution: there is nothing in them but
shape. -/
theorem Shape.IsNumeral.subst {τ : Subst} : ∀ {n} {v : Shape n},
    Shape.IsNumeral v → Shape.IsNumeral (v.subst τ) := by
  intro n v h
  induction h with
  | bot => rw [Shape.subst_bot]; exact .bot
  | zero => exact .zero
  | succ _ ih => exact .succ ih

/-! ## The lookup is coherent

What the relational lookup owes and master does not: master's lookup is a
saturated max-below *function*, single-valued, so there is nothing to
join and nothing to check. -/

/-- Everything a single lookup returns is pairwise compatible, given that
the graph is internally coherent and the query shape is.

Coherence asks for the two entries' *inputs* to be compatible, and that is
exactly what the query supplies: both inputs lie below the query shape, so
`of_common_upper` applies. -/
theorem Evaluates.compat {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a : Term}
    {x : Shape n} (hf : ShapeFun.Compat Shape.Compat Δ f f) (hx : Shape.Compat Δ x x)
    {y z : Shape n} (hy : Evaluates Δ f A a x y) (hz : Evaluates Δ f A a x z) :
    Shape.Compat Δ y z := by
  induction hy with
  | bot => exact .bot_left
  | lower hle _ ih => exact ih.symm hΔ |>.anti_right hΔ hle |>.symm hΔ
  | join _ _ _ ih₁ ih₂ => exact ih₁.join hΔ ih₂
  | entry e he hlab hin
  induction hz with
  | bot => exact .bot_right
  | entry e' he' hlab' hin' =>
    simpa using hf e he e' he' Δ .id hΔ (.id hΔ)
      (by simpa using hlab.trans hlab'.symm)
      (by simpa using hx.of_common_upper hΔ hin hin')
  | lower hle _ ih => exact ih.anti_right hΔ hle
  | join _ _ _ ih₁ ih₂ => exact ((ih₁.symm hΔ).join hΔ (ih₂.symm hΔ)).symm hΔ

/-- Everything the lookup returns is well formed, structurally: it is `⊥`,
an entry output, a join of those, or a lowering.  `WF` is not downward
closed, so the last case is not free — it holds because the order carries
the well-formedness of its lower bound (`Shape.LE.wf`). -/
theorem Evaluates.wf {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a : Term}
    {x : Shape n} (hf : ∀ e ∈ f, Shape.WF Δ e.out) :
    ∀ {y : Shape n}, Evaluates Δ f A a x y → Shape.WF Δ y := by
  intro y h
  induction h with
  | bot => cases n <;> trivial
  | entry e he _ _ => exact hf e he
  | lower hle _ _ => exact hle.wf
  | join hc _ _ ih₁ ih₂ => exact Shape.WF.join hΔ hc ih₁ ih₂

/-! ## `Evaluates`, without `Evaluates`

A lookup returns exactly the shapes dominated by the join of the outputs
of some sublist of matching entries whose inputs are dominated by the
query.  It replaces reasoning about derivations by reasoning about two
joins over one sublist, which is what the (now removed) cycle argument
ran on; `Evaluates.lift_of` still uses it.

`of_sublist` is the constructive half -- a sublist of matching entries can
be folded into one lookup, which is where graph coherence
(`Evaluates.compat`) is spent -- and `tighten` the destructive half. -/
open List in
/-- The outputs of a sublist of matching entries have a least upper bound,
and the lookup reaches it. -/
theorem Evaluates.of_sublist {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n}
    (hwf : ShapeFun.WF Δ (Shape.WF Δ) f) (hco : ShapeFun.Compat Shape.Compat Δ f f)
    {A a : Term} {x : Shape n} (hx : Shape.Compat Δ x x) :
    ∀ {s : List (Entry (Shape n))}, s <+ f → (∀ e ∈ s, LabelEq Δ e.ty e.tm A a) →
      (∀ e ∈ s, Shape.LE Δ e.inp x) →
      ∃ J, Shape.Joins Δ (s.map Entry.out) J ∧ Shape.WF Δ J ∧ Evaluates Δ f A a x J := by
  intro s
  induction s with
  | nil => exact fun _ _ _ => ⟨.bot, .nil, by cases n <;> trivial, .bot⟩
  | cons e s ih =>
    intro hsf hlab hin
    have ⟨J, hJ, hwJ, hevJ⟩ := ih ((List.sublist_cons_self e s).trans hsf)
      (fun e' he' => hlab e' (.tail _ he')) (fun e' he' => hin e' (.tail _ he'))
    have he : e ∈ f := hsf.subset (.head _)
    have heve : Evaluates Δ f A a x e.out := .entry e he (hlab e (.head _)) (hin e (.head _))
    have hwe := (hwf.1 e he).2.2.2
    have hc := Evaluates.compat hΔ hco hx heve hevJ
    exact ⟨e.out.join J, hJ.cons hΔ hwe hwJ hc, Shape.WF.join hΔ hc hwe hwJ, .join hc heve hevJ⟩

open List in
/-- Every lookup is dominated by the join of the outputs of the entries it
uses, whose inputs are in turn dominated by the query. -/
theorem Evaluates.tighten {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n}
    (hwf : ShapeFun.WF Δ (Shape.WF Δ) f) (hco : ShapeFun.Compat Shape.Compat Δ f f)
    {A a : Term} {x : Shape n} (hwx : Shape.WF Δ x) {y : Shape n}
    (H : Evaluates Δ f A a x y) :
    ∃ (s : List (Entry (Shape n))) (ji jo : Shape n), s <+ f ∧
      (∀ e ∈ s, LabelEq Δ e.ty e.tm A a) ∧
      Shape.Joins Δ (s.map Entry.inp) ji ∧ Shape.WF Δ ji ∧ Shape.LE Δ ji x ∧
      Shape.Joins Δ (s.map Entry.out) jo ∧ Shape.WF Δ jo ∧ Shape.LE Δ y jo := by
  induction H with
  | bot =>
    exact ⟨[], .bot, .bot, List.nil_sublist f, nofun, .nil, by cases n <;> trivial,
      Shape.LE.bot, .nil, by cases n <;> trivial, Shape.LE.bot⟩
  | entry e he hlab hin =>
    have hwi := (hwf.1 e he).2.2.1
    have hwo := (hwf.1 e he).2.2.2
    exact ⟨[e], e.inp, e.out, List.singleton_sublist.2 he,
      (fun e' he' => by cases List.mem_singleton.1 he'; exact hlab),
      Shape.Joins.singleton hΔ hwi, hwi, hin,
      Shape.Joins.singleton hΔ hwo, hwo, Shape.LE.refl hwo⟩
  | lower hle _ ih =>
    have ⟨s, ji, jo, hs, hlab, hji, hwji, hjix, hjo, hwjo, hyjo⟩ := ih
    exact ⟨s, ji, jo, hs, hlab, hji, hwji, hjix, hjo, hwjo, hle.trans hΔ hyjo⟩
  | join hc _ _ ih₁ ih₂ =>
    have ⟨s₁, ji₁, jo₁, hs₁, hlab₁, hji₁, hwji₁, hji₁x, hjo₁, _, hy₁⟩ := ih₁
    have ⟨s₂, ji₂, jo₂, hs₂, hlab₂, hji₂, hwji₂, hji₂x, hjo₂, _, hy₂⟩ := ih₂
    have ⟨s, hs, hss₁, hss₂, hunion⟩ := hs₁.union hs₂
    have hlab : ∀ e ∈ s, LabelEq Δ e.ty e.tm A a := fun e he =>
      match hunion e he with
      | .inl h' => hlab₁ e h'
      | .inr h' => hlab₂ e h'
    have hinx : ∀ e ∈ s, Shape.LE Δ e.inp x := fun e he =>
      match hunion e he with
      | .inl h' => (hji₁.le hwji₁ _ (List.mem_map.2 ⟨e, h', rfl⟩)).trans hΔ hji₁x
      | .inr h' => (hji₂.le hwji₂ _ (List.mem_map.2 ⟨e, h', rfl⟩)).trans hΔ hji₂x
    have ⟨ji, hji, hwji, hjix⟩ :=
      Shape.exists_joins hΔ hwx
        (fun v hv => have ⟨e, he, hv⟩ := List.mem_map.1 hv
          hv ▸ (hwf.1 e (hs.subset he)).2.2.1)
        (fun v hv => have ⟨e, he, hv⟩ := List.mem_map.1 hv; hv ▸ hinx e he)
    have ⟨J, hJ, hwJ, _⟩ := Evaluates.of_sublist hΔ hwf hco hwx.coherent hs hlab hinx
    have hout : ∀ {t : List (Entry (Shape n))}, t <+ s → ∀ v ∈ t.map Entry.out,
        Shape.LE Δ v J := fun ht v hv =>
      have ⟨e, he, hv⟩ := List.mem_map.1 hv
      hv ▸ hJ.le hwJ _ (List.mem_map.2 ⟨e, ht.subset he, rfl⟩)
    exact ⟨s, ji, J, hs, hlab, hji, hwji, hjix, hJ, hwJ,
      Shape.join_le (hy₁.trans hΔ (hjo₁.min hwJ (hout hss₁)))
        (hy₂.trans hΔ (hjo₂.min hwJ (hout hss₂)))⟩

open List in
/-- The characterisation, as the equivalence it is. -/
theorem Evaluates.joins_iff {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n}
    (hwf : ShapeFun.WF Δ (Shape.WF Δ) f) (hco : ShapeFun.Compat Shape.Compat Δ f f)
    {A a : Term} {x y : Shape n} (hwx : Shape.WF Δ x) :
    Evaluates Δ f A a x y ↔
      ∃ (s : List (Entry (Shape n))) (ji jo : Shape n), s <+ f ∧
        (∀ e ∈ s, LabelEq Δ e.ty e.tm A a) ∧
        Shape.Joins Δ (s.map Entry.inp) ji ∧ Shape.WF Δ ji ∧ Shape.LE Δ ji x ∧
        Shape.Joins Δ (s.map Entry.out) jo ∧ Shape.WF Δ jo ∧ Shape.LE Δ y jo := by
  refine ⟨Evaluates.tighten hΔ hwf hco hwx, ?_⟩
  rintro ⟨s, ji, jo, hs, hlab, hji, hwji, hjix, hjo, hwjo, hyjo⟩
  have ⟨J, hJ, hwJ, hev⟩ :=
    Evaluates.of_sublist hΔ hwf hco hwx.coherent hs hlab fun e he =>
      (hji.le hwji _ (List.mem_map.2 ⟨e, he, rfl⟩)).trans hΔ hjix
  exact .lower (hyjo.trans hΔ (hjo.min hwJ (hJ.le hwJ))) hev

/-! ## Lifting

`Interp` quantifies over `TShape`, so every notion it mentions has to be
transportable along `Shape.lift`.  For the order, well-formedness,
compatibility and the join that transport is an equivalence
(`Shape.lift_le_lift` and friends).

For the *lookup* it is one-directional: `Evaluates.lower` can produce a
witness at the higher level that is not the lift of anything, since the
order on graphs is contravariant in the input, so a shape below a lifted
shape need not itself be a lift.  Master has the equivalence only because
its lookup is a function.  This is why `TEvaluates` compares `TShape`s
instead: there is then nothing to reflect, and `TShape.HasType` inherits
that — `lift_subject` *and* `lower_subject` are both theorems. -/

theorem Evaluates.lift {Δ : List Term} {n k} (h : n ≤ k) {f : ShapeFun n} {A a : Term}
    {x c : Shape n} (H : Evaluates Δ f A a x c) :
    Evaluates Δ (ShapeFun.lift (Shape.lift k) f) A a (x.lift k) (c.lift k) := by
  induction H with
  | bot => rw [Shape.lift_bot]; exact .bot
  | entry e he hlab hin =>
    exact .entry ⟨e.ty, e.tm, e.inp.lift k, e.out.lift k⟩ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)
      hlab (Shape.lift_le h hin)
  | lower hle _ ih => exact .lower (Shape.lift_le h hle) ih
  | join hc _ _ ih₁ ih₂ =>
    rw [← Shape.lift_join h]
    exact .join ((Shape.lift_compat h).2 hc) ih₁ ih₂

/-! ### The layers are full substructures

Each level consists of the same shapes as the one below, related the same
way, plus new ones.  So a relation established at one layer is preserved
*and reflected* by the embedding into a higher one.  For the lookup that
is `Evaluates.lift_iff` below.

The `lower` rule is what makes this need an argument.  A well-formed shape
below a lift need **not** be a lift — the order on graphs is contravariant
in the input, so a smaller λ-shape can have inputs with genuine
higher-level structure — so a lookup over a lifted graph really can
produce shapes outside the image.  But by `Evaluates.tighten` such a
lookup is dominated by a join over a sublist of the lifted graph, a
sublist of a lifted graph is a lifted sublist, and `Joins.lift` says the
join of the lifts is the lift of the join.  So the dominating shape is
always in the image, and that is the whole content. -/

/-- Everything a lifted graph's lookup returns is below the lift of
something the original lookup returns, namely the join of the outputs of
the sublist it uses, taken one level down. -/
theorem Evaluates.lift_of {Δ : List Term} (hΔ : ⊢ Δ) {n k} (h : n ≤ k) {f : ShapeFun n}
    {A a : Term} {x : Shape n}
    (hwf : ShapeFun.WF Δ (Shape.WF Δ) f) (hco : ShapeFun.Compat Shape.Compat Δ f f)
    (hwx : Shape.WF Δ x) :
    ∀ {c' : Shape k}, Evaluates Δ (ShapeFun.lift (Shape.lift k) f) A a (x.lift k) c' →
      ∃ c, Shape.LE Δ c' (c.lift k) ∧ Evaluates Δ f A a x c := by
  intro c' H
  have ⟨s, ji, jo, hs, hlab, hji, hwji, hjix, hjo, hwjo, hcjo⟩ :=
    Evaluates.tighten hΔ ((ShapeFun.lift_wf h).2 hwf) ((ShapeFun.lift_compat h).2 hco)
      ((Shape.lift_wf h).2 hwx) H
  simp only [ShapeFun.lift] at hs
  obtain ⟨s₀, hs₀, rfl⟩ := List.sublist_map hs
  rw [ShapeFun.map_lift_inp] at hji
  rw [ShapeFun.map_lift_out] at hjo
  have hinx : ∀ e ∈ s₀, Shape.LE Δ e.inp x := fun e he =>
    (Shape.lift_le_lift hΔ h).1
      ((hji.le hwji _ (List.mem_map.2 ⟨e.inp, List.mem_map.2 ⟨e, he, rfl⟩, rfl⟩)).trans hΔ hjix)
  have ⟨J, hJ, hwJ, hevJ⟩ :=
    Evaluates.of_sublist hΔ hwf hco hwx.coherent hs₀
      (fun e he => hlab _ (List.mem_map.2 ⟨e, he, rfl⟩)) hinx
  have ⟨hle, _⟩ :=
    Shape.Joins.uniq hwjo ((Shape.lift_wf h).2 hwJ) hjo
      (Shape.Joins.lift hΔ h (fun v hv => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hv
        exact (hwf.1 e (hs₀.subset he)).2.2.2) hwJ hJ)
  exact ⟨J, hcjo.trans hΔ hle, hevJ⟩

/-- **Fullness for the lookup.**  On the shapes that come from the level
below, the lifted graph relates exactly what the original one did. -/
theorem Evaluates.lift_iff {Δ : List Term} (hΔ : ⊢ Δ) {n k} (h : n ≤ k) {f : ShapeFun n}
    {A a : Term} {x c : Shape n}
    (hwf : ShapeFun.WF Δ (Shape.WF Δ) f) (hco : ShapeFun.Compat Shape.Compat Δ f f)
    (hwx : Shape.WF Δ x) :
    Evaluates Δ (ShapeFun.lift (Shape.lift k) f) A a (x.lift k) (c.lift k) ↔
      Evaluates Δ f A a x c := by
  refine ⟨fun H => ?_, Evaluates.lift h⟩
  have ⟨c₀, hle, hc₀⟩ := Evaluates.lift_of hΔ h hwf hco hwx H
  exact .lower ((Shape.lift_le_lift hΔ h).1 hle) hc₀

theorem ShapeFun.LE.lift {Δ : List Term} {n k} (h : n ≤ k) {f g : ShapeFun n}
    (H : ShapeFun.LE Δ (Shape.LE Δ) (Shape.WF Δ) f g) :
    ShapeFun.LE Δ (Shape.LE Δ) (Shape.WF Δ) (ShapeFun.lift (Shape.lift k) f)
      (ShapeFun.lift (Shape.lift k) g) := by
  refine ⟨fun e' he' => ?_, (ShapeFun.lift_wf h).2 H.2.1, (ShapeFun.lift_wf h).2 H.2.2⟩
  obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he'
  exact ShapeFun.Eval.lift h (Shape.lift_le h) (H.1 e he)

/-- Numerals lift and reflect. -/
theorem Shape.IsNumeral.lift_iff {n k} (h : n ≤ k) {v : Shape n} :
    Shape.IsNumeral (v.lift k) ↔ Shape.IsNumeral v := by
  constructor <;> intro H
  · induction n generalizing k with
    | zero =>
      cases v with | bot => exact .bot | sort r
      let 0 := k; rw [Shape.lift_self] at H; cases H
    | succ n ih
    let k + 1 := k
    match v with
    | .bot => exact .bot
    | .zero => exact .zero
    | .succ w => let .succ hw := H; exact .succ (ih (Nat.le_of_succ_le_succ h) hw)
  · induction H generalizing k with
    | bot => rw [Shape.lift_bot]; exact .bot
    | zero => let k+1 := k; exact .zero
    | succ _ ih => let k+1 := k; exact .succ (ih (Nat.le_of_succ_le_succ h))

/-! ## What the level-indexed typing cost, and why it is gone

A first version of this file defined typing by *recursion on the level*,
mirroring `ShapeOld.lean`.  It is deleted; this note says what it was and
why, since the shape of the difficulty recurs.

Every fact about a level-indexed relation has to be transported along
`lift`, and the reflection direction of that transport is expensive:
`Shape.HasType.lift_iff` ran 160 lines.  Worse, it dictated the clauses.
To reflect, the `lam` clause had to be stated *per entry*; stated per
entry it is not closed under the order, whose lookup has joins; so
`mono_l` at `lam` was **false**, not merely unproved (§5.5 of
`presheaf-proof-strategy.md` has the Σ counterexample).  Stating it with a
*dominating* codomain instead restores closure and destroys reflection.
That is the dilemma the inductive over `TShape` dissolves.

Two further casualties of dropping saturation went at the same time, and
neither is missed.  Join-closure of typing at an arbitrary type
(`join_at`) has no counterpart in the other repo: its directedness lemmas
(`pi_isDirected`, `abstraction_isDirected`, `succ_isDirected`) are about
*values*, which are ideals there and directed by construction, never about
the extension of a type.  Master needs it only because its interpretation
is a relation, so soundness's `tr` case has two interpretations to
combine; `Interp` makes compatibility of any two elements automatic.  And
`HasDom` reflection along `lift` fails for the same reason the `lam`
clause did: a dominating graph at the level above need not be a lift.

The cycle argument that was built for those went with them.  What stays,
because it is independent: `find_cycle`,
`List.Sublist.union`/`allSublists`/`sublist_map`, `Shape.Joins`, and
`Evaluates.tighten`/`of_sublist`/`joins_iff`, from which
`Evaluates.lift_of` is proved. -/

/-! ## Typing over `TShape`, as one inductive

Defined directly on `TShape` there is nothing to reflect, and every clause
**pins the shape of its subject and its type** while leaving the
*contents* free.  `.succ v'` below `.succ v` is the `succ` clause again at
`v'`; a λ below `.lam g` is the `lam` clause again at its own graph, with
`g₀` kept as the generator the codomain witnesses live over (the other
repo's pattern — *the conditions constrain a generator above the shape
being classified*, `ΩLower`, `piGenerator`; §5.5); a pair below
`.pair ty tm x y` is the `pair` clause again at its own first component
`x'`, with `x` kept as the dominator the code is read at.  Everything
strictly below a shape and not of its head is `⊥`, and the `bot` clause
takes that.  `mono_l` and `mono_r` are then both theorems.

`forallE` and `sigma` are stated *directly* on `d` and `f`, with no
generator: `mono_l` pushes the premises into a smaller Π through
`Eval.tHasType`, whose `join` case is `join_sort` and whose `lower` case
is `mono_l_sort` — available because a Π is typed at a sort, where no
existential level can appear.

`id`, `refl`, `pair`, `lam`, `forallE` and `sigma` pay for pinning with a
`Shape.WF` premise, since their subject's well-formedness is not otherwise
free; `succ` does not, because `IsNumeral` implies it.

The codomain witness of `lam` is a **list of pairs** `g₀`, not an `∃`
inside the premise: `∃ c, … ∧ HasType …` would put the inductive under
`Exists`, and the kernel refuses a nested inductive whose parameters
mention locals (here `Shape n'` mentions `n'`).  A *function*
`Entry (Shape n₀) → TShape` typechecks but does not substitute — see
`HasType.subst`.  For the same reason the constructors spell the Π
condition out rather than abbreviating it: the kernel will not take the
inductive being declared as an argument to a definition. -/

/-- The order carries the well-formedness of its lower bound at the total
level too, which is `Shape.LE.wf` through the canonical level. -/
theorem TShape.LE.wf {Δ : List Term} {a b : TShape} (h : TShape.LE Δ a b) :
    TShape.WF Δ a :=
  (Shape.lift_wf (Nat.le_max_left ..)).1 (Shape.LE.wf h)

/-- `⊥` is well formed at every level. -/
theorem Shape.WF.bot {Δ : List Term} {n} :
    Shape.WF Δ (Shape.bot : Shape n) := by cases n <;> trivial

/-- A numeral is well formed: its only labels are none. -/
theorem Shape.IsNumeral.wf {Δ : List Term} {n} {v : Shape n} (h : Shape.IsNumeral v) :
    Shape.WF Δ v := by
  induction h with
  | bot => exact Shape.WF.bot
  | zero => trivial
  | succ _ ih => exact ih

/-- A sort is well formed at every level. -/
theorem Shape.WF.sort {Δ : List Term} {n} {r : Bool} :
    Shape.WF Δ (Shape.sort r : Shape n) := by cases n <;> trivial

/-- Only a sort is above a sort. -/
theorem Shape.sort_le {Δ : List Term} : ∀ {n} {s : Shape n} {r : Bool},
    Shape.LE Δ (Shape.sort r) s → s = Shape.sort r := by
  intro n s r h
  cases n with
  | zero => cases s with | bot => exact absurd h id | sort r' => cases h; rfl
  | succ n =>
    cases s with
    | sort r' => cases h; rfl
    | _ => exact absurd h id

/-- A sort is rigid: anything above it is it, at whatever level.  Proved by
reflecting the comparison back down with `Shape.lift_le_lift`. -/
theorem TShape.LE.sort_eq {Δ : List Term} (hΔ : ⊢ Δ) {n} {j : Bool} {a : TShape}
    (h : TShape.LE Δ (Shape.T (n := n) (Shape.sort j)) a) : a.2 = Shape.sort j := by
  have h2 : Shape.LE Δ ((Shape.sort j : Shape n).lift (max n a.1))
      (a.2.lift (max n a.1)) := h
  rw [Shape.lift_sort, show (Shape.sort j : Shape (max n a.1))
      = (Shape.sort j : Shape a.1).lift (max n a.1) from Shape.lift_sort.symm] at h2
  exact Shape.sort_le ((Shape.lift_le_lift hΔ (Nat.le_max_right ..)).1 h2)

/-- And so is `nat`. -/
theorem TShape.LE.nat_eq {Δ : List Term} {n} {a : TShape}
    (h : TShape.LE Δ (Shape.T (n := n+1) ShapeS.nat) a) :
    ∃ k, a = Shape.T (n := k+1) ShapeS.nat := by
  obtain ⟨j, s⟩ := a
  cases j with
  | zero =>
    obtain ⟨M, hM⟩ : ∃ M, max (n+1) 0 = M+1 := by
      cases hmax : max (n+1) 0 with
      | zero => exact absurd (hmax ▸ Nat.le_max_left (n+1) 0) (by omega)
      | succ M => exact ⟨M, rfl⟩
    have h2 : Shape.LE Δ (Shape.lift (max (n+1) 0) (Shape.T (n := n+1) ShapeS.nat).2)
        (Shape.lift (max (n+1) 0) s) := h
    rw [hM] at h2
    cases s <;> exact absurd h2 (fun x => x)
  | succ j =>
    refine ⟨j, ?_⟩
    obtain ⟨M, hM⟩ : ∃ M, max (n+1) (j+1) = M+1 := by
      cases hmax : max (n+1) (j+1) with
      | zero => exact absurd (hmax ▸ Nat.le_max_left (n+1) (j+1)) (by omega)
      | succ M => exact ⟨M, rfl⟩
    have h2 : Shape.LE Δ (Shape.lift (max (n+1) (j+1)) (Shape.T (n := n+1) ShapeS.nat).2)
        (Shape.lift (max (n+1) (j+1)) s) := h
    rw [hM] at h2
    cases s <;> first | rfl | exact absurd h2 (fun x => x)

/-- Inversion for a bound against a shape at a positive level, with the
level arithmetic done once: the comparison can be read at a successor
level, where `Shape.LE` computes. -/
theorem TShape.LE.at_succ {Δ : List Term} {n} {t : Shape (n+1)} {j} {s : Shape j}
    (h : TShape.LE Δ (Shape.T s) (Shape.T t)) :
    ∃ M, n ≤ M ∧ j ≤ M + 1 ∧ Shape.LE Δ (s.lift (M+1)) (t.lift (M+1)) := by
  obtain ⟨M, hM⟩ : ∃ M, max j (n+1) = M+1 := by
    cases hmax : max j (n+1) with
    | zero => exact absurd (hmax ▸ Nat.le_max_right j (n+1)) (by omega)
    | succ M => exact ⟨M, rfl⟩
  have hn : n + 1 ≤ M + 1 := hM ▸ Nat.le_max_right j (n+1)
  have hj : j ≤ M + 1 := hM ▸ Nat.le_max_left j (n+1)
  refine ⟨M, Nat.le_of_succ_le_succ hn, hj, ?_⟩
  have h2 : Shape.LE Δ (Shape.lift (max j (n+1)) s) (Shape.lift (max j (n+1)) t) := h
  rwa [hM] at h2

/-- The same, when it is the *smaller* shape that sits at a positive level.
Needed for `sort`, whose generator may sit at level `0`. -/
theorem TShape.LE.src_succ {Δ : List Term} {n} {t : Shape n} {j} {s : Shape (j+1)}
    (h : TShape.LE Δ (Shape.T s) (Shape.T t)) :
    ∃ M, j ≤ M ∧ n ≤ M + 1 ∧ Shape.LE Δ (s.lift (M+1)) (t.lift (M+1)) := by
  obtain ⟨M, hM⟩ : ∃ M, max (j+1) n = M+1 := by
    cases hmax : max (j+1) n with
    | zero => exact absurd (hmax ▸ Nat.le_max_left (j+1) n) (by omega)
    | succ M => exact ⟨M, rfl⟩
  have hj : j + 1 ≤ M + 1 := hM ▸ Nat.le_max_left (j+1) n
  have hn : n ≤ M + 1 := hM ▸ Nat.le_max_right (j+1) n
  refine ⟨M, Nat.le_of_succ_le_succ hj, hn, ?_⟩
  have h2 : Shape.LE Δ (Shape.lift (max (j+1) n) s) (Shape.lift (max (j+1) n) t) := h
  rwa [hM] at h2

/-- The lookup over `TShape`: the four rules of `ShapeFun.Eval`, comparing
with the level-independent `TShape.LE`, so it needs no `lift` lemma. -/
inductive TEvaluates (Δ : List Term) {n} (f : ShapeFun n) (A a : Term) (x : TShape) :
    TShape → Prop where
  | bot : TEvaluates Δ f A a x TShape.bot
  | entry (e : Entry (Shape n)) : e ∈ f → LabelEq Δ e.ty e.tm A a →
    TShape.LE Δ e.inp.T x → TEvaluates Δ f A a x e.out.T
  | lower {y z} : TShape.LE Δ y z → TEvaluates Δ f A a x z → TEvaluates Δ f A a x y
  | join {y z} : TShape.Compat Δ y z → TEvaluates Δ f A a x y → TEvaluates Δ f A a x z →
    TEvaluates Δ f A a x (y.join z)

/-- Everything the lookup returns is well formed, given that the graph's
outputs are.  `bot` and `join` are the join semilattice, `entry` is the
hypothesis, and `lower` is free: the order carries the well-formedness of
its lower bound.  This is why `lam` and `pair` need no `WF` premise on
their codomain witnesses. -/
theorem TEvaluates.wf {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a : Term}
    {x : TShape} (hf : ∀ e ∈ f, TShape.WF Δ e.out.T) :
    ∀ {c : TShape}, TEvaluates Δ f A a x c → TShape.WF Δ c := by
  intro c h
  induction h with
  | bot => exact TShape.WF.bot
  | entry e he _ _ => exact hf e he
  | lower hle _ _ => exact hle.wf
  | join hc _ _ ih₁ ih₂ => exact TShape.WF.join hΔ hc ih₁ ih₂

/-- The lookup grows when the input grows.  Only `entry` has content. -/
theorem TEvaluates.mono_inp {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a : Term}
    {x x' : TShape} (hx : TShape.LE Δ x x') :
    ∀ {c : TShape}, TEvaluates Δ f A a x c → TEvaluates Δ f A a x' c := by
  intro c h
  induction h with
  | bot => exact .bot
  | entry e he hl hin => exact .entry e he hl (hin.trans hΔ hx)
  | lower hle _ ih => exact .lower hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- The lookup grows when the label moves along a definitional equality and
the input grows. -/
theorem TEvaluates.mono {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a A' a' : Term}
    {x x' : TShape} (hlab : LabelEq Δ A a A' a') (hx : TShape.LE Δ x x') :
    ∀ {c : TShape}, TEvaluates Δ f A a x c → TEvaluates Δ f A' a' x' c := by
  intro c h
  induction h with
  | bot => exact .bot
  | entry e he hl hin => exact .entry e he (hl.trans hlab) (hin.trans hΔ hx)
  | lower hle _ ih => exact .lower hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- **The query's type moves freely along a definitional equality.**

Only the type: the label equation that `entry` carries is stated at the
*entry's* type, not at the query's, so retyping the query touches nothing
but the `TyEq` conjunct.  This is what lets two `app` derivations at the
same argument but different domain labels be read at one query, without
the argument having to be typed — which at a non-admissible valuation it
is not. -/
theorem TEvaluates.retype {Δ : List Term} {n} {f : ShapeFun n} {A A' a : Term}
    {x : TShape} (hA : TyEq Δ A A') :
    ∀ {c : TShape}, TEvaluates Δ f A a x c → TEvaluates Δ f A' a x c := by
  intro c h
  induction h with
  | bot => exact .bot
  | entry e he hl hin => exact .entry e he ⟨TyEq.trans hl.1 hA, hl.2⟩ hin
  | lower hle _ ih => exact .lower hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- Two lookups at one query in one coherent graph are compatible, so
their join exists.  `Evaluates.compat` at the total level, with the same
double induction. -/
theorem TEvaluates.compat {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a : Term}
    {x : TShape} (hf : ShapeFun.Compat Shape.Compat Δ f f) (hwx : TShape.WF Δ x)
    {y z : TShape} (hy : TEvaluates Δ f A a x y) (hz : TEvaluates Δ f A a x z) :
    TShape.Compat Δ y z := by
  induction hy with
  | bot => exact TShape.Compat.bot_left
  | lower hle _ ih => exact (ih.symm hΔ).anti_right hΔ hle |>.symm hΔ
  | join _ _ _ ih₁ ih₂ => exact ih₁.join hΔ ih₂
  | entry e he hlab hin
  induction hz with
  | bot => exact TShape.Compat.bot_right
  | entry e' he' hlab' hin' =>
    refine (TShape.Compat.T (n := n)).2 ?_
    simpa using hf e he e' he' Δ .id hΔ (.id hΔ)
      (by simpa using hlab.trans hlab'.symm)
      (by
        have := TShape.Compat.of_common_upper hΔ hwx hin hin'
        simpa using (TShape.Compat.T (n := n)).1 this)
  | lower hle _ ih => exact ih.anti_right hΔ hle
  | join _ _ _ ih₁ ih₂ => exact ((ih₁.symm hΔ).join hΔ (ih₂.symm hΔ)).symm hΔ

/-- A lookup in a covered graph is a lookup in the covering one. -/
theorem TEvaluates.trans {Δ : List Term} (hΔ : ⊢ Δ) {n n'} {f : ShapeFun n} {f' : ShapeFun n'}
    {A a : Term} {x : TShape}
    (hf : ∀ e ∈ f, TEvaluates Δ f' e.ty e.tm e.inp.T e.out.T) :
    ∀ {c : TShape}, TEvaluates Δ f A a x c → TEvaluates Δ f' A a x c := by
  intro c h
  induction h with
  | bot => exact .bot
  | entry e he hl hin => exact TEvaluates.mono hΔ hl hin (hf e he)
  | lower hle _ ih => exact .lower hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- A lookup survives lifting the graph: the lifted entry has the same
label, an input equivalent to the old one and an output equivalent to the
old one, so `mono_inp` and `lower` carry it across. -/
theorem TEvaluates.lift_graph {Δ : List Term} (hΔ : ⊢ Δ) {n m} (hm : n ≤ m)
    {f : ShapeFun n} (hw : ShapeFun.WFE Δ (Shape.WF Δ) f) {A a : Term} {x : TShape} :
    ∀ {c : TShape}, TEvaluates Δ f A a x c →
      TEvaluates Δ (ShapeFun.lift (Shape.lift m) f) A a x c := by
  intro c h
  induction h with
  | bot => exact .bot
  | entry e he hl hin =>
    have hwe := hw e he
    refine .lower (TShape.LE.le_lift hΔ (m := e.out.T) hm hwe.2) ?_
    exact .entry ⟨e.ty, e.tm, e.inp.lift m, e.out.lift m⟩
      (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩) hl
      ((TShape.LE.lift_le hΔ (m := e.inp.T) hm hwe.1).trans hΔ hin)
  | lower hle _ ih => exact .lower hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- A lookup survives adding entries to the graph: only `entry` has
content, and there it is membership. -/
theorem TEvaluates.mono_graph {Δ : List Term} {n} {f f' : ShapeFun n} {A a : Term}
    {x : TShape} (hf : ∀ e ∈ f, e ∈ f') :
    ∀ {c : TShape}, TEvaluates Δ f A a x c → TEvaluates Δ f' A a x c := by
  intro c h
  induction h with
  | bot => exact .bot
  | entry e he hl hin => exact .entry e (hf e he) hl hin
  | lower hle _ ih => exact .lower hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- The level-indexed lookup is the `TShape` one, at a fixed level.  Only
`bot` and `join` need anything: `TEvaluates.bot` lands at `⟨0, ⊥⟩` where the
goal is at `⟨n, ⊥⟩`, and `TShape.join` sits at `max n n`. -/
theorem ShapeFun.Eval.toT {Δ : List Term} {n} {f : ShapeFun n} {A a : Term}
    {x : Shape n} : ∀ {y : Shape n}, ShapeFun.Eval Δ (Shape.LE Δ) f A a x y →
      TEvaluates Δ f A a x.T y.T := by
  intro y h
  induction h with
  | bot => exact .lower (TShape.bot_le' rfl) .bot
  | entry e he hl hin => exact .entry e he hl (TShape.LE.T.2 hin)
  | lower hle _ ih => exact .lower (TShape.LE.T.2 hle) ih
  | join hc hy hz ih₁ ih₂ =>
    -- `TEvaluates.join` lands at `TShape.join y.T z.T`, whose level is
    -- `max n n`, where the goal's is `n`; `TShape.join_T` is that dependent
    -- rewrite along `Nat.max_self`
    exact TShape.join_T ▸ TEvaluates.join (TShape.Compat.T.2 hc) ih₁ ih₂

/-- A graph covers itself: each entry is its own lookup.  The label and
input reflexivities are exactly what `ShapeFun.WF` supplies. -/
theorem TEvaluates.refl {Δ : List Term} {n} {f : ShapeFun n}
    (hw : ShapeFun.WF Δ (Shape.WF Δ) f) :
    ∀ e ∈ f, TEvaluates Δ f e.ty e.tm e.inp.T e.out.T := by
  intro e he
  obtain ⟨⟨u, hty⟩, htm, hin, _⟩ := hw.1 e he
  exact .entry e he (LabelEq.refl hty htm) (TShape.LE.T.2 (Shape.LE.refl hin))

/-- Entrywise coverage survives lifting the covered graph: `lift` moves
neither an input nor an output, as a `TShape`.  Used where a clause's graph
is compared at a level above both. -/
theorem TEvaluates.lift_cover {Δ : List Term} (hΔ : ⊢ Δ) {n n'} {g : ShapeFun n}
    {f' : ShapeFun n'} {k} (hk : n ≤ k) (hw : ShapeFun.WF Δ (Shape.WF Δ) g)
    (hg : ∀ e ∈ g, TEvaluates Δ f' e.ty e.tm e.inp.T e.out.T) :
    ∀ e ∈ ShapeFun.lift (Shape.lift k) g,
      TEvaluates Δ f' e.ty e.tm e.inp.T e.out.T := by
  intro e he
  obtain ⟨e₀, he₀, rfl⟩ := ShapeFun.mem_lift.1 he
  have hwe := hw.1 e₀ he₀
  exact .lower (TShape.LE.lift_le hΔ (m := e₀.out.T) hk hwe.2.2.2)
    (TEvaluates.mono_inp hΔ (TShape.LE.le_lift hΔ (m := e₀.inp.T) hk hwe.2.2.1)
      (hg e₀ he₀))

/-- And back: coverage of the lift is coverage of the graph. -/
theorem TEvaluates.lower_cover {Δ : List Term} (hΔ : ⊢ Δ) {n n'} {g : ShapeFun n}
    {f' : ShapeFun n'} {k} (hk : n ≤ k) (hw : ShapeFun.WF Δ (Shape.WF Δ) g)
    (hg : ∀ e ∈ ShapeFun.lift (Shape.lift k) g,
      TEvaluates Δ f' e.ty e.tm e.inp.T e.out.T) :
    ∀ e ∈ g, TEvaluates Δ f' e.ty e.tm e.inp.T e.out.T := by
  intro e he
  have hwe := hw.1 e he
  exact .lower (TShape.LE.le_lift hΔ (m := e.out.T) hk hwe.2.2.2)
    (TEvaluates.mono_inp hΔ (TShape.LE.lift_le hΔ (m := e.inp.T) hk hwe.2.2.1)
      (hg _ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)))

/-- The converse transport: a graph `g'` whose *lift* is covered by `g`,
which is itself covered by `f'`, is covered by `f'` at its own level.  This
is what a `Shape.LE` between two λ-shapes, read at a level above both,
hands back to the `lam` clause. -/
theorem TEvaluates.of_cover_lift {Δ : List Term} (hΔ : ⊢ Δ) {j k n'} (hjk : j ≤ k)
    {g' : ShapeFun j} {g : ShapeFun k} {f' : ShapeFun n'}
    (hw : ShapeFun.WF Δ (Shape.WF Δ) g')
    (hcov : ∀ e ∈ ShapeFun.lift (Shape.lift k) g',
      ShapeFun.Eval Δ (Shape.LE Δ) g e.ty e.tm e.inp e.out)
    (hg : ∀ e ∈ g, TEvaluates Δ f' e.ty e.tm e.inp.T e.out.T) :
    ∀ e ∈ g', TEvaluates Δ f' e.ty e.tm e.inp.T e.out.T := by
  intro e he
  have hwe := hw.1 e he
  have h2 := TEvaluates.trans hΔ hg
    (ShapeFun.Eval.toT (hcov _ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)))
  exact .lower (TShape.LE.le_lift hΔ (m := e.out.T) hjk hwe.2.2.2)
    (TEvaluates.mono_inp hΔ (TShape.LE.lift_le hΔ (m := e.inp.T) hjk hwe.2.2.1) h2)

/-! ### The `_decomp` family

Master's component inversions for the order, in the form these clauses
consume them: the sub-shape relations come back as `TShape.LE` **at their
own canonical levels** rather than at `max n n'`, and a graph relation
comes back as *coverage over `TShape`* — each entry of the smaller graph
is a lookup in whatever the bigger one's entries are lookups in.  The
level arithmetic is `TShape.LE.at_succ` once, here, instead of at every
use site. -/

/-- The domain half of `forallE_decomp`, which needs no well-formedness:
the Π order is covariant in the domain. -/
theorem TShape.LE.forallE_dom {Δ : List Term} (hΔ : ⊢ Δ) {n n'}
    {A B A' B' : Term} {d : Shape n} {f : ShapeFun n} {d' : Shape n'} {f' : ShapeFun n'}
    (h : TShape.LE Δ (Shape.T (n := n+1) (.forallE A B d f))
      (Shape.T (n := n'+1) (.forallE A' B' d' f'))) :
    TShape.LE Δ d.T d'.T := by
  obtain ⟨M, hn'M, hnM, h2⟩ := TShape.LE.at_succ h
  exact (TShape.LE.def hΔ (Nat.le_of_succ_le_succ hnM) hn'M).2 h2.2.1

/-- The Σ twin. -/
theorem TShape.LE.sigma_dom {Δ : List Term} (hΔ : ⊢ Δ) {n n'}
    {A B A' B' : Term} {d : Shape n} {f : ShapeFun n} {d' : Shape n'} {f' : ShapeFun n'}
    (h : TShape.LE Δ (Shape.T (n := n+1) (.sigma A B d f))
      (Shape.T (n := n'+1) (.sigma A' B' d' f'))) :
    TShape.LE Δ d.T d'.T := by
  obtain ⟨M, hn'M, hnM, h2⟩ := TShape.LE.at_succ h
  exact (TShape.LE.def hΔ (Nat.le_of_succ_le_succ hnM) hn'M).2 h2.2.1

/-- Π-decomposition.  The codomain half composes the coverage the order
gives with a coverage of the bigger graph, which is what both `mono_l` and
`mono_r` have to hand. -/
theorem TShape.LE.forallE_decomp {Δ : List Term} (hΔ : ⊢ Δ) {n n' k}
    {A B A' B' : Term} {d : Shape n} {f : ShapeFun n} {d' : Shape n'}
    {f' : ShapeFun n'} {f'' : ShapeFun k}
    (h : TShape.LE Δ (Shape.T (n := n+1) (.forallE A B d f))
      (Shape.T (n := n'+1) (.forallE A' B' d' f')))
    (hw : Shape.WF (n := n+1) Δ (.forallE A B d f))
    (hw' : Shape.WF (n := n'+1) Δ (.forallE A' B' d' f'))
    (hf' : ∀ e ∈ f', TEvaluates Δ f'' e.ty e.tm e.inp.T e.out.T) :
    PiLabelEq Δ A B A' B' ∧ TShape.LE Δ d.T d'.T ∧
      ∀ e ∈ f, TEvaluates Δ f'' e.ty e.tm e.inp.T e.out.T := by
  obtain ⟨M, hn'M, hnM, h2⟩ := TShape.LE.at_succ h
  have hn : n ≤ M := Nat.le_of_succ_le_succ hnM
  exact ⟨h2.1, (TShape.LE.def hΔ hn hn'M).2 h2.2.1,
    TEvaluates.of_cover_lift hΔ hn hw.2.2.2 h2.2.2.1
      (TEvaluates.lift_cover hΔ hn'M hw'.2.2.2 hf')⟩

/-- Σ-decomposition; the clause is the same as Π's. -/
theorem TShape.LE.sigma_decomp {Δ : List Term} (hΔ : ⊢ Δ) {n n' k}
    {A B A' B' : Term} {d : Shape n} {f : ShapeFun n} {d' : Shape n'}
    {f' : ShapeFun n'} {f'' : ShapeFun k}
    (h : TShape.LE Δ (Shape.T (n := n+1) (.sigma A B d f))
      (Shape.T (n := n'+1) (.sigma A' B' d' f')))
    (hw : Shape.WF (n := n+1) Δ (.sigma A B d f))
    (hw' : Shape.WF (n := n'+1) Δ (.sigma A' B' d' f'))
    (hf' : ∀ e ∈ f', TEvaluates Δ f'' e.ty e.tm e.inp.T e.out.T) :
    PiLabelEq Δ A B A' B' ∧ TShape.LE Δ d.T d'.T ∧
      ∀ e ∈ f, TEvaluates Δ f'' e.ty e.tm e.inp.T e.out.T := by
  obtain ⟨M, hn'M, hnM, h2⟩ := TShape.LE.at_succ h
  have hn : n ≤ M := Nat.le_of_succ_le_succ hnM
  exact ⟨h2.1, (TShape.LE.def hΔ hn hn'M).2 h2.2.1,
    TEvaluates.of_cover_lift hΔ hn hw.2.2.2 h2.2.2.1
      (TEvaluates.lift_cover hΔ hn'M hw'.2.2.2 hf')⟩

/-- λ-decomposition: a λ-shape's graph is covered by any bigger one's, and
the non-degeneracy conjuncts are about the smaller graph alone, so they
carry no information downwards. -/
theorem TShape.LE.lam_decomp {Δ : List Term} (hΔ : ⊢ Δ) {n n' k} {A A' : Term}
    {g : ShapeFun n} {g' : ShapeFun n'} {f'' : ShapeFun k}
    (h : TShape.LE Δ (Shape.T (n := n+1) (.lam A g)) (Shape.T (n := n'+1) (.lam A' g')))
    (hw : Shape.WF (n := n+1) Δ (.lam A g)) (hw' : Shape.WF (n := n'+1) Δ (.lam A' g'))
    (hg' : ∀ e ∈ g', TEvaluates Δ f'' e.ty e.tm e.inp.T e.out.T) :
    ∀ e ∈ g, TEvaluates Δ f'' e.ty e.tm e.inp.T e.out.T := by
  obtain ⟨M, hn'M, hnM, h2⟩ := TShape.LE.at_succ h
  exact TEvaluates.of_cover_lift hΔ (Nat.le_of_succ_le_succ hnM) hw.2.2.1 h2.1.1
    (TEvaluates.lift_cover hΔ hn'M hw'.2.2.1 hg')

/-- The lookup only sees its query label up to definitional equality. -/
theorem TEvaluates.label {Δ : List Term} {n} {f : ShapeFun n} {A a A' a' : Term}
    {x c : TShape} (hlab : LabelEq Δ A a A' a') (H : TEvaluates Δ f A a x c) :
    TEvaluates Δ f A' a' x c := by
  induction H with
  | bot => exact .bot
  | entry e he hl hin => exact .entry e he (hl.trans hlab) hin
  | lower hle _ ih => exact .lower hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- The lookup transports along a typed substitution, rule by rule.  The
`join` case is the only one with content, and it is `TShape.join_subst`. -/
theorem TEvaluates.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {n} {f : ShapeFun n} {A a : Term} {x : TShape} :
    ∀ {c : TShape}, TEvaluates Δ f A a x c →
      TEvaluates Θ (ShapeFun.subst (Shape.subst · τ) τ f) (A.subst τ) (a.subst τ)
        (x.subst τ) (c.subst τ) := by
  intro c h
  induction h with
  | bot => exact .bot
  | entry e he hl hin =>
    exact .entry ⟨e.ty.subst τ, e.tm.subst τ, e.inp.subst τ, e.out.subst τ⟩
      (ShapeFun.mem_subst.2 ⟨e, he, rfl⟩) (hl.subst hΘ W) (TShape.LE.subst hΘ W hin)
  | lower hle _ ih => exact .lower (TShape.LE.subst hΘ W hle) ih
  | join hc _ _ ih₁ ih₂ =>
    exact TShape.join_subst ▸ TEvaluates.join (TShape.Compat.subst hΘ W hc) ih₁ ih₂

/-- Pair-decomposition: the first component back at its own canonical
level, the label equality, and the graph covered by any bigger one's —
`lam_decomp` with a first component alongside. -/
theorem TShape.LE.pair_decomp {Δ : List Term} (hΔ : ⊢ Δ) {j n k} {A A' : Term}
    {x₂ : Shape j} {g₂ : ShapeFun j} {x : Shape n} {g : ShapeFun n} {f'' : ShapeFun k}
    (h : TShape.LE Δ (Shape.T (n := j+1) (ShapeS.pair A x₂ g₂))
      (Shape.T (n := n+1) (ShapeS.pair A' x g)))
    (hw : Shape.WF (n := j+1) Δ (.pair A x₂ g₂)) (hw' : Shape.WF (n := n+1) Δ (.pair A' x g))
    (hg' : ∀ e ∈ g, TEvaluates Δ f'' e.ty e.tm e.inp.T e.out.T) :
    TyEq Δ A A' ∧ TShape.LE Δ x₂.T x.T ∧
      ∀ e ∈ g₂, TEvaluates Δ f'' e.ty e.tm e.inp.T e.out.T := by
  obtain ⟨M, hnM, hjM, h2⟩ := TShape.LE.at_succ h
  have hj : j ≤ M := Nat.le_of_succ_le_succ hjM
  refine ⟨h2.2.2.2.2.1, (TShape.LE.def hΔ hj hnM).2 h2.1,
    TEvaluates.of_cover_lift hΔ hj hw.2.2.1 h2.2.1.1
      (TEvaluates.lift_cover hΔ hnM hw'.2.2.1 hg')⟩

/-- Typing, over `TShape`. -/
inductive TShape.HasType (Δ : List Term) : TShape → TShape → Prop where
  | bot : HasType Δ a TShape.type → HasType Δ (Shape.T (n := n) .bot) a
  | sort : HasType Δ (Shape.T (n := n) (.sort r)) (Shape.T (n := k) .type)
  | unit : r ≤ j → HasType Δ (Shape.T (n := n+1) (.unit r)) (Shape.T (n := k) (.sort j))
  | nat : HasType Δ (Shape.T (n := n+1) .nat) (Shape.T (n := k) .type)
  | zero : HasType Δ (Shape.T (n := n+1) .zero) (Shape.T (n := k+1) .nat)
  | succ {n k} {v : Shape n} : v.IsNumeral →
    HasType Δ (Shape.T (n := n+1) (.succ v)) (Shape.T (n := k+1) .nat)
  | id {n k r j} {A x y : Term} : r ≤ j → Shape.WF (n := n+1) Δ (.id r A x y) →
    HasType Δ (Shape.T (n := n+1) (.id r A x y)) (Shape.T (n := k) (.sort j))
  -- stated directly on `d` and `f`: `mono_l` pushes the premises into a
  -- smaller Π through `Eval.tHasType`, whose `join` case is `join_sort`.
  -- The outputs are typed at the *same* sort as the Π, so that `join_sort`
  -- can merge two of them without cumulativity
  | forallE {n k} {A B : Term} {d : Shape n} {f : ShapeFun n} {j : Bool} :
    HasType Δ d.T .type →
    (∀ e ∈ f, HasType Δ e.out.T (.sort j)) →
    Shape.WF (n := n+1) Δ (.forallE A B d f) →
    HasType Δ (Shape.T (n := n+1) (.forallE A B d f)) (Shape.T (n := k) (.sort j))
  | sigma {n k} {A B : Term} {d : Shape n} {f : ShapeFun n} :
    HasType Δ d.T .type →
    (∀ e ∈ f, HasType Δ e.out.T .type) →
    Shape.WF (n := n+1) Δ (.sigma A B d f) →
    HasType Δ (Shape.T (n := n+1) (.sigma A B d f)) (Shape.T (n := k) (.sort true))
  -- the shape is pinned, the graph is not: `g` is any graph below the
  -- generator `g₀`, which is where the codomain witnesses live (§5.5)
  | lam {n n₀ n'} {A₀ : Term} {g : ShapeFun n} {f : ShapeFun n'}
      {A B : Term} {d : Shape n'} {g₀ : List (Entry (Shape n₀) × TShape)} :
    HasType Δ d.T .type →
    (∀ e ∈ f, HasType Δ e.out.T .type) →
    Shape.WF (n := n+1) Δ (.lam A₀ g) →
    Shape.WF (n := n'+1) Δ (.forallE A B d f) →
    ShapeFun.WFE Δ (Shape.WF Δ) (g₀.map (·.1)) →
    (∀ e ∈ g, TEvaluates Δ (g₀.map (·.1)) e.ty e.tm e.inp.T e.out.T) →
    (∀ e ∈ g₀, TEvaluates Δ f e.1.ty e.1.tm e.1.inp.T e.2) →
    (∀ e ∈ g₀, HasType Δ e.1.out.T e.2) →
    -- the domain label is the Π's domain: intgrah's `Section` condition
    TyEq Δ A₀ A →
    HasType Δ (Shape.T (n := n+1) (.lam A₀ g)) (Shape.T (n := n'+1) (.forallE A B d f))
  -- **`lam`'s clause, with a first component alongside** (§5.1b).  The
  -- second component is a graph, so each of its entries is typed at the
  -- codomain read at *that entry's own* input, through the same generator
  -- `g₀`; there is no dominating first component, and joins are unions
  | pair {n n₀ n'} {A₀ : Term} {x : Shape n} {g : ShapeFun n} {f : ShapeFun n'}
      {A B : Term} {d : Shape n'} {g₀ : List (Entry (Shape n₀) × TShape)} :
    HasType Δ d.T .type →
    (∀ e ∈ f, HasType Δ e.out.T .type) →
    Shape.WF (n := n+1) Δ (.pair A₀ x g) →
    Shape.WF (n := n'+1) Δ (.sigma A B d f) →
    HasType Δ x.T d.T →
    ShapeFun.WFE Δ (Shape.WF Δ) (g₀.map (·.1)) →
    (∀ e ∈ g, TEvaluates Δ (g₀.map (·.1)) e.ty e.tm e.inp.T e.out.T) →
    (∀ e ∈ g₀, TEvaluates Δ f e.1.ty e.1.tm e.1.inp.T e.2) →
    (∀ e ∈ g₀, HasType Δ e.1.out.T e.2) →
    TyEq Δ A₀ A →
    HasType Δ (Shape.T (n := n+1) (.pair A₀ x g)) (Shape.T (n := n'+1) (.sigma A B d f))
  | refl {a n k} {w : Shape n} {A x y : Term} : Shape.WF Δ w →
    TShape.LE Δ (Shape.T (n := k+1) (.id true A x y)) a →
    HasType Δ a .type → HasType Δ (Shape.T (n := n+1) (.refl w)) a

/-- **Everything a shape is typed at is a type.** -/
theorem TShape.HasType.isType {Δ : List Term} {m a : TShape}
    (H : TShape.HasType Δ m a) : TShape.HasType Δ a TShape.type := by
  induction H with
  | bot hA _ => exact hA
  | sort => exact .sort
  | unit _ => exact .sort
  | nat => exact .sort
  | zero => exact .nat
  | succ _ => exact .nat
  | id _ _ => exact .sort
  | forallE _ _ _ _ _ => exact .sort
  | sigma _ _ _ _ _ => exact .sort
  | lam hd hf _ hwPi _ _ _ _ _ _ _ => exact .forallE hd hf hwPi
  | pair hd hf _ hwSg _ _ _ _ _ _ _ _ => exact .sigma hd hf hwSg
  | refl _ _ hA _ => exact hA

/-- Sorts are injective at every level. -/
theorem Shape.sort_inj {n} {r r' : Bool} (h : (Shape.sort r : Shape n) = Shape.sort r') :
    r = r' := by cases n <;> cases h <;> rfl

/-- The level at which a sort is written as the type is immaterial.  Needed
because the `forallE` clause types its outputs at the same sort as the Π
itself, so moving the Π's sort to another level has to move theirs. -/
theorem TShape.HasType.sort_level {Δ : List Term} {m a : TShape}
    (H : TShape.HasType Δ m a) : ∀ {k' : Nat} {j : Bool}, a.2 = Shape.sort j →
      TShape.HasType Δ m (Shape.T (n := k') (Shape.sort j)) := by
  induction H with
  | bot _ _ => intro _ _ _; exact .bot .sort
  | sort => intro _ _ ha; exact Shape.sort_inj ha ▸ .sort
  | unit hj => intro _ _ ha; exact Shape.sort_inj ha ▸ .unit hj
  | nat => intro _ _ ha; exact Shape.sort_inj ha ▸ .nat
  | zero => intro _ _ ha; exact absurd ha (by cases ha)
  | succ _ => intro _ _ ha; exact absurd ha (by cases ha)
  | id hj hw => intro _ _ ha; exact Shape.sort_inj ha ▸ .id hj hw
  | forallE hd hf hw _ ihf =>
    intro _ _ ha
    exact Shape.sort_inj ha ▸ .forallE hd (fun e he => ihf e he rfl) hw
  | sigma hd hf hw _ _ => intro _ _ ha; exact Shape.sort_inj ha ▸ .sigma hd hf hw
  -- the type is a pinned Π, resp. Σ, so it is not a sort outright
  | lam _ _ _ _ _ _ _ _ _ _ _ => intro _ _ ha; exact absurd ha (fun h => by cases h)
  | pair _ _ _ _ _ _ _ _ _ _ _ _ => intro _ _ ha; exact absurd ha (fun h => by cases h)
  | refl _ hc _ _ =>
    intro _ _ ha
    obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ hc
    rw [ha, Shape.lift_sort] at h2
    exact absurd h2 (fun x => x)

/-- Inversion at a Π, when the type is a sort.  `cases` needs the type to
be a variable — `Shape.sort` at a variable level is a stuck `match`, so it
does not unify with itself — which is why this is a lemma rather than a
`cases` at the use site. -/
theorem TShape.HasType.forallE_inv {Δ : List Term} {n} {A B : Term} {d : Shape n}
    {f : ShapeFun n} {a : TShape} {j : Bool}
    (H : TShape.HasType Δ (Shape.T (n := n+1) (.forallE A B d f)) a)
    (ha : a.2 = Shape.sort j) :
    TShape.HasType Δ d.T .type ∧
      (∀ e ∈ f, TShape.HasType Δ e.out.T (TShape.sort j)) ∧
      Shape.WF (n := n+1) Δ (.forallE A B d f) := by
  cases H with
  | forallE hd hf hw =>
    cases Shape.sort_inj ha
    exact ⟨hd, fun e he => (hf e he).sort_level rfl, hw⟩

theorem TShape.HasType.sigma_inv {Δ : List Term} {n} {A B : Term} {d : Shape n}
    {f : ShapeFun n} {a : TShape} {j : Bool}
    (H : TShape.HasType Δ (Shape.T (n := n+1) (.sigma A B d f)) a)
    (ha : a.2 = Shape.sort j) :
    TShape.HasType Δ d.T .type ∧
      (∀ e ∈ f, TShape.HasType Δ e.out.T .type) ∧
      Shape.WF (n := n+1) Δ (.sigma A B d f) := by
  cases H with
  | sigma hd hf hw => exact ⟨hd, hf, hw⟩

/-- **Right monotonicity.**  At `lam`, `pair` and `refl` the type may grow
and the clause takes it by transitivity; at the rigid types — the sorts
and `nat` — it can only change level, and the clause is re-applied at the
new one. -/
theorem TShape.HasType.mono_r {Δ : List Term} (hΔ : ⊢ Δ) {m a : TShape}
    (H : TShape.HasType Δ m a) :
    ∀ (a' : TShape), TShape.LE Δ a a' → TShape.HasType Δ a' TShape.type →
      TShape.HasType Δ m a' := by
  induction H with
  | bot _ _ => exact fun _ _ hA' => .bot hA'
  | sort =>
    exact fun a' h _ => by
      show TShape.HasType Δ _ ⟨a'.1, a'.2⟩
      rw [TShape.LE.sort_eq hΔ h]; exact .sort
  | unit hj =>
    exact fun a' h _ => by
      show TShape.HasType Δ _ ⟨a'.1, a'.2⟩
      rw [TShape.LE.sort_eq hΔ h]; exact .unit hj
  | nat =>
    exact fun a' h _ => by
      show TShape.HasType Δ _ ⟨a'.1, a'.2⟩
      rw [TShape.LE.sort_eq hΔ h]; exact .nat
  | zero => exact fun a' h _ => by obtain ⟨k, rfl⟩ := TShape.LE.nat_eq h; exact .zero
  | succ hN =>
    exact fun a' h _ => by obtain ⟨k, rfl⟩ := TShape.LE.nat_eq h; exact .succ hN
  | id hj hw =>
    exact fun a' h _ => by
      show TShape.HasType Δ _ ⟨a'.1, a'.2⟩
      rw [TShape.LE.sort_eq hΔ h]; exact .id hj hw
  | forallE hd hf hw _ _ =>
    exact fun a' h _ => by
      show TShape.HasType Δ _ ⟨a'.1, a'.2⟩
      rw [TShape.LE.sort_eq hΔ h]
      exact .forallE hd (fun e he => (hf e he).sort_level rfl) hw
  | sigma hd hf hw _ _ =>
    exact fun a' h _ => by
      show TShape.HasType Δ _ ⟨a'.1, a'.2⟩
      rw [TShape.LE.sort_eq hΔ h]; exact .sigma hd hf hw
  -- the type is pinned, so a bigger one is a bigger Π, resp. Σ, and it is
  -- the *codomain* witnesses that move: `hg₀ev`, resp. `hev`, are lookups
  -- in the Π's graph, and a bigger graph covers them (`TEvaluates.trans`).
  -- The new Π's own premises are read off `hA'`, which says it is a type
  | lam hd hf hwg hwPi hwg₀ hg hg₀ev hg₀ty hdom _ _ _ =>
    intro a' h hA'
    obtain ⟨k, s⟩ := a'
    obtain ⟨M, hnM, hkM, h2⟩ := TShape.LE.src_succ h
    cases k with
    | zero => cases s <;> exact absurd h2 (fun x => x)
    | succ k =>
      cases s with
      | forallE A' B' d' f' =>
        obtain ⟨hd', hf', hw'⟩ := hA'.forallE_inv rfl
        obtain ⟨hPi, _, hcov⟩ :=
          TShape.LE.forallE_decomp hΔ h hwPi hw' (TEvaluates.refl hw'.2.2.2)
        exact .lam hd' hf' hwg hw' hwg₀ hg
          (fun e he => TEvaluates.trans hΔ hcov (hg₀ev e he)) hg₀ty (hdom.trans hPi.1)
      | _ => exact absurd h2 (fun x => x)
  | pair hd hf hwp hwSg hxd hwg₀ hg hg₀ev hg₀ty hdom _ _ ihxd _ =>
    intro a' h hA'
    obtain ⟨k, s⟩ := a'
    obtain ⟨M, hnM, hkM, h2⟩ := TShape.LE.src_succ h
    cases k with
    | zero => cases s <;> exact absurd h2 (fun x => x)
    | succ k =>
      cases s with
      | sigma A' B' d' f' =>
        obtain ⟨hd', hf', hw'⟩ := hA'.sigma_inv rfl
        obtain ⟨hSg, hdd, hcov⟩ :=
          TShape.LE.sigma_decomp hΔ h hwSg hw' (TEvaluates.refl hw'.2.2.2)
        exact .pair hd' hf' hwp hw' (ihxd d'.T hdd hd') hwg₀ hg
          (fun e he => TEvaluates.trans hΔ hcov (hg₀ev e he)) hg₀ty (hdom.trans hSg.1)
      | _ => exact absurd h2 (fun x => x)
  | refl hw hc _ _ => exact fun _ h hA' => .refl hw (hc.trans hΔ h) hA'

/-- **Everything typed is well formed, and so is its type.**

The shape: a clause that carries a bound gets it from the order, which
carries the well-formedness of its lower bound; a clause whose subject is
pinned (`bot`, `unit`, `nat`, `zero`) has nothing to check.  The type: the
clauses whose type is not a sort carry its typing, so the induction
hypothesis gives it, and a sort or `nat` is well formed outright. -/
theorem TShape.HasType.wf {Δ : List Term} {m a : TShape}
    (H : TShape.HasType Δ m a) : TShape.WF Δ m ∧ TShape.WF Δ a := by
  induction H with
  | bot _ ih => exact ⟨TShape.WF.bot, ih.1⟩
  | sort => exact ⟨Shape.WF.sort, Shape.WF.sort⟩
  | unit _ => exact ⟨trivial, Shape.WF.sort⟩
  | nat => exact ⟨trivial, Shape.WF.sort⟩
  | zero => exact ⟨trivial, trivial⟩
  | succ hN => exact ⟨hN.wf, trivial⟩
  | id _ hw => exact ⟨hw, Shape.WF.sort⟩
  | forallE _ _ hw _ _ => exact ⟨hw, Shape.WF.sort⟩
  | sigma _ _ hw _ _ => exact ⟨hw, Shape.WF.sort⟩
  | lam _ _ hwg hwPi _ _ _ _ _ _ _ _ => exact ⟨hwg, hwPi⟩
  | pair _ _ hwp hwSg _ _ _ _ _ _ _ _ _ => exact ⟨hwp, hwSg⟩
  | refl hw _ _ ih => exact ⟨hw, ih.1⟩

/-- Typing does not see the level of its subject: `⟨n, m⟩` and
`⟨k, m.lift k⟩` are order-equivalent, and every clause reaches the subject
only through the order or a pin.  Its converse `lower_subject` is below;
the level-indexed relation had the first at 40 lines and the second not at
all (§5.5). -/
theorem TShape.HasType.lift_subject {Δ : List Term} (hΔ : ⊢ Δ) {m a : TShape}
    (H : TShape.HasType Δ m a) : ∀ {k}, m.1 ≤ k → TShape.HasType Δ (m.lift k) a := by
  have succ_of {n k} (hk : n + 1 ≤ k) : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  induction H with
  | bot hA _ => intro k _; show TShape.HasType Δ ⟨k, _⟩ _; rw [Shape.lift_bot]; exact .bot hA
  | sort => intro k _; show TShape.HasType Δ ⟨k, _⟩ _; rw [Shape.lift_sort]; exact .sort
  | unit hj => intro k hk; obtain ⟨k, rfl⟩ := succ_of hk; exact .unit hj
  | nat => intro k hk; obtain ⟨k, rfl⟩ := succ_of hk; exact .nat
  | zero => intro k hk; obtain ⟨k, rfl⟩ := succ_of hk; exact .zero
  | succ hN =>
    intro k hk; obtain ⟨k, rfl⟩ := succ_of hk
    exact .succ ((Shape.IsNumeral.lift_iff (Nat.le_of_succ_le_succ hk)).2 hN)
  | id hj hw => intro k hk; obtain ⟨k, rfl⟩ := succ_of hk; exact .id hj hw
  | forallE hd hf hw ihd ihf =>
    intro k hk; obtain ⟨k, rfl⟩ := succ_of hk
    have hn := Nat.le_of_succ_le_succ hk
    exact .forallE (ihd hn)
      (fun e he => by
        obtain ⟨e₀, he₀, rfl⟩ := ShapeFun.mem_lift.1 he
        exact ihf e₀ he₀ hn)
      ((Shape.lift_wf (Nat.succ_le_succ hn)).2 hw)
  | sigma hd hf hw ihd ihf =>
    intro k hk; obtain ⟨k, rfl⟩ := succ_of hk
    have hn := Nat.le_of_succ_le_succ hk
    exact .sigma (ihd hn)
      (fun e he => by
        obtain ⟨e₀, he₀, rfl⟩ := ShapeFun.mem_lift.1 he
        exact ihf e₀ he₀ hn)
      ((Shape.lift_wf (Nat.succ_le_succ hn)).2 hw)
  | lam hd hf hwg hwPi hwg₀ hg hg₀ev hg₀ty hdom _ _ _ =>
    intro k hk; obtain ⟨k, rfl⟩ := succ_of hk
    have hn := Nat.le_of_succ_le_succ hk
    exact .lam hd hf ((Shape.lift_wf (Nat.succ_le_succ hn)).2 hwg) hwPi hwg₀
      (TEvaluates.lift_cover hΔ hn hwg.2.2.1 hg) hg₀ev hg₀ty hdom
  | pair hd hf hwp hwSg hxd hwg₀ hg hg₀ev hg₀ty hdom _ _ ihxd _ =>
    intro k hk; obtain ⟨k, rfl⟩ := succ_of hk
    have hn := Nat.le_of_succ_le_succ hk
    exact .pair hd hf ((Shape.lift_wf (Nat.succ_le_succ hn)).2 hwp) hwSg
      (ihxd hn) hwg₀ (TEvaluates.lift_cover hΔ hn hwp.2.2.1 hg) hg₀ev hg₀ty hdom
  | refl hw hc hA _ =>
    intro k hk; obtain ⟨k, rfl⟩ := succ_of hk
    exact .refl ((Shape.lift_wf (Nat.le_of_succ_le_succ hk)).2 hw) hc hA

/-- **And the level of the subject can be lowered again.**  This is the
reflection direction that §5.5 shows the level-indexed definition cannot
have: it works here because every object a clause quantifies over — the
codomain generator `g₀`, the pair's dominator `x` and its code `c` — is a
`TShape`, so `lift` touches none of them.  What is left is entrywise, and
`TEvaluates.lower_cover` does it.

With `lift_subject` this makes typing blind to the subject's level, which
is what lets `mono_l` at a sort be run at one fixed level. -/
theorem TShape.HasType.lower_subject {Δ : List Term} (hΔ : ⊢ Δ) :
    ∀ {N} {y : Shape N} {k}, N ≤ k → ∀ {a : TShape},
      TShape.HasType Δ (y.lift k).T a → TShape.HasType Δ y.T a := by
  intro N
  induction N with
  | zero =>
    intro y k hk a H
    cases k with
    | zero => rwa [Shape.lift_self] at H
    | succ k =>
      cases y with
      | bot =>
        cases H with | bot hA
        exact .bot hA
      | sort r =>
        cases H with | sort
        exact .sort
  | succ N ih =>
    intro y k hk a H
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hk' : N ≤ k := Nat.le_of_succ_le_succ hk
    cases y with
    | bot =>
      cases H with | bot hA
      exact .bot hA
    | sort r =>
      cases H with | sort
      exact .sort
    | unit r =>
      cases H with | unit hj
      exact .unit hj
    | nat =>
      cases H with | nat
      exact .nat
    | zero =>
      cases H with | zero
      exact .zero
    | succ v =>
      cases H with | succ hN
      exact .succ ((Shape.IsNumeral.lift_iff hk').1 hN)
    | id r A x y =>
      cases H with | id hj hw
      exact .id hj hw
    | refl w =>
      cases H with | refl hw hc hA
      exact .refl ((Shape.lift_wf hk').1 hw) hc hA
    | forallE A B d f =>
      cases H with | forallE hd hf hw
      exact .forallE (ih hk' hd)
        (fun e he => ih hk' (hf _ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)))
        ((Shape.lift_wf hk).1 hw)
    | sigma A B d f =>
      cases H with | sigma hd hf hw
      exact .sigma (ih hk' hd)
        (fun e he => ih hk' (hf _ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)))
        ((Shape.lift_wf hk).1 hw)
    | lam A₀ g =>
      cases H with | lam hd hf hwg hwPi hwg₀ hg hg₀ev hg₀ty hdom
      have hwg' := (Shape.lift_wf (s := Shape.lam A₀ g) hk).1 hwg
      exact .lam hd hf hwg' hwPi hwg₀
        (TEvaluates.lower_cover hΔ hk' hwg'.2.2.1 hg) hg₀ev hg₀ty hdom
    | pair A₀ x g =>
      cases H with | pair hd hf hwp hwSg hxd hwg₀ hg hg₀ev hg₀ty hdom
      have hwp' := (Shape.lift_wf (s := ShapeS.pair A₀ x g) hk).1 hwp
      exact .pair hd hf hwp' hwSg (ih hk' hxd) hwg₀
        (TEvaluates.lower_cover hΔ hk' hwp'.2.2.1 hg) hg₀ev hg₀ty hdom

/-- `⊥` is typed at `⊥`, since `⊥` is a type. -/
theorem TShape.HasType.bot_bot {Δ : List Term} {m : TShape} (h : m.2 = Shape.bot) :
    TShape.HasType Δ m TShape.bot := by
  show TShape.HasType Δ ⟨m.1, m.2⟩ _
  rw [h]; exact .bot (.bot .sort)

/-- **Cumulativity**, which the sort-typed clauses build in: each carries
the sort as a bound (`unit`, `id`) or inherits it from its outputs
(`forallE`), and the rigid ones are already at `.type`.  Stated in
`sort_level`'s form, with the sort read off `a.2`, because `Shape.sort` at
a variable level is a stuck `match` and will not unify with itself. -/
theorem TShape.HasType.cumul {Δ : List Term} {m a : TShape}
    (H : TShape.HasType Δ m a) : ∀ {k' : Nat} {r s : Bool}, a.2 = Shape.sort r → r ≤ s →
      TShape.HasType Δ m (Shape.T (n := k') (Shape.sort s)) := by
  induction H with
  | bot _ _ => intro _ _ _ _ _; exact .bot .sort
  | sort => intro _ _ _ ha hrs; rw [Bool.eq_true_of_le (Shape.sort_inj ha).symm hrs]; exact .sort
  | unit hj => intro _ _ _ ha hrs; exact .unit (Bool.le_tr hj (Shape.sort_inj ha ▸ hrs))
  | nat => intro _ _ _ ha hrs; rw [Bool.eq_true_of_le (Shape.sort_inj ha).symm hrs]; exact .nat
  | zero => intro _ _ _ ha _; exact absurd ha (fun h => by cases h)
  | succ _ => intro _ _ _ ha _; exact absurd ha (fun h => by cases h)
  | id hj hw => intro _ _ _ ha hrs; exact .id (Bool.le_tr hj (Shape.sort_inj ha ▸ hrs)) hw
  | forallE hd _ hw _ ihf =>
    intro _ _ _ ha hrs
    exact .forallE hd (fun e he => ihf e he rfl (Shape.sort_inj ha ▸ hrs)) hw
  | sigma hd hf hw _ _ =>
    intro _ _ _ ha hrs
    rw [Bool.eq_true_of_le (Shape.sort_inj ha).symm hrs]; exact .sigma hd hf hw
  | lam _ _ _ _ _ _ _ _ _ _ _ => intro _ _ _ ha _; exact absurd ha (fun h => by cases h)
  | pair _ _ _ _ _ _ _ _ _ _ _ _ => intro _ _ _ ha _; exact absurd ha (fun h => by cases h)
  | refl _ hc _ _ =>
    intro _ _ _ ha _
    obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ hc
    rw [ha, Shape.lift_sort] at h2
    exact absurd h2 (fun x => x)

/-- **Typed substitution.**  Every clause transports componentwise: the
labels by the term lemmas, the shapes by `Shape.WF.subst` and
`Shape.LE.subst`, and the lookups by `TEvaluates.subst`.

This is what the list-of-pairs generator buys.  With a *function*
`cs : Entry (Shape n₀) → TShape` (which is what strict positivity forces if
the witness is not to be quantified existentially inside the premise),
`fun e' => (cs e').subst τ` is the wrong reindexing — it gives
`cs (e.subst τ) |>.subst τ` where `(cs e).subst τ` is wanted.  A list is
reindexed by `List.map`, which has no such mismatch. -/
theorem TShape.HasType.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {m a : TShape} (H : TShape.HasType Δ m a) :
    TShape.HasType Θ (m.subst τ) (a.subst τ) := by
  induction H with
  | bot _ ih => simp only [TShape.subst_T, Shape.subst_bot]; exact .bot ih
  | sort => simp only [TShape.subst_T, Shape.subst_sort]; exact .sort
  | unit hj => simp only [TShape.subst_T, Shape.subst_sort]; exact .unit hj
  | nat => simp only [TShape.subst_T, Shape.subst_sort]; exact .nat
  | zero => simp only [TShape.subst_T]; exact .zero
  | succ hN => simp only [TShape.subst_T]; exact .succ hN.subst
  | id hj hw =>
    simp only [TShape.subst_T, Shape.subst_sort]
    exact .id hj (Shape.WF.subst hΘ W hw)
  | forallE hd _ hw ihd ihf =>
    simp only [TShape.subst_T, Shape.subst_sort] at *
    refine .forallE ihd (fun e he => ?_) (Shape.WF.subst hΘ W hw)
    obtain ⟨e₀, he₀, rfl⟩ := ShapeFun.mem_subst.1 he
    exact ihf e₀ he₀
  | sigma hd _ hw ihd ihf =>
    simp only [TShape.subst_T, Shape.subst_sort] at *
    refine .sigma ihd (fun e he => ?_) (Shape.WF.subst hΘ W hw)
    obtain ⟨e₀, he₀, rfl⟩ := ShapeFun.mem_subst.1 he
    exact ihf e₀ he₀
  | @lam _ _ _ _ _ _ _ _ _ g₀ _ _ hwg hwPi hwg₀ hg hg₀ev _ hdom ihd ihf ihg₀ty =>
    simp only [TShape.subst_T] at *
    refine .lam (g₀ := g₀.map fun p =>
        (⟨p.1.ty.subst τ, p.1.tm.subst τ, p.1.inp.subst τ, p.1.out.subst τ⟩, p.2.subst τ))
      ihd (fun e he => ?_) (Shape.WF.subst hΘ W hwg) (Shape.WF.subst hΘ W hwPi) ?_
      (fun e he => ?_) (fun e he => ?_) (fun e he => ?_) (hdom.subst hΘ W)
    · obtain ⟨e₀, he₀, rfl⟩ := ShapeFun.mem_subst.1 he
      exact ihf e₀ he₀
    · have := ShapeFun.WFE.subst_of (Δ := Δ) (Shape.WF.subst hΘ W) hwg₀
      simpa [ShapeFun.subst, List.map_map, Function.comp_def] using this
    · obtain ⟨e₀, he₀, rfl⟩ := ShapeFun.mem_subst.1 he
      have := TEvaluates.subst hΘ W (hg e₀ he₀)
      simpa [ShapeFun.subst, List.map_map, Function.comp_def] using this
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
      exact TEvaluates.subst hΘ W (hg₀ev p hp)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
      exact ihg₀ty p hp
  | @pair _ _ _ _ _ _ _ _ _ _ g₀ _ _ hwp hwSg _ hwg₀ hg hg₀ev _ hdom ihd ihf ihxd ihg₀ty =>
    simp only [TShape.subst_T] at *
    refine .pair (g₀ := g₀.map fun p =>
        (⟨p.1.ty.subst τ, p.1.tm.subst τ, p.1.inp.subst τ, p.1.out.subst τ⟩, p.2.subst τ))
      ihd (fun e he => ?_) (Shape.WF.subst hΘ W hwp) (Shape.WF.subst hΘ W hwSg)
      ihxd ?_ (fun e he => ?_) (fun e he => ?_) (fun e he => ?_) (hdom.subst hΘ W)
    · obtain ⟨e₀, he₀, rfl⟩ := ShapeFun.mem_subst.1 he
      exact ihf e₀ he₀
    · have := ShapeFun.WFE.subst_of (Δ := Δ) (Shape.WF.subst hΘ W) hwg₀
      simpa [ShapeFun.subst, List.map_map, Function.comp_def] using this
    · obtain ⟨e₀, he₀, rfl⟩ := ShapeFun.mem_subst.1 he
      have := TEvaluates.subst hΘ W (hg e₀ he₀)
      simpa [ShapeFun.subst, List.map_map, Function.comp_def] using this
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
      exact TEvaluates.subst hΘ W (hg₀ev p hp)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
      exact ihg₀ty p hp
  | refl hw hc _ ih =>
    simp only [TShape.subst_T] at *
    exact .refl (Shape.WF.subst hΘ W hw) (TShape.LE.subst hΘ W hc) ih

/-- **The join of two types is a type.**  Only `forallE` and `sigma` have
content: the join is componentwise, the domains join by the induction
hypothesis one level down, and the graphs append.  Everywhere else the join
is one of the two arguments, or the head mismatch makes `Compat` false, or
the shape cannot be typed at a sort at all — a λ, a pair and a `refl` are
typed only below a Π, a Σ and an `id`, none of which is below a sort. -/
theorem TShape.HasType.join_sort {Δ : List Term} (hΔ : ⊢ Δ) :
    ∀ {n} {y z : Shape n} {a : TShape} {j : Bool}, a.2 = Shape.sort j →
      TShape.HasType Δ y.T a → TShape.HasType Δ z.T a → Shape.Compat Δ y z →
      TShape.HasType Δ (y.join z).T a := by
  intro n
  induction n with
  | zero =>
    intro y z a j ha hy hz _
    cases y with
    | bot => exact hz
    | sort r => cases z <;> exact hy
  | succ n ih =>
    intro y z a j ha hy hz hc
    cases y with
    | bot => exact hz
    | sort r | unit r | nat | zero | id r A x y =>
      cases z <;> first | exact hy | exact absurd hc (fun x => x)
    | succ v =>
      cases z with
      | bot => exact hy
      | succ v' => cases hy; cases ha
      | _ => exact absurd hc (fun x => x)
    | forallE A B d f =>
      cases z with
      | forallE A' B' d' f' =>
        have ⟨hd, hf, hw⟩ := hy.forallE_inv ha
        have ⟨hd', hf', hw'⟩ := hz.forallE_inv ha
        show TShape.HasType Δ _ ⟨a.1, a.2⟩
        rw [ha]
        exact .forallE (ih rfl hd hd' hc.2.1)
          (fun e he => match List.mem_append.1 he with
            | .inl h => hf e h
            | .inr h => hf' e h)
          (Shape.WF.join hΔ hc hw hw')
      | _ => first | exact hy | exact absurd hc (fun x => x)
    | sigma A B d f =>
      cases z with
      | sigma A' B' d' f' =>
        cases hy with | sigma hd hf hw
        have ⟨hd', hf', hw'⟩ := hz.sigma_inv rfl
        exact .sigma (ih rfl hd hd' hc.2.1)
          (fun e he => match List.mem_append.1 he with
            | .inl h => hf e h
            | .inr h => hf' e h)
          (Shape.WF.join hΔ hc hw hw')
      | _ => first | exact hy | exact absurd hc (fun x => x)
    | lam g =>
      cases z with
      | lam g' =>
        cases hy with | lam _ _ _ _ _ _ _
        exact absurd ha (fun h => by cases h)
      | _ => first | exact hy | exact absurd hc (fun x => x)
    | pair A₀ x g =>
      cases z with
      | pair A₀' x' g' =>
        cases hy with | pair _ _ _ _ _ _ _ _ _
        exact absurd ha (fun h => by cases h)
      | _ => first | exact hy | exact absurd hc (fun x => x)
    | refl w =>
      cases z with
      | refl w' =>
        cases hy with | refl _ hcg _
        obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ hcg
        rw [ha, Shape.lift_sort] at h2
        exact absurd h2 (fun x => x)
      | _ => first | exact hy | exact absurd hc (fun x => x)

/-- Everything the lookup returns is typed at a sort, when the graph's
outputs are.  `bot` is `⊥`, `entry` is the hypothesis, `lower` is the
lowering it is handed, and `join` is `join_sort`. -/
theorem ShapeFun.Eval.tHasType {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n}
    {A a : Term} {x : Shape n} {c : TShape} {j : Bool} (hc : c.2 = Shape.sort j)
    (hty : ∀ e ∈ f, TShape.HasType Δ e.out.T c)
    (hlow : ∀ {u v : Shape n}, Shape.LE Δ u v → TShape.HasType Δ v.T c →
      TShape.HasType Δ u.T c) :
    ∀ {y : Shape n}, ShapeFun.Eval Δ (Shape.LE Δ) f A a x y →
      TShape.HasType Δ y.T c := by
  intro y h
  induction h with
  | bot =>
    refine .bot ?_
    show TShape.HasType Δ ⟨c.1, c.2⟩ _
    rw [hc]; exact .sort
  | entry e he _ _ => exact hty e he
  | lower hle _ ih => exact hlow hle ih
  | join hcj _ _ ih₁ ih₂ => exact TShape.HasType.join_sort hΔ hc ih₁ ih₂ hcj

/-- **Left monotonicity at a sort, at a fixed level.**

This is the shape the old `Shape.HasType.mono_l_sort` had, and the reason
it can be an induction on the level where the general `mono_l` cannot: at a
sort the `lam` and `pair` clauses never arise — a λ is typed only below a
Π, a pair only below a Σ, and neither is below a sort — so the
existentially chosen `n₀`, which can sit *above* the subject's level, never
appears.  Both shapes being at one level is what keeps the components at
`N`, where the induction hypothesis lives; `TShape.LE` would put them at a
`max` that the smaller shape can push arbitrarily high. -/
theorem TShape.HasType.mono_l_sort_T {Δ : List Term} (hΔ : ⊢ Δ) :
    ∀ {N} {y y' : Shape N} {a : TShape} {j : Bool}, a.2 = Shape.sort j →
      TShape.HasType Δ y.T a → Shape.LE Δ y' y → TShape.HasType Δ y'.T a := by
  intro N
  induction N with
  | zero =>
    intro y y' a j ha hy hle
    cases hy with
    | bot hA => cases Shape.le_bot_iff.1 hle; exact .bot hA
    | sort =>
      match Shape.le_sort hle with
      | .inl hb => cases hb; exact .bot .sort
      | .inr hs => cases hs; exact .sort
  | succ N ih =>
    intro y y' a j ha hy hle
    cases hy with
    | bot hA => cases Shape.le_bot_iff.1 hle; exact .bot hA
    | sort =>
      match Shape.le_sort hle with
      | .inl hb => cases hb; exact .bot .sort
      | .inr hs => cases hs; exact .sort
    | unit hj =>
      match Shape.le_unit hle with
      | .inl hb => cases hb; exact .bot .sort
      | .inr hs => cases hs; exact .unit hj
    | nat =>
      match Shape.le_nat hle with
      | .inl hb => cases hb; exact .bot .sort
      | .inr hs => cases hs; exact .nat
    | zero =>
      match Shape.le_zero hle with
      | .inl hb => cases hb; exact .bot .nat
      | .inr hs => cases hs; exact .zero
    | succ hN =>
      match Shape.le_succ hle with
      | .inl hb => cases hb; exact .bot .nat
      | .inr ⟨v', hs, hv⟩ => cases hs; exact .succ (Shape.IsNumeral.lower hv hN)
    | id hj hw =>
      match Shape.le_id hle with
      | .inl hb => cases hb; exact .bot .sort
      | .inr ⟨A', a', b', hs, ⟨⟨u, hA⟩, hx, hy⟩⟩ =>
        cases hs
        exact .id hj ⟨⟨u, hA.hasType.1⟩, hx.hasType.1, hy.hasType.1⟩
    | forallE hd hf hw =>
      match Shape.le_forallE hle with
      | .inl hb => cases hb; exact .bot .sort
      | .inr ⟨A', B', d', f', hs, _, hdd, hff⟩ =>
        cases hs
        refine .forallE (ih rfl hd hdd) (fun e he => ?_) (Shape.LE.wf hle)
        exact (ShapeFun.Eval.tHasType hΔ ha (fun e he => (hf e he).sort_level rfl)
          (fun hle' hv => ih ha hv hle') (hff.1 e he)).sort_level rfl
    | sigma hd hf hw =>
      match Shape.le_sigma hle with
      | .inl hb => cases hb; exact .bot .sort
      | .inr ⟨A', B', d', f', hs, _, hdd, hff⟩ =>
        cases hs
        refine .sigma (ih rfl hd hdd) (fun e he => ?_) (Shape.LE.wf hle)
        exact ShapeFun.Eval.tHasType hΔ rfl hf (fun hle' hv => ih rfl hv hle') (hff.1 e he)
    -- a λ is typed only at a Π and a pair only at a Σ, neither of which is
    -- a sort, so `ha` refutes both outright now that the type is pinned
    | lam _ _ _ _ _ _ _ => exact absurd ha (fun h => by cases h)
    | pair _ _ _ _ _ _ _ _ => exact absurd ha (fun h => by cases h)
    | refl _ hc _ =>
      have h2 := TShape.LE.def_mp (k := max _ a.1 + 1)
        (Nat.succ_le_succ (Nat.le_max_left ..))
        (Nat.le_succ_of_le (Nat.le_max_right ..)) hc
      rw [ha, Shape.lift_sort] at h2
      exact absurd h2 (fun x => x)

/-- **Left monotonicity at a sort**, with the two shapes at any levels.
`lift_subject` puts both at the level the order compares them at,
`mono_l_sort_T` does the work there, and `lower_subject` brings the smaller
one back down. -/
theorem TShape.HasType.mono_l_sort {Δ : List Term} (hΔ : ⊢ Δ) {m a : TShape}
    {j : Bool} (ha : a.2 = Shape.sort j) (H : TShape.HasType Δ m a)
    {m' : TShape} (h : TShape.LE Δ m' m) : TShape.HasType Δ m' a :=
  lower_subject hΔ (Nat.le_max_left ..)
    (mono_l_sort_T hΔ ha (H.lift_subject hΔ (Nat.le_max_right ..)) h)

/-- **Left monotonicity.**  Where the clause carries a bound the smaller
shape slides down it by transitivity; where the subject is pinned, `⊥` is
all that sits strictly below, and the `bot` clause takes it. -/
theorem TShape.HasType.mono_l {Δ : List Term} (hΔ : ⊢ Δ) {m a : TShape}
    (H : TShape.HasType Δ m a) :
    ∀ {m' : TShape}, TShape.LE Δ m' m → TShape.HasType Δ m' a := by
  induction H with
  | bot hA _ =>
    exact fun {m'} h => by
      show TShape.HasType Δ ⟨m'.1, m'.2⟩ _
      rw [TShape.le_bot hΔ rfl h]; exact .bot hA
  | sort =>
    intro m' h
    obtain ⟨j, s⟩ := m'
    cases j with
    | zero => cases s with | bot => exact .bot .sort | sort r' => exact .sort
    | succ j =>
      obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ h
      rw [Shape.lift_sort] at h2
      cases s <;> first | exact .bot .sort | exact .sort | exact absurd h2 (fun x => x)
  | unit hj =>
    exact fun {m'} h => by
      obtain ⟨j, s⟩ := m'
      obtain ⟨M, _, _, h2⟩ := TShape.LE.at_succ h
      cases j <;> cases s <;> first
        | exact .bot .sort | (cases h2; exact .unit hj) | exact absurd h2 (fun x => x)
  | nat =>
    exact fun {m'} h => by
      obtain ⟨j, s⟩ := m'
      obtain ⟨M, _, _, h2⟩ := TShape.LE.at_succ h
      cases j <;> cases s <;> first
        | exact .bot .sort | exact .nat | exact absurd h2 (fun x => x)
  | zero =>
    exact fun {m'} h => by
      obtain ⟨j, s⟩ := m'
      obtain ⟨M, _, _, h2⟩ := TShape.LE.at_succ h
      cases j <;> cases s <;> first
        | exact .bot .nat | exact .zero | exact absurd h2 (fun x => x)
  | succ hN =>
    exact fun {m'} h => by
      obtain ⟨j, s⟩ := m'
      obtain ⟨M, hnM, hjM, h2⟩ := TShape.LE.at_succ h
      cases j with
      | zero => cases s <;> first | exact .bot .nat | exact absurd h2 (fun x => x)
      | succ j =>
        cases s with
        | bot => exact .bot .nat
        | succ v' =>
          exact .succ ((Shape.IsNumeral.lift_iff (Nat.le_of_succ_le_succ hjM)).1
            (Shape.IsNumeral.lower h2 ((Shape.IsNumeral.lift_iff hnM).2 hN)))
        | _ => exact absurd h2 (fun x => x)
  | id hj hw =>
    exact fun {m'} h => by
      obtain ⟨j, s⟩ := m'
      obtain ⟨M, _, _, h2⟩ := TShape.LE.at_succ h
      cases j with
      | zero => cases s <;> first | exact .bot .sort | exact absurd h2 (fun x => x)
      | succ j =>
        cases s with
        | bot => exact .bot .sort
        | id r' A' x' y' =>
          obtain ⟨rfl, ⟨u, hA⟩, hx, hy⟩ := h2
          exact .id hj ⟨⟨u, hA.hasType.1⟩, hx.hasType.1, hy.hasType.1⟩
        | _ => exact absurd h2 (fun x => x)
  -- a Π and a Σ are typed at a sort, so they are `mono_l_sort`'s business:
  -- the components sit one level down, where the order compares them
  -- levelwise and the induction on the level reaches them
  | forallE hd hf hw _ _ => exact mono_l_sort hΔ rfl (.forallE hd hf hw)
  | sigma hd hf hw _ _ => exact mono_l_sort hΔ rfl (.sigma hd hf hw)
  -- the λ-shape is pinned, so a smaller one is `⊥` or another λ, whose
  -- graph the order covers by `g` at a level above both; `of_cover_lift`
  -- brings that coverage back down and composes it with `g`'s own
  | lam hd hf hwg hwPi hwg₀ hg hg₀ev hg₀ty hdom _ _ _ =>
    intro m' h
    obtain ⟨j, s⟩ := m'
    obtain ⟨M, hnM, hjM, h2⟩ := TShape.LE.at_succ h
    cases j with
    | zero =>
      cases s <;> first
        | exact .bot (.forallE hd hf hwPi)
        | exact absurd h2 (fun x => x)
    | succ j =>
      cases s with
      | bot => exact .bot (.forallE hd hf hwPi)
      | lam A' g' =>
        have hwg' : Shape.WF (n := j+1) Δ (.lam A' g') :=
          (Shape.lift_wf hjM).1 (Shape.LE.wf h2)
        exact .lam hd hf hwg' hwPi hwg₀
          (TShape.LE.lam_decomp hΔ h hwg' hwg hg) hg₀ev hg₀ty (h2.2.2.2.1.trans hdom)
      | _ => exact absurd h2 (fun x => x)
  | pair hd hf hwp hwSg hxd hwg₀ hg hg₀ev hg₀ty hdom _ _ ihxd _ =>
    intro m' h
    obtain ⟨j, s⟩ := m'
    obtain ⟨M, _, hjM, h2⟩ := TShape.LE.at_succ h
    cases j with
    | zero => cases s <;> first | exact .bot (.sigma hd hf hwSg) | exact absurd h2 (fun x => x)
    | succ j =>
      cases s with
      | bot => exact .bot (.sigma hd hf hwSg)
      | pair A' x' g' =>
        have hwp' : Shape.WF (n := j+1) Δ (.pair A' x' g') :=
          (Shape.lift_wf hjM).1 (Shape.LE.wf h2)
        obtain ⟨hA', hx', hcov⟩ := TShape.LE.pair_decomp hΔ h hwp' hwp hg
        exact .pair hd hf hwp' hwSg (ihxd hx') hwg₀ hcov hg₀ev hg₀ty (hA'.trans hdom)
      | _ => exact absurd h2 (fun x => x)
  | refl hw hc hA _ =>
    exact fun {m'} h => by
      obtain ⟨j, s⟩ := m'
      obtain ⟨M, _, hjM, h2⟩ := TShape.LE.at_succ h
      cases j with
      | zero => cases s <;> first | exact .bot hA | exact absurd h2 (fun x => x)
      | succ j =>
        cases s with
        | bot => exact .bot hA
        | refl w' =>
          exact .refl ((Shape.lift_wf (Nat.le_of_succ_le_succ hjM)).1 (Shape.LE.wf h2)) hc hA
        | _ => exact absurd h2 (fun x => x)

/-! ## Proof irrelevance, over `TShape`

`HasType Δ a .prop → HasType Δ x a → x = ⊥`.  Master's `HasType.proofIrrel`
and the shape-level content of the syntactic `proofIrrel` rule.

The old level-indexed proof inducted on the *level*, because everything in
sight lived at one.  Here it is an induction on the **derivation**, and the
`lam` clause's own induction hypothesis — the one for `hg₀ty`, at the
codomain generator — is exactly the recursive call needed.  That is the
generator earning its keep a second time: with a dominating codomain there
is no such hypothesis to have. -/

/-- The join of two types at one sort is a type at that sort, over
`TShape`: both sides go up to the level the join is taken at. -/
theorem TShape.HasType.join_sort' {Δ : List Term} (hΔ : ⊢ Δ) {y z c : TShape}
    {j : Bool} (hc : c.2 = Shape.sort j) (hy : TShape.HasType Δ y c)
    (hz : TShape.HasType Δ z c) (hyz : TShape.Compat Δ y z) :
    TShape.HasType Δ (TShape.join y z) c :=
  TShape.HasType.join_sort hΔ hc (hy.lift_subject hΔ (Nat.le_max_left ..))
    (hz.lift_subject hΔ (Nat.le_max_right ..)) hyz

/-- **Everything typed at `nat` is a numeral.**  The three clauses whose
type can be a `nat` shape are `bot`, `zero` and `succ`, and those are the
three constructors of `IsNumeral`. -/
theorem TShape.HasType.isNumeral {Δ : List Term} (hΔ : ⊢ Δ) {m a : TShape}
    (ha : TShape.LE Δ a (Shape.T (n := 1) ShapeS.nat)) (h : TShape.HasType Δ m a) :
    Shape.IsNumeral m.2 := by
  cases TShape.HasType.mono_r hΔ h (Shape.T (n := 1) ShapeS.nat) ha .nat with
  | bot _ => exact .bot
  | zero => exact .zero
  | succ hN => exact .succ hN
  | refl _ hc _ =>
    obtain ⟨M, _, _, h2⟩ := TShape.LE.at_succ hc
    exact absurd h2 (fun x => x)

/-- And back: a numeral is typed at `nat`.  `bot` needs `nat` to be a
type, which it is at every level. -/
theorem Shape.IsNumeral.hasType {Δ : List Term} : ∀ {n} {v : Shape n},
    Shape.IsNumeral v → TShape.HasType Δ v.T (Shape.T (n := 1) ShapeS.nat) := by
  intro n v h
  induction h with
  | bot => exact .bot .nat
  | zero => exact .zero
  | succ hw _ => exact .succ hw

/-- The predecessor of a numeral is one. -/
theorem Shape.IsNumeral.pred {n} {v : Shape n}
    (h : Shape.IsNumeral (n := n+1) (.succ v)) : Shape.IsNumeral v := by
  cases h with | succ hw => exact hw

/-! ### Concatenating two generators

`HasType.lam` and `HasType.pair` both certify a graph by a *generator*: a
list of entries paired with codes, covering the graph, each code a lookup
in the type's codomain graph and each output typed at its code.  Joining
two such shapes appends the graphs, so the generators concatenate — after
lifting both to a common level, since a generator is a list at one level.
These four lemmas are that concatenation, and they serve `lam` and `pair`
alike. -/

/-- The common level's lifted generator. -/
abbrev TShape.liftGen {n : Nat} (m : Nat) (g₀ : List (Entry (Shape n) × TShape)) :
    List (Entry (Shape m) × TShape) :=
  g₀.map fun p => ((⟨p.1.ty, p.1.tm, p.1.inp.lift m, p.1.out.lift m⟩ : Entry (Shape m)), p.2)

theorem TShape.liftGen_map {n m : Nat} {g₀ : List (Entry (Shape n) × TShape)} :
    (TShape.liftGen m g₀).map (·.1) = ShapeFun.lift (Shape.lift m) (g₀.map (·.1)) := by
  simp [TShape.liftGen, ShapeFun.lift, List.map_map, Function.comp_def]

theorem join_gen_wf {Δ : List Term} {n₀ n₀'}
    {g₀ : List (Entry (Shape n₀) × TShape)} {g₀' : List (Entry (Shape n₀') × TShape)}
    (hw : ShapeFun.WFE Δ (Shape.WF Δ) (g₀.map (·.1)))
    (hw' : ShapeFun.WFE Δ (Shape.WF Δ) (g₀'.map (·.1))) :
    ShapeFun.WFE Δ (Shape.WF Δ)
      ((TShape.liftGen (max n₀ n₀') g₀ ++ TShape.liftGen (max n₀ n₀') g₀').map (·.1)) := by
  intro e he
  rw [List.map_append] at he
  have lifted {k} (hk : k ≤ max n₀ n₀') {h : List (Entry (Shape k) × TShape)}
      (hh : ShapeFun.WFE Δ (Shape.WF Δ) (h.map (·.1)))
      (he : e ∈ (TShape.liftGen (max n₀ n₀') h).map (·.1)) :
      Shape.WF Δ e.inp ∧ Shape.WF Δ e.out := by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact ⟨(Shape.lift_wf hk).2 (hh q.1 (List.mem_map.2 ⟨q, hq, rfl⟩)).1,
      (Shape.lift_wf hk).2 (hh q.1 (List.mem_map.2 ⟨q, hq, rfl⟩)).2⟩
  match List.mem_append.1 he with
  | .inl h => exact lifted (Nat.le_max_left ..) hw h
  | .inr h => exact lifted (Nat.le_max_right ..) hw' h

theorem join_gen_cover {Δ : List Term} (hΔ : ⊢ Δ) {n n₀ n₀'}
    {g g' : ShapeFun n} {g₀ : List (Entry (Shape n₀) × TShape)}
    {g₀' : List (Entry (Shape n₀') × TShape)}
    (hw : ShapeFun.WFE Δ (Shape.WF Δ) (g₀.map (·.1)))
    (hw' : ShapeFun.WFE Δ (Shape.WF Δ) (g₀'.map (·.1)))
    (hg : ∀ e ∈ g, TEvaluates Δ (g₀.map (·.1)) e.ty e.tm e.inp.T e.out.T)
    (hg' : ∀ e ∈ g', TEvaluates Δ (g₀'.map (·.1)) e.ty e.tm e.inp.T e.out.T) :
    ∀ e ∈ g ++ g', TEvaluates Δ
      ((TShape.liftGen (max n₀ n₀') g₀ ++ TShape.liftGen (max n₀ n₀') g₀').map (·.1))
      e.ty e.tm e.inp.T e.out.T := by
  intro e he
  rw [List.map_append]
  match List.mem_append.1 he with
  | .inl h =>
    refine TEvaluates.mono_graph (fun d hd => List.mem_append.2 (.inl hd)) ?_
    rw [TShape.liftGen_map]
    exact TEvaluates.lift_graph hΔ (Nat.le_max_left ..) hw (hg e h)
  | .inr h =>
    refine TEvaluates.mono_graph (fun d hd => List.mem_append.2 (.inr hd)) ?_
    rw [TShape.liftGen_map]
    exact TEvaluates.lift_graph hΔ (Nat.le_max_right ..) hw' (hg' e h)

theorem join_gen_code {Δ : List Term} (hΔ : ⊢ Δ) {n' n₀ n₀'} {f : ShapeFun n'}
    {g₀ : List (Entry (Shape n₀) × TShape)} {g₀' : List (Entry (Shape n₀') × TShape)}
    (hw : ShapeFun.WFE Δ (Shape.WF Δ) (g₀.map (·.1)))
    (hw' : ShapeFun.WFE Δ (Shape.WF Δ) (g₀'.map (·.1)))
    (hev : ∀ e ∈ g₀, TEvaluates Δ f e.1.ty e.1.tm e.1.inp.T e.2)
    (hev' : ∀ e ∈ g₀', TEvaluates Δ f e.1.ty e.1.tm e.1.inp.T e.2) :
    ∀ e ∈ TShape.liftGen (max n₀ n₀') g₀ ++ TShape.liftGen (max n₀ n₀') g₀',
      TEvaluates Δ f e.1.ty e.1.tm e.1.inp.T e.2 := by
  intro e he
  have lifted {k} (hk : k ≤ max n₀ n₀') {h : List (Entry (Shape k) × TShape)}
      (hh : ShapeFun.WFE Δ (Shape.WF Δ) (h.map (·.1)))
      (hhev : ∀ e ∈ h, TEvaluates Δ f e.1.ty e.1.tm e.1.inp.T e.2)
      (he : e ∈ TShape.liftGen (max n₀ n₀') h) :
      TEvaluates Δ f e.1.ty e.1.tm e.1.inp.T e.2 := by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    exact TEvaluates.mono_inp hΔ
      (TShape.LE.le_lift hΔ (m := p.1.inp.T) hk (hh p.1 (List.mem_map.2 ⟨p, hp, rfl⟩)).1)
      (hhev p hp)
  match List.mem_append.1 he with
  | .inl h => exact lifted (Nat.le_max_left ..) hw hev h
  | .inr h => exact lifted (Nat.le_max_right ..) hw' hev' h

theorem join_gen_ty {Δ : List Term} (hΔ : ⊢ Δ) {n₀ n₀'}
    {g₀ : List (Entry (Shape n₀) × TShape)} {g₀' : List (Entry (Shape n₀') × TShape)}
    (hty : ∀ e ∈ g₀, TShape.HasType Δ e.1.out.T e.2)
    (hty' : ∀ e ∈ g₀', TShape.HasType Δ e.1.out.T e.2) :
    ∀ e ∈ TShape.liftGen (max n₀ n₀') g₀ ++ TShape.liftGen (max n₀ n₀') g₀',
      TShape.HasType Δ e.1.out.T e.2 := by
  intro e he
  have lifted {k} (hk : k ≤ max n₀ n₀') {h : List (Entry (Shape k) × TShape)}
      (hhty : ∀ e ∈ h, TShape.HasType Δ e.1.out.T e.2)
      (he : e ∈ TShape.liftGen (max n₀ n₀') h) :
      TShape.HasType Δ e.1.out.T e.2 := by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    exact (hhty p hp).lift_subject hΔ hk
  match List.mem_append.1 he with
  | .inl h => exact lifted (Nat.le_max_left ..) hty h
  | .inr h => exact lifted (Nat.le_max_right ..) hty' h

/-- **The join of two compatible subjects at one type, at one level** —
master's `WShape.HasType.join`, and the content of `SoundJoin` (§5.1).

It is provable now that a Σ-value is a first component and a graph
(§5.1b): two pairs join by joining first components and *appending*
graphs, each entry keeping the code it was typed at, exactly as two λs
do.  With the old product pair it was false — §5.5's counterexample — and
that is what made `SoundJoin` an open problem.

The sort-typed shapes go to `join_sort`, numerals to `IsNumeral.join`,
and `lam`/`pair` append their graphs and concatenate their generators,
lifted to a common level. -/
theorem TShape.HasType.join_at {Δ : List Term} (hΔ : ⊢ Δ) :
    ∀ {n} {y z : Shape n} {c : TShape}, Shape.Compat Δ y z →
      TShape.HasType Δ y.T c → TShape.HasType Δ z.T c →
      TShape.HasType Δ (y.join z).T c := by
  intro n
  induction n with
  | zero =>
    intro y z c hc hy hz
    cases y with
    | bot => exact hz
    | sort r => cases z <;> exact hy
  | succ n ih =>
    intro y z c hc hy hz
    cases y with
    | bot => exact hz
    | sort | unit | nat | zero | id =>
      cases z <;> first | exact hy | exact absurd hc (fun x => x)
    | succ v =>
      cases z with
      | bot => exact hy
      | succ v' =>
        cases hy with | succ hv => cases hz with | succ hv' =>
        exact .succ (Shape.IsNumeral.join hc hv hv')
      | _ => exact absurd hc (fun x => x)
    | forallE A B d f =>
      cases hy with | forallE hd hf hw =>
      exact TShape.HasType.join_sort hΔ rfl (.forallE hd hf hw) hz hc
    | sigma A B d f =>
      cases hy with | sigma hd hf hw =>
      exact TShape.HasType.join_sort hΔ rfl (.sigma hd hf hw) hz hc
    | refl w =>
      cases z with
      | bot => exact hy
      | refl w' =>
        cases hy with | refl hw hle hA =>
        cases hz with | refl hw' _ _ =>
        exact .refl (Shape.WF.join hΔ hc hw hw') hle hA
      | _ => exact absurd hc (fun x => x)
    | lam A₀ g =>
      cases z with
      | bot => exact hy
      | lam A₀' g' =>
        cases hy with
        | @lam _ n₀ n' _ _ f A B d g₀ hd hfo hwg hwPi hwg₀ hg hg₀ev hg₀ty hdom =>
          cases hz with
          | @lam _ n₀' _ _ _ _ _ _ _ g₀' _ _ hwg' _ hwg₀' hg' hg₀ev' hg₀ty' hdom' =>
            exact .lam hd hfo (Shape.WF.join hΔ hc hwg hwg') hwPi
              (join_gen_wf hwg₀ hwg₀')
              (join_gen_cover hΔ hwg₀ hwg₀' hg hg')
              (join_gen_code hΔ hwg₀ hwg₀' hg₀ev hg₀ev')
              (join_gen_ty hΔ hg₀ty hg₀ty') hdom
      | _ => exact absurd hc (fun x => x)
    | pair A₀ x g =>
      cases z with
      | bot => exact hy
      | pair A₀' x' g' =>
        cases hy with
        | @pair _ n₀ n' _ _ _ f A B d g₀ hd hfo hwp hwSg hxd hwg₀ hg hg₀ev hg₀ty hdom =>
          cases hz with
          | @pair _ n₀' _ _ _ _ _ _ _ _ g₀' _ _ hwp' _ hxd' hwg₀' hg' hg₀ev' hg₀ty' hdom' =>
            exact .pair hd hfo (Shape.WF.join hΔ hc hwp hwp') hwSg
              (ih hc.2.1 hxd hxd')
              (join_gen_wf hwg₀ hwg₀')
              (join_gen_cover hΔ hwg₀ hwg₀' hg hg')
              (join_gen_code hΔ hwg₀ hwg₀' hg₀ev hg₀ev')
              (join_gen_ty hΔ hg₀ty hg₀ty') hdom
      | _ => exact absurd hc (fun x => x)

/-- The same at the total level: lift both subjects to the common level
and join there. -/
theorem TShape.HasType.join {Δ : List Term} (hΔ : ⊢ Δ) {y z c : TShape}
    (hc : TShape.Compat Δ y z) (hy : TShape.HasType Δ y c) (hz : TShape.HasType Δ z c) :
    TShape.HasType Δ (y.join z) c :=
  TShape.HasType.join_at hΔ
    ((TShape.Compat.def (Nat.le_max_left ..) (Nat.le_max_right ..)).1 hc)
    (hy.lift_subject hΔ (Nat.le_max_left ..)) (hz.lift_subject hΔ (Nat.le_max_right ..))

/-- Everything the `TShape` lookup returns is typed at a sort, when the
graph's outputs are.  `lower` is `mono_l_sort` and `join` is `join_sort'`;
the level-indexed `ShapeFun.Eval.tHasType` had to take both as
hypotheses. -/
theorem TEvaluates.tHasType {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n}
    {A a : Term} {x c : TShape} {j : Bool} (hc : c.2 = Shape.sort j)
    (hty : ∀ e ∈ f, TShape.HasType Δ e.out.T c) :
    ∀ {y : TShape}, TEvaluates Δ f A a x y → TShape.HasType Δ y c := by
  intro y h
  induction h with
  | bot =>
    refine .bot ?_
    show TShape.HasType Δ ⟨c.1, c.2⟩ _
    rw [hc]; exact .sort
  | entry e he _ _ => exact hty e he
  | lower hle _ ih => exact TShape.HasType.mono_l_sort hΔ hc ih hle
  | join hcj _ _ ih₁ ih₂ => exact TShape.HasType.join_sort' hΔ hc ih₁ ih₂ hcj

/-- A lookup in a graph whose outputs are all `⊥` is `⊥`. -/
theorem TEvaluates.eq_bot {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n}
    {A a : Term} {x : TShape} (hf : ∀ e ∈ f, e.out = Shape.bot) :
    ∀ {c : TShape}, TEvaluates Δ f A a x c → c.2 = Shape.bot := by
  intro c h
  induction h with
  | bot => rfl
  | entry e he _ _ => exact hf e he
  | lower hle _ ih => exact TShape.le_bot hΔ ih hle
  | join _ _ _ ih₁ ih₂ => exact TShape.join_eq_bot ih₁ ih₂

/-- **A lookup is `⊥`, or it inherits any property its matching entries'
outputs have.**  `eq_bot` is `Q := False`; the useful instances take `Q` to
be a property of the *query label*, which the `entry` premise's `LabelEq`
transfers from the entry.

The disjunction is what makes the chain of §5.5b compose without a case
split on "is this output `⊥`": each link hands the next one exactly this
shape, and the `⊥` branch is discharged once at the top, by a λ-shape's
non-degeneracy. -/
theorem TEvaluates.bot_or {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n}
    {A a : Term} {x : TShape} {Q : Prop}
    (hf : ∀ e ∈ f, LabelEq Δ e.ty e.tm A a → e.out = Shape.bot ∨ Q) :
    ∀ {c : TShape}, TEvaluates Δ f A a x c → c.2 = Shape.bot ∨ Q := by
  intro c h
  induction h with
  | bot => exact .inl rfl
  | entry e he hl _ => exact hf e he hl
  | lower hle _ ih => exact ih.imp (fun hb => TShape.le_bot hΔ hb hle) (fun h => h)
  | join _ _ _ ih₁ ih₂ =>
    match ih₁, ih₂ with
    | .inl h₁, .inl h₂ => exact .inl (TShape.join_eq_bot h₁ h₂)
    | .inr h, _ => exact .inr h
    | _, .inr h => exact .inr h

/-- A lookup is `⊥` or it matched an entry.  `bot_or` at the tautological
property. -/
theorem TEvaluates.eq_bot_or_entry {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n}
    {A a : Term} {x : TShape} {c : TShape} (h : TEvaluates Δ f A a x c) :
    c.2 = Shape.bot ∨ ∃ e ∈ f, LabelEq Δ e.ty e.tm A a :=
  TEvaluates.bot_or hΔ (fun e he hl => .inr ⟨e, he, hl⟩) h

/-- Nothing but `⊥` is typed at `⊥`.  `refl` is the only clause whose type
is not pinned, and its bound puts an `id` shape below `⊥`. -/
theorem TShape.HasType.bot_r {Δ : List Term} (hΔ : ⊢ Δ) {x a : TShape}
    (ha : a.2 = Shape.bot) (h : TShape.HasType Δ x a) : x.2 = Shape.bot := by
  cases h with
  | bot _ => rfl
  | sort => exact absurd ha Shape.sort_ne_bot
  | unit _ => exact absurd ha Shape.sort_ne_bot
  | nat => exact absurd ha Shape.sort_ne_bot
  | zero => exact absurd ha (fun h => by cases h)
  | succ _ => exact absurd ha (fun h => by cases h)
  | id _ _ => exact absurd ha Shape.sort_ne_bot
  | forallE _ _ _ => exact absurd ha Shape.sort_ne_bot
  | sigma _ _ _ => exact absurd ha Shape.sort_ne_bot
  | lam _ _ _ _ _ _ _ => exact absurd ha (fun h => by cases h)
  | pair _ _ _ _ _ _ _ _ => exact absurd ha (fun h => by cases h)
  | refl _ hc _ => exact absurd (TShape.le_bot hΔ ha hc) (fun h => by cases h)

/-- A sort is typed at `.type` and nothing else, so never at `.prop`.  The
hypothesis form is forced: `Shape.sort` at a variable level is a stuck
`match`, so the subject has to be a variable for `cases` to fire. -/
theorem TShape.HasType.sort_not_prop {Δ : List Term} {a : TShape} {j : Bool}
    (ha : a.2 = Shape.sort j) (h : TShape.HasType Δ a TShape.prop) : False := by
  cases h with
  | bot _ => exact Shape.bot_ne_sort ha
  | unit _ => exact absurd ha (fun h => by cases h)
  | id _ _ => exact absurd ha (fun h => by cases h)
  | forallE _ _ _ => exact absurd ha (fun h => by cases h)
  | refl _ _ _ => exact absurd ha (fun h => by cases h)

/-- **A proposition is inhabited only by `⊥`.**

Master's `HasType.proofIrrel`.  The old level-indexed proof inducted on the
*level*, because everything in sight lived at one; here it is an induction
on the **derivation**, and the `lam` clause's own induction hypothesis —
the one at `hg₀ty`, the codomain generator — is exactly the recursive call
needed.  That is the generator earning its keep a second time: with a
dominating codomain witness there is no such hypothesis to have. -/
theorem TShape.HasType.proofIrrel {Δ : List Term} (hΔ : ⊢ Δ) {x a : TShape}
    (h : TShape.HasType Δ x a) : TShape.HasType Δ a TShape.prop → x.2 = Shape.bot := by
  induction h with
  | bot _ _ => intro _; rfl
  | sort => intro ha; exact absurd ha (TShape.HasType.sort_not_prop rfl)
  | unit _ => intro ha; exact absurd ha (TShape.HasType.sort_not_prop rfl)
  | nat => intro ha; exact absurd ha (TShape.HasType.sort_not_prop rfl)
  | id _ _ => intro ha; exact absurd ha (TShape.HasType.sort_not_prop rfl)
  | forallE _ _ _ _ _ => intro ha; exact absurd ha (TShape.HasType.sort_not_prop rfl)
  | sigma _ _ _ _ _ => intro ha; exact absurd ha (TShape.HasType.sort_not_prop rfl)
  | zero => intro ha; exact absurd ha (fun h => by cases h)
  | succ _ => intro ha; exact absurd ha (fun h => by cases h)
  | pair _ _ _ _ _ _ _ _ _ _ _ _ => intro ha; exact absurd ha (fun h => by cases h)
  | refl _ hc _ _ =>
    intro ha
    cases ha with
    | bot _ => exact absurd (TShape.le_bot hΔ rfl hc) (fun h => by cases h)
    | id hj _ =>
      obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ hc
      cases h2.1
      exact absurd (Bool.eq_true_of_le rfl hj) (fun h => by cases h)
    | unit _ =>
      obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ hc
      exact absurd h2 (fun x => x)
    | forallE _ _ _ =>
      obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ hc
      exact absurd h2 (fun x => x)
    | refl _ _ _ =>
      obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ hc
      exact absurd h2 (fun x => x)
  | @lam n n₀ n' _ g f _ _ d g₀ _ _ hwg _ _ hg hg₀ev _ _ _ _ ihg₀ty =>
    intro ha
    obtain ⟨_, hf, _⟩ := ha.forallE_inv rfl
    -- each generator output is `⊥`: its type is a lookup in a graph whose
    -- own outputs are propositions, so the clause's induction hypothesis
    -- applies to it
    have hbot : ∀ e' ∈ g₀, e'.1.out = Shape.bot := fun e' he' =>
      ihg₀ty e' he' (TEvaluates.tHasType hΔ rfl hf (hg₀ev e' he'))
    have hbot' : ∀ e ∈ g₀.map (·.1), e.out = Shape.bot := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
      exact hbot p hp
    -- so is every output of `g`, and a well-formed λ-shape has none
    cases g with
    | nil => exact absurd rfl hwg.1
    | cons e g' =>
      have hout : e.out = Shape.bot := TEvaluates.eq_bot hΔ hbot' (hg e (.head _))
      exact absurd (show Shape.IsBot e.out by rw [hout]; cases n <;> trivial)
        (hwg.2.1 e (.head _))

/-! ## Hereditarily typed shapes

`Interp.lam` puts an entry's input in the body's slot and `Adm` asks that
a slot be typed; η needs more, and so does the `app` case of `SoundDom`:
that the *inputs of that input* are typed one binder down, and that an
entry's *output* is again hereditarily typed at the codomain it is read
at.  Both are what the original's Π-decoder does — `arrow Q P F = λX. Q
(F (P X))` decodes the argument *and* the result (`Domain/Decoder/
FunctionRetraction.lean`) -- and `x : a ↔ p_a x = x` is its per-point
form.

`Dom` is an **inductive** relation rather than a recursion on the code:
the codomain code an entry's output is read at is a *lookup* in the Π's
graph, so it is not a subterm of the code, and a least fixed point says
what is wanted without a measure.  It is deliberately **not** downward
closed; the form that is, `SoundDom`, is the saturating one. -/

/-- The graph a shape carries, if it carries one: a λ's or a pair's. -/
def Shape.graph {n} : Shape (n+1) → List (Entry (Shape n))
  | .lam _ g => g
  | .pair _ _ g => g
  | _ => []

/-- A shape's entries, levels forgotten. -/
def TShape.entries : TShape → List (Entry TShape)
  | ⟨0, _⟩ => []
  | ⟨_+1, s⟩ => s.graph.map (fun e => ⟨e.ty, e.tm, e.inp.T, e.out.T⟩)

/-- A pair shape's first component, as a one-element list (empty for
everything else), so that `Dom`'s Σ clause can quantify over it. -/
def TShape.fstPart : TShape → List TShape
  | ⟨0, _⟩ => []
  | ⟨_+1, .pair _ x _⟩ => [x.T]
  | ⟨_+1, _⟩ => []

/-- A code that binds: the two whose decoder does more than filter. -/
def TShape.IsBinder : TShape → Prop
  | ⟨0, _⟩ => False
  | ⟨_+1, .forallE ..⟩ => True
  | ⟨_+1, .sigma ..⟩ => True
  | ⟨_+1, _⟩ => False

/-- **Hereditarily typed at a code.**

The codomain codes are a *parameter* (a list of pairs, as in
`HasType.lam`): a premise may not existentially quantify a witness of the
inductive being declared. -/
inductive TShape.Dom (Δ : List Term) : TShape → TShape → Prop where
  /-- At a filtering code, typing is all there is. -/
  | base {d x : TShape} : ¬ d.IsBinder → TShape.HasType Δ x d → Dom Δ d x
  /-- At a Π, the entries' inputs are hereditarily typed at the domain
  and their outputs at the codomain read there. -/
  | pi {n} {A B : Term} {d : Shape n} {f : ShapeFun n} {x : TShape}
      {cs : List (Entry TShape × TShape)} :
    TShape.HasType Δ x (Shape.T (n := n+1) (ShapeS.forallE A B d f)) →
    x.entries = cs.map (·.1) →
    (∀ p ∈ cs, Dom Δ d.T p.1.inp) →
    (∀ p ∈ cs, TEvaluates Δ f p.1.ty p.1.tm p.1.inp p.2) →
    (∀ p ∈ cs, Dom Δ p.2 p.1.out) →
    Dom Δ (Shape.T (n := n+1) (ShapeS.forallE A B d f)) x
  /-- At a Σ, the same, plus the first component. -/
  | sg {n} {A B : Term} {d : Shape n} {f : ShapeFun n} {x : TShape}
      {cs : List (Entry TShape × TShape)} :
    TShape.HasType Δ x (Shape.T (n := n+1) (ShapeS.sigma A B d f)) →
    x.entries = cs.map (·.1) →
    (∀ y ∈ x.fstPart, Dom Δ d.T y) →
    (∀ p ∈ cs, Dom Δ d.T p.1.inp) →
    (∀ p ∈ cs, TEvaluates Δ f p.1.ty p.1.tm p.1.inp p.2) →
    (∀ p ∈ cs, Dom Δ p.2 p.1.out) →
    Dom Δ (Shape.T (n := n+1) (ShapeS.sigma A B d f)) x

theorem TShape.Dom.hasType {Δ : List Term} {d x : TShape} (h : TShape.Dom Δ d x) :
    TShape.HasType Δ x d := by cases h <;> assumption

@[simp] theorem TShape.entries_bot {n} : (Shape.T (n := n) Shape.bot).entries = [] := by
  cases n <;> rfl

@[simp] theorem TShape.fstPart_bot {n} : (Shape.T (n := n) Shape.bot).fstPart = [] := by
  cases n <;> rfl

/-- `⊥` is hereditarily typed wherever it is typed: it carries nothing. -/
theorem TShape.Dom.bot {Δ : List Term} {d : TShape} {n}
    (h : TShape.HasType Δ (Shape.T (n := n) .bot) d) :
    TShape.Dom Δ d (Shape.T (n := n) .bot) := by
  obtain ⟨m, c⟩ := d
  cases m with
  | zero => exact .base (fun h => h) h
  | succ m =>
    match c with
    | .forallE .. =>
      exact .pi (cs := []) h (by simp) (by simp) (by simp) (by simp)
    | .sigma .. =>
      exact .sg (cs := []) h (by simp) (by simp) (by simp) (by simp) (by simp)
    | .bot | .sort _ | .unit _ | .nat | .zero | .succ _ | .refl _ | .id _ _ _ _
    | .lam _ _ | .pair _ _ _ => exact .base (fun h => h) h

/-- The same, for a subject that is `⊥` only up to its level. -/
theorem TShape.Dom.bot_subject {Δ : List Term} {d x : TShape} (hx : x.2 = Shape.bot)
    (h : TShape.HasType Δ x d) : TShape.Dom Δ d x := by
  obtain ⟨n, s⟩ := x
  cases n with
  | zero => cases s with
    | bot => exact TShape.Dom.bot h
    | sort r => exact absurd hx (by simp [Shape.bot, Shape.sort])
  | succ n =>
    cases s <;> first
      | exact TShape.Dom.bot (n := n+1) h
      | exact absurd hx (by simp [Shape.bot])

@[simp] theorem TShape.entries_subst {x : TShape} {τ : Subst} :
    (x.subst τ).entries = x.entries.map
      (fun e => ⟨e.ty.subst τ, e.tm.subst τ, e.inp.subst τ, e.out.subst τ⟩) := by
  obtain ⟨n, s⟩ := x
  cases n with
  | zero => cases s <;> rfl
  | succ n =>
    cases s <;>
      simp [TShape.entries, TShape.subst, Shape.graph, Shape.subst, ShapeFun.subst,
        List.map_map, Function.comp_def, Shape.T]

@[simp] theorem TShape.fstPart_subst {x : TShape} {τ : Subst} :
    (x.subst τ).fstPart = x.fstPart.map (·.subst τ) := by
  obtain ⟨n, s⟩ := x
  cases n with
  | zero => cases s <;> rfl
  | succ n =>
    cases s <;>
      simp [TShape.fstPart, TShape.subst, Shape.subst, Shape.T]

theorem TShape.IsBinder.subst {d : TShape} {τ : Subst} (h : ¬ d.IsBinder) :
    ¬ (d.subst τ).IsBinder := by
  obtain ⟨n, c⟩ := d
  cases n with
  | zero => cases c <;> exact h
  | succ n => cases c <;> first | exact h | exact fun x => x

/-- `Dom` transports along a typed substitution, like `HasType`. -/
theorem TShape.Dom.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {d x : TShape} (h : TShape.Dom Δ d x) :
    TShape.Dom Θ (d.subst τ) (x.subst τ) := by
  induction h with
  | base hnb hty => exact .base (TShape.IsBinder.subst hnb) (TShape.HasType.subst hΘ W hty)
  | @pi n A B d f x cs hty hent _ hev _ ihin ihout =>
    refine .pi (cs := cs.map fun p =>
        (⟨p.1.ty.subst τ, p.1.tm.subst τ, p.1.inp.subst τ, p.1.out.subst τ⟩, p.2.subst τ))
      (by simpa [Shape.subst] using TShape.HasType.subst hΘ W hty) ?_ ?_ ?_ ?_
    · simp [TShape.entries_subst, hent, List.map_map, Function.comp_def]
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact ihin q hq
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact TEvaluates.subst hΘ W (hev q hq)
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact ihout q hq
  | @sg n A B d f x cs hty hent _ _ hev _ ihfst ihin ihout =>
    refine .sg (cs := cs.map fun p =>
        (⟨p.1.ty.subst τ, p.1.tm.subst τ, p.1.inp.subst τ, p.1.out.subst τ⟩, p.2.subst τ))
      (by simpa [Shape.subst] using TShape.HasType.subst hΘ W hty) ?_ ?_ ?_ ?_ ?_
    · simp [TShape.entries_subst, hent, List.map_map, Function.comp_def]
    · intro y hy
      rw [TShape.fstPart_subst, List.mem_map] at hy
      obtain ⟨y₀, hy₀, rfl⟩ := hy
      exact ihfst y₀ hy₀
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact ihin q hq
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact TEvaluates.subst hΘ W (hev q hq)
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact ihout q hq

theorem TShape.entries_lift {x : TShape} {k} (hk : x.1 ≤ k + 1) :
    (x.lift (k+1)).entries = x.entries.map
      (fun e => ⟨e.ty, e.tm, e.inp.lift k, e.out.lift k⟩) := by
  obtain ⟨n, s⟩ := x
  cases n with
  | zero => cases s <;> rfl
  | succ n =>
    cases s <;>
      simp [TShape.entries, TShape.lift, Shape.graph, Shape.lift, ShapeFun.lift,
        List.map_map, Function.comp_def, Shape.T]

theorem TShape.fstPart_lift {x : TShape} {k} (hk : x.1 ≤ k + 1) :
    (x.lift (k+1)).fstPart = x.fstPart.map (·.lift k) := by
  obtain ⟨n, s⟩ := x
  cases n with
  | zero => cases s <;> rfl
  | succ n => cases s <;> simp [TShape.fstPart, TShape.lift, Shape.lift, Shape.T]

theorem TShape.entries_level {x : TShape} {e : Entry TShape} (he : e ∈ x.entries) :
    e.inp.1 + 1 = x.1 ∧ e.out.1 + 1 = x.1 := by
  obtain ⟨n, s⟩ := x
  cases n with
  | zero => simp [TShape.entries] at he
  | succ n =>
    simp only [TShape.entries, List.mem_map] at he
    obtain ⟨e₀, _, rfl⟩ := he
    exact ⟨rfl, rfl⟩

theorem TShape.fstPart_level {x : TShape} {y : TShape} (hy : y ∈ x.fstPart) :
    y.1 + 1 = x.1 := by
  obtain ⟨n, s⟩ := x
  cases n with
  | zero => simp [TShape.fstPart] at hy
  | succ n =>
    match s, hy with
    | .pair _ _ _, hy => simp [TShape.fstPart] at hy; subst hy; rfl

/-- `Dom` survives lifting the subject: its entries lift with it, one
level down, and a lifted query reads the same codes. -/
theorem TShape.Dom.lift_subject {Δ : List Term} (hΔ : ⊢ Δ) {d x : TShape}
    (h : TShape.Dom Δ d x) : ∀ {k}, x.1 ≤ k → TShape.Dom Δ d (x.lift k) := by
  induction h with
  | base hnb hty => exact fun hk => .base hnb (hty.lift_subject hΔ hk)
  | @pi n A B d f x cs hty hent hin hev hout ihin ihout =>
    intro k hk
    match k, hk with
    | 0, hk =>
      exact .pi (cs := []) (hty.lift_subject hΔ hk) rfl (by simp) (by simp) (by simp)
    | k+1, hk =>
      refine .pi (cs := cs.map fun p =>
          (⟨p.1.ty, p.1.tm, p.1.inp.lift k, p.1.out.lift k⟩, p.2))
        (hty.lift_subject hΔ hk) ?_ ?_ ?_ ?_
      · simp [TShape.entries_lift hk, hent, List.map_map, Function.comp_def]
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        refine ihin q hq ?_
        have := TShape.entries_level (x := x) (e := q.1) (by rw [hent]; exact List.mem_map_of_mem hq)
        omega
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        refine TEvaluates.mono_inp hΔ ?_ (hev q hq)
        exact TShape.LE.le_lift hΔ (by
          have := TShape.entries_level (x := x) (e := q.1) (by rw [hent]; exact List.mem_map_of_mem hq)
          omega) (TShape.Dom.hasType (hin q hq)).wf.1
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        refine ihout q hq ?_
        have := TShape.entries_level (x := x) (e := q.1) (by rw [hent]; exact List.mem_map_of_mem hq)
        omega
  | @sg n A B d f x cs hty hent hfst hin hev hout ihfst ihin ihout =>
    intro k hk
    match k, hk with
    | 0, hk =>
      exact .sg (cs := []) (hty.lift_subject hΔ hk) rfl
        (fun y hy => absurd hy (by simp [TShape.fstPart, TShape.lift]))
        (by simp) (by simp) (by simp)
    | k+1, hk =>
      refine .sg (cs := cs.map fun p =>
          (⟨p.1.ty, p.1.tm, p.1.inp.lift k, p.1.out.lift k⟩, p.2))
        (hty.lift_subject hΔ hk) ?_ ?_ ?_ ?_ ?_
      · simp [TShape.entries_lift hk, hent, List.map_map, Function.comp_def]
      · intro y hy
        rw [TShape.fstPart_lift hk, List.mem_map] at hy
        obtain ⟨y₀, hy₀, rfl⟩ := hy
        refine ihfst y₀ hy₀ ?_
        have := TShape.fstPart_level hy₀
        omega
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        refine ihin q hq ?_
        have := TShape.entries_level (x := x) (e := q.1) (by rw [hent]; exact List.mem_map_of_mem hq)
        omega
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        refine TEvaluates.mono_inp hΔ ?_ (hev q hq)
        exact TShape.LE.le_lift hΔ (by
          have := TShape.entries_level (x := x) (e := q.1) (by rw [hent]; exact List.mem_map_of_mem hq)
          omega) (TShape.Dom.hasType (hin q hq)).wf.1
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        refine ihout q hq ?_
        have := TShape.entries_level (x := x) (e := q.1) (by rw [hent]; exact List.mem_map_of_mem hq)
        omega

/-- A code below a binder code is a binder code, or `⊥`: the order pins
the head.  This is what lets `Dom`'s `base` clause stay disjoint from the
other two under `mono_r`. -/
theorem TShape.IsBinder.of_le {Δ : List Term} (hΔ : ⊢ Δ) {d d' : TShape}
    (hle : TShape.LE Δ d d') (hb : d'.IsBinder) (hnb : d.2 ≠ Shape.bot) : d.IsBinder := by
  obtain ⟨n, s⟩ := d
  obtain ⟨k, s'⟩ := d'
  cases k with
  | zero => cases s' <;> exact absurd hb (fun x => x)
  | succ k =>
    obtain ⟨M, hkM, hnM, h2⟩ := TShape.LE.at_succ hle
    cases n with
    | zero =>
      cases s with
      | bot => exact absurd rfl hnb
      | sort r =>
        match s' with
        | .forallE .. | .sigma .. => exact absurd h2 (fun x => x)
        | .bot | .sort _ | .unit _ | .nat | .zero | .succ _ | .refl _ | .id _ _ _ _
        | .lam _ _ | .pair _ _ _ => exact absurd hb (fun x => x)
    | succ n =>
      match s, s' with
      | .forallE .., .forallE .. => exact trivial
      | .sigma .., .sigma .. => exact trivial
      | .bot, _ => exact absurd rfl hnb
      | .sort _, .forallE .. | .sort _, .sigma ..
      | .unit _, .forallE .. | .unit _, .sigma ..
      | .nat, .forallE .. | .nat, .sigma ..
      | .zero, .forallE .. | .zero, .sigma ..
      | .succ _, .forallE .. | .succ _, .sigma ..
      | .refl _, .forallE .. | .refl _, .sigma ..
      | .id .., .forallE .. | .id .., .sigma ..
      | .lam .., .forallE .. | .lam .., .sigma ..
      | .pair .., .forallE .. | .pair .., .sigma ..
      | .forallE .., .sigma .. | .sigma .., .forallE .. => exact absurd h2 (fun x => x)
      | _, .bot | _, .sort _ | _, .unit _ | _, .nat | _, .zero | _, .succ _
      | _, .refl _ | _, .id .. | _, .lam .. | _, .pair .. => exact absurd hb (fun x => x)

/-- **`Dom` grows with the code.**  The Π and Σ orders are covariant in
the domain, so the hereditary conditions move up with them; where the
head changes the smaller code is `⊥`, and then the subject is too. -/
theorem TShape.Dom.mono_r {Δ : List Term} (hΔ : ⊢ Δ) {d x : TShape}
    (h : TShape.Dom Δ d x) : ∀ {d' : TShape}, TShape.LE Δ d d' →
      TShape.HasType Δ d' TShape.type → TShape.Dom Δ d' x := by
  induction h with
  | @base d x hnb hty0 =>
    intro d' hle hty
    by_cases hb : d.2 = Shape.bot
    · exact TShape.Dom.bot_subject (TShape.HasType.bot_r hΔ hb hty0)
        (TShape.HasType.mono_r hΔ hty0 _ hle hty)
    · exact .base (fun hbind => hnb (TShape.IsBinder.of_le hΔ hle hbind hb))
        (TShape.HasType.mono_r hΔ hty0 _ hle hty)
  | @pi n A B d f x cs hty0 hent hin hev hout ihin ihout =>
    intro d' hle hty
    obtain ⟨k, s⟩ := d'
    obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ hle
    cases k with
    | zero => cases s <;> exact absurd h2 (fun x => x)
    | succ k =>
      match s with
      | .forallE A' B' d₂ f₂ =>
        obtain ⟨hd₂, hf₂, hw₂⟩ := hty.forallE_inv rfl
        have hdle := TShape.LE.forallE_dom hΔ hle
        refine .pi (cs := cs) (TShape.HasType.mono_r hΔ hty0 _ hle hty) hent
          (fun p hp => ihin p hp hdle hd₂) ?_ (fun p hp => hout p hp)
        · -- the codes are lookups in the bigger graph
          intro p hp
          obtain ⟨_, _, hcov⟩ := TShape.LE.forallE_decomp hΔ hle
            (TShape.HasType.wf hty0).2 hw₂ (fun e he => TEvaluates.refl hw₂.2.2.2 e he)
          exact TEvaluates.trans hΔ hcov (hev p hp)
      | .bot | .sort _ | .unit _ | .nat | .zero | .succ _ | .refl _ | .id _ _ _ _
      | .lam _ _ | .sigma .. | .pair _ _ _ => exact absurd h2 (fun x => x)
  | @sg n A B d f x cs hty0 hent hfst hin hev hout ihfst ihin ihout =>
    intro d' hle hty
    obtain ⟨k, s⟩ := d'
    obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ hle
    cases k with
    | zero => cases s <;> exact absurd h2 (fun x => x)
    | succ k =>
      match s with
      | .sigma A' B' d₂ f₂ =>
        obtain ⟨hd₂, hf₂, hw₂⟩ := hty.sigma_inv rfl
        have hdle := TShape.LE.sigma_dom hΔ hle
        refine .sg (cs := cs) (TShape.HasType.mono_r hΔ hty0 _ hle hty) hent
          (fun y hy => ihfst y hy hdle hd₂) (fun p hp => ihin p hp hdle hd₂) ?_
          (fun p hp => hout p hp)
        · intro p hp
          obtain ⟨_, _, hcov⟩ := TShape.LE.sigma_decomp hΔ hle
            (TShape.HasType.wf hty0).2 hw₂ (fun e he => TEvaluates.refl hw₂.2.2.2 e he)
          exact TEvaluates.trans hΔ hcov (hev p hp)
      | .bot | .sort _ | .unit _ | .nat | .zero | .succ _ | .refl _ | .id _ _ _ _
      | .lam _ _ | .forallE .. | .pair _ _ _ => exact absurd h2 (fun x => x)

/-- At a code that only filters — anything but a Π or a Σ — typing is
`Dom`. -/
theorem TShape.Dom.of_not_binder {Δ : List Term} {d x : TShape} (hnb : ¬ d.IsBinder)
    (h : TShape.HasType Δ x d) : TShape.Dom Δ d x := .base hnb h

theorem Shape.graph_join {n} : ∀ {x y : Shape (n+1)},
    (x.join y).graph = x.graph ++ y.graph ∨ (x.join y).graph = x.graph ∨
      (x.join y).graph = y.graph
  | .bot, .bot => .inr (.inr rfl)
  | .bot, .sort _ => .inr (.inr rfl)
  | .bot, .unit _ => .inr (.inr rfl)
  | .bot, .forallE _ _ _ _ => .inr (.inr rfl)
  | .bot, .lam _ _ => .inr (.inr rfl)
  | .bot, .sigma _ _ _ _ => .inr (.inr rfl)
  | .bot, .pair _ _ _ => .inr (.inr rfl)
  | .bot, .nat => .inr (.inr rfl)
  | .bot, .zero => .inr (.inr rfl)
  | .bot, .succ _ => .inr (.inr rfl)
  | .bot, .id _ _ _ _ => .inr (.inr rfl)
  | .bot, .refl _ => .inr (.inr rfl)
  | .sort _, .bot => .inr (.inl rfl)
  | .sort _, .sort _ => .inr (.inl rfl)
  | .sort _, .unit _ => .inr (.inl rfl)
  | .sort _, .forallE _ _ _ _ => .inr (.inl rfl)
  | .sort _, .lam _ _ => .inr (.inl rfl)
  | .sort _, .sigma _ _ _ _ => .inr (.inl rfl)
  | .sort _, .pair _ _ _ => .inr (.inl rfl)
  | .sort _, .nat => .inr (.inl rfl)
  | .sort _, .zero => .inr (.inl rfl)
  | .sort _, .succ _ => .inr (.inl rfl)
  | .sort _, .id _ _ _ _ => .inr (.inl rfl)
  | .sort _, .refl _ => .inr (.inl rfl)
  | .unit _, .bot => .inr (.inl rfl)
  | .unit _, .sort _ => .inr (.inl rfl)
  | .unit _, .unit _ => .inr (.inl rfl)
  | .unit _, .forallE _ _ _ _ => .inr (.inl rfl)
  | .unit _, .lam _ _ => .inr (.inl rfl)
  | .unit _, .sigma _ _ _ _ => .inr (.inl rfl)
  | .unit _, .pair _ _ _ => .inr (.inl rfl)
  | .unit _, .nat => .inr (.inl rfl)
  | .unit _, .zero => .inr (.inl rfl)
  | .unit _, .succ _ => .inr (.inl rfl)
  | .unit _, .id _ _ _ _ => .inr (.inl rfl)
  | .unit _, .refl _ => .inr (.inl rfl)
  | .forallE _ _ _ _, .bot => .inr (.inl rfl)
  | .forallE _ _ _ _, .sort _ => .inr (.inl rfl)
  | .forallE _ _ _ _, .unit _ => .inr (.inl rfl)
  | .forallE _ _ _ _, .forallE _ _ _ _ => .inr (.inl rfl)
  | .forallE _ _ _ _, .lam _ _ => .inr (.inl rfl)
  | .forallE _ _ _ _, .sigma _ _ _ _ => .inr (.inl rfl)
  | .forallE _ _ _ _, .pair _ _ _ => .inr (.inl rfl)
  | .forallE _ _ _ _, .nat => .inr (.inl rfl)
  | .forallE _ _ _ _, .zero => .inr (.inl rfl)
  | .forallE _ _ _ _, .succ _ => .inr (.inl rfl)
  | .forallE _ _ _ _, .id _ _ _ _ => .inr (.inl rfl)
  | .forallE _ _ _ _, .refl _ => .inr (.inl rfl)
  | .lam _ _, .bot => .inr (.inl rfl)
  | .lam _ _, .sort _ => .inr (.inl rfl)
  | .lam _ _, .unit _ => .inr (.inl rfl)
  | .lam _ _, .forallE _ _ _ _ => .inr (.inl rfl)
  | .lam _ _, .lam _ _ => .inl rfl
  | .lam _ _, .sigma _ _ _ _ => .inr (.inl rfl)
  | .lam _ _, .pair _ _ _ => .inr (.inl rfl)
  | .lam _ _, .nat => .inr (.inl rfl)
  | .lam _ _, .zero => .inr (.inl rfl)
  | .lam _ _, .succ _ => .inr (.inl rfl)
  | .lam _ _, .id _ _ _ _ => .inr (.inl rfl)
  | .lam _ _, .refl _ => .inr (.inl rfl)
  | .sigma _ _ _ _, .bot => .inr (.inl rfl)
  | .sigma _ _ _ _, .sort _ => .inr (.inl rfl)
  | .sigma _ _ _ _, .unit _ => .inr (.inl rfl)
  | .sigma _ _ _ _, .forallE _ _ _ _ => .inr (.inl rfl)
  | .sigma _ _ _ _, .lam _ _ => .inr (.inl rfl)
  | .sigma _ _ _ _, .sigma _ _ _ _ => .inr (.inl rfl)
  | .sigma _ _ _ _, .pair _ _ _ => .inr (.inl rfl)
  | .sigma _ _ _ _, .nat => .inr (.inl rfl)
  | .sigma _ _ _ _, .zero => .inr (.inl rfl)
  | .sigma _ _ _ _, .succ _ => .inr (.inl rfl)
  | .sigma _ _ _ _, .id _ _ _ _ => .inr (.inl rfl)
  | .sigma _ _ _ _, .refl _ => .inr (.inl rfl)
  | .pair _ _ _, .bot => .inr (.inl rfl)
  | .pair _ _ _, .sort _ => .inr (.inl rfl)
  | .pair _ _ _, .unit _ => .inr (.inl rfl)
  | .pair _ _ _, .forallE _ _ _ _ => .inr (.inl rfl)
  | .pair _ _ _, .lam _ _ => .inr (.inl rfl)
  | .pair _ _ _, .sigma _ _ _ _ => .inr (.inl rfl)
  | .pair _ _ _, .pair _ _ _ => .inl rfl
  | .pair _ _ _, .nat => .inr (.inl rfl)
  | .pair _ _ _, .zero => .inr (.inl rfl)
  | .pair _ _ _, .succ _ => .inr (.inl rfl)
  | .pair _ _ _, .id _ _ _ _ => .inr (.inl rfl)
  | .pair _ _ _, .refl _ => .inr (.inl rfl)
  | .nat, .bot => .inr (.inl rfl)
  | .nat, .sort _ => .inr (.inl rfl)
  | .nat, .unit _ => .inr (.inl rfl)
  | .nat, .forallE _ _ _ _ => .inr (.inl rfl)
  | .nat, .lam _ _ => .inr (.inl rfl)
  | .nat, .sigma _ _ _ _ => .inr (.inl rfl)
  | .nat, .pair _ _ _ => .inr (.inl rfl)
  | .nat, .nat => .inr (.inl rfl)
  | .nat, .zero => .inr (.inl rfl)
  | .nat, .succ _ => .inr (.inl rfl)
  | .nat, .id _ _ _ _ => .inr (.inl rfl)
  | .nat, .refl _ => .inr (.inl rfl)
  | .zero, .bot => .inr (.inl rfl)
  | .zero, .sort _ => .inr (.inl rfl)
  | .zero, .unit _ => .inr (.inl rfl)
  | .zero, .forallE _ _ _ _ => .inr (.inl rfl)
  | .zero, .lam _ _ => .inr (.inl rfl)
  | .zero, .sigma _ _ _ _ => .inr (.inl rfl)
  | .zero, .pair _ _ _ => .inr (.inl rfl)
  | .zero, .nat => .inr (.inl rfl)
  | .zero, .zero => .inr (.inl rfl)
  | .zero, .succ _ => .inr (.inl rfl)
  | .zero, .id _ _ _ _ => .inr (.inl rfl)
  | .zero, .refl _ => .inr (.inl rfl)
  | .succ _, .bot => .inr (.inl rfl)
  | .succ _, .sort _ => .inr (.inl rfl)
  | .succ _, .unit _ => .inr (.inl rfl)
  | .succ _, .forallE _ _ _ _ => .inr (.inl rfl)
  | .succ _, .lam _ _ => .inr (.inl rfl)
  | .succ _, .sigma _ _ _ _ => .inr (.inl rfl)
  | .succ _, .pair _ _ _ => .inr (.inl rfl)
  | .succ _, .nat => .inr (.inl rfl)
  | .succ _, .zero => .inr (.inl rfl)
  | .succ _, .succ _ => .inr (.inl rfl)
  | .succ _, .id _ _ _ _ => .inr (.inl rfl)
  | .succ _, .refl _ => .inr (.inl rfl)
  | .id _ _ _ _, .bot => .inr (.inl rfl)
  | .id _ _ _ _, .sort _ => .inr (.inl rfl)
  | .id _ _ _ _, .unit _ => .inr (.inl rfl)
  | .id _ _ _ _, .forallE _ _ _ _ => .inr (.inl rfl)
  | .id _ _ _ _, .lam _ _ => .inr (.inl rfl)
  | .id _ _ _ _, .sigma _ _ _ _ => .inr (.inl rfl)
  | .id _ _ _ _, .pair _ _ _ => .inr (.inl rfl)
  | .id _ _ _ _, .nat => .inr (.inl rfl)
  | .id _ _ _ _, .zero => .inr (.inl rfl)
  | .id _ _ _ _, .succ _ => .inr (.inl rfl)
  | .id _ _ _ _, .id _ _ _ _ => .inr (.inl rfl)
  | .id _ _ _ _, .refl _ => .inr (.inl rfl)
  | .refl _, .bot => .inr (.inl rfl)
  | .refl _, .sort _ => .inr (.inl rfl)
  | .refl _, .unit _ => .inr (.inl rfl)
  | .refl _, .forallE _ _ _ _ => .inr (.inl rfl)
  | .refl _, .lam _ _ => .inr (.inl rfl)
  | .refl _, .sigma _ _ _ _ => .inr (.inl rfl)
  | .refl _, .pair _ _ _ => .inr (.inl rfl)
  | .refl _, .nat => .inr (.inl rfl)
  | .refl _, .zero => .inr (.inl rfl)
  | .refl _, .succ _ => .inr (.inl rfl)
  | .refl _, .id _ _ _ _ => .inr (.inl rfl)
  | .refl _, .refl _ => .inr (.inl rfl)

theorem TShape.mem_entries_join {n} {x y : Shape (n+1)} {e : Entry TShape}
    (he : e ∈ (Shape.T (x.join y)).entries) :
    e ∈ (Shape.T x).entries ∨ e ∈ (Shape.T y).entries := by
  simp only [TShape.entries, List.mem_map] at he ⊢
  obtain ⟨e₀, he₀, rfl⟩ := he
  rcases Shape.graph_join (x := x) (y := y) with h | h | h <;> rw [h] at he₀
  · rcases List.mem_append.1 he₀ with h' | h'
    · exact .inl ⟨e₀, h', rfl⟩
    · exact .inr ⟨e₀, h', rfl⟩
  · exact .inl ⟨e₀, he₀, rfl⟩
  · exact .inr ⟨e₀, he₀, rfl⟩

theorem TShape.entries_join {n} {x y : Shape (n+1)} :
    (Shape.T (x.join y)).entries = (Shape.T x).entries ++ (Shape.T y).entries ∨
      (Shape.T (x.join y)).entries = (Shape.T x).entries ∨
      (Shape.T (x.join y)).entries = (Shape.T y).entries := by
  rcases Shape.graph_join (x := x) (y := y) with h | h | h <;>
    simp [TShape.entries, h]

theorem TShape.fstPart_join {n} {x y : Shape (n+1)} :
    (Shape.T (x.join y)).fstPart = (Shape.T x).fstPart ∨
      (Shape.T (x.join y)).fstPart = (Shape.T y).fstPart ∨
      ∃ x₀ y₀ : Shape n, (Shape.T x).fstPart = [Shape.T x₀] ∧
        (Shape.T y).fstPart = [Shape.T y₀] ∧
        (Shape.T (x.join y)).fstPart = [Shape.T (x₀.join y₀)] := by
  match x, y with
  | .bot, y => exact .inr (.inl (by cases y <;> rfl))
  | .pair _ x₀ _, .pair _ y₀ _ => exact .inr (.inr ⟨x₀, y₀, rfl, rfl, rfl⟩)
  | .sort _, y | .unit _, y | .nat, y | .zero, y | .succ _, y | .refl _, y
  | .id .., y | .forallE .., y | .sigma .., y | .lam _ _, y =>
    exact .inl (by cases y <;> rfl)
  | .pair _ x₀ _, .sort _ | .pair _ x₀ _, .unit _ | .pair _ x₀ _, .nat
  | .pair _ x₀ _, .zero | .pair _ x₀ _, .succ _ | .pair _ x₀ _, .refl _
  | .pair _ x₀ _, .id .. | .pair _ x₀ _, .forallE .. | .pair _ x₀ _, .sigma ..
  | .pair _ x₀ _, .lam _ _ | .pair _ x₀ _, .bot => exact .inl rfl

/-- Two compatible shapes with first components have compatible ones. -/
theorem Shape.Compat.fst_of {Δ : List Term} {n} {y z : Shape (n+1)}
    (hc : Shape.Compat Δ y z) {y₀ z₀ : Shape n}
    (hy : (Shape.T y).fstPart = [Shape.T y₀]) (hz : (Shape.T z).fstPart = [Shape.T z₀]) :
    Shape.Compat Δ y₀ z₀ := by
  match y, z with
  | .pair _ y₁ _, .pair _ z₁ _ =>
    have h1 : y₁ = y₀ := by
      have h := hy
      simp only [TShape.fstPart, Shape.T, List.cons.injEq, and_true] at h
      exact eq_of_heq (Sigma.mk.inj h).2
    have h2 : z₁ = z₀ := by
      have h := hz
      simp only [TShape.fstPart, Shape.T, List.cons.injEq, and_true] at h
      exact eq_of_heq (Sigma.mk.inj h).2
    subst h1; subst h2; exact hc.2.1
  | .pair .., .bot | .pair .., .sort _ | .pair .., .unit _ | .pair .., .nat
  | .pair .., .zero | .pair .., .succ _ | .pair .., .refl _ | .pair .., .id ..
  | .pair .., .forallE .. | .pair .., .sigma .. | .pair .., .lam _ _ =>
    exact absurd hz (by simp [TShape.fstPart])
  | .bot, _ | .sort _, _ | .unit _, _ | .nat, _ | .zero, _ | .succ _, _ | .refl _, _
  | .id .., _ | .forallE .., _ | .sigma .., _ | .lam _ _, _ =>
    exact absurd hy (by simp [TShape.fstPart])

/-- **`Dom` is closed under the join**, at one level: the joined graph's
entries are the two graphs' entries, so the generators concatenate.  This
is what lets a slot grow — `dir`'s upper bound dominates the join, and
`Interp` is downward closed, so the join is an approximant too. -/
theorem TShape.Dom.join_at {Δ : List Term} (hΔ : ⊢ Δ) :
    ∀ {n} {y z : Shape n} {d : TShape}, Shape.Compat Δ y z →
      TShape.Dom Δ d y.T → TShape.Dom Δ d z.T → TShape.Dom Δ d (y.join z).T := by
  intro n
  induction n with
  | zero =>
    intro y z d hc hy hz
    cases y with
    | bot => exact hz
    | sort r => cases z <;> exact hy
  | succ n ih =>
    intro y z d hc hy hz
    have hty : TShape.HasType Δ (y.join z).T d :=
      TShape.HasType.join_at hΔ hc hy.hasType hz.hasType
    cases hy with
    | base hnb _ => exact .base hnb hty
    | @pi _ A B d₀ f _ csy htyy henty hiny hevy houty =>
      cases hz with
      | base hnb _ => exact absurd trivial hnb
      | @pi _ _ _ _ _ _ csz htyz hentz hinz hevz houtz =>
        rcases TShape.entries_join (x := y) (y := z) with he | he | he
        · exact .pi (cs := csy ++ csz) hty (by rw [he, henty, hentz, List.map_append])
            (by intro p hp; rcases List.mem_append.1 hp with hp | hp
                exacts [hiny p hp, hinz p hp])
            (by intro p hp; rcases List.mem_append.1 hp with hp | hp
                exacts [hevy p hp, hevz p hp])
            (by intro p hp; rcases List.mem_append.1 hp with hp | hp
                exacts [houty p hp, houtz p hp])
        · exact .pi (cs := csy) hty (by rw [he, henty]) hiny hevy houty
        · exact .pi (cs := csz) hty (by rw [he, hentz]) hinz hevz houtz
    | @sg _ A B d₀ f _ csy htyy henty hfsty hiny hevy houty =>
      cases hz with
      | base hnb _ => exact absurd trivial hnb
      | @sg _ _ _ _ _ _ csz htyz hentz hfstz hinz hevz houtz =>
        have hfst : ∀ w ∈ (Shape.T (y.join z)).fstPart, TShape.Dom Δ d₀.T w := by
          rcases TShape.fstPart_join (x := y) (y := z) with hf | hf | ⟨y₀, z₀, hfy, hfz, hf⟩
          · rw [hf]; exact hfsty
          · rw [hf]; exact hfstz
          · rw [hf]
            intro w hw
            rw [List.mem_singleton] at hw
            subst hw
            exact ih (Shape.Compat.fst_of hc hfy hfz)
              (hfsty _ (by rw [hfy]; exact List.mem_singleton_self _))
              (hfstz _ (by rw [hfz]; exact List.mem_singleton_self _))
        rcases TShape.entries_join (x := y) (y := z) with he | he | he
        · exact .sg (cs := csy ++ csz) hty (by rw [he, henty, hentz, List.map_append]) hfst
            (by intro p hp; rcases List.mem_append.1 hp with hp | hp
                exacts [hiny p hp, hinz p hp])
            (by intro p hp; rcases List.mem_append.1 hp with hp | hp
                exacts [hevy p hp, hevz p hp])
            (by intro p hp; rcases List.mem_append.1 hp with hp | hp
                exacts [houty p hp, houtz p hp])
        · exact .sg (cs := csy) hty (by rw [he, henty]) hfst hiny hevy houty
        · exact .sg (cs := csz) hty (by rw [he, hentz]) hfst hinz hevz houtz

/-- The join, with the two sides at their own levels. -/
theorem TShape.Dom.join {Δ : List Term} (hΔ : ⊢ Δ) {y z d : TShape}
    (hc : TShape.Compat Δ y z) (hy : TShape.Dom Δ d y) (hz : TShape.Dom Δ d z) :
    TShape.Dom Δ d (y.join z) :=
  TShape.Dom.join_at hΔ
    ((TShape.Compat.def (Nat.le_max_left ..) (Nat.le_max_right ..)).1 hc)
    (hy.lift_subject hΔ (Nat.le_max_left ..)) (hz.lift_subject hΔ (Nat.le_max_right ..))

/-- Nothing below a non-binder code binds: the order pins the head. -/
theorem TShape.not_binder_of_le {Δ : List Term} {a c : TShape} (h : TShape.LE Δ a c)
    (hc : ¬ c.IsBinder) : ¬ a.IsBinder := by
  intro hb
  obtain ⟨n, s⟩ := a
  obtain ⟨k, s'⟩ := c
  cases n with
  | zero => cases s <;> exact hb
  | succ n =>
    obtain ⟨M, hkM, hnM, h2⟩ := TShape.LE.src_succ h
    cases k with
    | zero =>
      match s, s' with
      | .forallE .., .bot | .forallE .., .sort _
      | .sigma .., .bot | .sigma .., .sort _ => exact absurd h2 (fun x => x)
      | .bot, _ | .sort _, _ | .unit _, _ | .nat, _ | .zero, _ | .succ _, _
      | .refl _, _ | .id .., _ | .lam _ _, _ | .pair _ _ _, _ => exact hb
    | succ k =>
      match s, s' with
      | .forallE .., .forallE .. | .sigma .., .sigma .. => exact hc trivial
      | .forallE .., .bot | .forallE .., .sort _ | .forallE .., .unit _
      | .forallE .., .nat | .forallE .., .zero | .forallE .., .succ _
      | .forallE .., .refl _ | .forallE .., .id .. | .forallE .., .lam _ _
      | .forallE .., .pair .. | .forallE .., .sigma ..
      | .sigma .., .bot | .sigma .., .sort _ | .sigma .., .unit _
      | .sigma .., .nat | .sigma .., .zero | .sigma .., .succ _
      | .sigma .., .refl _ | .sigma .., .id .. | .sigma .., .lam _ _
      | .sigma .., .pair .. | .sigma .., .forallE .. => exact absurd h2 (fun x => x)
      | .bot, _ | .sort _, _ | .unit _, _ | .nat, _ | .zero, _ | .succ _, _
      | .refl _, _ | .id .., _ | .lam _ _, _ | .pair _ _ _, _ => exact hb
