import DomainSemantics.Shape
import DomainSemantics.Regular

/-! # Typing of labelled shapes

`TShape.HasType Δ m a` says the shape `m` is a well-typed inhabitant of
the type-shape `a`.  It is one inductive over `TShape`, the shapes at all
levels; see the section heading below it for why, and §5.5/§5.5a of
`presheaf-proof-strategy.md` for the history.

Before it comes the machinery it is built on: `Evaluates`, the relational
graph lookup at a fixed level (master's `ShapeFun.app` was a
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

inductive Shape.IsNumeral : ∀ {n}, Shape n → Prop
  | bot : IsNumeral .bot
  | zero : IsNumeral (n := n+1) .zero
  | succ : IsNumeral (n := n) w → IsNumeral (.succ w)

/-- A numeral's head carries no label, so it names anything. -/
theorem Shape.WF.numeral_mem {Γ : List Term} {o} {n} {s : Shape n}
    (hnum : s.IsNumeral) (hw : s.WF Γ) : s.WF Γ o := by
  cases hnum <;> first | exact .bot_mem | trivial | exact hw

/-- A join of compatible numerals is a numeral. -/
theorem Shape.IsNumeral.join {Δ : List Term} {n} {v w : Shape n}
    (hc : v.Compat Δ w) (hv : v.IsNumeral) (hw : w.IsNumeral) :
    (v.join w).IsNumeral := by
  induction n with | zero => cases hv; simpa using hw | succ n ih
  cases hv with
  | bot => simpa using hw
  | zero =>
    cases hw with
    | bot => simpa using zero
    | zero => exact .zero
    | succ => cases hc
  | @succ _ v' hv'
  cases hw with
  | bot => simpa using succ hv'
  | zero => cases hc
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

theorem Shape.IsNumeral.lower {Δ : List Term} {n} {v v' : Shape n}
    (hle : v'.LE Δ v) (h : v.IsNumeral) : v'.IsNumeral := by
  induction h with
  | bot => cases le_bot_iff.1 hle; exact .bot
  | zero => match v' with | .bot => exact .bot | .zero => exact .zero
  | succ _ ih => match v' with | .bot => exact .bot | .succ w' => exact .succ (ih hle)

theorem Shape.IsNumeral.subst {τ : Subst} {n} {v : Shape n} (h : v.IsNumeral) :
    (v.subst τ).IsNumeral := by
  induction h with
  | bot => rw [subst_bot]; exact .bot
  | zero => exact .zero
  | succ _ ih => exact .succ ih

/-! ## The lookup is coherent

What the relational lookup owes and master does not: master's lookup is a
saturated max-below *function*, single-valued, so there is nothing to
join and nothing to check. -/

theorem Shape.IsNumeral.lift_iff {n k} (h : n ≤ k) {v : Shape n} :
    (v.lift k).IsNumeral ↔ v.IsNumeral := by
  constructor <;> intro H
  · induction n generalizing k with
    | zero =>
      cases v with | bot => exact .bot | sort r
      let 0 := k; rw [lift_self] at H; cases H
    | succ n ih
    let k + 1 := k
    match v with
    | .bot => exact .bot
    | .zero => exact .zero
    | .succ w => let .succ hw := H; exact .succ (ih (Nat.le_of_succ_le_succ h) hw)
  · induction H generalizing k with
    | bot => rw [lift_bot]; exact .bot
    | zero => let k+1 := k; exact .zero
    | succ _ ih => let k+1 := k; exact .succ (ih (Nat.le_of_succ_le_succ h))

/-! ## What the level-indexed typing cost, and why it is gone

A first version of this file defined typing by *recursion on the level*,
mirroring master's `Shape.lean`.  It is deleted; this note says what it was and
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
`v'`; a λ below `.lam A₀ g` is the `lam` clause again at its own graph, with
`g₀` kept as the generator the codomain witnesses live over (the other
repo's pattern — *the conditions constrain a generator above the shape
being classified*, `ΩLower`, `piGenerator`; §5.5); a pair below
`.pair A₀ a x y` is the `pair` clause again at its own first component
`x'`, with the dominator `xd` that the code is read at kept where it was.
Everything strictly below a shape and not of its head is `⊥`, and the
`bot` clause takes that.  `mono_l` and `mono_r` are then both theorems.

`forallE` and `sigma` are stated *directly* on `d` and `f`, with no
generator: `mono_l` pushes the premises into a smaller Π through
`Eval.tHasType`, whose `join` case is `join_sort` and whose `lower` case
is `mono_l_sort` — available because a Π is typed at a sort, where no
existential level can appear.

`id`, `pair`, `lam`, `forallE` and `sigma` pay for pinning with a
`Shape.WF` premise, since their subject's well-formedness is not otherwise
free; `succ` does not, because `IsNumeral` implies it, and `refl` does not
because it carries nothing to be well formed.

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
nonrec theorem TShape.LE.wf {Δ : List Term} {a b : TShape} (h : a.LE Δ b) :
    a.WF Δ :=
  (Shape.lift_wf (Nat.le_max_left ..)).1 h.wf

/-- `⊥` is well formed at every level. -/
theorem Shape.WF.bot {Δ : List Term} {n} :
    (.bot : Shape n).WF Δ := by cases n <;> trivial

/-- A numeral is well formed: its only labels are none. -/
theorem Shape.IsNumeral.wf {Δ : List Term} {n} {v : Shape n} (h : v.IsNumeral) :
    v.WF Δ := by
  induction h with
  | bot => exact .bot
  | zero => trivial
  | succ _ ih => exact ih

/-- A sort is well formed at every level. -/
theorem Shape.WF.sort {Δ : List Term} {n} {r : Bool} :
    (.sort r : Shape n).WF Δ := by cases n <;> trivial

/-- Only a sort is above a sort. -/
theorem Shape.sort_le {Δ : List Term} {n} {s : Shape n} {r : Bool}
    (h : (sort r).LE Δ s) : s = .sort r := by
  cases n with
  | zero => cases s with | bot => cases h | sort r' => cases h; rfl
  | succ n => cases s <;> cases h; rfl

/-- A sort is rigid: anything above it is it, at whatever level.  Proved by
reflecting the comparison back down with `Shape.lift_le_lift`. -/
theorem TShape.LE.sort_eq {Δ : List Term} (hΔ : ⊢ Δ) {n} {j : Bool} {a : TShape}
    (h : (Shape.T (n := n) (.sort j)).LE Δ a) : a.2 = .sort j := by
  have h2 : ((.sort j : Shape n).lift (max n a.1)).LE Δ
      (a.2.lift (max n a.1)) := h
  rw [Shape.lift_sort, show (Shape.sort j : Shape (max n a.1))
      = (Shape.sort j : Shape a.1).lift (max n a.1) from Shape.lift_sort.symm] at h2
  exact Shape.sort_le ((Shape.lift_le_lift hΔ (Nat.le_max_right ..)).1 h2)

/-- And so is `nat`. -/
theorem TShape.LE.nat_eq {Δ : List Term} {n} {a : TShape}
    (h : LE Δ (Shape.T (n := n+1) ShapeS.nat) a) :
    ∃ k, a = Shape.T (n := k+1) ShapeS.nat := by
  obtain ⟨j, s⟩ := a
  cases j with
  | zero =>
    obtain ⟨M, hM⟩ : ∃ M, max (n+1) 0 = M+1 := by
      cases hmax : max (n+1) 0 with
      | zero => exact absurd (hmax ▸ (n+1).le_max_left 0) (by omega)
      | succ M => exact ⟨M, rfl⟩
    have h2 : Shape.LE Δ (Shape.lift (max (n+1) 0) (Shape.T (n := n+1) ShapeS.nat).2)
        (s.lift (max (n+1) 0)) := h
    rw [hM] at h2
    cases s <;> cases h2
  | succ j
  refine ⟨j, ?_⟩
  obtain ⟨M, hM⟩ : ∃ M, max (n+1) (j+1) = M+1 := by
    cases hmax : max (n+1) (j+1) with
    | zero => exact absurd (hmax ▸ (n+1).le_max_left (j+1)) (by omega)
    | succ M => exact ⟨M, rfl⟩
  have h2 : Shape.LE Δ (Shape.lift (max (n+1) (j+1)) (Shape.T (n := n+1) ShapeS.nat).2)
      (s.lift (max (n+1) (j+1))) := h
  rw [hM] at h2
  cases s <;> first | rfl | exact absurd h2 id

/-- Inversion for a bound against a shape at a positive level, with the
level arithmetic done once: the comparison can be read at a successor
level, where `Shape.LE` computes. -/
theorem TShape.LE.at_succ {Δ : List Term} {n} {t : Shape (n+1)} {j} {s : Shape j}
    (h : LE Δ (Shape.T s) (Shape.T t)) :
    ∃ M, n ≤ M ∧ j ≤ M + 1 ∧ (s.lift (M+1)).LE Δ (t.lift (M+1)) := by
  obtain ⟨M, hM⟩ : ∃ M, max j (n+1) = M+1 := by
    cases hmax : max j (n+1) with
    | zero => exact absurd (hmax ▸ j.le_max_right (n+1)) (by omega)
    | succ M => exact ⟨M, rfl⟩
  have hn : n + 1 ≤ M + 1 := hM ▸ j.le_max_right (n+1)
  have hj : j ≤ M + 1 := hM ▸ j.le_max_left (n+1)
  refine ⟨M, Nat.le_of_succ_le_succ hn, hj, ?_⟩
  have h2 : (s.lift (max j (n+1))).LE Δ (t.lift (max j (n+1))) := h
  rwa [hM] at h2

/-- The same, when it is the *smaller* shape that sits at a positive level.
Needed for `sort`, whose generator may sit at level `0`. -/
theorem TShape.LE.src_succ {Δ : List Term} {n} {t : Shape n} {j} {s : Shape (j+1)}
    (h : LE Δ (Shape.T s) (Shape.T t)) :
    ∃ M, j ≤ M ∧ n ≤ M + 1 ∧ (s.lift (M+1)).LE Δ (t.lift (M+1)) := by
  obtain ⟨M, hM⟩ : ∃ M, max (j+1) n = M+1 := by
    cases hmax : max (j+1) n with
    | zero => exact absurd (hmax ▸ (j+1).le_max_left n) (by omega)
    | succ M => exact ⟨M, rfl⟩
  have hj : j + 1 ≤ M + 1 := hM ▸ (j+1).le_max_left n
  have hn : n ≤ M + 1 := hM ▸ (j+1).le_max_right n
  refine ⟨M, Nat.le_of_succ_le_succ hj, hn, ?_⟩
  have h2 : (s.lift (max (j+1) n)).LE Δ (t.lift (max (j+1) n)) := h
  rwa [hM] at h2

/-- The lookup over `TShape`: the four rules of `ShapeFun.Eval`, comparing
with the level-independent `TShape.LE`, so it needs no `lift` lemma. -/
inductive TEvaluates (Δ : List Term) {n} (f : ShapeFun n) (A a : Term) (x : TShape) :
    TShape → Prop where
  | bot : TEvaluates Δ f A a x TShape.bot
  | entry (e : Entry (Shape n)) : e ∈ f → LabelEq Δ A e.tm A a →
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
    {x : TShape} (hf : ∀ e ∈ f, e.out.T.WF Δ)
    {c : TShape} (h : TEvaluates Δ f A a x c) : c.WF Δ := by
  induction h with
  | bot => exact .bot
  | entry e he => exact hf e he
  | lower hle => exact hle.wf
  | join hc _ _ ih₁ ih₂ => exact ih₁.join hΔ hc ih₂

/-- The lookup grows when the input grows.  Only `entry` has content. -/
theorem TEvaluates.mono_inp {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a : Term}
    {x x' : TShape} (hx : x.LE Δ x')
    {c : TShape} (h : TEvaluates Δ f A a x c) : TEvaluates Δ f A a x' c := by
  induction h with
  | bot => exact .bot
  | entry e he hl hin => exact .entry e he hl (hin.trans hΔ hx)
  | lower hle _ ih => exact .lower hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- The lookup grows when the label moves along a definitional equality and
the input grows. -/
theorem TEvaluates.mono {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a A' a' : Term}
    {x x' : TShape} (hlab : LabelEq Δ A a A' a') (hx : x.LE Δ x')
    {c : TShape} (h : TEvaluates Δ f A a x c) : TEvaluates Δ f A' a' x' c := by
  induction h with
  | bot => exact .bot
  | entry e he hl hin => exact .entry e he (hl.trans hlab).right (hin.trans hΔ hx)
  | lower hle _ ih => exact .lower hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- **The query's type moves freely along a definitional equality.**

Only the type: retyping converts the label equation `entry` carries along
the equality of types, which needs no typing of the query's term.  This is
what lets two `app` derivations at the same argument but different domain
labels be read at one query, without the argument having to be typed,
which at a non-admissible valuation it is not. -/
theorem TEvaluates.retype {Δ : List Term} {n} {f : ShapeFun n} {A A' a : Term}
    {x : TShape} (hA : TyEq Δ A A')
    {c : TShape} (h : TEvaluates Δ f A a x c) : TEvaluates Δ f A' a x c := by
  induction h with
  | bot => exact .bot
  | entry e he hl hin => exact .entry e he (hl.retype hA) hin
  | lower hle _ ih => exact .lower hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- Two lookups at one query in one coherent graph are compatible, so
their join exists.  `Evaluates.compat` at the total level, with the same
double induction. -/
theorem TEvaluates.compat {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a : Term}
    {x : TShape} (hf : f.Compat Shape.Compat Δ A f) (hwx : x.WF Δ)
    {y z : TShape} (hy : TEvaluates Δ f A a x y) (hz : TEvaluates Δ f A a x z) :
    y.Compat Δ z := by
  induction hy with
  | bot => exact .bot_left
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
    (hf : ∀ e ∈ f, TEvaluates Δ f' A e.tm e.inp.T e.out.T)
    {c : TShape} (h : TEvaluates Δ f A a x c) : TEvaluates Δ f' A a x c := by
  induction h with
  | bot => exact .bot
  | entry e he hl hin => exact (hf e he).mono hΔ hl hin
  | lower hle _ ih => exact .lower hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- A lookup survives lifting the graph: the lifted entry has the same
label, an input equivalent to the old one and an output equivalent to the
old one, so `mono_inp` and `lower` carry it across. -/
theorem TEvaluates.lift_graph {Δ : List Term} (hΔ : ⊢ Δ) {n m} (hm : n ≤ m)
    {f : ShapeFun n} (hw : f.WFE (Shape.WF Δ)) {A a : Term} {x : TShape}
    {c : TShape} (h : TEvaluates Δ f A a x c) :
    TEvaluates Δ (ShapeFun.lift (Shape.lift m) f) A a x c := by
  induction h with
  | bot => exact .bot
  | entry e he hl hin =>
    have hwe := hw e he
    refine .lower (TShape.LE.le_lift hΔ (m := e.out.T) hm hwe.2) ?_
    exact .entry ⟨e.tm, e.inp.lift m, e.out.lift m⟩
      (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩) hl
      ((TShape.LE.lift_le hΔ (m := e.inp.T) hm hwe.1).trans hΔ hin)
  | lower hle _ ih => exact .lower hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- A lookup survives adding entries to the graph: only `entry` has
content, and there it is membership. -/
theorem TEvaluates.mono_graph {Δ : List Term} {n} {f f' : ShapeFun n} {A a : Term}
    {x : TShape} (hf : ∀ e ∈ f, e ∈ f')
    {c : TShape} (h : TEvaluates Δ f A a x c) : TEvaluates Δ f' A a x c := by
  induction h with
  | bot => exact .bot
  | entry e he hl hin => exact .entry e (hf e he) hl hin
  | lower hle _ ih => exact .lower hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- The level-indexed lookup is the `TShape` one, at a fixed level.  Only
`bot` and `join` need anything: `TEvaluates.bot` lands at `⟨0, ⊥⟩` where the
goal is at `⟨n, ⊥⟩`, and `TShape.join` sits at `max n n`. -/
theorem ShapeFun.Eval.toT {Δ : List Term} {n} {f : ShapeFun n} {A a : Term}
    {x y : Shape n} (h : f.Eval Δ (Shape.LE Δ) A a x y) :
    TEvaluates Δ f A a x.T y.T := by
  induction h with
  | bot => exact .lower (TShape.bot_le' rfl) .bot
  | entry e he hl hin => exact .entry e he hl (TShape.LE.T.2 hin)
  | lower hle _ ih => exact .lower (TShape.LE.T.2 hle) ih
  | join hc hy hz ih₁ ih₂ =>
    -- `TEvaluates.join` lands at `TShape.join y.T z.T`, whose level is
    -- `max n n`, where the goal's is `n`; `TShape.join_T` is that dependent
    -- rewrite along `Nat.max_self`
    exact TShape.join_T ▸ .join (TShape.Compat.T.2 hc) ih₁ ih₂

/-- A graph covers itself: each entry is its own lookup.  The label and
input reflexivities are exactly what `ShapeFun.WF` supplies. -/
theorem TEvaluates.refl {Δ : List Term} {n} {f : ShapeFun n}
    (hw : f.WF Δ Ty oB (@Shape.WF Δ _)) :
    ∀ e ∈ f, TEvaluates Δ f Ty e.tm e.inp.T e.out.T := by
  intro e he
  obtain ⟨⟨u, hty⟩, htm, hin, _⟩ := hw.1 e he
  exact .entry e he (.refl hty htm) (TShape.LE.T.2 (.refl hin))

/-- Entrywise coverage survives lifting the covered graph: `lift` moves
neither an input nor an output, as a `TShape`.  Used where a clause's graph
is compared at a level above both. -/
theorem TEvaluates.lift_cover {Δ : List Term} (hΔ : ⊢ Δ) {n n'} {g : ShapeFun n}
    {f' : ShapeFun n'} {k} (hk : n ≤ k) (hw : g.WF Δ Ty oB (@Shape.WF Δ _))
    (hg : ∀ e ∈ g, TEvaluates Δ f' Ty e.tm e.inp.T e.out.T) :
    ∀ e ∈ ShapeFun.lift (Shape.lift k) g,
      TEvaluates Δ f' Ty e.tm e.inp.T e.out.T := by
  intro e he
  obtain ⟨e₀, he₀, rfl⟩ := ShapeFun.mem_lift.1 he
  have hwe := hw.1 e₀ he₀
  exact .lower (TShape.LE.lift_le hΔ (m := e₀.out.T) hk hwe.2.2.2.forget)
    (mono_inp hΔ (TShape.LE.le_lift hΔ (m := e₀.inp.T) hk hwe.2.2.1)
      (hg e₀ he₀))

/-- And back: coverage of the lift is coverage of the graph. -/
theorem TEvaluates.lower_cover {Δ : List Term} (hΔ : ⊢ Δ) {n n'} {g : ShapeFun n}
    {f' : ShapeFun n'} {k} (hk : n ≤ k) (hw : g.WF Δ Ty oB (@Shape.WF Δ _))
    (hg : ∀ e ∈ ShapeFun.lift (Shape.lift k) g,
      TEvaluates Δ f' Ty e.tm e.inp.T e.out.T) :
    ∀ e ∈ g, TEvaluates Δ f' Ty e.tm e.inp.T e.out.T := by
  intro e he
  have hwe := hw.1 e he
  exact .lower (TShape.LE.le_lift hΔ (m := e.out.T) hk hwe.2.2.2.forget)
    (mono_inp hΔ (TShape.LE.lift_le hΔ (m := e.inp.T) hk hwe.2.2.1)
      (hg _ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)))

/-- The converse transport: a graph `g'` whose *lift* is covered by `g`,
which is itself covered by `f'`, is covered by `f'` at its own level.  This
is what a `Shape.LE` between two λ-shapes, read at a level above both,
hands back to the `lam` clause. -/
theorem TEvaluates.of_cover_lift {Δ : List Term} (hΔ : ⊢ Δ) {j k n'} (hjk : j ≤ k)
    {g' : ShapeFun j} {g : ShapeFun k} {f' : ShapeFun n'}
    (hw : g'.WF Δ Ty oB (@Shape.WF Δ _))
    (hcov : ∀ e ∈ ShapeFun.lift (Shape.lift k) g',
      g.Eval Δ (Shape.LE Δ) Ty e.tm e.inp e.out)
    (hg : ∀ e ∈ g, TEvaluates Δ f' Ty e.tm e.inp.T e.out.T) :
    ∀ e ∈ g', TEvaluates Δ f' Ty e.tm e.inp.T e.out.T := by
  intro e he
  have hwe := hw.1 e he
  have h2 := trans hΔ hg
    (hcov _ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)).toT
  exact .lower (TShape.LE.le_lift hΔ (m := e.out.T) hjk hwe.2.2.2.forget)
    (h2.mono_inp hΔ (TShape.LE.lift_le hΔ (m := e.inp.T) hjk hwe.2.2.1))

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
    (h : (Shape.T (n := n+1) (.forallE A B d f)).LE Δ
      (Shape.T (n := n'+1) (.forallE A' B' d' f'))) :
    d.T.LE Δ d'.T := by
  obtain ⟨M, hn'M, hnM, h2⟩ := h.at_succ
  exact (TShape.LE.def hΔ (Nat.le_of_succ_le_succ hnM) hn'M).2 h2.2.1

/-- The Σ twin. -/
theorem TShape.LE.sigma_dom {Δ : List Term} (hΔ : ⊢ Δ) {n n'}
    {A B A' B' : Term} {d : Shape n} {f : ShapeFun n} {d' : Shape n'} {f' : ShapeFun n'}
    (h : (Shape.T (n := n+1) (.sigma A B d f)).LE Δ
      (Shape.T (n := n'+1) (.sigma A' B' d' f'))) :
    d.T.LE Δ d'.T := by
  obtain ⟨M, hn'M, hnM, h2⟩ := h.at_succ
  exact (TShape.LE.def hΔ (Nat.le_of_succ_le_succ hnM) hn'M).2 h2.2.1

/-- Π-decomposition.  The codomain half composes the coverage the order
gives with a coverage of the bigger graph, which is what both `mono_l` and
`mono_r` have to hand. -/
theorem TShape.LE.forallE_decomp {Δ : List Term} (hΔ : ⊢ Δ) {n n' k}
    {A B A' B' : Term} {d : Shape n} {f : ShapeFun n} {d' : Shape n'}
    {f' : ShapeFun n'} {f'' : ShapeFun k}
    (h : (Shape.T (n := n+1) (.forallE A B d f)).LE Δ
      (Shape.T (n := n'+1) (.forallE A' B' d' f')))
    (hw' : Shape.WF (n := n'+1) Δ (.forallE A' B' d' f'))
    (hf' : ∀ e ∈ f', TEvaluates Δ f'' A' e.tm e.inp.T e.out.T) :
    PiLabelEq Δ A B A' B' ∧ d.T.LE Δ d'.T ∧
      ∀ e ∈ f, TEvaluates Δ f'' A e.tm e.inp.T e.out.T := by
  have hw := h.wf
  obtain ⟨M, hn'M, hnM, h2⟩ := h.at_succ
  have hn : n ≤ M := Nat.le_of_succ_le_succ hnM
  have hA : TyEq Δ A' A := h2.1.1.symm
  exact ⟨h2.1, (TShape.LE.def hΔ hn hn'M).2 h2.2.1,
    .of_cover_lift hΔ hn hw.2.2.2.1 h2.2.2.1.1
      (.lift_cover hΔ hn'M (hw'.2.2.2.1.retype hA)
        fun e he => (hf' e he).retype hA)⟩

/-- Σ-decomposition; the clause is the same as Π's. -/
theorem TShape.LE.sigma_decomp {Δ : List Term} (hΔ : ⊢ Δ) {n n' k}
    {A B A' B' : Term} {d : Shape n} {f : ShapeFun n} {d' : Shape n'}
    {f' : ShapeFun n'} {f'' : ShapeFun k}
    (h : (Shape.T (n := n+1) (.sigma A B d f)).LE Δ
      (Shape.T (n := n'+1) (.sigma A' B' d' f')))
    (hw' : Shape.WF (n := n'+1) Δ (.sigma A' B' d' f'))
    (hf' : ∀ e ∈ f', TEvaluates Δ f'' A' e.tm e.inp.T e.out.T) :
    PiLabelEq Δ A B A' B' ∧ d.T.LE Δ d'.T ∧
      ∀ e ∈ f, TEvaluates Δ f'' A e.tm e.inp.T e.out.T := by
  have hw := h.wf
  obtain ⟨M, hn'M, hnM, h2⟩ := h.at_succ
  have hn : n ≤ M := Nat.le_of_succ_le_succ hnM
  have hA : TyEq Δ A' A := h2.1.1.symm
  exact ⟨h2.1, (TShape.LE.def hΔ hn hn'M).2 h2.2.1,
    .of_cover_lift hΔ hn hw.2.2.2.1 h2.2.2.1.1
      (.lift_cover hΔ hn'M (hw'.2.2.2.1.retype hA)
        fun e he => (hf' e he).retype hA)⟩

/-- λ-decomposition: a λ-shape's graph is covered by any bigger one's, and
the non-degeneracy conjuncts are about the smaller graph alone, so they
carry no information downwards. -/
theorem TShape.LE.lam_decomp {Δ : List Term} (hΔ : ⊢ Δ) {n n' k} {A A' : Term}
    {g : ShapeFun n} {g' : ShapeFun n'} {f'' : ShapeFun k}
    (h : (Shape.T (n := n+1) (.lam A g)).LE Δ (Shape.T (n := n'+1) (.lam A' g')))
    (hw' : Shape.WF (n := n'+1) Δ (.lam A' g'))
    (hg' : ∀ e ∈ g', TEvaluates Δ f'' A' e.tm e.inp.T e.out.T) :
    ∀ e ∈ g, TEvaluates Δ f'' A e.tm e.inp.T e.out.T := by
  have hw := h.wf
  obtain ⟨M, hn'M, hnM, h2⟩ := h.at_succ
  have hA : TyEq Δ A' A := h2.2.2.2.1.symm
  exact .of_cover_lift hΔ (Nat.le_of_succ_le_succ hnM) hw.2.2.1 h2.1.1
    (.lift_cover hΔ hn'M (hw'.2.2.1.retype hA) fun e he => (hg' e he).retype hA)

/-- The lookup only sees its query label up to definitional equality. -/
theorem TEvaluates.label {Δ : List Term} {n} {f : ShapeFun n} {A a A' a' : Term}
    {x c : TShape} (hlab : LabelEq Δ A a A' a') (H : TEvaluates Δ f A a x c) :
    TEvaluates Δ f A' a' x c := by
  induction H with
  | bot => exact .bot
  | entry e he hl hin => exact .entry e he (hl.trans hlab).right hin
  | lower hle _ ih => exact .lower hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- The lookup transports along a typed substitution, rule by rule.  The
`join` case is the only one with content, and it is `TShape.join_subst`. -/
theorem TEvaluates.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {n} {f : ShapeFun n} {A a : Term} {x : TShape} :
    ∀ {c : TShape}, TEvaluates Δ f A a x c →
      TEvaluates Θ (f.subst (Shape.subst · τ) τ) (A.subst τ) (a.subst τ)
        (x.subst τ) (c.subst τ) := by
  intro c h
  induction h with
  | bot => exact .bot
  | entry e he hl hin =>
    exact .entry ⟨e.tm.subst τ, e.inp.subst τ, e.out.subst τ⟩
      (ShapeFun.mem_subst.2 ⟨e, he, rfl⟩) (hl.subst hΘ W) (hin.subst hΘ W)
  | lower hle _ ih => exact .lower (hle.subst hΘ W) ih
  | join hc _ _ ih₁ ih₂ =>
    exact TShape.join_subst ▸ .join (hc.subst hΘ W) ih₁ ih₂

/-- Pair-decomposition: both components back at their own canonical
level, with the label equalities. -/
theorem TShape.LE.pair_decomp {Δ : List Term} (hΔ : ⊢ Δ) {j n} {A A' a a' : Term}
    {x₂ y₂ : Shape j} {x y : Shape n}
    (h : (Shape.T (n := j+1) (.pair A a x₂ y₂)).LE Δ
      (Shape.T (n := n+1) (.pair A' a' x y))) :
    TyEq Δ A A' ∧ (Δ ⊢ a ≡ a' : A) ∧ x₂.T.LE Δ x.T ∧ y₂.T.LE Δ y.T := by
  obtain ⟨M, hnM, hjM, h2⟩ := h.at_succ
  have hj : j ≤ M := Nat.le_of_succ_le_succ hjM
  exact ⟨h2.2.2.2.1, h2.2.2.2.2, (TShape.LE.def hΔ hj hnM).2 h2.1,
    (TShape.LE.def hΔ hj hnM).2 h2.2.1⟩

/-- Lifting a shape's level does not move it in the order: the `TShape`
it names is the same one. -/
theorem TShape.lift_le_self {Δ : List Term} (hΔ : ⊢ Δ) {n k} (h : n ≤ k) {x : Shape n}
    (hw : Shape.WF Δ x) : LE Δ (Shape.T (Shape.lift k x)) x.T := by
  refine (LE.def hΔ (k := max k n) (Nat.le_max_left ..) (Nat.le_max_right ..)).2 ?_
  rw [Shape.lift_lift h]
  exact .refl ((Shape.lift_wf (k.le_max_right n)).2 hw)

theorem TShape.self_le_lift {Δ : List Term} (hΔ : ⊢ Δ) {n k} (h : n ≤ k) {x : Shape n}
    (hw : Shape.WF Δ x) : LE Δ x.T (Shape.T (Shape.lift k x)) := by
  refine (LE.def hΔ (k := max k n) (Nat.le_max_right ..) (Nat.le_max_left ..)).2 ?_
  rw [Shape.lift_lift h]
  exact .refl ((Shape.lift_wf (k.le_max_right n)).2 hw)

/-- Typing, over `TShape`. -/
inductive TShape.HasType (Δ : List Term) : TShape → TShape → Prop where
  | bot : HasType Δ a TShape.type → HasType Δ (Shape.T (n := n) .bot) a
  | sort : HasType Δ (Shape.T (n := n) (.sort r)) (Shape.T (n := k) .type)
  | unit : r ≤ j → HasType Δ (Shape.T (n := n+1) (.unit r)) (Shape.T (n := k) (.sort j))
  | nat : HasType Δ (Shape.T (n := n+1) .nat) (Shape.T (n := k) .type)
  | zero : HasType Δ (Shape.T (n := n+1) .zero) (Shape.T (n := k+1) .nat)
  | succ {n k} {v : Shape n} : v.IsNumeral →
    HasType Δ (Shape.T (n := n+1) (.succ v)) (Shape.T (n := k+1) .nat)
  | protected id {n k r j} {A x y : Term} : r ≤ j → Shape.WF (n := n+1) Δ (.id r A x y) →
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
    HasType Δ (Shape.T (n := n+1) (.sigma A B d f)) (Shape.T (n := k) .type)
  -- the shape is pinned, the graph is not: `g` is any graph below the
  -- generator `g₀`, which is where the codomain witnesses live (§5.5)
  | lam {n n₀ n'} {A₀ : Term} {g : ShapeFun n} {f : ShapeFun n'}
      {A B : Term} {d : Shape n'} {g₀ : List (Entry (Shape n₀) × TShape)} :
    HasType Δ d.T .type →
    (∀ e ∈ f, HasType Δ e.out.T .type) →
    Shape.WF (n := n+1) Δ (.lam A₀ g) →
    Shape.WF (n := n'+1) Δ (.forallE A B d f) →
    ShapeFun.WFE (Shape.WF Δ) (g₀.map (·.1)) →
    (∀ e ∈ g, TEvaluates Δ (g₀.map (·.1)) A₀ e.tm e.inp.T e.out.T) →
    (∀ e ∈ g₀, TEvaluates Δ f A e.1.tm e.1.inp.T e.2) →
    (∀ e ∈ g₀, HasType Δ e.1.out.T e.2) →
    -- the domain label is the Π's domain: intgrah's `Section` condition
    TyEq Δ A₀ A →
    HasType Δ (Shape.T (n := n+1) (.lam A₀ g)) (Shape.T (n := n'+1) (.forallE A B d f))
  -- **A pair is two components, not a graph** (§4.7f).  The first is
  -- typed at the Σ's domain; the second at the code the Σ's codomain
  -- graph gives at the pair's own name `a`, read at a **dominator** `xd`
  -- of the first component.  The dominator is what keeps typing lower-closed
  -- (§4.7b): shrinking either component keeps the same `xd` and the same
  -- code.  Join-closure is what it costs, and `TShape.Named`'s `sg`
  -- clause, which reads the code at the first component itself, is what
  -- supplies it where it is needed
  | pair {n n'} {A₀ a : Term} {x y : Shape n} {f : ShapeFun n'}
      {A B : Term} {d : Shape n'} {xd c : TShape} :
    HasType Δ d.T .type →
    (∀ e ∈ f, HasType Δ e.out.T .type) →
    Shape.WF (n := n+1) Δ (.pair A₀ a x y) →
    Shape.WF (n := n'+1) Δ (.sigma A B d f) →
    HasType Δ x.T d.T →
    LE Δ x.T xd →
    TEvaluates Δ f A a xd c →
    HasType Δ y.T c →
    TyEq Δ A₀ A →
    HasType Δ (Shape.T (n := n+1) (.pair A₀ a x y)) (Shape.T (n := n'+1) (.sigma A B d f))
  | refl {a n k} {A x y : Term} :
    LE Δ (Shape.T (n := k+1) (.id true A x y)) a →
    HasType Δ a .type → HasType Δ (Shape.T (n := n+1) .refl) a

/-- **Everything a shape is typed at is a type.** -/
theorem TShape.HasType.isType {Δ : List Term} {m a : TShape}
    (H : m.HasType Δ a) : a.HasType Δ .type := by
  induction H with
  | bot hA => exact hA
  | sort => exact .sort
  | unit => exact .sort
  | nat => exact .sort
  | zero => exact .nat
  | succ => exact .nat
  | id => exact .sort
  | forallE => exact .sort
  | sigma => exact .sort
  | lam hd hf _ hwPi => exact .forallE hd hf hwPi
  | pair hd hf _ hwSg => exact .sigma hd hf hwSg
  | refl _ hA => exact hA

/-- Sorts are injective at every level. -/
theorem Shape.sort_inj {n} {r r' : Bool} (h : (.sort r : Shape n) = .sort r') :
    r = r' := by cases n <;> cases h <;> rfl

/-- The level at which a sort is written as the type is immaterial.  Needed
because the `forallE` clause types its outputs at the same sort as the Π
itself, so moving the Π's sort to another level has to move theirs. -/
theorem TShape.HasType.sort_level {Δ : List Term} {m a : TShape}
    (H : m.HasType Δ a) {k' : Nat} {j : Bool} (ha : a.2 = .sort j) :
    m.HasType Δ (Shape.T (n := k') (.sort j)) := by
  induction H generalizing k' j with
  | bot => exact .bot .sort
  | sort => exact Shape.sort_inj ha ▸ .sort
  | unit hj => exact Shape.sort_inj ha ▸ .unit hj
  | nat => exact Shape.sort_inj ha ▸ .nat
  | zero | succ => cases ha
  | id hj hw => exact Shape.sort_inj ha ▸ .id hj hw
  | forallE hd hf hw _ ihf => exact Shape.sort_inj ha ▸ .forallE hd (fun e he => ihf e he rfl) hw
  | sigma hd hf hw => exact Shape.sort_inj ha ▸ .sigma hd hf hw
  -- the type is a pinned Π, resp. Σ, so it is not a sort outright
  | lam | pair => cases ha
  | refl hc
  obtain ⟨M, _, _, h2⟩ := hc.src_succ
  rw [ha, Shape.lift_sort] at h2
  cases h2

/-- Inversion at a Π, when the type is a sort.  `cases` needs the type to
be a variable — `Shape.sort` at a variable level is a stuck `match`, so it
does not unify with itself — which is why this is a lemma rather than a
`cases` at the use site. -/
theorem TShape.HasType.forallE_inv {Δ : List Term} {n} {A B : Term} {d : Shape n}
    {f : ShapeFun n} {a : TShape} {j : Bool}
    (H : (Shape.T (n := n+1) (.forallE A B d f)).HasType Δ a)
    (ha : a.2 = .sort j) :
    d.T.HasType Δ .type ∧
      (∀ e ∈ f, e.out.T.HasType Δ (.sort j)) ∧
      Shape.WF (n := n+1) Δ (.forallE A B d f) := by
  cases H with
  | forallE hd hf hw =>
    cases Shape.sort_inj ha
    exact ⟨hd, fun e he => (hf e he).sort_level rfl, hw⟩

theorem TShape.HasType.sigma_inv {Δ : List Term} {n} {A B : Term} {d : Shape n}
    {f : ShapeFun n} {a : TShape} {j : Bool}
    (H : (Shape.T (n := n+1) (.sigma A B d f)).HasType Δ a)
    (ha : a.2 = .sort j) :
    d.T.HasType Δ .type ∧
      (∀ e ∈ f, e.out.T.HasType Δ .type) ∧
      Shape.WF (n := n+1) Δ (.sigma A B d f) := by
  cases H with
  | sigma hd hf hw => exact ⟨hd, hf, hw⟩

/-- **Right monotonicity.**  At `lam`, `pair` and `refl` the type may grow
and the clause takes it by transitivity; at the rigid types — the sorts
and `nat` — it can only change level, and the clause is re-applied at the
new one. -/
theorem TShape.HasType.mono_r {Δ : List Term} (hΔ : ⊢ Δ) {m a : TShape}
    (H : m.HasType Δ a) (a' : TShape) (h : a.LE Δ a')
    (hA' : a'.HasType Δ .type) : m.HasType Δ a' := by
  induction H generalizing a' with
  | bot => exact .bot hA'
  | sort => show HasType Δ _ ⟨a'.1, a'.2⟩; rw [LE.sort_eq hΔ h]; exact .sort
  | unit hj =>
    show HasType Δ _ ⟨a'.1, a'.2⟩
    rw [LE.sort_eq hΔ h]; exact .unit hj
  | nat => show HasType Δ _ ⟨a'.1, a'.2⟩; rw [LE.sort_eq hΔ h]; exact .nat
  | zero => obtain ⟨k, rfl⟩ := h.nat_eq; exact .zero
  | succ hN => obtain ⟨k, rfl⟩ := h.nat_eq; exact .succ hN
  | id hj hw =>
    show HasType Δ _ ⟨a'.1, a'.2⟩
    rw [LE.sort_eq hΔ h]; exact .id hj hw
  | forallE hd hf hw =>
    show HasType Δ _ ⟨a'.1, a'.2⟩
    rw [LE.sort_eq hΔ h]
    exact .forallE hd (fun e he => (hf e he).sort_level rfl) hw
  | sigma hd hf hw =>
    show HasType Δ _ ⟨a'.1, a'.2⟩
    rw [LE.sort_eq hΔ h]; exact .sigma hd hf hw
  -- the type is pinned, so a bigger one is a bigger Π, resp. Σ, and it is
  -- the *codomain* witnesses that move: `hg₀ev`, resp. `hev`, are lookups
  -- in the Π's graph, and a bigger graph covers them (`TEvaluates.trans`).
  -- The new Π's own premises are read off `hA'`, which says it is a type
  | lam hd hf hwg hwPi hwg₀ hg hg₀ev hg₀ty hdom =>
    obtain ⟨k, s⟩ := a'
    obtain ⟨M, hnM, hkM, h2⟩ := h.src_succ
    cases k with | zero => cases s <;> cases h2 | succ k
    cases s with | forallE A' B' d' f' => ?_ | _ => cases h2
    obtain ⟨hd', hf', hw'⟩ := hA'.forallE_inv rfl
    obtain ⟨hPi, _, hcov⟩ := h.forallE_decomp hΔ hw' (.refl hw'.2.2.2.1)
    refine .lam hd' hf' hwg hw' hwg₀ hg (fun e he => ?_) hg₀ty (hdom.trans hPi.1)
    exact ((hg₀ev e he).trans hΔ hcov).retype hPi.1
  | pair hd hf hwp hwSg hxd hxle hev hyty hdom _ _ ihxd ihy =>
    obtain ⟨k, s⟩ := a'
    obtain ⟨M, hnM, hkM, h2⟩ := h.src_succ
    cases k with | zero => cases s <;> cases h2 | succ k
    cases s with | sigma A' B' d' f' => ?_ | _ => cases h2
    obtain ⟨hd', hf', hw'⟩ := hA'.sigma_inv rfl
    obtain ⟨hSg, hdd, hcov⟩ := h.sigma_decomp hΔ hw' (.refl hw'.2.2.2.1)
    refine .pair hd' hf' hwp hw' (ihxd d'.T hdd hd') hxle ?_ hyty (hdom.trans hSg.1)
    exact (hev.trans hΔ hcov).retype hSg.1
  | refl hc => exact .refl (hc.trans hΔ h) hA'

/-- **Everything typed is well formed, and so is its type.**

The shape: a clause that carries a bound gets it from the order, which
carries the well-formedness of its lower bound; a clause whose subject is
pinned (`bot`, `unit`, `nat`, `zero`) has nothing to check.  The type: the
clauses whose type is not a sort carry its typing, so the induction
hypothesis gives it, and a sort or `nat` is well formed outright. -/
theorem TShape.HasType.wf {Δ : List Term} {m a : TShape}
    (H : m.HasType Δ a) : m.WF Δ ∧ a.WF Δ := by
  induction H with
  | bot _ ih => exact ⟨.bot, ih.1⟩
  | sort => exact ⟨.sort, .sort⟩
  | unit => exact ⟨trivial, .sort⟩
  | nat => exact ⟨trivial, .sort⟩
  | zero => exact ⟨trivial, trivial⟩
  | succ hN => exact ⟨hN.wf, trivial⟩
  | id _ hw => exact ⟨hw, .sort⟩
  | forallE _ _ hw => exact ⟨hw, .sort⟩
  | sigma _ _ hw => exact ⟨hw, .sort⟩
  | lam _ _ hwg hwPi => exact ⟨hwg, hwPi⟩
  | pair _ _ hwp hwSg => exact ⟨hwp, hwSg⟩
  | refl _ _ ih => exact ⟨trivial, ih.1⟩

/-- Typing does not see the level of its subject: `⟨n, m⟩` and
`⟨k, m.lift k⟩` are order-equivalent, and every clause reaches the subject
only through the order or a pin.  Its converse `lower_subject` is below;
the level-indexed relation had the first at 40 lines and the second not at
all (§5.5). -/
theorem TShape.HasType.lift_subject {Δ : List Term} (hΔ : ⊢ Δ) {m a : TShape}
    (H : m.HasType Δ a) {k} (hk : m.1 ≤ k) : (m.lift k).HasType Δ a := by
  have succ_of {n k} (hk : n + 1 ≤ k) : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  induction H generalizing k with
  | bot hA => show HasType Δ ⟨k, _⟩ _; rw [Shape.lift_bot]; exact .bot hA
  | sort => show HasType Δ ⟨k, _⟩ _; rw [Shape.lift_sort]; exact .sort
  | unit hj => obtain ⟨k, rfl⟩ := succ_of hk; exact .unit hj
  | nat => obtain ⟨k, rfl⟩ := succ_of hk; exact .nat
  | zero => obtain ⟨k, rfl⟩ := succ_of hk; exact .zero
  | succ hN =>
    obtain ⟨k, rfl⟩ := succ_of hk
    exact .succ ((Shape.IsNumeral.lift_iff (Nat.le_of_succ_le_succ hk)).2 hN)
  | id hj hw => obtain ⟨k, rfl⟩ := succ_of hk; exact .id hj hw
  | forallE hd hf hw ihd ihf =>
    obtain ⟨k, rfl⟩ := succ_of hk
    have hn := Nat.le_of_succ_le_succ hk
    refine .forallE (ihd hn) (fun e he => ?_) ((Shape.lift_wf (Nat.succ_le_succ hn)).2 hw)
    obtain ⟨e₀, he₀, rfl⟩ := ShapeFun.mem_lift.1 he
    exact ihf e₀ he₀ hn
  | sigma hd hf hw ihd ihf =>
    obtain ⟨k, rfl⟩ := succ_of hk
    have hn := Nat.le_of_succ_le_succ hk
    refine .sigma (ihd hn) (fun e he => ?_) ((Shape.lift_wf (Nat.succ_le_succ hn)).2 hw)
    obtain ⟨e₀, he₀, rfl⟩ := ShapeFun.mem_lift.1 he
    exact ihf e₀ he₀ hn
  | lam hd hf hwg hwPi hwg₀ hg hg₀ev hg₀ty hdom =>
    obtain ⟨k, rfl⟩ := succ_of hk
    have hn := Nat.le_of_succ_le_succ hk
    exact .lam hd hf ((Shape.lift_wf (Nat.succ_le_succ hn)).2 hwg) hwPi hwg₀
      (.lift_cover hΔ hn hwg.2.2.1 hg) hg₀ev hg₀ty hdom
  | pair hd hf hwp hwSg hxd hxle hev hyty hdom _ _ ihxd ihy =>
    obtain ⟨k, rfl⟩ := succ_of hk
    have hn := Nat.le_of_succ_le_succ hk
    exact .pair hd hf ((Shape.lift_wf (Nat.succ_le_succ hn)).2 hwp) hwSg
      (ihxd hn) ((lift_le_self hΔ hn hwp.2.2.2.1).trans hΔ hxle) hev
      (ihy hn) hdom
  | refl hc hA => obtain ⟨k, rfl⟩ := succ_of hk; exact .refl hc hA

/-- **And the level of the subject can be lowered again.**  This is the
reflection direction that §5.5 shows the level-indexed definition cannot
have: it works here because every object a clause quantifies over — the
codomain generator `g₀`, the pair's dominator `x` and its code `c` — is a
`TShape`, so `lift` touches none of them.  What is left is entrywise, and
`TEvaluates.lower_cover` does it.

With `lift_subject` this makes typing blind to the subject's level, which
is what lets `mono_l` at a sort be run at one fixed level. -/
theorem TShape.HasType.lower_subject {Δ : List Term} (hΔ : ⊢ Δ) {N} {y : Shape N} {k}
    (hk : N ≤ k) {a : TShape} (H : (y.lift k).T.HasType Δ a) :
    y.T.HasType Δ a := by
  induction N generalizing k a with
  | zero =>
    cases k with | zero => rwa [Shape.lift_self] at H | succ k
    cases y with
    | bot => cases H with | bot hA => exact .bot hA
    | sort r => cases H with | sort => exact .sort
  | succ N ih
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hk' : N ≤ k := Nat.le_of_succ_le_succ hk
  cases y with
  | bot => cases H with | bot hA => exact .bot hA
  | sort r => cases H with | sort => exact .sort
  | unit r => cases H with | unit hj => exact .unit hj
  | nat => cases H with | nat => exact .nat
  | zero => cases H with | zero => exact .zero
  | succ v => cases H with | succ hN => exact .succ ((Shape.IsNumeral.lift_iff hk').1 hN)
  | id r A x y => cases H with | id hj hw => exact .id hj hw
  | refl => cases H with | refl hc hA => exact .refl hc hA
  | forallE A B d f =>
    cases H with | forallE hd hf hw
    exact .forallE (ih hk' hd) (fun e he => ih hk' (hf _ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)))
      ((Shape.lift_wf hk).1 hw)
  | sigma A B d f =>
    cases H with | sigma hd hf hw
    exact .sigma (ih hk' hd) (fun e he => ih hk' (hf _ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)))
      ((Shape.lift_wf hk).1 hw)
  | lam A₀ g =>
    cases H with | lam hd hf hwg hwPi hwg₀ hg hg₀ev hg₀ty hdom
    have hwg' := (Shape.lift_wf (s := .lam A₀ g) hk).1 hwg
    exact .lam hd hf hwg' hwPi hwg₀ (.lower_cover hΔ hk' hwg'.2.2.1 hg) hg₀ev hg₀ty hdom
  | pair A₀ a x y =>
    cases H with | pair hd hf hwp hwSg hxd hxle hev hyty hdom
    have hwp' := (Shape.lift_wf (s := .pair A₀ a x y) hk).1 hwp
    exact .pair hd hf hwp' hwSg (ih hk' hxd)
      ((self_le_lift hΔ hk' hwp'.2.2.2.1).trans hΔ hxle) hev (ih hk' hyty) hdom

/-- `⊥` is typed at `⊥`, since `⊥` is a type. -/
theorem TShape.HasType.bot_bot {Δ : List Term} {m : TShape} (h : m.2 = .bot) :
    m.HasType Δ .bot := by
  show HasType Δ ⟨m.1, m.2⟩ _
  rw [h]; exact .bot (.bot .sort)

/-- **Cumulativity**, which the sort-typed clauses build in: each carries
the sort as a bound (`unit`, `id`) or inherits it from its outputs
(`forallE`), and the rigid ones are already at `.type`.  Stated in
`sort_level`'s form, with the sort read off `a.2`, because `Shape.sort` at
a variable level is a stuck `match` and will not unify with itself. -/
theorem TShape.HasType.cumul {Δ : List Term} {m a : TShape}
    (H : m.HasType Δ a) {k' : Nat} {r s : Bool} (ha : a.2 = .sort r) (hrs : r ≤ s) :
    m.HasType Δ (Shape.T (n := k') (.sort s)) := by
  induction H generalizing k' r with
  | bot => exact .bot .sort
  | sort => rw [Bool.eq_true_of_le (Shape.sort_inj ha).symm hrs]; exact .sort
  | unit hj => exact .unit (Bool.le_tr hj (Shape.sort_inj ha ▸ hrs))
  | nat => rw [Bool.eq_true_of_le (Shape.sort_inj ha).symm hrs]; exact .nat
  | zero | succ | lam | pair => cases ha
  | id hj hw => exact .id (Bool.le_tr hj (Shape.sort_inj ha ▸ hrs)) hw
  | forallE hd _ hw _ ihf =>
    exact .forallE hd (fun e he => ihf e he rfl (Shape.sort_inj ha ▸ hrs)) hw
  | sigma hd hf hw =>
    rw [Bool.eq_true_of_le (Shape.sort_inj ha).symm hrs]; exact .sigma hd hf hw
  | refl hc
  obtain ⟨M, _, _, h2⟩ := hc.src_succ
  rw [ha, Shape.lift_sort] at h2
  cases h2

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
    (W : Ctx.SubstEq Θ τ τ Δ) {m a : TShape} (H : m.HasType Δ a) :
    (m.subst τ).HasType Θ (a.subst τ) := by
  induction H with
  | bot _ ih => simp only [subst_T, Shape.subst_bot]; exact .bot ih
  | sort => simp only [subst_T, Shape.subst_sort]; exact .sort
  | unit hj => simp only [subst_T, Shape.subst_sort]; exact .unit hj
  | nat => simp only [subst_T, Shape.subst_sort]; exact .nat
  | zero => simp only [subst_T]; exact .zero
  | succ hN => simp only [subst_T]; exact .succ hN.subst
  | id hj hw =>
    simp only [subst_T, Shape.subst_sort]
    exact .id hj (hw.subst hΘ W)
  | forallE hd _ hw ihd ihf =>
    simp only [subst_T, Shape.subst_sort] at *
    refine .forallE ihd (fun e he => ?_) (hw.subst hΘ W)
    obtain ⟨e₀, he₀, rfl⟩ := ShapeFun.mem_subst.1 he
    exact ihf e₀ he₀
  | sigma hd _ hw ihd ihf =>
    simp only [subst_T, Shape.subst_sort] at *
    refine .sigma ihd (fun e he => ?_) (hw.subst hΘ W)
    obtain ⟨e₀, he₀, rfl⟩ := ShapeFun.mem_subst.1 he
    exact ihf e₀ he₀
  | @lam _ _ _ _ _ _ _ _ _ g₀ _ _ hwg hwPi hwg₀ hg hg₀ev _ hdom ihd ihf ihg₀ty =>
    simp only [subst_T] at *
    refine .lam (g₀ := g₀.map fun p =>
        (⟨p.1.tm.subst τ, p.1.inp.subst τ, p.1.out.subst τ⟩, p.2.subst τ))
      ihd (fun e he => ?_) (hwg.subst hΘ W) (hwPi.subst hΘ W) ?_
      (fun e he => ?_) (fun e he => ?_) (fun e he => ?_) (hdom.subst hΘ W)
    · obtain ⟨e₀, he₀, rfl⟩ := ShapeFun.mem_subst.1 he
      exact ihf e₀ he₀
    · have := ShapeFun.WFE.subst_of (Δ := Δ) (Shape.WF.subst hΘ W) hwg₀
      simpa [ShapeFun.subst, List.map_map, Function.comp_def] using this
    · obtain ⟨e₀, he₀, rfl⟩ := ShapeFun.mem_subst.1 he
      have := (hg e₀ he₀).subst hΘ W
      simpa [ShapeFun.subst, List.map_map, Function.comp_def] using this
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
      exact (hg₀ev p hp).subst hΘ W
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
      exact ihg₀ty p hp
  | pair _ _ hwp hwSg _ hxle hev _ hdom ihd ihf ihxd ihy =>
    simp only [subst_T] at *
    exact .pair ihd (fun e he => by
        obtain ⟨e₀, he₀, rfl⟩ := ShapeFun.mem_subst.1 he
        exact ihf e₀ he₀)
      (hwp.subst hΘ W) (hwSg.subst hΘ W) ihxd
      (hxle.subst hΘ W) (hev.subst hΘ W) ihy (hdom.subst hΘ W)
  | refl hc _ ih =>
    simp only [subst_T] at *
    exact .refl (hc.subst hΘ W) ih

/-- **The join of two types is a type.**  Only `forallE` and `sigma` have
content: the join is componentwise, the domains join by the induction
hypothesis one level down, and the graphs append.  Everywhere else the join
is one of the two arguments, or the head mismatch makes `Compat` false, or
the shape cannot be typed at a sort at all — a λ, a pair and a `refl` are
typed only below a Π, a Σ and an `id`, none of which is below a sort. -/
theorem TShape.HasType.join_sort {Δ : List Term} (hΔ : ⊢ Δ) {n} {y z : Shape n} {a : TShape}
    {j : Bool} (ha : a.2 = .sort j) (hy : y.T.HasType Δ a)
    (hz : z.T.HasType Δ a) (hc : y.Compat Δ z) :
    (y.join z).T.HasType Δ a := by
  induction n generalizing a j with
  | zero => cases y with | bot => exact hz | sort r => cases z <;> exact hy
  | succ n ih
  cases y with
  | bot => exact hz
  | sort r | unit r | nat | zero | id r A x y =>
    cases z <;> first | exact hy | exact absurd hc (fun x => x)
  | succ v => cases z with | bot => exact hy | succ v' => cases hy; cases ha | _ => cases hc
  | forallE A B d f =>
    cases z with | forallE A' B' d' f' => ?_ | bot => exact hy | _ => cases hc
    have ⟨hd, hf, hw⟩ := hy.forallE_inv ha
    have ⟨hd', hf', hw'⟩ := hz.forallE_inv ha
    show HasType Δ _ ⟨a.1, a.2⟩
    rw [ha]
    refine .forallE (ih rfl hd hd' hc.2.1) (fun e he => ?_) (hw.join hΔ hc hw')
    match List.mem_append.1 he with
    | .inl h => exact hf e h
    | .inr h => exact hf' e h
  | sigma A B d f =>
    cases z with | sigma A' B' d' f' => ?_ | bot => exact hy | _ => cases hc
    cases hy with | sigma hd hf hw
    have ⟨hd', hf', hw'⟩ := hz.sigma_inv rfl
    refine .sigma (ih rfl hd hd' hc.2.1) (fun e he => ?_) (hw.join hΔ hc hw')
    match List.mem_append.1 he with
    | .inl h => exact hf e h
    | .inr h => exact hf' e h
  | lam g =>
    cases z with | lam g' => ?_ | bot => exact hy | _ => cases hc
    cases hy with | lam => cases ha
  | pair A₀ x g =>
    cases z with | pair A₀' x' g' => ?_ | bot => exact hy | _ => cases hc
    cases hy with | pair => cases ha
  | refl =>
    cases z with | refl => ?_ | bot => exact hy | _ => cases hc
    cases hy with | refl hcg
    obtain ⟨M, _, _, h2⟩ := hcg.src_succ
    rw [ha, Shape.lift_sort] at h2
    cases h2

/-- Everything the lookup returns is typed at a sort, when the graph's
outputs are.  `bot` is `⊥`, `entry` is the hypothesis, `lower` is the
lowering it is handed, and `join` is `join_sort`. -/
theorem ShapeFun.Eval.tHasType {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n}
    {A a : Term} {x : Shape n} {c : TShape} {j : Bool} (hc : c.2 = .sort j)
    (hty : ∀ e ∈ f, e.out.T.HasType Δ c)
    (hlow : ∀ {u v : Shape n}, u.LE Δ v → v.T.HasType Δ c →
      u.T.HasType Δ c)
    {y : Shape n} (h : f.Eval Δ (Shape.LE Δ) A a x y) : y.T.HasType Δ c := by
  induction h with
  | bot =>
    refine .bot ?_
    show TShape.HasType Δ ⟨c.1, c.2⟩ _
    rw [hc]; exact .sort
  | entry e he => exact hty e he
  | lower hle _ ih => exact hlow hle ih
  | join hcj _ _ ih₁ ih₂ => exact ih₁.join_sort hΔ hc ih₂ hcj

/-- **Left monotonicity at a sort, at a fixed level.**

This is the shape the old `Shape.HasType.mono_l_sort` had, and the reason
it can be an induction on the level where the general `mono_l` cannot: at a
sort the `lam` and `pair` clauses never arise — a λ is typed only below a
Π, a pair only below a Σ, and neither is below a sort — so the
existentially chosen `n₀`, which can sit *above* the subject's level, never
appears.  Both shapes being at one level is what keeps the components at
`N`, where the induction hypothesis lives; `TShape.LE` would put them at a
`max` that the smaller shape can push arbitrarily high. -/
theorem TShape.HasType.mono_l_sort_T {Δ : List Term} (hΔ : ⊢ Δ) {N} {y y' : Shape N}
    {a : TShape} {j : Bool} (ha : a.2 = .sort j) (hy : y.T.HasType Δ a)
    (hle : y'.LE Δ y) : y'.T.HasType Δ a := by
  induction N generalizing a j with
  | zero =>
    cases hy with
    | bot hA => cases Shape.le_bot_iff.1 hle; exact .bot hA
    | sort =>
      match Shape.le_sort hle with
      | .inl hb => cases hb; exact .bot .sort
      | .inr hs => cases hs; exact .sort
  | succ N ih
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
    | .inr ⟨v', hs, hv⟩ => cases hs; exact .succ (hN.lower hv)
  | id hj hw =>
    match Shape.le_id hle with
    | .inl hb => cases hb; exact .bot .sort
    | .inr ⟨A', a', b', hs, ⟨⟨u, hA⟩, hx, hy⟩⟩ =>
      cases hs
      exact .id hj ⟨⟨u, hA.hasType.1⟩, hx.hasType.1, hy.hasType.1, trivial⟩
  | forallE hd hf hw =>
    match Shape.le_forallE hle with
    | .inl hb => cases hb; exact .bot .sort
    | .inr ⟨A', B', d', f', hs, _, hdd, hff⟩ =>
      cases hs
      refine .forallE (ih rfl hd hdd) (fun e he => ?_) hle.wf
      exact (ShapeFun.Eval.tHasType hΔ ha (fun e he => (hf e he).sort_level rfl)
        (fun hle' hv => ih ha hv hle') (hff.1 e he)).sort_level rfl
  | sigma hd hf hw =>
    match Shape.le_sigma hle with
    | .inl hb => cases hb; exact .bot .sort
    | .inr ⟨A', B', d', f', hs, _, hdd, hff⟩ =>
      cases hs
      refine .sigma (ih rfl hd hdd) (fun e he => ?_) hle.wf
      exact (hff.1 e he).tHasType hΔ rfl hf (fun hle' hv => ih rfl hv hle')
  -- a λ is typed only at a Π and a pair only at a Σ, neither of which is
  -- a sort, so `ha` refutes both outright now that the type is pinned
  | lam | pair => cases ha
  | refl hc
  have h2 := LE.def_mp (k := max _ a.1 + 1)
    (Nat.succ_le_succ (Nat.le_max_left ..)) (Nat.le_succ_of_le (Nat.le_max_right ..)) hc
  rw [ha, Shape.lift_sort] at h2
  cases h2

/-- **Left monotonicity at a sort**, with the two shapes at any levels.
`lift_subject` puts both at the level the order compares them at,
`mono_l_sort_T` does the work there, and `lower_subject` brings the smaller
one back down. -/
theorem TShape.HasType.mono_l_sort {Δ : List Term} (hΔ : ⊢ Δ) {m a : TShape}
    {j : Bool} (ha : a.2 = .sort j) (H : m.HasType Δ a)
    {m' : TShape} (h : m'.LE Δ m) : m'.HasType Δ a :=
  lower_subject hΔ (Nat.le_max_left ..)
    (mono_l_sort_T hΔ ha (H.lift_subject hΔ (Nat.le_max_right ..)) h)

/-- **Left monotonicity.**  Where the clause carries a bound the smaller
shape slides down it by transitivity; where the subject is pinned, `⊥` is
all that sits strictly below, and the `bot` clause takes it. -/
theorem TShape.HasType.mono_l {Δ : List Term} (hΔ : ⊢ Δ) {m a : TShape}
    (H : m.HasType Δ a) {m' : TShape} (h : m'.LE Δ m) :
    m'.HasType Δ a := by
  induction H generalizing m' with
  | bot hA => show HasType Δ ⟨m'.1, m'.2⟩ _; rw [le_bot hΔ rfl h]; exact .bot hA
  | sort =>
    obtain ⟨j, s⟩ := m'
    cases j with
    | zero => cases s with | bot => exact .bot .sort | sort r' => exact .sort
    | succ j
    obtain ⟨M, _, _, h2⟩ := h.src_succ
    rw [Shape.lift_sort] at h2
    cases s <;> first | exact .bot .sort | exact .sort | exact absurd h2 (fun x => x)
  | unit hj =>
    obtain ⟨j, s⟩ := m'
    obtain ⟨M, _, _, h2⟩ := h.at_succ
    cases j <;> cases s <;> first
      | exact .bot .sort | (cases h2; exact .unit hj) | exact absurd h2 (fun x => x)
  | nat =>
    obtain ⟨j, s⟩ := m'
    obtain ⟨M, _, _, h2⟩ := h.at_succ
    cases j <;> cases s <;> first | exact .bot .sort | exact .nat | exact absurd h2 (fun x => x)
  | zero =>
    obtain ⟨j, s⟩ := m'
    obtain ⟨M, _, _, h2⟩ := h.at_succ
    cases j <;> cases s <;> first | exact .bot .nat | exact .zero | exact absurd h2 (fun x => x)
  | succ hN =>
    obtain ⟨j, s⟩ := m'
    obtain ⟨M, hnM, hjM, h2⟩ := h.at_succ
    cases j with
    | zero => cases s <;> first | exact .bot .nat | exact absurd h2 (fun x => x)
    | succ j
    cases s with | bot => exact .bot .nat | succ v' => ?_ | _ => cases h2
    exact .succ ((Shape.IsNumeral.lift_iff (Nat.le_of_succ_le_succ hjM)).1
      (((Shape.IsNumeral.lift_iff hnM).2 hN).lower h2))
  | id hj hw =>
    obtain ⟨j, s⟩ := m'
    obtain ⟨M, _, _, h2⟩ := h.at_succ
    cases j with
    | zero => cases s <;> first | exact .bot .sort | exact absurd h2 (fun x => x)
    | succ j
    cases s with | bot => exact .bot .sort | id r' A' x' y' => ?_ | _ => cases h2
    obtain ⟨rfl, ⟨u, hA⟩, hx, hy⟩ := h2
    exact .id hj ⟨⟨u, hA.hasType.1⟩, hx.hasType.1, hy.hasType.1, trivial⟩
  -- a Π and a Σ are typed at a sort, so they are `mono_l_sort`'s business:
  -- the components sit one level down, where the order compares them
  -- levelwise and the induction on the level reaches them
  | forallE hd hf hw => exact mono_l_sort hΔ rfl (.forallE hd hf hw) h
  | sigma hd hf hw => exact mono_l_sort hΔ rfl (.sigma hd hf hw) h
  -- the λ-shape is pinned, so a smaller one is `⊥` or another λ, whose
  -- graph the order covers by `g` at a level above both; `of_cover_lift`
  -- brings that coverage back down and composes it with `g`'s own
  | lam hd hf hwg hwPi hwg₀ hg hg₀ev hg₀ty hdom =>
    obtain ⟨j, s⟩ := m'
    obtain ⟨M, hnM, hjM, h2⟩ := h.at_succ
    cases j with
    | zero => cases s <;> first | exact .bot (.forallE hd hf hwPi) | exact absurd h2 (fun x => x)
    | succ j
    cases s with | bot => exact .bot (.forallE hd hf hwPi) | lam A' g' => ?_ | _ => cases h2
    have hwg' : Shape.WF (n := j+1) Δ (.lam A' g') := (Shape.lift_wf hjM).1 h2.wf
    exact .lam hd hf hwg' hwPi hwg₀
      (h.lam_decomp hΔ hwg hg) hg₀ev hg₀ty (h2.2.2.2.1.trans hdom)
  | pair hd hf hwp hwSg hxd hxle hev hyty hdom _ _ ihxd ihy =>
    obtain ⟨j, s⟩ := m'
    obtain ⟨M, _, hjM, h2⟩ := h.at_succ
    cases j with
    | zero => cases s <;> first | exact .bot (.sigma hd hf hwSg) | exact absurd h2 (fun x => x)
    | succ j
    cases s with | bot => exact .bot (.sigma hd hf hwSg) | pair A' a' x' y' => ?_ | _ => cases h2
    have hwp' : Shape.WF (n := j+1) Δ (.pair A' a' x' y') := (Shape.lift_wf hjM).1 h2.wf
    obtain ⟨hA', ha', hx', hy'⟩ := h.pair_decomp hΔ
    refine .pair hd hf hwp' hwSg (ihxd hx') (hx'.trans hΔ hxle) ?_
      (ihy hy') (hA'.trans hdom)
    exact hev.label ⟨hdom.symm.trans hdom, (hA'.trans hdom).defeqDF ha'.symm⟩
  | refl hc hA
  obtain ⟨j, s⟩ := m'
  obtain ⟨M, _, hjM, h2⟩ := h.at_succ
  cases j with
  | zero => cases s <;> first | exact .bot hA | exact absurd h2 (fun x => x)
  | succ j
  cases s with | bot => exact .bot hA | refl => exact .refl hc hA | _ => cases h2

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
    {j : Bool} (hc : c.2 = .sort j) (hy : y.HasType Δ c)
    (hz : z.HasType Δ c) (hyz : y.Compat Δ z) :
    (y.join z).HasType Δ c :=
  (hy.lift_subject hΔ (Nat.le_max_left ..)).join_sort hΔ hc
    (hz.lift_subject hΔ (Nat.le_max_right ..)) hyz

/-- **Everything typed at `nat` is a numeral.**  The three clauses whose
type can be a `nat` shape are `bot`, `zero` and `succ`, and those are the
three constructors of `IsNumeral`. -/
theorem TShape.HasType.isNumeral {Δ : List Term} (hΔ : ⊢ Δ) {m a : TShape}
    (ha : LE Δ a (Shape.T (n := 1) ShapeS.nat)) (h : HasType Δ m a) :
    m.2.IsNumeral := by
  cases mono_r hΔ h (Shape.T (n := 1) ShapeS.nat) ha .nat with
  | bot => exact .bot
  | zero => exact .zero
  | succ hN => exact .succ hN
  | refl hc
  obtain ⟨M, _, _, h2⟩ := hc.at_succ
  cases h2

/-- And back: a numeral is typed at `nat`.  `bot` needs `nat` to be a
type, which it is at every level. -/
theorem Shape.IsNumeral.hasType {Δ : List Term} {n} {v : Shape n} (h : v.IsNumeral) :
    TShape.HasType Δ v.T (T (n := 1) ShapeS.nat) := by
  induction h with
  | bot => exact .bot .nat
  | zero => exact .zero
  | succ hw => exact .succ hw

/-- The predecessor of a numeral is one. -/
theorem Shape.IsNumeral.pred {n} {v : Shape n}
    (h : IsNumeral (n := n+1) (.succ v)) : v.IsNumeral := by
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
  g₀.map fun p => ((⟨p.1.tm, p.1.inp.lift m, p.1.out.lift m⟩ : Entry (Shape m)), p.2)

theorem TShape.liftGen_map {n m : Nat} {g₀ : List (Entry (Shape n) × TShape)} :
    (liftGen m g₀).map (·.1) = ShapeFun.lift (Shape.lift m) (g₀.map (·.1)) := by
  simp [liftGen, ShapeFun.lift, List.map_map, Function.comp_def]

theorem join_gen_wf {Δ : List Term} {n₀ n₀'}
    {g₀ : List (Entry (Shape n₀) × TShape)} {g₀' : List (Entry (Shape n₀') × TShape)}
    (hw : ShapeFun.WFE (Shape.WF Δ) (g₀.map (·.1)))
    (hw' : ShapeFun.WFE (Shape.WF Δ) (g₀'.map (·.1))) :
    ShapeFun.WFE (Shape.WF Δ)
      ((TShape.liftGen (max n₀ n₀') g₀ ++ TShape.liftGen (max n₀ n₀') g₀').map (·.1)) := by
  intro e he
  rw [List.map_append] at he
  have lifted {k} (hk : k ≤ max n₀ n₀') {h : List (Entry (Shape k) × TShape)}
      (hh : ShapeFun.WFE (Shape.WF Δ) (h.map (·.1)))
      (he : e ∈ (TShape.liftGen (max n₀ n₀') h).map (·.1)) :
      e.inp.WF Δ ∧ e.out.WF Δ := by
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
    (hw : ShapeFun.WFE (Shape.WF Δ) (g₀.map (·.1)))
    (hw' : ShapeFun.WFE (Shape.WF Δ) (g₀'.map (·.1)))
    (hg : ∀ e ∈ g, TEvaluates Δ (g₀.map (·.1)) Ty e.tm e.inp.T e.out.T)
    (hg' : ∀ e ∈ g', TEvaluates Δ (g₀'.map (·.1)) Ty e.tm e.inp.T e.out.T) :
    ∀ e ∈ g ++ g', TEvaluates Δ
      ((TShape.liftGen (max n₀ n₀') g₀ ++ TShape.liftGen (max n₀ n₀') g₀').map (·.1))
      Ty e.tm e.inp.T e.out.T := by
  intro e he
  rw [List.map_append]
  match List.mem_append.1 he with
  | .inl h =>
    refine TEvaluates.mono_graph (fun d hd => List.mem_append.2 (.inl hd)) ?_
    rw [TShape.liftGen_map]
    exact (hg e h).lift_graph hΔ (Nat.le_max_left ..) hw
  | .inr h =>
    refine TEvaluates.mono_graph (fun d hd => List.mem_append.2 (.inr hd)) ?_
    rw [TShape.liftGen_map]
    exact (hg' e h).lift_graph hΔ (Nat.le_max_right ..) hw'

theorem join_gen_code {Δ : List Term} (hΔ : ⊢ Δ) {n' n₀ n₀'} {f : ShapeFun n'}
    {g₀ : List (Entry (Shape n₀) × TShape)} {g₀' : List (Entry (Shape n₀') × TShape)}
    (hw : ShapeFun.WFE (Shape.WF Δ) (g₀.map (·.1)))
    (hw' : ShapeFun.WFE (Shape.WF Δ) (g₀'.map (·.1)))
    (hev : ∀ e ∈ g₀, TEvaluates Δ f Ty e.1.tm e.1.inp.T e.2)
    (hev' : ∀ e ∈ g₀', TEvaluates Δ f Ty e.1.tm e.1.inp.T e.2) :
    ∀ e ∈ TShape.liftGen (max n₀ n₀') g₀ ++ TShape.liftGen (max n₀ n₀') g₀',
      TEvaluates Δ f Ty e.1.tm e.1.inp.T e.2 := by
  intro e he
  have lifted {k} (hk : k ≤ max n₀ n₀') {h : List (Entry (Shape k) × TShape)}
      (hh : ShapeFun.WFE (Shape.WF Δ) (h.map (·.1)))
      (hhev : ∀ e ∈ h, TEvaluates Δ f Ty e.1.tm e.1.inp.T e.2)
      (he : e ∈ TShape.liftGen (max n₀ n₀') h) :
      TEvaluates Δ f Ty e.1.tm e.1.inp.T e.2 := by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    exact TEvaluates.mono_inp hΔ
      (TShape.LE.le_lift hΔ (m := p.1.inp.T) hk (hh p.1 (List.mem_map.2 ⟨p, hp, rfl⟩)).1)
      (hhev p hp)
  match List.mem_append.1 he with
  | .inl h => exact lifted (Nat.le_max_left ..) hw hev h
  | .inr h => exact lifted (Nat.le_max_right ..) hw' hev' h

theorem join_gen_ty {Δ : List Term} (hΔ : ⊢ Δ) {n₀ n₀'}
    {g₀ : List (Entry (Shape n₀) × TShape)} {g₀' : List (Entry (Shape n₀') × TShape)}
    (hty : ∀ e ∈ g₀, e.1.out.T.HasType Δ e.2)
    (hty' : ∀ e ∈ g₀', e.1.out.T.HasType Δ e.2) :
    ∀ e ∈ TShape.liftGen (max n₀ n₀') g₀ ++ TShape.liftGen (max n₀ n₀') g₀',
      e.1.out.T.HasType Δ e.2 := by
  intro e he
  have lifted {k} (hk : k ≤ max n₀ n₀') {h : List (Entry (Shape k) × TShape)}
      (hhty : ∀ e ∈ h, e.1.out.T.HasType Δ e.2)
      (he : e ∈ TShape.liftGen (max n₀ n₀') h) :
      e.1.out.T.HasType Δ e.2 := by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    exact (hhty p hp).lift_subject hΔ hk
  match List.mem_append.1 he with
  | .inl h => exact lifted (Nat.le_max_left ..) hty h
  | .inr h => exact lifted (Nat.le_max_right ..) hty' h

/-- Everything the `TShape` lookup returns is typed at a sort, when the
graph's outputs are.  `lower` is `mono_l_sort` and `join` is `join_sort'`;
the level-indexed `ShapeFun.Eval.tHasType` had to take both as
hypotheses. -/
theorem TEvaluates.tHasType {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n}
    {A a : Term} {x c : TShape} {j : Bool} (hc : c.2 = .sort j)
    (hty : ∀ e ∈ f, e.out.T.HasType Δ c) {y : TShape} (h : TEvaluates Δ f A a x y) :
    y.HasType Δ c := by
  induction h with
  | bot =>
    refine .bot ?_
    show TShape.HasType Δ ⟨c.1, c.2⟩ _
    rw [hc]; exact .sort
  | entry e he => exact hty e he
  | lower hle _ ih => exact ih.mono_l_sort hΔ hc hle
  | join hcj _ _ ih₁ ih₂ => exact ih₁.join_sort' hΔ hc ih₂ hcj

/-- A lookup in a graph whose outputs are all `⊥` is `⊥`. -/
theorem TEvaluates.eq_bot {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n}
    {A a : Term} {x : TShape} (hf : ∀ e ∈ f, e.out = .bot)
    {c : TShape} (h : TEvaluates Δ f A a x c) : c.2 = .bot := by
  induction h with
  | bot => rfl
  | entry e he => exact hf e he
  | lower hle _ ih => exact TShape.le_bot hΔ ih hle
  | join _ _ _ ih₁ ih₂ => exact TShape.join_eq_bot ih₁ ih₂

theorem TShape.HasType.bot_r {Δ : List Term} (hΔ : ⊢ Δ) {x a : TShape}
    (ha : a.2 = .bot) (h : x.HasType Δ a) : x.2 = .bot := by
  cases h with
  | bot => rfl
  | sort | unit | nat | id | forallE | sigma => cases Shape.sort_ne_bot ha
  | zero | succ | lam | pair => cases ha
  | refl hc => cases le_bot hΔ ha hc

/-- A sort is typed at `.type` and nothing else, so never at `.prop`.  The
hypothesis form is forced: `Shape.sort` at a variable level is a stuck
`match`, so the subject has to be a variable for `cases` to fire. -/
theorem TShape.HasType.sort_not_prop {Δ : List Term} {a : TShape} {j : Bool}
    (ha : a.2 = .sort j) (h : a.HasType Δ .prop) : False := by
  cases h with
  | bot => exact Shape.bot_ne_sort ha
  | unit | id | forallE | refl => cases ha

/-- **A proposition is inhabited only by `⊥`.**

Master's `HasType.proofIrrel`.  The old level-indexed proof inducted on the
*level*, because everything in sight lived at one; here it is an induction
on the **derivation**, and the `lam` clause's own induction hypothesis —
the one at `hg₀ty`, the codomain generator — is exactly the recursive call
needed.  That is the generator earning its keep a second time: with a
dominating codomain witness there is no such hypothesis to have. -/
theorem TShape.HasType.proofIrrel {Δ : List Term} (hΔ : ⊢ Δ) {x a : TShape}
    (h : x.HasType Δ a) (ha : a.HasType Δ .prop) : x.2 = .bot := by
  induction h with
  | bot => rfl
  | sort | unit | nat | id | forallE | sigma => cases ha.sort_not_prop rfl
  | zero | succ | pair => cases ha
  | refl hc =>
    cases ha with
    | bot => cases le_bot hΔ rfl hc
    | id hj =>
      obtain ⟨M, _, _, h2⟩ := hc.src_succ
      cases h2.1
      cases Bool.eq_true_of_le rfl hj
    | unit | forallE | refl =>
      obtain ⟨M, _, _, h2⟩ := hc.src_succ
      cases h2
  | @lam n n₀ n' _ g f _ _ d g₀ _ _ hwg _ _ hg hg₀ev _ _ _ _ ihg₀ty
  obtain ⟨_, hf, _⟩ := ha.forallE_inv rfl
  -- each generator output is `⊥`: its type is a lookup in a graph whose
  -- own outputs are propositions, so the clause's induction hypothesis
  -- applies to it
  have hbot (e') (he' : e' ∈ g₀) : e'.1.out = .bot :=
    ihg₀ty e' he' ((hg₀ev e' he').tHasType hΔ rfl hf)
  have hbot' (e : Entry (Shape n₀)) (he : e ∈ g₀.map (·.1)) : e.out = .bot := by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    exact hbot p hp
  -- so is every output of `g`, and a well-formed λ-shape has none
  cases g with | nil => cases hwg.1 rfl | cons e g'
  have hout : e.out = .bot := (hg e (.head _)).eq_bot hΔ hbot'
  cases hwg.2.1 e (.head _) (show e.out.IsBot by rw [hout]; cases n <;> trivial)

/-! ## Hereditarily typed shapes

`Interp.lam` puts an entry's input in the body's slot and `Adm` asks that
a slot be typed; η needs more, and so does the `app` case of `SoundTy`:
that the *inputs of that input* are typed one binder down, and that an
entry's *output* is again hereditarily typed at the codomain it is read
at.  Both are what the original's Π-decoder does — `arrow Q P F = λX. Q
(F (P X))` decodes the argument *and* the result (`Domain/Decoder/
FunctionRetraction.lean`) -- and `x : a ↔ p_a x = x` is its per-point
form.

`Named` is an **inductive** relation rather than a recursion on the code:
the codomain code an entry's output is read at is a *lookup* in the Π's
graph, so it is not a subterm of the code, and a least fixed point says
what is wanted without a measure.  It is deliberately **not** downward
closed; the form that is, `SoundTy`, is the saturating one. -/

/-- The graph a shape carries, if it carries one: a λ's or a pair's. -/
def Shape.graph {n} : Shape (n+1) → List (Entry (Shape n))
  | .lam _ g => g
  | _ => []

/-- A shape's entries, levels forgotten. -/
def TShape.entries : TShape → List (Entry TShape)
  | ⟨0, _⟩ => []
  | ⟨_+1, s⟩ => s.graph.map (fun e => ⟨e.tm, e.inp.T, e.out.T⟩)

def TShape.pairParts : TShape → Option (Term × TShape × TShape)
  | ⟨0, _⟩ => none
  | ⟨_+1, .pair _ a x y⟩ => some (a, x.T, y.T)
  | ⟨_+1, _⟩ => none

@[simp] theorem TShape.pairParts_bot {n} :
    (Shape.T (n := n) .bot).pairParts = none := by cases n <;> rfl

/-- A code that binds: the two whose decoder does more than filter. -/
def TShape.IsBinder : TShape → Prop
  | ⟨0, _⟩ => False
  | ⟨_+1, .forallE ..⟩ => True
  | ⟨_+1, .sigma ..⟩ => True
  | ⟨_+1, _⟩ => False

/-- Membership in a mapped `Option`, in the form the `Named` proofs use. -/
theorem Option.exists_of_mem_map {α β : Type} {o : Option α} {f : α → β} {b : β}
    (h : b ∈ o.map f) : ∃ a ∈ o, b = f a := by
  cases o with
  | none => cases h
  | some a => exact ⟨a, rfl, by simpa using h.symm⟩

/-! ## The lookup

A lookup in a canonical code's codomain graph at a well-typed query is a
canonical code of the family at that query.  This is the query-based
reading of the entry-based condition; it is a theorem rather than the
definition because the definition has to survive substitution, and an
entry that is dead at one stage can be live at a later one. -/
theorem TShape.WF.lookup {Δ : List Term} (hΔ : ⊢ Δ) {n} {A B q : Term} {u v : Bool}
    {f : ShapeFun n} (hw : f.WF Δ A oB (@Shape.WF Δ _))
    (hf : ∀ e ∈ f, e.out.WF Δ (B.inst e.tm))
    (hA : Δ ⊢ A : .sort u) (hB : A :: Δ ⊢ B : .sort v) {x : TShape}
    {c : TShape} (h : TEvaluates Δ f A q x c) : c.WF Δ (B.inst q) := by
  have hwo (e) (he : e ∈ f) : e.out.T.WF Δ := (hw.1 e he).2.2.2.forget
  induction h with
  | bot => exact .bot_mem
  | entry e he hlab => exact (hf e he).conv (.inst hΔ hA hB hlab.2.symm)
  | lower hle hz ih => exact ih.mono hΔ hle
  | join hc hy hz ihy ihz => exact ihy.join hΔ hc ihz

/-- **Hereditary typing, with a name when one is asked for.**  The
`Option Term` index is the name: at `none` it is hereditary typing
alone, and at `some t` it is that together with "`x` names `t`".  The
index is the last argument and defaults to `none`, so `Named Δ d x` is
hereditary typing and `Named Δ d x t` is that together with the naming.

The index threads through the recursive positions whose name depends on
it: an entry's *output* names the application and a Σ's components the
projections, so both carry `o.map`.  An entry's *input* does not — it is
named at the entry's own label, which is intrinsic to the shape, so that
premise is at `p.1.tm` whether or not a name is asked for.  That is why
`Named.forget` does not recurse there: at the input there is nothing to
forget. -/
inductive TShape.Named (Δ : List Term) :
    TShape → TShape → (o : Option Term := none) → Prop where
  | base {o} {d x : TShape} : ¬ d.IsBinder → TShape.HasType Δ x d →
    WF Δ x o → Named Δ d x o
  | pi {o} {n} {A B : Term} {d : Shape n} {f : ShapeFun n} {x : TShape}
      {cs : List (Entry TShape × TShape)} :
    HasType Δ x (Shape.T (n := n+1) (ShapeS.forallE A B d f)) →
    x.entries = cs.map (·.1) →
    (∀ p ∈ cs, Named Δ d.T p.1.inp p.1.tm) →
    (∀ p ∈ cs, TEvaluates Δ f A p.1.tm p.1.inp p.2) →
    (∀ p ∈ cs, Named Δ p.2 p.1.out (o.map fun t => Term.app t p.1.tm)) →
    Named Δ (Shape.T (n := n+1) (ShapeS.forallE A B d f)) x o
  | sg {o} {n} {A B : Term} {d : Shape n} {f : ShapeFun n} {x : TShape}
      {ps : Option (Term × TShape × TShape)} {c : TShape} :
    HasType Δ x (Shape.T (n := n+1) (ShapeS.sigma A B d f)) →
    x.pairParts = ps →
    (∀ p ∈ ps, ∀ t ∈ o, Δ ⊢ p.1 ≡ Term.fst t : A) →
    (∀ p ∈ ps, Named Δ d.T p.2.1 (o.map Term.fst)) →
    (∀ p ∈ ps, TEvaluates Δ f A p.1 p.2.1 c) →
    (∀ p ∈ ps, Named Δ c p.2.2 (o.map Term.snd)) →
    Named Δ (Shape.T (n := n+1) (ShapeS.sigma A B d f)) x o

/-- **The extraction**: the subject is well formed *at the index*.  At a
`lam` or a `pair` the naming half is `True`, so it is the subject's own
well-formedness; at every other head the `base` clause carries it.

This is where the index pays off twice: the premise and the conclusion are
the same proposition, with no `∀ t ∈ o` on either side. -/
theorem TShape.Named.wf {Δ : List Term} {o} {d x : TShape}
    (h : d.Named Δ x o) : x.WF Δ o := by
  cases h with
  | base _ _ hc => exact hc
  | @pi _ _ _ _ _ _ _ _ hty | @sg _ _ _ _ _ _ _ _ _ hty =>
    -- the subject's head is a `lam`, a `pair` or `⊥`, and at those the
    -- clause does not mention the index at all
    have hty' := hty
    cases hty' <;> first | exact WF.bot | exact (HasType.wf hty).1

theorem TShape.Named.hasType {Δ : List Term} {o} {d x : TShape}
    (h : d.Named Δ x o) : x.HasType Δ d := by cases h <;> assumption

@[simp] theorem TShape.entries_bot {n} : (Shape.T (n := n) .bot).entries = [] := by
  cases n <;> rfl

theorem TShape.Named.bot {Δ : List Term} {o} {d : TShape} {n}
    (h : (Shape.T (n := n) .bot).HasType Δ d) :
    d.Named Δ (Shape.T (n := n) .bot) o := by
  obtain ⟨m, c⟩ := d
  cases m with | zero => exact .base (fun h => h) h (by cases n <;> trivial) | succ m
  match c with
  | .forallE .. => exact .pi (cs := []) h (by simp) (by simp) (by simp) (by simp)
  | .sigma .. =>
    exact .sg (ps := none) (c := .bot) h (by simp) (by simp) (by simp) (by simp) (by simp)
  | .bot | .sort _ | .unit _ | .nat | .zero | .succ _ | .refl | .id .. | .lam .. | .pair .. =>
    exact .base (fun h => h) h (by cases n <;> trivial)

/-- The same, for a subject that is `⊥` only up to its level. -/
theorem TShape.Named.bot_subject {Δ : List Term} {o} {d x : TShape} (hx : x.2 = .bot)
    (h : x.HasType Δ d) : d.Named Δ x o := by
  obtain ⟨n, s⟩ := x
  cases n with
  | zero => cases s with | bot => exact .bot h | sort r => cases hx
  | succ n
  cases s <;> first | exact bot (n := n+1) h | exact absurd hx (by simp [Shape.bot])

@[simp] theorem TShape.entries_subst {x : TShape} {τ : Subst} :
    (x.subst τ).entries = x.entries.map
      (fun e => ⟨e.tm.subst τ, e.inp.subst τ, e.out.subst τ⟩) := by
  obtain ⟨n, s⟩ := x
  cases n with | zero => cases s <;> rfl | succ n
  cases s <;> simp [entries, subst, Shape.graph, Shape.subst, ShapeFun.subst,
    List.map_map, Function.comp_def, Shape.T]

theorem TShape.IsBinder.subst {d : TShape} {τ : Subst} (h : ¬ d.IsBinder) :
    ¬ (d.subst τ).IsBinder := by
  obtain ⟨n, c⟩ := d
  cases n <;> cases c <;> first | exact h | exact fun x => x

/-- It transports along a typed substitution, like `HasType`, carrying
the index along with it. -/
theorem TShape.Named.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {o} {d x : TShape} (h : d.Named Δ x o) :
    (d.subst τ).Named Θ (x.subst τ) (o.map (·.subst τ)) := by
  induction h with
  | @base o d' x' hnb hty hc =>
    exact .base (IsBinder.subst hnb) (hty.subst hΘ W)
      (Shape.WF.subst hΘ W hc)
  | @pi o n A B d f x cs hty hent _ hev _ ihin ihout =>
    refine .pi (cs := cs.map fun p =>
        (⟨p.1.tm.subst τ, p.1.inp.subst τ, p.1.out.subst τ⟩, p.2.subst τ))
      (by simpa [Shape.subst] using hty.subst hΘ W) ?_ ?_ ?_ ?_
    · simp [entries_subst, hent, List.map_map, Function.comp_def]
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      cases o <;> simpa using ihin q hq
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact (hev q hq).subst hΘ W
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      cases o <;> simpa [Term.subst] using ihout q hq
  | @sg o n A B d f x ps c hty hps hname _ hev _ ihx ihy =>
    refine .sg (ps := ps.map fun p => (p.1.subst τ, p.2.1.subst τ, p.2.2.subst τ))
      (c := c.subst τ)
      (by simpa [Shape.subst] using hty.subst hΘ W) ?_ ?_ ?_ ?_ ?_
    · rw [← hps]; cases x with | mk k s => cases k <;> [skip; cases s] <;>
        simp [pairParts, TShape.subst, Shape.subst]
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := Option.exists_of_mem_map hp
      intro t ht
      cases o with | none => cases ht | some u
      simp only [Option.map_some, Option.mem_def, Option.some.injEq] at ht
      subst ht
      simpa [Term.subst] using (hname q hq u rfl).subst hΘ W
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := Option.exists_of_mem_map hp
      cases o <;> simpa [Term.subst] using ihx q hq
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := Option.exists_of_mem_map hp
      exact (hev q hq).subst hΘ W
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := Option.exists_of_mem_map hp
      cases o <;> simpa [Term.subst] using ihy q hq

theorem TShape.entries_lift {x : TShape} {k} (hk : x.1 ≤ k + 1) :
    (x.lift (k+1)).entries = x.entries.map
      (fun e => ⟨e.tm, e.inp.lift k, e.out.lift k⟩) := by
  obtain ⟨n, s⟩ := x
  cases n with | zero => cases s <;> rfl | succ n
  cases s <;> simp [entries, lift, Shape.graph, Shape.lift, ShapeFun.lift,
    List.map_map, Function.comp_def, Shape.T]

theorem TShape.pairParts_lift {x : TShape} {k} (hk : x.1 ≤ k + 1) :
    (x.lift (k+1)).pairParts =
      x.pairParts.map (fun p => (p.1, p.2.1.lift k, p.2.2.lift k)) := by
  obtain ⟨n, s⟩ := x
  cases n with | zero => cases s <;> rfl | succ n
  cases s <;> simp [pairParts, lift, Shape.lift, Shape.T]

theorem TShape.pairParts_lift_zero {x : TShape} : (x.lift 0).pairParts = none := by
  obtain ⟨n, s⟩ := x
  cases n <;> [cases s; skip] <;> rfl

theorem TShape.entries_level {x : TShape} {e : Entry TShape} (he : e ∈ x.entries) :
    e.inp.1 + 1 = x.1 ∧ e.out.1 + 1 = x.1 := by
  obtain ⟨n, s⟩ := x
  cases n with | zero => simp [entries] at he | succ n
  simp only [entries, List.mem_map] at he
  obtain ⟨e₀, _, rfl⟩ := he
  exact ⟨rfl, rfl⟩

theorem TShape.pairParts_level {x : TShape} {ps} (hps : x.pairParts = ps)
    {p} (hp : p ∈ ps) : p.2.1.1 + 1 = x.1 ∧ p.2.2.1 + 1 = x.1 := by
  obtain ⟨n, s⟩ := x
  subst hps
  cases n with | zero => cases hp | succ n
  match s with
  | .pair .. => simp [pairParts] at hp; subst hp; exact ⟨rfl, rfl⟩
  | .bot | .sort _ | .unit _ | .nat | .zero | .succ _ | .refl | .id ..
  | .lam .. | .forallE .. | .sigma .. => cases hp

/-- `Named` survives lifting the subject: its entries lift with it, one
level down, and a lifted query reads the same codes. -/
theorem TShape.Named.lift_subject {Δ : List Term} (hΔ : ⊢ Δ) {o} {d x : TShape}
    (h : d.Named Δ x o) {k} (hk : x.1 ≤ k) : d.Named Δ (x.lift k) o := by
  induction h generalizing k with
  | base hnb hty hc => exact .base hnb (hty.lift_subject hΔ hk) ((Shape.lift_wf hk).2 hc)
  | @pi o n A B d f x cs hty hent hin hev hout ihin ihout =>
    match k, hk with
    | 0, hk =>
      exact .pi (cs := []) (hty.lift_subject hΔ hk) rfl (by simp) (by simp) (by simp)
    | k+1, hk =>
      refine .pi (cs := cs.map fun p =>
          (⟨p.1.tm, p.1.inp.lift k, p.1.out.lift k⟩, p.2))
        (hty.lift_subject hΔ hk) ?_ ?_ ?_ ?_
      · simp [entries_lift hk, hent, List.map_map, Function.comp_def]
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        refine ihin q hq ?_
        have := entries_level (x := x) (e := q.1)
          (by rw [hent]; exact List.mem_map_of_mem hq)
        omega
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        refine (hev q hq).mono_inp hΔ ?_
        refine LE.le_lift hΔ ?_ (hasType (hin q hq)).wf.1
        have := entries_level (x := x) (e := q.1)
          (by rw [hent]; exact List.mem_map_of_mem hq)
        omega
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        refine ihout q hq ?_
        have := entries_level (x := x) (e := q.1)
          (by rw [hent]; exact List.mem_map_of_mem hq)
        omega
  | @sg o n A B d f x ps c hty hps hname hx hev hy ihx ihy =>
    match k, hk with
    | 0, hk =>
      exact .sg (ps := none) (c := c) (hty.lift_subject hΔ hk) pairParts_lift_zero
        (by simp) (by simp) (by simp) (by simp)
    | k+1, hk =>
      refine .sg (ps := ps.map fun p => (p.1, p.2.1.lift k, p.2.2.lift k)) (c := c)
        (hty.lift_subject hΔ hk) ?_ ?_ ?_ ?_ ?_
      · rw [← hps, pairParts_lift hk]
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := Option.exists_of_mem_map hp
        exact hname q hq
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := Option.exists_of_mem_map hp
        exact ihx q hq (by have := pairParts_level hps hq; omega)
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := Option.exists_of_mem_map hp
        refine (hev q hq).mono_inp hΔ ?_
        exact .le_lift hΔ (by have := pairParts_level hps hq; omega)
          (hasType (hx q hq)).wf.1
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := Option.exists_of_mem_map hp
        exact ihy q hq (by have := pairParts_level hps hq; omega)

/-- A code below a binder code is a binder code, or `⊥`: the order pins
the head.  This is what lets `Named`'s `base` clause stay disjoint from the
other two under `mono_r`. -/
theorem TShape.IsBinder.of_le {Δ : List Term} {d d' : TShape}
    (hle : d.LE Δ d') (hb : d'.IsBinder) (hnb : d.2 ≠ .bot) : d.IsBinder := by
  obtain ⟨n, s⟩ := d
  obtain ⟨k, s'⟩ := d'
  cases k with | zero => cases s' <;> cases hb | succ k
  obtain ⟨M, hkM, hnM, h2⟩ := hle.at_succ
  cases n with
  | zero =>
    cases s with
    | bot => cases hnb rfl
    | sort r =>
      match s' with
      | .forallE .. | .sigma .. => cases h2
      | .bot | .sort _ | .unit _ | .nat | .zero | .succ _ | .refl | .id ..
      | .lam .. | .pair .. => cases hb
  | succ n
  match s, s' with
  | .forallE .., .forallE .. => exact trivial
  | .sigma .., .sigma .. => exact trivial
  | .bot, _ => cases hnb rfl
  | .sort _, .forallE .. | .sort _, .sigma ..
  | .unit _, .forallE .. | .unit _, .sigma ..
  | .nat, .forallE .. | .nat, .sigma ..
  | .zero, .forallE .. | .zero, .sigma ..
  | .succ _, .forallE .. | .succ _, .sigma ..
  | .refl, .forallE .. | .refl, .sigma ..
  | .id .., .forallE .. | .id .., .sigma ..
  | .lam .., .forallE .. | .lam .., .sigma ..
  | .pair .., .forallE .. | .pair .., .sigma ..
  | .forallE .., .sigma .. | .sigma .., .forallE .. => cases h2
  | _, .bot | _, .sort _ | _, .unit _ | _, .nat | _, .zero | _, .succ _
  | _, .refl | _, .id .. | _, .lam .. | _, .pair .. => cases hb

/-- **`Named` grows with the code.**  The Π and Σ orders are covariant in
the domain, so the hereditary conditions move up with them; where the
head changes the smaller code is `⊥`, and then the subject is too. -/
theorem TShape.Named.mono_r {Δ : List Term} (hΔ : ⊢ Δ) {o} {d x : TShape}
    (h : d.Named Δ x o) {d' : TShape} (hle : d.LE Δ d')
    (hty : d'.HasType Δ .type) : d'.Named Δ x o := by
  induction h generalizing d' with
  | @base o d x hnb hty0 hc =>
    -- the split is on `IsBot`, which is decidable, rather than on equality
    -- with `⊥`, which would need `Classical.em`; for a well-formed shape the
    -- two agree
    by_cases hb : d.2.IsBot
    · exact .bot_subject
        (HasType.bot_r hΔ
          (Shape.WF.eq_bot_of_isBot (HasType.wf hty0).2 hb) hty0)
        (hty0.mono_r hΔ _ hle hty)
    · exact .base (fun hbind => hnb (hbind.of_le hle
        (fun he => hb (by rw [he]; cases d.1 <;> trivial))))
        (hty0.mono_r hΔ _ hle hty) hc
  | @pi o n A B d f x cs hty0 hent hin hev hout ihin ihout =>
    obtain ⟨k, s⟩ := d'
    obtain ⟨M, _, _, h2⟩ := hle.src_succ
    cases k with | zero => cases s <;> cases h2 | succ k
    cases s with | forallE A' B' d₂ f₂ => ?_ | _ => cases h2
    obtain ⟨hd₂, hf₂, hw₂⟩ := hty.forallE_inv rfl
    have hdle := hle.forallE_dom hΔ
    refine .pi (cs := cs) (hty0.mono_r hΔ _ hle hty) hent
      (fun p hp => ihin p hp hdle hd₂) (fun p hp => ?_) (fun p hp => hout p hp)
    -- the codes are lookups in the bigger graph
    obtain ⟨hPi, _, hcov⟩ := hle.forallE_decomp hΔ
      hw₂ (fun e he => .refl hw₂.2.2.2.1 e he)
    exact ((hev p hp).trans hΔ hcov).retype hPi.1
  | @sg o n A B d f x ps c hty0 hps hname hx hev hy ihx ihy
  obtain ⟨k, s⟩ := d'
  obtain ⟨M, _, _, h2⟩ := hle.src_succ
  cases k with | zero => cases s <;> cases h2 | succ k
  cases s with | sigma A' B' d₂ f₂ => ?_ | _ => cases h2
  obtain ⟨hd₂, hf₂, hw₂⟩ := hty.sigma_inv rfl
  have hdle := hle.sigma_dom hΔ
  obtain ⟨hlab, _, hcov⟩ := hle.sigma_decomp hΔ
    hw₂ (fun e he => .refl hw₂.2.2.2.1 e he)
  exact .sg (c := c) (hty0.mono_r hΔ _ hle hty) hps
    (fun p hp t ht => hlab.1.defeqDF (hname p hp t ht))
    (fun p hp => ihx p hp hdle hd₂)
    (fun p hp => ((hev p hp).trans hΔ hcov).retype hlab.1)
    (fun p hp => hy p hp)

/-- A code typed at a sort is hereditarily typed there: a sort filters. -/
theorem TShape.Named.of_isType {Δ : List Term} {x : TShape}
    (h : x.HasType Δ .type) : TShape.type.Named Δ x :=
  .base (fun h => h) h (HasType.wf h).1

theorem Shape.graph_join {n} {x y : Shape (n+1)} :
    (x.join y).graph = x.graph ++ y.graph ∨ (x.join y).graph = x.graph ∨
      (x.join y).graph = y.graph := by
  cases x <;> cases y <;>
    first | exact .inl rfl | exact .inr (.inl rfl) | exact .inr (.inr rfl)

theorem TShape.entries_join {n} {x y : Shape (n+1)} :
    (Shape.T (x.join y)).entries = (Shape.T x).entries ++ (Shape.T y).entries ∨
      (Shape.T (x.join y)).entries = (Shape.T x).entries ∨
      (Shape.T (x.join y)).entries = (Shape.T y).entries := by
  rcases Shape.graph_join (x := x) (y := y) with h | h | h <;>
    simp [entries, h]

/-- **Forgetting the name**: the index-free half of the merged notion,
which is what a consumer that does not care about the name wants.  One
induction, dropping the naming at every clause. -/
theorem TShape.Named.forget {Δ : List Term} {o} {d x : TShape}
    (h : d.Named Δ x o) : d.Named Δ x := by
  induction h with
  | base hnb hty hc => exact .base hnb hty hc.forget
  | @pi o n A B d f x cs hty hent hin hev _ _ ihout =>
    exact .pi hty hent hin hev (fun p hp => ihout p hp)
  | @sg o n A B d f x ps c hty hps _ _ hev _ ihx ihy =>
    exact .sg hty hps (fun _ _ => nofun) (fun p hp => ihx p hp) hev (fun p hp => ihy p hp)

/-- **The transport, on the merged notion.**  The name moves along a
definitional equality of the subject, given the code the shape is
hereditarily typed at and that code's own naming.  The code knows the
type, so `fstDF`/`sndDF`/`appDF` apply, and the sub-shapes are typed at
the code's sub-codes, which name the sub-types.

One induction on `Named`, which is legal because the index is a variable:
the conclusion maps it to the constant `t'`, so `none` goes to `none` and
`some t` to `some t'`. -/
theorem TShape.Named.defeq_mem {Δ : List Term} (hΔ : ⊢ Δ) {o} {d x : TShape}
    (h : d.Named Δ x o) {T t' : Term} (hC : d.WF Δ T)
    (ht : ∀ t ∈ o, Δ ⊢ t ≡ t' : T) : d.Named Δ x (o.map fun _ => t') := by
  induction h generalizing T t' with
  | @base o d x hnb hty hc =>
    cases o with | none => exact .base hnb hty hc.forget | some t
    -- a code-shaped subject: its type is a sort, read off the code, and
    -- the equation is then an equation of types.  At every other head
    -- the clause does not mention the index.
    have hcode {k : Nat} {j : Bool} (hd : d = Shape.T (n := k) (.sort j)) :
        x.WF Δ t' := by
      subst hd
      have hT : TyEq Δ T (.sort j) := WF.sort_iff.1 hC
      exact Shape.WF.conv hc ⟨_, (hT.defeqDF (ht t rfl)).symm⟩
    refine .base hnb hty ?_
    cases hty <;> first | exact .bot_mem | exact hc | exact hcode rfl
  | @pi o n A B d f x cs hty hent hin hev hout ihin ihout =>
    cases o with | none => exact .pi hty hent hin hev hout | some t
    have hT := hC.2.2.2.2
    have hwf := (HasType.wf hty).2
    obtain ⟨_, hA⟩ := hwf.1
    obtain ⟨_, hB⟩ := hwf.2.1
    have htm (p) (hp : p ∈ cs) : Δ ⊢ p.1.tm : A := by
      cases hty with
      | bot =>
        obtain rfl : cs = [] := by
          simpa only [entries_bot, List.map_eq_nil_iff] using hent.symm
        cases hp
      | refl =>
        obtain rfl : cs = [] := by
          simpa only [entries, Shape.graph, List.map_nil, List.map_eq_nil_iff]
            using hent.symm
        cases hp
      | @lam _ _ _ _ _ _ _ _ _ _ _ _ hwl _ _ _ _ _ hA₀A =>
        have hmem : p.1 ∈ cs.map (·.1) := List.mem_map.2 ⟨p, hp, rfl⟩
        rw [← hent] at hmem
        simp only [entries, Shape.graph, List.mem_map] at hmem
        obtain ⟨e, he, hpe⟩ := hmem
        exact hpe ▸ hA₀A.defeqDF (hwl.2.2.1.1 e he).2.1
    refine .pi hty hent (fun p hp => hin p hp) hev (fun p hp => ?_)
    refine ihout p hp (.lookup hΔ hwf.2.2.2.1
      hwf.2.2.2.1.canon hA hB (hev p hp)) ?_
    intro u hu
    simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hu
    subst hu
    exact (hT.defeqDF (ht t rfl)).appDF₀ hΔ (htm p hp)
  | @sg o n A B d f x ps c hty hps hname hx hev hy ihx ihy
  cases o with | none => exact .sg hty hps (fun _ _ => nofun) hx hev hy | some t
  have hT := hC.2.2.2.2
  have hwf := (HasType.wf hty).2
  obtain ⟨_, hA⟩ := hwf.1
  obtain ⟨_, hB⟩ := hwf.2.1
  have ht' : Δ ⊢ t ≡ t' : .sigma A B := hT.defeqDF (ht t rfl)
  have hfst : Δ ⊢ .fst t ≡ .fst t' : A := ht'.fstDF₀ hΔ
  have hsnd : Δ ⊢ .snd t ≡ .snd t' : B.inst (.fst t) := ht'.sndDF₀ hΔ
  refine .sg hty hps (fun p hp u hu => ?_) (fun p hp => ?_) hev (fun p hp => ?_)
  · simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hu
    subst hu
    exact (hname p hp t rfl).trans hfst
  · refine ihx p hp hwf.2.2.1 ?_
    intro u hu
    simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hu
    subst hu; exact hfst
  · refine ihy p hp (.lookup hΔ hwf.2.2.2.1
      hwf.2.2.2.1.canon hA hB (hev p hp)) ?_
    intro u hu
    simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hu
    subst hu
    exact (TyEq.inst hΔ hA hB (hname p hp t rfl).symm).defeqDF hsnd

/-- The transport at a name that is there. -/
theorem TShape.Named.defeq {Δ : List Term} (hΔ : ⊢ Δ) {T t t' : Term} {d x : TShape}
    (h : d.Named Δ x t) (hC : d.WF Δ T)
    (ht : Δ ⊢ t ≡ t' : T) : d.Named Δ x t' :=
  h.defeq_mem hΔ hC (by
    intro _ hu; simp only [Option.mem_def, Option.some.injEq] at hu; subst hu; exact ht)

/-- **Inverting `Named` at a Σ**: the first component is hereditarily typed
at the domain, and the second at the codomain read at the pair's own name
and first component. -/
theorem TShape.Named.sg_inv {Δ : List Term} {o} {n k} {A B A₀ a : Term} {d : Shape n}
    {f : ShapeFun n} {x y : Shape k}
    (h : (Shape.T (n := n+1) (.sigma A B d f)).Named Δ
      (Shape.T (n := k+1) (.pair A₀ a x y)) o) :
    ∃ c, d.T.Named Δ x.T (o.map .fst) ∧ TEvaluates Δ f A a x.T c ∧
      c.Named Δ y.T (o.map .snd) := by
  cases h with | base hnb => cases hnb trivial | @sg _ _ _ _ _ _ _ ps c hty hps _ hx hev hy
  have hps' : ps = some (a, x.T, y.T) := by simpa [pairParts, Shape.T] using hps.symm
  subst hps'
  exact ⟨c, hx _ rfl, hev _ rfl, hy _ rfl⟩

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
theorem TShape.HasType.join_at {Δ : List Term} (hΔ : ⊢ Δ) {n} {o} {y z : Shape n} {c : TShape}
    (hc : y.Compat Δ z) (hyD : c.Named Δ y.T o) (hzD : c.Named Δ z.T o) :
    (y.join z).T.HasType Δ c := by
  induction n generalizing o c with
  | zero =>
    have hy := hyD.hasType; have hz := hzD.hasType
    cases y with | bot => exact hz | sort r => cases z <;> exact hy
  | succ n ih
  have hy := hyD.hasType; have hz := hzD.hasType
  cases y with
  | bot => exact hz
  | sort | unit | nat | zero | id => cases z <;> first | exact hy | exact absurd hc (fun x => x)
  | succ v =>
    cases z with | bot => exact hy | succ v' => ?_ | _ => cases hc
    cases hy with | succ hv
    cases hz with | succ hv'
    exact .succ (hv.join hc hv')
  | forallE A B d f =>
    cases hy with | forallE hd hf hw
    exact join_sort hΔ rfl (.forallE hd hf hw) hz hc
  | sigma A B d f =>
    cases hy with | sigma hd hf hw
    exact join_sort hΔ rfl (.sigma hd hf hw) hz hc
  | refl =>
    cases z with | bot => exact hy | refl => ?_ | _ => cases hc
    cases hy with | refl hle hA
    cases hz with | refl
    exact .refl hle hA
  | lam A₀ g =>
    cases z with | bot => exact hy | lam A₀' g' => ?_ | _ => cases hc
    cases hy with | @lam _ n₀ n' _ _ f A B d g₀ hd hfo hwg hwPi hwg₀ hg hg₀ev hg₀ty hdom
    cases hz with | @lam _ n₀' _ _ _ _ _ _ _ g₀' _ _ hwg' _ hwg₀' hg' hg₀ev' hg₀ty' hdom'
    exact .lam hd hfo (hwg.join hΔ hc hwg') hwPi (join_gen_wf hwg₀ hwg₀')
      (join_gen_cover hΔ hwg₀ hwg₀' hg fun e he => (hg' e he).retype hc.1.symm)
      (join_gen_code hΔ hwg₀ hwg₀' hg₀ev hg₀ev') (join_gen_ty hΔ hg₀ty hg₀ty') hdom
  | pair A₀ a x₁ y₁
  cases z with | bot => exact hy | pair A₀' a' x₂ y₂ => ?_ | _ => cases hc
  cases hy with | @pair _ n' _ _ _ _ f A B d _ _ hd hfo hwp hwSg hxd _ _ _ hdom
  cases hz with | @pair _ _ _ _ _ _ _ _ _ _ _ _ _ _ hwp' _ _ _ _ _ hdom'
  obtain ⟨c₁, hdx₁, hev₁, hdy₁⟩ := hyD.sg_inv
  obtain ⟨c₂, hdx₂, hev₂, hdy₂⟩ := hzD.sg_inv
  -- the two codes are lookups at one query once the inputs are
  -- joined, so they join, and the components' typings move up
  have hjx := Shape.le_join hΔ hwp.2.2.2.1 hwp'.2.2.2.1 hc.2.2.1
  have hev₁' := hev₁.mono_inp hΔ (LE.T.2 hjx.1)
  have hev₂' := TEvaluates.label ⟨hdom.symm.trans hdom, (hdom.defeqDF hc.2.1).symm⟩
    (hev₂.mono_inp hΔ (LE.T.2 hjx.2))
  have hcc := TEvaluates.compat hΔ hwSg.2.2.2.1.2
    (WF.T.2 (hwp.2.2.2.1.join hΔ hc.2.2.1 hwp'.2.2.2.1)) hev₁' hev₂'
  refine .pair hd hfo (hwp.join hΔ hc hwp') hwSg (ih hc.2.2.1 hdx₁ hdx₂)
    (.refl (WF.T.2 (hwp.join hΔ hc hwp').2.2.2.1))
    (.join hcc hev₁' hev₂') ?_ hdom
  have hcty := TEvaluates.tHasType (c := .type) hΔ rfl
    (fun e he => hfo e he) (.join hcc hev₁' hev₂')
  have hjc := le_join hΔ
    (TEvaluates.wf hΔ (fun e he =>
      WF.T.2 (hwSg.2.2.2.1.1 e he).2.2.2.forget) hev₁')
    (TEvaluates.wf hΔ (fun e he =>
      WF.T.2 (hwSg.2.2.2.1.1 e he).2.2.2.forget) hev₂') hcc
  exact ih hc.2.2.2 (hdy₁.mono_r hΔ hjc.1 hcty)
    (hdy₂.mono_r hΔ hjc.2 hcty)

/-- The same at the total level: lift both subjects to the common level
and join there. -/
theorem TShape.HasType.join {Δ : List Term} (hΔ : ⊢ Δ) {y z c : TShape}
    {o} (hc : y.Compat Δ z) (hy : c.Named Δ y o) (hz : c.Named Δ z o) :
    (y.join z).HasType Δ c :=
  .join_at hΔ
    ((Compat.def (Nat.le_max_left ..) (Nat.le_max_right ..)).1 hc)
    (hy.lift_subject hΔ (Nat.le_max_left ..)) (hz.lift_subject hΔ (Nat.le_max_right ..))

/-- **`Named` is closed under the join**, at one level: the joined graph's
entries are the two graphs' entries, so the generators concatenate.  This
is what lets a slot grow — `dir`'s upper bound dominates the join, and
`Interp` is downward closed, so the join is an approximant too. -/
theorem TShape.Named.join_at {Δ : List Term} (hΔ : ⊢ Δ) {n} {o} {y z : Shape n} {d : TShape}
    (hc : y.Compat Δ z) (hy : d.Named Δ y.T o) (hz : d.Named Δ z.T o) :
    d.Named Δ (y.join z).T o := by
  induction n generalizing o d with
  | zero => cases y with | bot => exact hz | sort r => cases z <;> exact hy
  | succ n ih
  have hty : (y.join z).T.HasType Δ d := .join_at hΔ hc hy hz
  cases hy with
  | base hnb _ hcy => exact .base hnb hty (hcy.join_mem hΔ hc hz.wf)
  | @pi _ _ A B d₀ f _ csy htyy henty hiny hevy houty =>
    cases hz with
    | base hnb => cases hnb trivial
    | @pi _ _ _ _ _ _ _ csz htyz hentz hinz hevz houtz
    rcases entries_join (x := y) (y := z) with he | he | he
    · refine .pi (cs := csy ++ csz) hty (by rw [he, henty, hentz, List.map_append])
        (fun p hp => ?_) (fun p hp => ?_) (fun p hp => ?_) <;>
        rcases List.mem_append.1 hp with hp | hp
      exacts [hiny p hp, hinz p hp, hevy p hp, hevz p hp, houty p hp, houtz p hp]
    · exact .pi (cs := csy) hty (by rw [he, henty]) hiny hevy houty
    · exact .pi (cs := csz) hty (by rw [he, hentz]) hinz hevz houtz
  | @sg _ _ A B d₀ f _ psy cy htyy hpsy hnamey hxy hevy hyy
  cases hz with
  | base hnb => cases hnb trivial
  | @sg _ _ _ _ _ _ _ psz cz htyz hpsz hnamez hxz hevz hyz
  -- the join is a pair exactly when both sides are, and then the two
  -- codes are lookups at one query once the inputs are joined
  match y, z, hc, hpsy, hpsz, hty, htyy with
  | .bot, z, _, _, hpsz, hty, _ => exact .sg (ps := psz) (c := cz) hty hpsz hnamez hxz hevz hyz
  | .pair A₁ a₁ x₁ y₁, .bot, _, hpsy, _, hty, _ =>
    exact .sg (ps := psy) (c := cy) hty hpsy hnamey hxy hevy hyy
  | .pair A₁ a₁ x₁ y₁, .pair A₂ a₂ x₂ y₂, hc, hpsy, hpsz, hty, htyy =>
    obtain ⟨c₁, hdx₁, hev₁, hdy₁⟩ :=
      sg_inv (.sg (ps := psy) (c := cy) htyy hpsy hnamey hxy hevy hyy)
    obtain ⟨c₂, hdx₂, hev₂, hdy₂⟩ :=
      sg_inv (.sg (ps := psz) (c := cz) htyz hpsz hnamez hxz hevz hyz)
    cases htyy with | @pair _ _ _ _ _ _ _ _ _ _ _ _ hd hfo hwp hwSg _ _ _ _ hdomA
    have hwp' := (HasType.wf htyz).1
    have hjx := Shape.le_join hΔ hwp.2.2.2.1 hwp'.2.2.2.1 hc.2.2.1
    have hev₁' := hev₁.mono_inp hΔ (LE.T.2 hjx.1)
    have hev₂' := TEvaluates.label ⟨hdomA.symm.trans hdomA, (hdomA.defeqDF hc.2.1).symm⟩
      (hev₂.mono_inp hΔ (LE.T.2 hjx.2))
    have hcc := TEvaluates.compat hΔ hwSg.2.2.2.1.2
      (WF.T.2 (hwp.2.2.2.1.join hΔ hc.2.2.1 hwp'.2.2.2.1)) hev₁' hev₂'
    refine .sg (ps := some (a₁, (x₁.join x₂).T, (y₁.join y₂).T)) (c := c₁.join c₂)
      hty rfl (fun p hp => ?_) (fun p hp => ?_) (fun p hp => ?_) (fun p hp => ?_) <;>
      simp only [Option.mem_def, Option.some.injEq] at hp <;> subst hp
    · -- the joined pair's first component is `y`'s own, so `y` names it
      have hpsy' : psy = some (a₁, x₁.T, y₁.T) := by
        simpa [pairParts, Shape.T] using hpsy.symm
      subst hpsy'; exact hnamey (a₁, x₁.T, y₁.T) rfl
    · exact ih hc.2.2.1 hdx₁ hdx₂
    · exact .join hcc hev₁' hev₂'
    · have hcty := TEvaluates.tHasType (c := .type) hΔ rfl
        (fun e he => hfo e he) (.join hcc hev₁' hev₂')
      have hjc := le_join hΔ
        (TEvaluates.wf hΔ (fun e he =>
          WF.T.2 (hwSg.2.2.2.1.1 e he).2.2.2.forget) hev₁')
        (TEvaluates.wf hΔ (fun e he =>
          WF.T.2 (hwSg.2.2.2.1.1 e he).2.2.2.forget) hev₂') hcc
      exact ih hc.2.2.2 (hdy₁.mono_r hΔ hjc.1 hcty)
        (hdy₂.mono_r hΔ hjc.2 hcty)
  | .refl, z, hc, _, _, _, htyy =>
    cases htyy with | refl hleid
    obtain ⟨M, _, _, h2⟩ := hleid.src_succ
    cases h2
  | .sort _, z, hc, _, _, _, htyy | .unit _, z, hc, _, _, _, htyy
  | .nat, z, hc, _, _, _, htyy | .zero, z, hc, _, _, _, htyy
  | .succ _, z, hc, _, _, _, htyy
  | .id .., z, hc, _, _, _, htyy | .forallE .., z, hc, _, _, _, htyy
  | .sigma .., z, hc, _, _, _, htyy | .lam .., z, hc, _, _, _, htyy => cases htyy
  | .pair .., .sort _, hc, _, _, _, _ | .pair .., .unit _, hc, _, _, _, _
  | .pair .., .nat, hc, _, _, _, _ | .pair .., .zero, hc, _, _, _, _
  | .pair .., .succ _, hc, _, _, _, _ | .pair .., .refl, hc, _, _, _, _
  | .pair .., .id .., hc, _, _, _, _ | .pair .., .forallE .., hc, _, _, _, _
  | .pair .., .sigma .., hc, _, _, _, _ | .pair .., .lam .., hc, _, _, _, _ => cases hc

/-- The join, with the two sides at their own levels. -/
theorem TShape.Named.join {Δ : List Term} (hΔ : ⊢ Δ) {o} {y z d : TShape}
    (hc : y.Compat Δ z) (hy : d.Named Δ y o) (hz : d.Named Δ z o) :
    d.Named Δ (y.join z) o :=
  join_at hΔ
    ((Compat.def (Nat.le_max_left ..) (Nat.le_max_right ..)).1 hc)
    (hy.lift_subject hΔ (Nat.le_max_left ..)) (hz.lift_subject hΔ (Nat.le_max_right ..))

/-- Nothing below a non-binder code binds: the order pins the head. -/
theorem TShape.not_binder_of_le {Δ : List Term} {a c : TShape} (h : a.LE Δ c)
    (hc : ¬ c.IsBinder) : ¬ a.IsBinder := by
  intro hb
  obtain ⟨n, s⟩ := a
  obtain ⟨k, s'⟩ := c
  cases n with | zero => cases s <;> exact hb | succ n
  obtain ⟨M, hkM, hnM, h2⟩ := h.src_succ
  cases k with
  | zero =>
    match s, s' with
    | .forallE .., .bot | .forallE .., .sort _
    | .sigma .., .bot | .sigma .., .sort _ => cases h2
    | .bot, _ | .sort _, _ | .unit _, _ | .nat, _ | .zero, _ | .succ _, _
    | .refl, _ | .id .., _ | .lam .., _ | .pair .., _ => exact hb
  | succ k
  match s, s' with
  | .forallE .., .forallE .. | .sigma .., .sigma .. => exact hc trivial
  | .forallE .., .bot | .forallE .., .sort _ | .forallE .., .unit _
  | .forallE .., .nat | .forallE .., .zero | .forallE .., .succ _
  | .forallE .., .refl | .forallE .., .id .. | .forallE .., .lam ..
  | .forallE .., .pair .. | .forallE .., .sigma ..
  | .sigma .., .bot | .sigma .., .sort _ | .sigma .., .unit _
  | .sigma .., .nat | .sigma .., .zero | .sigma .., .succ _
  | .sigma .., .refl | .sigma .., .id .. | .sigma .., .lam ..
  | .sigma .., .pair .. | .sigma .., .forallE .. => cases h2
  | .bot, _ | .sort _, _ | .unit _, _ | .nat, _ | .zero, _ | .succ _, _
  | .refl, _ | .id .., _ | .lam .., _ | .pair .., _ => exact hb

/-- The two binder codes, separately: a Π-shape and a Σ-shape. -/
def TShape.IsPi : TShape → Prop
  | ⟨0, _⟩ => False
  | ⟨_+1, .forallE ..⟩ => True
  | ⟨_+1, _⟩ => False

def TShape.IsSigma : TShape → Prop
  | ⟨0, _⟩ => False
  | ⟨_+1, .sigma ..⟩ => True
  | ⟨_+1, _⟩ => False

theorem TShape.IsPi.not_sigma {p : TShape} (h : p.IsPi) : ¬ p.IsSigma := by
  obtain ⟨n, s⟩ := p
  cases n with | zero => cases h | succ n
  cases s <;> first | exact fun x => x | exact absurd h (fun x => x)

theorem TShape.IsPi.not_bot {p : TShape} (h : p.IsPi) : p.2 ≠ .bot := by
  obtain ⟨n, s⟩ := p
  cases n with | zero => cases h | succ n
  cases s <;> first | exact absurd h (fun x => x) | simp [Shape.bot]

theorem TShape.IsSigma.not_bot {p : TShape} (h : p.IsSigma) : p.2 ≠ .bot := by
  obtain ⟨n, s⟩ := p
  cases n with | zero => cases h | succ n
  cases s <;> first | exact absurd h (fun x => x) | simp [Shape.bot]

theorem TShape.IsPi.isBinder {p : TShape} (h : p.IsPi) : p.IsBinder := by
  obtain ⟨n, s⟩ := p
  cases n <;> cases s <;> first | exact h | exact trivial

theorem TShape.IsSigma.isBinder {p : TShape} (h : p.IsSigma) : p.IsBinder := by
  obtain ⟨n, s⟩ := p
  cases n <;> cases s <;> first | exact h | exact trivial

/-- Below a Π-shape there are only `⊥` and Π-shapes: the order pins the
head, which is what lets an approximant of a Π type be analysed. -/
theorem TShape.isPi_or_bot_of_le {Δ : List Term} {p q : TShape} (h : p.LE Δ q)
    (hq : q.IsPi) : p.2 = .bot ∨ p.IsPi := by
  obtain ⟨n, s⟩ := p
  obtain ⟨k, s'⟩ := q
  cases k with | zero => cases hq | succ k
  cases s' with | forallE => ?_ | _ => cases hq
  obtain ⟨M, hkM, hnM, h2⟩ := h.at_succ
  cases n with
  | zero => cases s with | bot => exact .inl rfl | sort => cases h2
  | succ n
  cases s with | bot => exact .inl rfl | forallE => exact .inr trivial | _ => cases h2

/-- **The level-free lookup, read back at the graph's own level**:
`ShapeFun.Eval.toT`'s converse, up to the order.  A `TEvaluates` value is
below one the level-indexed lookup reaches, which is all an order
comparison between λ-shapes needs, since `Eval` is closed under `lower`.
The `join` case is where the graph's coherence comes in
(`ShapeFun.Eval.compat`). -/
theorem TEvaluates.toEval {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a : Term}
    {x : Shape n} (hwf : f.WF Δ A oB (@Shape.WF Δ _)) (hx : x.WF Δ)
    {c : TShape} (h : TEvaluates Δ f A a x.T c) :
    ∃ c' : Shape n, c.LE Δ c'.T ∧ f.Eval Δ (Shape.LE Δ) A a x c' := by
  induction h with
  | bot => exact ⟨.bot, TShape.bot_le' rfl, .bot⟩
  | entry e he hlab hin =>
    refine ⟨e.out, .refl (TShape.WF.T.2 (hwf.1 e he).2.2.2.forget), ?_⟩
    exact .entry e he hlab (TShape.LE.T.1 hin)
  | lower hle _ ih =>
    obtain ⟨c', hc', hev⟩ := ih
    exact ⟨c', hle.trans hΔ hc', hev⟩
  | join hc _ _ ih₁ ih₂
  obtain ⟨c₁, hc₁, hev₁⟩ := ih₁
  obtain ⟨c₂, hc₂, hev₂⟩ := ih₂
  have hw₁ := hev₁.wf hΔ (fun e he => (hwf.1 e he).2.2.2.forget)
  have hw₂ := hev₂.wf hΔ (fun e he => (hwf.1 e he).2.2.2.forget)
  have hcc : c₁.Compat Δ c₂ := hev₁.compat hΔ hwf.2 hx.coherent hev₂
  obtain ⟨hj₁, hj₂⟩ := Shape.le_join hΔ hw₁ hw₂ hcc
  exact ⟨c₁.join c₂,
    TShape.join_le hΔ (hc₁.trans hΔ (TShape.LE.T.2 hj₁))
      (hc₂.trans hΔ (TShape.LE.T.2 hj₂)),
    .join hcc hev₁ hev₂⟩

/-- A shape that dominates a λ-shape is one: the order pins the head
upward too. -/
def TShape.IsLam : TShape → Prop
  | ⟨0, _⟩ => False
  | ⟨_+1, .lam ..⟩ => True
  | ⟨_+1, _⟩ => False

theorem TShape.isLam_of_le {Δ : List Term} {x y : TShape} (h : x.LE Δ y)
    (hx : x.IsLam) : y.IsLam := by
  obtain ⟨n, s⟩ := x
  obtain ⟨k, s'⟩ := y
  cases n with | zero => cases hx | succ n
  cases s with | lam => ?_ | _ => cases hx
  obtain ⟨M, hkM, hnM, h2⟩ := h.src_succ
  cases k with | zero => cases s' <;> cases h2 | succ k
  cases s' with | lam => exact trivial | _ => cases h2

/-- The Σ twin of `TShape.isPi_or_bot_of_le`. -/
theorem TShape.isSigma_or_bot_of_le {Δ : List Term} {p q : TShape} (h : p.LE Δ q)
    (hq : q.IsSigma) : p.2 = .bot ∨ p.IsSigma := by
  obtain ⟨n, s⟩ := p
  obtain ⟨k, s'⟩ := q
  cases k with | zero => cases hq | succ k
  cases s' with | sigma => ?_ | _ => cases hq
  obtain ⟨M, hkM, hnM, h2⟩ := h.at_succ
  cases n with
  | zero => cases s with | bot => exact .inl rfl | sort => cases h2
  | succ n
  cases s with | bot => exact .inl rfl | sigma => exact .inr trivial | _ => cases h2

/-! ## The slot condition

A slot is one notion applied twice.  `Named` says a shape is hereditarily
typed at a code and names a term; a *slot* is that for the value, together
with the same for its code -- read at a sort, where `Named` degenerates to
the code naming its type.  There is no third conjunct and no bundle: the
naming travels inside the hereditary typing, so moving a name along a
definitional equality of the subject takes nothing beyond what the slot
already holds. -/

/-- `x` is hereditarily typed at the code `d` and names the term `t`, and
`d` names the type `T`. -/
def TShape.Slot (Δ : List Term) (T : Term) (d : TShape) (t : Term) (x : TShape) : Prop :=
  Named Δ d x t ∧ WF Δ d T

/-- **The transport, with nothing to pass in.** -/
theorem TShape.Slot.defeq {Δ : List Term} (hΔ : ⊢ Δ) {T t t' : Term} {d x : TShape}
    (h : d.Slot Δ T t x) (ht : Δ ⊢ t ≡ t' : T) : d.Slot Δ T t' x :=
  ⟨h.1.defeq hΔ h.2 ht, h.2⟩

/-- **The stage moves both halves at once**, which is the point of
bundling them: `Interp`'s `pair`, `Y` and `tr` clauses each hold a slot,
and the substitution lemma moves it without naming its parts. -/
theorem TShape.Slot.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {T t : Term} {d x : TShape}
    (h : d.Slot Δ T t x) :
    (d.subst τ).Slot Θ (T.subst τ) (t.subst τ) (x.subst τ) :=
  ⟨h.1.subst hΘ W, h.2.subst hΘ W⟩

/-- Conversion in the type: the code's naming is the only field that sees it. -/
theorem TShape.Slot.conv {Δ : List Term} {T T' t : Term} {d x : TShape}
    (h : d.Slot Δ T t x) (hT : TyEq Δ T' T) : d.Slot Δ T' t x :=
  ⟨h.1, Shape.WF.conv h.2 hT⟩
