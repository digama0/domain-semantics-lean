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

theorem Shape.IsNumeral.lower {Δ : List Term} {n} {v v' : Shape n}
    (hle : Shape.LE Δ v' v) (h : Shape.IsNumeral v) : Shape.IsNumeral v' := by
  induction h with
  | bot => cases Shape.le_bot_iff.1 hle; exact .bot
  | zero => match v' with | .bot => exact .bot | .zero => exact .zero
  | succ _ ih => match v' with | .bot => exact .bot | .succ w' => exact .succ (ih hle)

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
    {x : TShape} (hA : TyEq Δ A A') :
    ∀ {c : TShape}, TEvaluates Δ f A a x c → TEvaluates Δ f A' a x c := by
  intro c h
  induction h with
  | bot => exact .bot
  | entry e he hl hin => exact .entry e he (hl.retype hA) hin
  | lower hle _ ih => exact .lower hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- Two lookups at one query in one coherent graph are compatible, so
their join exists.  `Evaluates.compat` at the total level, with the same
double induction. -/
theorem TEvaluates.compat {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a : Term}
    {x : TShape} (hf : ShapeFun.Compat Shape.Compat Δ A f f) (hwx : TShape.WF Δ x)
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
    (hf : ∀ e ∈ f, TEvaluates Δ f' A e.tm e.inp.T e.out.T) :
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
    {f : ShapeFun n} (hw : ShapeFun.WFE (Shape.WF Δ) f) {A a : Term} {x : TShape} :
    ∀ {c : TShape}, TEvaluates Δ f A a x c →
      TEvaluates Δ (ShapeFun.lift (Shape.lift m) f) A a x c := by
  intro c h
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
    (hw : ShapeFun.WF Δ Ty (Shape.WF Δ) f) :
    ∀ e ∈ f, TEvaluates Δ f Ty e.tm e.inp.T e.out.T := by
  intro e he
  obtain ⟨⟨u, hty⟩, htm, hin, _⟩ := hw.1 e he
  exact .entry e he (LabelEq.refl hty htm) (TShape.LE.T.2 (Shape.LE.refl hin))

/-- Entrywise coverage survives lifting the covered graph: `lift` moves
neither an input nor an output, as a `TShape`.  Used where a clause's graph
is compared at a level above both. -/
theorem TEvaluates.lift_cover {Δ : List Term} (hΔ : ⊢ Δ) {n n'} {g : ShapeFun n}
    {f' : ShapeFun n'} {k} (hk : n ≤ k) (hw : ShapeFun.WF Δ Ty (Shape.WF Δ) g)
    (hg : ∀ e ∈ g, TEvaluates Δ f' Ty e.tm e.inp.T e.out.T) :
    ∀ e ∈ ShapeFun.lift (Shape.lift k) g,
      TEvaluates Δ f' Ty e.tm e.inp.T e.out.T := by
  intro e he
  obtain ⟨e₀, he₀, rfl⟩ := ShapeFun.mem_lift.1 he
  have hwe := hw.1 e₀ he₀
  exact .lower (TShape.LE.lift_le hΔ (m := e₀.out.T) hk hwe.2.2.2)
    (TEvaluates.mono_inp hΔ (TShape.LE.le_lift hΔ (m := e₀.inp.T) hk hwe.2.2.1)
      (hg e₀ he₀))

/-- And back: coverage of the lift is coverage of the graph. -/
theorem TEvaluates.lower_cover {Δ : List Term} (hΔ : ⊢ Δ) {n n'} {g : ShapeFun n}
    {f' : ShapeFun n'} {k} (hk : n ≤ k) (hw : ShapeFun.WF Δ Ty (Shape.WF Δ) g)
    (hg : ∀ e ∈ ShapeFun.lift (Shape.lift k) g,
      TEvaluates Δ f' Ty e.tm e.inp.T e.out.T) :
    ∀ e ∈ g, TEvaluates Δ f' Ty e.tm e.inp.T e.out.T := by
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
    (hw : ShapeFun.WF Δ Ty (Shape.WF Δ) g')
    (hcov : ∀ e ∈ ShapeFun.lift (Shape.lift k) g',
      ShapeFun.Eval Δ (Shape.LE Δ) g Ty e.tm e.inp e.out)
    (hg : ∀ e ∈ g, TEvaluates Δ f' Ty e.tm e.inp.T e.out.T) :
    ∀ e ∈ g', TEvaluates Δ f' Ty e.tm e.inp.T e.out.T := by
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
    (hf' : ∀ e ∈ f', TEvaluates Δ f'' A' e.tm e.inp.T e.out.T) :
    PiLabelEq Δ A B A' B' ∧ TShape.LE Δ d.T d'.T ∧
      ∀ e ∈ f, TEvaluates Δ f'' A e.tm e.inp.T e.out.T := by
  obtain ⟨M, hn'M, hnM, h2⟩ := TShape.LE.at_succ h
  have hn : n ≤ M := Nat.le_of_succ_le_succ hnM
  have hA : TyEq Δ A' A := TyEq.symm h2.1.1
  exact ⟨h2.1, (TShape.LE.def hΔ hn hn'M).2 h2.2.1,
    TEvaluates.of_cover_lift hΔ hn hw.2.2.2 h2.2.2.1
      (TEvaluates.lift_cover hΔ hn'M (hw'.2.2.2.retype hA)
        fun e he => (hf' e he).retype hA)⟩

/-- Σ-decomposition; the clause is the same as Π's. -/
theorem TShape.LE.sigma_decomp {Δ : List Term} (hΔ : ⊢ Δ) {n n' k}
    {A B A' B' : Term} {d : Shape n} {f : ShapeFun n} {d' : Shape n'}
    {f' : ShapeFun n'} {f'' : ShapeFun k}
    (h : TShape.LE Δ (Shape.T (n := n+1) (.sigma A B d f))
      (Shape.T (n := n'+1) (.sigma A' B' d' f')))
    (hw : Shape.WF (n := n+1) Δ (.sigma A B d f))
    (hw' : Shape.WF (n := n'+1) Δ (.sigma A' B' d' f'))
    (hf' : ∀ e ∈ f', TEvaluates Δ f'' A' e.tm e.inp.T e.out.T) :
    PiLabelEq Δ A B A' B' ∧ TShape.LE Δ d.T d'.T ∧
      ∀ e ∈ f, TEvaluates Δ f'' A e.tm e.inp.T e.out.T := by
  obtain ⟨M, hn'M, hnM, h2⟩ := TShape.LE.at_succ h
  have hn : n ≤ M := Nat.le_of_succ_le_succ hnM
  have hA : TyEq Δ A' A := TyEq.symm h2.1.1
  exact ⟨h2.1, (TShape.LE.def hΔ hn hn'M).2 h2.2.1,
    TEvaluates.of_cover_lift hΔ hn hw.2.2.2 h2.2.2.1
      (TEvaluates.lift_cover hΔ hn'M (hw'.2.2.2.retype hA)
        fun e he => (hf' e he).retype hA)⟩

/-- λ-decomposition: a λ-shape's graph is covered by any bigger one's, and
the non-degeneracy conjuncts are about the smaller graph alone, so they
carry no information downwards. -/
theorem TShape.LE.lam_decomp {Δ : List Term} (hΔ : ⊢ Δ) {n n' k} {A A' : Term}
    {g : ShapeFun n} {g' : ShapeFun n'} {f'' : ShapeFun k}
    (h : TShape.LE Δ (Shape.T (n := n+1) (.lam A g)) (Shape.T (n := n'+1) (.lam A' g')))
    (hw : Shape.WF (n := n+1) Δ (.lam A g)) (hw' : Shape.WF (n := n'+1) Δ (.lam A' g'))
    (hg' : ∀ e ∈ g', TEvaluates Δ f'' A' e.tm e.inp.T e.out.T) :
    ∀ e ∈ g, TEvaluates Δ f'' A e.tm e.inp.T e.out.T := by
  obtain ⟨M, hn'M, hnM, h2⟩ := TShape.LE.at_succ h
  have hA : TyEq Δ A' A := TyEq.symm h2.2.2.2.1
  exact TEvaluates.of_cover_lift hΔ (Nat.le_of_succ_le_succ hnM) hw.2.2.1 h2.1.1
    (TEvaluates.lift_cover hΔ hn'M (hw'.2.2.1.retype hA) fun e he => (hg' e he).retype hA)

/-- The lookup only sees its query label up to definitional equality. -/
theorem TEvaluates.label {Δ : List Term} {n} {f : ShapeFun n} {A a A' a' : Term}
    {x c : TShape} (hlab : LabelEq Δ A a A' a') (H : TEvaluates Δ f A a x c) :
    TEvaluates Δ f A' a' x c := by
  induction H with
  | bot => exact .bot
  | entry e he hl hin => exact .entry e he (LabelEq.right (hl.trans hlab)) hin
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
    exact .entry ⟨e.tm.subst τ, e.inp.subst τ, e.out.subst τ⟩
      (ShapeFun.mem_subst.2 ⟨e, he, rfl⟩) (hl.subst hΘ W) (TShape.LE.subst hΘ W hin)
  | lower hle _ ih => exact .lower (TShape.LE.subst hΘ W hle) ih
  | join hc _ _ ih₁ ih₂ =>
    exact TShape.join_subst ▸ TEvaluates.join (TShape.Compat.subst hΘ W hc) ih₁ ih₂

/-- Pair-decomposition: both components back at their own canonical
level, with the label equalities. -/
theorem TShape.LE.pair_decomp {Δ : List Term} (hΔ : ⊢ Δ) {j n} {A A' a a' : Term}
    {x₂ y₂ : Shape j} {x y : Shape n}
    (h : TShape.LE Δ (Shape.T (n := j+1) (ShapeS.pair A a x₂ y₂))
      (Shape.T (n := n+1) (ShapeS.pair A' a' x y))) :
    TyEq Δ A A' ∧ (Δ ⊢ a ≡ a' : A) ∧ TShape.LE Δ x₂.T x.T ∧ TShape.LE Δ y₂.T y.T := by
  obtain ⟨M, hnM, hjM, h2⟩ := TShape.LE.at_succ h
  have hj : j ≤ M := Nat.le_of_succ_le_succ hjM
  exact ⟨h2.2.2.2.1, h2.2.2.2.2, (TShape.LE.def hΔ hj hnM).2 h2.1,
    (TShape.LE.def hΔ hj hnM).2 h2.2.1⟩

/-- Lifting a shape's level does not move it in the order: the `TShape`
it names is the same one. -/
theorem TShape.lift_le_self {Δ : List Term} (hΔ : ⊢ Δ) {n k} (h : n ≤ k) {x : Shape n}
    (hw : Shape.WF Δ x) : TShape.LE Δ (Shape.T (Shape.lift k x)) x.T := by
  refine (TShape.LE.def hΔ (k := max k n) (Nat.le_max_left ..) (Nat.le_max_right ..)).2 ?_
  rw [Shape.lift_lift h]
  exact Shape.LE.refl ((Shape.lift_wf (Nat.le_max_right k n)).2 hw)

theorem TShape.self_le_lift {Δ : List Term} (hΔ : ⊢ Δ) {n k} (h : n ≤ k) {x : Shape n}
    (hw : Shape.WF Δ x) : TShape.LE Δ x.T (Shape.T (Shape.lift k x)) := by
  refine (TShape.LE.def hΔ (k := max k n) (Nat.le_max_right ..) (Nat.le_max_left ..)).2 ?_
  rw [Shape.lift_lift h]
  exact Shape.LE.refl ((Shape.lift_wf (Nat.le_max_right k n)).2 hw)

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
  -- code.  Join-closure is what it costs, and `TShape.Dom`'s `sg`
  -- clause, which reads the code at the first component itself, is what
  -- supplies it where it is needed
  | pair {n n'} {A₀ a : Term} {x y : Shape n} {f : ShapeFun n'}
      {A B : Term} {d : Shape n'} {xd c : TShape} :
    HasType Δ d.T .type →
    (∀ e ∈ f, HasType Δ e.out.T .type) →
    Shape.WF (n := n+1) Δ (.pair A₀ a x y) →
    Shape.WF (n := n'+1) Δ (.sigma A B d f) →
    HasType Δ x.T d.T →
    TShape.LE Δ x.T xd →
    TEvaluates Δ f A a xd c →
    HasType Δ y.T c →
    TyEq Δ A₀ A →
    HasType Δ (Shape.T (n := n+1) (.pair A₀ a x y)) (Shape.T (n := n'+1) (.sigma A B d f))
  | refl {a n k} {A x y : Term} :
    TShape.LE Δ (Shape.T (n := k+1) (.id true A x y)) a →
    HasType Δ a .type → HasType Δ (Shape.T (n := n+1) .refl) a

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
  | pair hd hf _ hwSg _ _ _ _ _ => exact .sigma hd hf hwSg
  | refl _ hA _ => exact hA

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
  | refl hc _ _ =>
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
          (fun e he => (TEvaluates.trans hΔ hcov (hg₀ev e he)).retype hPi.1) hg₀ty
          (hdom.trans hPi.1)
      | _ => exact absurd h2 (fun x => x)
  | pair hd hf hwp hwSg hxd hxle hev hyty hdom _ _ ihxd ihy =>
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
        refine .pair hd' hf' hwp hw' (ihxd d'.T hdd hd') hxle ?_ hyty (hdom.trans hSg.1)
        exact TEvaluates.retype hSg.1 (TEvaluates.trans hΔ hcov hev)
      | _ => exact absurd h2 (fun x => x)
  | refl hc _ _ => exact fun _ h hA' => .refl (hc.trans hΔ h) hA'

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
  | refl _ _ ih => exact ⟨trivial, ih.1⟩

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
  | pair hd hf hwp hwSg hxd hxle hev hyty hdom _ _ ihxd ihy =>
    intro k hk; obtain ⟨k, rfl⟩ := succ_of hk
    have hn := Nat.le_of_succ_le_succ hk
    exact .pair hd hf ((Shape.lift_wf (Nat.succ_le_succ hn)).2 hwp) hwSg
      (ihxd hn) (TShape.LE.trans hΔ (TShape.lift_le_self hΔ hn hwp.2.2.2.1) hxle) hev
      (ihy hn) hdom
  | refl hc hA _ =>
    intro k hk; obtain ⟨k, rfl⟩ := succ_of hk
    exact .refl hc hA

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
    | refl =>
      cases H with | refl hc hA
      exact .refl hc hA
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
    | pair A₀ a x y =>
      cases H with | pair hd hf hwp hwSg hxd hxle hev hyty hdom
      have hwp' := (Shape.lift_wf (s := ShapeS.pair A₀ a x y) hk).1 hwp
      exact .pair hd hf hwp' hwSg (ih hk' hxd)
        (TShape.LE.trans hΔ (TShape.self_le_lift hΔ hk' hwp'.2.2.2.1) hxle)
        hev (ih hk' hyty) hdom

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
  | refl hc _ _ =>
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
        (⟨p.1.tm.subst τ, p.1.inp.subst τ, p.1.out.subst τ⟩, p.2.subst τ))
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
  | pair _ _ hwp hwSg _ hxle hev _ hdom ihd ihf ihxd ihy =>
    simp only [TShape.subst_T] at *
    exact .pair ihd (fun e he => by
        obtain ⟨e₀, he₀, rfl⟩ := ShapeFun.mem_subst.1 he
        exact ihf e₀ he₀)
      (Shape.WF.subst hΘ W hwp) (Shape.WF.subst hΘ W hwSg) ihxd
      (TShape.LE.subst hΘ W hxle) (TEvaluates.subst hΘ W hev) ihy (hdom.subst hΘ W)
  | refl hc _ ih =>
    simp only [TShape.subst_T] at *
    exact .refl (TShape.LE.subst hΘ W hc) ih

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
    | refl =>
      cases z with
      | refl =>
        cases hy with | refl hcg _
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
    | refl hc _ =>
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
          (TShape.LE.lam_decomp hΔ h hwg' hwg hg) hg₀ev hg₀ty (TyEq.trans h2.2.2.2.1 hdom)
      | _ => exact absurd h2 (fun x => x)
  | pair hd hf hwp hwSg hxd hxle hev hyty hdom _ _ ihxd ihy =>
    intro m' h
    obtain ⟨j, s⟩ := m'
    obtain ⟨M, _, hjM, h2⟩ := TShape.LE.at_succ h
    cases j with
    | zero => cases s <;> first | exact .bot (.sigma hd hf hwSg) | exact absurd h2 (fun x => x)
    | succ j =>
      cases s with
      | bot => exact .bot (.sigma hd hf hwSg)
      | pair A' a' x' y' =>
        have hwp' : Shape.WF (n := j+1) Δ (.pair A' a' x' y') :=
          (Shape.lift_wf hjM).1 (Shape.LE.wf h2)
        obtain ⟨hA', ha', hx', hy'⟩ := TShape.LE.pair_decomp hΔ h
        refine .pair hd hf hwp' hwSg (ihxd hx') (TShape.LE.trans hΔ hx' hxle) ?_
          (ihy hy') (hA'.trans hdom)
        exact TEvaluates.label ⟨hdom.symm.trans hdom,
          (hA'.trans hdom).choose_spec.defeqDF ha'.symm⟩ hev
      | _ => exact absurd h2 (fun x => x)
  | refl hc hA _ =>
    exact fun {m'} h => by
      obtain ⟨j, s⟩ := m'
      obtain ⟨M, _, hjM, h2⟩ := TShape.LE.at_succ h
      cases j with
      | zero => cases s <;> first | exact .bot hA | exact absurd h2 (fun x => x)
      | succ j =>
        cases s with
        | bot => exact .bot hA
        | refl =>
          exact .refl hc hA
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
  | refl hc _ =>
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
  g₀.map fun p => ((⟨p.1.tm, p.1.inp.lift m, p.1.out.lift m⟩ : Entry (Shape m)), p.2)

theorem TShape.liftGen_map {n m : Nat} {g₀ : List (Entry (Shape n) × TShape)} :
    (TShape.liftGen m g₀).map (·.1) = ShapeFun.lift (Shape.lift m) (g₀.map (·.1)) := by
  simp [TShape.liftGen, ShapeFun.lift, List.map_map, Function.comp_def]

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
    exact TEvaluates.lift_graph hΔ (Nat.le_max_left ..) hw (hg e h)
  | .inr h =>
    refine TEvaluates.mono_graph (fun d hd => List.mem_append.2 (.inr hd)) ?_
    rw [TShape.liftGen_map]
    exact TEvaluates.lift_graph hΔ (Nat.le_max_right ..) hw' (hg' e h)

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
  | refl hc _ => exact absurd (TShape.le_bot hΔ ha hc) (fun h => by cases h)

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
  | refl _ _ => exact absurd ha (fun h => by cases h)

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
  | refl hc _ _ =>
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
    | refl _ _ =>
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
    (Shape.T (n := n) Shape.bot).pairParts = none := by cases n <;> rfl

/-- A code that binds: the two whose decoder does more than filter. -/
def TShape.IsBinder : TShape → Prop
  | ⟨0, _⟩ => False
  | ⟨_+1, .forallE ..⟩ => True
  | ⟨_+1, .sigma ..⟩ => True
  | ⟨_+1, _⟩ => False

/-- Membership in a mapped `Option`, in the form the `Dom` proofs use. -/
theorem Option.exists_of_mem_map {α β : Type} {o : Option α} {f : α → β} {b : β}
    (h : b ∈ o.map f) : ∃ a ∈ o, b = f a := by
  cases o with
  | none => exact absurd h (by simp)
  | some a => exact ⟨a, rfl, by simpa using h.symm⟩

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
    (∀ p ∈ cs, TEvaluates Δ f A p.1.tm p.1.inp p.2) →
    (∀ p ∈ cs, Dom Δ p.2 p.1.out) →
    Dom Δ (Shape.T (n := n+1) (ShapeS.forallE A B d f)) x
  /-- At a Σ: the first component hereditarily typed at the domain, the
  second at the codomain read at the pair's own name and first component.
  Read at `x` itself, where `HasType` reads a *dominator* of it: that is
  what keeps `Dom` closed under joins (§4.7e), and `Dom`, unlike
  `HasType`, is only ever used upward, so it needs no lower-closure. -/
  | sg {n} {A B : Term} {d : Shape n} {f : ShapeFun n} {x : TShape}
      {ps : Option (Term × TShape × TShape)} {c : TShape} :
    TShape.HasType Δ x (Shape.T (n := n+1) (ShapeS.sigma A B d f)) →
    x.pairParts = ps →
    (∀ p ∈ ps, Dom Δ d.T p.2.1) →
    (∀ p ∈ ps, TEvaluates Δ f A p.1 p.2.1 c) →
    (∀ p ∈ ps, Dom Δ c p.2.2) →
    Dom Δ (Shape.T (n := n+1) (ShapeS.sigma A B d f)) x

theorem TShape.Dom.hasType {Δ : List Term} {d x : TShape} (h : TShape.Dom Δ d x) :
    TShape.HasType Δ x d := by cases h <;> assumption

@[simp] theorem TShape.entries_bot {n} : (Shape.T (n := n) Shape.bot).entries = [] := by
  cases n <;> rfl

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
      exact .sg (ps := none) (c := TShape.bot) h (by simp) (by simp) (by simp) (by simp)
    | .bot | .sort _ | .unit _ | .nat | .zero | .succ _ | .refl | .id _ _ _ _
    | .lam _ _ | .pair _ _ _ _ => exact .base (fun h => h) h

/-- The same, for a subject that is `⊥` only up to its level. -/
theorem TShape.Dom.bot_subject {Δ : List Term} {d x : TShape} (hx : x.2 = Shape.bot)
    (h : TShape.HasType Δ x d) : TShape.Dom Δ d x := by
  obtain ⟨n, s⟩ := x
  cases n with
  | zero => cases s with
    | bot => exact TShape.Dom.bot h
    | sort r => exact absurd hx (by simp [Shape.bot])
  | succ n =>
    cases s <;> first
      | exact TShape.Dom.bot (n := n+1) h
      | exact absurd hx (by simp [Shape.bot])

@[simp] theorem TShape.entries_subst {x : TShape} {τ : Subst} :
    (x.subst τ).entries = x.entries.map
      (fun e => ⟨e.tm.subst τ, e.inp.subst τ, e.out.subst τ⟩) := by
  obtain ⟨n, s⟩ := x
  cases n with
  | zero => cases s <;> rfl
  | succ n =>
    cases s <;>
      simp [TShape.entries, TShape.subst, Shape.graph, Shape.subst, ShapeFun.subst,
        List.map_map, Function.comp_def, Shape.T]

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
        (⟨p.1.tm.subst τ, p.1.inp.subst τ, p.1.out.subst τ⟩, p.2.subst τ))
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
  | @sg n A B d f x ps c hty hps _ hev _ ihx ihy =>
    refine .sg (ps := ps.map fun p => (p.1.subst τ, p.2.1.subst τ, p.2.2.subst τ))
      (c := c.subst τ)
      (by simpa [Shape.subst] using TShape.HasType.subst hΘ W hty) ?_ ?_ ?_ ?_
    · rw [← hps]; cases x with | mk k s => cases k <;> [skip; cases s] <;>
        simp [TShape.pairParts, TShape.subst, Shape.subst]
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := Option.exists_of_mem_map hp
      exact ihx q hq
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := Option.exists_of_mem_map hp
      exact TEvaluates.subst hΘ W (hev q hq)
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := Option.exists_of_mem_map hp
      exact ihy q hq

theorem TShape.entries_lift {x : TShape} {k} (hk : x.1 ≤ k + 1) :
    (x.lift (k+1)).entries = x.entries.map
      (fun e => ⟨e.tm, e.inp.lift k, e.out.lift k⟩) := by
  obtain ⟨n, s⟩ := x
  cases n with
  | zero => cases s <;> rfl
  | succ n =>
    cases s <;>
      simp [TShape.entries, TShape.lift, Shape.graph, Shape.lift, ShapeFun.lift,
        List.map_map, Function.comp_def, Shape.T]

theorem TShape.pairParts_lift {x : TShape} {k} (hk : x.1 ≤ k + 1) :
    (x.lift (k+1)).pairParts =
      x.pairParts.map (fun p => (p.1, p.2.1.lift k, p.2.2.lift k)) := by
  obtain ⟨n, s⟩ := x
  cases n with
  | zero => cases s <;> rfl
  | succ n => cases s <;> simp [TShape.pairParts, TShape.lift, Shape.lift, Shape.T]

theorem TShape.pairParts_lift_zero {x : TShape} : (x.lift 0).pairParts = none := by
  obtain ⟨n, s⟩ := x
  cases n <;> [cases s; skip] <;> rfl

theorem TShape.entries_level {x : TShape} {e : Entry TShape} (he : e ∈ x.entries) :
    e.inp.1 + 1 = x.1 ∧ e.out.1 + 1 = x.1 := by
  obtain ⟨n, s⟩ := x
  cases n with
  | zero => simp [TShape.entries] at he
  | succ n =>
    simp only [TShape.entries, List.mem_map] at he
    obtain ⟨e₀, _, rfl⟩ := he
    exact ⟨rfl, rfl⟩

theorem TShape.pairParts_level {x : TShape} {ps} (hps : x.pairParts = ps)
    {p} (hp : p ∈ ps) : p.2.1.1 + 1 = x.1 ∧ p.2.2.1 + 1 = x.1 := by
  obtain ⟨n, s⟩ := x
  cases n with
  | zero => subst hps; exact absurd hp (by simp [TShape.pairParts])
  | succ n =>
    subst hps
    match s with
    | .pair _ _ _ _ => simp [TShape.pairParts] at hp; subst hp; exact ⟨rfl, rfl⟩
    | .bot | .sort _ | .unit _ | .nat | .zero | .succ _ | .refl | .id _ _ _ _
    | .lam _ _ | .forallE .. | .sigma .. =>
      exact absurd hp (by simp [TShape.pairParts])

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
          (⟨p.1.tm, p.1.inp.lift k, p.1.out.lift k⟩, p.2))
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
  | @sg n A B d f x ps c hty hps hx hev hy ihx ihy =>
    intro k hk
    match k, hk with
    | 0, hk =>
      exact .sg (ps := none) (c := c) (hty.lift_subject hΔ hk)
        TShape.pairParts_lift_zero
        (by simp) (by simp) (by simp)
    | k+1, hk =>
      refine .sg (ps := ps.map fun p => (p.1, p.2.1.lift k, p.2.2.lift k)) (c := c)
        (hty.lift_subject hΔ hk) ?_ ?_ ?_ ?_
      · rw [← hps, TShape.pairParts_lift hk]
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := Option.exists_of_mem_map hp
        exact ihx q hq (by have := TShape.pairParts_level hps hq; omega)
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := Option.exists_of_mem_map hp
        refine TEvaluates.mono_inp hΔ ?_ (hev q hq)
        exact TShape.LE.le_lift hΔ (by have := TShape.pairParts_level hps hq; omega)
          (TShape.Dom.hasType (hx q hq)).wf.1
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := Option.exists_of_mem_map hp
        exact ihy q hq (by have := TShape.pairParts_level hps hq; omega)

/-- A code below a binder code is a binder code, or `⊥`: the order pins
the head.  This is what lets `Dom`'s `base` clause stay disjoint from the
other two under `mono_r`. -/
theorem TShape.IsBinder.of_le {Δ : List Term} {d d' : TShape}
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
        | .bot | .sort _ | .unit _ | .nat | .zero | .succ _ | .refl | .id _ _ _ _
        | .lam _ _ | .pair _ _ _ _ => exact absurd hb (fun x => x)
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
      | .refl, .forallE .. | .refl, .sigma ..
      | .id .., .forallE .. | .id .., .sigma ..
      | .lam .., .forallE .. | .lam .., .sigma ..
      | .pair .., .forallE .. | .pair .., .sigma ..
      | .forallE .., .sigma .. | .sigma .., .forallE .. => exact absurd h2 (fun x => x)
      | _, .bot | _, .sort _ | _, .unit _ | _, .nat | _, .zero | _, .succ _
      | _, .refl | _, .id .. | _, .lam .. | _, .pair .. => exact absurd hb (fun x => x)

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
    · exact .base (fun hbind => hnb (TShape.IsBinder.of_le hle hbind hb))
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
          obtain ⟨hPi, _, hcov⟩ := TShape.LE.forallE_decomp hΔ hle
            (TShape.HasType.wf hty0).2 hw₂ (fun e he => TEvaluates.refl hw₂.2.2.2 e he)
          exact (TEvaluates.trans hΔ hcov (hev p hp)).retype hPi.1
      | .bot | .sort _ | .unit _ | .nat | .zero | .succ _ | .refl | .id _ _ _ _
      | .lam _ _ | .sigma .. | .pair _ _ _ _ => exact absurd h2 (fun x => x)
  | @sg n A B d f x ps c hty0 hps hx hev hy ihx ihy =>
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
        obtain ⟨hlab, _, hcov⟩ := TShape.LE.sigma_decomp hΔ hle
          (TShape.HasType.wf hty0).2 hw₂ (fun e he => TEvaluates.refl hw₂.2.2.2 e he)
        exact .sg (c := c) (TShape.HasType.mono_r hΔ hty0 _ hle hty) hps
          (fun p hp => ihx p hp hdle hd₂)
          (fun p hp => TEvaluates.retype hlab.1 (TEvaluates.trans hΔ hcov (hev p hp)))
          (fun p hp => hy p hp)
      | .bot | .sort _ | .unit _ | .nat | .zero | .succ _ | .refl | .id _ _ _ _
      | .lam _ _ | .forallE .. | .pair _ _ _ _ => exact absurd h2 (fun x => x)

/-- A code typed at a sort is `Dom` there: a sort filters. -/
theorem TShape.Dom.of_isType {Δ : List Term} {x : TShape}
    (h : TShape.HasType Δ x TShape.type) : TShape.Dom Δ TShape.type x :=
  .base (fun h => h) h

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
  | .bot, .pair _ _ _ _ => .inr (.inr rfl)
  | .bot, .nat => .inr (.inr rfl)
  | .bot, .zero => .inr (.inr rfl)
  | .bot, .succ _ => .inr (.inr rfl)
  | .bot, .id _ _ _ _ => .inr (.inr rfl)
  | .bot, .refl => .inr (.inr rfl)
  | .sort _, .bot => .inr (.inl rfl)
  | .sort _, .sort _ => .inr (.inl rfl)
  | .sort _, .unit _ => .inr (.inl rfl)
  | .sort _, .forallE _ _ _ _ => .inr (.inl rfl)
  | .sort _, .lam _ _ => .inr (.inl rfl)
  | .sort _, .sigma _ _ _ _ => .inr (.inl rfl)
  | .sort _, .pair _ _ _ _ => .inr (.inl rfl)
  | .sort _, .nat => .inr (.inl rfl)
  | .sort _, .zero => .inr (.inl rfl)
  | .sort _, .succ _ => .inr (.inl rfl)
  | .sort _, .id _ _ _ _ => .inr (.inl rfl)
  | .sort _, .refl => .inr (.inl rfl)
  | .unit _, .bot => .inr (.inl rfl)
  | .unit _, .sort _ => .inr (.inl rfl)
  | .unit _, .unit _ => .inr (.inl rfl)
  | .unit _, .forallE _ _ _ _ => .inr (.inl rfl)
  | .unit _, .lam _ _ => .inr (.inl rfl)
  | .unit _, .sigma _ _ _ _ => .inr (.inl rfl)
  | .unit _, .pair _ _ _ _ => .inr (.inl rfl)
  | .unit _, .nat => .inr (.inl rfl)
  | .unit _, .zero => .inr (.inl rfl)
  | .unit _, .succ _ => .inr (.inl rfl)
  | .unit _, .id _ _ _ _ => .inr (.inl rfl)
  | .unit _, .refl => .inr (.inl rfl)
  | .forallE _ _ _ _, .bot => .inr (.inl rfl)
  | .forallE _ _ _ _, .sort _ => .inr (.inl rfl)
  | .forallE _ _ _ _, .unit _ => .inr (.inl rfl)
  | .forallE _ _ _ _, .forallE _ _ _ _ => .inr (.inl rfl)
  | .forallE _ _ _ _, .lam _ _ => .inr (.inl rfl)
  | .forallE _ _ _ _, .sigma _ _ _ _ => .inr (.inl rfl)
  | .forallE _ _ _ _, .pair _ _ _ _ => .inr (.inl rfl)
  | .forallE _ _ _ _, .nat => .inr (.inl rfl)
  | .forallE _ _ _ _, .zero => .inr (.inl rfl)
  | .forallE _ _ _ _, .succ _ => .inr (.inl rfl)
  | .forallE _ _ _ _, .id _ _ _ _ => .inr (.inl rfl)
  | .forallE _ _ _ _, .refl => .inr (.inl rfl)
  | .lam _ _, .bot => .inr (.inl rfl)
  | .lam _ _, .sort _ => .inr (.inl rfl)
  | .lam _ _, .unit _ => .inr (.inl rfl)
  | .lam _ _, .forallE _ _ _ _ => .inr (.inl rfl)
  | .lam _ _, .lam _ _ => .inl rfl
  | .lam _ _, .sigma _ _ _ _ => .inr (.inl rfl)
  | .lam _ _, .pair _ _ _ _ => .inr (.inl rfl)
  | .lam _ _, .nat => .inr (.inl rfl)
  | .lam _ _, .zero => .inr (.inl rfl)
  | .lam _ _, .succ _ => .inr (.inl rfl)
  | .lam _ _, .id _ _ _ _ => .inr (.inl rfl)
  | .lam _ _, .refl => .inr (.inl rfl)
  | .sigma _ _ _ _, .bot => .inr (.inl rfl)
  | .sigma _ _ _ _, .sort _ => .inr (.inl rfl)
  | .sigma _ _ _ _, .unit _ => .inr (.inl rfl)
  | .sigma _ _ _ _, .forallE _ _ _ _ => .inr (.inl rfl)
  | .sigma _ _ _ _, .lam _ _ => .inr (.inl rfl)
  | .sigma _ _ _ _, .sigma _ _ _ _ => .inr (.inl rfl)
  | .sigma _ _ _ _, .pair _ _ _ _ => .inr (.inl rfl)
  | .sigma _ _ _ _, .nat => .inr (.inl rfl)
  | .sigma _ _ _ _, .zero => .inr (.inl rfl)
  | .sigma _ _ _ _, .succ _ => .inr (.inl rfl)
  | .sigma _ _ _ _, .id _ _ _ _ => .inr (.inl rfl)
  | .sigma _ _ _ _, .refl => .inr (.inl rfl)
  | .pair _ _ _ _, .bot => .inr (.inl rfl)
  | .pair _ _ _ _, .sort _ => .inr (.inl rfl)
  | .pair _ _ _ _, .unit _ => .inr (.inl rfl)
  | .pair _ _ _ _, .forallE _ _ _ _ => .inr (.inl rfl)
  | .pair _ _ _ _, .lam _ _ => .inr (.inl rfl)
  | .pair _ _ _ _, .sigma _ _ _ _ => .inr (.inl rfl)
  | .pair _ _ _ _, .pair _ _ _ _ => .inl rfl
  | .pair _ _ _ _, .nat => .inr (.inl rfl)
  | .pair _ _ _ _, .zero => .inr (.inl rfl)
  | .pair _ _ _ _, .succ _ => .inr (.inl rfl)
  | .pair _ _ _ _, .id _ _ _ _ => .inr (.inl rfl)
  | .pair _ _ _ _, .refl => .inr (.inl rfl)
  | .nat, .bot => .inr (.inl rfl)
  | .nat, .sort _ => .inr (.inl rfl)
  | .nat, .unit _ => .inr (.inl rfl)
  | .nat, .forallE _ _ _ _ => .inr (.inl rfl)
  | .nat, .lam _ _ => .inr (.inl rfl)
  | .nat, .sigma _ _ _ _ => .inr (.inl rfl)
  | .nat, .pair _ _ _ _ => .inr (.inl rfl)
  | .nat, .nat => .inr (.inl rfl)
  | .nat, .zero => .inr (.inl rfl)
  | .nat, .succ _ => .inr (.inl rfl)
  | .nat, .id _ _ _ _ => .inr (.inl rfl)
  | .nat, .refl => .inr (.inl rfl)
  | .zero, .bot => .inr (.inl rfl)
  | .zero, .sort _ => .inr (.inl rfl)
  | .zero, .unit _ => .inr (.inl rfl)
  | .zero, .forallE _ _ _ _ => .inr (.inl rfl)
  | .zero, .lam _ _ => .inr (.inl rfl)
  | .zero, .sigma _ _ _ _ => .inr (.inl rfl)
  | .zero, .pair _ _ _ _ => .inr (.inl rfl)
  | .zero, .nat => .inr (.inl rfl)
  | .zero, .zero => .inr (.inl rfl)
  | .zero, .succ _ => .inr (.inl rfl)
  | .zero, .id _ _ _ _ => .inr (.inl rfl)
  | .zero, .refl => .inr (.inl rfl)
  | .succ _, .bot => .inr (.inl rfl)
  | .succ _, .sort _ => .inr (.inl rfl)
  | .succ _, .unit _ => .inr (.inl rfl)
  | .succ _, .forallE _ _ _ _ => .inr (.inl rfl)
  | .succ _, .lam _ _ => .inr (.inl rfl)
  | .succ _, .sigma _ _ _ _ => .inr (.inl rfl)
  | .succ _, .pair _ _ _ _ => .inr (.inl rfl)
  | .succ _, .nat => .inr (.inl rfl)
  | .succ _, .zero => .inr (.inl rfl)
  | .succ _, .succ _ => .inr (.inl rfl)
  | .succ _, .id _ _ _ _ => .inr (.inl rfl)
  | .succ _, .refl => .inr (.inl rfl)
  | .id _ _ _ _, .bot => .inr (.inl rfl)
  | .id _ _ _ _, .sort _ => .inr (.inl rfl)
  | .id _ _ _ _, .unit _ => .inr (.inl rfl)
  | .id _ _ _ _, .forallE _ _ _ _ => .inr (.inl rfl)
  | .id _ _ _ _, .lam _ _ => .inr (.inl rfl)
  | .id _ _ _ _, .sigma _ _ _ _ => .inr (.inl rfl)
  | .id _ _ _ _, .pair _ _ _ _ => .inr (.inl rfl)
  | .id _ _ _ _, .nat => .inr (.inl rfl)
  | .id _ _ _ _, .zero => .inr (.inl rfl)
  | .id _ _ _ _, .succ _ => .inr (.inl rfl)
  | .id _ _ _ _, .id _ _ _ _ => .inr (.inl rfl)
  | .id _ _ _ _, .refl => .inr (.inl rfl)
  | .refl, .bot => .inr (.inl rfl)
  | .refl, .sort _ => .inr (.inl rfl)
  | .refl, .unit _ => .inr (.inl rfl)
  | .refl, .forallE _ _ _ _ => .inr (.inl rfl)
  | .refl, .lam _ _ => .inr (.inl rfl)
  | .refl, .sigma _ _ _ _ => .inr (.inl rfl)
  | .refl, .pair _ _ _ _ => .inr (.inl rfl)
  | .refl, .nat => .inr (.inl rfl)
  | .refl, .zero => .inr (.inl rfl)
  | .refl, .succ _ => .inr (.inl rfl)
  | .refl, .id _ _ _ _ => .inr (.inl rfl)
  | .refl, .refl => .inr (.inl rfl)

theorem TShape.entries_join {n} {x y : Shape (n+1)} :
    (Shape.T (x.join y)).entries = (Shape.T x).entries ++ (Shape.T y).entries ∨
      (Shape.T (x.join y)).entries = (Shape.T x).entries ∨
      (Shape.T (x.join y)).entries = (Shape.T y).entries := by
  rcases Shape.graph_join (x := x) (y := y) with h | h | h <;>
    simp [TShape.entries, h]

/-- **Inverting `Dom` at a Σ**: the first component is hereditarily typed
at the domain, and the second at the codomain read at the pair's own name
and first component. -/
theorem TShape.Dom.sg_inv {Δ : List Term} {n k} {A B A₀ a : Term} {d : Shape n}
    {f : ShapeFun n} {x y : Shape k}
    (h : TShape.Dom Δ (Shape.T (n := n+1) (ShapeS.sigma A B d f))
      (Shape.T (n := k+1) (ShapeS.pair A₀ a x y))) :
    ∃ c, TShape.Dom Δ d.T x.T ∧ TEvaluates Δ f A a x.T c ∧ TShape.Dom Δ c y.T := by
  cases h with
  | base hnb _ => exact absurd trivial hnb
  | @sg _ _ _ _ _ _ ps c hty hps hx hev hy =>
    have hps' : ps = some (a, x.T, y.T) := by
      simpa [TShape.pairParts, Shape.T] using hps.symm
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
theorem TShape.HasType.join_at {Δ : List Term} (hΔ : ⊢ Δ) :
    ∀ {n} {y z : Shape n} {c : TShape}, Shape.Compat Δ y z →
      TShape.Dom Δ c y.T → TShape.Dom Δ c z.T →
      TShape.HasType Δ (y.join z).T c := by
  intro n
  induction n with
  | zero =>
    intro y z c hc hyD hzD
    have hy := hyD.hasType; have hz := hzD.hasType
    cases y with
    | bot => exact hz
    | sort r => cases z <;> exact hy
  | succ n ih =>
    intro y z c hc hyD hzD
    have hy := hyD.hasType; have hz := hzD.hasType
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
    | refl =>
      cases z with
      | bot => exact hy
      | refl =>
        cases hy with | refl hle hA =>
        cases hz with | refl _ _ =>
        exact .refl hle hA
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
              (join_gen_cover hΔ hwg₀ hwg₀' hg fun e he => (hg' e he).retype (TyEq.symm hc.1))
              (join_gen_code hΔ hwg₀ hwg₀' hg₀ev hg₀ev')
              (join_gen_ty hΔ hg₀ty hg₀ty') hdom
      | _ => exact absurd hc (fun x => x)
    | pair A₀ a x₁ y₁ =>
      cases z with
      | bot => exact hy
      | pair A₀' a' x₂ y₂ =>
        cases hy with
        | @pair _ n' _ _ _ _ f A B d _ _ hd hfo hwp hwSg hxd _ _ _ hdom =>
          cases hz with
          | @pair _ _ _ _ _ _ _ _ _ _ _ _ _ _ hwp' _ _ _ _ _ hdom' =>
            obtain ⟨c₁, hdx₁, hev₁, hdy₁⟩ := hyD.sg_inv
            obtain ⟨c₂, hdx₂, hev₂, hdy₂⟩ := hzD.sg_inv
            -- the two codes are lookups at one query once the inputs are
            -- joined, so they join, and the components' typings move up
            have hjx := Shape.le_join hΔ hwp.2.2.2.1 hwp'.2.2.2.1 hc.2.2.1
            have hev₁' := TEvaluates.mono_inp hΔ (TShape.LE.T.2 hjx.1) hev₁
            have hev₂' := TEvaluates.label ⟨hdom.symm.trans hdom,
                (hdom.choose_spec.defeqDF hc.2.1).symm⟩
              (TEvaluates.mono_inp hΔ (TShape.LE.T.2 hjx.2) hev₂)
            have hcc := TEvaluates.compat hΔ hwSg.2.2.2.2 (TShape.WF.T.2 (Shape.WF.join hΔ hc.2.2.1 hwp.2.2.2.1 hwp'.2.2.2.1)) hev₁' hev₂'
            refine .pair hd hfo (Shape.WF.join hΔ hc hwp hwp') hwSg
              (ih hc.2.2.1 hdx₁ hdx₂) (TShape.LE.refl (TShape.WF.T.2
                (Shape.WF.join hΔ hc hwp hwp').2.2.2.1))
              (TEvaluates.join hcc hev₁' hev₂') ?_ hdom
            have hcty := TEvaluates.tHasType (c := TShape.type) hΔ rfl
              (fun e he => hfo e he) (TEvaluates.join hcc hev₁' hev₂')
            have hjc := TShape.le_join hΔ (TEvaluates.wf hΔ (fun e he => TShape.WF.T.2 (hwSg.2.2.2.1 e he).2.2.2) hev₁')
              (TEvaluates.wf hΔ (fun e he => TShape.WF.T.2 (hwSg.2.2.2.1 e he).2.2.2) hev₂') hcc
            exact ih hc.2.2.2 (TShape.Dom.mono_r hΔ hdy₁ hjc.1 hcty)
              (TShape.Dom.mono_r hΔ hdy₂ hjc.2 hcty)
      | _ => exact absurd hc (fun x => x)

/-- The same at the total level: lift both subjects to the common level
and join there. -/
theorem TShape.HasType.join {Δ : List Term} (hΔ : ⊢ Δ) {y z c : TShape}
    (hc : TShape.Compat Δ y z) (hy : TShape.Dom Δ c y) (hz : TShape.Dom Δ c z) :
    TShape.HasType Δ (y.join z) c :=
  TShape.HasType.join_at hΔ
    ((TShape.Compat.def (Nat.le_max_left ..) (Nat.le_max_right ..)).1 hc)
    (hy.lift_subject hΔ (Nat.le_max_left ..)) (hz.lift_subject hΔ (Nat.le_max_right ..))

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
      TShape.HasType.join_at hΔ hc hy hz
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
    | @sg _ A B d₀ f _ psy cy htyy hpsy hxy hevy hyy =>
      cases hz with
      | base hnb _ => exact absurd trivial hnb
      | @sg _ _ _ _ _ _ psz cz htyz hpsz hxz hevz hyz =>
        -- the join is a pair exactly when both sides are, and then the two
        -- codes are lookups at one query once the inputs are joined
        match y, z, hc, hpsy, hpsz, hty, htyy with
        | .bot, z, _, _, hpsz, hty, _ => exact .sg (ps := psz) (c := cz) hty hpsz hxz hevz hyz
        | .pair A₁ a₁ x₁ y₁, .bot, _, hpsy, _, hty, _ =>
          exact .sg (ps := psy) (c := cy) hty hpsy hxy hevy hyy
        | .pair A₁ a₁ x₁ y₁, .pair A₂ a₂ x₂ y₂, hc, hpsy, hpsz, hty, htyy =>
          obtain ⟨c₁, hdx₁, hev₁, hdy₁⟩ :=
            TShape.Dom.sg_inv (.sg (ps := psy) (c := cy) htyy hpsy hxy hevy hyy)
          obtain ⟨c₂, hdx₂, hev₂, hdy₂⟩ :=
            TShape.Dom.sg_inv (.sg (ps := psz) (c := cz) htyz hpsz hxz hevz hyz)
          cases htyy with | @pair _ _ _ _ _ _ _ _ _ _ _ _ hd hfo hwp hwSg _ _ _ _ hdomA =>
          have hwp' := (TShape.HasType.wf htyz).1
          have hjx := Shape.le_join hΔ hwp.2.2.2.1 hwp'.2.2.2.1 hc.2.2.1
          have hev₁' := TEvaluates.mono_inp hΔ (TShape.LE.T.2 hjx.1) hev₁
          have hev₂' := TEvaluates.label ⟨hdomA.symm.trans hdomA,
              (hdomA.choose_spec.defeqDF hc.2.1).symm⟩
            (TEvaluates.mono_inp hΔ (TShape.LE.T.2 hjx.2) hev₂)
          have hcc := TEvaluates.compat hΔ hwSg.2.2.2.2 (TShape.WF.T.2 (Shape.WF.join hΔ hc.2.2.1 hwp.2.2.2.1 hwp'.2.2.2.1)) hev₁' hev₂'
          refine .sg (ps := some (a₁, (x₁.join x₂).T, (y₁.join y₂).T)) (c := c₁.join c₂)
            hty rfl (fun p hp => ?_) (fun p hp => ?_) (fun p hp => ?_) <;>
            simp only [Option.mem_def, Option.some.injEq] at hp <;> subst hp
          · exact ih hc.2.2.1 hdx₁ hdx₂
          · exact TEvaluates.join hcc hev₁' hev₂'
          · have hcty := TEvaluates.tHasType (c := TShape.type) hΔ rfl
              (fun e he => hfo e he) (TEvaluates.join hcc hev₁' hev₂')
            have hjc := TShape.le_join hΔ (TEvaluates.wf hΔ (fun e he => TShape.WF.T.2 (hwSg.2.2.2.1 e he).2.2.2) hev₁')
              (TEvaluates.wf hΔ (fun e he => TShape.WF.T.2 (hwSg.2.2.2.1 e he).2.2.2) hev₂') hcc
            exact ih hc.2.2.2 (TShape.Dom.mono_r hΔ hdy₁ hjc.1 hcty)
              (TShape.Dom.mono_r hΔ hdy₂ hjc.2 hcty)
        | .refl, z, hc, _, _, _, htyy =>
          refine absurd htyy ?_
          intro h
          cases h with
          | refl hleid _ =>
            obtain ⟨M, _, _, h2⟩ := TShape.LE.src_succ hleid
            exact absurd h2 (fun x => x)
        | .sort _, z, hc, _, _, _, htyy | .unit _, z, hc, _, _, _, htyy
        | .nat, z, hc, _, _, _, htyy | .zero, z, hc, _, _, _, htyy =>
          exact absurd htyy (by rintro ⟨⟩)
        | .succ _, z, hc, _, _, _, htyy
        | .id .., z, hc, _, _, _, htyy | .forallE .., z, hc, _, _, _, htyy
        | .sigma .., z, hc, _, _, _, htyy | .lam .., z, hc, _, _, _, htyy =>
          exact absurd htyy (by rintro ⟨⟩)
        | .pair .., .sort _, hc, _, _, _, _ | .pair .., .unit _, hc, _, _, _, _
        | .pair .., .nat, hc, _, _, _, _ | .pair .., .zero, hc, _, _, _, _
        | .pair .., .succ _, hc, _, _, _, _ | .pair .., .refl, hc, _, _, _, _
        | .pair .., .id .., hc, _, _, _, _ | .pair .., .forallE .., hc, _, _, _, _
        | .pair .., .sigma .., hc, _, _, _, _ | .pair .., .lam .., hc, _, _, _, _ =>
          exact absurd hc id

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
      | .refl, _ | .id .., _ | .lam _ _, _ | .pair _ _ _ _, _ => exact hb
    | succ k =>
      match s, s' with
      | .forallE .., .forallE .. | .sigma .., .sigma .. => exact hc trivial
      | .forallE .., .bot | .forallE .., .sort _ | .forallE .., .unit _
      | .forallE .., .nat | .forallE .., .zero | .forallE .., .succ _
      | .forallE .., .refl | .forallE .., .id .. | .forallE .., .lam _ _
      | .forallE .., .pair .. | .forallE .., .sigma ..
      | .sigma .., .bot | .sigma .., .sort _ | .sigma .., .unit _
      | .sigma .., .nat | .sigma .., .zero | .sigma .., .succ _
      | .sigma .., .refl | .sigma .., .id .. | .sigma .., .lam _ _
      | .sigma .., .pair .. | .sigma .., .forallE .. => exact absurd h2 (fun x => x)
      | .bot, _ | .sort _, _ | .unit _, _ | .nat, _ | .zero, _ | .succ _, _
      | .refl, _ | .id .., _ | .lam _ _, _ | .pair _ _ _ _, _ => exact hb

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
  cases n with
  | zero => exact absurd h (fun x => x)
  | succ n => cases s <;> first | exact fun x => x | exact absurd h (fun x => x)

theorem TShape.IsPi.not_bot {p : TShape} (h : p.IsPi) : p.2 ≠ Shape.bot := by
  obtain ⟨n, s⟩ := p
  cases n with
  | zero => exact absurd h (fun x => x)
  | succ n =>
    cases s <;> first | exact absurd h (fun x => x) | exact (by simp [Shape.bot])

theorem TShape.IsSigma.not_bot {p : TShape} (h : p.IsSigma) : p.2 ≠ Shape.bot := by
  obtain ⟨n, s⟩ := p
  cases n with
  | zero => exact absurd h (fun x => x)
  | succ n =>
    cases s <;> first | exact absurd h (fun x => x) | exact (by simp [Shape.bot])

theorem TShape.IsPi.isBinder {p : TShape} (h : p.IsPi) : p.IsBinder := by
  obtain ⟨n, s⟩ := p
  cases n with
  | zero => exact h
  | succ n => cases s <;> first | exact h | exact trivial

theorem TShape.IsSigma.isBinder {p : TShape} (h : p.IsSigma) : p.IsBinder := by
  obtain ⟨n, s⟩ := p
  cases n with
  | zero => exact h
  | succ n => cases s <;> first | exact h | exact trivial

/-- Below a Π-shape there are only `⊥` and Π-shapes: the order pins the
head, which is what lets an approximant of a Π type be analysed. -/
theorem TShape.isPi_or_bot_of_le {Δ : List Term} {p q : TShape} (h : TShape.LE Δ p q)
    (hq : q.IsPi) : p.2 = Shape.bot ∨ p.IsPi := by
  obtain ⟨n, s⟩ := p
  obtain ⟨k, s'⟩ := q
  cases k with
  | zero => exact absurd hq (fun x => x)
  | succ k =>
    match s' with
    | .forallE .. =>
      obtain ⟨M, hkM, hnM, h2⟩ := TShape.LE.at_succ h
      cases n with
      | zero =>
        match s with
        | .bot => exact .inl rfl
        | .sort _ => exact absurd h2 (fun x => x)
      | succ n =>
        match s with
        | .bot => exact .inl rfl
        | .forallE .. => exact .inr trivial
        | .sort _ | .unit _ | .nat | .zero | .succ _ | .refl | .id _ _ _ _
        | .lam _ _ | .sigma .. | .pair _ _ _ _ => exact absurd h2 (fun x => x)
    | .bot | .sort _ | .unit _ | .nat | .zero | .succ _ | .refl | .id _ _ _ _
    | .lam _ _ | .sigma .. | .pair _ _ _ _ => exact absurd hq (fun x => x)

/-- **The level-free lookup, read back at the graph's own level**:
`ShapeFun.Eval.toT`'s converse, up to the order.  A `TEvaluates` value is
below one the level-indexed lookup reaches, which is all an order
comparison between λ-shapes needs, since `Eval` is closed under `lower`.
The `join` case is where the graph's coherence comes in
(`ShapeFun.Eval.compat`). -/
theorem TEvaluates.toEval {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a : Term}
    {x : Shape n} (hwf : ShapeFun.WF Δ A (Shape.WF Δ) f) (hx : Shape.WF Δ x) :
    ∀ {c : TShape}, TEvaluates Δ f A a x.T c →
      ∃ c' : Shape n, TShape.LE Δ c c'.T ∧ ShapeFun.Eval Δ (Shape.LE Δ) f A a x c' := by
  intro c h
  induction h with
  | bot => exact ⟨.bot, TShape.bot_le' rfl, .bot⟩
  | entry e he hlab hin =>
    refine ⟨e.out, TShape.LE.refl (TShape.WF.T.2 (hwf.1 e he).2.2.2), ?_⟩
    exact .entry e he hlab (TShape.LE.T.1 hin)
  | lower hle _ ih =>
    obtain ⟨c', hc', hev⟩ := ih
    exact ⟨c', TShape.LE.trans hΔ hle hc', hev⟩
  | join hc _ _ ih₁ ih₂ =>
    obtain ⟨c₁, hc₁, hev₁⟩ := ih₁
    obtain ⟨c₂, hc₂, hev₂⟩ := ih₂
    have hw₁ := ShapeFun.Eval.wf hΔ (fun e he => (hwf.1 e he).2.2.2) hev₁
    have hw₂ := ShapeFun.Eval.wf hΔ (fun e he => (hwf.1 e he).2.2.2) hev₂
    have hcc : Shape.Compat Δ c₁ c₂ :=
      ShapeFun.Eval.compat hΔ hwf.2 hx.coherent hev₁ hev₂
    obtain ⟨hj₁, hj₂⟩ := Shape.le_join hΔ hw₁ hw₂ hcc
    exact ⟨c₁.join c₂,
      TShape.join_le hΔ (TShape.LE.trans hΔ hc₁ (TShape.LE.T.2 hj₁))
        (TShape.LE.trans hΔ hc₂ (TShape.LE.T.2 hj₂)),
      .join hcc hev₁ hev₂⟩

/-- A shape that dominates a λ-shape is one: the order pins the head
upward too. -/
def TShape.IsLam : TShape → Prop
  | ⟨0, _⟩ => False
  | ⟨_+1, .lam ..⟩ => True
  | ⟨_+1, _⟩ => False

theorem TShape.isLam_of_le {Δ : List Term} {x y : TShape} (h : TShape.LE Δ x y)
    (hx : x.IsLam) : y.IsLam := by
  obtain ⟨n, s⟩ := x
  obtain ⟨k, s'⟩ := y
  cases n with
  | zero => exact absurd hx (fun x => x)
  | succ n =>
    match s with
    | .lam _ _ =>
      obtain ⟨M, hkM, hnM, h2⟩ := TShape.LE.src_succ h
      cases k with
      | zero => cases s' <;> exact absurd h2 (fun x => x)
      | succ k =>
        match s' with
        | .lam _ _ => exact trivial
        | .bot | .sort _ | .unit _ | .nat | .zero | .succ _ | .refl | .id _ _ _ _
        | .forallE .. | .sigma .. | .pair _ _ _ _ => exact absurd h2 (fun x => x)
    | .bot | .sort _ | .unit _ | .nat | .zero | .succ _ | .refl | .id _ _ _ _
    | .forallE .. | .sigma .. | .pair _ _ _ _ => exact absurd hx (fun x => x)

/-- The Σ twin of `TShape.isPi_or_bot_of_le`. -/
theorem TShape.isSigma_or_bot_of_le {Δ : List Term} {p q : TShape} (h : TShape.LE Δ p q)
    (hq : q.IsSigma) : p.2 = Shape.bot ∨ p.IsSigma := by
  obtain ⟨n, s⟩ := p
  obtain ⟨k, s'⟩ := q
  cases k with
  | zero => exact absurd hq (fun x => x)
  | succ k =>
    match s' with
    | .sigma .. =>
      obtain ⟨M, hkM, hnM, h2⟩ := TShape.LE.at_succ h
      cases n with
      | zero =>
        match s with
        | .bot => exact .inl rfl
        | .sort _ => exact absurd h2 (fun x => x)
      | succ n =>
        match s with
        | .bot => exact .inl rfl
        | .sigma .. => exact .inr trivial
        | .sort _ | .unit _ | .nat | .zero | .succ _ | .refl | .id _ _ _ _
        | .lam _ _ | .forallE .. | .pair _ _ _ _ => exact absurd h2 (fun x => x)
    | .bot | .sort _ | .unit _ | .nat | .zero | .succ _ | .refl | .id _ _ _ _
    | .lam _ _ | .forallE .. | .pair _ _ _ _ => exact absurd hq (fun x => x)
