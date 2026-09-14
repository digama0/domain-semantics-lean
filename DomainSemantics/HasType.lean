import DomainSemantics.Shape

/-! # Typing of labelled shapes

`Shape.HasType Δ m a` says the shape `m` is a well-typed inhabitant of the
type-shape `a`.  This is `ShapeOld.lean`'s `HasType`, with three changes.

* It is `Prop`-valued and defined directly, not factored through a `Bool`
  function: labels are compared up to definitional equality, so nothing
  here is decidable and the `hasType` / `hasType.core` / `HasTypeU` /
  `unfold_iff` layering has no purpose.
* It is indexed by a context, for the same reason.
* The Π and λ clauses used `ShapeFun.app`, the search for the maximal
  graph entry below the input, which was only correct because graphs were
  saturated (`ShapeFun.WF`).  Saturation is gone, so the codomain type is
  obtained from the relational lookup `Evaluates` instead, and the output
  of an entry must be typed at *some* code the family graph yields — which
  is also how the other repo reads it (`rawExtend T X` quantifies
  `∃ c ∈ T`).

Together with `InterpTyped`/`SoundTy` this plays the role of the other
repo's decoder: see §4.2 of `presheaf-plan.md`.  Its fixed-point
construction (`piStep`/`piStage`/`rank`/`piLimit`) is unnecessary here
because the recursion is structural in the level. -/

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

/-- The graph is a family **over the domain**: every entry's output is
already reached at some input that is typed at the domain and below the
entry's own input.

Master says "every entry is dominated by an *entry* whose input is typed",
which is a saturation-era formulation — it needs a saturated graph and a
search for the maximal entry below the argument, with the entry the search
lands on found by a finiteness argument on the domination chain.

Simply demanding that every input be typed is the other extreme, and it is
too strong: the lookup closes under joins and lowering, so an
interpretation's graph will contain entries at inputs that are not
themselves typed.  What has to hold is that nothing is *gained* there —
the graph is determined by its behaviour on typed inputs.  So the
dominating entry becomes a dominating *lookup*, which is the
non-saturated analogue. -/
def ShapeFun.HasDom (Δ : List Term) (T : Shape n → Shape n → Prop)
    (f : ShapeFun n) (d : Shape n) : Prop :=
  ∀ e ∈ f, ∃ x, Shape.WF Δ x ∧ T x d ∧ Shape.LE Δ x e.inp ∧
    Evaluates Δ f e.ty e.tm x e.out

/-- The Π/Σ signature condition: `(d, f)` is a domain together with a
codomain family landing in `a`.

`(d, f)` has only to **approximate** such a pair.  That is how downward
closure is built into the clause, and it is needed because `HasDom` is the
one condition here that is not stable under shrinking a graph: a smaller
graph has weaker lookups, so an entry that was justified by a lookup in
`f₀` need not be justified by one in `f`.  Everything else in sight is
stable on its own, by induction.

Compare the other repo, where a type is a lower set outright (`ΩLower` has
`lower` as a field) and Π-membership reads
`∃ a f, A.mem σ a ∧ B.GraphValid σ f ∧ q ≤ piGenerator label a f`: the
conditions constrain a generator *above* the shape being classified, never
the shape itself. -/
def ShapeFun.HasPi (T : Shape n → Shape n → Prop)
    (d : Shape n) (f : ShapeFun n) (a : Shape n) : Prop :=
  T d .type ∧ ∀ e ∈ f, T e.out a

/-- "is a numeral".  The one condition that cannot be phrased as
`HasType · .nat` uniformly, because `Shape 0` has no `nat`; it is
independent of typing, so it gets its own recursion rather than an
inline match in `HasType`.  `HasType v .nat ↔ IsNumeral v` at positive
level (`Shape.hasType_nat_iff`). -/
inductive Shape.IsNumeral : ∀ {n}, Shape n → Prop
  | bot : IsNumeral .bot
  | zero : IsNumeral (n := n+1) .zero
  | succ : IsNumeral (n := n) w → IsNumeral (.succ w)

/-- Weaken the codomain condition of a Π/Σ signature. -/
theorem ShapeFun.HasPi.cod {n} {T : Shape n → Shape n → Prop}
    {d : Shape n} {f : ShapeFun n} {a a' : Shape n}
    (H : ∀ {z}, T z a → T z a') (h : ShapeFun.HasPi T d f a) :
    ShapeFun.HasPi T d f a' :=
  ⟨h.1, fun e he => H (h.2 e he)⟩

inductive Shape.HasType0 : Shape 0 → Shape 0 → Prop
  | bot : HasType0 .bot a
  | sort : HasType0 (.sort u) (.sort true)

/-- One level of the typing relation, as an inductive family in the typing
relation `T` of the level below — the same shape as `ShapeFun.HasDom` and
`ShapeFun.HasPi`, which it uses.

Being inductive rather than a match buys the inversion principles: `cases`
on a derivation replaces the `cases m <;> cases a <;> first | exact absurd
h id | …` boilerplate, and each clause gets a name.

A type is a **lower set**: `HasType Δ · a` is downward closed
(`HasType.lower`), so `≈`-equivalent shapes inhabit the same types
(`mono_l`).  That is not automatic — it is why `lam` and `pair` are stated
about a *dominating* graph resp. first component rather than about the
value's own, exactly as `HasPi` is — and it is what makes typing reflect
along `lift`.

`lam` and `pair` carry the well-formedness of the Π/Σ type they inhabit,
which together with the `bot` constructor is what makes `isType`
(`HasType m a → HasType a .type`) go through; without it `mono_r` cannot
be stated, let alone proved. -/
inductive Shape.HasTypeS (Δ : List Term) {n} (T : Shape n → Shape n → Prop) :
    Shape (n + 1) → Shape (n + 1) → Prop where
  -- `⊥` inhabits exactly the types.  Being *inductive* is what lets this be
  -- one constructor with a premise at the same level; as a match it had to
  -- be spelled out per type former, because `HasType a .type` is not
  -- structurally smaller than `HasType .bot a`
  | bot {a} : HasTypeS Δ T a .type → HasTypeS Δ T .bot a
  | sort {r} : HasTypeS Δ T (.sort r) (.sort true)
  | unit {r j} : r ≤ j → HasTypeS Δ T (.unit r) (.sort j)
  | nat : HasTypeS Δ T .nat (.sort true)
  | zero : HasTypeS Δ T .zero .nat
  | succ {v} : Shape.IsNumeral v → HasTypeS Δ T (.succ v) .nat
  | id {r j A a b} : r ≤ j → HasTypeS Δ T (.id r A a b) (.sort j)
  | forallE {A B d f r} :
    ShapeFun.HasPi T d f (.sort r) → HasTypeS Δ T (.forallE A B d f) (.sort r)
  | sigma {A B d f} :
    ShapeFun.HasPi T d f .type → HasTypeS Δ T (.sigma A B d f) (.sort true)
  -- no dominating graph: with `HasDom` gone the condition is downward
  -- closed in `g` on its own, by `mono_input` on the code and `mono_l` on
  -- the output.
  -- WRONG under lookup coverage, and `mono_l`'s `lam` case is the sorry
  -- that says so: `g' ≤ g` reaches an entry output that is a *join* of
  -- outputs of `g`, and typing that join asks for join-closure of a type's
  -- extension, which is false at Σ.  A dominating graph `g₀ ≥ g` would fix
  -- that and break reflection along `lift` instead (see the note above
  -- `Evaluates.lift`), so lower-closure of typing has to become semantic.
  -- §5.5 of `presheaf-proof-strategy.md` has the counterexample and the
  -- options; `mono_l_sort` below is the part that survives here
  | lam {g A B d f} :
    ShapeFun.HasPi T d f .type →
    (∀ e ∈ g, ∃ c, Shape.WF Δ c ∧ Evaluates Δ f e.ty e.tm e.inp c ∧ T e.out c) →
    HasTypeS Δ T (.lam g) (.forallE A B d f)
  -- and here on a first component dominating the pair's own, because the
  -- code is read off at it and the lookup is monotone in its input
  | pair {ty tm x y x₀ c A B d f} :
    ShapeFun.HasPi T d f .type → Shape.LE Δ x x₀ → Shape.WF Δ x₀ → T x₀ d →
    Shape.WF Δ c → Evaluates Δ f ty tm x₀ c → T y c →
    HasTypeS Δ T (.pair ty tm x y) (.sigma A B d f)
  | refl {w A a b} : HasTypeS Δ T (.refl w) (.id true A a b)

/-- The base level, where the only shapes are `⊥` and the sorts. -/
def Shape.HasType (Δ : List Term) : ∀ {n}, Shape n → Shape n → Prop
  | 0 => HasType0
  | _ + 1 => HasTypeS Δ (HasType Δ)

/-- The recursion equations, for `cases` and `rw`, which do not unfold the
definition. -/
theorem Shape.hasType_zero {Δ : List Term} {m a : Shape 0} :
    Shape.HasType Δ m a ↔ Shape.HasType0 m a := Iff.rfl


theorem Shape.hasType_succ {Δ : List Term} {n} {m a : Shape (n + 1)} :
    HasType Δ m a ↔ HasTypeS Δ (HasType Δ) m a := Iff.rfl

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

private theorem Bool.eq_true_of_le {r s : Bool} (h : r = true) (hrs : r ≤ s) : s = true := by
  subst h; revert hrs; cases s <;> decide

private theorem Bool.le_true' (r : Bool) : r ≤ true := by cases r <;> decide

private theorem Bool.le_tr {t r s : Bool} (h₁ : t ≤ r) (h₂ : r ≤ s) : t ≤ s := by
  revert h₁ h₂; cases t <;> cases r <;> cases s <;> decide

/-- The universes are cumulative: a `prop` is also a `type`. -/
theorem Shape.HasType.cumul {n} {a : Shape n} {r s : Bool}
    (h : Shape.HasType Δ a (.sort r)) (hrs : r ≤ s) : Shape.HasType Δ a (.sort s) := by
  induction n with
  | zero =>
    cases h with | bot => exact .bot | sort
    cases Bool.eq_true_of_le rfl hrs; exact .sort
  | succ n ih
  cases h with
  | bot _ => exact .bot .sort
  | sort => cases Bool.eq_true_of_le rfl hrs; exact .sort
  | nat => cases Bool.eq_true_of_le rfl hrs; exact .nat
  | sigma hpi => cases Bool.eq_true_of_le rfl hrs; exact .sigma hpi
  | unit hle => exact .unit (Bool.le_tr hle hrs)
  | id hle => exact .id (Bool.le_tr hle hrs)
  | forallE hpi => exact .forallE (hpi.cod ih)

/-- `⊥` inhabits every type; at positive level this is the constructor. -/
theorem Shape.HasType.bot {n} {a : Shape n}
    (h : Shape.HasType Δ a .type) : Shape.HasType Δ .bot a :=
  match n with
  | 0 => Shape.HasType0.bot
  | _+1 => Shape.HasTypeS.bot h

/-- A sort is a type, at any level. -/
theorem Shape.HasType.sort {Δ : List Term} {n} {r : Bool} :
    Shape.HasType Δ (.sort r : Shape n) .type :=
  match n with
  | 0 => Shape.HasType0.sort
  | _+1 => Shape.HasTypeS.sort

/-- Hence `⊥` inhabits every sort. -/
theorem Shape.HasType.bot_sort {Δ : List Term} {n} {r : Bool} :
    Shape.HasType Δ (.bot : Shape n) (.sort r) := Shape.HasType.bot Shape.HasType.sort

/-- Anything typed has a type that is itself a type.  Now one line per
constructor: the inversion the inductive gives us does the case analysis
that used to be done by hand on both arguments. -/
theorem Shape.HasType.isType : ∀ {n} {m a : Shape n},
    Shape.HasType Δ m a → Shape.HasType Δ a .type := by
  intro n
  cases n with
  | zero =>
    intro m a h
    cases h with
    | bot => cases a with | bot => exact Shape.HasType0.bot | sort => exact .sort
    | sort => exact .sort
  | succ n =>
    intro m a h
    cases h with
    | bot h => exact h
    | sort | unit | id | nat | forallE | sigma => exact .sort
    | zero | succ => exact .nat
    | lam hpi => exact .forallE hpi
    | pair hpi => exact .sigma hpi
    | refl => exact .id (Bool.le_true' true)

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

theorem ShapeFun.HasDom.subst_of {Δ Θ : List Term} {τ : Subst} {n} {f : ShapeFun n}
    {d : Shape n} (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ)
    (ih : ∀ {m a : Shape n}, Shape.HasType Δ m a → Shape.HasType Θ (m.subst τ) (a.subst τ))
    (h : ShapeFun.HasDom Δ (Shape.HasType Δ) f d) :
    ShapeFun.HasDom Θ (Shape.HasType Θ) (ShapeFun.subst (Shape.subst · τ) τ f)
      (d.subst τ) := by
  intro e' he'
  obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
  have ⟨x, hwx, hx, hxle, hev⟩ := h e he
  exact ⟨x.subst τ, hwx.subst hΘ W, ih hx, Shape.LE.subst hΘ W hxle, hev.subst hΘ W⟩

/-- Numerals are stable under substitution: there is nothing in them but
shape. -/
theorem Shape.IsNumeral.subst {τ : Subst} : ∀ {n} {v : Shape n},
    Shape.IsNumeral v → Shape.IsNumeral (v.subst τ) := by
  intro n v h
  induction h with
  | bot => rw [Shape.subst_bot]; exact .bot
  | zero => exact .zero
  | succ _ ih => exact .succ ih

theorem ShapeFun.HasPi.subst_of {Δ Θ : List Term} {τ : Subst} {n} {d : Shape n}
    {f : ShapeFun n} {a : Shape n}
    (ih : ∀ {m a : Shape n}, Shape.HasType Δ m a → Shape.HasType Θ (m.subst τ) (a.subst τ))
    (h : f.HasPi (Shape.HasType Δ) d a) :
    (f.subst (Shape.subst · τ) τ).HasPi (Shape.HasType Θ) (d.subst τ) (a.subst τ) := by
  refine ⟨by simpa using ih h.1, fun e' he' => ?_⟩
  obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
  exact ih (h.2 e he)

/-- Typing of shapes is stable along a typed substitution. -/
theorem Shape.HasType.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) : ∀ {n} {m a : Shape n},
    Shape.HasType Δ m a → Shape.HasType Θ (m.subst τ) (a.subst τ) := by
  intro n
  induction n with
  | zero =>
    intro m a h
    cases h with
    | bot => exact Shape.HasType0.bot
    | sort => exact .sort
  | succ n ih =>
    intro m a h
    replace h : Shape.HasTypeS Δ (Shape.HasType Δ) m a := h
    induction h with
    | bot _ ihb => exact .bot ihb
    | sort => exact .sort
    | unit hle => exact .unit hle
    | nat => exact .nat
    | zero => exact .zero
    | succ hN => exact .succ hN.subst
    | id hle => exact .id hle
    | forallE hpi =>
      exact .forallE (by simpa using hpi.subst_of ih)
    | sigma hpi => exact .sigma (by simpa using hpi.subst_of ih)
    | lam hpi hcod =>
      refine .lam (by simpa using hpi.subst_of ih) fun e' he' => ?_
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have ⟨c, hwc, hev, hty⟩ := hcod e he
      exact ⟨c.subst τ, Shape.WF.subst hΘ W hwc, Evaluates.subst hΘ W hev, ih hty⟩
    | pair hpi hxle hwx hxd hwc hev hyc =>
      exact .pair (by simpa using hpi.subst_of ih) (hxle.subst hΘ W)
        (hwx.subst hΘ W) (ih hxd) (hwc.subst hΘ W) (hev.subst hΘ W) (ih hyc)
    | refl => exact .refl

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
query.  This is the characterisation the normalisation of `HasDom`'s
witness runs on: it replaces reasoning about derivations by reasoning
about two joins over one sublist, so the cycle argument's states carry no
derivation at all.

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

/-- The lookup is monotone in the graph, plainly: a dominating graph
reaches at least as much.  `mono_graph` below adds that the witness can be
taken to be a type; this version needs no typing at all and is what the
`lam`/`pair` cases of `mono_r` use, since they transport the code back down
with `lower` rather than retyping at a bigger one. -/
theorem Evaluates.mono_graph' {Δ : List Term} (hΔ : ⊢ Δ) {n} {f f' : ShapeFun n}
    {A a : Term} {x : Shape n} (hwf : ∀ e ∈ f', Shape.WF Δ e.out)
    (hff' : ShapeFun.LE Δ (Shape.LE Δ) (Shape.WF Δ) f f') :
    ∀ {c : Shape n}, Evaluates Δ f A a x c →
      ∃ c', Evaluates Δ f' A a x c' ∧ Shape.LE Δ c c' := by
  intro c h
  -- with lookup coverage the transport is exact, so the dominating witness
  -- is the shape itself; `Eval.wf` supplies the reflexivity `WF`
  have h' := ShapeFun.Eval.trans (R := Shape.LE Δ)
    (fun _ _ _ h₁ h₂ => h₁.trans hΔ h₂) hff'.1 h
  exact ⟨c, h', Shape.LE.refl (ShapeFun.Eval.wf hΔ hwf h')⟩

/-! ## Monotonicity on the right, and typed joins

These two are **mutually recursive on the level** and so are proved
together: `mono_r` at level `n+1` uses `mono_graph`, whose `join` case
needs typed joins at level `n`; and typed joins at level `n+1` need
`mono_r` at level `n` to move an entry's input from one domain shape up to
the joined one.  Both descend, so one induction on the level does it.

`mono_r` is monotone on the **right** only.  `HasType` is not monotone on
the left, and the hypothesis that the larger type is itself a type is what
lets it avoid needing that. -/
theorem Shape.HasType.mono_r_join (hΔ : ⊢ Δ) : ∀ {n},
    (∀ {m a a' : Shape n} {r : Bool}, Shape.WF Δ m → Shape.WF Δ a' →
      Shape.HasType Δ m a → Shape.LE Δ a a' → Shape.HasType Δ a' (.sort r) →
      Shape.HasType Δ m a') ∧
    (∀ {y z : Shape n} {r : Bool}, Shape.WF Δ y → Shape.WF Δ z → Shape.Compat Δ y z →
      Shape.HasType Δ y (.sort r) → Shape.HasType Δ z (.sort r) →
      Shape.HasType Δ (y.join z) (.sort r)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun {m a a' r} _ _ h hle hA => ?_, fun {y z r} _ _ _ hy hz => ?_⟩
    · cases m with | bot => exact Shape.HasType0.bot | sort s
      let .sort j := a; let .sort j' := a'; cases h; cases hle; exact .sort
    · cases y with | bot => exact hz | sort s
      cases z with | bot => exact hy | sort s'
      exact hy
  | succ n ih
  obtain ⟨ihm, ihj⟩ := ih
  refine ⟨fun {m a a' r} hwm hwa h hle hA => ?_, fun {y z r} hwy hwz hc hy hz => ?_⟩
  · -- mono_r
    cases h with
    | bot _ => exact .bot (Shape.HasType.cumul hA (Bool.le_true' r))
    | sort => cases a' with | sort => cases hle; exact .sort | _ => cases hle
    | nat => cases a' with | sort => cases hle; exact .nat | _ => cases hle
    | sigma hpi => cases a' with | sort => cases hle; exact .sigma hpi | _ => cases hle
    | unit hj => cases a' with | sort => cases hle; exact .unit hj | _ => cases hle
    | id hj => cases a' with | sort => cases hle; exact .id hj | _ => cases hle
    | forallE hpi => cases a' with | sort => cases hle; exact .forallE hpi | _ => cases hle
    | zero => cases a' with | nat => exact .zero | _ => cases hle
    | succ hN => cases a' with | nat => exact .succ hN | _ => cases hle
    | refl => cases a' with | id => cases hle.1; exact .refl | _ => cases hle
    | lam hpi hcod =>
      cases a' with | forallE A₁ B₁ d' f' => ?_ | _ => cases hle
      cases hA with | forallE hpiA
      refine .lam (hpiA.cod (Shape.HasType.cumul · (Bool.le_true' r))) fun e he => ?_
      have ⟨c, hwc, hev, hcty⟩ := hcod e he
      have ⟨c', hev', hcle⟩ := hev.mono_graph' hΔ
        (fun e' he' => (hwa.2.2.2.1 e' he').2.2.2) hle.2.2
      exact ⟨c, hwc, .lower hcle hev', hcty⟩
    | pair hpi hxle hwx hxd hwc hev hyc =>
      cases a' with | sigma A₁ B₁ d' f' => ?_ | _ => cases hle
      cases hA with | sigma hpiA => ?_
      have hd' : Shape.HasType Δ d' .type := hpiA.1
      have ⟨c', hev', hcle⟩ := hev.mono_graph' hΔ
        (fun e' he' => (hwa.2.2.2.1 e' he').2.2.2) hle.2.2
      exact .pair hpiA hxle hwx (ihm hwx hwa.2.2.1 hxd hle.2.1 hd') hwc (.lower hcle hev') hyc
  · -- typed joins
    cases y with
    | bot => exact hz
    | forallE A₀ B₀ d f =>
      cases z with | bot => exact hy | forallE A₁ B₁ d' g => ?_ | _ => cases hc
      cases hy with | forallE hpy
      cases hz with | forallE hpz
      refine .forallE ⟨ihj hwy.2.2.1 hwz.2.2.1 hc.2.1 hpy.1 hpz.1, fun e he => ?_⟩
      match List.mem_append.1 he with
      | .inl he => exact hpy.2 e he
      | .inr he => exact hpz.2 e he
    | sigma A₀ B₀ d f =>
      cases z with | bot => exact hy | sigma A₁ B₁ d' g => ?_ | _ => cases hc
      cases hy with | sigma hpy
      cases hz with | sigma hpz
      refine .sigma ⟨ihj hwy.2.2.1 hwz.2.2.1 hc.2.1 hpy.1 hpz.1, fun e he => ?_⟩
      match List.mem_append.1 he with
      | .inl he => exact hpy.2 e he
      | .inr he => exact hpz.2 e he
    | _ => cases z <;> first | exact hy | cases hy

/-- Typing is monotone on the right. -/
theorem Shape.HasType.mono_r (hΔ : ⊢ Δ) {n} {m a a' : Shape n} {r : Bool}
    (hwm : Shape.WF Δ m) (hwa : Shape.WF Δ a') (h : Shape.HasType Δ m a)
    (hle : Shape.LE Δ a a') (hA : Shape.HasType Δ a' (.sort r)) :
    Shape.HasType Δ m a' := (Shape.HasType.mono_r_join hΔ).1 hwm hwa h hle hA

/-- The join of two types is a type. -/
theorem Shape.HasType.join (hΔ : ⊢ Δ) {n} {y z : Shape n} {r : Bool}
    (hwy : Shape.WF Δ y) (hwz : Shape.WF Δ z) (hc : Shape.Compat Δ y z)
    (hy : Shape.HasType Δ y (.sort r)) (hz : Shape.HasType Δ z (.sort r)) :
    Shape.HasType Δ (y.join z) (.sort r) := (Shape.HasType.mono_r_join hΔ).2 hwy hwz hc hy hz

/-! ## Reading the lookup off, once the graph's outputs are typed

Two forms, and the difference between them is the whole reason the `lam`
typing clause is where the order change bites (§5.3).  `hasType` types the
value *itself*, and so needs the type's extension to be closed under
lowering and joins; `bounded` only produces a typed value *above* it, and
needs neither -- the `lower` case keeps the bigger witness and the `join`
case joins the two witnesses.  At a sort both are available, since
`HasType.mono_l` and `HasType.join` are exactly those two closures. -/

/-- Everything the lookup returns is typed, given that the type's extension
is a lower set closed under compatible joins.  Both closures are
hypotheses, because at the level where this is used -- inside `mono_l`'s
own induction -- lowering is the induction hypothesis. -/
theorem Evaluates.hasType (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a : Term} {x t : Shape n}
    (hwf : ∀ e ∈ f, Shape.WF Δ e.out) (htt : Shape.HasType Δ t .type)
    (hty : ∀ e ∈ f, Shape.HasType Δ e.out t)
    (hlower : ∀ {m m' : Shape n}, Shape.LE Δ m' m →
      Shape.HasType Δ m t → Shape.HasType Δ m' t)
    (hjoin : ∀ {y z : Shape n}, Shape.WF Δ y → Shape.WF Δ z → Shape.Compat Δ y z →
      Shape.HasType Δ y t → Shape.HasType Δ z t → Shape.HasType Δ (y.join z) t) :
    ∀ {c : Shape n}, Evaluates Δ f A a x c → Shape.HasType Δ c t := by
  intro c h
  induction h with
  | bot => exact Shape.HasType.bot htt
  | entry e he _ _ => exact hty e he
  | lower hle _ ih => exact hlower hle ih
  | join hc hy hz ih₁ ih₂ =>
    exact hjoin (Evaluates.wf hΔ hwf hy) (Evaluates.wf hΔ hwf hz) hc ih₁ ih₂

/-- Everything the lookup returns is below something the lookup returns
that is a type, in whatever sort the graph's outputs live.  A direct
induction: `lower` keeps the witness it was handed, and `join` joins the
two, which is compatible (`Evaluates.compat`), bounded (`le_join`, via
`Evaluates.wf`) and typed (`HasType.join`). -/
theorem Evaluates.bounded (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a : Term} {x : Shape n}
    {r : Bool} (hwf : ShapeFun.WF Δ (Shape.WF Δ) f) (hx : Shape.Compat Δ x x)
    (hty : ∀ e ∈ f, Shape.HasType Δ e.out (.sort r)) :
    ∀ {c : Shape n}, Evaluates Δ f A a x c →
      ∃ z, Evaluates Δ f A a x z ∧ Shape.LE Δ c z ∧ Shape.HasType Δ z (.sort r) := by
  have hout : ∀ e ∈ f, Shape.WF Δ e.out := fun e he => (hwf.1 e he).2.2.2
  intro c h
  induction h with
  | bot => exact ⟨.bot, .bot, Shape.LE.bot, Shape.HasType.bot_sort⟩
  | entry e he hlab hin =>
    exact ⟨e.out, .entry e he hlab hin, Shape.LE.refl (hout e he), hty e he⟩
  | lower hle _ ih =>
    have ⟨z, hz, hle', hzty⟩ := ih
    exact ⟨z, hz, hle.trans hΔ hle', hzty⟩
  | join _ _ _ ih₁ ih₂ =>
    have ⟨y', hy', hley, htyy⟩ := ih₁
    have ⟨z', hz', hlez, htyz⟩ := ih₂
    have hc : Shape.Compat Δ y' z' := Evaluates.compat hΔ hwf.2 hx hy' hz'
    have hwy := Evaluates.wf hΔ hout hy'
    have hwz := Evaluates.wf hΔ hout hz'
    have ⟨hu₁, hu₂⟩ := Shape.le_join hΔ hwy hwz hc
    exact ⟨y'.join z', .join hc hy' hz',
      Shape.join_le (hley.trans hΔ hu₁) (hlez.trans hΔ hu₂),
      Shape.HasType.join hΔ hwy hwz hc htyy htyz⟩

/-- The lookup is **monotone in the graph**, and what it returns is below
something the covering graph returns that is a type.  Master gets
monotonicity from `app_mono_l`, its lookup being a function; with lookup
coverage the transport is exact (`Eval.trans`, as in `mono_graph'`) and the
typing is `bounded`.  The order carries the covering graph's
well-formedness and coherence, so this needs neither as a hypothesis. -/
theorem Evaluates.mono_graph (hΔ : ⊢ Δ) {n} {f f' : ShapeFun n} {A a : Term}
    {x : Shape n} {r : Bool} (hx : Shape.Compat Δ x x)
    (hty : ∀ e ∈ f', Shape.HasType Δ e.out (.sort r))
    (hff' : ShapeFun.LE Δ (Shape.LE Δ) (Shape.WF Δ) f f')
    {c : Shape n} (h : Evaluates Δ f A a x c) :
    ∃ c', Evaluates Δ f' A a x c' ∧ Shape.LE Δ c c' ∧
      Shape.HasType Δ c' (.sort r) :=
  Evaluates.bounded hΔ hff'.2.2 hx hty
    (ShapeFun.Eval.trans (R := Shape.LE Δ) (fun _ _ _ h₁ h₂ => h₁.trans hΔ h₂) hff'.1 h)

/-- A Π/Σ signature is inherited by anything it dominates: the whole point
of stating it with a dominating pair. -/
theorem ShapeFun.HasPi.lower (hΔ : ⊢ Δ) {n}
    {d d' : Shape n} {f f' : ShapeFun n} {r : Bool}
    (ih : ∀ {m m' : Shape n}, Shape.LE Δ m' m →
      Shape.HasType Δ m (.sort r) → Shape.HasType Δ m' (.sort r))
    (ihty : ∀ {m m' : Shape n}, Shape.LE Δ m' m →
      Shape.HasType Δ m .type → Shape.HasType Δ m' .type)
    (hd : Shape.LE Δ d' d) (hf : ShapeFun.LE Δ (Shape.LE Δ) (Shape.WF Δ) f' f)
    (h : ShapeFun.HasPi (Shape.HasType Δ) d f (.sort r)) :
    ShapeFun.HasPi (Shape.HasType Δ) d' f' (.sort r) :=
  -- `hf.1 e he` is a lookup derivation, so this is `Evaluates.hasType`;
  -- the outputs live in a sort, where both closures it wants are theorems
  ⟨ihty hd h.1, fun e he =>
    Evaluates.hasType hΔ (fun e' he' => (hf.2.2.1 e' he').2.2.2)
      Shape.HasType.sort h.2 ih (Shape.HasType.join hΔ) (hf.1 e he)⟩

/-- **Left monotonicity**: a type is a lower set.  Master has only the
two-sided form (`WShape.HasType.mono_l`, a 70-line mutual induction whose
graph cases run a cycle argument); here the clauses were arranged so that
the genuine one-sided statement is an induction with no side conditions --
the dominating existentials in `HasPi`, `lam` and `pair` absorb the
approximation by transitivity, the componentwise clauses use the induction
hypothesis, and every `m' = ⊥` branch is `.bot (isType h)`. -/
theorem Shape.HasType.mono_l (hΔ : ⊢ Δ) {n} {m m' a : Shape n}
    (hle : Shape.LE Δ m' m) (h : Shape.HasType Δ m a) : Shape.HasType Δ m' a := by
  induction n with
  | zero =>
    cases m' with | bot => exact Shape.HasType0.bot | sort s
    cases m <;> cases hle; exact h
  | succ n ih
  have hty := h.isType
  cases h with
  | bot hb => cases Shape.le_bot_iff.1 hle; exact .bot hb
  | sort =>
    cases m' with | bot => exact .bot hty | sort s' => cases hle; exact .sort | _ => cases hle
  | unit hj =>
    cases m' with | bot => exact .bot hty | unit r' => cases hle; exact .unit hj | _ => cases hle
  | nat => cases m' with | bot => exact .bot hty | nat => exact .nat | _ => cases hle
  | zero => cases m' with | bot => exact .bot hty | zero => exact .zero | _ => cases hle
  | succ hN =>
    cases m' with | bot => exact .bot hty | succ => exact .succ (hN.lower hle) | _ => cases hle
  | id hj =>
    cases m' with | bot => exact .bot hty | id => cases hle.1; exact .id hj | _ => cases hle
  | forallE hpi =>
    cases m' with | bot => exact .bot hty | forallE => ?_ | _ => cases hle
    exact .forallE <| hpi.lower hΔ ih ih hle.2.1 hle.2.2
  | sigma hpi =>
    cases m' with | bot => exact .bot hty | sigma => ?_ | _ => cases hle
    exact .sigma <| hpi.lower hΔ ih ih hle.2.1 hle.2.2
  | lam hpi hcod =>
    cases m' with | bot => exact .bot hty | lam => ?_ | _ => cases hle
    refine .lam hpi fun e he => ?_
    -- FALSE as stated: see the `lam` constructor's comment and §5.5 of
    -- `presheaf-proof-strategy.md`.  Lower-closure at `lam` holds only of
    -- approximants of a term, so it belongs beside `sound`, not here.
    exact sorry
  | pair hpi hxle hwx hxd hwc hev hyc =>
    cases m' with | bot => exact .bot hty | pair => ?_ | _ => cases hle
    exact .pair hpi (hle.2.1.trans hΔ hxle) hwx hxd hwc (hev.label hle.1.symm) (ih hle.2.2.1 hyc)
  | refl => cases m' with | bot => exact .bot hty | refl => exact .refl | _ => cases hle

/-- **Left monotonicity at a sort**, which is the part of `mono_l` that is
true at the shape level.

The `lam`, `pair`, `zero`, `succ` and `refl` clauses cannot arise — their
types are a `forallE`, a `sigma`, `nat` and an `id` — so the case that
makes `mono_l` false never comes up, and what is left is `HasPi.lower` at
the two graph formers.  `SoundTy.hasType` uses exactly this. -/
theorem Shape.HasType.mono_l_sort {Δ : List Term} (hΔ : ⊢ Δ) :
    ∀ {n} {m m' : Shape n} {r : Bool},
    Shape.LE Δ m' m → Shape.HasType Δ m (.sort r) → Shape.HasType Δ m' (.sort r) := by
  intro n
  induction n with
  | zero =>
    intro m m' r hle h
    cases m' with | bot => exact Shape.HasType0.bot | sort s
    cases m <;> cases hle; exact h
  | succ n ih =>
    intro m m' r hle h
    have hty := h.isType
    cases h with
    | bot hb => cases Shape.le_bot_iff.1 hle; exact .bot hb
    | sort =>
      cases m' with | bot => exact .bot hty | sort s' => cases hle; exact .sort | _ => cases hle
    | unit hj =>
      cases m' with | bot => exact .bot hty | unit r' => cases hle; exact .unit hj | _ => cases hle
    | nat => cases m' with | bot => exact .bot hty | nat => exact .nat | _ => cases hle
    | id hj =>
      cases m' with | bot => exact .bot hty | id => cases hle.1; exact .id hj | _ => cases hle
    | forallE hpi =>
      cases m' with | bot => exact .bot hty | forallE => ?_ | _ => cases hle
      exact .forallE <| hpi.lower hΔ ih ih hle.2.1 hle.2.2
    | sigma hpi =>
      cases m' with | bot => exact .bot hty | sigma => ?_ | _ => cases hle
      exact .sigma <| hpi.lower hΔ ih ih hle.2.1 hle.2.2

/-! ## Proof irrelevance

`HasType Δ a .prop → HasType Δ x a → x = ⊥`: a proposition has no
information in it.  This is master's `HasType.proofIrrel`, and it is the
shape-level content of the syntactic `proofIrrel` rule.

Only the Π case has anything to it, and it is where dropping saturation
bites once more.  Master reads the codomain off the graph with the
function `ShapeFun.app` and recurses on its value directly.  Here the
codomain comes out of `Evaluates`, which may hand back a *lowering* of an
entry output, and `HasType · (.sort r)` is not downward closed — master's
`mono_l` is an equivalence (`m ≤ m'` and `m' ≤ m`), not monotonicity, so
it does not help either.  `Evaluates.bounded` is the way round: every
witness is below a witness that is a type, and `mono_r` retypes at that
one. -/

/-- Nothing but `⊥` is typed at `⊥`. -/
theorem Shape.HasType.bot_r {n} {x : Shape n} (h : Shape.HasType Δ x .bot) : x = .bot := by
  cases n <;> cases h <;> rfl

/-- A proposition is inhabited only by `⊥`. -/
theorem Shape.HasType.proofIrrel (hΔ : ⊢ Δ) {n} {a x : Shape n}
    (hwa : Shape.WF Δ a) (hwx : Shape.WF Δ x)
    (ha : Shape.HasType Δ a .prop) (h : Shape.HasType Δ x a) : x = .bot := by
  induction n with
  | zero => cases ha; exact Shape.HasType.bot_r h
  | succ n ih
  -- the inversion narrows `a` to the four formers that can be a `prop`
  cases ha with
  | bot _ => exact Shape.HasType.bot_r h
  | unit _ => cases h; rfl
  | @id r _ A₀ a₀ b₀ hj => let .false := r; cases h; rfl
  | @forallE A₀ B₀ d f _ hpi =>
    cases h with | bot _ => rfl | @lam g _ _ _ _ hpi' hcod
    -- a well-formed λ carries real information, so it cannot inhabit a
    -- Π-type whose codomain family is propositional
    have ⟨hne, hnb, hwg'⟩ := hwx
    have ⟨_, _, _, hwf⟩ := hwa
    have hco := hwf.2
    let e :: g' := g
    have ⟨c, hwc, hev, hcty⟩ := hcod e (.head _)
    have ⟨_, _, hi, ho⟩ := hwg'.1 e (.head _)
    have ⟨z, hevz, hcz, hzty⟩ := hev.bounded hΔ hwf (Shape.WF.coherent hi) hpi.2
    have hwz := hevz.wf hΔ fun e he => (hwf.1 e he).2.2.2
    have hbot := ih hwz ho hzty <| hcty.mono_r hΔ ho hwz hcz hzty
    cases hnb e (.head _) (hbot ▸ (by cases n <;> trivial))

/-! ## Lifting

`Interp` quantifies over `TShape`, so every notion it mentions has to be
transportable along `Shape.lift`.  For the order, well-formedness,
compatibility and the join that transport is an equivalence
(`Shape.lift_le_lift` and friends).  For typing it is **one-directional**:
lifting *up* preserves `HasType`, but the converse fails, because
`Evaluates.lower` can produce a witness at the higher level that is not
the lift of anything — the order on graphs is contravariant in the input,
so a shape below a lifted shape need not itself be a lift.  Master has the
equivalence only because its lookup is a function.

One direction is enough: `TShape.HasTypeOld` is defined at the canonical
level and read off at any higher one. -/

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
    Evaluates.tighten hΔ (ShapeFun.lift_wf h hwf) ((ShapeFun.lift_compat h).2 hco)
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
  refine ⟨fun e' he' => ?_, ShapeFun.lift_wf h H.2.1, ShapeFun.lift_wf h H.2.2⟩
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

/-- Lifting **preserves** typing, with no hypothesis at all.

Split off from `lift_iff` for the same reason as `Shape.lift_le`: only the
reflection direction needs `⊢ Δ` and well-formedness of both sides, and
every clause here gets the well-formedness it needs out of the constructor
it is looking at. -/
theorem Shape.HasType.lift {Δ : List Term} : ∀ {n k}, n ≤ k → ∀ {m a : Shape n},
    Shape.HasType Δ m a → Shape.HasType Δ (m.lift k) (a.lift k) := by
  intro n
  induction n with
  | zero =>
    intro k h m a H
    cases k with
    | zero => rwa [Shape.lift_self, Shape.lift_self]
    | succ k =>
      cases H with
      | bot => cases a with | bot => exact .bot (.bot .sort) | sort => exact .bot .sort
      | sort => exact .sort
  | succ n ih
  intro k h
  let k+1 := k; have h' := Nat.le_of_succ_le_succ h
  have ihs : ∀ {d : Shape n} {r : Bool}, Shape.HasType Δ d (.sort r) →
      Shape.HasType Δ (d.lift k) (.sort r) := by
    intro d r H
    have := ih h' (a := Shape.sort r) H
    rwa [Shape.lift_sort] at this
  have ihpi : ∀ {d : Shape n} {f : ShapeFun n} {r : Bool},
      ShapeFun.HasPi (Shape.HasType Δ) d f (.sort r) →
      ShapeFun.HasPi (Shape.HasType Δ) (d.lift k)
        (ShapeFun.lift (Shape.lift k) f) (.sort r) := by
    intro d f r hpi
    refine ⟨ihs hpi.1, fun e'' he'' => ?_⟩
    obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
    exact ihs (hpi.2 e he)
  intro m a H
  induction H with
  | bot _ ihb => exact .bot (by simpa only [Shape.lift_sort] using ihb)
  | sort => exact .sort
  | unit hj => exact .unit hj
  | nat => exact .nat
  | zero => exact .zero
  | succ hN => exact .succ ((Shape.IsNumeral.lift_iff h').2 hN)
  | id hj => exact .id hj
  | forallE hpi => exact .forallE (ihpi hpi)
  | sigma hpi => exact .sigma (ihpi hpi)
  | lam hpi hcod =>
    refine .lam (ihpi hpi) fun e'' he'' => ?_
    obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
    have ⟨c, hwc, hev, hcty⟩ := hcod e he
    exact ⟨c.lift k, (Shape.lift_wf h').2 hwc, hev.lift h', ih h' hcty⟩
  | pair hpi hxle hwx hxd hwc hev hyc =>
    exact .pair (ihpi hpi) (Shape.lift_le h' hxle) ((Shape.lift_wf h').2 hwx)
      (ih h' hxd) ((Shape.lift_wf h').2 hwc) (hev.lift h') (ih h' hyc)
  | refl => exact .refl

/-- **Fullness for typing.**  On the shapes that come from the level below,
the higher level types exactly what the lower one did. -/
theorem Shape.HasType.lift_iff {Δ : List Term} (hΔ : ⊢ Δ)
    {n k} (h : n ≤ k) {m a : Shape n} (hwm : Shape.WF Δ m) (hwa : Shape.WF Δ a) :
    Shape.HasType Δ (m.lift k) (a.lift k) ↔ Shape.HasType Δ m a := by
  induction n generalizing k with
  | zero =>
    cases k with | zero => rw [Shape.lift_self, Shape.lift_self] | succ k
    constructor <;> intro H
    · cases m with | bot => exact HasType0.bot | sort s
      cases a with | bot => cases H | sort j
      cases H with | sort => exact HasType0.sort
    · cases H with | sort => exact .sort | bot
      cases a with | sort r => exact .bot .sort | bot
      exact .bot (.bot .sort)
  | succ n ih
  let k+1 := k; have h' := Nat.le_of_succ_le_succ h
  have ihs {d : Shape n} {r : Bool} (hwd : Shape.WF Δ d) :
      Shape.HasType Δ (d.lift k) (.sort r) ↔ Shape.HasType Δ d (.sort r) := by
    have := ih h' (a := Shape.sort r) hwd (by cases n <;> trivial)
    rwa [Shape.lift_sort] at this
  have ihpi {d : Shape n} {f : ShapeFun n} {r : Bool}
      (hwd : Shape.WF Δ d) (hwf : ShapeFun.WF Δ (Shape.WF Δ) f) :
      ShapeFun.HasPi (Shape.HasType Δ) (d.lift k)
        (ShapeFun.lift (Shape.lift k) f) (.sort r) ↔
      ShapeFun.HasPi (Shape.HasType Δ) d f (.sort r) := by
    refine ⟨fun hpi => ⟨(ihs hwd).1 hpi.1, fun e he => ?_⟩, fun hpi => ⟨(ihs hwd).2 hpi.1, ?_⟩⟩
    · exact (ihs (hwf.1 e he).2.2.2).1 (hpi.2 _ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩))
    · intro e'' he''
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
      exact (ihs (hwf.1 e he).2.2.2).2 (hpi.2 e he)
  have ihcode {f : ShapeFun n} {A a : Term} {xin yout : Shape n}
      (hwf : ShapeFun.WF Δ (Shape.WF Δ) f) (hco : ShapeFun.Compat Shape.Compat Δ f f)
      (hty : ∀ e ∈ f, Shape.HasType Δ e.out .type)
      (hwx : Shape.WF Δ xin) (hwy : Shape.WF Δ yout)
      (H : ∃ c', Shape.WF Δ c' ∧
        Evaluates Δ (ShapeFun.lift (Shape.lift k) f) A a (xin.lift k) c' ∧
        Shape.HasType Δ (yout.lift k) c') :
      ∃ c, Shape.WF Δ c ∧ Evaluates Δ f A a xin c ∧ Shape.HasType Δ yout c := by
    have ⟨c', _, hev', hty'⟩ := H
    have houts : ∀ e ∈ f, Shape.WF Δ e.out := fun e he => (hwf.1 e he).2.2.2
    have ⟨c₀, hle, hev₀⟩ := Evaluates.lift_of hΔ h' hwf hco hwx hev'
    have ⟨c₁, hev₁, hc₀c₁, hc₁ty⟩ :=
      Evaluates.mono_graph hΔ hwx.coherent hty (ShapeFun.LE.refl hwf) hev₀
    have hwc₁ := Evaluates.wf hΔ houts hev₁
    refine ⟨c₁, hwc₁, hev₁, (ih h' hwy hwc₁).1 (Shape.HasType.mono_r (r := true) hΔ
      ((Shape.lift_wf h').2 hwy) ((Shape.lift_wf h').2 hwc₁) hty'
      (hle.trans hΔ (Shape.lift_le h' hc₀c₁)) ?_)⟩
    exact (ihs hwc₁).2 hc₁ty
  suffices ∀ {m a}, WF Δ m → WF Δ a →
      (HasType Δ (Shape.lift (k + 1) a) .type ↔ HasType Δ a .type) →
      (HasType Δ (Shape.lift (k + 1) m) (Shape.lift (k + 1) a) ↔ HasType Δ m a) from
    this hwm hwa <| this (a := .type) hwa trivial ⟨fun _ => .sort, fun _ => .sort⟩
  intro m a hwm hwa hs
  constructor <;> intro H
  · cases m with
    | bot =>
      cases H with | bot hb
      exact .bot (hs.1 hb)
    | sort s =>
      cases a with | sort j => ?_ | _ => cases H
      cases H with | sort => exact .sort
    | unit r =>
      cases a with | sort j => ?_ | _ => cases H
      cases H with | unit hj => exact .unit hj
    | nat =>
      cases a with | sort j => ?_ | _ => cases H
      cases H with | nat => exact .nat
    | zero => cases a with | nat => exact .zero | _ => cases H
    | id r A₀ a₀ b₀ =>
      cases a with | sort j => ?_ | _ => cases H
      cases H with | id hj => exact .id hj
    | refl w =>
      cases a with | id r A₁ a₁ b₁ => ?_ | _ => cases H
      cases H with | refl => exact .refl
    | succ v =>
      cases a with | nat => ?_ | _ => cases H
      cases H with | succ hN
      exact .succ ((Shape.IsNumeral.lift_iff h').1 hN)
    | forallE A B d f =>
      cases a with | sort r => ?_ | _ => cases H
      cases H with | forallE hpi
      exact .forallE ((ihpi hwm.2.2.1 hwm.2.2.2).1 hpi)
    | sigma A B d f =>
      cases a with | sort r => ?_ | _ => cases H
      cases H with | sigma hpi
      exact .sigma ((ihpi hwm.2.2.1 hwm.2.2.2).1 hpi)
    | lam g =>
      cases a with | forallE A₁ B₁ d f => ?_ | _ => cases H
      cases H with | lam hpi hcod
      let ⟨_, _, hwa₁, hwa₂⟩ := hwa
      have hwa₃ := hwa₂.2
      have hpi' := (ihpi hwa₁ hwa₂).1 hpi
      refine .lam hpi' fun e he => ?_
      let ⟨_, _, hwm₁, hwm₂⟩ := hwm.2.2.1 e he
      exact ihcode hwa₂ hwa₃ hpi'.2 hwm₁ hwm₂ (hcod _ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩))
    | pair ty tm x y =>
      cases a with | sigma A₁ B₁ d f => ?_ | _ => cases H
      cases H with | @pair _ _ _ _ X₀ C _ _ _ _ hpi hxle hwX hxd hwc hev hyc
      let ⟨_, _, hwd, hwf⟩ := hwa
      have hcf := hwf.2
      let ⟨_, _, hwx, hwy, _⟩ := hwm
      have hpi' := (ihpi hwd hwf).1 hpi
      have hwf' := ShapeFun.lift_wf h' hwf
      have hco' := (ShapeFun.lift_compat h' (f := f) (f' := f)).2 hcf
      -- the dominating first component `X₀` need not be a lift, but the
      -- entries the lookup at it actually uses are a lifted sublist, and
      -- their join *is* one
      have ⟨s, ji, jo, hs, hlab, hji, hwji, hjiX, hjo, hwjo, hCjo⟩ := hev.tighten hΔ hwf' hco' hwX
      simp only [ShapeFun.lift] at hs
      obtain ⟨s₀, hs₀, rfl⟩ := List.sublist_map hs
      rw [ShapeFun.map_lift_inp] at hji
      rw [ShapeFun.map_lift_out] at hjo
      have hwin (v) (hv : v ∈ s₀.map Entry.inp) : Shape.WF Δ v := by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hv
        exact (hwf.1 e (hs₀.subset he)).2.2.1
      have hmem (v) (hv : v ∈ s₀.map Entry.inp) : Shape.LE Δ (v.lift k) ji :=
        hji.le hwji _ (List.mem_map.2 ⟨v, hv, rfl⟩)
      have ⟨ji₀, hji₀, hwji₀, _⟩ := Shape.exists_joins_of_pairwise hΔ hwin fun v hv w hw =>
        (Shape.lift_compat h').1 <| hwji.coherent.of_common_upper hΔ (hmem v hv) (hmem w hw)
      have ⟨hji₁, hji₂⟩ := hji.uniq hwji ((Shape.lift_wf h').2 hwji₀) (hji₀.lift hΔ h' hwin hwji₀)
      have hcx : Shape.Compat Δ x ji₀ := (Shape.lift_compat h').1 <|
          hwX.coherent.of_common_upper hΔ hxle (hji₂.trans hΔ hjiX)
      have hwx₀ := hwx.join hΔ hcx hwji₀
      have hle₀ : Shape.LE Δ ((x.join ji₀).lift k) X₀ := by
        rw [← Shape.lift_join h']
        exact Shape.join_le hxle (hji₂.trans hΔ hjiX)
      have hx₀d := (ih h' hwx₀ hwd).1 (hxd.mono_l hΔ hle₀)
      have ⟨hu₁, hu₂⟩ := Shape.le_join hΔ hwx hwji₀ hcx
      have ⟨J, hJ, hwJ, hevJ⟩ :=
        Evaluates.of_sublist hΔ hwf hcf hwx₀.coherent hs₀
          (fun e he => hlab _ (List.mem_map.2 ⟨e, he, rfl⟩))
          (fun e he => (hji₀.le hwji₀ _ (List.mem_map.2 ⟨e, he, rfl⟩)).trans hΔ hu₂)
      have ⟨J', hevJ', hJJ', hJ'ty⟩ :=
        hevJ.mono_graph hΔ hwx₀.coherent hpi'.2 (.refl hwf)
      have hwJ' := hevJ'.wf hΔ fun e he => (hwf.1 e he).2.2.2
      refine .pair hpi' hu₁ hwx₀ hx₀d hwJ' hevJ' ((ih h' hwy hwJ').1 ?_)
      refine hyc.mono_r (r := true) hΔ ((Shape.lift_wf h').2 hwy)
        ((Shape.lift_wf h').2 hwJ') ?_ ?_
      · refine hCjo.trans hΔ <| hjo.min ((Shape.lift_wf h').2 hwJ') fun v hv => ?_
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
        exact Shape.lift_le h' ((hJ.le hwJ w hw).trans hΔ hJJ')
      · exact (ihs hwJ').2 hJ'ty
  · clear hs; induction H with
    | bot _ ihb => exact .bot <| ihb hwa <| by cases n <;> trivial
    | sort => exact .sort
    | unit hj => exact .unit hj
    | nat => exact .nat
    | zero => exact .zero
    | succ hN => exact .succ ((Shape.IsNumeral.lift_iff h').2 hN)
    | id hj => exact .id hj
    | forallE hpi => exact .forallE ((ihpi hwm.2.2.1 hwm.2.2.2).2 hpi)
    | sigma hpi => exact .sigma ((ihpi hwm.2.2.1 hwm.2.2.2).2 hpi)
    | lam hpi hcod =>
      refine .lam ((ihpi hwa.2.2.1 hwa.2.2.2).2 hpi) fun e'' he'' => ?_
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
      have ⟨c, hwc, hev, hcty⟩ := hcod e he
      exact ⟨c.lift k, (Shape.lift_wf h').2 hwc, hev.lift h',
        (ih h' (hwm.2.2.1 e he).2.2.2 hwc).2 hcty⟩
    | pair hpi hxle hwx hxd hwc hev hyc =>
      exact .pair ((ihpi hwa.2.2.1 hwa.2.2.2).2 hpi) (Shape.lift_le h' hxle)
        ((Shape.lift_wf h').2 hwx) ((ih h' hwx hwa.2.2.1).2 hxd)
        ((Shape.lift_wf h').2 hwc) (hev.lift h')
        ((ih h' hwm.2.2.2.1 hwc).2 hyc)
    | refl => exact .refl

/-- Typing at the total level: at the canonical level, and (by
`lift_mono`) at every level above it. -/
def TShape.HasTypeOld (Δ : List Term) (m a : TShape) : Prop :=
  Shape.HasType Δ (m.2.lift (max m.1 a.1)) (a.2.lift (max m.1 a.1))

/-- One direction only, for the reason given above: a witness at the
canonical level can be read at any higher level. -/
theorem TShape.HasTypeOld.def {Δ : List Term} (hΔ : ⊢ Δ) {m a : TShape} {k}
    (hwm : Shape.WF Δ m.2) (hwa : Shape.WF Δ a.2)
    (h1 : m.1 ≤ k) (h2 : a.1 ≤ k) (H : TShape.HasTypeOld Δ m a) :
    Shape.HasType Δ (m.2.lift k) (a.2.lift k) := by
  rw [show m.2.lift k = (m.2.lift (max m.1 a.1)).lift k from
        (Shape.lift_lift (Nat.le_max_left ..)).symm,
      show a.2.lift k = (a.2.lift (max m.1 a.1)).lift k from
        (Shape.lift_lift (Nat.le_max_right ..)).symm]
  exact (Shape.HasType.lift_iff hΔ (Nat.max_le.2 ⟨h1, h2⟩)
    ((Shape.lift_wf (Nat.le_max_left ..)).2 hwm)
    ((Shape.lift_wf (Nat.le_max_right ..)).2 hwa)).2 H

/-- At a common level the two agree. -/
theorem TShape.HasTypeOld.T {Δ : List Term} {n} {m a : Shape n} :
    TShape.HasTypeOld Δ (Shape.T m) (Shape.T a) ↔ Shape.HasType Δ m a := by
  show Shape.HasType Δ (m.lift (max n n)) (a.lift (max n n)) ↔ _
  rw [Nat.max_self, Shape.lift_self, Shape.lift_self]

/-- At a sort the two agree as well, without the levels having to match:
a sort is the same shape at every level, so the canonical level of
`⟨n, m⟩ : TShape` typed at `TShape.sort r` is just `n`. -/
theorem TShape.HasTypeOld.sort_T {Δ : List Term} {n} {m : Shape n} {r : Bool} :
    TShape.HasTypeOld Δ (Shape.T m) (TShape.sort r) ↔ Shape.HasType Δ m (Shape.sort r) := by
  show Shape.HasType Δ (m.lift (max n 0)) ((Shape.sort r).lift (max n 0)) ↔ _
  rw [Nat.max_zero, Shape.lift_self, Shape.lift_sort]

/-- Typing at the total level transports along a typed substitution of the
context.  The level is untouched, so the canonical level is too, and the
statement is `Shape.HasType.subst` with `lift_subst` on each side. -/
theorem TShape.HasTypeOld.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {m a : TShape} (H : TShape.HasTypeOld Δ m a) :
    TShape.HasTypeOld Θ (m.subst τ) (a.subst τ) := by
  show Shape.HasType Θ (Shape.lift (max m.1 a.1) (m.2.subst τ))
    (Shape.lift (max m.1 a.1) (a.2.subst τ))
  rw [Shape.lift_subst, Shape.lift_subst]
  exact Shape.HasType.subst hΘ W H

/-- Left monotonicity at the total level: lift both sides to a level above
everything, use `Shape.HasType.mono_l` there, and reflect back down with
`lift_iff` -- the reflection direction is what makes this statable at all. -/
theorem TShape.HasTypeOld.mono_l {Δ : List Term} (hΔ : ⊢ Δ) {m m' a : TShape}
    (hwm : Shape.WF Δ m.2) (hwm' : Shape.WF Δ m'.2) (hwa : Shape.WF Δ a.2)
    (hle : TShape.LE Δ m' m) (H : TShape.HasTypeOld Δ m a) : TShape.HasTypeOld Δ m' a := by
  have h1 : m.1 ≤ max (max m.1 a.1) (max m'.1 a.1) :=
    Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..)
  have h2 : a.1 ≤ max (max m.1 a.1) (max m'.1 a.1) :=
    Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..)
  have h3 : m'.1 ≤ max (max m.1 a.1) (max m'.1 a.1) :=
    Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..)
  have key := Shape.HasType.mono_l hΔ ((TShape.LE.def_mp h3 h1) hle)
    (TShape.HasTypeOld.def hΔ hwm hwa h1 h2 H)
  show Shape.HasType Δ (m'.2.lift (max m'.1 a.1)) (a.2.lift (max m'.1 a.1))
  refine (Shape.HasType.lift_iff hΔ (Nat.max_le.2 ⟨h3, h2⟩)
    ((Shape.lift_wf (Nat.le_max_left ..)).2 hwm')
    ((Shape.lift_wf (Nat.le_max_right ..)).2 hwa)).1 ?_
  rwa [Shape.lift_lift (Nat.le_max_left ..), Shape.lift_lift (Nat.le_max_right ..)]

/-- Right monotonicity at the total level, by the same lift-and-reflect. -/
theorem TShape.HasTypeOld.mono_r {Δ : List Term} (hΔ : ⊢ Δ) {m a a' : TShape} {r : Bool}
    (hwm : Shape.WF Δ m.2) (hwa : Shape.WF Δ a.2) (hwa' : Shape.WF Δ a'.2)
    (H : TShape.HasTypeOld Δ m a) (hle : TShape.LE Δ a a')
    (hA : TShape.HasTypeOld Δ a' (TShape.sort r)) : TShape.HasTypeOld Δ m a' := by
  have h1 : m.1 ≤ max (max m.1 a.1) (max a'.1 0) :=
    Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..)
  have h2 : a.1 ≤ max (max m.1 a.1) (max a'.1 0) :=
    Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..)
  have h3 : a'.1 ≤ max (max m.1 a.1) (max a'.1 0) :=
    Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..)
  have hAk := TShape.HasTypeOld.def (a := TShape.sort r) hΔ hwa' trivial h3 (Nat.zero_le _) hA
  rw [show ((TShape.sort r).2.lift (max (max m.1 a.1) (max a'.1 0))) = Shape.sort r from
    Shape.lift_sort] at hAk
  have key := Shape.HasType.mono_r hΔ ((Shape.lift_wf h1).2 hwm) ((Shape.lift_wf h3).2 hwa')
    (TShape.HasTypeOld.def hΔ hwm hwa h1 h2 H) ((TShape.LE.def_mp h2 h3) hle) hAk
  show Shape.HasType Δ (m.2.lift (max m.1 a'.1)) (a'.2.lift (max m.1 a'.1))
  refine (Shape.HasType.lift_iff hΔ (Nat.max_le.2 ⟨h1, h3⟩)
    ((Shape.lift_wf (Nat.le_max_left ..)).2 hwm)
    ((Shape.lift_wf (Nat.le_max_right ..)).2 hwa')).1 ?_
  rwa [Shape.lift_lift (Nat.le_max_left ..), Shape.lift_lift (Nat.le_max_right ..)]

/-- Cumulativity at the total level. -/
theorem TShape.HasTypeOld.cumul {Δ : List Term} {a : TShape} {r s : Bool}
    (h : TShape.HasTypeOld Δ a (TShape.sort r)) (hrs : r ≤ s) :
    TShape.HasTypeOld Δ a (TShape.sort s) := by
  show Shape.HasType Δ (Shape.lift (max a.1 0) a.2) (Shape.lift (max a.1 0) (Shape.sort s))
  rw [Shape.lift_sort]
  exact Shape.HasType.cumul (by rw [← Shape.lift_sort (m := max a.1 0)]; exact h) hrs

/-! ## Reflection of `HasDom` along `lift`, and join-closure of typing

Both are **removed**, not deferred.

Join-closure of typing at an arbitrary type (`join_at`) has no counterpart
in the other repo: its directedness lemmas (`pi_isDirected`,
`abstraction_isDirected`, `succ_isDirected`) are all about *values*, which
are ideals there and directed by construction, never about the extension of
a type.  Master needs it only because its interpretation is a relation, so
soundness's `tr` case has two interpretations to combine; whether ours does
too is a question for `Interp`, where compatibility of any two elements is
automatic and the obstruction below does not arise.

The obstruction: with the `pair` clause stated about a *dominating* first
component -- which is what makes it downward closed, hence `mono_l` -- two
compatible pairs can carry incompatible dominators, so there is no shape
above `x₁ ⊔ x₂` at which to read a code.  The same shape of problem removes
`HasDom` reflection along `lift`: the `lam` clause's dominating graph at
the level above need not be a lift.

Everything the cycle argument was built for went with them:
`Evaluates.retype`, `Shape.HasType.exists_joins`, `ShapeFun.HasDom.step`,
`ShapeFun.HasDom.normalize`, `ShapeFun.HasDom.lift_of`/`lift_iff`.
`find_cycle`, `List.Sublist.union`/`allSublists`/`sublist_map`,
`Shape.Joins` and `Evaluates.tighten`/`of_sublist`/`joins_iff` all stay --
they are independent, and `Evaluates.lift_of` is proved from them. -/

/-! ## Typing over `TShape`, as one inductive

`TShape.HasTypeOld` above is `Shape.HasType` at the canonical level, so it
is defined by *recursion on the level* and every fact about it has to be
transported along `lift` — and the reflection direction of that transport
is what `Shape.HasType.lift_iff` costs.  That is also what makes
`Shape.HasType.mono_l` unfixable at `lam` (§5.5 of
`presheaf-proof-strategy.md`): the clause has to be per entry to reflect,
and per entry it is not closed under the order, whose lookup has joins.

Defined directly on `TShape` there is nothing to reflect.  A clause either
**pins** its subject, when everything strictly below the shape is `⊥` and
the `bot` clause takes it, or **bounds** it — the other repo's pattern,
*the conditions constrain a generator above the shape being classified,
never the shape itself* (`ΩLower`, `piGenerator`).  Three clauses have to
bound: `succ`, because `.succ v'` sits below `.succ v` for every `v' ≤ v`;
`id` and `refl`, because their subject's well-formedness is not free and
the bound is exactly what supplies it; `sort`, because its generator may
sit at level `0`, where the level surgery `at_succ` does for the others is
not available; and `lam`/`pair`, where the dominating generator is the
whole point (§5.5).  The type index is pinned throughout except at `lam`,
`pair` and `refl`, where it may grow.

The codomain witness of `lam` is a **function** `cs`, not an `∃` inside
the premise: `∃ c, … ∧ HasType …` would put the inductive under `Exists`,
and the kernel refuses a nested inductive whose parameters mention locals
(here `Shape n'` mentions `n'`).  `HasTypeS` is not affected because there
the recursive slot is its parameter `T`.  For the same reason the
constructors spell `ShapeFun.THasPi` out: the kernel will not take the
inductive being declared as an argument to a definition. -/

/-- The order carries the well-formedness of its lower bound at the total
level too, which is `Shape.LE.wf` through the canonical level. -/
theorem TShape.LE.wf {Δ : List Term} {a b : TShape} (h : TShape.LE Δ a b) :
    TShape.WF Δ a :=
  (Shape.lift_wf (Nat.le_max_left ..)).1 (Shape.LE.wf h)

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
    ∃ M, Shape.LE Δ (s.lift (M+1)) (t.lift (M+1)) := by
  obtain ⟨M, hM⟩ : ∃ M, max j (n+1) = M+1 := by
    cases hmax : max j (n+1) with
    | zero => exact absurd (hmax ▸ Nat.le_max_right j (n+1)) (by omega)
    | succ M => exact ⟨M, rfl⟩
  refine ⟨M, ?_⟩
  have h2 : Shape.LE Δ (Shape.lift (max j (n+1)) s) (Shape.lift (max j (n+1)) t) := h
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

/-- `ShapeFun.HasPi`, over `TShape`.  Only for stating lemmas; the
constructors spell it out. -/
def ShapeFun.THasPi (T : TShape → TShape → Prop) {n}
    (d : Shape n) (f : ShapeFun n) (a : TShape) : Prop :=
  T d.T TShape.type ∧ ∀ e ∈ f, T e.out.T a

/-- Typing, over `TShape`. -/
inductive TShape.HasType (Δ : List Term) : TShape → TShape → Prop where
  | bot : HasType Δ a TShape.type → HasType Δ (Shape.T (n := n) .bot) a
  | sort : TShape.LE Δ m (Shape.T (n := n) (.sort r)) →
    HasType Δ m (Shape.T (n := k) .type)
  | unit : r ≤ j → HasType Δ (Shape.T (n := n+1) (.unit r)) (Shape.T (n := k) (.sort j))
  | nat : HasType Δ (Shape.T (n := n+1) .nat) (Shape.T (n := k) .type)
  | zero : HasType Δ (Shape.T (n := n+1) .zero) (Shape.T (n := k+1) .nat)
  | succ {m n k} {v : Shape n} : Shape.IsNumeral v →
    TShape.LE Δ m (Shape.T (n := n+1) (.succ v)) →
    HasType Δ m (Shape.T (n := k+1) .nat)
  | id {m n k r j} {A x y : Term} : r ≤ j →
    TShape.LE Δ m (Shape.T (n := n+1) (.id r A x y)) →
    HasType Δ m (Shape.T (n := k) (Shape.sort j))
  | forallE {m n k} {A B : Term} {d : Shape n} {f : ShapeFun n} {r j : Bool} :
    HasType Δ d.T TShape.type →
    (∀ e ∈ f, HasType Δ e.out.T (TShape.sort r)) → r ≤ j →
    TShape.LE Δ m (Shape.T (n := n+1) (.forallE A B d f)) →
    HasType Δ m (Shape.T (n := k) (Shape.sort j))
  | sigma {m n k} {A B : Term} {d : Shape n} {f : ShapeFun n} :
    HasType Δ d.T TShape.type →
    (∀ e ∈ f, HasType Δ e.out.T TShape.type) →
    TShape.LE Δ m (Shape.T (n := n+1) (.sigma A B d f)) →
    HasType Δ m (Shape.T (n := k) (Shape.sort true))
  | lam {m a n₀ n'} {g₀ : ShapeFun n₀} {f : ShapeFun n'} {A B : Term} {d : Shape n'}
      (cs : Entry (Shape n₀) → TShape) :
    HasType Δ d.T TShape.type →
    (∀ e ∈ f, HasType Δ e.out.T TShape.type) →
    (∀ e ∈ g₀, TEvaluates Δ f e.ty e.tm e.inp.T (cs e)) →
    (∀ e ∈ g₀, HasType Δ e.out.T (cs e)) →
    TShape.LE Δ m (Shape.T (n := n₀+1) (.lam g₀)) →
    TShape.LE Δ (Shape.T (n := n'+1) (.forallE A B d f)) a →
    HasType Δ a TShape.type → HasType Δ m a
  | pair {m a n₀ n'} {ty tm : Term} {x₀ y₀ : Shape n₀} {c : TShape}
      {A B : Term} {d : Shape n'} {f : ShapeFun n'} :
    HasType Δ d.T TShape.type →
    (∀ e ∈ f, HasType Δ e.out.T TShape.type) →
    HasType Δ x₀.T d.T →
    TEvaluates Δ f ty tm x₀.T c → HasType Δ y₀.T c →
    TShape.LE Δ m (Shape.T (n := n₀+1) (.pair ty tm x₀ y₀)) →
    TShape.LE Δ (Shape.T (n := n'+1) (.sigma A B d f)) a →
    HasType Δ a TShape.type → HasType Δ m a
  | refl {m a n k} {w : Shape n} {A x y : Term} :
    TShape.LE Δ m (Shape.T (n := n+1) (.refl w)) →
    TShape.LE Δ (Shape.T (n := k+1) (.id true A x y)) a →
    HasType Δ a TShape.type → HasType Δ m a

/-- **Everything a shape is typed at is a type.** -/
theorem TShape.HasType.isType {Δ : List Term} {m a : TShape}
    (H : TShape.HasType Δ m a) : TShape.HasType Δ a TShape.type := by
  induction H with
  | bot hA _ => exact hA
  | sort _ => exact .sort (TShape.LE.refl Shape.WF.sort)
  | unit _ => exact .sort (TShape.LE.refl Shape.WF.sort)
  | nat => exact .sort (TShape.LE.refl Shape.WF.sort)
  | zero => exact .nat
  | succ _ _ => exact .nat
  | id _ _ => exact .sort (TShape.LE.refl Shape.WF.sort)
  | forallE _ _ _ _ _ _ => exact .sort (TShape.LE.refl Shape.WF.sort)
  | sigma _ _ _ _ _ => exact .sort (TShape.LE.refl Shape.WF.sort)
  | lam _ _ _ _ _ _ _ hA _ _ _ _ => exact hA
  | pair _ _ _ _ _ _ _ hA _ _ _ _ _ => exact hA
  | refl _ _ hA _ => exact hA

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
  | sort hg => exact fun h => .sort (h.trans hΔ hg)
  | unit hj =>
    exact fun {m'} h => by
      obtain ⟨j, s⟩ := m'
      obtain ⟨M, h2⟩ := TShape.LE.at_succ h
      cases j <;> cases s <;> first
        | exact .bot (.sort (TShape.LE.refl Shape.WF.sort))
        | (cases h2; exact .unit hj)
        | exact absurd h2 (fun x => x)
  | nat =>
    exact fun {m'} h => by
      obtain ⟨j, s⟩ := m'
      obtain ⟨M, h2⟩ := TShape.LE.at_succ h
      cases j <;> cases s <;> first
        | exact .bot (.sort (TShape.LE.refl Shape.WF.sort))
        | exact .nat
        | exact absurd h2 (fun x => x)
  | zero =>
    exact fun {m'} h => by
      obtain ⟨j, s⟩ := m'
      obtain ⟨M, h2⟩ := TShape.LE.at_succ h
      cases j <;> cases s <;> first
        | exact .bot .nat
        | exact .zero
        | exact absurd h2 (fun x => x)
  | succ hN hg => exact fun h => .succ hN (h.trans hΔ hg)
  | id hj hg => exact fun h => .id hj (h.trans hΔ hg)
  | forallE hd hf hj hg _ _ => exact fun h => .forallE hd hf hj (h.trans hΔ hg)
  | sigma hd hf hg _ _ => exact fun h => .sigma hd hf (h.trans hΔ hg)
  | lam cs hd hf hev hty hg hc hA _ _ _ _ =>
    exact fun h => .lam cs hd hf hev hty (h.trans hΔ hg) hc hA
  | pair hd hf hxd hev hyc hg hc hA _ _ _ _ _ =>
    exact fun h => .pair hd hf hxd hev hyc (h.trans hΔ hg) hc hA
  | refl hg hc hA _ => exact fun h => .refl (h.trans hΔ hg) hc hA

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
  | sort hg =>
    exact fun a' h _ => by
      show TShape.HasType Δ _ ⟨a'.1, a'.2⟩
      rw [TShape.LE.sort_eq hΔ h]; exact .sort hg
  | unit hj =>
    exact fun a' h _ => by
      show TShape.HasType Δ _ ⟨a'.1, a'.2⟩
      rw [TShape.LE.sort_eq hΔ h]; exact .unit hj
  | nat =>
    exact fun a' h _ => by
      show TShape.HasType Δ _ ⟨a'.1, a'.2⟩
      rw [TShape.LE.sort_eq hΔ h]; exact .nat
  | zero => exact fun a' h _ => by obtain ⟨k, rfl⟩ := TShape.LE.nat_eq h; exact .zero
  | succ hN hg =>
    exact fun a' h _ => by obtain ⟨k, rfl⟩ := TShape.LE.nat_eq h; exact .succ hN hg
  | id hj hg =>
    exact fun a' h _ => by
      show TShape.HasType Δ _ ⟨a'.1, a'.2⟩
      rw [TShape.LE.sort_eq hΔ h]; exact .id hj hg
  | forallE hd hf hj hg _ _ =>
    exact fun a' h _ => by
      show TShape.HasType Δ _ ⟨a'.1, a'.2⟩
      rw [TShape.LE.sort_eq hΔ h]; exact .forallE hd hf hj hg
  | sigma hd hf hg _ _ =>
    exact fun a' h _ => by
      show TShape.HasType Δ _ ⟨a'.1, a'.2⟩
      rw [TShape.LE.sort_eq hΔ h]; exact .sigma hd hf hg
  | lam cs hd hf hev hty hg hc _ _ _ _ _ =>
    exact fun _ h hA' => .lam cs hd hf hev hty hg (hc.trans hΔ h) hA'
  | pair hd hf hxd hev hyc hg hc _ _ _ _ _ =>
    exact fun _ h hA' => .pair hd hf hxd hev hyc hg (hc.trans hΔ h) hA'
  | refl hg hc _ _ => exact fun _ h hA' => .refl hg (hc.trans hΔ h) hA'

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
  | sort hg => exact ⟨hg.wf, Shape.WF.sort⟩
  | unit _ => exact ⟨trivial, Shape.WF.sort⟩
  | nat => exact ⟨trivial, Shape.WF.sort⟩
  | zero => exact ⟨trivial, trivial⟩
  | succ _ hg => exact ⟨hg.wf, trivial⟩
  | id _ hg => exact ⟨hg.wf, Shape.WF.sort⟩
  | forallE _ _ _ hg _ _ => exact ⟨hg.wf, Shape.WF.sort⟩
  | sigma _ _ hg _ _ => exact ⟨hg.wf, Shape.WF.sort⟩
  | lam _ _ _ _ _ hg _ _ _ _ _ ih => exact ⟨hg.wf, ih.1⟩
  | pair _ _ _ _ _ hg _ _ _ _ _ _ ih => exact ⟨hg.wf, ih.1⟩
  | refl hg _ _ ih => exact ⟨hg.wf, ih.1⟩

/-- Typing does not see the level of its subject: `⟨n, m⟩` and
`⟨k, m.lift k⟩` are order-equivalent, and every clause reaches the subject
only through the order or a pin.  Contrast `Shape.HasType.lift_iff`, 160
lines, whose reflection direction is what §5.5 shows a dominating graph
cannot survive. -/
theorem TShape.HasType.lift_subject {Δ : List Term} (hΔ : ⊢ Δ) {k}
    {m a : TShape} (hk : m.1 ≤ k) (H : TShape.HasType Δ m a) :
    TShape.HasType Δ (m.lift k) a :=
  H.mono_l hΔ (TShape.LE.lift_le hΔ hk H.wf.1)

theorem TShape.HasType.unlift_subject {Δ : List Term} (hΔ : ⊢ Δ) {k}
    {m a : TShape} (hk : m.1 ≤ k) (H : TShape.HasType Δ (m.lift k) a) :
    TShape.HasType Δ m a :=
  H.mono_l hΔ (TShape.LE.le_lift hΔ hk ((Shape.lift_wf hk).1 H.wf.1))

/-- `⊥` is typed at `⊥`, since `⊥` is a type. -/
theorem TShape.HasType.bot_bot {Δ : List Term} {n} :
    TShape.HasType Δ (Shape.T (n := n) Shape.bot) TShape.bot :=
  .bot (.bot (.sort (TShape.LE.refl Shape.WF.sort)))

/-- Cumulativity, which the sort-typed clauses build in. -/
theorem TShape.HasType.cumul {Δ : List Term} {m : TShape} {r s : Bool} {k}
    (H : TShape.HasType Δ m (Shape.T (n := k) (Shape.sort r))) (hrs : r ≤ s) :
    TShape.HasType Δ m (Shape.T (n := k) (Shape.sort s)) := by
  sorry

/-- Typed substitution.

**Open**, and the obstruction is in the *definition*: the `lam` clause's
codomain witness is a function `cs : Entry (Shape n₀) → TShape`, because an
`∃` in that premise would nest the inductive inside `Exists` and the kernel
refuses it.  A substitution reindexes the generator graph to `g₀.subst τ`,
and `fun e' => (cs e').subst τ` is the wrong function: it gives
`(cs (e.subst τ)).subst τ` where `(cs e).subst τ` is wanted.  Two ways out,
and the choice belongs with the definition rather than here: index `cs` by
position in `g₀` (`Nat → TShape`, with `g₀[i]? = some e` premises), which
substitution preserves; or keep the entry indexing and build the
substituted witness with `Classical.skolem`, at the price of
`Classical.choice` in the axiom list. -/
theorem TShape.HasType.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {m a : TShape} (H : TShape.HasType Δ m a) :
    TShape.HasType Θ (m.subst τ) (a.subst τ) := by
  sorry
