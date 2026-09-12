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

variable (Δ : List Term) {n} (f : ShapeFun n) (A a : Term) (x : Shape n) in
/-- Relational graph lookup: `Evaluates Δ f A a x y` says `y` approximates
the result of applying the graph `f`, at the argument label `(A, a)`, to an
input at least `x`.  It is the set of outputs of matching entries, closed
downwards and under compatible joins — the other repo's `Evaluates`.

Replacing `ShapeFun.app` (a function) by this (a relation) is what lets us
drop saturation: the join of several matching entries is available here
without having to be stored in the graph. -/
inductive Evaluates : Shape n → Prop where
  | bot : Evaluates .bot
  | entry (e : Entry (Shape n)) : e ∈ f → LabelEq Δ e.ty e.tm A a →
    Shape.LE Δ e.inp x → Evaluates e.out
  -- the lookup is a lower set, but **lowering is constrained to well-formed
  -- shapes**.  Unrestricted lowering would break `Evaluates.wf`, since `WF`
  -- is not downward closed: a smaller λ-shape may have a bottom output,
  -- which non-degeneracy forbids.  With the constraint the lookup stays an
  -- ideal and everything it returns is still well formed.
  | lower {y z} : Shape.WF Δ y → Shape.LE Δ y z → Evaluates z → Evaluates y
  -- Now that the `join` *function* is correct (no information-free λ-shapes),
  -- closing under it rather than under the `Join` relation is what makes
  -- `Evaluates` transport along a substitution: `join` commutes with
  -- substitution on the nose, whereas `Join Θ` quantifies over more shapes
  -- than the image of the substitution
  | join {y z} : Shape.Compat Δ y z → Evaluates y → Evaluates z → Evaluates (y.join z)

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
  have ⟨⟨_, hty⟩, htm, hin, _⟩ := hwf e he
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
  | lower hw hle _ ih => exact .lower hw hle ih
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
def ShapeFun.HasPi (Δ : List Term) (T : Shape n → Shape n → Prop)
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
theorem ShapeFun.HasPi.cod {Δ : List Term} {n} {T : Shape n → Shape n → Prop}
    {d : Shape n} {f : ShapeFun n} {a a' : Shape n}
    (H : ∀ {z}, T z a → T z a') (h : ShapeFun.HasPi Δ T d f a) :
    ShapeFun.HasPi Δ T d f a' :=
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
    ShapeFun.HasPi Δ T d f (.sort r) → HasTypeS Δ T (.forallE A B d f) (.sort r)
  | sigma {A B d f} :
    ShapeFun.HasPi Δ T d f .type → HasTypeS Δ T (.sigma A B d f) (.sort true)
  -- no dominating graph: with `HasDom` gone the condition is downward
  -- closed in `g` on its own, by `mono_input` on the code and `mono_l` on
  -- the output
  | lam {g A B d f} :
    ShapeFun.HasPi Δ T d f .type →
    (∀ e ∈ g, ∃ c, Shape.WF Δ c ∧ Evaluates Δ f e.ty e.tm e.inp c ∧ T e.out c) →
    HasTypeS Δ T (.lam g) (.forallE A B d f)
  -- and here on a first component dominating the pair's own, because the
  -- code is read off at it and the lookup is monotone in its input
  | pair {ty tm x y x₀ c A B d f} :
    ShapeFun.HasPi Δ T d f .type → Shape.LE Δ x x₀ → Shape.WF Δ x₀ → T x₀ d →
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
theorem Shape.HasType.cumul : ∀ {n} {a : Shape n} {r s : Bool},
    Shape.HasType Δ a (.sort r) → r ≤ s → Shape.HasType Δ a (.sort s) := by
  intro n
  induction n with
  | zero =>
    intro a r s h hrs
    cases Shape.hasType_zero.1 h with
    | bot => exact .bot
    | sort => cases Bool.eq_true_of_le rfl hrs; exact .sort
  | succ n ih =>
    intro a r s h hrs
    cases Shape.hasType_succ.1 h with
    | bot _ => exact .bot .sort
    | sort => cases Bool.eq_true_of_le rfl hrs; exact .sort
    | nat => cases Bool.eq_true_of_le rfl hrs; exact .nat
    | sigma hpi => cases Bool.eq_true_of_le rfl hrs; exact .sigma hpi
    | unit hle => exact .unit (Bool.le_tr hle hrs)
    | id hle => exact .id (Bool.le_tr hle hrs)
    | forallE hpi => exact .forallE (hpi.cod (ih · hrs))

/-- `⊥` inhabits every type; at positive level this is the constructor. -/
theorem Shape.HasType.bot : ∀ {n} {a : Shape n},
    Shape.HasType Δ a .type → Shape.HasType Δ .bot a := by
  intro n
  cases n with
  | zero => intro _ _; exact Shape.HasType0.bot
  | succ n => intro _ h; exact Shape.HasTypeS.bot h

/-- A sort is a type, at any level. -/
theorem Shape.HasType.sort {Δ : List Term} : ∀ {n} {r : Bool},
    Shape.HasType Δ (.sort r : Shape n) .type := by
  intro n
  cases n with
  | zero => intro _; exact Shape.HasType0.sort
  | succ n => intro _; exact Shape.HasTypeS.sort

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
    cases Shape.hasType_zero.1 h with
    | bot => cases a with | bot => exact Shape.HasType0.bot | sort => exact .sort
    | sort => exact .sort
  | succ n =>
    intro m a h
    cases Shape.hasType_succ.1 h with
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
  | lower hw hle _ ih => exact .lower hw hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- And it only sees the query label up to definitional equality. -/
theorem Evaluates.label {Δ : List Term} {n} {f : ShapeFun n} {A a A' a' : Term}
    {x c : Shape n} (hlab : LabelEq Δ A a A' a') (H : Evaluates Δ f A a x c) :
    Evaluates Δ f A' a' x c := by
  induction H with
  | bot => exact .bot
  | entry e he hl hin => exact .entry e he (hl.trans hlab) hin
  | lower hw hle _ ih => exact .lower hw hle ih
  | join hc _ _ ih₁ ih₂ => exact .join hc ih₁ ih₂

/-- Numerals are downward closed. -/
theorem Shape.IsNumeral.lower {Δ : List Term} (hΔ : ⊢ Δ) : ∀ {n} {v v' : Shape n},
    Shape.LE Δ v' v → Shape.IsNumeral v → Shape.IsNumeral v' := by
  intro n v v' hle h
  induction h with
  | bot => cases Shape.le_bot_iff.1 hle; exact .bot
  | @zero n =>
    cases v' with
    | bot => exact .bot
    | zero => exact .zero
    | _ => exact absurd hle id
  | @succ n w _ ih =>
    cases v' with
    | bot => exact .bot
    | succ w' => exact .succ (ih hle)
    | _ => exact absurd hle id

/-- A Π/Σ signature is inherited by anything it dominates: the whole point
of stating it with a dominating pair. -/
theorem ShapeFun.HasPi.lower {Δ : List Term} (hΔ : ⊢ Δ) {n}
    {d d' : Shape n} {f f' : ShapeFun n} {a : Shape n}
    (ih : ∀ {m m' : Shape n}, Shape.LE Δ m' m → Shape.HasType Δ m a → Shape.HasType Δ m' a)
    (ihty : ∀ {m m' : Shape n}, Shape.LE Δ m' m →
      Shape.HasType Δ m .type → Shape.HasType Δ m' .type)
    (hd : Shape.LE Δ d' d) (hf : ShapeFun.LE Δ (Shape.LE Δ) f' f)
    (h : ShapeFun.HasPi Δ (Shape.HasType Δ) d f a) :
    ShapeFun.HasPi Δ (Shape.HasType Δ) d' f' a :=
  ⟨ihty hd h.1, fun e he => have ⟨e', he', _, _, hout⟩ := hf e he; ih hout (h.2 e' he')⟩

/-- **Left monotonicity**: a type is a lower set.  Master has only the
two-sided form (`WShape.HasType.mono_l`, a 70-line mutual induction whose
graph cases run a cycle argument); here the clauses were arranged so that
the genuine one-sided statement is an induction with no side conditions --
the dominating existentials in `HasPi`, `lam` and `pair` absorb the
approximation by transitivity, the componentwise clauses use the induction
hypothesis, and every `m' = ⊥` branch is `.bot (isType h)`. -/
theorem Shape.HasType.mono_l (hΔ : ⊢ Δ) : ∀ {n} {m m' a : Shape n},
    Shape.LE Δ m' m → Shape.HasType Δ m a → Shape.HasType Δ m' a := by
  intro n
  induction n with
  | zero =>
    intro m m' a hle h
    cases m' with
    | bot => exact Shape.HasType0.bot
    | sort s =>
      cases m with
      | bot => exact absurd hle id
      | sort s' => cases (hle : s = s'); exact h
  | succ n ih =>
    intro m m' a hle h
    have hty := Shape.HasType.isType h
    cases Shape.hasType_succ.1 h with
    | bot hb => cases Shape.le_bot_iff.1 hle; exact .bot hb
    | sort =>
      cases m' with
      | bot => exact .bot hty
      | sort s' => cases (hle : s' = _); exact .sort
      | _ => exact absurd hle id
    | unit hj =>
      cases m' with
      | bot => exact .bot hty
      | unit r' => cases (hle : r' = _); exact .unit hj
      | _ => exact absurd hle id
    | nat =>
      cases m' with
      | bot => exact .bot hty
      | nat => exact .nat
      | _ => exact absurd hle id
    | zero =>
      cases m' with
      | bot => exact .bot hty
      | zero => exact .zero
      | _ => exact absurd hle id
    | succ hN =>
      cases m' with
      | bot => exact .bot hty
      | succ v' => exact .succ (Shape.IsNumeral.lower hΔ hle hN)
      | _ => exact absurd hle id
    | id hj =>
      cases m' with
      | bot => exact .bot hty
      | id r' A' a' b' => cases (hle.1 : r' = _); exact .id hj
      | _ => exact absurd hle id
    | forallE hpi =>
      cases m' with
      | bot => exact .bot hty
      | forallE A' B' d' f' =>
        exact .forallE (hpi.lower hΔ (ih (a := Shape.sort _)) (ih (a := Shape.type))
          hle.2.1 hle.2.2)
      | _ => exact absurd hle id
    | sigma hpi =>
      cases m' with
      | bot => exact .bot hty
      | sigma A' B' d' f' =>
        exact .sigma (hpi.lower hΔ (ih (a := Shape.type)) (ih (a := Shape.type))
          hle.2.1 hle.2.2)
      | _ => exact absurd hle id
    | lam hpi hcod =>
      cases m' with
      | bot => exact .bot hty
      | lam g' =>
        refine .lam hpi fun e he => ?_
        have ⟨e₀, he₀, hlab, hin, hout⟩ := hle e he
        have ⟨c, hwc, hev, hcty⟩ := hcod e₀ he₀
        exact ⟨c, hwc, (hev.label hlab).mono_input hΔ hin, ih hout hcty⟩
      | _ => exact absurd hle id
    | pair hpi hxle hwx hxd hwc hev hyc =>
      cases m' with
      | bot => exact .bot hty
      | pair ty' tm' x' y' =>
        exact .pair hpi (hle.2.1.trans hΔ hxle) hwx hxd hwc
          (hev.label (LabelEq.symm hle.1)) (ih hle.2.2 hyc)
      | _ => exact absurd hle id
    | refl =>
      cases m' with
      | bot => exact .bot hty
      | refl w' => exact .refl
      | _ => exact absurd hle id

theorem Evaluates.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ)
    {n} {f : ShapeFun n} {A a : Term} {x c : Shape n} :
    Evaluates Δ f A a x c →
    Evaluates Θ (ShapeFun.subst (Shape.subst · τ) τ f) (A.subst τ) (a.subst τ)
      (x.subst τ) (c.subst τ) := by
  intro h
  induction h with
  | bot => simp only [Shape.subst_bot]; exact .bot
  | entry e he hlab hin =>
    exact .entry _ (ShapeFun.mem_subst.2 ⟨e, he, rfl⟩) (hlab.subst hΘ W)
      (Shape.LE.subst hΘ W hin)
  | lower hw hle _ ih =>
    exact .lower (Shape.WF.subst hΘ W hw) (Shape.LE.subst hΘ W hle) ih
  | join hc _ _ ih₁ ih₂ =>
    exact Shape.join_subst ▸ .join (Shape.Compat.subst hΘ W hc) ih₁ ih₂

theorem ShapeFun.HasDom.subst_of {Δ Θ : List Term} {τ : Subst} {n} {f : ShapeFun n}
    {d : Shape n} (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ)
    (ih : ∀ {m a : Shape n}, Shape.HasType Δ m a → Shape.HasType Θ (m.subst τ) (a.subst τ))
    (h : ShapeFun.HasDom Δ (Shape.HasType Δ) f d) :
    ShapeFun.HasDom Θ (Shape.HasType Θ) (ShapeFun.subst (Shape.subst · τ) τ f)
      (d.subst τ) := by
  intro e' he'
  obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
  have ⟨x, hwx, hx, hxle, hev⟩ := h e he
  exact ⟨x.subst τ, Shape.WF.subst hΘ W hwx, ih hx, Shape.LE.subst hΘ W hxle,
    Evaluates.subst hΘ W hev⟩

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
    {f : ShapeFun n} {a : Shape n} (hΘ : ⊢ Θ) (W : Ctx.SubstEq Θ τ τ Δ)
    (ih : ∀ {m a : Shape n}, Shape.HasType Δ m a → Shape.HasType Θ (m.subst τ) (a.subst τ))
    (h : ShapeFun.HasPi Δ (Shape.HasType Δ) d f a) :
    ShapeFun.HasPi Θ (Shape.HasType Θ) (d.subst τ)
      (ShapeFun.subst (Shape.subst · τ) τ f) (a.subst τ) := by
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
    cases Shape.hasType_zero.1 h with
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
      exact .forallE (by simpa using ShapeFun.HasPi.subst_of hΘ W ih hpi)
    | sigma hpi => exact .sigma (by simpa using ShapeFun.HasPi.subst_of hΘ W ih hpi)
    | lam hpi hcod =>
      refine .lam (by simpa using ShapeFun.HasPi.subst_of hΘ W ih hpi) fun e' he' => ?_
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      have ⟨c, hwc, hev, hty⟩ := hcod e he
      exact ⟨c.subst τ, Shape.WF.subst hΘ W hwc, Evaluates.subst hΘ W hev, ih hty⟩
    | pair hpi hxle hwx hxd hwc hev hyc =>
      exact .pair (by simpa using ShapeFun.HasPi.subst_of hΘ W ih hpi) (Shape.LE.subst hΘ W hxle)
        (Shape.WF.subst hΘ W hwx) (ih hxd) (Shape.WF.subst hΘ W hwc)
        (Evaluates.subst hΘ W hev) (ih hyc)
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
    {x : Shape n} (hf : ShapeFun.Compat Shape.Compat Δ f f) (hx : Shape.Compat Δ x x) :
    ∀ {y z : Shape n}, Evaluates Δ f A a x y → Evaluates Δ f A a x z →
      Shape.Compat Δ y z := by
  -- an entry output selected by the query is compatible with anything the
  -- lookup returns
  have atom : ∀ {e : Entry (Shape n)}, e ∈ f → LabelEq Δ e.ty e.tm A a →
      Shape.LE Δ e.inp x → ∀ {z}, Evaluates Δ f A a x z →
      Shape.Compat Δ e.out z := by
    intro e he hlab hin z hz
    induction hz with
    | bot => exact Shape.Compat.bot_right
    | entry e' he' hlab' hin' =>
      have key := hf e he e' he' Δ .id hΔ (Ctx.SubstEq.id hΔ)
        (by simpa using hlab.trans (LabelEq.symm hlab'))
        (by simpa using Shape.Compat.of_common_upper hΔ hx hin hin')
      simpa using key
    | lower _ hle _ ih => exact Shape.Compat.anti_right hΔ ih hle
    | join _ _ _ ih₁ ih₂ =>
      exact Shape.Compat.symm hΔ
        (Shape.join_compat hΔ (Shape.Compat.symm hΔ ih₁) (Shape.Compat.symm hΔ ih₂))
  intro y z hy hz
  induction hy with
  | bot => exact Shape.Compat.bot_left
  | entry e he hlab hin => exact atom he hlab hin hz
  | lower _ hle _ ih =>
    exact Shape.Compat.symm hΔ (Shape.Compat.anti_right hΔ (Shape.Compat.symm hΔ ih) hle)
  | join _ _ _ ih₁ ih₂ => exact Shape.join_compat hΔ ih₁ ih₂

/-- Everything the lookup returns is well formed, structurally: it is `⊥`,
an entry output, a join of those, or an explicitly well-formed lowering.
The `WF` premise on `lower` is exactly what makes this hold — `WF` is not
downward closed, so unconstrained lowering would break it. -/
theorem Evaluates.wf {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a : Term}
    {x : Shape n} (hf : ∀ e ∈ f, Shape.WF Δ e.out) :
    ∀ {y : Shape n}, Evaluates Δ f A a x y → Shape.WF Δ y := by
  intro y h
  induction h with
  | bot => cases n <;> trivial
  | entry e he _ _ => exact hf e he
  | lower hw _ _ _ => exact hw
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
    have hwe := (hwf e he).2.2.2
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
    have hwi := (hwf e he).2.2.1
    have hwo := (hwf e he).2.2.2
    exact ⟨[e], e.inp, e.out, List.singleton_sublist.2 he,
      (fun e' he' => by cases List.mem_singleton.1 he'; exact hlab),
      Shape.Joins.singleton hΔ hwi, hwi, hin,
      Shape.Joins.singleton hΔ hwo, hwo, Shape.LE.refl hwo⟩
  | lower _ hle _ ih =>
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
          hv ▸ (hwf e (hs.subset he)).2.2.1)
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
    {A a : Term} {x y : Shape n} (hwx : Shape.WF Δ x) (hwy : Shape.WF Δ y) :
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
  exact .lower hwy (hyjo.trans hΔ (hjo.min hwJ (hJ.le hwJ))) hev

/-- The lookup is monotone in the graph, plainly: a dominating graph
reaches at least as much.  `mono_graph` below adds that the witness can be
taken to be a type; this version needs no typing at all and is what the
`lam`/`pair` cases of `mono_r` use, since they transport the code back down
with `lower` rather than retyping at a bigger one. -/
theorem Evaluates.mono_graph' {Δ : List Term} (hΔ : ⊢ Δ) {n} {f f' : ShapeFun n}
    {A a : Term} {x : Shape n}
    (hf' : ShapeFun.Compat Shape.Compat Δ f' f') (hx : Shape.Compat Δ x x)
    (hwf : ∀ e ∈ f', Shape.WF Δ e.out)
    (hff' : ShapeFun.LE Δ (Shape.LE Δ) f f') :
    ∀ {c : Shape n}, Evaluates Δ f A a x c →
      ∃ c', Evaluates Δ f' A a x c' ∧ Shape.LE Δ c c' := by
  intro c h
  induction h with
  | bot => exact ⟨.bot, .bot, Shape.LE.bot⟩
  | entry e he hlab hin =>
    have ⟨e', he', hlab', hin', hout'⟩ := hff' e he
    exact ⟨e'.out, .entry e' he' (hlab'.trans hlab) (hin'.trans hΔ hin), hout'⟩
  | lower _ hle _ ih =>
    have ⟨c', hc', hle'⟩ := ih
    exact ⟨c', hc', hle.trans hΔ hle'⟩
  | join _ _ _ ih₁ ih₂ =>
    have ⟨y', hy', hley⟩ := ih₁
    have ⟨z', hz', hlez⟩ := ih₂
    have hc : Shape.Compat Δ y' z' := Evaluates.compat hΔ hf' hx hy' hz'
    have ⟨hu₁, hu₂⟩ :=
      Shape.le_join hΔ (Evaluates.wf hΔ hwf hy') (Evaluates.wf hΔ hwf hz') hc
    exact ⟨y'.join z', .join hc hy' hz',
      Shape.join_le (hley.trans hΔ hu₁) (hlez.trans hΔ hu₂)⟩

/-- The lookup is **monotone in the graph**, and what it returns is a type
whenever the graph's outputs are.  Master gets monotonicity from
`app_mono_l`, its lookup being a function; ours produces a witness, and
the `join` case needs the two witnesses to be compatible
(`Evaluates.compat`), bounded (`le_join`, via `Evaluates.wf`), and typed
(`hjoin`, which is `mono_r`'s companion at the level below). -/
theorem Evaluates.mono_graph {Δ : List Term} (hΔ : ⊢ Δ) {n} {f f' : ShapeFun n}
    {A a : Term} {x : Shape n} {r : Bool}
    (hf' : ShapeFun.Compat Shape.Compat Δ f' f') (hx : Shape.Compat Δ x x)
    (hwf : ∀ e ∈ f', Shape.WF Δ e.out)
    (hty : ∀ e ∈ f', Shape.HasType Δ e.out (.sort r))
    (hjoin : ∀ {y z : Shape n}, Shape.WF Δ y → Shape.WF Δ z → Shape.Compat Δ y z →
      Shape.HasType Δ y (.sort r) → Shape.HasType Δ z (.sort r) →
      Shape.HasType Δ (y.join z) (.sort r))
    (hff' : ShapeFun.LE Δ (Shape.LE Δ) f f') :
    ∀ {c : Shape n}, Evaluates Δ f A a x c →
      ∃ c', Evaluates Δ f' A a x c' ∧ Shape.LE Δ c c' ∧
        Shape.HasType Δ c' (.sort r) := by
  intro c h
  induction h with
  | bot => exact ⟨.bot, .bot, Shape.LE.bot, Shape.HasType.bot_sort⟩
  | entry e he hlab hin =>
    have ⟨e', he', hlab', hin', hout'⟩ := hff' e he
    exact ⟨e'.out, .entry e' he' (hlab'.trans hlab)
      (hin'.trans hΔ hin), hout', hty e' he'⟩
  | lower _ hle _ ih =>
    have ⟨c', hc', hle', hty'⟩ := ih
    exact ⟨c', hc', hle.trans hΔ hle', hty'⟩
  | join _ _ _ ih₁ ih₂ =>
    have ⟨y', hy', hley, htyy⟩ := ih₁
    have ⟨z', hz', hlez, htyz⟩ := ih₂
    have hc : Shape.Compat Δ y' z' := Evaluates.compat hΔ hf' hx hy' hz'
    have hwy := Evaluates.wf hΔ hwf hy'
    have hwz := Evaluates.wf hΔ hwf hz'
    have ⟨hu₁, hu₂⟩ := Shape.le_join hΔ hwy hwz hc
    exact ⟨y'.join z', .join hc hy' hz',
      Shape.join_le (hley.trans hΔ hu₁) (hlez.trans hΔ hu₂),
      hjoin hwy hwz hc htyy htyz⟩

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
    · cases m with
      | bot => exact Shape.HasType0.bot
      | sort s =>
        cases a with | bot => cases Shape.hasType_zero.1 h | sort j => ?_
        cases a' with | bot => cases hle | sort j' => ?_
        cases Shape.hasType_zero.1 h with | sort => ?_
        cases (hle : true = j'); exact Shape.HasType0.sort
    · cases y with | bot => exact hz | sort s
      cases z with | bot => exact hy | sort s'
      exact hy
  | succ n ih =>
    obtain ⟨ihm, ihj⟩ := ih
    refine ⟨?_, ?_⟩
    · -- mono_r
      intro m a a' r hwm hwa h hle hA
      cases Shape.hasType_succ.1 h with
      | bot _ => exact .bot (Shape.HasType.cumul hA (Bool.le_true' r))
      | sort =>
        cases a' with | sort j' => ?_ | _ => cases hle
        cases (hle : true = j'); exact .sort
      | nat =>
        cases a' with | sort j' => ?_ | _ => cases hle
        cases (hle : true = j'); exact .nat
      | sigma hpi =>
        cases a' with | sort j' => ?_ | _ => cases hle
        cases (hle : true = j'); exact .sigma hpi
      | unit hj =>
        cases a' with | sort j' => ?_ | _ => cases hle
        cases (hle : _ = j'); exact .unit hj
      | id hj =>
        cases a' with | sort j' => ?_ | _ => cases hle
        cases (hle : _ = j'); exact .id hj
      | forallE hpi =>
        cases a' with | sort j' => ?_ | _ => cases hle
        cases (hle : _ = j'); exact .forallE hpi
      | zero => cases a' with | nat => exact .zero | _ => cases hle
      | succ hN => cases a' with | nat => exact .succ hN | _ => cases hle
      | refl =>
        cases a' with | id t' A₁ a₁ b₁ => ?_ | _ => cases hle
        cases (hle.1 : true = t'); exact .refl
      | lam hpi hcod =>
        cases a' with | forallE A₁ B₁ d' f' => ?_ | _ => cases hle
        cases Shape.hasType_succ.1 hA with | forallE hpiA => ?_
        refine .lam (hpiA.cod (Shape.HasType.cumul · (Bool.le_true' r))) fun e he => ?_
        have ⟨c, hwc, hev, hcty⟩ := hcod e he
        have ⟨c', hev', hcle⟩ :=
          Evaluates.mono_graph' hΔ hwa.2.2.2.2 (hwm.2.2.1 e he).2.2.1.coherent
            (fun e' he' => (hwa.2.2.2.1 e' he').2.2.2) hle.2.2 hev
        exact ⟨c, hwc, .lower hwc hcle hev', hcty⟩
      | pair hpi hxle hwx hxd hwc hev hyc =>
        cases a' with | sigma A₁ B₁ d' f' => ?_ | _ => cases hle
        cases Shape.hasType_succ.1 hA with | sigma hpiA => ?_
        have hd' : Shape.HasType Δ d' .type := hpiA.1
        have ⟨c', hev', hcle⟩ :=
          Evaluates.mono_graph' hΔ hwa.2.2.2.2 hwx.coherent
            (fun e' he' => (hwa.2.2.2.1 e' he').2.2.2) hle.2.2 hev
        exact .pair hpiA hxle hwx (ihm hwx hwa.2.2.1 hxd hle.2.1 hd') hwc
          (.lower hwc hcle hev') hyc
    · -- typed joins
      intro y z r hwy hwz hc hy hz
      cases y with
      | bot => exact hz
      | forallE A₀ B₀ d f =>
        cases z with | bot => exact hy | forallE A₁ B₁ d' g => ?_ | _ => cases hc
        cases Shape.hasType_succ.1 hy with | forallE hpy => ?_
        cases Shape.hasType_succ.1 hz with | forallE hpz => ?_
        refine .forallE ⟨ihj hwy.2.2.1 hwz.2.2.1 hc.2.1 hpy.1 hpz.1, fun e he => ?_⟩
        match List.mem_append.1 he with
        | .inl he => exact hpy.2 e he
        | .inr he => exact hpz.2 e he
      | sigma A₀ B₀ d f =>
        cases z with | bot => exact hy | sigma A₁ B₁ d' g => ?_ | _ => cases hc
        cases Shape.hasType_succ.1 hy with | sigma hpy => ?_
        cases Shape.hasType_succ.1 hz with | sigma hpz => ?_
        refine .sigma ⟨ihj hwy.2.2.1 hwz.2.2.1 hc.2.1 hpy.1 hpz.1, fun e he => ?_⟩
        match List.mem_append.1 he with
        | .inl he => exact hpy.2 e he
        | .inr he => exact hpz.2 e he
      | _ => cases z <;> first | exact hy | cases Shape.hasType_succ.1 hy

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

/-- Everything the lookup returns is below something the lookup returns
that is a type, in whatever sort the graph's outputs live.  Immediate from
`mono_graph` at `f' = f`. -/
theorem Evaluates.bounded (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {A a : Term} {x : Shape n}
    {r : Bool} (hwf : ShapeFun.WF Δ (Shape.WF Δ) f)
    (hco : ShapeFun.Compat Shape.Compat Δ f f) (hx : Shape.Compat Δ x x)
    (hty : ∀ e ∈ f, Shape.HasType Δ e.out (.sort r))
    {c : Shape n} (h : Evaluates Δ f A a x c) :
    ∃ z, Shape.WF Δ z ∧ Shape.LE Δ c z ∧ Shape.HasType Δ z (.sort r) :=
  have hout : ∀ e ∈ f, Shape.WF Δ e.out := fun e he => (hwf e he).2.2.2
  have ⟨c', hc', hle, hc'ty⟩ :=
    Evaluates.mono_graph hΔ hco hx hout hty (Shape.HasType.join hΔ)
      (ShapeFun.LE.refl_aux hwf) h
  ⟨c', Evaluates.wf hΔ hout hc', hle, hc'ty⟩

/-- Nothing but `⊥` is typed at `⊥`. -/
theorem Shape.HasType.bot_r : ∀ {n} {x : Shape n}, Shape.HasType Δ x .bot → x = .bot := by
  intro n x h
  cases n with
  | zero => cases Shape.hasType_zero.1 h with | bot => rfl
  | succ n => cases Shape.hasType_succ.1 h with | bot => rfl

/-- A proposition is inhabited only by `⊥`. -/
theorem Shape.HasType.proofIrrel (hΔ : ⊢ Δ) : ∀ {n} {a x : Shape n},
    Shape.WF Δ a → Shape.WF Δ x →
    Shape.HasType Δ a .prop → Shape.HasType Δ x a → x = .bot := by
  intro n
  induction n with
  | zero =>
    intro a x _ _ ha h
    cases Shape.hasType_zero.1 ha with
    | bot => exact Shape.HasType.bot_r h
  | succ n ih =>
    intro a x hwa hwx ha h
    -- the inversion narrows `a` to the four formers that can be a `prop`
    cases Shape.hasType_succ.1 ha with
    | bot _ => exact Shape.HasType.bot_r h
    | unit _ =>
      -- nothing but `⊥` inhabits `unit` at all, so the flag never matters
      cases Shape.hasType_succ.1 h with | bot _ => rfl
    | @id r _ A₀ a₀ b₀ hj =>
      -- `HasType (.id t ..) .prop` forces `t = false`, and `refl` needs `t = true`
      have hr : r = false := by
        cases r with | false => rfl | true => exact absurd hj (by decide)
      subst hr
      cases Shape.hasType_succ.1 h with | bot _ => rfl
    | @forallE A₀ B₀ d f _ hpi =>
      cases Shape.hasType_succ.1 h with
      | bot _ => rfl
      | @lam g _ _ _ _ hpi' hcod =>
        -- a well-formed λ carries real information, so it cannot inhabit a
        -- Π-type whose codomain family is propositional
        exfalso
        have ⟨hne, hnb, hwg', _⟩ := hwx
        have ⟨_, _, _, hwf, hco⟩ := hwa
        cases g with
        | nil => exact hne rfl
        | cons e g' =>
          have he : e ∈ e :: g' := List.mem_cons_self ..
          have ⟨c, hwc, hev, hcty⟩ := hcod e he
          have ⟨z, hwz, hcz, hzty⟩ :=
            Evaluates.bounded hΔ hwf hco (Shape.WF.coherent (hwg' e he).2.2.1) hpi.2 hev
          have hbot : e.out = .bot :=
            ih hwz (hwg' e he).2.2.2 hzty
              (Shape.HasType.mono_r hΔ (hwg' e he).2.2.2 hwz hcty hcz hzty)
          have hb : Shape.IsBot (Shape.bot : Shape n) := by cases n <;> trivial
          exact hnb e he (hbot ▸ hb)

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

One direction is enough: `TShape.HasType` is defined at the canonical
level and read off at any higher one. -/

theorem Evaluates.lift {Δ : List Term} {n k} (h : n ≤ k) {f : ShapeFun n} {A a : Term}
    {x c : Shape n} (H : Evaluates Δ f A a x c) :
    Evaluates Δ (ShapeFun.lift (Shape.lift k) f) A a (x.lift k) (c.lift k) := by
  induction H with
  | bot => rw [Shape.lift_bot]; exact .bot
  | entry e he hlab hin =>
    exact .entry ⟨e.ty, e.tm, e.inp.lift k, e.out.lift k⟩ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)
      hlab ((Shape.lift_le_lift h).2 hin)
  | lower hwf hle _ ih =>
    exact .lower ((Shape.lift_wf h).2 hwf) ((Shape.lift_le_lift h).2 hle) ih
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
    (Shape.lift_le_lift h).1
      ((hji.le hwji _ (List.mem_map.2 ⟨e.inp, List.mem_map.2 ⟨e, he, rfl⟩, rfl⟩)).trans hΔ hjix)
  have ⟨J, hJ, hwJ, hevJ⟩ :=
    Evaluates.of_sublist hΔ hwf hco hwx.coherent hs₀
      (fun e he => hlab _ (List.mem_map.2 ⟨e, he, rfl⟩)) hinx
  have ⟨hle, _⟩ :=
    Shape.Joins.uniq hwjo ((Shape.lift_wf h).2 hwJ) hjo
      (Shape.Joins.lift hΔ h (fun v hv => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hv
        exact (hwf e (hs₀.subset he)).2.2.2) hwJ hJ)
  exact ⟨J, hcjo.trans hΔ hle, hevJ⟩

/-- **Fullness for the lookup.**  On the shapes that come from the level
below, the lifted graph relates exactly what the original one did. -/
theorem Evaluates.lift_iff {Δ : List Term} (hΔ : ⊢ Δ) {n k} (h : n ≤ k) {f : ShapeFun n}
    {A a : Term} {x c : Shape n}
    (hwf : ShapeFun.WF Δ (Shape.WF Δ) f) (hco : ShapeFun.Compat Shape.Compat Δ f f)
    (hwx : Shape.WF Δ x) (hwc : Shape.WF Δ c) :
    Evaluates Δ (ShapeFun.lift (Shape.lift k) f) A a (x.lift k) (c.lift k) ↔
      Evaluates Δ f A a x c := by
  refine ⟨fun H => ?_, Evaluates.lift h⟩
  have ⟨c₀, hle, hc₀⟩ := Evaluates.lift_of hΔ h hwf hco hwx H
  exact .lower hwc ((Shape.lift_le_lift h).1 hle) hc₀

theorem Shape.IsNumeral.lift : ∀ {n} {v : Shape n}, Shape.IsNumeral v →
    ∀ {k}, n ≤ k → Shape.IsNumeral (v.lift k) := by
  intro n v hv
  induction hv with
  | bot => intro k _; rw [Shape.lift_bot]; exact .bot
  | zero =>
    intro k hk
    cases k with
    | zero => exact absurd hk (Nat.not_succ_le_zero _)
    | succ k => exact .zero
  | succ _ ih =>
    intro k hk
    cases k with
    | zero => exact absurd hk (Nat.not_succ_le_zero _)
    | succ k => exact .succ (ih (Nat.le_of_succ_le_succ hk))

theorem Shape.IsNumeral.lift_of : ∀ {n k}, n ≤ k → ∀ {v : Shape n},
    Shape.IsNumeral (v.lift k) → Shape.IsNumeral v := by
  intro n
  induction n with
  | zero =>
    intro k _ v H
    cases v with
    | bot => exact .bot
    | sort r =>
      cases k with
      | zero => rw [Shape.lift_self] at H; cases H
      | succ k => cases H
  | succ n ih =>
    intro k h v H
    cases k with
    | zero => exact absurd h (Nat.not_succ_le_zero _)
    | succ k =>
      cases v with
      | bot => exact .bot
      | zero => exact .zero
      | succ w =>
        cases H with | succ hw => exact .succ (ih (Nat.le_of_succ_le_succ h) hw)
      | _ => cases H

theorem ShapeFun.LE.lift {Δ : List Term} {n k} (h : n ≤ k) {f g : ShapeFun n}
    (H : ShapeFun.LE Δ (Shape.LE Δ) f g) :
    ShapeFun.LE Δ (Shape.LE Δ) (ShapeFun.lift (Shape.lift k) f)
      (ShapeFun.lift (Shape.lift k) g) := by
  intro e' he'
  obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he'
  have ⟨e₀, he₀, hlab, hin, hout⟩ := H e he
  exact ⟨_, ShapeFun.mem_lift.2 ⟨e₀, he₀, rfl⟩, hlab,
    (Shape.lift_le_lift h).2 hin, (Shape.lift_le_lift h).2 hout⟩

theorem Shape.HasType.lift_mono {Δ : List Term} : ∀ {n k}, n ≤ k → ∀ {m a : Shape n},
    Shape.HasType Δ m a → Shape.HasType Δ (m.lift k) (a.lift k) := by
  intro n
  induction n with
  | zero =>
    intro k _ m a H
    cases k with
    | zero => rw [Shape.lift_self, Shape.lift_self]; exact H
    | succ k =>
      replace H : Shape.HasType0 m a := H
      cases H with
      | bot =>
        cases a with
        | bot => exact .bot (.bot .sort)
        | sort r => exact .bot .sort
      | sort => exact .sort
  | succ n ih =>
    intro k h m a
    cases k with
    | zero => exact absurd h (Nat.not_succ_le_zero _)
    | succ k =>
      have h' := Nat.le_of_succ_le_succ h
      have ihs : ∀ {d : Shape n} {r : Bool},
          Shape.HasType Δ d (.sort r) → Shape.HasType Δ (d.lift k) (.sort r) := by
        intro d r hd
        have := ih h' (a := Shape.sort r) hd
        rwa [Shape.lift_sort] at this
      have ihpi : ∀ {d : Shape n} {f : ShapeFun n} {r : Bool},
          ShapeFun.HasPi Δ (Shape.HasType Δ) d f (.sort r) →
          ShapeFun.HasPi Δ (Shape.HasType Δ) (d.lift k)
            (ShapeFun.lift (Shape.lift k) f) (.sort r) := by
        intro d f r hpi
        refine ⟨ihs hpi.1, fun e'' he'' => ?_⟩
        obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
        exact ihs (hpi.2 e he)
      have ihdom : ∀ {f : ShapeFun n} {d : Shape n},
          ShapeFun.HasDom Δ (Shape.HasType Δ) f d →
          ShapeFun.HasDom Δ (Shape.HasType Δ)
            (ShapeFun.lift (Shape.lift k) f) (d.lift k) := by
        intro f d H e'' he''
        obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
        have ⟨x, hwx, hx, hxle, hev⟩ := H e he
        exact ⟨x.lift k, (Shape.lift_wf h').2 hwx, ih h' hx,
          (Shape.lift_le_lift h').2 hxle, Evaluates.lift h' hev⟩
      intro H
      replace H : Shape.HasTypeS Δ (Shape.HasType Δ) m a := H
      induction H with
      | bot _ ihb => exact .bot ihb
      | sort => exact .sort
      | unit hj => exact .unit hj
      | nat => exact .nat
      | zero => exact .zero
      | succ hN => exact .succ (hN.lift h')
      | id hj => exact .id hj
      | forallE hpi => exact .forallE (ihpi hpi)
      | sigma hpi => exact .sigma (ihpi hpi)
      | lam hpi hcod =>
        refine .lam (ihpi hpi) fun e'' he'' => ?_
        obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
        have ⟨c, hwc, hev, hcty⟩ := hcod e he
        exact ⟨c.lift k, (Shape.lift_wf h').2 hwc, Evaluates.lift h' hev, ih h' hcty⟩
      | pair hpi hxle hwx hxd hwc hev hyc =>
        exact .pair (ihpi hpi) ((Shape.lift_le_lift h').2 hxle) ((Shape.lift_wf h').2 hwx)
          (ih h' hxd) ((Shape.lift_wf h').2 hwc) (Evaluates.lift h' hev) (ih h' hyc)
      | refl => exact .refl

/-- Typing at the total level: at the canonical level, and (by
`lift_mono`) at every level above it. -/
def TShape.HasType (Δ : List Term) (m a : TShape) : Prop :=
  Shape.HasType Δ (m.2.lift (max m.1 a.1)) (a.2.lift (max m.1 a.1))

/-- One direction only, for the reason given above: a witness at the
canonical level can be read at any higher level. -/
theorem TShape.HasType.def {Δ : List Term} {m a : TShape} {k}
    (h1 : m.1 ≤ k) (h2 : a.1 ≤ k) (H : TShape.HasType Δ m a) :
    Shape.HasType Δ (m.2.lift k) (a.2.lift k) := by
  rw [show m.2.lift k = (m.2.lift (max m.1 a.1)).lift k from
        (Shape.lift_lift (Nat.le_max_left ..)).symm,
      show a.2.lift k = (a.2.lift (max m.1 a.1)).lift k from
        (Shape.lift_lift (Nat.le_max_right ..)).symm]
  exact Shape.HasType.lift_mono (Nat.max_le.2 ⟨h1, h2⟩) H

/-- At a common level the two agree. -/
theorem TShape.HasType.T {Δ : List Term} {n} {m a : Shape n} :
    TShape.HasType Δ (Shape.T m) (Shape.T a) ↔ Shape.HasType Δ m a := by
  show Shape.HasType Δ (m.lift (max n n)) (a.lift (max n n)) ↔ _
  rw [Nat.max_self, Shape.lift_self, Shape.lift_self]

/-- Typing at the total level transports along a typed substitution of the
context.  The level is untouched, so the canonical level is too, and the
statement is `Shape.HasType.subst` with `lift_subst` on each side. -/
theorem TShape.HasType.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {m a : TShape} (H : TShape.HasType Δ m a) :
    TShape.HasType Θ (m.subst τ) (a.subst τ) := by
  show Shape.HasType Θ (Shape.lift (max m.1 a.1) (m.2.subst τ))
    (Shape.lift (max m.1 a.1) (a.2.subst τ))
  rw [Shape.lift_subst, Shape.lift_subst]
  exact Shape.HasType.subst hΘ W H

/-- Cumulativity at the total level. -/
theorem TShape.HasType.cumul {Δ : List Term} {a : TShape} {r s : Bool}
    (h : TShape.HasType Δ a (TShape.sort r)) (hrs : r ≤ s) :
    TShape.HasType Δ a (TShape.sort s) := by
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

/-! ## Reflection of `HasType` along `lift`

The converse of `lift_mono`, by induction on the level.  Every clause is
either literally unchanged by lifting or reflects componentwise; the two
that need work are the graph clauses, where the domain condition goes
through `HasDom.lift_of` (this induction hypothesis being exactly the `ih`
it wants), and the code conditions of `lam`/`pair`, where the code
produced at the level above need not be a lift.

For the codes, `Evaluates.lift_of` finds a lift above the given code and
`mono_graph` then raises it to a lift that is both lookup-reachable and a
type, at which `mono_r` can retype the output before the induction
hypothesis reflects it. -/
theorem Shape.HasType.lift_of_type {Δ : List Term} : ∀ {n k}, n ≤ k → ∀ {a : Shape n},
    Shape.HasType Δ (a.lift k) .type → Shape.HasType Δ a .type := by
  intro n
  induction n with
  | zero =>
    intro k _ a H
    cases k with
    | zero => rwa [Shape.lift_self] at H
    | succ k => cases a with
      | bot => exact Shape.HasType0.bot
      | sort r => exact Shape.HasType0.sort
  | succ n ih =>
    intro k h a H
    cases k with
    | zero => exact absurd h (Nat.not_succ_le_zero _)
    | succ k =>
      have h' := Nat.le_of_succ_le_succ h
      cases a with
      | bot => exact .bot .sort
      | sort r => exact .sort
      | unit r => exact .unit (Bool.le_true' r)
      | nat => exact .nat
      | id r A₀ a₀ b₀ => exact .id (Bool.le_true' r)
      | forallE A B d f =>
        cases Shape.hasType_succ.1 H with | forallE hpi => ?_
        exact .forallE ⟨ih h' hpi.1,
          fun e he => ih h' (hpi.2 _ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩))⟩
      | sigma A B d f =>
        cases Shape.hasType_succ.1 H with | sigma hpi => ?_
        exact .sigma ⟨ih h' hpi.1,
          fun e he => ih h' (hpi.2 _ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩))⟩
      | zero | succ | lam | pair | refl => cases Shape.hasType_succ.1 H

theorem Shape.HasType.lift_of {Δ : List Term} (hΔ : ⊢ Δ) :
    ∀ {n k}, n ≤ k → ∀ {m a : Shape n}, Shape.WF Δ m → Shape.WF Δ a →
      Shape.HasType Δ (m.lift k) (a.lift k) → Shape.HasType Δ m a := by
  intro n
  induction n with
  | zero =>
    intro k _ m a _ _ H
    cases k with
    | zero => rwa [Shape.lift_self, Shape.lift_self] at H
    | succ k =>
      cases m with
      | bot => exact Shape.HasType0.bot
      | sort s =>
        cases a with
        | bot => cases Shape.hasType_succ.1 H
        | sort j => cases Shape.hasType_succ.1 H with | sort => exact Shape.HasType0.sort
  | succ n ih =>
    intro k h m a hwm hwa
    cases k with
    | zero => exact absurd h (Nat.not_succ_le_zero _)
    | succ k =>
      have h' := Nat.le_of_succ_le_succ h
      have ihpi : ∀ {d : Shape n} {f : ShapeFun n} {r : Bool},
          Shape.WF Δ d → ShapeFun.WF Δ (Shape.WF Δ) f →
          ShapeFun.HasPi Δ (Shape.HasType Δ) (d.lift k)
            (ShapeFun.lift (Shape.lift k) f) (.sort r) →
          ShapeFun.HasPi Δ (Shape.HasType Δ) d f (.sort r) := by
        intro d f r hwd hwf hpi
        refine ⟨Shape.HasType.lift_of_type h' hpi.1, fun e he => ?_⟩
        exact ih h' (hwf e he).2.2.2 (by cases n <;> trivial)
          (by rw [Shape.lift_sort]; exact hpi.2 _ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩))
      have ihcode : ∀ {f : ShapeFun n} {A a : Term} {xin yout : Shape n},
          ShapeFun.WF Δ (Shape.WF Δ) f → ShapeFun.Compat Shape.Compat Δ f f →
          (∀ e ∈ f, Shape.HasType Δ e.out .type) →
          Shape.WF Δ xin → Shape.WF Δ yout →
          (∃ c', Shape.WF Δ c' ∧
            Evaluates Δ (ShapeFun.lift (Shape.lift k) f) A a (xin.lift k) c' ∧
            Shape.HasType Δ (yout.lift k) c') →
          ∃ c, Shape.WF Δ c ∧ Evaluates Δ f A a xin c ∧ Shape.HasType Δ yout c := by
        intro f A a xin yout hwf hco hty hwx hwy H
        have ⟨c', _, hev', hty'⟩ := H
        have houts : ∀ e ∈ f, Shape.WF Δ e.out := fun e he => (hwf e he).2.2.2
        have ⟨c₀, hle, hev₀⟩ := Evaluates.lift_of hΔ h' hwf hco hwx hev'
        have ⟨c₁, hev₁, hc₀c₁, hc₁ty⟩ :=
          Evaluates.mono_graph hΔ hco hwx.coherent houts hty (Shape.HasType.join hΔ)
            (ShapeFun.LE.refl_aux hwf) hev₀
        have hwc₁ := Evaluates.wf hΔ houts hev₁
        refine ⟨c₁, hwc₁, hev₁, ih h' hwy hwc₁ (Shape.HasType.mono_r (r := true) hΔ
          ((Shape.lift_wf h').2 hwy) ((Shape.lift_wf h').2 hwc₁) hty'
          (hle.trans hΔ ((Shape.lift_le_lift h').2 hc₀c₁)) ?_)⟩
        have := Shape.HasType.lift_mono (Δ := Δ) h' hc₁ty
        rwa [Shape.lift_sort] at this
      intro H
      cases m with
      | bot =>
        cases Shape.hasType_succ.1 H with
        | bot hb => exact .bot (Shape.HasType.lift_of_type h hb)
      | sort s =>
        cases a with
        | sort j => cases Shape.hasType_succ.1 H with | sort => exact .sort
        | _ => cases Shape.hasType_succ.1 H
      | unit r =>
        cases a with
        | sort j => cases Shape.hasType_succ.1 H with | unit hj => exact .unit hj
        | _ => cases Shape.hasType_succ.1 H
      | nat =>
        cases a with
        | sort j => cases Shape.hasType_succ.1 H with | nat => exact .nat
        | _ => cases Shape.hasType_succ.1 H
      | zero =>
        cases a with
        | nat => exact .zero
        | _ => cases Shape.hasType_succ.1 H
      | id r A₀ a₀ b₀ =>
        cases a with
        | sort j => cases Shape.hasType_succ.1 H with | id hj => exact .id hj
        | _ => cases Shape.hasType_succ.1 H
      | refl w =>
        cases a with
        | id r A₁ a₁ b₁ => cases Shape.hasType_succ.1 H with | refl => exact .refl
        | _ => cases Shape.hasType_succ.1 H
      | succ v =>
        cases a with
        | nat =>
          cases Shape.hasType_succ.1 H with
          | succ hN => exact .succ (Shape.IsNumeral.lift_of h' hN)
        | _ => cases Shape.hasType_succ.1 H
      | forallE A B d f =>
        cases a with
        | sort r =>
          cases Shape.hasType_succ.1 H with
          | forallE hpi => exact .forallE (ihpi hwm.2.2.1 hwm.2.2.2.1 hpi)
        | _ => cases Shape.hasType_succ.1 H
      | sigma A B d f =>
        cases a with
        | sort r =>
          cases Shape.hasType_succ.1 H with
          | sigma hpi => exact .sigma (ihpi hwm.2.2.1 hwm.2.2.2.1 hpi)
        | _ => cases Shape.hasType_succ.1 H
      | lam g =>
        cases a with
        | forallE A₁ B₁ d f =>
          cases Shape.hasType_succ.1 H with | lam hpi hcod => ?_
          have hpi' := ihpi hwa.2.2.1 hwa.2.2.2.1 hpi
          refine .lam hpi' fun e he => ?_
          exact ihcode hwa.2.2.2.1 hwa.2.2.2.2 hpi'.2 (hwm.2.2.1 e he).2.2.1
            (hwm.2.2.1 e he).2.2.2 (hcod _ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩))
        | _ => cases Shape.hasType_succ.1 H
      | pair ty tm x y =>
        cases a with
        | sigma A₁ B₁ d f =>
          cases Shape.hasType_succ.1 H with
          | pair hpi hxle hwx hxd hwc hev hyc => ?_
          sorry
        | _ => cases Shape.hasType_succ.1 H

/-- **Fullness for typing.**  On the shapes that come from the level
below, the higher level types exactly what the lower one did. -/
theorem Shape.HasType.lift_iff {Δ : List Term} (hΔ : ⊢ Δ) {n k} (h : n ≤ k) {m a : Shape n}
    (hwm : Shape.WF Δ m) (hwa : Shape.WF Δ a) :
    Shape.HasType Δ (m.lift k) (a.lift k) ↔ Shape.HasType Δ m a :=
  ⟨Shape.HasType.lift_of hΔ h hwm hwa, Shape.HasType.lift_mono h⟩
