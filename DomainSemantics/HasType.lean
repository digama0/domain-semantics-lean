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
  ∃ d₀ f₀, Shape.LE Δ d d₀ ∧ ShapeFun.LE Δ (Shape.LE Δ) f f₀ ∧
    T d₀ .type ∧ ShapeFun.HasDom Δ T f₀ d₀ ∧ ∀ e ∈ f₀, T e.out a

/-- "is a numeral".  The one condition that cannot be phrased as
`HasType · .nat` uniformly, because `Shape 0` has no `nat`; it is
independent of typing, so it gets its own recursion rather than an
inline match in `HasType`.  `HasType v .nat ↔ IsNumeral v` at positive
level (`Shape.hasType_nat_iff`). -/
def Shape.IsNumeral : ∀ {n}, Shape n → Prop
  | 0, w => w = .bot
  | _ + 1, .bot => True
  | _ + 1, .zero => True
  | _ + 1, .succ w => IsNumeral w
  | _ + 1, _ => False

/-- Weaken the codomain condition of a Π/Σ signature. -/
theorem ShapeFun.HasPi.cod {Δ : List Term} {n} {T : Shape n → Shape n → Prop}
    {d : Shape n} {f : ShapeFun n} {a a' : Shape n}
    (H : ∀ {z}, T z a → T z a') (h : ShapeFun.HasPi Δ T d f a) :
    ShapeFun.HasPi Δ T d f a' :=
  have ⟨d₀, f₀, h1, h2, h3, h4, h5⟩ := h
  ⟨d₀, f₀, h1, h2, h3, h4, fun e he => H (h5 e he)⟩

/-- One level of the typing relation, as an inductive family in the typing
relation `T` of the level below — the same shape as `ShapeFun.HasDom` and
`ShapeFun.HasPi`, which it uses.  `N` is "is a numeral", which cannot be
written as `T · .nat` uniformly because `Shape 0` has no `nat`.

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
inductive Shape.HasTypeS (Δ : List Term) {n} (T : Shape n → Shape n → Prop)
    (N : Shape n → Prop) : Shape (n + 1) → Shape (n + 1) → Prop where
  -- `⊥` inhabits exactly the types.  Being *inductive* is what lets this be
  -- one constructor with a premise at the same level; as a match it had to
  -- be spelled out per type former, because `HasType a .type` is not
  -- structurally smaller than `HasType .bot a`
  | bot {a} : HasTypeS Δ T N a .type → HasTypeS Δ T N .bot a
  | sort {r} : HasTypeS Δ T N (.sort r) (.sort true)
  | unit {r j} : r ≤ j → HasTypeS Δ T N (.unit r) (.sort j)
  | nat : HasTypeS Δ T N .nat (.sort true)
  | zero : HasTypeS Δ T N .zero .nat
  | succ {v} : N v → HasTypeS Δ T N (.succ v) .nat
  | id {r j A a b} : r ≤ j → HasTypeS Δ T N (.id r A a b) (.sort j)
  | forallE {A B d f r} :
    ShapeFun.HasPi Δ T d f (.sort r) → HasTypeS Δ T N (.forallE A B d f) (.sort r)
  | sigma {A B d f} :
    ShapeFun.HasPi Δ T d f .type → HasTypeS Δ T N (.sigma A B d f) (.sort true)
  -- the graph condition is on a graph *dominating* the λ's own
  | lam {g g₀ A B d f} :
    ShapeFun.HasPi Δ T d f .type → ShapeFun.LE Δ (Shape.LE Δ) g g₀ →
    ShapeFun.HasDom Δ T g₀ d →
    (∀ e ∈ g₀, ∃ c, Evaluates Δ f e.ty e.tm e.inp c ∧ T e.out c) →
    HasTypeS Δ T N (.lam g) (.forallE A B d f)
  -- and here on a first component dominating the pair's own, because the
  -- code is read off at it and the lookup is monotone in its input
  | pair {ty tm x y x₀ c A B d f} :
    ShapeFun.HasPi Δ T d f .type → Shape.LE Δ x x₀ → T x₀ d →
    Evaluates Δ f ty tm x₀ c → T y c →
    HasTypeS Δ T N (.pair ty tm x y) (.sigma A B d f)
  | refl {w A a b} : HasTypeS Δ T N (.refl w) (.id true A a b)

/-- `m` is a well-typed inhabitant of the type-shape `a`, by iterating
`HasTypeS` up the levels. -/
def Shape.HasType (Δ : List Term) : ∀ {n}, Shape n → Shape n → Prop
  | 0 => fun m a =>
      match m, a with
      | .bot, .bot => True
      | .bot, .sort _ => True
      | .sort _, .bot => False
      | .sort _, .sort j => j = true
  | _ + 1 => Shape.HasTypeS Δ (HasType Δ) Shape.IsNumeral

/-- The recursion equation at positive level, for `cases` and `rw`, which
do not unfold definitions. -/
theorem Shape.hasType_succ {Δ : List Term} {n} {m a : Shape (n + 1)} :
    Shape.HasType Δ m a ↔ Shape.HasTypeS Δ (Shape.HasType Δ) Shape.IsNumeral m a := Iff.rfl

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
    cases a with
    | bot => trivial
    | sort => exact Bool.eq_true_of_le h hrs
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
  | zero => intro a _; cases a <;> trivial
  | succ n => intro _ h; exact Shape.HasTypeS.bot h

/-- Anything typed has a type that is itself a type.  Now one line per
constructor: the inversion the inductive gives us does the case analysis
that used to be done by hand on both arguments. -/
theorem Shape.HasType.isType : ∀ {n} {m a : Shape n},
    Shape.HasType Δ m a → Shape.HasType Δ a .type := by
  intro n
  cases n with
  | zero => intro m a h; cases m <;> cases a <;> simp_all [Shape.HasType]
  | succ n =>
    intro m a h
    cases Shape.hasType_succ.1 h with
    | bot h => exact h
    | sort | unit | id | nat | forallE | sigma => exact .sort
    | zero | succ => exact .nat
    | lam hpi => exact .forallE hpi
    | pair hpi => exact .sigma hpi
    | refl => exact .id (Bool.le_true' true)

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

/-- Typing of shapes is stable along a typed substitution. -/
theorem Shape.HasType.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) : ∀ {n} {m a : Shape n},
    Shape.HasType Δ m a → Shape.HasType Θ (m.subst τ) (a.subst τ) := by
  intro n
  induction n with
  | zero => intro m a h; cases m <;> cases a <;> simp_all [Shape.HasType, Shape.subst]
  | succ n ih =>
    -- the "this Π/Σ type is well-formed" conjunct, substituted
    have hpi : ∀ {f : ShapeFun n} {d : Shape n},
        (Shape.HasType Δ d .type ∧ ShapeFun.HasDom Δ (Shape.HasType Δ) f d ∧
            ∀ e ∈ f, Shape.HasType Δ e.out .type) →
        (Shape.HasType Θ (d.subst τ) .type ∧
          ShapeFun.HasDom Θ (Shape.HasType Θ) (ShapeFun.subst (Shape.subst · τ) τ f)
            (d.subst τ) ∧
          ∀ e ∈ ShapeFun.subst (Shape.subst · τ) τ f, Shape.HasType Θ e.out .type) := by
      intro f d h
      refine ⟨by simpa using ih h.1, ShapeFun.HasDom.subst_of hΘ W ih h.2.1, fun e' he' => ?_⟩
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      simpa using ih (h.2.2 e he)
    intro m a h
    cases m with
    | bot =>
      cases a with
      | bot | sort | unit | nat | id => trivial
      | forallE A B d f => exact hpi h
      | sigma A B d f => exact hpi h
      | _ => exact absurd h id
    | sort s => cases a <;> first | exact absurd h id | exact h
    | unit s => cases a <;> first | exact absurd h id | exact h
    | nat => cases a <;> first | exact absurd h id | exact h
    | zero => cases a <;> first | exact absurd h id | exact h
    | id s A a' b' => cases a <;> first | exact absurd h id | exact h
    | refl w => cases a <;> first | exact absurd h id | exact h
    | succ v =>
      cases a with
      | nat =>
        cases n with
        | zero => cases (h : v = .bot); exact Shape.subst_bot
        | succ m => exact ih h
      | _ => exact absurd h id
    | forallE A B d f =>
      cases a with
      | sort r => exact ⟨by simpa using ih h.1,
          ShapeFun.HasDom.subst_of hΘ W ih h.2.1, fun e' he' => by
          obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
          simpa using ih (h.2.2 e he)⟩
      | _ => exact absurd h id
    | sigma A B d f =>
      cases a with
      | sort r => exact ⟨h.1, hpi h.2⟩
      | _ => exact absurd h id
    | lam g =>
      cases a with
      | forallE A B d f =>
        refine ⟨hpi h.1, ShapeFun.HasDom.subst_of hΘ W ih h.2.1, fun e' he' => ?_⟩
        obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
        have ⟨c, hev, hty⟩ := h.2.2 e he
        exact ⟨c.subst τ, Evaluates.subst hΘ W hev, ih hty⟩
      | _ => exact absurd h id
    | pair ty tm x y =>
      cases a with
      | sigma A B d f =>
        have ⟨c, hev, hcty⟩ := h.2.2
        exact ⟨hpi h.1, ih h.2.1, c.subst τ, Evaluates.subst hΘ W hev, ih hcty⟩
      | _ => exact absurd h id

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
  | bot => exact ⟨.bot, .bot, Shape.LE.bot, by cases n <;> trivial⟩
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
    · cases m with | bot => cases a' <;> trivial | sort s
      cases a with | bot => cases h | sort j
      cases a' with | bot => cases hle | sort j'
      exact (hle : j = j').symm.trans h
    · cases y with | bot => exact hz | sort s
      cases z with | bot => exact hy | sort s'
      exact hy
  | succ n ih =>
    obtain ⟨ihm, ihj⟩ := ih
    refine ⟨?_, ?_⟩
    · -- mono_r
      intro m a a' r hwm hwa h hle hA
      cases m with
      | bot => exact .bot (.cumul hA (Bool.le_true' r))
      | sort s =>
        cases a with | sort j => ?_ | _ => cases h
        cases a' <;> cases hle; exact h
      | unit t =>
        cases a with | sort j => ?_ | _ => cases h
        cases a' <;> cases hle; exact h
      | nat =>
        cases a with | sort j => ?_ | _ => cases h
        cases a' <;> cases hle; exact h
      | id t A₀ a₀ b₀ =>
        cases a with | sort j => ?_ | _ => cases h
        cases a' <;> cases hle; exact h
      | zero => cases a <;> cases h; cases a' <;> cases hle; trivial
      | succ v => cases a <;> (try cases h); cases a' <;> cases hle; trivial
      | refl w =>
        cases a with | id t A₀ a₀ b₀ => ?_ | _ => cases h
        cases a' with | id t' A₁ a₁ b₁ => ?_ | _ => cases hle
        exact (hle.1 : t = t').symm.trans h
      | forallE A₀ B₀ d f =>
        cases a with | sort j => ?_ | _ => cases h
        cases a' with | sort j' => exact ((hle : j = j') ▸ h : _) | _ => cases hle
      | sigma A₀ B₀ d f =>
        cases a with | sort j => ?_ | _ => cases h
        cases a' with | sort j' => ?_ | _ => cases hle
        exact hle ▸ h
      | pair ty tm x y =>
        cases a with | sigma A₀ B₀ d g => ?_ | _ => cases h
        cases a' with | sigma A₁ B₁ d' g' => ?_ | _ => cases hle
        have ⟨c, hev, hcty⟩ := h.2.2
        have ⟨c', hev', hcle, hc'ty⟩ :=
          Evaluates.mono_graph hΔ hwa.2.2.2.2 (Shape.WF.coherent hwm.2.2.1)
            (fun e' he' => (hwa.2.2.2.1 e' he').2.2.2)
            (fun e' he' => hA.2.2.2 e' he') ihj hle.2.2 hev
        exact ⟨hA.2, ihm hwm.2.2.1 hwa.2.2.1 h.2.1 hle.2.1 hA.2.1,
          c', hev', ihm hwm.2.2.2.1 (Evaluates.wf hΔ
            (fun e' he' => (hwa.2.2.2.1 e' he').2.2.2) hev') hcty hcle hc'ty⟩
      | lam g =>
        cases a with | forallE A₀ B₀ d f => ?_ | _ => cases h
        cases a' with | forallE A₁ B₁ d' f' => ?_ | _ => cases hle
        refine ⟨⟨hA.1, hA.2.1, fun e he => .cumul (hA.2.2 e he) (Bool.le_true' r)⟩, ?_, ?_⟩
        · intro e he
          have ⟨x, hwx, hx, hxle, hev⟩ := h.2.1 e he
          exact ⟨x, hwx, ihm hwx hwa.2.2.1 hx hle.2.1 hA.1, hxle, hev⟩
        · intro e he
          have ⟨c, hev, hcty⟩ := h.2.2 e he
          have ⟨c', hev', hcle, hc'ty⟩ :=
            Evaluates.mono_graph hΔ hwa.2.2.2.2 (hwm.2.2.1 e he).2.2.1.coherent
              (fun e' he' => (hwa.2.2.2.1 e' he').2.2.2)
              (fun e' he' => hA.2.2 e' he') ihj hle.2.2 hev
          exact ⟨c', hev', ihm (hwm.2.2.1 e he).2.2.2 (Evaluates.wf hΔ
            (fun e' he' => (hwa.2.2.2.1 e' he').2.2.2) hev') hcty hcle hc'ty⟩
    · -- typed joins
      intro y z r hwy hwz hc hy hz
      cases y with
      | bot => exact hz
      | forallE A₀ B₀ d f =>
        cases z with | bot => exact hy | forallE A₁ B₁ d' g => ?_ | _ => cases hc
        have hdj := ihj hwy.2.2.1 hwz.2.2.1 hc.2.1 hy.1 hz.1
        have ⟨hu₁, hu₂⟩ := Shape.le_join hΔ hwy.2.2.1 hwz.2.2.1 hc.2.1
        refine ⟨hdj, fun e he => ?_, fun e he => ?_⟩
        · match List.mem_append.1 he with
          | .inl he =>
            have ⟨x, hwx, hx, hxle, hev⟩ := hy.2.1 e he
            exact ⟨x, hwx, ihm hwx (Shape.WF.join hΔ hc.2.1 hwy.2.2.1 hwz.2.2.1) hx hu₁ hdj,
              hxle, Evaluates.mono_sub (fun _ h => List.mem_append.2 (.inl h)) hev⟩
          | .inr he =>
            have ⟨x, hwx, hx, hxle, hev⟩ := hz.2.1 e he
            exact ⟨x, hwx, ihm hwx (Shape.WF.join hΔ hc.2.1 hwy.2.2.1 hwz.2.2.1) hx hu₂ hdj,
              hxle, Evaluates.mono_sub (fun _ h => List.mem_append.2 (.inr h)) hev⟩
        · match List.mem_append.1 he with
          | .inl he => exact hy.2.2 e he
          | .inr he => exact hz.2.2 e he
      | sigma A₀ B₀ d f =>
        cases z with | bot => exact hy | sigma A₁ B₁ d' g => ?_ | _ => cases hc
        have hdj := ihj hwy.2.2.1 hwz.2.2.1 hc.2.1 hy.2.1 hz.2.1
        have ⟨hu₁, hu₂⟩ := Shape.le_join hΔ hwy.2.2.1 hwz.2.2.1 hc.2.1
        refine ⟨hy.1, hdj, fun e he => ?_, fun e he => ?_⟩
        · match List.mem_append.1 he with
          | .inl he =>
            have ⟨x, hwx, hx, hxle, hev⟩ := hy.2.2.1 e he
            exact ⟨x, hwx, ihm hwx (Shape.WF.join hΔ hc.2.1 hwy.2.2.1 hwz.2.2.1) hx hu₁ hdj,
              hxle, Evaluates.mono_sub (fun _ h => List.mem_append.2 (.inl h)) hev⟩
          | .inr he =>
            have ⟨x, hwx, hx, hxle, hev⟩ := hz.2.2.1 e he
            exact ⟨x, hwx, ihm hwx (Shape.WF.join hΔ hc.2.1 hwy.2.2.1 hwz.2.2.1) hx hu₂ hdj,
              hxle, Evaluates.mono_sub (fun _ h => List.mem_append.2 (.inr h)) hev⟩
        · match List.mem_append.1 he with
          | .inl he => exact hy.2.2.2 e he
          | .inr he => exact hz.2.2.2 e he
      | _ => cases z <;> exact hy

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
  cases n <;> cases x <;> first | rfl | exact absurd h id

/-- A proposition is inhabited only by `⊥`. -/
theorem Shape.HasType.proofIrrel (hΔ : ⊢ Δ) : ∀ {n} {a x : Shape n},
    Shape.WF Δ a → Shape.WF Δ x →
    Shape.HasType Δ a .prop → Shape.HasType Δ x a → x = .bot := by
  intro n
  induction n with
  | zero =>
    intro a x _ _ ha h
    cases a with
    | bot => exact Shape.HasType.bot_r h
    | sort s => exact Bool.noConfusion (ha : false = true)
  | succ n ih =>
    intro a x hwa hwx ha h
    cases a with
    | bot => exact Shape.HasType.bot_r h
    | sort s => exact Bool.noConfusion (ha : false = true)
    | nat => exact Bool.noConfusion (ha : false = true)
    | sigma => exact Bool.noConfusion (ha.1 : false = true)
    | zero | succ | lam | pair | refl => exact absurd ha id
    | unit t =>
      -- nothing but `⊥` inhabits `unit` at all, so the flag never matters
      cases x <;> first | rfl | exact absurd h id
    | id t A₀ a₀ b₀ =>
      -- `HasType (.id t ..) .prop` forces `t = false`, and `refl` needs `t = true`
      have ht : t = false := by
        cases t with
        | false => rfl
        | true => exact Bool.noConfusion (Bool.eq_true_of_le (r := true) rfl ha)
      subst ht
      cases x with
      | bot => rfl
      | refl w => exact Bool.noConfusion (h : false = true)
      | _ => exact absurd h id
    | forallE A₀ B₀ d f =>
      cases x with
      | bot => rfl
      | lam g =>
        -- a well-formed λ carries real information, so it cannot inhabit a
        -- Π-type whose codomain family is propositional
        have ⟨hne, hnb, hwg, _⟩ := hwx
        have ⟨_, _, _, hwf, hco⟩ := hwa
        cases g with
        | nil => exact absurd rfl hne
        | cons e g' =>
          have he : e ∈ e :: g' := List.mem_cons_self ..
          have ⟨_, _, hwin, hwout⟩ := hwg e he
          have ⟨c, hev, hcty⟩ := h.2.2 e he
          have ⟨z, hwz, hcz, hzty⟩ :=
            Evaluates.bounded hΔ hwf hco (Shape.WF.coherent hwin) ha.2.2 hev
          have hbot : e.out = .bot :=
            ih hwz hwout hzty (Shape.HasType.mono_r hΔ hwout hwz hcty hcz hzty)
          have hb : Shape.IsBot (Shape.bot : Shape n) := by cases n <;> trivial
          exact absurd (hbot ▸ hb) (hnb e he)
      | _ => exact absurd h id

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

theorem Shape.HasType.lift_mono {Δ : List Term} : ∀ {n k}, n ≤ k → ∀ {m a : Shape n},
    Shape.HasType Δ m a → Shape.HasType Δ (m.lift k) (a.lift k) := by
  intro n
  induction n with
  | zero =>
    intro k _ m a
    cases k with
    | zero => rw [Shape.lift_self, Shape.lift_self]; exact id
    | succ k => cases m <;> cases a <;> exact id
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
      have ihdom : ∀ {f : ShapeFun n} {d : Shape n},
          ShapeFun.HasDom Δ (Shape.HasType Δ) f d →
          ShapeFun.HasDom Δ (Shape.HasType Δ)
            (ShapeFun.lift (Shape.lift k) f) (d.lift k) := by
        intro f d H e'' he''
        obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
        have ⟨x, hwx, hx, hxle, hev⟩ := H e he
        exact ⟨x.lift k, (Shape.lift_wf h').2 hwx, ih h' hx,
          (Shape.lift_le_lift h').2 hxle, Evaluates.lift h' hev⟩
      have ihout : ∀ {f : ShapeFun n} {r : Bool},
          (∀ e ∈ f, Shape.HasType Δ e.out (.sort r)) →
          ∀ e ∈ ShapeFun.lift (Shape.lift k) f, Shape.HasType Δ e.out (.sort r) := by
        intro f r H e'' he''
        obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
        exact ihs (H e he)
      have ihpi : ∀ {d : Shape n} {f : ShapeFun n} {r : Bool},
          (Shape.HasType Δ d .type ∧ ShapeFun.HasDom Δ (Shape.HasType Δ) f d ∧
              ∀ e ∈ f, Shape.HasType Δ e.out (.sort r)) →
          (Shape.HasType Δ (d.lift k) .type ∧
            ShapeFun.HasDom Δ (Shape.HasType Δ) (ShapeFun.lift (Shape.lift k) f) (d.lift k) ∧
            ∀ e ∈ ShapeFun.lift (Shape.lift k) f, Shape.HasType Δ e.out (.sort r)) :=
        fun ⟨h1, h2, h3⟩ => ⟨ihs h1, ihdom h2, ihout h3⟩
      intro H
      cases m with
      | bot =>
        cases a with
        | forallE A B d f => exact ihpi H
        | sigma A B d f => exact ihpi H
        | _ => exact H
      | sort | unit | nat | zero => cases a <;> exact H
      | id t A₀ a₀ b₀ => cases a <;> exact H
      | refl w => cases a <;> exact H
      | succ v =>
        cases a with
        | nat =>
          cases n with
          | zero =>
            have hv : v = Shape.bot := H
            cases k with
            | zero =>
              show Shape.lift 0 v = Shape.bot
              rw [hv, Shape.lift_bot]
            | succ k =>
              show Shape.HasType Δ (v.lift (k+1)) Shape.nat
              rw [hv, Shape.lift_bot]
              trivial
          | succ n =>
            cases k with
            | zero => exact absurd h' (Nat.not_succ_le_zero _)
            | succ k =>
              show Shape.HasType Δ (v.lift (k+1)) Shape.nat
              exact ih h' (a := Shape.nat) H
        | _ => exact H
      | pair ty tm x y =>
        cases a with
        | sigma A B d f =>
          have ⟨c, hev, hcty⟩ := H.2.2
          exact ⟨ihpi H.1, ih h' H.2.1, c.lift k, Evaluates.lift h' hev, ih h' hcty⟩
        | _ => exact H
      | forallE A₀ B₀ d f =>
        cases a with
        | sort r => exact ihpi H
        | _ => exact H
      | sigma A₀ B₀ d f =>
        cases a with
        | sort j => exact ⟨H.1, ihpi H.2⟩
        | _ => exact H
      | lam g =>
        cases a with
        | forallE A₁ B₁ d f =>
          refine ⟨ihpi H.1, ihdom H.2.1, ?_⟩
          intro e'' he''
          obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he''
          have ⟨c, hev, hcty⟩ := H.2.2 e he
          exact ⟨c.lift k, Evaluates.lift h' hev, ih h' hcty⟩
        | _ => exact H

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

/-! ## Join-closure of typing, at any type

Master has this at an arbitrary type (`WShape.HasType.join`); ours so far
only at a sort, as a by-product of `mono_r_join`.  The general form is
directedness of the *inhabitant* set, and it is what the saturation-closure
argument for `HasDom`'s witness needs: a witness normalised to a join of
witnesses of matching entries is typed only if typing survives joins.

Unlike master this is a standalone induction rather than part of the
mutual one, because `mono_r` is already available. -/
theorem Shape.HasType.join_at {Δ : List Term} (hΔ : ⊢ Δ) : ∀ {n} {y z a : Shape n},
    Shape.WF Δ y → Shape.WF Δ z → Shape.WF Δ a → Shape.Compat Δ y z →
    Shape.HasType Δ y a → Shape.HasType Δ z a → Shape.HasType Δ (y.join z) a := by
  intro n
  induction n with
  | zero =>
    intro y z a _ _ _ _ hy hz
    cases y with
    | bot => exact hz
    | sort s => cases z with | bot => exact hy | sort s' => exact hy
  | succ n ih =>
    intro y z a hwy hwz hwa hc hy hz
    cases y with
    | bot => exact hz
    | sort s => cases z with | bot => exact hy | _ => exact hy
    | unit t => cases z with | bot => exact hy | _ => exact hy
    | nat => cases z with | bot => exact hy | _ => exact hy
    | zero => cases z with | bot => exact hy | _ => exact hy
    | id t A a' b' => cases z with | bot => exact hy | _ => exact hy
    -- a Π or Σ is only ever typed at a sort, where the sort-join applies
    | forallE A B d f =>
      cases a with
      | sort r => exact Shape.HasType.join hΔ hwy hwz hc hy hz
      | _ => exact absurd hy id
    | sigma A B d f =>
      cases a with
      | sort r => exact Shape.HasType.join hΔ hwy hwz hc hy hz
      | _ => exact absurd hy id
    | succ v =>
      cases z with
      | bot => exact hy
      | succ w =>
        cases a with
        | nat =>
          cases n with
          | zero =>
            show Shape.join v w = Shape.bot
            rw [show v = Shape.bot from hy, show w = Shape.bot from hz]
            rfl
          | succ n => exact ih hwy hwz trivial hc hy hz
        | _ => exact absurd hy id
      | _ => exact hy
    | refl v =>
      cases z with
      | bot => exact hy
      | refl w =>
        cases a with
        | id t A' a'' b'' => exact hy
        | _ => exact absurd hy id
      | _ => exact hy
    | lam g =>
      cases z with
      | bot => exact hy
      | lam g' =>
        cases a with
        | forallE A₀ B₀ d f =>
          refine ⟨hy.1, ?_, ?_⟩
          · intro e he
            match List.mem_append.1 he with
            | .inl he =>
              have ⟨x, hwx, hx, hxle, hev⟩ := hy.2.1 e he
              exact ⟨x, hwx, hx, hxle,
                Evaluates.mono_sub (fun _ h => List.mem_append.2 (.inl h)) hev⟩
            | .inr he =>
              have ⟨x, hwx, hx, hxle, hev⟩ := hz.2.1 e he
              exact ⟨x, hwx, hx, hxle,
                Evaluates.mono_sub (fun _ h => List.mem_append.2 (.inr h)) hev⟩
          · intro e he
            match List.mem_append.1 he with
            | .inl he => exact hy.2.2 e he
            | .inr he => exact hz.2.2 e he
        | _ => exact absurd hy id
      | _ => exact hy
    | pair ty tm x₁ y₁ =>
      cases z with
      | bot => exact hy
      | pair ty' tm' x₂ y₂ =>
        cases a with
        | sigma A₀ B₀ d f =>
          -- the two pairs merge componentwise, so unlike `lam` the codes
          -- have to be merged too: evaluate both at the joined input (the
          -- labels agree by `Compat`), join the two results, and bound that
          -- join by a *typed* code so that `mono_r` can retype both second
          -- components at it
          have hwx := Shape.WF.join hΔ hc.2.1 hwy.2.2.1 hwz.2.2.1
          have hout : ∀ e ∈ f, Shape.WF Δ e.out := fun e he => (hwa.2.2.2.1 e he).2.2.2
          have ⟨c₁, ev₁, hty₁⟩ := hy.2.2
          have ⟨c₂, ev₂, hty₂⟩ := hz.2.2
          have ⟨hu₁, hu₂⟩ := Shape.le_join hΔ hwy.2.2.1 hwz.2.2.1 hc.2.1
          have ev₁' : Evaluates Δ f ty tm (x₁.join x₂) c₁ := Evaluates.mono_input hΔ hu₁ ev₁
          have ev₂' : Evaluates Δ f ty tm (x₁.join x₂) c₂ :=
            Evaluates.label (LabelEq.symm hc.1) (Evaluates.mono_input hΔ hu₂ ev₂)
          have hcc : Shape.Compat Δ c₁ c₂ :=
            Evaluates.compat hΔ hwa.2.2.2.2 hwx.coherent ev₁' ev₂'
          have ⟨c', ev', hcle, hc'ty⟩ :=
            Evaluates.mono_graph hΔ hwa.2.2.2.2 hwx.coherent hout
              (fun e he => hy.1.2.2 e he) (Shape.HasType.join hΔ)
              (ShapeFun.LE.refl_aux hwa.2.2.2.1) (Evaluates.join hcc ev₁' ev₂')
          have hwc' := Evaluates.wf hΔ hout ev'
          have ⟨hv₁, hv₂⟩ :=
            Shape.le_join hΔ (Evaluates.wf hΔ hout ev₁') (Evaluates.wf hΔ hout ev₂') hcc
          exact ⟨hy.1, ih hwy.2.2.1 hwz.2.2.1 hwa.2.2.1 hc.2.1 hy.2.1 hz.2.1, c', ev',
            ih hwy.2.2.2.1 hwz.2.2.2.1 hwc' hc.2.2
              (Shape.HasType.mono_r hΔ hwy.2.2.2.1 hwc' hty₁ (hv₁.trans hΔ hcle) hc'ty)
              (Shape.HasType.mono_r hΔ hwz.2.2.2.1 hwc' hty₂ (hv₂.trans hΔ hcle) hc'ty)⟩
        | _ => exact absurd hy id
      | _ => exact hy

/-! ## Retyping a lookup at a typed query

Round (b): any query shape can be replaced by a *typed* one -- the join of
`HasDom`'s own witnesses for the entries the derivation uses -- without
changing the result.  The `entry` step splices in that entry's witness
derivation (relabelled by `Evaluates.label`, since `HasDom` states it at
the entry's own label), and the `join` step needs typing to survive joins,
which is `HasType.join_at`.

Dual to `Evaluates.tighten`: that one lands in the graph but says nothing
about typing, this one is typed but says nothing about the graph.  The
fixed point of the two is what `HasDom` reflection needs. -/
theorem Evaluates.retype {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {d : Shape n}
    (hwd : Shape.WF Δ d) (hd : Shape.HasType Δ d .type)
    (hdom : ShapeFun.HasDom Δ (Shape.HasType Δ) f d)
    {A a : Term} {x : Shape n} (hwx : Shape.WF Δ x) {c : Shape n}
    (H : Evaluates Δ f A a x c) :
    ∃ y, Shape.WF Δ y ∧ Shape.HasType Δ y d ∧ Shape.LE Δ y x ∧ Evaluates Δ f A a y c := by
  induction H with
  | bot =>
    exact ⟨.bot, by cases n <;> trivial, Shape.HasType.bot hd, Shape.LE.bot, .bot⟩
  | entry e he hlab hin =>
    have ⟨y, hwy, hty, hyle, hev⟩ := hdom e he
    exact ⟨y, hwy, hty, hyle.trans hΔ hin, hev.label hlab⟩
  | lower hw hle _ ih =>
    have ⟨y, hwy, hty, hyx, hev⟩ := ih
    exact ⟨y, hwy, hty, hyx, .lower hw hle hev⟩
  | join hc _ _ ih₁ ih₂ =>
    have ⟨y₁, hwy₁, hty₁, hy₁x, hev₁⟩ := ih₁
    have ⟨y₂, hwy₂, hty₂, hy₂x, hev₂⟩ := ih₂
    have hcy := Shape.Compat.of_common_upper hΔ hwx.coherent hy₁x hy₂x
    have ⟨hu₁, hu₂⟩ := Shape.le_join hΔ hwy₁ hwy₂ hcy
    exact ⟨y₁.join y₂, Shape.WF.join hΔ hcy hwy₁ hwy₂,
      Shape.HasType.join_at hΔ hwy₁ hwy₂ hwd hcy hty₁ hty₂,
      Shape.join_le hy₁x hy₂x,
      .join hc (hev₁.mono_input hΔ hu₁) (hev₂.mono_input hΔ hu₂)⟩

/-- `Shape.exists_joins` with typing carried along: a list of well-formed
inhabitants of `d` with a common upper bound has a least upper bound, and
that is an inhabitant of `d` too.  Immediate from `join_at`. -/
theorem Shape.HasType.exists_joins {Δ : List Term} (hΔ : ⊢ Δ) {n} {d w : Shape n}
    (hwd : Shape.WF Δ d) (hd : Shape.HasType Δ d .type) (hw : Shape.WF Δ w) :
    ∀ {s : List (Shape n)}, (∀ y ∈ s, Shape.WF Δ y ∧ Shape.HasType Δ y d) →
      (∀ y ∈ s, Shape.LE Δ y w) →
      ∃ j, Shape.Joins Δ s j ∧ Shape.WF Δ j ∧ Shape.HasType Δ j d ∧ Shape.LE Δ j w := by
  intro s
  induction s with
  | nil =>
    exact fun _ _ =>
      ⟨.bot, .nil, by cases n <;> trivial, Shape.HasType.bot hd, Shape.LE.bot⟩
  | cons y s ih =>
    intro hty hle
    have ⟨j, hj, hwj, hjd, hjw⟩ :=
      ih (fun z hz => hty z (.tail _ hz)) (fun z hz => hle z (.tail _ hz))
    have ⟨hwy, hyd⟩ := hty y (.head _)
    have hc := Shape.Compat.of_common_upper hΔ hw.coherent (hle y (.head _)) hjw
    exact ⟨y.join j, hj.cons hΔ hwy hwj hc, Shape.WF.join hΔ hc hwy hwj,
      Shape.HasType.join_at hΔ hwy hwj hwd hc hyd hjd,
      Shape.join_le (hle y (.head _)) hjw⟩

/-- One round of the normalisation, packaged so that it depends on the
sublist `s` **alone** and not on `s`'s join.

This is what lets the cycle argument's relation stay conditional -- `R s s'`
may assume that `s` has a join and dominates the result -- while its
successor `s'` is still chosen outside that assumption, as `find_cycle`'s
totality hypothesis requires.  For each entry of `s`, `HasDom`'s witness
(round (b)) is tightened back into the graph (round (a)); `t` collects the
entries so reached and `ys` the witnesses, whose join will be the round's
typed intermediate once a common bound is available.

The two `∀ w` clauses are minimality deferred in the same way: the joins of
`t`'s inputs and outputs do not exist until a bound is known, so what is
recorded is that `y`, resp. `e.out`, is below every upper bound of them. -/
theorem ShapeFun.HasDom.step {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n} {d : Shape n}
    (hwf : ShapeFun.WF Δ (Shape.WF Δ) f) (hco : ShapeFun.Compat Shape.Compat Δ f f)
    (hdom : ShapeFun.HasDom Δ (Shape.HasType Δ) f d) :
    ∀ {s : List (Entry (Shape n))}, s.Sublist f →
      ∃ (t : List (Entry (Shape n))) (ys : List (Shape n)), t.Sublist f ∧
        (∀ e' ∈ t, ∃ e ∈ s, LabelEq Δ e'.ty e'.tm e.ty e.tm) ∧
        (∀ y ∈ ys, Shape.WF Δ y ∧ Shape.HasType Δ y d ∧ ∃ e ∈ s, Shape.LE Δ y e.inp) ∧
        (∀ v ∈ t.map Entry.inp, ∃ y ∈ ys, Shape.LE Δ v y) ∧
        (∀ e ∈ s, ∀ w, Shape.WF Δ w → (∀ v ∈ t.map Entry.out, Shape.LE Δ v w) →
          Shape.LE Δ e.out w) := by
  intro s
  induction s with
  | nil => exact fun _ => ⟨[], [], List.nil_sublist f, nofun, nofun, nofun, nofun⟩
  | cons e s ih =>
    intro hsf
    have he : e ∈ f := hsf.subset (.head _)
    have ⟨t₀, ys₀, ht₀, hlab₀, hys₀, hbd₀, hmin₀⟩ :=
      ih ((List.sublist_cons_self e s).trans hsf)
    have ⟨y, hwy, hyd, hyle, hev⟩ := hdom e he
    have ⟨se, ji, jo, hse, hlabe, hjie, hwjie, hjiy, hjoe, hwjoe, houte⟩ :=
      Evaluates.tighten hΔ hwf hco hwy hev
    have ⟨t, ht, htt₀, htse, hunion⟩ := ht₀.union hse
    refine ⟨t, y :: ys₀, ht, ?_, ?_, ?_, ?_⟩
    · intro e' he'
      match hunion e' he' with
      | .inl h' => have ⟨e'', he'', hl⟩ := hlab₀ e' h'; exact ⟨e'', .tail _ he'', hl⟩
      | .inr h' => exact ⟨e, .head _, hlabe e' h'⟩
    · intro z hz
      match List.mem_cons.1 hz with
      | .inl h' => exact h' ▸ ⟨hwy, hyd, e, .head _, hyle⟩
      | .inr h' =>
        have ⟨hwz, hzd, e', he', hzle⟩ := hys₀ z h'
        exact ⟨hwz, hzd, e', .tail _ he', hzle⟩
    · intro v hv
      obtain ⟨e'', he'', rfl⟩ := List.mem_map.1 hv
      match hunion e'' he'' with
      | .inl h' =>
        have ⟨y', hy', hle'⟩ := hbd₀ e''.inp (List.mem_map.2 ⟨e'', h', rfl⟩)
        exact ⟨y', .tail _ hy', hle'⟩
      | .inr h' =>
        exact ⟨y, .head _,
          (hjie.le hwjie _ (List.mem_map.2 ⟨e'', h', rfl⟩)).trans hΔ hjiy⟩
    · intro e' he' w hw hub
      match List.mem_cons.1 he' with
      | .inl h' =>
        subst h'
        exact houte.trans hΔ (hjoe.min hw fun v hv => hub v (by
          obtain ⟨e'', he'', rfl⟩ := List.mem_map.1 hv
          exact List.mem_map.2 ⟨e'', htse.subset he'', rfl⟩))
      | .inr h' =>
        exact hmin₀ e' h' w hw fun v hv => hub v (by
          obtain ⟨e'', he'', rfl⟩ := List.mem_map.1 hv
          exact List.mem_map.2 ⟨e'', htt₀.subset he'', rfl⟩)

/-- Typing is invariant under mutual `≤`.  Master's
`WShape.HasType.mono_l` (ShapeOld.lean:3554), a mutual induction on the
level whose graph cases run the same cycle argument as `HasDom.normalize`
below. -/
theorem Shape.HasType.mono_l (hΔ : ⊢ Δ) : ∀ {n} {m m' a : Shape n},
    Shape.WF Δ m → Shape.WF Δ m' → Shape.LE Δ m m' → Shape.LE Δ m' m →
    Shape.HasType Δ m a → Shape.HasType Δ m' a := sorry

open List in
/-- **Normalisation of `HasDom`'s witness.**  Every lookup succeeds at a
query that is simultaneously a join of the graph's own inputs (so a lift,
when the graph is one) and an inhabitant of the domain.

Rounds (a) and (b) each give one of the two properties and destroy the
other, so they are alternated to a fixed point.  A state is a sublist of
the graph -- master runs the cycle on `f` itself (ShapeOld.lean:3615)
because saturation makes `f.app x` the output of a single entry; without
it a lookup is answered by a *set* of entries, so the carrier is
`f.allSublists`.

Nothing in the relation mentions `Evaluates`: by `Evaluates.joins_iff` a
state is fully described by its two joins, the one over inputs bounding
the query from below and the one over outputs bounding the result from
above.  That is what lets `R` be conditional on `s` having those joins
while its successor is still a function of `s` alone (`HasDom.step`). -/
theorem ShapeFun.HasDom.normalize {Δ : List Term} (hΔ : ⊢ Δ) {n} {f : ShapeFun n}
    {d : Shape n} (hwf : ShapeFun.WF Δ (Shape.WF Δ) f)
    (hco : ShapeFun.Compat Shape.Compat Δ f f)
    (hwd : Shape.WF Δ d) (hd : Shape.HasType Δ d .type)
    (hdom : ShapeFun.HasDom Δ (Shape.HasType Δ) f d)
    {A a : Term} {x c : Shape n} (hwx : Shape.WF Δ x) (H : Evaluates Δ f A a x c) :
    ∃ s j, s <+ f ∧ Shape.Joins Δ (s.map Entry.inp) j ∧ Shape.WF Δ j ∧
      Shape.HasType Δ j d ∧ Shape.LE Δ j x ∧ Evaluates Δ f A a j c := by
  have hwc := Evaluates.wf hΔ (fun e he => (hwf e he).2.2.2) H
  -- a state is good when its entries match the query label and its two
  -- joins exist, the output one dominating the result
  let Good : List (Entry (Shape n)) → Shape n → Shape n → Prop := fun s ji jo =>
    (∀ e ∈ s, LabelEq Δ e.ty e.tm A a) ∧
      Shape.Joins Δ (s.map Entry.inp) ji ∧ Shape.WF Δ ji ∧
      Shape.Joins Δ (s.map Entry.out) jo ∧ Shape.WF Δ jo ∧ Shape.LE Δ c jo
  -- one round: down from `s`'s input join to `s'`'s, through a typed `Y`
  let R : List (Entry (Shape n)) → List (Entry (Shape n)) → Prop := fun s s' =>
    ∀ ji jo, Good s ji jo → ∃ ji' jo' Y, Good s' ji' jo' ∧
      Shape.WF Δ Y ∧ Shape.HasType Δ Y d ∧ Shape.LE Δ ji' Y ∧ Shape.LE Δ Y ji
  have htrans : ∀ {s s' s''}, R s s' → R s' s'' → R s s'' := by
    intro s s' s'' h₁ h₂ ji jo hg
    have ⟨ji', jo', Y, hg', hwY, hYd, hj'Y, hYj⟩ := h₁ ji jo hg
    have ⟨ji'', jo'', Y', hg'', hwY', hY'd, hj''Y', hY'j'⟩ := h₂ ji' jo' hg'
    exact ⟨ji'', jo'', Y', hg'', hwY', hY'd, hj''Y',
      (hY'j'.trans hΔ hj'Y).trans hΔ hYj⟩
  have htot : ∀ s ∈ f.allSublists, ∃ s' ∈ f.allSublists, R s s' := by
    intro s hs
    have hsf : s <+ f := List.mem_allSublists.1 hs
    have ⟨t, ys, ht, hlabt, hys, hbd, hmin⟩ := hdom.step hΔ hwf hco hsf
    refine ⟨t, List.mem_allSublists.2 ht, fun ji jo hg => ?_⟩
    have ⟨hlabs, hji, hwji, hjo, hwjo, hcjo⟩ := hg
    -- the witnesses lie below `ji`, so they have a typed join `Y ≤ ji`
    have ⟨Y, hY, hwY, hYd, hYji⟩ :=
      Shape.HasType.exists_joins hΔ hwd hd hwji
        (fun y hy => ⟨(hys y hy).1, (hys y hy).2.1⟩)
        (fun y hy => have ⟨_, _, e, he, hle⟩ := hys y hy
          hle.trans hΔ (hji.le hwji _ (List.mem_map.2 ⟨e, he, rfl⟩)))
    -- `t`'s inputs lie below `Y`, and its outputs below the lookup's own
    -- bound, so both joins exist
    have ⟨ji', hji', hwji', hj'Y⟩ :=
      Shape.exists_joins hΔ hwY
        (fun v hv => have ⟨e, he, hv⟩ := List.mem_map.1 hv
          hv ▸ (hwf e (ht.subset he)).2.2.1)
        (fun v hv => have ⟨y, hy, hle⟩ := hbd v hv; hle.trans hΔ (hY.le hwY y hy))
    have hlabt' : ∀ e ∈ t, LabelEq Δ e.ty e.tm A a := fun e he =>
      have ⟨e', he', hl⟩ := hlabt e he; hl.trans (hlabs e' he')
    have ⟨J, hJ, hwJ, _⟩ :=
      Evaluates.of_sublist hΔ hwf hco hwji'.coherent ht hlabt'
        (fun e he => hji'.le hwji' _ (List.mem_map.2 ⟨e, he, rfl⟩))
    -- every output of `s` is below `t`'s output join, hence so is `c`
    refine ⟨ji', J, Y, ⟨hlabt', hji', hwji', hJ, hwJ, ?_⟩, hwY, hYd, hj'Y, hYji⟩
    refine hcjo.trans hΔ (hjo.min hwJ fun v hv => ?_)
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hv
    exact hmin e he J hwJ (hJ.le hwJ)
  -- start from the tightening of the given derivation and run the cycle
  have ⟨s₀, ji₀, jo₀, hs₀, hlab₀, hji₀, hwji₀, hji₀x, hjo₀, hwjo₀, hcjo₀⟩ :=
    Evaluates.tighten hΔ hwf hco hwx H
  have ⟨s, hsmem, hstart, hfix⟩ :=
    find_cycle R htrans f.allSublists htot s₀ (List.mem_allSublists.2 hs₀)
  have hsf : s <+ f := List.mem_allSublists.1 hsmem
  have ⟨ji₁, jo₁, Y₁, hg₁, _, _, hj₁Y₁, hY₁j₀⟩ :=
    hstart ji₀ jo₀ ⟨hlab₀, hji₀, hwji₀, hjo₀, hwjo₀, hcjo₀⟩
  have ⟨ji₂, jo₂, Y₂, hg₂, hwY₂, hY₂d, hj₂Y₂, hY₂j₁⟩ := hfix ji₁ jo₁ hg₁
  -- the fixed point squeezes the typed `Y₂` between `ji₁` and itself
  have ⟨h₁₂, _⟩ := Shape.Joins.uniq hg₁.2.2.1 hg₂.2.2.1 hg₁.2.1 hg₂.2.1
  refine ⟨s, ji₁, hsf, hg₁.2.1, hg₁.2.2.1,
    Shape.HasType.mono_l hΔ hwY₂ hg₁.2.2.1 hY₂j₁ (h₁₂.trans hΔ hj₂Y₂) hY₂d,
    (hj₁Y₁.trans hΔ hY₁j₀).trans hΔ hji₀x, ?_⟩
  exact (Evaluates.joins_iff hΔ hwf hco hg₁.2.2.1 hwc).2
    ⟨s, ji₁, jo₁, hsf, hg₁.1, hg₁.2.1, hg₁.2.2.1, Shape.LE.refl hg₁.2.2.1,
      hg₁.2.2.2.1, hg₁.2.2.2.2.1, hg₁.2.2.2.2.2⟩

/-! ## Reflection of `HasDom` along `lift`

The point of the normalisation.  `HasDom`'s witness is an existential over
shapes at the ambient level, and a shape below a lift need not itself be a
lift (`Evaluates.lift_of`'s preamble), so the witness cannot simply be
read back down.  `normalize` replaces it by a join of the graph's own
inputs, and those *are* lifts.

Reflection of the witness's typing is not available at this level -- it is
the very statement being proved one level up -- so it comes in as the
hypothesis `ih`, exactly as master threads its `mono_l` induction
hypothesis through `HasType.mono_l.ih_dom`. -/

/-- The easy direction. -/
theorem ShapeFun.HasDom.lift_mono {Δ : List Term} {n k} (h : n ≤ k) {f : ShapeFun n}
    {d : Shape n} (H : ShapeFun.HasDom Δ (Shape.HasType Δ) f d) :
    ShapeFun.HasDom Δ (Shape.HasType Δ) (ShapeFun.lift (Shape.lift k) f) (d.lift k) := by
  intro e' he'
  obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he'
  have ⟨x, hwx, hxd, hxle, hev⟩ := H e he
  exact ⟨x.lift k, (Shape.lift_wf h).2 hwx, Shape.HasType.lift_mono h hxd,
    (Shape.lift_le_lift h).2 hxle, hev.lift h⟩

/-- The reflection. -/
theorem ShapeFun.HasDom.lift_of {Δ : List Term} (hΔ : ⊢ Δ) {n k} (h : n ≤ k)
    {f : ShapeFun n} {d : Shape n}
    (hwf : ShapeFun.WF Δ (Shape.WF Δ) f) (hco : ShapeFun.Compat Shape.Compat Δ f f)
    (hwd : Shape.WF Δ d) (hd : Shape.HasType Δ d .type)
    (ih : ∀ {m a : Shape n}, Shape.WF Δ m → Shape.WF Δ a →
      Shape.HasType Δ (m.lift k) (a.lift k) → Shape.HasType Δ m a)
    (H : ShapeFun.HasDom Δ (Shape.HasType Δ) (ShapeFun.lift (Shape.lift k) f) (d.lift k)) :
    ShapeFun.HasDom Δ (Shape.HasType Δ) f d := by
  have hwf' := ShapeFun.lift_wf h hwf
  have hco' := (ShapeFun.lift_compat h (f := f) (f' := f)).2 hco
  have hd' : Shape.HasType Δ (d.lift k) .type := by
    have := Shape.HasType.lift_mono (Δ := Δ) h hd
    rwa [Shape.lift_sort] at this
  intro e he
  have hwe := hwf e he
  have ⟨X, hwX, hXd, hXle, hevX⟩ :=
    H ⟨e.ty, e.tm, e.inp.lift k, e.out.lift k⟩ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)
  have ⟨s, j, hs, hj, hwj, hjd, hjX, hevj⟩ :=
    ShapeFun.HasDom.normalize hΔ hwf' hco' ((Shape.lift_wf h).2 hwd) hd' H hwX hevX
  -- a sublist of a lifted graph is a lifted sublist, so its inputs are lifts
  simp only [ShapeFun.lift] at hs
  obtain ⟨s₀, hs₀, rfl⟩ := List.sublist_map hs
  rw [ShapeFun.map_lift_inp] at hj
  have hwin : ∀ v ∈ s₀.map Entry.inp, Shape.WF Δ v := by
    intro v hv
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 hv
    exact (hwf e' (hs₀.subset he')).2.2.1
  have hinle : ∀ v ∈ s₀.map Entry.inp, Shape.LE Δ v e.inp := by
    intro v hv
    refine (Shape.lift_le_lift h).1 ?_
    exact ((hj.le hwj _ (List.mem_map.2 ⟨v, hv, rfl⟩)).trans hΔ hjX).trans hΔ hXle
  -- their join at the level below is the witness
  have ⟨j₀, hj₀, hwj₀, hj₀e⟩ := Shape.exists_joins hΔ hwe.2.2.1 hwin hinle
  have hj₀l := Shape.Joins.lift hΔ h hwin hwj₀ hj₀
  have ⟨hle₁, hle₂⟩ := Shape.Joins.uniq hwj ((Shape.lift_wf h).2 hwj₀) hj hj₀l
  refine ⟨j₀, hwj₀, ih hwj₀ hwd
      (Shape.HasType.mono_l hΔ hwj ((Shape.lift_wf h).2 hwj₀) hle₁ hle₂ hjd),
    hj₀e, ?_⟩
  refine (Evaluates.lift_iff hΔ h hwf hco hwj₀ hwe.2.2.2).1 ?_
  exact hevj.mono_input hΔ hle₁

/-- Reflection and preservation together. -/
theorem ShapeFun.HasDom.lift_iff {Δ : List Term} (hΔ : ⊢ Δ) {n k} (h : n ≤ k)
    {f : ShapeFun n} {d : Shape n}
    (hwf : ShapeFun.WF Δ (Shape.WF Δ) f) (hco : ShapeFun.Compat Shape.Compat Δ f f)
    (hwd : Shape.WF Δ d) (hd : Shape.HasType Δ d .type)
    (ih : ∀ {m a : Shape n}, Shape.WF Δ m → Shape.WF Δ a →
      Shape.HasType Δ (m.lift k) (a.lift k) → Shape.HasType Δ m a) :
    ShapeFun.HasDom Δ (Shape.HasType Δ) (ShapeFun.lift (Shape.lift k) f) (d.lift k) ↔
      ShapeFun.HasDom Δ (Shape.HasType Δ) f d :=
  ⟨ShapeFun.HasDom.lift_of hΔ h hwf hco hwd hd ih, ShapeFun.HasDom.lift_mono h⟩

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
theorem Shape.HasType.lift_of {Δ : List Term} (hΔ : ⊢ Δ) :
    ∀ {n k}, n ≤ k → ∀ {m a : Shape n}, Shape.WF Δ m → Shape.WF Δ a →
      Shape.HasType Δ (m.lift k) (a.lift k) → Shape.HasType Δ m a := by
  intro n
  induction n with
  | zero =>
    intro k _ m a _ _
    cases k with
    | zero => rw [Shape.lift_self, Shape.lift_self]; exact id
    | succ k => cases m <;> cases a <;> exact id
  | succ n ih =>
    intro k h m a hwm hwa
    cases k with
    | zero => exact absurd h (Nat.not_succ_le_zero _)
    | succ k =>
      have h' := Nat.le_of_succ_le_succ h
      have ihs : ∀ {d : Shape n} {r : Bool}, Shape.WF Δ d →
          Shape.HasType Δ (d.lift k) (.sort r) → Shape.HasType Δ d (.sort r) := by
        intro d r hwd hd
        exact ih h' hwd (by cases n <;> trivial) (by rwa [Shape.lift_sort])
      have ihpi : ∀ {d : Shape n} {f : ShapeFun n} {r : Bool},
          Shape.WF Δ d → ShapeFun.WF Δ (Shape.WF Δ) f →
          ShapeFun.Compat Shape.Compat Δ f f →
          (Shape.HasType Δ (d.lift k) .type ∧
            ShapeFun.HasDom Δ (Shape.HasType Δ) (ShapeFun.lift (Shape.lift k) f) (d.lift k) ∧
            ∀ e ∈ ShapeFun.lift (Shape.lift k) f, Shape.HasType Δ e.out (.sort r)) →
          (Shape.HasType Δ d .type ∧ ShapeFun.HasDom Δ (Shape.HasType Δ) f d ∧
            ∀ e ∈ f, Shape.HasType Δ e.out (.sort r)) := by
        intro d f r hwd hwf hco H
        have hd := ihs hwd H.1
        exact ⟨hd, ShapeFun.HasDom.lift_of hΔ h' hwf hco hwd hd (ih h') H.2.1,
          fun e he => ihs (hwf e he).2.2.2 (H.2.2 _ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩))⟩
      have ihcode : ∀ {f : ShapeFun n} {A a : Term} {xin yout : Shape n},
          ShapeFun.WF Δ (Shape.WF Δ) f → ShapeFun.Compat Shape.Compat Δ f f →
          (∀ e ∈ f, Shape.HasType Δ e.out .type) →
          Shape.WF Δ xin → Shape.WF Δ yout →
          (∃ c', Evaluates Δ (ShapeFun.lift (Shape.lift k) f) A a (xin.lift k) c' ∧
            Shape.HasType Δ (yout.lift k) c') →
          ∃ c, Evaluates Δ f A a xin c ∧ Shape.HasType Δ yout c := by
        intro f A a xin yout hwf hco hty hwx hwy H
        have ⟨c', hev', hty'⟩ := H
        have houts : ∀ e ∈ f, Shape.WF Δ e.out := fun e he => (hwf e he).2.2.2
        have ⟨c₀, hle, hev₀⟩ := Evaluates.lift_of hΔ h' hwf hco hwx hev'
        have ⟨c₁, hev₁, hc₀c₁, hc₁ty⟩ :=
          Evaluates.mono_graph hΔ hco hwx.coherent houts hty (Shape.HasType.join hΔ)
            (ShapeFun.LE.refl_aux hwf) hev₀
        have hwc₁ := Evaluates.wf hΔ houts hev₁
        refine ⟨c₁, hev₁, ih h' hwy hwc₁ (Shape.HasType.mono_r (r := true) hΔ
          ((Shape.lift_wf h').2 hwy) ((Shape.lift_wf h').2 hwc₁) hty'
          (hle.trans hΔ ((Shape.lift_le_lift h').2 hc₀c₁)) ?_)⟩
        have := Shape.HasType.lift_mono (Δ := Δ) h' hc₁ty
        rwa [Shape.lift_sort] at this
      intro H
      cases m with
      | bot =>
        cases a with
        | forallE A B d f => exact ihpi hwa.2.2.1 hwa.2.2.2.1 hwa.2.2.2.2 H
        | sigma A B d f => exact ihpi hwa.2.2.1 hwa.2.2.2.1 hwa.2.2.2.2 H
        | _ => exact H
      | sort | unit | nat | zero => cases a <;> exact H
      | id t A₀ a₀ b₀ => cases a <;> exact H
      | refl w => cases a <;> exact H
      | succ v =>
        cases a with
        | nat =>
          cases n with
          | zero =>
            cases k with
            | zero => show v = Shape.bot; rwa [Shape.lift_self] at H
            | succ k =>
              show v = Shape.bot
              cases v with
              | bot => rfl
              | sort r => exact absurd (H : Shape.HasType Δ (Shape.sort r) Shape.nat) id
          | succ n =>
            cases k with
            | zero => exact absurd h' (Nat.not_succ_le_zero _)
            | succ k => exact ih h' hwm (by trivial) H
        | _ => exact H
      | pair ty tm x y =>
        cases a with
        | sigma A₀ B₀ d f =>
          have hpi := ihpi hwa.2.2.1 hwa.2.2.2.1 hwa.2.2.2.2 H.1
          exact ⟨hpi, ih h' hwm.2.2.1 hwa.2.2.1 H.2.1,
            ihcode hwa.2.2.2.1 hwa.2.2.2.2 hpi.2.2 hwm.2.2.1 hwm.2.2.2.1 H.2.2⟩
        | _ => exact H
      | forallE A₀ B₀ d f =>
        cases a with
        | sort r => exact ihpi hwm.2.2.1 hwm.2.2.2.1 hwm.2.2.2.2 H
        | _ => exact H
      | sigma A₀ B₀ d f =>
        cases a with
        | sort j => exact ⟨H.1, ihpi hwm.2.2.1 hwm.2.2.2.1 hwm.2.2.2.2 H.2⟩
        | _ => exact H
      | lam g =>
        cases a with
        | forallE A₁ B₁ d f =>
          have hpi := ihpi hwa.2.2.1 hwa.2.2.2.1 hwa.2.2.2.2 H.1
          refine ⟨hpi, ShapeFun.HasDom.lift_of hΔ h' hwm.2.2.1 hwm.2.2.2 hwa.2.2.1 hpi.1
            (ih h') H.2.1, fun e he => ?_⟩
          exact ihcode hwa.2.2.2.1 hwa.2.2.2.2 hpi.2.2 (hwm.2.2.1 e he).2.2.1
            (hwm.2.2.1 e he).2.2.2 (H.2.2 _ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩))
        | _ => exact H

/-- **Fullness for typing.**  On the shapes that come from the level
below, the higher level types exactly what the lower one did. -/
theorem Shape.HasType.lift_iff {Δ : List Term} (hΔ : ⊢ Δ) {n k} (h : n ≤ k) {m a : Shape n}
    (hwm : Shape.WF Δ m) (hwa : Shape.WF Δ a) :
    Shape.HasType Δ (m.lift k) (a.lift k) ↔ Shape.HasType Δ m a :=
  ⟨Shape.HasType.lift_of hΔ h hwm hwa, Shape.HasType.lift_mono h⟩
