import DomainSemantics.HasType

/-! # Canonical names (§4.7i)

Naming, relative to a *term*.  Codes name their type and values name
their own projections:

* `Shape.CodeCanonS Δ T d` — defined in `Shape.lean` — says the code `d`
  **names its type** `T`, and only at `d`'s own head: a Σ-code carries
  labels `A B` with `T ≡ Σ A B`, and nothing is said about the domain
  code or the codomain graph.  It needs no recursion of its own because
  `Shape.WF` already carries one of these at every Π and Σ node it
  descends through, so for a well-formed shape the shallow statement is
  the hereditary one.
* `Shape.ValCanon Δ t x` — the value `x` **names its own projections**: a
  pair standing for `t` is named `fst t`, its components stand for `fst t`
  and `snd t`; a λ-value's entry inputs stand for the entry labels and its
  outputs for `app t e.tm`; a code-shaped value names its type.

The point of the file is `Shape.ValCanon.defeq`: canonicity moves along a
definitional equality of the subject, **given the code the value is typed
at and that code's canonicity**.  The three doors of §4.7d were all ways
of asking the value to know its own type; here the code knows it, and the
code is what `Dom` already carries.

`TShape.Named` merges `Dom` with `ValCanon`, and `Slot` is that together
with the code's own naming — the three facts a valuation slot carries. -/

namespace DomainSemantics


/-- A value names its own projections. -/
def Shape.ValCanon (Δ : List Term) : ∀ {n}, Term → Shape n → Prop
  | 0, t, s => CodeCanonS Δ t s
  | _+1, t, .pair A₀ a x y =>
      (Δ ⊢ a ≡ Term.fst t : A₀) ∧ ValCanon Δ (.fst t) x ∧ ValCanon Δ (.snd t) y
  | _+1, t, .lam _ g =>
      ∀ e ∈ g, ValCanon Δ e.tm e.inp ∧ ValCanon Δ (.app t e.tm) e.out
  | _+1, _, .zero => True
  | _+1, _, .succ _ => True
  | _+1, _, .refl => True
  | _+1, _, .bot => True
  | _+1, t, s@(.sort _) => CodeCanonS Δ t s
  | _+1, t, s@(.unit _) => CodeCanonS Δ t s
  | _+1, t, s@.nat => CodeCanonS Δ t s
  | _+1, t, s@(.id ..) => CodeCanonS Δ t s
  | _+1, t, s@(.sigma ..) => CodeCanonS Δ t s
  | _+1, t, s@(.forallE ..) => CodeCanonS Δ t s

def TShape.CodeCanonS (Δ : List Term) (T : Term) (x : TShape) : Prop :=
  Shape.CodeCanonS Δ T x.2

def TShape.ValCanon (Δ : List Term) (t : Term) (x : TShape) : Prop :=
  Shape.ValCanon Δ t x.2


@[simp] theorem Shape.ValCanon.bot {Δ : List Term} {t : Term} {n} :
    Shape.ValCanon Δ t (Shape.bot (n := n)) := by
  cases n with
  | zero => exact Shape.CodeCanonS.bot (n := 0)
  | succ n => trivial

/-- A sort-shaped code names a sort, at every level. -/
theorem TShape.CodeCanonS.sort_iff {Δ : List Term} {T : Term} {k} {j : Bool} :
    TShape.CodeCanonS Δ T (Shape.T (n := k) (Shape.sort j)) ↔ TyEq Δ T (.sort j) := by
  cases k <;> exact Iff.rfl





/-- The instance of a type family at two equal arguments. -/
theorem TyEq.inst {Δ : List Term} (hΔ : ⊢ Δ) {A B B' a a' : Term} {u v : Bool}
    (hA : Δ ⊢ A : .sort u) (hB : A :: Δ ⊢ B ≡ B' : .sort v) (ha : Δ ⊢ a ≡ a' : A) :
    TyEq Δ (B.inst a) (B'.inst a') :=
  ⟨v, hA.instDF hΔ .sort hB ha⟩

/-! ## Transport along the type -/




/-! ## Lifting -/


theorem TShape.CodeCanonS.lift_iff {Δ : List Term} (_hΔ : ⊢ Δ) {T : Term} {a : TShape} {k}
    (h : a.1 ≤ k) : TShape.CodeCanonS Δ T a ↔ Shape.CodeCanonS Δ T (a.2.lift k) :=
  (Shape.CodeCanonS.lift_iff h).symm

/-! ## The join -/


/-! ## Downward closure -/


/-- The total-level order. -/
theorem TShape.CodeCanonS.mono {Δ : List Term} (hΔ : ⊢ Δ) {T : Term} {x x' : TShape}
    (hle : TShape.LE Δ x' x) (hC : TShape.CodeCanonS Δ T x) :
    TShape.CodeCanonS Δ T x' := by
  have h := TShape.LE.def_mp (Nat.le_max_left x'.1 x.1) (Nat.le_max_right x'.1 x.1) hle
  rw [TShape.CodeCanonS.lift_iff hΔ (Nat.le_max_right x'.1 x.1)] at hC
  rw [TShape.CodeCanonS.lift_iff hΔ (Nat.le_max_left x'.1 x.1)]
  exact Shape.CodeCanonS.mono hΔ h hC

/-- The total-level join. -/
theorem TShape.CodeCanonS.join {Δ : List Term} (hΔ : ⊢ Δ) {T : Term} {y z : TShape}
    (hy : TShape.CodeCanonS Δ T y) (hz : TShape.CodeCanonS Δ T z) :
    TShape.CodeCanonS Δ T (TShape.join y z) := by
  have h1 := Nat.le_max_left y.1 z.1; have h2 := Nat.le_max_right y.1 z.1
  rw [TShape.CodeCanonS.lift_iff hΔ (k := max y.1 z.1) (Nat.le_refl _), TShape.join.def h1 h2]
  exact Shape.CodeCanonS.join ((TShape.CodeCanonS.lift_iff hΔ h1).1 hy)
    ((TShape.CodeCanonS.lift_iff hΔ h2).1 hz)

/-! ## The lookup

A lookup in a canonical code's codomain graph at a well-typed query is a
canonical code of the family at that query.  This is the query-based
reading of the entry-based condition; it is a theorem rather than the
definition because the definition has to survive substitution, and an
entry that is dead at one stage can be live at a later one. -/
theorem TShape.CodeCanonS.lookup {Δ : List Term} (hΔ : ⊢ Δ) {n} {A B q : Term} {u v : Bool}
    {f : ShapeFun n} (hw : ShapeFun.WF Δ A (Shape.WF Δ) f)
    (hf : ∀ e ∈ f, Shape.CodeCanonS Δ (B.inst e.tm) e.out)
    (hA : Δ ⊢ A : .sort u) (hB : A :: Δ ⊢ B : .sort v) {x : TShape} :
    ∀ {c : TShape}, TEvaluates Δ f A q x c → TShape.CodeCanonS Δ (B.inst q) c := by
  intro c h
  have hwo : ∀ e ∈ f, TShape.WF Δ e.out.T := fun e he => (hw.1 e he).2.2.2
  induction h with
  | bot => exact Shape.CodeCanonS.bot
  | entry e he hlab _ =>
    exact (hf e he).conv (TyEq.inst hΔ hA hB hlab.2.symm)
  | lower hle hz ih => exact TShape.CodeCanonS.mono hΔ hle  ih
  | join hc hy hz ihy ihz =>
    exact TShape.CodeCanonS.join hΔ    ihy ihz

/-! ## The transport, along the subject -/

/-! ## Substitution

The other horn of §4.7g: the entry-based conditions substitute, because
entries map and the subject's projections commute with substitution
syntactically.  No typing is consulted. -/


theorem Shape.ValCanon.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) :
    ∀ {n} {t : Term} {s : Shape n}, Shape.ValCanon Δ t s →
      Shape.ValCanon Θ (t.subst τ) (s.subst τ) := by
  intro n
  induction n with
  | zero => intro t s h; exact Shape.CodeCanonS.subst hΘ W (n := 0) h
  | succ n ih =>
    intro t s h
    cases s with
    | bot | zero | succ | refl => trivial
    | sort | unit | nat | id | sigma | forallE => exact Shape.CodeCanonS.subst hΘ W h
    | pair A₀ a x y =>
      obtain ⟨hname, hx, hy⟩ := h
      exact ⟨IsDefEq.subst hΘ W hname, ih hx, ih hy⟩
    | lam A₀ g =>
      intro e' he'
      obtain ⟨e, he, rfl⟩ := ShapeFun.mem_subst.1 he'
      obtain ⟨hin, hout⟩ := h e he
      exact ⟨ih hin, ih hout⟩

theorem TShape.CodeCanonS.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {T : Term} {x : TShape} (h : TShape.CodeCanonS Δ T x) :
    TShape.CodeCanonS Θ (T.subst τ) (x.subst τ) :=
  Shape.CodeCanonS.subst hΘ W h


/-! ## Values: the bridge, lifting and the join -/

/-- **A canonical value is a canonical code**, read as a code: on code
heads the two predicates agree, and on value heads `CodeCanonS` asks
nothing.  So the saturated approximants of a *type* name it. -/
theorem Shape.ValCanon.toCode {Δ : List Term} :
    ∀ {n} {t : Term} {x : Shape n}, Shape.ValCanon Δ t x → Shape.CodeCanonS Δ t x := by
  intro n t x h
  cases n with
  | zero => exact h
  | succ n => cases x <;> first | exact h | trivial

/-- Numerals carry no names. -/
theorem Shape.ValCanon.of_numeral {Δ : List Term} {t : Term} :
    ∀ {n} {x : Shape n}, Shape.IsNumeral x → Shape.ValCanon Δ t x := by
  intro n x h
  cases h <;> first | exact Shape.ValCanon.bot | trivial

theorem Shape.ValCanon.lift {Δ : List Term} (_hΔ : ⊢ Δ) :
    ∀ {n m} (_ : n ≤ m) {t : Term} {s : Shape n},
      Shape.ValCanon Δ t (s.lift m) ↔ Shape.ValCanon Δ t s := by
  intro n
  induction n with
  | zero =>
    intro m _ t s
    cases m with
    | zero => rw [Shape.lift_self]
    | succ m => cases s <;> exact Iff.rfl
  | succ n ih =>
    intro m h t s
    let m+1 := m; have h' := Nat.le_of_succ_le_succ h
    cases s with
    | bot | zero | succ | refl => exact Iff.rfl
    | sort r =>
      exact (Shape.CodeCanonS.lift_iff h (T := t) (s := (ShapeS.sort r : Shape (n+1))) :)
    | unit r =>
      exact (Shape.CodeCanonS.lift_iff h (T := t) (s := (ShapeS.unit r : Shape (n+1))) :)
    | nat => exact (Shape.CodeCanonS.lift_iff h (T := t) (s := (ShapeS.nat : Shape (n+1))) :)
    | id r A a b =>
      exact (Shape.CodeCanonS.lift_iff h (T := t) (s := (ShapeS.id r A a b : Shape (n+1))) :)
    | sigma A B d f =>
      exact (Shape.CodeCanonS.lift_iff h (T := t) (s := (ShapeS.sigma A B d f : Shape (n+1))) :)
    | forallE A B d f =>
      exact (Shape.CodeCanonS.lift_iff h (T := t) (s := (ShapeS.forallE A B d f : Shape (n+1))) :)
    | pair A a x y => exact and_congr Iff.rfl (and_congr (ih h') (ih h'))
    | lam A f =>
      constructor
      · intro H e he
        have := H ⟨e.tm, e.inp.lift m, e.out.lift m⟩ (ShapeFun.mem_lift.2 ⟨e, he, rfl⟩)
        exact ⟨(ih h').1 this.1, (ih h').1 this.2⟩
      · intro H e' he'
        obtain ⟨e, he, rfl⟩ := ShapeFun.mem_lift.1 he'
        exact ⟨(ih h').2 (H e he).1, (ih h').2 (H e he).2⟩

theorem TShape.ValCanon.lift_iff {Δ : List Term} (hΔ : ⊢ Δ) {t : Term} {a : TShape} {k}
    (h : a.1 ≤ k) : TShape.ValCanon Δ t a ↔ Shape.ValCanon Δ t (a.2.lift k) :=
  (Shape.ValCanon.lift hΔ h).symm

/-- **Two canonical values of one term join canonically**: the join keeps
the left name, joins components and appends graphs. -/
theorem Shape.ValCanon.join {Δ : List Term} (_hΔ : ⊢ Δ) :
    ∀ {n} {t : Term} {y z : Shape n}, Shape.WF Δ y → Shape.WF Δ z → Shape.Compat Δ y z →
      Shape.ValCanon Δ t y → Shape.ValCanon Δ t z → Shape.ValCanon Δ t (y.join z) := by
  intro n
  induction n with
  | zero => intro t y z hwy hwz hc hy hz; exact Shape.CodeCanonS.join hy hz
  | succ n ih =>
    intro t y z hwy hwz hc hy hz
    cases y with
    | bot => simpa using hz
    | pair A a x₁ y₁ =>
      cases z with
      | bot => simpa using hy
      | pair A' a' x₂ y₂ =>
        exact ⟨hy.1, ih hwy.2.2.2.1 hwz.2.2.2.1 hc.2.2.1 hy.2.1 hz.2.1,
          ih hwy.2.2.2.2 hwz.2.2.2.2 hc.2.2.2 hy.2.2 hz.2.2⟩
      | _ => exact absurd hc id
    | lam A f =>
      cases z with
      | bot => simpa using hy
      | lam A' f' =>
        intro e he
        rcases List.mem_append.1 he with he | he
        · exact hy e he
        · exact hz e he
      | _ => exact absurd hc id
    | zero | succ | refl =>
      cases z with
      | bot => simpa using hy
      | _ => first | trivial | exact absurd hc id
    | sort | unit | nat | id | sigma | forallE =>
      cases z with
      | bot => simpa using hy
      | _ =>
        first
        | exact absurd hc id
        | exact Shape.CodeCanonS.join hy hz

theorem TShape.ValCanon.join {Δ : List Term} (hΔ : ⊢ Δ) {t : Term} {y z : TShape}
    (hwy : TShape.WF Δ y) (hwz : TShape.WF Δ z) (hc : TShape.Compat Δ y z)
    (hy : TShape.ValCanon Δ t y) (hz : TShape.ValCanon Δ t z) :
    TShape.ValCanon Δ t (TShape.join y z) := by
  have h1 := Nat.le_max_left y.1 z.1; have h2 := Nat.le_max_right y.1 z.1
  rw [TShape.ValCanon.lift_iff hΔ (k := max y.1 z.1) (Nat.le_refl _), TShape.join.def h1 h2]
  exact Shape.ValCanon.join hΔ ((TShape.WF.def h1).1 hwy) ((TShape.WF.def h2).1 hwz)
    ((TShape.Compat.def h1 h2).1 hc) ((TShape.ValCanon.lift_iff hΔ h1).1 hy)
    ((TShape.ValCanon.lift_iff hΔ h2).1 hz)

theorem TShape.ValCanon.toCode {Δ : List Term} {t : Term} {x : TShape}
    (h : TShape.ValCanon Δ t x) : TShape.CodeCanonS Δ t x := Shape.ValCanon.toCode h

theorem TShape.CodeCanonS.conv {Δ : List Term} {T T' : Term} {x : TShape}
    (h : TShape.CodeCanonS Δ T x) (hT : TyEq Δ T' T) : TShape.CodeCanonS Δ T' x :=
  Shape.CodeCanonS.conv h hT

@[simp] theorem TShape.CodeCanonS.bot {Δ : List Term} {T : Term} {n} :
    TShape.CodeCanonS Δ T (Shape.T (n := n) Shape.bot) := Shape.CodeCanonS.bot

theorem TShape.ValCanon.of_bot {Δ : List Term} {t : Term} {x : TShape} (h : x.2 = Shape.bot) :
    TShape.ValCanon Δ t x := by
  obtain ⟨n, s⟩ := x
  show Shape.ValCanon Δ t s
  rw [show s = Shape.bot from h]; exact Shape.ValCanon.bot


/-! ## Merging the slot condition into one recursion

`Slot` above is the conjunction.  `Named` below is the same thing stated
as one relation, by the same induction on the code that `TShape.Dom`
uses, with the naming conjuncts folded into its clauses.  The two agree
(`Named.iff`), which is what says the merge is sound; what it costs is
that `Dom`'s term argument has to be supplied at every site.

Three observations make the fold go through:

* at a code that only filters, a shape typed there is never a `lam` or a
  `pair`, so the only naming left is a code naming its type, and
  `CodeCanonS` is `True` on the numerals and on `refl`;
* at a Π, an entry's *input* names the entry's own label term and its
  *output* names the application — exactly `ValCanon`'s `lam` clause;
* at a Σ, the pair's name is its first projection and the components
  name the projections, with the equation read at the Σ's domain label
  rather than the pair shape's, the two being definitionally equal
  because `HasType.pair` says so. -/

/-- **The extraction.**  A name's shallow half, which is what building a
`Shape.WF` at a named index needs: at a `lam` or a `pair` it is `True`,
and at any other head the `base` clause carries it. -/
theorem TShape.NamedO.shallow {Δ : List Term} {o} {d x : TShape}
    (h : TShape.NamedO Δ o d x) : ∀ t ∈ o, Shape.CodeCanonS Δ t x.2 := by
  cases h with
  | base _ _ hc => exact hc
  | @pi _ _ _ _ _ _ _ _ hty _ _ _ _ =>
    intro _ _; cases hty <;> first | trivial | exact Shape.CodeCanonS.bot
  | @sg _ _ _ _ _ _ _ _ _ hty _ _ _ _ _ =>
    intro _ _; cases hty <;> first | trivial | exact Shape.CodeCanonS.bot

theorem TShape.Named.shallow {Δ : List Term} {d x : TShape} {t : Term}
    (h : TShape.Named Δ d t x) : Shape.CodeCanonS Δ t x.2 :=
  TShape.NamedO.shallow h t rfl

/-- **Forgetting the name.**  `Dom` is this at `none`, and this is how
the two are still bridged while `Dom` remains its own inductive. -/
theorem TShape.NamedO.toDom {Δ : List Term} {o} {d x : TShape}
    (h : TShape.NamedO Δ o d x) : TShape.Dom Δ d x := by
  induction h with
  | base hnb hty _ => exact .base hnb hty
  | @pi _ _ _ _ _ _ _ _ hty hent hin hev _ ihin ihout =>
    exact .pi hty hent ihin hev ihout
  | sg hty hps _ _ hev _ ihx ihy => exact .sg hty hps ihx hev ihy

/-- At a code that only filters, a typed shape is never a `lam` or a
`pair`, and on every other head `ValCanon` *is* `CodeCanonS`.  This is
what lets `Named`'s `base` clause carry only the code's naming. -/
theorem TShape.ValCanon.of_code {Δ : List Term} {t : Term} {d x : TShape}
    (hnb : ¬ d.IsBinder) (hty : TShape.HasType Δ x d) (hc : TShape.CodeCanonS Δ t x) :
    TShape.ValCanon Δ t x := by
  obtain ⟨n, s⟩ := x
  cases hty with
  | lam _ _ _ hwPi _ _ _ _ _ => exact absurd trivial hnb
  | pair _ _ _ hwSg _ _ _ _ _ => exact absurd trivial hnb
  | bot _ => exact Shape.ValCanon.bot
  | zero => trivial
  | succ _ => trivial
  | refl _ _ => trivial
  | sort => cases n <;> exact hc
  | unit _ => exact hc
  | nat => exact hc
  | id _ _ => exact hc
  | forallE _ _ _ => exact hc
  | sigma _ _ _ => exact hc

/-- **And back.**  At `none` nothing is asked beyond hereditary typing,
so `NamedO ... none` and `TShape.Dom` are the same thing, which is what
lets everything downstream speak only of `NamedO`. -/
theorem TShape.Dom.toNamedO {Δ : List Term} {d x : TShape}
    (h : TShape.Dom Δ d x) : TShape.NamedO Δ none d x := by
  induction h with
  | base hnb hty => exact .base hnb hty nofun
  | @pi _ _ _ _ _ _ _ hty hent _ hev _ ihin ihout =>
    exact .pi hty hent ihin hev ihout
  | @sg _ _ _ _ _ _ _ _ hty hps _ hev _ ihx ihy =>
    exact .sg hty hps (fun _ _ => nofun) ihx hev ihy

theorem TShape.NamedO.iff_none {Δ : List Term} {d x : TShape} :
    TShape.NamedO Δ none d x ↔ TShape.Dom Δ d x :=
  ⟨TShape.NamedO.toDom, TShape.Dom.toNamedO⟩

/-- **`Named` carries the naming.**  Each clause's per-part conditions
are exactly what `ValCanon` asks of the corresponding head. -/
theorem TShape.NamedO.val {Δ : List Term} {o} {d x : TShape}
    (h : TShape.NamedO Δ o d x) : ∀ t ∈ o, TShape.ValCanon Δ t x := by
  induction h with
  | base hnb hty hc => exact fun t ht => TShape.ValCanon.of_code hnb hty (hc t ht)
  | @pi o n A B d f x cs hty hent _ hev _ ihin ihout =>
    intro t ht
    cases hty with
    | bot _ => exact Shape.ValCanon.bot
    | refl _ _ => trivial
    | @lam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      intro e he
      have hmem : (⟨e.tm, e.inp.T, e.out.T⟩ : Entry TShape) ∈ cs.map (·.1) := by
        rw [← hent]
        simp only [TShape.entries, Shape.graph, List.mem_map]
        exact ⟨e, he, rfl⟩
      obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hmem
      have h1 := ihin p hp p.1.tm (by simp [Option.mem_def] at ht ⊢; simp [ht])
      have h2 := ihout p hp (Term.app t p.1.tm) (by simp [Option.mem_def] at ht ⊢; simp [ht])
      simp only [hpe] at h1 h2
      exact ⟨h1, h2⟩
  | @sg o n A B d f x ps c hty hps hname _ hev _ ihx ihy =>
    intro t ht
    cases hty with
    | bot _ => exact Shape.ValCanon.bot
    | refl _ _ => trivial
    | @pair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA₀A =>
      subst hps
      refine ⟨?_, ?_, ?_⟩
      · exact (hA₀A.choose_spec.symm.defeqDF (hname _ rfl t ht))
      · exact ihx _ rfl (Term.fst t) (by simp [Option.mem_def] at ht ⊢; simp [ht])
      · exact ihy _ rfl (Term.snd t) (by simp [Option.mem_def] at ht ⊢; simp [ht])

theorem TShape.Named.val {Δ : List Term} {d x : TShape} {t : Term}
    (h : TShape.Named Δ d t x) : TShape.ValCanon Δ t x :=
  TShape.NamedO.val h t rfl

/-- **Re-indexing.**  A `NamedO` moves to any index whose name the shape
can supply; at `none` nothing is supplied and nothing is asked.  This is
the one induction the merged notion needs, and it needs no `Dom`. -/
theorem TShape.NamedO.reindex {Δ : List Term} {o : Option Term} {d x : TShape}
    (h : TShape.NamedO Δ o d x) : ∀ {o' : Option Term},
      (∀ t ∈ o', TShape.ValCanon Δ t x) → TShape.NamedO Δ o' d x := by
  induction h with
  | base hnb hty _ =>
    intro o' hV; exact .base hnb hty fun t ht => Shape.ValCanon.toCode (hV t ht)
  | @pi o n A B d f x cs hty hent _ hev _ ihin ihout =>
    intro o' hV
    cases o' with
    | none => exact .pi hty hent (fun p hp => ihin p hp nofun) hev (fun p hp => ihout p hp nofun)
    | some t =>
      have hall : ∀ p ∈ cs, TShape.ValCanon Δ p.1.tm p.1.inp ∧
          TShape.ValCanon Δ (Term.app t p.1.tm) p.1.out := by
        cases hty with
        | bot _ =>
          have : cs = [] := by
            simpa only [TShape.entries_bot, List.map_eq_nil_iff] using hent.symm
          simp [this]
        | refl _ _ =>
          have : cs = [] := by
            simpa only [TShape.entries, Shape.graph, List.map_nil, List.map_eq_nil_iff]
              using hent.symm
          simp [this]
        | @lam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          intro p hp
          have hmem : p.1 ∈ cs.map (·.1) := List.mem_map.2 ⟨p, hp, rfl⟩
          rw [← hent] at hmem
          simp only [TShape.entries, Shape.graph, List.mem_map] at hmem
          obtain ⟨e, he, hpe⟩ := hmem
          obtain ⟨h1, h2⟩ := hV t rfl e he
          exact hpe ▸ ⟨h1, h2⟩
      refine .pi hty hent (fun p hp => ihin p hp ?_) hev (fun p hp => ihout p hp ?_)
      · intro _ h; simp only [Option.map_some, Option.mem_def, Option.some.injEq] at h
        subst h; exact (hall p hp).1
      · intro _ h; simp only [Option.map_some, Option.mem_def, Option.some.injEq] at h
        subst h; exact (hall p hp).2
  | @sg o n A B d f x ps c hty hps _ _ hev _ ihx ihy =>
    intro o' hV
    cases o' with
    | none =>
      exact .sg hty hps (fun _ _ => nofun) (fun p hp => ihx p hp nofun) hev
        (fun p hp => ihy p hp nofun)
    | some t =>
      have hall : ∀ p ∈ ps, (Δ ⊢ p.1 ≡ Term.fst t : A) ∧
          TShape.ValCanon Δ (Term.fst t) p.2.1 ∧ TShape.ValCanon Δ (Term.snd t) p.2.2 := by
        cases hty with
        | bot _ =>
          have : ps = none := by simpa only [TShape.pairParts_bot] using hps.symm
          simp [this]
        | refl _ _ =>
          have : ps = none := by simpa only [TShape.pairParts] using hps.symm
          simp [this]
        | @pair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA₀A =>
          subst hps
          intro p hp
          obtain rfl : p = _ := by simpa only [TShape.pairParts, Option.mem_def,
            Option.some.injEq] using hp.symm
          obtain ⟨hname, h1, h2⟩ := hV t rfl
          exact ⟨hA₀A.choose_spec.defeqDF hname, h1, h2⟩
      refine .sg hty hps (fun p hp => ?_) (fun p hp => ihx p hp ?_) hev
        (fun p hp => ihy p hp ?_)
      · intro _ h; simp only [Option.mem_def, Option.some.injEq] at h
        subst h; exact (hall p hp).1
      · intro _ h; simp only [Option.map_some, Option.mem_def, Option.some.injEq] at h
        subst h; exact (hall p hp).2.1
      · intro _ h; simp only [Option.map_some, Option.mem_def, Option.some.injEq] at h
        subst h; exact (hall p hp).2.2

/-- `TShape.HasType.join` with its hypotheses read as `NamedO`, so that
nothing downstream has to name `TShape.Dom`. -/
theorem TShape.HasType.joinN {Δ : List Term} (hΔ : ⊢ Δ) {o} {y z c : TShape}
    (hc : TShape.Compat Δ y z) (hy : TShape.NamedO Δ o c y)
    (hz : TShape.NamedO Δ o c z) : TShape.HasType Δ (y.join z) c :=
  TShape.HasType.join hΔ hc hy.toDom hz.toDom

/-- **Forgetting the name**, staying inside `NamedO`: this is what every
consumer downstream wants, so `TShape.Dom` never has to be mentioned
outside its own section. -/
theorem TShape.NamedO.dom {Δ : List Term} {o} {d x : TShape}
    (h : TShape.NamedO Δ o d x) : TShape.NamedO Δ none d x := h.reindex nofun

/-- **And it asks for nothing more**: the merged notion at `some t` is
hereditary typing together with the naming. -/
theorem TShape.Named.of_dom {Δ : List Term} {d x : TShape} {t : Term}
    (hD : TShape.NamedO Δ none d x) (hV : TShape.ValCanon Δ t x) :
    TShape.Named Δ d t x :=
  hD.reindex (o' := some t) (by
    intro _ h; simp only [Option.mem_def, Option.some.injEq] at h; subst h; exact hV)

/-! ### `NamedO`'s theory, once

Each closure lemma is the corresponding `Dom` one on the index-free half
and the corresponding `ValCanon` one on the name, glued by `reindex`.
Downstream speaks only of `NamedO`; `TShape.Dom` is its `none` case and
lives upstream with its own induction. -/

theorem TShape.NamedO.hasType {Δ : List Term} {o} {d x : TShape}
    (h : TShape.NamedO Δ o d x) : TShape.HasType Δ x d := h.toDom.hasType

theorem TShape.NamedO.bot {Δ : List Term} {o} {d : TShape} {n}
    (h : TShape.HasType Δ (Shape.T (n := n) .bot) d) :
    TShape.NamedO Δ o d (Shape.T (n := n) .bot) :=
  (TShape.Dom.bot h).toNamedO.reindex fun _ _ => TShape.ValCanon.of_bot rfl

theorem TShape.NamedO.of_not_binder {Δ : List Term} {d x : TShape} (hnb : ¬ d.IsBinder)
    (h : TShape.HasType Δ x d) : TShape.NamedO Δ none d x := .base hnb h nofun

theorem TShape.NamedO.of_isType {Δ : List Term} {x : TShape}
    (h : TShape.HasType Δ x TShape.type) : TShape.NamedO Δ none TShape.type x :=
  .base (fun h => h) h nofun

theorem TShape.NamedO.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {o} {d x : TShape} (h : TShape.NamedO Δ o d x) :
    TShape.NamedO Θ (o.map (·.subst τ)) (d.subst τ) (x.subst τ) :=
  (h.toDom.subst hΘ W).toNamedO.reindex (by
    intro t ht
    cases o with
    | none => simp at ht
    | some u =>
      simp only [Option.map_some, Option.mem_def, Option.some.injEq] at ht
      subst ht; exact Shape.ValCanon.subst hΘ W (h.val u rfl))

theorem TShape.NamedO.lift_subject {Δ : List Term} (hΔ : ⊢ Δ) {o} {d x : TShape}
    (h : TShape.NamedO Δ o d x) {k} (hk : x.1 ≤ k) :
    TShape.NamedO Δ o d (x.lift k) :=
  (h.toDom.lift_subject hΔ hk).toNamedO.reindex fun t ht =>
    (TShape.ValCanon.lift_iff hΔ hk).1 (h.val t ht)

theorem TShape.NamedO.mono_r {Δ : List Term} (hΔ : ⊢ Δ) {o} {d d' x : TShape}
    (h : TShape.NamedO Δ o d x) (hle : TShape.LE Δ d d')
    (hty : TShape.HasType Δ d' TShape.type) : TShape.NamedO Δ o d' x :=
  (h.toDom.mono_r hΔ hle hty).toNamedO.reindex h.val

theorem TShape.NamedO.join {Δ : List Term} (hΔ : ⊢ Δ) {o} {y z d : TShape}
    (hc : TShape.Compat Δ y z)
    (hy : TShape.NamedO Δ o d y) (hz : TShape.NamedO Δ o d z) :
    TShape.NamedO Δ o d (y.join z) :=
  (TShape.Dom.join hΔ hc hy.toDom hz.toDom).toNamedO.reindex fun t ht =>
    TShape.ValCanon.join hΔ (TShape.HasType.wf hy.hasType).1
      (TShape.HasType.wf hz.hasType).1 hc (hy.val t ht) (hz.val t ht)

/-- **The merge, as an equivalence.** -/
theorem TShape.Named.iff {Δ : List Term} {d x : TShape} {t : Term} :
    TShape.Named Δ d t x ↔ TShape.NamedO Δ none d x ∧ TShape.ValCanon Δ t x :=
  ⟨fun h => ⟨h.reindex (o' := none) nofun, h.val⟩, fun h => .of_dom h.1 h.2⟩

/-! ### `Named`'s closure properties

Each is the corresponding `Dom` lemma paired with the `ValCanon` one;
`Named.iff` is what makes that a proof. -/

theorem TShape.Named.subst {Δ Θ : List Term} {τ : Subst} (hΘ : ⊢ Θ)
    (W : Ctx.SubstEq Θ τ τ Δ) {d x : TShape} {t : Term} (h : TShape.Named Δ d t x) :
    TShape.Named Θ (d.subst τ) (t.subst τ) (x.subst τ) :=
  .of_dom (h.toDom.subst hΘ W).toNamedO (Shape.ValCanon.subst hΘ W h.val)





/-- **Canonicity moves along a definitional equality of the subject**,
given the code the value is hereditarily typed at and that code's own
canonicity.  The code knows the type (`T ≡ Σ A B`), so `fstDF`/`sndDF`/
`appDF` apply; the sub-values are typed at the code's sub-codes, which
are canonical for the sub-types; and the recursion is on the value. -/
theorem Shape.ValCanon.defeq {Δ : List Term} (hΔ : ⊢ Δ) :
    ∀ {n} {x : Shape n} {d : TShape} {T t t' : Term},
      TShape.NamedO Δ none d x.T → TShape.CodeCanonS Δ T d → Shape.ValCanon Δ t x →
      (Δ ⊢ t ≡ t' : T) → Shape.ValCanon Δ t' x := by
  intro n
  induction n with
  | zero =>
    intro x d T t t' hD hC hV ht
    replace hD := hD.toDom
    cases x with
    | bot => trivial
    | sort r =>
      cases hD.hasType with
      | sort =>
        have hT : TyEq Δ T (.sort true) := TShape.CodeCanonS.sort_iff.1 hC
        exact Shape.CodeCanonS.conv (n := 0) hV ⟨_, (hT.choose_spec.defeqDF ht).symm⟩
  | succ n ih =>
    intro x d T t t' hD hC hV ht
    replace hD := hD.toDom
    -- a code-shaped value: its type is a sort, read off the code
    have hcode {k : Nat} {j : Bool} (hd : d = Shape.T (n := k) (Shape.sort j))
        (hV' : Shape.CodeCanonS Δ t x) : Shape.CodeCanonS Δ t' x := by
      subst hd
      have hT : TyEq Δ T (.sort j) := TShape.CodeCanonS.sort_iff.1 hC
      exact hV'.conv ⟨_, (hT.choose_spec.defeqDF ht).symm⟩
    cases x with
    | bot | zero | succ | refl => trivial
    | sort r => cases hD.hasType with | sort => exact hcode rfl hV
    | unit r => cases hD.hasType with | unit => exact hcode rfl hV
    | nat => cases hD.hasType with | nat => exact hcode rfl hV
    | id r A a b => cases hD.hasType with | id => exact hcode rfl hV
    | forallE A B d f => cases hD.hasType with | forallE => exact hcode rfl hV
    | sigma A B d f => cases hD.hasType with | sigma => exact hcode rfl hV
    | pair A₀ a x y =>
      cases hD.hasType with
      | @pair _ _ _ _ _ _ f A B d _ _ _ _ _ hws _ _ _ _ hA₀A
      obtain ⟨c, hx₁, hev, hy₁⟩ := TShape.Dom.sg_inv hD
      have hwd := (TShape.HasType.wf hD.hasType).2
      have hT := hC
      have hCd := hwd.2.2.2.2.1
      have hCf := hwd.2.2.2.2.2
      obtain ⟨hname, hVx, hVy⟩ := hV
      have ht' : Δ ⊢ t ≡ t' : .sigma A B := hT.choose_spec.defeqDF ht
      have hfst : Δ ⊢ .fst t ≡ .fst t' : A := IsDefEq.fstDF₀ hΔ ht'
      have hsnd : Δ ⊢ .snd t ≡ .snd t' : B.inst (.fst t) := IsDefEq.sndDF₀ hΔ ht'
      have hA := hws.1.choose_spec
      have hB := hws.2.1.choose_spec
      have hname' : Δ ⊢ a ≡ .fst t : A := hA₀A.choose_spec.defeqDF hname
      refine ⟨hname.trans (hA₀A.choose_spec.symm.defeqDF hfst), ih hx₁.toNamedO hCd hVx hfst, ?_⟩
      refine ih hy₁.toNamedO (TShape.CodeCanonS.lookup hΔ hws.2.2.2.1 hCf hA hB hev) hVy ?_
      exact (TyEq.inst hΔ hA hB hname'.symm).choose_spec.defeqDF hsnd
    | lam A₀ g =>
      cases hD.hasType with
      | @lam _ _ _ _ _ f A B d _ _ _ hwl hwf _ _ _ _ hA₀A
      cases hD with
      | base hnb _ => exact absurd trivial hnb
      | @pi _ _ _ _ _ _ cs _ hent _ hev hout
      have hT := hC
      have hCd := hwf.2.2.2.2.1
      have hCf := hwf.2.2.2.2.2
      have hA := hwf.1.choose_spec
      have hB := hwf.2.1.choose_spec
      intro e he
      obtain ⟨hVin, hVout⟩ := hV e he
      refine ⟨hVin, ?_⟩
      -- the entry's code, from `Dom`'s per-entry list
      have hmem : (⟨e.tm, e.inp.T, e.out.T⟩ : Entry TShape) ∈ cs.map (·.1) := by
        rw [← hent]
        simp only [TShape.entries, Shape.graph, List.mem_map]
        exact ⟨e, he, rfl⟩
      obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hmem
      have hevp := hev p hp; have houtp := hout p hp
      simp only [hpe] at hevp houtp
      have htm : Δ ⊢ e.tm : A := hA₀A.choose_spec.defeqDF (hwl.2.2.1.1 e he).2.1
      have happ : Δ ⊢ .app t e.tm ≡ .app t' e.tm : B.inst e.tm :=
        IsDefEq.appDF₀ hΔ (hT.choose_spec.defeqDF ht) htm
      exact ih houtp.toNamedO (TShape.CodeCanonS.lookup hΔ hwf.2.2.2.1 hCf hA hB hevp) hVout happ

theorem TShape.ValCanon.defeq {Δ : List Term} (hΔ : ⊢ Δ) {x d : TShape} {T t t' : Term}
    (hD : TShape.NamedO Δ none d x) (hC : TShape.CodeCanonS Δ T d) (hV : TShape.ValCanon Δ t x)
    (ht : Δ ⊢ t ≡ t' : T) : TShape.ValCanon Δ t' x :=
  Shape.ValCanon.defeq hΔ (x := x.2) hD hC hV ht

/-- **The transport, on the merged notion.**  This is what the merge
buys: the hereditary typing travels with the name, so moving the name
along a definitional equality needs only the code's own naming. -/
theorem TShape.Named.defeq {Δ : List Term} (hΔ : ⊢ Δ) {T t t' : Term} {d x : TShape}
    (h : TShape.Named Δ d t x) (hC : TShape.CodeCanonS Δ T d)
    (ht : Δ ⊢ t ≡ t' : T) : TShape.Named Δ d t' x :=
  .of_dom h.toDom.toNamedO (TShape.ValCanon.defeq hΔ h.dom hC h.val ht)

/-- `⊥` names anything, at `⊥`. -/
theorem TShape.Named.bot {Δ : List Term} {t : Term} :
    TShape.Named Δ TShape.bot t TShape.bot :=
  .base (fun h => h) (TShape.HasType.bot_bot rfl) (by intro _ h; simp only [Option.mem_def, Option.some.injEq] at h; subst h; exact Shape.CodeCanonS.bot)

/-- The typing half, directly. -/
theorem TShape.Named.hasType {Δ : List Term} {d x : TShape} {t : Term}
    (h : TShape.Named Δ d t x) : TShape.HasType Δ x d := h.toDom.hasType

/-! ## The slot condition

A slot is one notion applied twice.  `Named` says a shape is hereditarily
typed at a code and names a term; a *slot* is that for the value,
together with the same for its code — read at a sort, where `Named`
degenerates to `Shape.CodeCanonS`, the code naming its type.  There is no
third conjunct, and no bundle: `Dom` and `ValCanon` are not separate
notions any more, so there is nothing left to bundle.

Its point is `Slot.defeq`: the hereditary typing travels with the name,
so moving the name along a definitional equality of the subject takes
nothing beyond what the slot already holds. -/

/-- `x` is hereditarily typed at the code `d` and names the term `t`, and
`d` names the type `T`. -/
def TShape.Slot (Δ : List Term) (T : Term) (d : TShape) (t : Term) (x : TShape) : Prop :=
  TShape.Named Δ d t x ∧ Shape.CodeCanonS Δ T d.2

/-- **The transport, with nothing to pass in.** -/
theorem TShape.Slot.defeq {Δ : List Term} (hΔ : ⊢ Δ) {T t t' : Term} {d x : TShape}
    (h : TShape.Slot Δ T d t x) (ht : Δ ⊢ t ≡ t' : T) : TShape.Slot Δ T d t' x :=
  ⟨h.1.defeq hΔ h.2 ht, h.2⟩

/-- Conversion in the type: the code's naming is the only field that sees it. -/
theorem TShape.Slot.conv {Δ : List Term} {T T' t : Term} {d x : TShape}
    (h : TShape.Slot Δ T d t x) (hT : TyEq Δ T' T) : TShape.Slot Δ T' d t x :=
  ⟨h.1, Shape.CodeCanonS.conv h.2 hT⟩
