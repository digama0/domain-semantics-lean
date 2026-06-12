import DomainSemantics.Basic

/-! # The shape domain

This file defines the semantic *shape* domain that the logical relation
will interpret terms into.

* `Shape n` is a level-graded inductive of "value-shape skeletons":
  `Shape 0` is just `bot` and `sort`; each successor level adds
  `forallE` / `lam` constructors whose function content is a finite graph
  `ShapeFun n`.
* `WShape n` carves out the well-formed shapes — those with compatible
  domain entries, joinable codomains, etc. `WShapeFun n` does the same
  for function graphs. These are the actual domain elements.
* `TShape := Σ n, WShape n` packages a shape together with its level so
  that operations across levels (`lift`, `Compat`, `join`, `app`) can be
  stated uniformly. Order, compatibility and joins on `TShape` lift both
  arguments to a common level first.
* `Shape.HasType` (and its `WShape`/`TShape` variants) is a decidable
  typing relation on shapes, including the `HasDom`/`HasTypePi`/
  `HasTypeLam` flavors used to constrain Π- and λ-shapes' graphs. -/

namespace DomainSemantics

/-- Ground (level-0) shapes: just the bottom element and a sort indexed by
`rel : Bool` (proof-relevant vs proof-irrelevant). All function-shape
information lives at level ≥ 1. -/
inductive Shape0 : Type where
  | bot : Shape0
  | sort (rel : Bool) : Shape0

/-- One step of the level-graded shape constructor: extends a previous level
`Shape` with Π- and λ-shapes whose function part is a finite graph
(`List (Shape × Shape)`). The graph encodes the function as an explicit
set of input/output samples. -/
inductive ShapeS (Shape : Type) : Type where
  | bot : ShapeS Shape
  | sort (rel : Bool) : ShapeS Shape
  | forallE : Shape → List (Shape × Shape) → ShapeS Shape
  | lam : List (Shape × Shape) → ShapeS Shape

/-- The graded shape domain: `Shape 0 = Shape0`, `Shape (n+1) = ShapeS (Shape n)`.
Higher `n` allows nesting Π/λ shapes inside other Π/λ shapes. Most of the
logical relation is parametric in this index. -/
def Shape : Nat → Type
  | 0 => Shape0
  | n + 1 => ShapeS (Shape n)

/-- A "function shape" at level `n`: a finite graph of input/output pairs
between level-`n` shapes. Used to represent the function content of a
Π-type or λ-abstraction at the next level. -/
abbrev ShapeFun (n) := List (Shape n × Shape n)

@[match_pattern] def Shape.bot : ∀ {n}, Shape n
  | 0 => Shape0.bot
  | _+1 => ShapeS.bot

@[match_pattern] def Shape.sort (rel : Bool) : ∀ {n}, Shape n
  | 0 => Shape0.sort rel
  | _+1 => ShapeS.sort rel

abbrev Shape.type : Shape n := .sort true

def ShapeFun.bot : ShapeFun n := [(.bot, .bot)]

def ShapeFun.Compat (R : α → β → Bool) (f : List (α × α)) (f' : List (β × β)) : Bool :=
  f.all fun (x, y) => f'.all fun (x', y') => R x x' → R y y'

theorem ShapeFun.Compat.def : Compat R f f' ↔ ∀ x ∈ f, ∀ y ∈ f', R x.1 y.1 → R x.2 y.2 := by
  simp [ShapeFun.Compat, -decide_implies]

/-- Decidable "compatibility" relation on shapes: two shapes are compatible
when they agree on their constructor shape and, recursively, on shared
function entries. `bot` is universally compatible. Used to characterise
when two shapes can be joined. -/
def Shape.Compat : ∀ {n}, Shape n → Shape n → Bool
  | 0, .bot, _ | 0, _, .bot | _+1, .bot, _ | _+1, _, .bot => true
  | 0, .sort r, .sort r' | _+1, .sort r, .sort r' => r = r'
  | _+1, .forallE s f, .forallE s' f' => s.Compat s' && ShapeFun.Compat Compat f f'
  | _+1, .lam f, .lam f' => ShapeFun.Compat Compat f f'
  | _, _, _ => false

theorem Shape.Compat.comm {n} {s t : Shape n} : s.Compat t = t.Compat s := by
  induction n with | zero => cases s <;> cases t <;> simp [Compat, eq_comm] | succ n ih
  let rec go {f f' : ShapeFun n} : ShapeFun.Compat Compat f f' = ShapeFun.Compat Compat f' f := by
    rw [Bool.eq_iff_iff]; simp [ShapeFun.Compat.def]
    constructor <;> intro H _ _ h1 _ _ h2 h3 <;> exact ih ▸ H _ _ h2 _ _ h1 (ih ▸ h3)
  cases s <;> cases t <;> simp +singlePass [Compat, eq_comm, ih, go]

theorem Shape.Compat.symm {n} {s t : Shape n} : s.Compat t → t.Compat s := (comm ▸ ·)

theorem Shape.Compat.bot_l {n} {s : Shape n} : bot.Compat s := by cases n <;> rfl
theorem Shape.Compat.bot_r {n} {s : Shape n} : s.Compat bot := symm bot_l

theorem Shape.Compat.sort_sort : Compat (sort r : Shape n) (sort r') ↔ r = r' := by
  cases n <;> simp [Compat]
theorem Shape.Compat.forallE_forallE {a a' : Shape n} {f f' : ShapeFun n} :
    Compat (n := n+1) (.forallE a f) (.forallE a' f') ↔
    a.Compat a' ∧ ShapeFun.Compat Compat f f' := by simp only [Compat, Bool.and_eq_true]
def ShapeFun.ble (R : α → α → Bool) (f f' : List (α × α)) : Bool :=
  f.all fun (x, y) => f'.any fun (x', y') => R x' x && R y y'

/-- Decidable order on shapes: `s ≤ s'` if both have matching head
constructors and every entry of `s`'s function part is dominated by an
entry of `s'`'s. `bot` is the least element. -/
def Shape.ble : ∀ {n}, Shape n → Shape n → Bool
  | 0, .bot, _ | _+1, .bot, _ => true
  | 0, .sort r, .sort r' | _+1, .sort r, .sort r' => r = r'
  | _+1, .forallE s f, .forallE s' f' => s.ble s' && ShapeFun.ble ble f f'
  | _+1, .lam f, .lam f' => ShapeFun.ble ble f f'
  | _, _, _ => false

/-- The order on `ShapeFun n` (function graphs): each entry of the smaller
graph must be witnessed (in both coordinates) by a wider entry of the
larger one. -/
def ShapeFun.LE (s s' : ShapeFun n) : Prop := ShapeFun.ble Shape.ble s s'
/-- The order on shapes, lifted to a `Prop` from the decidable `ble`. -/
def Shape.LE (s s' : Shape n) : Prop := s.ble s'
instance : LE (Shape n) := ⟨Shape.LE⟩
instance : DecidableRel (α := Shape n) (· ≤ ·) := fun x y => inferInstanceAs (Decidable (x.ble y))
@[simp] theorem Shape.bot_le : Shape.bot ≤ (s : Shape n) := by cases n <;> rfl

theorem ShapeFun.LE.def {f f' : ShapeFun n} : ShapeFun.LE f f' ↔
    ∀ x y : Shape n, (x, y) ∈ f → ∃ x' y' : Shape n, (x', y') ∈ f' ∧ x' ≤ x ∧ y ≤ y' := by
  simp [LE, ble]; rfl

theorem Shape.LE.def {s s' : Shape (n + 1)} : s ≤ s' ↔
    match s, s' with
    | .bot, _ => True
    | .sort r, .sort r' => r = r' --j ≤ i
    | .forallE s f, .forallE s' f' => s ≤ s' ∧ ShapeFun.LE f f'
    | .lam f, .lam f' => ShapeFun.LE f f'
        | _, _ => False := by
  dsimp only [(· ≤ ·), LE, ShapeFun.LE]
  rw [Shape.ble.eq_def]; cases s <;> cases s' <;> simp

theorem Shape.LE.rfl {s : Shape n} : s ≤ s := by
  dsimp [(· ≤ ·), Shape.LE]
  induction n with
  | zero => cases s <;> simp [ble]
  | succ n ih =>
    have ihf {s : List (Shape n × Shape n)} : ShapeFun.ble ble s s := by
      simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
      exact fun _ h => ⟨_, h, ih, ih⟩
    cases s <;> simp [ble, ih, ihf]

theorem ShapeFun.LE.rfl {s : ShapeFun n} : s.LE s := by
  simp only [ShapeFun.LE, ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
  exact fun _ h => ⟨_, h, Shape.LE.rfl, Shape.LE.rfl⟩

theorem Shape.le_bot {s : Shape n} : s ≤ .bot ↔ s = .bot :=
  ⟨(by cases n <;> cases s <;> first | rfl | cases ·), (· ▸ LE.rfl)⟩

theorem Shape.le_sort {s : Shape n} : s ≤ .sort r ↔ s = .bot ∨ s = .sort r := by
  cases n <;> simp [sort, bot, (· ≤ ·), Shape.LE] <;> cases s <;>
    simp [ble] <;> exact ⟨fun h => h ▸ rfl, fun h => by injection h⟩

theorem Shape.sort_le {s : Shape n} : .sort r ≤ s ↔ .sort r = s := by
  cases n <;> simp [sort, (· ≤ ·), Shape.LE] <;> cases s <;> simp [ble, Shape]

theorem Shape.forallE_le {s : Shape (n+1)} :
    .forallE a b ≤ s ↔ ∃ a' b', a ≤ a' ∧ ShapeFun.LE b b' ∧ .forallE a' b' = s := by
  rw [Shape.LE.def]; cases s <;> simp [Shape]

@[simp] theorem Shape.forallE_le_forallE :
    (by exact .forallE a b : Shape (n+1)) ≤ .forallE a' b' ↔ a ≤ a' ∧ ShapeFun.LE b b' := by
  refine Shape.forallE_le.trans ⟨?_, fun ⟨h1, h2⟩ => ⟨_, _, h1, h2, rfl⟩⟩
  rintro ⟨_, _, h1, h2, ⟨⟩⟩; exact ⟨h1, h2⟩

theorem Shape.lam_le {s : Shape (n+1)} :
    .lam f ≤ s ↔ ∃ f', ShapeFun.LE f f' ∧ .lam f' = s := by
  rw [Shape.LE.def]; cases s <;> simp [Shape]

@[simp] theorem Shape.lam_le_lam :
    (by exact .lam f : Shape (n+1)) ≤ .lam f' ↔ ShapeFun.LE f f' :=
  Shape.lam_le.trans ⟨by rintro ⟨_, h, ⟨⟩⟩; exact h, fun h => ⟨_, h, rfl⟩⟩

theorem Shape.LE.trans {s t u : Shape n} : s ≤ t → t ≤ u → s ≤ u := by
  dsimp [(· ≤ ·), Shape.LE]
  induction n with
  | zero => cases s <;> cases t <;> simp [ble] <;> cases u <;> simp [ble, *] <;>
      (intro h1 h2; exact h1.trans h2)
  | succ n ih =>
    have ihf {s t u : List (Shape n × Shape n)} :
        ShapeFun.ble ble s t → ShapeFun.ble ble t u → ShapeFun.ble ble s u := by
      simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
      rintro h1 h2 x hx; let ⟨_, hy, x1, x2⟩ := h1 _ hx; let ⟨_, hz, y1, y2⟩ := h2 _ hy
      exact ⟨_, hz, ih y1 x1, ih x2 y2⟩
    cases s <;> cases t <;> simp [ble] <;> cases u <;> simp [ble, *] <;> grind

theorem ShapeFun.LE.trans {s t u : ShapeFun n} : s.LE t → t.LE u → s.LE u := by
  simp only [ShapeFun.LE, ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
  rintro h1 h2 x hx; let ⟨_, hy, x1, x2⟩ := h1 _ hx; let ⟨_, hz, y1, y2⟩ := h2 _ hy
  exact ⟨_, hz, Shape.LE.trans y1 x1, Shape.LE.trans x2 y2⟩

theorem Shape.Compat.mono_r {n} {s t t' : Shape n}
    (le : t ≤ t') (H : s.Compat t') : s.Compat t := by
  induction n with
  | zero =>
    cases s <;> [simp [Compat]; skip]
    cases t <;> cases t' <;> simp [Compat, (·≤·), Shape.LE, Shape.ble] at H le ⊢
    exact H.trans le.symm
  | succ n ih
  let rec go {s t t' : ShapeFun n}
      (le : t.LE t') (H : ShapeFun.Compat Compat s t') : ShapeFun.Compat Compat s t := by
    simp [ShapeFun.Compat.def, ShapeFun.LE.def] at H le ⊢
    intro _ _ h1 _ _ h2 h3; have ⟨_, _, a1, a2, a3⟩ := le _ _ h2
    exact ih a3 <| H _ _ h1 _ _ a1 <| ih a2 h3
  (cases s with | bot => rfl | _) <;>
    (cases t' with | bot => cases le_bot.1 le; rfl | _) <;>
    simp [Compat] at H <;> (cases t with | bot => rfl | _) <;>
    simp [Shape.LE.def, Compat] at le ⊢
  · exact H.trans le.symm
  · exact ⟨ih le.1 H.1, go le.2 H.2⟩
  · exact go le H

theorem Shape.Compat.mono {n} {s s' t t' : Shape n}
    (le₁ : s ≤ s') (le₂ : t ≤ t') (H : s'.Compat t') : s.Compat t :=
  mono_r le₂ <| symm <| mono_r le₁ <| symm H

def ShapeFun.lift (lift : α → β) (x : List (α × α)) : List (β × β) :=
  x.map fun (a, b) => (lift a, lift b)

/-- Embed a `Shape n` into `Shape m` for any `m`. When `n ≤ m` this is the
canonical inclusion that preserves order; when `n > m` it forgets
structure (and `forallE`/`lam` shapes collapse to `.bot` once we hit
level 0). -/
def Shape.lift : ∀ {n} m, Shape n → Shape m
  | 0, _, .sort r | _+1, _, .sort r => .sort r
  | 0, _, .bot | _+1, _, .bot | _, 0, _ => .bot
  | _+1, _+1, .forallE s f => .forallE (lift _ s) <| ShapeFun.lift (lift _) f
  | _+1, _+1, .lam f => .lam <| ShapeFun.lift (lift _) f

@[simp] theorem Shape.lift_bot : (.bot : Shape n).lift m = .bot := by
  cases n <;> [rfl; cases m <;> rfl]

@[simp] theorem Shape.lift_sort : (.sort r : Shape n).lift m = .sort r := by
  cases n <;> [rfl; cases m <;> rfl]


theorem Shape.lift_self {s : Shape n} : s.lift n = s := by
  have {α} {lift : α → α} (IH : ∀ {s}, lift s = s) {s} : ShapeFun.lift lift s = s := by
    simp [ShapeFun.lift]; apply List.map_id''; simp [IH]
  unfold lift <;> split <;> (try rfl)
  · cases s <;> [rfl; grind]
  · rw [Shape.lift_self, this Shape.lift_self]
  · rw [this Shape.lift_self]

theorem Shape.lift_lift {s : Shape n₁} (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) :
    (s.lift n₂).lift n₃ = s.lift _ := by
  induction n₁ generalizing n₂ n₃ with
  | zero => cases s <;> simp [lift]
  | succ n₁ ih =>
    cases n₃ with
    | zero =>
      cases n₂ with | zero => rw [lift_self] | succ n₃
      cases s <;> simp [lift]
    | succ n₃ =>
      let n₂ + 1 := n₂; simp at le; replace ih {s} := ih (s := s) le
      have ihf {s : ShapeFun n₁} :
          ShapeFun.lift (lift n₃) (ShapeFun.lift (lift n₂) s) = ShapeFun.lift (lift _) s := by
        simp [ShapeFun.lift, ih]
      cases s <;> simp [lift, ih, ihf]

theorem ShapeFun.lift_lift {s : ShapeFun n₁} (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) :
    lift (Shape.lift n₃) (lift (Shape.lift n₂) s) = lift (Shape.lift _) s := by
  simp [ShapeFun.lift, Shape.lift_lift le]

theorem Shape.lift_le_lift {s t : Shape n} (le : n ≤ m) : s.lift m ≤ t.lift m ↔ s ≤ t := by
  dsimp [(· ≤ ·), Shape.LE]; rw [← Bool.eq_iff_iff]
  induction n generalizing m with
  | zero =>
    cases m with | zero => simp [lift_self] | succ m
    cases s <;> cases t <;> simp [lift, ble]
  | succ n ih =>
    let m + 1 := m; replace le := Nat.le_of_succ_le_succ le; replace ih {t' s} := @ih m t' s le
    let rec go {s t : ShapeFun n} :
        ShapeFun.ble ble (ShapeFun.lift (lift m) s) (ShapeFun.lift (lift m) t) =
        ShapeFun.ble ble s t := by
      simp only [ShapeFun.ble, ShapeFun.lift, List.all_map, List.any_map, Function.comp_def, ih]
    cases s <;> cases t <;> simp [ble, lift, go, *]

theorem ShapeFun.lift_le_lift {s t : ShapeFun n} (le : n ≤ m) :
    ShapeFun.LE (lift (Shape.lift m) s) (lift (Shape.lift m) t) ↔ ShapeFun.LE s t := by
  dsimp [ShapeFun.LE]; rw [← Bool.eq_iff_iff,
    Shape.lift_le_lift.go _ _ (Bool.eq_iff_iff.2 (Shape.lift_le_lift le))]

theorem Shape.lift_le_bot {s : Shape n} (h : n ≤ m) : s.lift m ≤ .bot ↔ s = .bot := by
  rw [← le_bot, ← lift_bot, Shape.lift_le_lift h]

theorem Shape.lift_eq_bot {s : Shape n} (h : n ≤ m) : s.lift m = .bot ↔ s = .bot := by
  rw [← le_bot, Shape.lift_le_bot h]

theorem Shape.lift_mono {s t : Shape n} : s ≤ t → s.lift m ≤ t.lift m := by
  dsimp [(· ≤ ·), Shape.LE]
  cases n with
  | zero =>
    cases s <;> cases t <;> simp [lift, ble] <;>
      first | exact Shape.bot_le | (intro h; subst h; exact Shape.LE.rfl)
  | succ n =>
    cases m with
    | zero => cases s <;> cases t <;> simp [lift, ble]
    | succ m =>
      let rec go {n m} (ih : ∀ {s t : Shape n}, s ≤ t → s.lift m ≤ t.lift m)
          {s t} : ShapeFun.ble ble s t → ShapeFun.ble ble
            (ShapeFun.lift (lift m) s) (ShapeFun.lift (lift m) t) := by
        simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true,
          ShapeFun.lift, List.any_map, List.all_map, Function.comp_apply]
        exact fun H _ h1 => let ⟨_, h2, h3, h4⟩ := H _ h1; ⟨_, h2, ih h3, ih h4⟩
      have := @Shape.lift_mono n m; dsimp [(· ≤ ·), Shape.LE] at this
      have := @go n m Shape.lift_mono
      cases s <;> cases t <;> simp [ble, lift, *] <;> grind

protected theorem Shape.Compat.lift {x y : Shape n} (le : n ≤ m) :
    (x.lift m).Compat (y.lift m) = x.Compat y := by
  induction n generalizing m with
  | zero =>
    cases m with | zero => simp [lift_self] | succ m
    cases x <;> cases y <;> simp [lift, Compat]
  | succ n ih
  let m + 1 := m; replace le := Nat.le_of_succ_le_succ le; replace ih {x y} := @ih m x y le
  let rec go {x y : ShapeFun n} :
      ShapeFun.Compat Compat (ShapeFun.lift (lift m) x) (ShapeFun.lift (lift m) y) =
      ShapeFun.Compat Compat x y := by
    rw [Bool.eq_iff_iff]; simp only [ShapeFun.lift, ShapeFun.Compat.def, List.forall_mem_map, ih]
  cases x <;> cases y <;> simp [Compat, lift, go, *]

def ShapeFun.olift (lift : α → Option β) (x : List (α × α)) : Option (List (β × β)) :=
  x.mapM fun (a, b) => return (← lift a, ← lift b)

def Shape.olift : ∀ {n m}, Shape n → Option (Shape m)
  | 0, _, .sort r | _+1, _, .sort r => some (.sort r)
  | 0, _, .bot | _+1, _, .bot => some .bot
  | _+1, 0, _ => none
  | _+1, _+1, .forallE s f => return .forallE (← s.olift) (← ShapeFun.olift olift f)
  | _+1, _+1, .lam f => return .lam (← ShapeFun.olift olift f)

theorem Shape.olift_eq_lift (le : n ≤ m) {s : Shape n} :
    s.olift = some (s.lift m) := by
  let rec go {n m} (IH : n ≤ m → ∀ {s : Shape n}, s.olift = some (s.lift m))
      (le : n ≤ m) {s : ShapeFun n} :
      ShapeFun.olift olift s = some (ShapeFun.lift (lift m) s) := by
    simp only [ShapeFun.olift, ShapeFun.lift, IH le]
    rw [List.mapM_eq_some, List.forall₂_map_right_iff]
    exact .rfl fun _ _ => rfl
  unfold olift; split <;> simp [lift] at le ⊢ <;> simp [olift_eq_lift le, go olift_eq_lift le]

theorem ShapeFun.olift_eq_lift (le : n ≤ m) {s : ShapeFun n} :
    olift Shape.olift s = some (lift (Shape.lift m) s) :=
  Shape.olift_eq_lift.go Shape.olift_eq_lift le

theorem Shape.olift_thm (le : n ≤ m) {s : Shape m} {t : Shape n} :
    s.olift (m := n) = some t ↔ s = t.lift m := by
  let rec go {n m}
      (IH : n ≤ m → ∀ {s : Shape m} {t : Shape n}, s.olift (m := n) = some t ↔ s = t.lift m)
      (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
      ShapeFun.olift olift s = some t ↔ s = ShapeFun.lift (lift m) t := by
    simp [ShapeFun.lift, ShapeFun.olift, List.mapM_eq_some]
    rw [← List.forall₂_eq, List.forall₂_map_right_iff]
    apply iff_of_eq; congr; ext ⟨a, a'⟩ ⟨b, b'⟩; simp [IH le]
  unfold olift; split
    <;> (try first | cases Nat.le_zero.1 le | cases n)
    <;> cases t <;> simp [lift, bot, sort]
  iterate 4 · grind
  all_goals have le := Nat.le_of_succ_le_succ le
  · simp [olift_thm le, go olift_thm le]; grind
  · simp [go olift_thm le]; grind

theorem ShapeFun.olift_thm (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
    olift Shape.olift s = some t ↔ s = lift (Shape.lift m) t :=
  Shape.olift_thm.go Shape.olift_thm le

theorem Shape.lift_inj (le : n ≤ m) {s t : Shape n} : s.lift m = t.lift m ↔ s = t := by
  refine ⟨fun H => ?_, (· ▸ rfl)⟩
  cases ((Shape.olift_thm le).2 H).symm.trans <| (Shape.olift_thm le).2 rfl; rfl

theorem ShapeFun.lift_inj (le : n ≤ m) {s t : ShapeFun n} :
    lift (Shape.lift m) s = lift (Shape.lift m) t ↔ s = t := by
  refine ⟨fun H => ?_, (· ▸ rfl)⟩
  cases ((ShapeFun.olift_thm le).2 H).symm.trans <| (ShapeFun.olift_thm le).2 rfl; rfl

@[simp] theorem Shape.olift_bot : Shape.olift (n := n) (m := m) .bot = some .bot := by
  cases n <;> cases m <;> rfl

@[simp] theorem ShapeFun.olift_bot :
    olift (Shape.olift (n := n) (m := m)) ShapeFun.bot = some ShapeFun.bot := by
  simp [bot, olift]

@[simp] theorem Shape.olift_sort : Shape.olift (n := n) (m := m) (.sort r) = some (.sort r) := by
  cases n <;> cases m <;> rfl

def ShapeFun.maxBelow (s : ShapeFun n) : Shape n × Shape n :=
  (s.find? fun (x, _) => s.all fun (x', _) => x' ≤ x).getD (.bot, .bot)

def ShapeFun.trunc (s : ShapeFun n) (a : Shape n) : ShapeFun n := s.filter (·.1 ≤ a)
def ShapeFun.app (s : ShapeFun n) (a : Shape n) : Shape n := maxBelow (s.trunc a) |>.2

theorem ShapeFun.lift_trunc (le : n ≤ m) :
    lift (Shape.lift m) (trunc f a : ShapeFun n) = trunc (lift (Shape.lift m) f) (a.lift m) := by
  simp [trunc, lift, List.filter_map]; congr 2; ext x; simp [Shape.lift_le_lift le]

theorem ShapeFun.lift_maxBelow {f : ShapeFun n} (le : n ≤ m) :
    (maxBelow f).1.lift m = (maxBelow (lift (Shape.lift m) f)).1 ∧
    (maxBelow f).2.lift m = (maxBelow (lift (Shape.lift m) f)).2 := by
  refine let F x := (x.1.lift m, x.2.lift m)
    have : F (maxBelow f) = maxBelow (lift (Shape.lift m) f) := ?_
    ⟨congrArg (·.1) this, congrArg (·.2) this⟩
  simp [maxBelow, lift]
  generalize eq₁ : List.find? .. = r, eq₂ : List.find? .. = r'
  suffices r = r' by subst this; cases r <;> simp [F]
  subst eq₁ eq₂; congr 1; ext x; simp; congr 1; ext y; simp [Shape.lift_le_lift le]

@[simp] theorem ShapeFun.lift_app (le : n ≤ m) :
    (app f a : Shape n).lift m = app (lift (Shape.lift m) f) (a.lift m) := by
  simp [app, lift_trunc le, lift_maxBelow le]

def ShapeFun.join (join : Shape n → Shape n → Shape n) (f f' : ShapeFun n) : ShapeFun n :=
  f.foldl (init := []) fun l x => f'.foldl (init := l) fun l y =>
  if x.1.Compat y.1 then let j := join x.1 y.1; (j, join (f.app j) (f'.app j)) :: l else l

theorem ShapeFun.mem_join {join} {f f' : ShapeFun n} {a} :
    a ∈ ShapeFun.join join f f' ↔ ∃ x ∈ f, ∃ y ∈ f', x.1.Compat y.1 ∧
      let j := join x.1 y.1; a = (j, join (f.app j) (f'.app j)) := by
  refine let F x := _; let G x y := _
    (?_ : a ∈ f.foldl (fun l x => f'.foldl (F x) l) [] ↔ (∃ x ∈ f, ∃ y ∈ f', G x y) ∨ a ∈ [])
    |>.trans (or_iff_left (by simp))
  generalize f = f₁, f' = f₂, [] = l
  induction f₁ generalizing l with simp [-Prod.exists, or_assoc, *] | cons _ f₁ ih
  refine .trans (or_congr_right ?_) or_left_comm; clear ih
  induction f₂ generalizing l <;> simp [-Prod.exists, or_assoc, *]
  refine .trans (or_congr_right ?_) or_left_comm
  unfold F G; split <;> rename_i h <;> simp [h]

def Shape.join : ∀ {n}, Shape n → Shape n → Shape n
  | 0, s, .bot | 0, .bot, s | _+1, .bot, s | _+1, s, .bot => s
  | 0, .sort r, .sort r' | _+1, .sort r, .sort r' => if r = r' then .sort r else .bot
  | _+1, .forallE s f, .forallE s' f' => .forallE (join s s') (ShapeFun.join join f f')
  | _+1, .lam f, .lam f' => .lam (ShapeFun.join join f f')
  | _+1, _, _ => .bot

theorem Shape.lift_join {x y : Shape n} (le : n ≤ m) :
    (x.join y).lift m = (x.lift m).join (y.lift m) := by
  induction n generalizing m with
  | zero =>
    cases m with | zero => simp [lift_self] | succ m
    cases x <;> cases y <;> simp [lift, join, sort]; split <;> simp [lift, sort]
  | succ n ih
  let m + 1 := m; replace le := Nat.le_of_succ_le_succ le; replace ih {x y} := @ih m x y le
  let rec go {x y : ShapeFun n} :
      ShapeFun.lift (lift m) (ShapeFun.join join x y) =
      ShapeFun.join join (ShapeFun.lift (lift m) x) (ShapeFun.lift (lift m) y) := by
    refine
      let G _ := _; let F l x := List.foldl (G x) l y
      let G' _ := _; let F' l x := List.foldl (G' x) l (ShapeFun.lift (lift m) y)
      have (r:_) : ShapeFun.lift (lift m) (x.foldl F r) =
        (ShapeFun.lift (lift m) x).foldl F' (r.map fun x => (lift m x.1, lift m x.2)) := ?_
      this []
    simp [ShapeFun.lift]; generalize x = x'; induction x' generalizing r <;> simp [*]; congr 1
    unfold F F'
    simp [ShapeFun.lift]; generalize y = y'; induction y' generalizing r <;> simp [*]; congr 1
    simp [G, G', Compat.lift le]; split <;> simp [ih, ShapeFun.lift_app le]
  cases x with cases y <;> simp [join, lift, go, sort, ih]
  | sort => split <;> simp [lift, sort]

theorem Shape.bot_join {x : Shape n} : bot.join x = x := by cases n <;> cases x <;> rfl
theorem Shape.join_bot {x : Shape n} : x.join bot = x := by cases n <;> cases x <;> rfl
@[simp] theorem Shape.sort_join_sort :
    join (.sort r : Shape n) (.sort r') = if r = r' then .sort r else .bot := by cases n <;> rfl

def ShapeFun.WF (WF : Shape n → Prop) (f : ShapeFun n) : Prop :=
  ((∃ y, (.bot, y) ∈ f) ∧ ∀ x ∈ f, ∀ y ∈ f,
    (x.1.Compat y.1 → ∃ z ∈ f, x.1.join y.1 ≤ z.1 ∧ z.1 ≤ x.1.join y.1) ∧
    (x.1 ≤ y.1 → x.2 ≤ y.2)) ∧
  ∀ x ∈ f, WF x.1 ∧ WF x.2

def ShapeFun.NonZero (f : ShapeFun n) := ∃ x ∈ f, ¬x.2 ≤ .bot

instance {f : ShapeFun n} : Decidable f.NonZero :=
  inferInstanceAs (Decidable (∃ x ∈ f, ¬x.2 ≤ .bot))

theorem ShapeFun.NonZero.mono {f f' : ShapeFun n} (le : f.LE f') : NonZero f → NonZero f'
  | ⟨_, h1, h2⟩ => have ⟨_, _, a1, _, a2⟩ := ShapeFun.LE.def.1 le _ _ h1; ⟨_, a1, mt a2.trans h2⟩

def Shape.WF : ∀ {n}, Shape n → Prop
  | 0, _ | _+1, .bot | _+1, .sort .. => True
  | _+1, .forallE s f => s.WF ∧ ShapeFun.WF WF f
  | _+1, .lam f => ShapeFun.WF WF f ∧ ShapeFun.NonZero f

theorem ShapeFun.NonZero.lift_iff {n m} {x : ShapeFun n} (le : n ≤ m) :
    NonZero (lift (Shape.lift m) x) ↔ NonZero (n := n) x := by
  simp [NonZero, lift]
  refine ⟨fun ⟨_, _, ⟨_, _, h1, rfl, rfl⟩, h2⟩ => ?_, fun ⟨_, _, h1, h2⟩ => ?_⟩
  · exact ⟨_, _, h1, mt ((Shape.lift_le_bot le).2 ∘ Shape.le_bot.1) h2⟩
  · exact ⟨_, _, ⟨_, _, h1, rfl, rfl⟩, mt (Shape.le_bot.2 ∘ (Shape.lift_le_bot le).1) h2⟩

theorem Shape.WF.lift_iff (le : n ≤ m) : WF (x.lift m) ↔ WF (n := n) x := by
  induction n generalizing m with | zero => cases m <;> cases x <;> trivial | succ n ih
  let m + 1 := m; replace le := Nat.le_of_succ_le_succ le; replace ih {x} := @ih m x le
  let rec go {x : ShapeFun n} : ShapeFun.WF WF (ShapeFun.lift (lift m) x) ↔ ShapeFun.WF WF x := by
    simp only [ShapeFun.WF, ShapeFun.lift, List.mem_map, Prod.mk.injEq,
      lift_eq_bot le, Prod.exists, exists_and_right, forall_exists_index, and_imp, Prod.forall]
    constructor
    · intro ⟨⟨⟨_, _, _, a1, rfl, rfl⟩, a2⟩, a3⟩; refine ⟨⟨⟨_, a1⟩, ?_⟩, fun _ _ h1 => ?_⟩
      · intro _ _ h1 _ _ h2; have := a2 _ _ _ _ h1 rfl rfl _ _ _ _ h2 rfl rfl
        simp [lift_le_lift le, Compat.lift le, ← lift_join le] at this
        refine ⟨fun h => ?_, this.2⟩
        let ⟨_, ⟨_, _, _, b1, rfl, rfl⟩, b2⟩ := this.1 h
        simp only [lift_le_lift le] at b2; exact ⟨_, ⟨_, b1⟩, b2⟩
      · simpa only [ih] using a3 _ _ _ _ h1 rfl rfl
    · intro ⟨⟨⟨_, a1⟩, a2⟩, a3⟩; refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact ⟨_, _, _, a1, rfl, rfl⟩
      · intro _ _ _ _ h1 rfl rfl _ _ _ _ h2 rfl rfl; have := a2 _ _ h1 _ _ h2
        simp [lift_le_lift le, Compat.lift le, ← lift_join le]
        refine ⟨fun h => ?_, this.2⟩
        let ⟨_, ⟨_, b1⟩, b2⟩ := this.1 h
        refine ⟨_, ⟨_, _, _, b1, rfl, rfl⟩, ?_⟩; simpa only [lift_le_lift le] using b2
      · intro _ _ _ _ h1 rfl rfl; simpa only [ih] using a3 _ _ h1
  cases x with simp [lift, WF, go, *]
  | lam => exact fun _ => ShapeFun.NonZero.lift_iff le

theorem ShapeFun.WF.lift_iff {x : ShapeFun n} (le : n ≤ m) :
    WF Shape.WF (lift (Shape.lift m) x) ↔ WF Shape.WF x :=
  Shape.WF.lift_iff.go _ _ le (Shape.WF.lift_iff le)

protected theorem Shape.WF.olift {x : Shape n} (H : x.olift (m := m) = some x') :
    WF x ↔ WF x' := by
  obtain le | le := Nat.le_total n m
  · cases olift_eq_lift le ▸ H; rw [WF.lift_iff le]
  · cases (olift_thm le).1 H; rw [WF.lift_iff le]

protected theorem ShapeFun.WF.olift {x : ShapeFun n}
    (H : olift (Shape.olift (m := m)) x = some x') : WF Shape.WF x ↔ WF Shape.WF x' := by
  obtain le | le := Nat.le_total n m
  · cases ShapeFun.olift_eq_lift le ▸ H; rw [WF.lift_iff le]
  · cases (olift_thm le).1 H; rw [WF.lift_iff le]

protected theorem Shape.WF.bot : (Shape.bot (n := n)).WF := by cases n <;> trivial
protected theorem Shape.WF.sort : (Shape.sort (n := n) r).WF := by cases n <;> trivial

protected theorem ShapeFun.WF.bot : (ShapeFun.bot (n := n)).WF Shape.WF := by
  simp [WF, bot, Shape.Compat.bot_l, Shape.bot_join, Shape.WF.bot]

/-- Well-formed shapes — the actual semantic domain. `Shape n` permits
ill-typed function graphs; `WShape n` carves out those that satisfy
`Shape.WF` (compatible domain entries, joinable codomains, …). Everything
the interpretation uses is built from `WShape`/`WShapeFun`. -/
def WShape (n : Nat) := {s : Shape n // s.WF}
/-- Well-formed function shapes. -/
def WShapeFun (n : Nat) := {s : ShapeFun n // s.WF Shape.WF}

instance : Membership (WShape n × WShape n) (WShapeFun n) := ⟨fun f a => (a.1.1, a.2.1) ∈ f.1⟩

theorem WShapeFun.mem_def {f : WShapeFun n} : a ∈ f ↔ (a.1.1, a.2.1) ∈ f.1 := .rfl

theorem WShapeFun.mem_val {f : WShapeFun n} {s t : Shape n} (h : (s, t) ∈ f.1) :
    (⟨s, (f.2.2 _ h).1⟩, ⟨t, (f.2.2 _ h).2⟩) ∈ f := h
theorem WShapeFun.mem_val' {f : WShapeFun n} {s t : Shape n} (h : (s, t) ∈ f.1) :
    ∃ hs ht, (⟨s, hs⟩, ⟨t, ht⟩) ∈ f := ⟨(f.2.2 _ h).1, (f.2.2 _ h).2, h⟩

def WShapeFun.elems (f : WShapeFun n) : List (WShape n × WShape n) :=
  f.1.pmap (fun a wf => (⟨a.1, wf.1⟩, ⟨a.2, wf.2⟩)) f.2.2

@[simp] theorem WShapeFun.mem_elems {f : WShapeFun n} : a ∈ f.elems ↔ a ∈ f := by
  simp only [elems, List.mem_pmap, Prod.exists, mem_def]
  exact ⟨fun ⟨_, _, h, rfl⟩ => h, fun h => ⟨_, _, h, rfl⟩⟩

@[ext] theorem WShape.ext {s t : WShape n} (h : s.1 = t.1) : s = t := Subtype.ext h
@[ext] theorem WShapeFun.ext {s t : WShapeFun n} (h : s.1 = t.1) : s = t := Subtype.ext h

def WShapeFun.NonZero (f : WShapeFun n) := f.1.NonZero
instance {f : WShapeFun n} : Decidable f.NonZero := inferInstanceAs (Decidable f.1.NonZero)

def WShape.bot : WShape n := ⟨.bot, .bot⟩
def WShape.sort (r : Bool) : WShape n := ⟨.sort r, .sort⟩
abbrev WShape.type : WShape n := .sort true
abbrev WShape.prop : WShape n := .sort false
def WShape.forallE (s : WShape n) (f : WShapeFun n) : WShape (n + 1) := ⟨.forallE s.1 f.1, s.2, f.2⟩
def WShape.lam (f : WShapeFun n) (h : f.NonZero) :
    WShape (n + 1) := ⟨.lam f.1, f.2, h⟩
def WShape.lam' (f : WShapeFun n) : WShape (n + 1) := if h : f.NonZero then .lam f h else .bot
theorem WShape.lam_eq_lam' {f : WShapeFun n} {hl} : WShape.lam f hl = .lam' f := by
  simp [lam', hl]

def WShapeFun.bot {n : Nat} : WShapeFun n := ⟨.bot, .bot⟩

theorem WShapeFun.NonZero.bot : ¬NonZero (n := n) .bot := by
  simp [NonZero, WShapeFun.bot, ShapeFun.bot, ShapeFun.NonZero]

@[simp] theorem WShape.lam'_bot : WShape.lam' (n := n) .bot = .bot := by
  simp [lam', WShapeFun.NonZero.bot]

theorem WShapeFun.mem_bot : (x, y) ∈ WShapeFun.bot ↔ x = .bot ∧ y = .bot := by
  simp [WShapeFun.mem_def, bot, WShape.ext_iff, WShape.bot, ShapeFun.bot]

/-- Case split on a `WShape (n+1)`. -/
@[elab_as_elim]
def WShape.casesOn' {motive : WShape (n+1) → Sort u}
    (s : WShape (n+1))
    (bot : motive .bot)
    (sort : ∀ r, motive (.sort r))
    (forallE : ∀ s f, motive (.forallE s f))
    (lam : ∀ f h, motive (.lam f h)) : motive s := by
  obtain ⟨s, wf⟩ := s
  cases s with
  | bot => exact bot
  | sort r => exact sort r
  | forallE s' f' => exact forallE ⟨s', wf.1⟩ ⟨f', wf.2⟩
  | lam f' => exact lam ⟨f', wf.1⟩ wf.2

/-- Case split on a `WShape n`. -/
@[elab_as_elim]
def WShape.casesOn {motive : ∀ {n}, WShape n → Sort u}
    {n} (s : WShape n)
    (bot : motive (n := n) .bot)
    (sort : ∀ r, motive (n := n) (.sort r))
    (forallE : ∀ {n'} s f, motive (n := n'+1) (.forallE s f))
    (lam : ∀ {n'} f h, motive (n := n'+1) (.lam f h)) : motive s := by
  cases n with
  | zero =>
    obtain ⟨s, wf⟩ := s
    cases s with
    | bot => exact bot
    | sort r => exact sort r
  | succ n => exact s.casesOn' bot sort forallE lam

def WShape.lift {n} (m) (s : WShape n) : WShape m := by
  refine ⟨(s.1.olift (m := m)).getD .bot, ?_⟩
  cases eq : s.1.olift <;> [exact .bot; exact (Shape.WF.olift eq).1 s.2]

def WShapeFun.lift {n} (m) (s : WShapeFun n) : WShapeFun m := by
  refine ⟨(ShapeFun.olift Shape.olift s.1).getD ShapeFun.bot, ?_⟩
  cases eq : ShapeFun.olift Shape.olift s.1 <;> [exact .bot; exact (ShapeFun.WF.olift eq).1 s.2]

abbrev WShape.LE (a b : WShape n) := a.1 ≤ b.1
abbrev WShapeFun.LE (a b : WShapeFun n) := a.1.LE b.1
instance : LE (WShape n) := ⟨WShape.LE⟩
instance : LE (WShapeFun n) := ⟨WShapeFun.LE⟩

instance : DecidableRel (α := WShape n) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (a.1 ≤ b.1))
theorem WShape.LE.def {a b : WShape n} : a ≤ b ↔ a.1 ≤ b.1 := .rfl
theorem WShapeFun.LE.def {a b : WShapeFun n} : a ≤ b ↔ a.1.LE b.1 := .rfl

theorem WShape.lift_val {s : WShape n} (le : n ≤ m) : (s.lift m).1 = s.1.lift m := by
  simp [lift, Shape.olift_eq_lift le]

theorem WShapeFun.lift_val {s : WShapeFun n} (le : n ≤ m) :
    (s.lift m).1 = ShapeFun.lift (Shape.lift m) s.1 := by
  simp [lift, ShapeFun.olift_eq_lift le]

theorem WShapeFun.mem_lift {s : WShapeFun n} (le : n ≤ m) :
    (x, x') ∈ s.lift m ↔ ∃ y y', (y, y') ∈ s ∧ x = y.lift m ∧ x' = y'.lift m := by
  cases x; cases x'
  simp [mem_def, lift_val le, WShape.lift_val le, ShapeFun.lift, WShape.ext_iff]
  constructor <;> exact fun ⟨_, _, h1, h2, h3⟩ => ⟨_, _, s.mem_val h1, h2.symm, h3.symm⟩

theorem WShape.forallE.inj {f : WShapeFun n} :
    WShape.forallE a f = WShape.forallE a' f' ↔ a = a' ∧ f = f' := by
  simp [WShape.ext_iff, WShapeFun.ext_iff, forallE]
  exact iff_of_eq (ShapeS.forallE.injEq ..)

@[simp] theorem WShape.lift_bot : (WShape.bot : WShape n).lift m = .bot := by
  ext; simp [lift, bot]

@[simp] theorem WShapeFun.lift_bot : WShapeFun.lift (n := n) m .bot = .bot := by
  ext1; simp [WShapeFun.lift, bot, ShapeFun.olift_bot]

@[simp] theorem WShape.lift_sort : (WShape.sort r : WShape n).lift m = .sort r := by
  ext; simp [lift, sort]

@[simp] theorem WShape.lift_type : (WShape.type (n := n)).lift m = WShape.type := WShape.lift_sort

theorem WShape.lift_self {s : WShape n} : s.lift n = s := by
  ext; rw [lift_val (Nat.le_refl _), Shape.lift_self]

theorem WShape.lift_lift {s : WShape n₁} (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) :
    (s.lift n₂).lift n₃ = s.lift n₃ := by
  ext; simp [lift]
  by_cases h1 : n₁ ≤ n₂
  · congr 1; ext t; rw [Shape.olift_eq_lift h1, Option.getD]
    obtain h2 | h2 := Nat.le_total n₂ n₃
    · rw [Shape.olift_eq_lift h2, Shape.lift_lift (.inl h1),
        Shape.olift_eq_lift (Nat.le_trans h1 h2)]
    rw [Shape.olift_thm h2]
    obtain h3 | h3 := Nat.le_total n₁ n₃
    · rw [Shape.olift_eq_lift h3, Option.some_inj, ← Shape.lift_lift (.inl h3), Shape.lift_inj h2]
    · rw [Shape.olift_thm h3, ← Shape.lift_lift (.inl h3), Shape.lift_inj h1]
  · have h2 := le.resolve_left h1; have h1 := Nat.le_of_not_ge h1
    cases eq : s.1.olift (m := n₂) <;> simp
    · cases eq' : s.1.olift (m := n₃) <;> simp
      rw [Shape.olift_thm (Nat.le_trans h2 h1), ← Shape.lift_lift (.inl h2),
        ← Shape.olift_thm h1, eq] at eq'; cases eq'
    · rw [(Shape.olift_thm h1).1 eq]; rename_i t
      cases eq₁ : t.olift
      · cases eq₂ : (Shape.lift n₁ t).olift; · rfl
        rw [Shape.olift_thm (Nat.le_trans h2 h1), ← Shape.lift_lift (.inl h2)] at eq₂
        rw [(Shape.lift_inj h1).1 eq₂, (Shape.olift_thm h2).2 rfl] at eq₁; cases eq₁
      · rw [(Shape.olift_thm h2).1 eq₁, Shape.lift_lift (.inl h2),
          (Shape.olift_thm (Nat.le_trans h2 h1)).2 rfl]

theorem WShapeFun.lift_lift {s : WShapeFun n₁} (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) :
    (s.lift n₂).lift n₃ = s.lift n₃ := by
  ext1; simp [lift]
  by_cases h1 : n₁ ≤ n₂
  · congr 1; ext t; rw [ShapeFun.olift_eq_lift h1, Option.getD]
    obtain h2 | h2 := Nat.le_total n₂ n₃
    · rw [ShapeFun.olift_eq_lift h2, ShapeFun.lift_lift (.inl h1),
        ShapeFun.olift_eq_lift (Nat.le_trans h1 h2)]
    rw [ShapeFun.olift_thm h2]
    obtain h3 | h3 := Nat.le_total n₁ n₃
    · rw [ShapeFun.olift_eq_lift h3, Option.some_inj, ← ShapeFun.lift_lift (.inl h3),
        ShapeFun.lift_inj h2]
    · rw [ShapeFun.olift_thm h3, ← ShapeFun.lift_lift (.inl h3), ShapeFun.lift_inj h1]
  · have h2 := le.resolve_left h1; have h1 := Nat.le_of_not_ge h1
    cases eq : ShapeFun.olift (Shape.olift (m := n₂)) s.1 <;> simp
    · cases eq' : ShapeFun.olift (Shape.olift (m := n₃)) s.1 <;> simp
      rw [ShapeFun.olift_thm (Nat.le_trans h2 h1), ← ShapeFun.lift_lift (.inl h2),
        ← ShapeFun.olift_thm h1, eq] at eq'; cases eq'
    · rw [(ShapeFun.olift_thm h1).1 eq]; rename_i t
      cases eq₁ : ShapeFun.olift Shape.olift t
      · cases eq₂ : ShapeFun.olift Shape.olift (ShapeFun.lift (Shape.lift n₁) t); · rfl
        rw [ShapeFun.olift_thm (Nat.le_trans h2 h1), ← ShapeFun.lift_lift (.inl h2)] at eq₂
        rw [(ShapeFun.lift_inj h1).1 eq₂, (ShapeFun.olift_thm h2).2 rfl] at eq₁; cases eq₁
      · rw [(ShapeFun.olift_thm h2).1 eq₁, ShapeFun.lift_lift (.inl h2),
          (ShapeFun.olift_thm (Nat.le_trans h2 h1)).2 rfl]

theorem WShape.lift_le_lift {s t : WShape n} (le : n ≤ m) :
    s.lift m ≤ t.lift m ↔ s ≤ t := by
  show (s.lift m).1 ≤ (t.lift m).1 ↔ s.1 ≤ t.1
  rw [lift_val le, lift_val le]; exact Shape.lift_le_lift le

theorem WShapeFun.lift_le_lift {s t : WShapeFun n} (le : n ≤ m) :
    s.lift m ≤ t.lift m ↔ s ≤ t := by
  show (s.lift m).1.LE (t.lift m).1 ↔ s.1.LE t.1
  rw [lift_val le, lift_val le]; exact ShapeFun.lift_le_lift le

theorem WShapeFun.lift_mono {s t : WShapeFun n} (le : n ≤ m) (h : s ≤ t) : s.lift m ≤ t.lift m :=
  (lift_le_lift le).2 h

theorem WShapeFun.LE.def' {f f' : WShapeFun n} : f ≤ f' ↔
    ∀ x y : WShape n, (x, y) ∈ f → ∃ x' y' : WShape n, (x', y') ∈ f' ∧ x' ≤ x ∧ y ≤ y' := by
  simp [(· ≤ ·), ShapeFun.LE.def]
  constructor <;> intro H x y h1
  · have ⟨_, _, h2, h3⟩ := H _ _ h1
    exact ⟨⟨_, (f'.2.2 _ h2).1⟩, ⟨_, (f'.2.2 _ h2).2⟩, h2, h3⟩
  · have ⟨x', y', h2, h3⟩ := H ⟨_, (f.2.2 _ h1).1⟩ ⟨_, (f.2.2 _ h1).2⟩ h1
    exact ⟨_, _, h2, h3⟩

theorem WShape.lift_mono {s t : WShape n} (le : n ≤ m) : s ≤ t → s.lift m ≤ t.lift m :=
  (lift_le_lift le).2

theorem WShape.lift_le_bot {s : WShape n} (h : n ≤ m) : s.lift m ≤ .bot ↔ s = .bot := by
  rw [← WShape.lift_bot (n := n), WShape.lift_le_lift h]
  exact ⟨fun h => WShape.ext (Shape.le_bot.1 h), fun h => h ▸ Shape.LE.rfl⟩

theorem WShape.lift_eq_bot {s : WShape n} (h : n ≤ m) : s.lift m = .bot ↔ s = .bot := by
  exact ⟨fun h' => (lift_le_bot h).1 (h' ▸ Shape.LE.rfl), fun h' => h' ▸ lift_bot⟩

theorem WShape.le_bot {s : WShape n} : s ≤ .bot ↔ s = .bot :=
  Shape.le_bot.trans (Subtype.ext_iff (a1 := s) (a2 := WShape.bot)).symm

@[simp] theorem WShape.lift_forallE {s : WShape n} {f : WShapeFun n} (h : n ≤ m) :
    (WShape.forallE s f).lift (m+1) = .forallE (s.lift m) (f.lift m) := by
  ext; simp [lift_val (Nat.succ_le_succ h), Shape.lift, WShape.forallE,
    lift_val h, WShapeFun.lift_val h]

theorem WShapeFun.NonZero.lift_iff {n m} {x : WShapeFun n} (le : n ≤ m) :
    (x.lift m).NonZero ↔ NonZero (n := n) x := by
  simp [NonZero, lift_val le, ShapeFun.NonZero.lift_iff le]

@[simp] theorem WShape.lift_lam' {f : WShapeFun n} (le : n ≤ m) :
    (WShape.lam' f).lift (m+1) = .lam' (f.lift m) := by
  ext1; simp [lam']; split <;> simp [WShapeFun.lift_val le, WShapeFun.NonZero.lift_iff le,
    lift_val (Nat.succ_le_succ le), lam, Shape.lift, *]

theorem WShape.lift_lam {f : WShapeFun n} {hl} (h : n ≤ m) :
    (WShape.lam f hl).lift (m+1) = .lam (f.lift m) ((WShapeFun.NonZero.lift_iff h).2 hl) := by
  ext1; simp [WShape.lift_val (Nat.succ_le_succ h), lam, WShapeFun.lift_val h, Shape.lift]

theorem WShape.lift_eq_lam' {s : WShape (n+1)} (le : n ≤ m)
    {f : WShapeFun m} (eq : s.lift (m+1) = .lam' f) :
    s = .bot ∧ f ≤ .bot ∨ ∃ f' : WShapeFun n, s = .lam' f' ∧ f = f'.lift m := by
  obtain ⟨f, hf⟩ := f
  have eq := congrArg (·.1) eq; simp [lift_val (Nat.succ_le_succ le)] at eq
  unfold lam' at eq; split at eq <;> rename_i h <;>
    obtain ⟨⟨⟩, wf⟩ := s <;> simp [lam, Shape.lift] at eq <;> cases eq
  · refine .inr ⟨⟨_, wf.1⟩, ?_⟩; rw [lam', dif_pos (by exact (ShapeFun.NonZero.lift_iff le).1 h)]
    exact ⟨rfl, WShapeFun.ext (WShapeFun.lift_val le ▸ rfl)⟩
  · refine .inl ⟨rfl, WShapeFun.LE.def'.2 fun x y h => ?_⟩; rename_i hn
    refine ⟨_, _, WShapeFun.mem_bot.2 ⟨rfl, rfl⟩, Shape.bot_le, Decidable.by_contra (hn ⟨_, h, ·⟩)⟩

@[simp] theorem WShape.bot_le : WShape.bot ≤ (s : WShape n) := Shape.bot_le

protected theorem WShape.LE.rfl {s : WShape n} : s ≤ s := Shape.LE.rfl
protected theorem WShape.LE.trans {s t u : WShape n} : s ≤ t → t ≤ u → s ≤ u := Shape.LE.trans

@[simp] theorem WShape.forallE_le_forallE {a a' : WShape n} {f f' : WShapeFun n} :
    WShape.forallE a f ≤ .forallE a' f' ↔ a ≤ a' ∧ f ≤ f' := Shape.forallE_le_forallE

theorem WShape.le_forallE_iff {s : WShape (n+1)} {a' : WShape n} {f' : WShapeFun n} :
    s ≤ .forallE a' f' ↔ s = .bot ∨ ∃ a f, s = .forallE a f ∧ a ≤ a' ∧ f ≤ f' := by
  constructor
  · cases s using WShape.casesOn' with
    | bot => exact fun _ => .inl rfl
    | forallE a f => exact fun h => .inr ⟨a, f, rfl, forallE_le_forallE.1 h⟩
      | _ => simp only [sort, lam, forallE, LE.def, Shape.LE.def, false_implies]
  · rintro (rfl | ⟨a, f, rfl, h1, h2⟩)
    · exact bot_le
    · exact forallE_le_forallE.2 ⟨h1, h2⟩

theorem WShape.le_sort {s : WShape n} : s ≤ .sort r ↔ s = .bot ∨ s = .sort r :=
  Shape.le_sort.trans <| by simp [WShape.ext_iff, WShape.bot, WShape.sort]

theorem WShape.sort_le {s : WShape n} : .sort r ≤ s ↔ .sort r = s :=
  Shape.sort_le.trans <| by simp [WShape.ext_iff, WShape.sort]

theorem WShape.forallE_le {s : WShape (n+1)} {a : WShape n} {f : WShapeFun n} :
    WShape.forallE a f ≤ s ↔
      ∃ a' : WShape n, ∃ f' : WShapeFun n, a ≤ a' ∧ f ≤ f' ∧ s = .forallE a' f' := by
  constructor
  · intro h
    have ⟨a', b', h1, h2, h3⟩ := Shape.forallE_le.1 h
    have wf := h3 ▸ s.2
    exact ⟨⟨a', wf.1⟩, ⟨b', wf.2⟩, h1, h2, WShape.ext h3.symm⟩
  · intro ⟨a', f', h1, h2, h3⟩; subst h3; exact WShape.forallE_le_forallE.2 ⟨h1, h2⟩

theorem WShape.lam'_le_lam' {f f' : WShapeFun n} :
    WShape.lam' f ≤ .lam' f' ↔ f ≤ f' := by
  simp [WShape.LE.def, lam', WShapeFun.LE.def]
  split <;> [split <;> rename_i h h'; rename_i h] <;> simp [lam, bot, Shape.LE.def, ShapeFun.LE.def]
  · let ⟨_, h1, h2⟩ := h
    refine ⟨_, _, h1, fun _ _ h3 h4 h5 => h' ⟨_, h3, mt h5.trans h2⟩⟩
  · intro _ y h1; have h2 := Decidable.by_contra (mt (⟨_, h1, ·⟩) h)
    have ⟨_, h⟩ := f'.2.1.1; exact ⟨_, _, h, Shape.bot_le, .trans h2 Shape.bot_le⟩

theorem WShapeFun.bot_mem (f : WShapeFun n) : ∃ y, (.bot, y) ∈ f :=
  let ⟨_, h⟩ := f.2.1.1; ⟨_, f.mem_val h⟩

@[simp] theorem WShapeFun.bot_le {f : WShapeFun n} : bot ≤ f := by
  simp [LE.def', mem_bot, WShape.le_bot, and_left_comm, WShape.bot_le, f.bot_mem]

def WShape.Compat (a b : WShape n) : Prop := a.1.Compat b.1
def WShapeFun.Compat (a b : WShapeFun n) : Prop := ShapeFun.Compat Shape.Compat a.1 b.1
instance : Decidable (WShape.Compat a b) := inferInstanceAs (Decidable (_ = true))
instance : Decidable (WShapeFun.Compat a b) := inferInstanceAs (Decidable (_ = true))

@[simp] theorem WShape.Compat.bot_l {n} {s : WShape n} : bot.Compat s := Shape.Compat.bot_l
@[simp] theorem WShape.Compat.bot_r {n} {s : WShape n} : s.Compat bot := Shape.Compat.bot_r
@[simp] theorem WShape.Compat.sort_sort : Compat (sort r : WShape n) (sort r') ↔ r = r' :=
  Shape.Compat.sort_sort

@[simp] theorem WShape.Compat.forallE_forallE {a a' : WShape n} {f f' : WShapeFun n} :
    (WShape.forallE a f).Compat (.forallE a' f') ↔ a.Compat a' ∧ WShapeFun.Compat f f' :=
  Shape.Compat.forallE_forallE

theorem WShapeFun.Compat.def {n} {f f' : WShapeFun n} :
    f.Compat f' ↔ ∀ x ∈ f, ∀ y ∈ f', x.1.Compat y.1 → x.2.Compat y.2 := by
  simp [Compat, ShapeFun.Compat.def]
  constructor <;> intro H _ _ h1 _ _ h2
  · exact H _ _ h1 _ _ h2
  · exact H _ _ (f.mem_val h1) _ _ (f'.mem_val h2)

theorem WShapeFun.join_mem' {f : WShapeFun n}
    (hx : (x, y) ∈ f) (hy : (x', y') ∈ f) (hc : x.Compat x') :
    ∃ z, z ∈ f ∧ x.1.join x'.1 ≤ z.1.1 ∧ z.1.1 ≤ x.1.join x'.1 := by
  let ⟨_, h1, h2⟩ := (f.2.1.2 _ (f.mem_val hx) _ (f.mem_val hy)).1 hc
  exact ⟨_, f.mem_val h1, h2⟩

theorem WShapeFun.mem_mono {f : WShapeFun n}
    (hx : (x, y) ∈ f) (hy : (x', y') ∈ f) : x ≤ x' → y ≤ y' :=
  (f.2.1.2 _ (f.mem_val hx) _ (f.mem_val hy)).2

protected theorem WShape.Compat.lift {x y : WShape n} (le : n ≤ m) :
    (x.lift m).Compat (y.lift m) ↔ x.Compat y := by
  simp [WShape.Compat, lift_val le, Shape.Compat.lift le]

theorem ShapeFun.mem_trunc {f : ShapeFun n} : x ∈ f.trunc a ↔ x ∈ f ∧ x.1 ≤ a := by simp [trunc]

namespace WShape.join_prop
variable (ih : ∀ {x y : WShape n}, (∀ z, x ≤ z → y ≤ z → x.Compat y) ∧
  (x.Compat y → (x.1.join y.1).WF ∧ ∀ z, x.1.join y.1 ≤ z.1 ↔ x ≤ z ∧ y ≤ z))
include ih

theorem exists_max {f : WShapeFun n}
    (hc : ∀ x ∈ f, ∀ y ∈ f, x.1.Compat y.1) : ∃ x ∈ f.1, ∀ x' ∈ f.1, x'.1 ≤ x.1 := by
  suffices ∀ l : ShapeFun n, (∀ x ∈ l, x ∈ f.1) → ∃ x ∈ f.1, ∀ x' ∈ l, x'.1 ≤ x.1 from
    have ⟨_, h1, h2⟩ := this _ fun _ => id; ⟨_, f.mem_val h1, fun _ => h2 _⟩
  intro l hl; induction l with
  | nil => let ⟨_, h⟩ := f.2.1.1; exact ⟨_, h, nofun⟩
  | cons a l ihl =>
    have ⟨hm, hl⟩ := List.forall_mem_cons.1 hl
    have ⟨x, h1, h2⟩ := ihl hl
    have := hc _ (f.mem_val hm) _ (f.mem_val h1)
    have ⟨_, a1, a2⟩ := f.join_mem' (f.mem_val hm) (f.mem_val h1) this
    have ⟨b1, b2⟩ := ((ih.2 this).2 ⟨_, (f.2.2 _ a1).1⟩).1 a2.1
    exact ⟨_, a1, List.forall_mem_cons.2 ⟨b1, fun _ h => (h2 _ h).trans b2⟩⟩

def wf_trunc (f : WShapeFun n) (a : WShape n) : WShapeFun n := by
  refine ⟨f.1.trunc a.1, ?_, fun _ h1 => f.2.2 _ (ShapeFun.mem_trunc.1 h1).1⟩
  simp [ShapeFun.trunc]
  refine ⟨f.2.1.1, fun _ _ h1 h2 _ _ h3 h4 => ?_⟩
  have ⟨a1, a2, h1⟩ := f.mem_val' h1; have ⟨b1, b2, h3⟩ := f.mem_val' h3
  have ⟨a3, a4⟩ := f.2.1.2 _ h1 _ h3; refine ⟨fun h => ?_, a4⟩
  have ⟨⟨z, z'⟩, a5, a6⟩ := a3 h
  refine ⟨_, ⟨⟨_, a5⟩, a6.2.trans ?_⟩, a6⟩
  exact (ih.2 <| (@ih ⟨_, a1⟩ ⟨_, b1⟩).1 _ h2 h4).2 _ |>.2 ⟨h2, h4⟩

theorem trunc_compat (f : WShapeFun n) (a : WShape n)
    {{x}} (h1 : x ∈ wf_trunc ih f a) {{y}} (h2 : y ∈ wf_trunc ih f a) : x.1.Compat y.1 :=
  have ⟨a1, a2⟩ := ShapeFun.mem_trunc.1 h1
  have ⟨b1, b2⟩ := ShapeFun.mem_trunc.1 h2
  (@ih ⟨_, (f.2.2 _ a1).1⟩ ⟨_, (f.2.2 _ b1).1⟩).1 a a2 b2

theorem app_core (f : WShapeFun n) (x : WShape n) :
    ∃ x', x' ≤ x.1 ∧ (x', f.1.app x.1) ∈ f.1 ∧ ∀ y ∈ f.1, y.1 ≤ x.1 → y.2 ≤ f.1.app x.1 := by
  simp only [ShapeFun.app, ShapeFun.maxBelow]
  have ⟨_, h1, h2⟩ := exists_max ih (trunc_compat ih f x)
  simp [wf_trunc, ShapeFun.mem_trunc] at h1 h2
  show let P := _; ∃ x', x' ≤ x.1 ∧ let y' := ((List.find? P _).getD (Shape.bot, Shape.bot)).snd
    (x', y') ∈ f.1 ∧ ∀ y ∈ f.1, y.1 ≤ x.1 → y.2 ≤ y'
  intro P
  have ⟨⟨x', y'⟩, h⟩ := Option.isSome_iff_exists.1 <|
    (List.find?_isSome (p := P)).2 ⟨_, ShapeFun.mem_trunc.2 h1, by simpa [P, ShapeFun.mem_trunc]⟩
  have := List.find?_some h; simp [P, ShapeFun.mem_trunc, h] at this ⊢
  have ⟨h1, h2⟩ := ShapeFun.mem_trunc.1 <| List.mem_of_find?_eq_some h
  exact ⟨_, h2, h1, fun _ _ a1 a2 => (f.2.1.2 _ a1 _ h1).2 (this _ _ a1 a2)⟩

theorem of_compat {x x' : WShape n} (hc : x.Compat x') :
    ∃ j : WShape n, j.1 = x.1.join x'.1 ∧ ∀ w, j ≤ w ↔ x ≤ w ∧ x' ≤ w :=
  ⟨⟨_, (ih.2 hc).1⟩, rfl, (ih.2 hc).2⟩

theorem join_mem' {f : WShapeFun n} {x y x' y'}
    (hx : (x, y) ∈ f) (hy : (x', y') ∈ f) (hc : x.Compat x') :
    ∃ j : WShape n, j.1 = x.1.join x'.1 ∧ ∃ z, z ∈ f ∧ j ≤ z.1 ∧ z.1 ≤ j ∧
      ∀ w, j ≤ w ↔ x ≤ w ∧ x' ≤ w :=
  let ⟨_, a1, a2, a3⟩ := f.join_mem' hx hy hc
  ⟨⟨_, (ih.2 hc).1⟩, rfl, _, a1, a2, a3, (ih.2 hc).2⟩

theorem compat_app_l {f f' : WShapeFun n} (hc : f.Compat f') (x : WShape n) :
    (f.1.app x.1).Compat (f'.1.app x.1) := by
  have ⟨_, a1, a2, _⟩ := app_core ih f x; have ⟨a4, a5, a2⟩ := f.mem_val' a2
  have ⟨_, b1, b2, _⟩ := app_core ih f' x; have ⟨b4, b5, b2⟩ := f'.mem_val' b2
  exact (ShapeFun.Compat.def.1 hc _ a2 _ b2 ((@ih ⟨_, a4⟩ ⟨_, b4⟩).1 _ a1 b1) :)

theorem ih_fun {f f' : WShapeFun n} :
    (∀ z, f ≤ z → f' ≤ z → f.Compat f') ∧
    (f.Compat f' → ∃ h, ∀ z, ⟨ShapeFun.join Shape.join f.1 f'.1, h⟩ ≤ z ↔ f ≤ z ∧ f' ≤ z) := by
  simp only [WShapeFun.LE.def']
  refine ⟨fun z le₁ le₂ => ShapeFun.Compat.def.2 fun _ h1 _ h2 h => ?_, fun hc => ?_⟩
  · have ⟨_, _, a1, a2, a3⟩ := le₁ _ _ (f.mem_val h1)
    have ⟨_, _, b1, b2, b3⟩ := le₂ _ _ (f'.mem_val h2)
    have h := Shape.Compat.mono a2 b2 h
    refine Shape.Compat.mono a3 b3 ?_
    have ⟨_, c1, c2, c3⟩ := z.join_mem' a1 b1 h
    have ⟨e1, e2⟩ := ((ih.2 h).2 _).1 c2
    exact ih.1 _ (z.mem_mono a1 c1 e1) (z.mem_mono b1 c1 e2)
  simp only [ShapeFun.WF, ShapeFun.mem_join]
  refine ⟨⟨⟨?_, ?_⟩, fun a => ?_⟩, ?_⟩
  · let ⟨_, a1⟩ := f.bot_mem; let ⟨_, a2⟩ := f'.bot_mem
    refine ⟨_, _, a1, _, a2, Compat.bot_l, cast (Prod.mk.injEq ..).symm ⟨.symm ?_, rfl⟩⟩
    exact Shape.le_bot.1 <| ((ih.2 .bot_l).2 _).2 ⟨.rfl, .rfl⟩
  · rintro _ ⟨x, a1, x', a2, a3, rfl⟩ _ ⟨y, b1, y', b2, b3, rfl⟩
    replace a1 := f.mem_val a1; replace a2 := f'.mem_val a2
    replace b1 := f.mem_val b1; replace b2 := f'.mem_val b2
    change Compat ⟨x.1, (f.2.2 _ a1).1⟩ ⟨x'.1, (f'.2.2 _ a2).1⟩ at a3
    change Compat ⟨y.1, (f.2.2 _ b1).1⟩ ⟨y'.1, (f'.2.2 _ b2).1⟩ at b3
    dsimp only
    have ⟨a, a5, a6⟩ := of_compat ih a3; have ⟨a31, a32⟩ := (a6 _).1 .rfl; have ac := ih.1 _ a31 a32
    have ⟨b, b5, b6⟩ := of_compat ih b3; have ⟨b31, b32⟩ := (b6 _).1 .rfl; have bc := ih.1 _ b31 b32
    refine ⟨fun h1 => ?_, fun h1 => a5 ▸ b5 ▸ ?_⟩
    · have h1' : a.Compat b := by simp [Compat, a5, b5, h1]
      have ⟨c, c1, c2⟩ := of_compat ih h1'; have ⟨c3, c4⟩ := (c2 _).1 .rfl
      have dc := ih.1 _ (a31.trans c3) (b31.trans c4)
      have ⟨d, d1, d', d2, d3, d4, d5⟩ := join_mem' ih a1 b1 dc; have ⟨d6, d7⟩ := (d5 _).1 .rfl
      have ec := ih.1 _ (a32.trans c3) (b32.trans c4)
      have ⟨e, e1, e', e2, e3, e4, e5⟩ := join_mem' ih a2 b2 ec; have ⟨e6, e7⟩ := (e5 _).1 .rfl
      have h4 := d4.trans <| (d5 _).2 ⟨a31.trans c3, b31.trans c4⟩
      have h5 := e4.trans <| (e5 _).2 ⟨a32.trans c3, b32.trans c4⟩
      have hc := ih.1 _ h4 h5
      have ⟨j, j1, j2⟩ := of_compat ih hc; have ⟨j3, j4⟩ := (j2 _).1 .rfl
      refine ⟨_, ⟨_, d2, _, e2, hc, rfl⟩, j1 ▸ a5 ▸ b5 ▸ c1 ▸ ?_⟩; dsimp only
      refine ⟨(c2 _).2 ⟨?_, ?_⟩, (j2 _).2 ⟨h4, h5⟩⟩
      · exact (a6 _).2 ⟨d6.trans (d3.trans j3), e6.trans (e3.trans j4)⟩
      · exact (b6 _).2 ⟨d7.trans (d3.trans j3), e7.trans (e3.trans j4)⟩
    · have ⟨_, c1, c2, _⟩ := app_core ih f a; have ⟨c3, c4, c2⟩ := f.mem_val' c2
      have ⟨_, d1, d2, _⟩ := app_core ih f' a; have ⟨d3, d4, d2⟩ := f'.mem_val' d2
      have ⟨_, f1, f2, cf⟩ := app_core ih f b; have ⟨f3, f4, f2⟩ := f.mem_val' f2
      have ⟨_, g1, g2, dg⟩ := app_core ih f' b; have ⟨g3, g4, g2⟩ := f'.mem_val' g2
      have ⟨e, e1, e2⟩ := of_compat ih (x := ⟨_, c4⟩) (x' := ⟨_, d4⟩) (compat_app_l ih hc a)
      have ⟨k, k1, k2⟩ := of_compat ih (x := ⟨_, f4⟩) (x' := ⟨_, g4⟩) (compat_app_l ih hc b)
      refine e1 ▸ k1 ▸ (e2 _).2 ⟨?_, ?_⟩
      · exact (cf _ c2 (c1.trans (a5 ▸ b5 ▸ h1))).trans ((k2 _).1 .rfl).1
      · exact (dg _ d2 (d1.trans (a5 ▸ b5 ▸ h1))).trans ((k2 _).1 .rfl).2
  · rintro ⟨b, b3, c, c3, a1, rfl⟩
    have ⟨b1, b2, b3⟩ := f.mem_val' b3; have ⟨c1, c2, c3⟩ := f'.mem_val' c3
    have ⟨d, d1, d2⟩ := of_compat ih (x := ⟨_, b1⟩) (x' := ⟨_, c1⟩) a1
    have ⟨_, f1, f2, cf⟩ := app_core ih f d; have ⟨f3, f4, f2⟩ := f.mem_val' f2
    have ⟨_, g1, g2, dg⟩ := app_core ih f' d; have ⟨g3, g4, g2⟩ := f'.mem_val' g2
    have ⟨e, e1, e2⟩ := of_compat ih (x := ⟨_, f4⟩) (x' := ⟨_, g4⟩) (compat_app_l ih hc d)
    refine d1 ▸ e1 ▸ ⟨d.2, e.2⟩
  · intro f₃; conv => enter [1,x,y,1]; simp only [WShapeFun.mem_def, ShapeFun.mem_join]
    refine ⟨fun H => ?_, fun ⟨H1, H2⟩ => ?_⟩
    · refine ⟨fun x y hf => ?_, fun x y hf' => ?_⟩
      · have ⟨_, hf'⟩ := f'.bot_mem
        have ⟨_, f1, f2, cf⟩ := app_core ih f x; have ⟨f3, f4, f2⟩ := f.mem_val' f2
        have ⟨_, g1, g2, dg⟩ := app_core ih f' x; have ⟨g3, g4, g2⟩ := f'.mem_val' g2
        have ⟨e, e1, e2⟩ := of_compat ih (x := ⟨_, f4⟩) (x' := ⟨_, g4⟩) (compat_app_l ih hc x)
        have ⟨c₁, c₂, c1, c2, c3⟩ := H ⟨_, Shape.join_bot ▸ x.2⟩ ⟨_, Shape.join_bot ▸ e1 ▸ e.2⟩
          ⟨_, hf, _, hf', Compat.bot_r, rfl⟩
        simp only [bot, Shape.join_bot] at c2 c3
        refine ⟨_, _, c1, c2, .trans ?_ c3⟩
        exact (cf _ hf .rfl).trans (e1 ▸ (show _ ≤ e.1 from ((e2 _).1 .rfl).1) :)
      · have ⟨_, hf⟩ := f.bot_mem
        have ⟨_, f1, f2, cf⟩ := app_core ih f x; have ⟨f3, f4, f2⟩ := f.mem_val' f2
        have ⟨_, g1, g2, dg⟩ := app_core ih f' x; have ⟨g3, g4, g2⟩ := f'.mem_val' g2
        have ⟨e, e1, e2⟩ := of_compat ih (x := ⟨_, f4⟩) (x' := ⟨_, g4⟩) (compat_app_l ih hc x)
        have ⟨c₁, c₂, c1, c2, c3⟩ := H ⟨_, Shape.bot_join ▸ x.2⟩ ⟨_, Shape.bot_join ▸ e1 ▸ e.2⟩
          ⟨_, hf, _, hf', Compat.bot_l, rfl⟩
        simp only [bot, Shape.bot_join] at c2 c3
        refine ⟨_, _, c1, c2, .trans ?_ c3⟩
        exact (dg _ hf' .rfl).trans (e1 ▸ (show _ ≤ e.1 from ((e2 _).1 .rfl).2) :)
    · rintro ⟨_, hx⟩ ⟨_, hy⟩ ⟨x, a3, y, b3, xy, ⟨⟩⟩
      have ⟨a1, a2, a3⟩ := f.mem_val' a3; have ⟨b1, b2, b3⟩ := f'.mem_val' b3
      have ⟨e, e1, e2⟩ := of_compat ih (x := ⟨_, a1⟩) (x' := ⟨_, b1⟩) xy
      have ⟨f₁, f1, f2, cf⟩ := app_core ih f e; have ⟨f3, f4, f2⟩ := f.mem_val' f2
      have ⟨g₁, g1, g2, dg⟩ := app_core ih f' e; have ⟨g3, g4, g2⟩ := f'.mem_val' g2
      have ⟨i, i1, i2, hi⟩ := app_core ih f₃ e; have ⟨i3, i4, i2⟩ := f₃.mem_val' i2
      have ⟨j, j1, j2⟩ := of_compat ih (x := ⟨_, f4⟩) (x' := ⟨_, g4⟩) (compat_app_l ih hc e)
      have ⟨l1, l2⟩ := (e2 _).1 .rfl
      refine ⟨_, _, i2, (e1 ▸ i1 :), ?_⟩
      simp only [WShape.LE.def, ← e1, ← j1]
      refine (j2 ⟨_, i4⟩).2 ⟨?_, ?_⟩
      · have ⟨m, m', m1, m2, m3⟩ := H1 _ _ f2; exact m3.trans (hi _ m1 (m2.trans f1))
      · have ⟨m, m', m1, m2, m3⟩ := H2 _ _ g2; exact m3.trans (hi _ m1 (m2.trans g1))

end WShape.join_prop

theorem WShape.join_prop {x y : WShape n} :
    (∀ z, x ≤ z → y ≤ z → x.Compat y) ∧
    (x.Compat y → (x.1.join y.1).WF ∧ ∀ z, x.1.join y.1 ≤ z.1 ↔ x ≤ z ∧ y ≤ z) := by
  induction n with
  | zero =>
    obtain ⟨⟨⟩, wf⟩ := x <;> obtain ⟨⟨⟩, _⟩ := y <;>
      simp +contextual [(·≤·), Compat, Shape.LE, Shape.ble, Shape.Compat, Shape.join, *]
    refine ⟨?_, (· ▸ ⟨wf, ?_⟩)⟩ <;> rintro ⟨⟨⟩⟩ <;> simp [Shape.ble]
    exact (·.trans ·.symm)
  | succ n ih
  have go {f f' : ShapeFun n} (wf : ShapeFun.WF Shape.WF f) (wf' : ShapeFun.WF Shape.WF f') :=
    @join_prop.ih_fun _ @ih ⟨f, wf⟩ ⟨f', wf'⟩
  let ⟨x, wf⟩ := x; let ⟨y, wf'⟩ := y
  simp only [WShape.LE.def]; simp [WShape, Compat]
  constructor
  · (cases x with | bot => exact fun _ _ _ _ => Shape.Compat.bot_l | _) <;>
    rintro ⟨⟩ wf₃ h2 h3 <;> simp [Shape.LE.def] at h2 <;>
    (cases y with | bot => exact Shape.Compat.bot_r | _) <;>
    simp [Shape.LE.def, Shape.Compat] at h3 ⊢ <;> dsimp [Shape.WF] at wf wf' wf₃
    · exact h2.trans h3.symm
    · exact ⟨(@ih ⟨_, wf.1⟩ ⟨_, wf'.1⟩).1 ⟨_, wf₃.1⟩ h2.1 h3.1,
        (go wf.2 wf'.2).1 ⟨_, wf₃.2⟩ h2.2 h3.2⟩
    · exact (go wf.1 wf'.1).1 ⟨_, wf₃.1⟩ h2 h3
  · (cases x with | bot => intro; exact ⟨wf', fun _ _ => (and_iff_right Shape.bot_le).symm⟩ | _) <;>
    (cases y with | bot => intro; exact ⟨wf, fun _ _ => (and_iff_left Shape.bot_le).symm⟩ | _) <;>
    simp [Shape.WF] at wf wf' <;>
    simp +contextual [Shape.Compat, Shape.join, Shape.sort, Shape.LE.def, Shape.WF]
    · intro h1 h2
      have ⟨a1, a2⟩ := (@ih ⟨_, wf.1⟩ ⟨_, wf'.1⟩).2 h1
      have ⟨b1, b2⟩ := (go wf.2 wf'.2).2 h2
      simp only [WShape.LE.def, WShapeFun.LE.def] at a1 a2 b1 b2
      simp [WShape, WShapeFun] at a2 b2 ⊢
      refine ⟨⟨a1, b1⟩, ?_⟩
      rintro ⟨⟨⟩⟩ <;> simp +contextual [Shape.WF, and_assoc, and_left_comm, *]
    · intro h1
      have ⟨a1, a2⟩ := (go wf.1 wf'.1).2 h1
      simp only [WShapeFun.LE.def] at a1 a2; simp [WShapeFun] at a2
      exact ⟨⟨a1, wf.2.mono ((a2 _ a1).1 .rfl).1⟩, by rintro ⟨⟩ <;> simp +contextual [Shape.WF, *]⟩

theorem WShape.Compat.iff {x y : WShape n} : x.Compat y ↔ ∃ z, x ≤ z ∧ y ≤ z := by
  refine ⟨fun h => ?_, fun ⟨_, h1, h2⟩ => WShape.join_prop.1 _ h1 h2⟩
  have ⟨_, _, h2⟩ := WShape.join_prop.of_compat WShape.join_prop h
  exact ⟨_, (h2 _).1 .rfl⟩

theorem WShape.Compat.of_le {x : WShape n} (h : x ≤ y) : x.Compat y :=
  WShape.Compat.iff.2 ⟨_, h, .rfl⟩
theorem WShape.Compat.rfl {x : WShape n} : x.Compat x := .of_le .rfl
def WShape.join (a b : WShape n) : WShape n :=
  if h : a.Compat b then ⟨a.1.join b.1, (WShape.join_prop.2 h).1⟩ else .bot
def WShape.Join (x y z : WShape n) : Prop :=
  ∀ w : WShape n, z ≤ w ↔ x ≤ w ∧ y ≤ w
theorem WShape.join_val {a b : WShape n} (h : a.Compat b) : (a.join b).1 = a.1.join b.1 := by
  simp [WShape.join, h]
theorem WShape.Join.le (H : WShape.Join x y z) : x ≤ z ∧ y ≤ z := (H _).1 .rfl
theorem WShape.Join.mk (h : x.Compat y) : WShape.Join x y (x.join y) := by
  simp only [join, dif_pos h]; exact (WShape.join_prop.2 h).2

theorem WShape.Join.compat (H : WShape.Join x y z) : x.Compat y :=
  WShape.Compat.iff.2 ⟨z, (H _).1 .rfl⟩

theorem WShape.Join.iff {x y z : WShape n} :
    WShape.Join x y z ↔ x.Compat y ∧ x.join y ≤ z ∧ z ≤ x.join y := by
  refine ⟨fun h => ⟨Compat.iff.2 ⟨_, h.le⟩, ?_⟩, fun ⟨h1, h2, h3⟩ w => ?_⟩
  · exact ⟨((mk h.compat _).2 h.le), (h _).2 (mk h.compat).le⟩
  · exact ⟨fun h => (mk h1 _).1 (h2.trans h), fun h => h3.trans <| (mk h1 _).2 h⟩

theorem WShape.lift_join {x y : WShape n} (le : n ≤ m) :
    (x.join y).lift m = (x.lift m).join (y.lift m) := by
  simp [join]; split <;> rename_i h
  · rw [dif_pos ((WShape.Compat.lift le).2 h)]; ext1; simp [lift_val le, Shape.lift_join le]
  · rw [dif_neg (mt (WShape.Compat.lift le).1 h), lift_bot]

@[simp] theorem WShape.bot_join {x : WShape n} : bot.join x = x := by
  ext1; rw [join_val Compat.bot_l, bot, Shape.bot_join]
@[simp] theorem WShape.join_bot {x : WShape n} : x.join bot = x := by
  ext1; rw [join_val Compat.bot_r, bot, Shape.join_bot]
@[simp] theorem WShape.sort_join_sort :
    join (.sort r : WShape n) (.sort r') = if r = r' then .sort r else .bot := by
  ext1; simp [join, WShape.Compat, sort, Shape.Compat.sort_sort]; split <;> rfl

theorem WShape.Join.lift {x y z : WShape n} (le : n ≤ m) :
    (x.lift m).Join (y.lift m) (z.lift m) ↔ x.Join y z := by
  constructor
  · intro hJ w
    have := hJ (w.lift m)
    rwa [lift_le_lift le, lift_le_lift le, lift_le_lift le] at this
  · intro hJ; have ⟨h1, h2, h3⟩ := Join.iff.1 hJ
    refine Join.iff.2 ⟨(Compat.lift le).2 h1, ?_⟩
    exact lift_join le ▸ ⟨WShape.lift_mono le h2, WShape.lift_mono le h3⟩

theorem WShape.join_self {x y : WShape n} : WShape.Join x x y ↔ x ≤ y ∧ y ≤ x :=
  ⟨fun H => ⟨((H _).1 .rfl).1, (H _).2 ⟨.rfl, .rfl⟩⟩,
   fun ⟨H1, H2⟩ _ => ⟨fun h => ⟨H1.trans h, H1.trans h⟩, fun h => H2.trans h.1⟩⟩

def WShapeFun.Join (x y z : WShapeFun n) : Prop := ∀ w : WShapeFun n, z ≤ w ↔ x ≤ w ∧ y ≤ w

theorem WShapeFun.Join.le (H : WShapeFun.Join x y z) : x ≤ z ∧ y ≤ z := (H _).1 .rfl

def WShapeFun.join (x y : WShapeFun n) : WShapeFun n :=
  if h : x.Compat y then
    ⟨ShapeFun.join Shape.join x.1 y.1, ((WShape.join_prop.ih_fun WShape.join_prop).2 h).1⟩
  else .bot

theorem WShapeFun.join_val {x y : WShapeFun n} (H : Compat x y) :
    (x.join y).1 = x.1.join Shape.join y.1 := by simp [join, dif_pos H]

@[simp] theorem WShape.forallE_join_forallE {a a' : WShape n} {f f' : WShapeFun n}
    (hc1 : a.Compat a') (hc2 : WShapeFun.Compat f f') :
    (WShape.forallE a f).join (.forallE a' f') = .forallE (a.join a') (f.join f') := by
  have hc := Compat.forallE_forallE.2 ⟨hc1, hc2⟩
  ext1; rw [join_val hc]; simp [forallE, Shape.join, join_val hc1, WShapeFun.join_val hc2]

theorem WShapeFun.Join.mk (H : WShapeFun.Compat x y) : WShapeFun.Join x y (x.join y) := by
  simp [Join, WShapeFun.LE.def, join_val H]
  have ⟨_, h⟩ := (WShape.join_prop.ih_fun WShape.join_prop).2 H; exact h

theorem WShapeFun.Compat.iff {x y : WShapeFun n} : x.Compat y ↔ ∃ z, x ≤ z ∧ y ≤ z := by
  refine ⟨fun h => ⟨_, (Join.mk h).le⟩, fun ⟨_, h1, h2⟩ => ?_⟩
  exact (WShape.join_prop.ih_fun WShape.join_prop).1 _ h1 h2

@[simp] theorem WShapeFun.Compat.bot_l {s : WShapeFun n} : bot.Compat s := iff.2 ⟨_, bot_le, .rfl⟩
@[simp] theorem WShapeFun.Compat.bot_r {s : WShapeFun n} : s.Compat bot := iff.2 ⟨_, .rfl, bot_le⟩

theorem WShapeFun.Join.compat (H : Join x y z) : x.Compat y := Compat.iff.2 ⟨z, (H _).1 .rfl⟩

theorem WShapeFun.Join.iff :
    Join x y z ↔ x.Compat y ∧ x.join y ≤ z ∧ z ≤ x.join y := by
  refine ⟨fun h => ⟨Compat.iff.2 ⟨_, h.le⟩, ?_⟩, fun ⟨h1, h2, h3⟩ w => ?_⟩
  · exact ⟨((mk h.compat _).2 h.le), (h _).2 (mk h.compat).le⟩
  · exact ⟨fun h => (mk h1 _).1 (h2.trans h), fun h => h3.trans <| (mk h1 _).2 h⟩

/-- The "total" shape domain: a dependent pair of a level `n` and a
well-formed shape at that level. Order, compatibility and joins on
`TShape` are defined by lifting both arguments to a common level. -/
def TShape := Σ n, WShape n
/-- Inject a `WShape n` into `TShape` by remembering its level. -/
abbrev WShape.T : WShape n → TShape := Sigma.mk _

def TShape.LE (a b : TShape) : Prop := a.2.lift (max a.1 b.1) ≤ b.2.lift _
instance : _root_.LE TShape := ⟨TShape.LE⟩
theorem TShape.LE.def' {a b : TShape} : a ≤ b ↔ a.2.lift (max a.1 b.1) ≤ b.2.lift _ := .rfl

def TShapeFun.LE (a : WShapeFun n) (b : WShapeFun m) : Prop :=
  a.lift (max n m) ≤ b.lift _

theorem TShape.LE.def {a b : TShape} (h1 : a.1 ≤ m) (h2 : b.1 ≤ m) :
    a ≤ b ↔ a.2.lift m ≤ b.2.lift m := by
  refine (WShape.lift_le_lift (Nat.max_le.2 ⟨h1, h2⟩)).symm.trans ?_
  rw [WShape.lift_lift (.inl (Nat.le_max_left ..)), WShape.lift_lift (.inl (Nat.le_max_right ..))]

theorem TShapeFun.LE.def {a : WShapeFun n} {b : WShapeFun m} (h1 : n ≤ k) (h2 : m ≤ k) :
    TShapeFun.LE a b ↔ a.lift k ≤ b.lift k := by
  refine (WShapeFun.lift_le_lift (Nat.max_le.2 ⟨h1, h2⟩)).symm.trans ?_
  rw [WShapeFun.lift_lift (.inl (Nat.le_max_left ..)),
    WShapeFun.lift_lift (.inl (Nat.le_max_right ..))]

theorem TShape.LE.forallE_decomp
    (le : (WShape.forallE (n := n) b f).T ≤ (WShape.forallE (n := n') b' f').T) :
    b.lift (max n n') ≤ b'.lift (max n n') ∧ f.lift (max n n') ≤ f'.lift (max n n') := by
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have h := (TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂)).1 le
  have h_raw : ((WShape.forallE b f).lift _).1 ≤ ((WShape.forallE b' f').lift _).1 := h
  rw [WShape.lift_val (Nat.succ_le_succ le₁), WShape.lift_val (Nat.succ_le_succ le₂)] at h_raw
  simp only [WShape.forallE, Shape.lift, Shape.LE.def] at h_raw
  constructor
  · show (b.lift _).1 ≤ (b'.lift _).1
    rw [WShape.lift_val le₁, WShape.lift_val le₂]; exact h_raw.1
  · show (f.lift _).1.LE (f'.lift _).1
    rw [WShapeFun.lift_val le₁, WShapeFun.lift_val le₂]; exact h_raw.2

theorem TShape.LE.lam'_decomp {f : WShapeFun n} {f' : WShapeFun n'} :
    (WShape.lam' f).T ≤ (WShape.lam' f').T →
    f.lift (max n n') ≤ f'.lift (max n n') := by
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have le₁' := Nat.succ_le_succ le₁; have le₂' := Nat.succ_le_succ le₂
  rw [TShape.LE.def le₁' le₂', WShape.LE.def, WShape.lift_val le₁', WShape.lift_val le₂',
    WShape.lam', WShape.lam']
  dsimp; split <;> rename_i hf
  · split <;> rename_i hf' <;>
      simp [WShape.lam, Shape.lift, WShapeFun.LE.def, WShapeFun.lift_val, le₁, le₂]
    intro h; cases Shape.le_bot.1 h
  · rintro -
    refine WShapeFun.LE.def'.2 fun x y h => ?_
    obtain ⟨_, _, h1, ⟨⟩, ⟨⟩⟩ := (WShapeFun.mem_lift le₁).1 h
    have := WShape.le_bot.1 <| Decidable.by_contra fun h => hf ⟨_, h1, h⟩
    dsimp at this; cases this
    have ⟨_, h⟩ := f'.bot_mem
    exact ⟨_, _, (WShapeFun.mem_lift le₂).2 ⟨_, _, h, rfl, rfl⟩, by simp⟩

def TShape.bot : TShape := WShape.T (n := 0) .bot
def TShape.sort (r : Bool) : TShape := WShape.T (n := 0) (.sort r)
def TShape.type : TShape := .sort true

nonrec theorem TShape.LE.rfl {a : TShape} : a ≤ a := WShape.LE.rfl

theorem TShape.LE.trans {a b c : TShape} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  let k := max (max a.1 b.1) c.1
  have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
  exact (LE.def hk.1.1 hk.2).2 (.trans ((LE.def hk.1.1 hk.1.2).1 h1) ((LE.def hk.1.2 hk.2).1 h2))

theorem TShape.LE.lift_l {a b : TShape} (h1 : a.1 ≤ b.1) : a ≤ b ↔ a.2.lift (b.1) ≤ b.2 :=
  (LE.def h1 (Nat.le_refl _)).trans (WShape.lift_self ▸ .rfl)
theorem TShape.LE.lift_r {a b : TShape} (h1 : b.1 ≤ a.1) : a ≤ b ↔ a.2 ≤ b.2.lift (a.1) :=
  (LE.def (Nat.le_refl _) h1).trans (WShape.lift_self ▸ .rfl)
theorem WShape.LE.T_iff {a b : WShape n} : a.T ≤ b.T ↔ a ≤ b :=
  (TShape.LE.lift_l (Nat.le_refl _) (a := a.T) (b := b.T)).trans (WShape.lift_self ▸ .rfl)
theorem WShape.LE.T {a b : WShape n} : a ≤ b → a.T ≤ b.T := T_iff.2
theorem TShape.bot_eqv : (WShape.bot (n := n)).T ≤ bot ∧ bot ≤ (WShape.bot (n := n)).T := by
  simp [TShape.LE.def', bot, WShape.lift_bot]

theorem TShape.bot_le' : (WShape.bot (n := n)).T ≤ a := by
  simp [TShape.LE.def', WShape.lift_bot]

theorem TShape.bot_le {a : TShape} : bot ≤ a := bot_le'

theorem TShape.le_bot {a : TShape} : a ≤ bot ↔ a.2 = .bot := by
  simp [TShape.LE.def', bot, WShape.lift_le_bot (Nat.le_max_left ..), WShape.lift_bot]

theorem TShape.le_bot' {a : TShape} : a ≤ bot ↔ a = WShape.T (n := a.1) .bot := by
  rw [le_bot]; let ⟨n, s⟩ := a
  exact ⟨fun h => congrArg (Sigma.mk n) h, fun h => Sigma.mk.inj h |>.2 |> eq_of_heq⟩

theorem TShape.lift_eqv {a : TShape} (h : a.1 ≤ m) :
    (a.2.lift m).T ≤ a ∧ a ≤ (a.2.lift m).T := by
  simp [TShape.LE.def', WShape.lift_lift (.inl h), WShape.LE.rfl]

theorem TShape.sort_eqv :
    (WShape.sort (n := n) r).T ≤ .sort r ∧ .sort r ≤ (WShape.sort (n := n) r).T := by
  simp [sort, TShape.LE.def', WShape.lift_sort, WShape.LE.rfl]

theorem TShape.sort_not_le_lam' {f : WShapeFun n'} :
    ¬(.sort r : WShape n).T ≤ (WShape.lam' f).T := by
  rw [TShape.LE.def']; simp only [WShape.T, WShape.lift_sort]
  intro h; have h := congrArg (·.1) (WShape.sort_le.1 h)
  simp only [WShape.sort, WShape.lam'] at h; split at h <;>
  · simp only [WShape.lam, WShape.bot, WShape.lift_val (Nat.le_max_right ..)] at h
    have hk : max n (n' + 1) = max n (n' + 1) - 1 + 1 := by omega
    rw [hk] at h; simp [Shape.sort, Shape.lift, Shape.bot] at h

theorem TShape.forallE_not_le_lam' {a : WShape n} {f₁ : WShapeFun n} {f₂ : WShapeFun n'} :
    ¬(.forallE a f₁ : WShape (n+1)).T ≤ (WShape.lam' f₂).T := by
  have' le₁ := Nat.le_max_left ..; have' le₂ := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_forallE le₁, WShape.lift_lam' le₂]
  intro hle; have ⟨_, _, _, _, hle⟩ := WShape.forallE_le.1 hle
  unfold WShape.lam' at hle; split at hle <;>
    simp [WShape.ext_iff, WShape.forallE, WShape.lam] at hle
  cases hle

theorem TShape.lam_not_le_forallE {f₁ : WShapeFun n} {hl} {a' : WShape n'} {f' : WShapeFun n'} :
    ¬(.lam f₁ hl : WShape (n+1)).T ≤ (.forallE a' f' : WShape (n'+1)).T := by
  have' le₁ := Nat.le_max_left ..; have' le₂ := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_lam le₁, WShape.lift_forallE le₂]
  simp [(· ≤ ·), Shape.LE, Shape.ble, WShape.lam, WShape.forallE]

theorem TShape.sort_not_le_forallE {a' : WShape n'} {f' : WShapeFun n'} :
    ¬(.sort r : WShape n).T ≤ (.forallE a' f' : WShape (n'+1)).T := by
  rw [TShape.LE.def']; simp only [WShape.T, WShape.lift_sort]
  intro h; have h := congrArg (·.1) (WShape.sort_le.1 h)
  simp only [WShape.sort, WShape.forallE, WShape.lift_val (Nat.le_max_right ..)] at h
  have hk : max n (n' + 1) = max n (n' + 1) - 1 + 1 := by omega
  rw [hk] at h; simp [Shape.sort, Shape.lift] at h

def TShape.Compat (x y : TShape) : Prop := (x.2.lift (max x.1 y.1)).Compat (y.2.lift _)

theorem TShape.Compat.def {x y : TShape} (h1 : x.1 ≤ m) (h2 : y.1 ≤ m) :
    x.Compat y ↔ (x.2.lift m).Compat (y.2.lift _) := by
  refine (WShape.Compat.lift (Nat.max_le.2 ⟨h1, h2⟩)).symm.trans ?_
  rw [WShape.lift_lift (.inl (Nat.le_max_left ..)), WShape.lift_lift (.inl (Nat.le_max_right ..))]

theorem WShape.Compat.T_iff {x y : WShape n} : x.Compat y ↔ x.T.Compat y.T := by
  refine .trans ?_ (TShape.Compat.def (x := x.T) (y := y.T) (Nat.le_refl _) (Nat.le_refl _)).symm
  rw [WShape.lift_self, WShape.lift_self]

theorem TShape.Compat.def' {x y : TShape} : x.Compat y ↔ ∃ z, x ≤ z ∧ y ≤ z := by
  refine ⟨fun h => ?_, fun ⟨z, h1, h2⟩ => ?_⟩
  · have ⟨z, h1, h2⟩ := WShape.Compat.iff.1 h
    exact ⟨z.T, (LE.lift_l (Nat.le_max_left ..)).2 h1, (LE.lift_l (Nat.le_max_right ..)).2 h2⟩
  · let k := max x.1 (max y.1 z.1); have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
    exact (TShape.Compat.def hk.1 hk.2.1).2 <|
      WShape.Compat.iff.2 ⟨z.2.lift k, (LE.def hk.1 hk.2.2).1 h1, (LE.def hk.2.1 hk.2.2).1 h2⟩

theorem NonZero.not_iff {f : WShapeFun n} : ¬f.NonZero ↔ f ≤ .bot := by
  simp only [WShapeFun.NonZero, ShapeFun.NonZero, Prod.exists, not_exists, not_and,
    Decidable.not_not, WShapeFun.bot, ShapeFun.bot, WShapeFun.LE.def, ShapeFun.LE.def,
    List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, and_assoc, exists_and_left,
    exists_eq_left, Shape.bot_le, true_and]

theorem WShape.Compat.mono {x y x' y' : WShape n}
    (h1 : x ≤ x') (h2 : y ≤ y') (H : x'.Compat y') : x.Compat y :=
  have ⟨_, a1, a2⟩ := WShape.Compat.iff.1 H
  WShape.Compat.iff.2 ⟨_, h1.trans a1, h2.trans a2⟩

theorem WShapeFun.Compat.mono {x y x' y' : WShapeFun n}
    (h1 : x ≤ x') (h2 : y ≤ y') (H : x'.Compat y') : x.Compat y :=
  have ⟨_, a1, a2⟩ := WShapeFun.Compat.iff.1 H
  WShapeFun.Compat.iff.2 ⟨_, h1.trans a1, h2.trans a2⟩

theorem WShape.Compat.lam' {a b : WShapeFun n} : Compat (.lam' a) (.lam' b) ↔ a.Compat b := by
  rw [WShape.lam']; split <;> rename_i h1
  · rw [WShape.lam']; split <;> [rfl; rename_i h2]
    simp; exact .mono .rfl (NonZero.not_iff.1 h2) .bot_r
  · simp; exact .mono (NonZero.not_iff.1 h1) .rfl .bot_l

theorem WShape.Join.lam' {a b c : WShapeFun n} :
    Join (.lam' a) (.lam' b) (.lam' c) ↔ a.Join b c := by
  refine ⟨fun H z => by simpa [lam'_le_lam'] using H (.lam' z), fun H z => ?_⟩
  by_cases hz : ∃ z', .lam' z' = z
  · obtain ⟨z', rfl⟩ := hz; simp only [lam'_le_lam', H _]
  have {x} : WShape.lam' x ≤ z ↔ x ≤ .bot := by
    unfold WShape.lam'; split <;> rename_i h
    · simp [← NonZero.not_iff, h, WShape.LE.def, lam, Shape.lam_le]
      obtain ⟨_, wf⟩ := z; rintro _ h1 ⟨⟩; refine hz ⟨⟨_, wf.1⟩, ?_⟩
      rw [WShape.lam', dif_pos (by exact wf.2)]; rfl
    · simp [NonZero.not_iff.1 h]
  simp only [this, H _]

def TShape.join (x y : TShape) : TShape := ⟨max x.1 y.1, (x.2.lift _).join (y.2.lift _)⟩

theorem TShape.lift_join {x y : TShape} (h1 : x.1 ≤ m) (h2 : y.1 ≤ m) :
    (x.join y).2.lift m = (x.2.lift m).join (y.2.lift m) := by
  simp [join, WShape.lift_join (Nat.max_le.2 ⟨h1, h2⟩),
    WShape.lift_lift (.inl (Nat.le_max_left ..)), WShape.lift_lift (.inl (Nat.le_max_right ..))]

def TShape.Join (x y z : TShape) := ∀ w, z ≤ w ↔ x ≤ w ∧ y ≤ w

theorem TShape.Join.le (H : Join x y z) : x ≤ z ∧ y ≤ z := (H _).1 .rfl

theorem TShape.Join.def (h1 : x.1 ≤ m) (h2 : y.1 ≤ m) (h3 : z.1 ≤ m) :
    Join x y z ↔ WShape.Join (x.2.lift m) (y.2.lift m) (z.2.lift m) := by
  constructor <;> intro hJ w
  · have hle : m ≤ m := Nat.le_refl m
    have := hJ (⟨m, w⟩ : TShape)
    rwa [TShape.LE.def h3 hle, TShape.LE.def h1 hle, TShape.LE.def h2 hle, WShape.lift_self] at this
  · let k := max m w.1
    have hk : m ≤ k := Nat.le_max_left ..
    have hwk : w.1 ≤ k := Nat.le_max_right ..
    rw [TShape.LE.def (Nat.le_trans h3 hk) hwk, TShape.LE.def (Nat.le_trans h1 hk) hwk,
      TShape.LE.def (Nat.le_trans h2 hk) hwk, ← WShape.lift_lift (.inl h3),
      ← WShape.lift_lift (.inl h1), ← WShape.lift_lift (.inl h2)]
    exact (WShape.Join.lift hk |>.2 hJ) _

theorem WShape.Join.T_iff {x y z : WShape n} : WShape.Join x y z ↔ TShape.Join x.T y.T z.T := by
  refine .symm <| (TShape.Join.def (x := x.T) (y := y.T) (z := z.T)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)).trans ?_
  rw [WShape.lift_self, WShape.lift_self, WShape.lift_self]

theorem WShape.Join.T {x y z : WShape n} : Join x y z → TShape.Join x.T y.T z.T := T_iff.1

theorem TShape.Join.mk (H : x.Compat y) : Join x y (x.join y) := by
  let m := max x.1 y.1; have ⟨hx, hy⟩ := Nat.max_le.1 (Nat.le_refl m)
  rw [TShape.Join.def hx hy (Nat.le_refl _), TShape.lift_join hx hy]
  exact .mk ((TShape.Compat.def hx hy).1 H)

def ShapeFun.WF.app {f : ShapeFun n} (wf : WF Shape.WF f) (wfa : a.WF) : (ShapeFun.app f a).WF := by
  have ⟨_, _, h, _⟩ := WShape.join_prop.app_core WShape.join_prop ⟨_, wf⟩ ⟨_, wfa⟩
  exact (wf.2 _ h).2

/-- Semantic application of a function shape to an argument shape: looks up
the join of all output samples whose input shape is below `a`. -/
def WShapeFun.app (f : WShapeFun n) (a : WShape n) : WShape n :=
  ⟨ShapeFun.app f.1 a.1, f.2.app a.2⟩

theorem WShapeFun.app_core (f : WShapeFun n) (x) :
    ∃ x', x' ≤ x ∧ (x', f.app x) ∈ f ∧ ∀ y ∈ f, y.1 ≤ x → y.2 ≤ f.app x := by
  have ⟨_, h1, h2, h3⟩ := WShape.join_prop.app_core WShape.join_prop f x
  exact ⟨_, h1, f.mem_val h2, fun _ a1 => h3 _ (f.mem_val a1)⟩

theorem WShapeFun.Compat.app_l {f f' : WShapeFun n} :
    f.Compat f' → ∀ x, (f.app x).Compat (f'.app x) := WShape.join_prop.compat_app_l WShape.join_prop

@[simp] theorem ShapeFun.bot_app : (@ShapeFun.bot n).app x = .bot := by
  simp [ShapeFun.bot, ShapeFun.app, ShapeFun.maxBelow, trunc]

def Shape.app : Shape (n + 1) → Shape n → Shape n
  | .lam f, x => ShapeFun.app f x
  | _, _ => .bot

@[simp] theorem Shape.bot_app : (@Shape.bot (n+1)).app x = .bot := rfl

@[simp] theorem Shape.lift_app (le : n ≤ m) :
    (app f a : Shape n).lift m = app (f.lift _) (a.lift _) := by
  cases f <;> simp [app, lift, ShapeFun.lift_app le]

def WShape.app (f : WShape (n+1)) (a : WShape n) : WShape n := by
  refine ⟨Shape.app f.1 a.1, ?_⟩
  obtain ⟨⟨⟩, wf⟩ := f <;> try exact .bot
  exact (WShapeFun.app ⟨_, wf.1⟩ _).2

@[simp] theorem WShape.bot_app {x : WShape n} : WShape.app (WShape.bot (n := n+1)) x = .bot :=
  WShape.ext (Shape.bot_app (x := x.1))

@[simp] theorem WShape.lam_app {f : WShapeFun n} {hl} {x : WShape n} :
    WShape.app (WShape.lam f hl) x = f.app x := rfl

theorem WShapeFun.app_of_mem {f : WShapeFun n} (h : (x, y) ∈ f) :
    f.app x ≤ y ∧ y ≤ f.app x :=
  have ⟨_, h1, h2, h3⟩ := f.app_core x
  ⟨f.mem_mono h2 h h1, h3 _ h .rfl⟩

theorem WShapeFun.app_eq (f : WShapeFun n) (x : WShape n) :
    ∃ x', x' ≤ x ∧ (x', f.app x) ∈ f :=
  let ⟨x', h1, h2, _⟩ := f.app_core x; ⟨x', h1, h2⟩

theorem WShapeFun.app_mono_l {f f' : WShapeFun n} (h : f ≤ f') (a : WShape n) :
    f.app a ≤ f'.app a := by
  have ⟨_, a1, a2, a3⟩ := f.app_core a
  have ⟨_, b1, b2, b3⟩ := f'.app_core a
  have ⟨_, _, c1, c2, c3⟩ := WShapeFun.LE.def'.1 h _ _ a2
  exact c3.trans <| b3 _ c1 (c2.trans a1)

theorem WShapeFun.app_mono_r {f : WShapeFun n} {a a' : WShape n} (h : a ≤ a') :
    f.app a ≤ f.app a' := by
  have ⟨_, a1, a2, a3⟩ := f.app_core a
  have ⟨_, b1, b2, b3⟩ := f.app_core a'
  exact b3 _ a2 (a1.trans h)

theorem WShape.app_mono_l {f f' : WShape (n+1)} (h : f ≤ f') (a : WShape n) :
    f.app a ≤ f'.app a := by
  change f.1 ≤ f'.1 at h; show Shape.app f.1 a.1 ≤ Shape.app f'.1 a.1
  cases hf : f.1 with | lam => ?_ | _ => exact Shape.bot_le
  let ⟨f', wf'⟩ := f'; have := hf ▸ f.2
  cases f' with rw [hf] at h | lam => ?_ | _ => exact (Shape.LE.def.1 h).elim
  exact WShapeFun.app_mono_l (f := ⟨_, (hf ▸ f.2).1⟩) (f' := ⟨_, wf'.1⟩) h _

theorem WShape.app_mono_r {f : WShape (n+1)} {a a' : WShape n} (h : a ≤ a') :
    f.app a ≤ f.app a' := by
  obtain ⟨⟨⟩, wf⟩ := f <;> try exact .rfl
  exact WShapeFun.app_mono_r (f := ⟨_, wf.1⟩) h

@[simp] theorem WShapeFun.bot_app : (WShapeFun.bot (n := n)).app x = .bot := by
  ext1; exact ShapeFun.bot_app

theorem WShapeFun.lift_app {f : WShapeFun n} {a : WShape n} (le : n ≤ m) :
    (f.app a).lift m = (f.lift m).app (a.lift m) := by
  ext1; simp [WShape.lift_val le, app, WShapeFun.lift_val le]
  exact ShapeFun.lift_app le

@[simp] theorem WShape.lift_app (le : n ≤ m) :
    (app f a : WShape n).lift m = app (f.lift _) (a.lift _) := by
  ext1; simp [lift_val le, app, Shape.lift_app le, lift_val (Nat.succ_le_succ le)]

@[simp] theorem WShape.lam'_app {f : WShapeFun n} {x : WShape n} : (lam' f).app x = f.app x := by
  simp [lam']; split <;> simp; rename_i h
  have ⟨_, h1, h2⟩ := f.app_eq x
  rw [eq_comm, ← WShape.le_bot]; exact Decidable.by_contra <| mt (⟨_, h2, ·⟩) h

theorem TShape.app_mono {f : WShape (n + 1)} {f' : WShape (m + 1)} {a : WShape n} {a' : WShape m}
    (le₁ : f.T ≤ f'.T) (le₂ : a.T ≤ a'.T) : (f.app a).T ≤ (f'.app a').T := by
  have lm₁ := Nat.le_max_left n m; have lm₂ := Nat.le_max_right n m
  rw [TShape.LE.def', WShape.lift_app lm₁, WShape.lift_app lm₂]
  refine (WShape.app_mono_l ?_ _).trans (WShape.app_mono_r le₂)
  exact (LE.def (Nat.succ_le_succ lm₁) (Nat.succ_le_succ lm₂)).1 le₁

theorem WShapeFun.mem_join {f f' : WShapeFun n} {a} (hc : f.Compat f') :
    (a, b) ∈ f.join f' ↔ ∃ x ∈ f, ∃ y ∈ f', x.1.Compat y.1 ∧
      let j := x.1.join y.1; a = j ∧ b = (f.app j).join (f'.app j) := by
  simp only [WShapeFun.mem_def, WShapeFun.join_val hc, ShapeFun.mem_join]
  constructor
  · intro ⟨x, h1, y, h2, h3, h4⟩
    refine have h3' := ?_; ⟨_, f.mem_val h1, _, f'.mem_val h2, h3', ?_⟩; · exact h3
    cases a; cases b; cases h4; simp; constructor <;> ext1
    · simp [WShape.join_val h3']
    · rw [WShape.join_val (hc.app_l _)]; simp [app, WShape.join_val h3']
  · rintro ⟨x, h1, y, h2, h3, rfl, rfl⟩; refine ⟨_, h1, _, h2, h3, ?_⟩
    simp [WShape.join_val h3]; rw [WShape.join_val (hc.app_l _)]; simp [app, WShape.join_val h3]

def ShapeFun.single (x y : Shape n) : ShapeFun n :=
  (x, y) :: if x ≤ .bot then [] else [(.bot, .bot)]

protected theorem ShapeFun.WF.single (x y : WShape n) : WF Shape.WF (single x.1 y.1) := by
  refine ⟨?_, fun p hp => ?_⟩; rotate_left
  · simp [single] at hp
    obtain rfl | ⟨_, rfl⟩ := hp
    · exact ⟨x.2, y.2⟩
    · exact ⟨.bot, .bot⟩
  simp only [single, List.mem_cons, List.mem_ite_nil_left, List.not_mem_nil, or_false,
    exists_eq_or_imp, forall_eq_or_imp, and_imp, forall_eq_apply_imp_iff, Shape.bot_le,
    imp_self, and_true]
  have self : x.1.join x.1 ≤ x.1 ∧ x.1 ≤ x.1.join x.1 :=
    WShape.join_val .rfl ▸ (WShape.Join.iff.1 (WShape.join_self.2 ⟨.rfl, .rfl⟩)).2
  refine ⟨?_, ⟨⟨fun _ => .inl self, fun _ => .rfl⟩, ?_⟩, fun nle => ⟨fun h1 => ?_, fun h1 => ?_⟩⟩
  · obtain ⟨x, _⟩ := x; by_cases h : x ≤ .bot
    · cases Shape.le_bot.1 h; exact ⟨_, .inl rfl⟩
    · exact ⟨_, .inr ⟨h, rfl⟩⟩
  · exact (⟨by simp [Shape.join_bot, Shape.LE.rfl], ·.elim⟩)
  · simp [Shape.bot_join, Shape.LE.rfl]
  · simp [Shape.bot_join, nle]

def WShapeFun.single (x y : WShape n) : WShapeFun n :=
  ⟨ShapeFun.single x.1 y.1, .single x y⟩

theorem ShapeFun.single_app : (single x y).app x' = if x ≤ x' then y else .bot := by
  simp [single, app, trunc, maxBelow, List.find?]
  by_cases h : x ≤ x' <;> simp [h, Shape.LE.rfl]; split <;> simp

theorem WShapeFun.single_app {x y : WShape n} {x' : WShape n} :
    (WShapeFun.single x y).app x' = if x ≤ x' then y else .bot := by
  ext1; simp [WShapeFun.single, app, ShapeFun.single_app]
  split <;> simp [*, WShape.LE.def, WShape.bot]

theorem WShapeFun.mem_single {x y : WShape n} :
    a ∈ WShapeFun.single x y ↔ a = (x, y) ∨ ¬x ≤ .bot ∧ a = (.bot, .bot) := by
  cases a; simp [WShapeFun.mem_def, WShapeFun.single, ShapeFun.single,
    WShape.ext_iff, WShape.LE.def, WShape.bot]

theorem WShapeFun.single_le {f : WShapeFun n} :
    WShapeFun.single x y ≤ f ↔ ∃ x' y', (x', y') ∈ f ∧ x' ≤ x ∧ y ≤ y' := by
  simp [WShapeFun.LE.def', WShapeFun.mem_single]
  refine ⟨fun H => H _ _ (.inl ⟨rfl, rfl⟩), ?_⟩
  rintro H _ _ (⟨rfl, rfl⟩ | ⟨h4, rfl, rfl⟩)
  · exact H
  · let ⟨_, h1⟩ := f.bot_mem; exact ⟨_, _, h1, .rfl, WShape.bot_le⟩

theorem WShapeFun.lift_single (le : n ≤ m) {x y : WShape n} :
    (WShapeFun.single x y).lift m = WShapeFun.single (x.lift m) (y.lift m) := by
  ext1; simp [lift_val le, single, WShape.lift_val le, ShapeFun.single, ShapeFun.lift]
  split <;> simp [*, Shape.lift_le_bot le, ← Shape.le_bot]

theorem WShapeFun.compat_single {f : WShapeFun n} :
    Compat f (single x y) ↔ ∀ a ∈ f, a.1.Compat x → a.2.Compat y := by
  simp [WShapeFun.Compat.def, mem_single, WShape.Compat.bot_r]

theorem WShapeFun.Join.app_l {f g h : WShapeFun n}
    (hJ : Join f g h) (p : WShape n) : WShape.Join (f.app p) (g.app p) (h.app p) := by
  refine fun z => ⟨fun H => ⟨?_, ?_⟩, fun ⟨h1, h2⟩ => ?_⟩
  · exact (app_mono_l hJ.le.1 p).trans H
  · exact (app_mono_l hJ.le.2 p).trans H
  · refine (app_mono_l (Join.iff.1 hJ).2.2 _).trans ?_
    have ⟨x, a1, a2, a3⟩ := (f.join g).app_core p
    obtain ⟨⟨a, _⟩, b1, ⟨b, _⟩, b2, b3, rfl, b5⟩ := (WShapeFun.mem_join hJ.compat).1 a2
    have hJ' := WShape.Join.mk (hJ.compat.app_l (a.join b))
    exact b5 ▸ (hJ' _).2 ⟨(app_mono_r a1).trans h1, (app_mono_r a1).trans h2⟩

def hasType.core (hasType : Shape n → Shape n → Bool)
    (f : ShapeFun n) (a : Shape n) (G : Shape n → Shape n) : Bool :=
  f.all fun (x, y) => (f.any fun (x', y') => x' ≤ x && y ≤ y' && hasType x' a) && hasType y (G x)

def Shape.hasType : ∀ {n}, Shape n → Shape n → Bool
  | _+1, .bot, .forallE a b => hasType.core hasType b a fun _ => .type
  | _+1, .forallE a b, .sort r => hasType.core hasType b a fun _ => .sort r
  | 0, .bot, _ | _+1, .bot, .bot | _+1, .bot, .sort _ => true
  | 0, .sort _, .sort j | _+1, .sort _, .sort j => j
  | _+1, .lam f, .forallE a b =>
    hasType.core hasType b a (fun _ => .type) && hasType.core hasType f a (ShapeFun.app b)
  | _, _, _ => false

/-- "Has a type": the propositional reflection of `hasType`. `m.HasType a`
asserts that the shape `m` is a well-typed inhabitant of the type-shape
`a`, in particular witnessing the dependent-function structure on Π/λ. -/
def Shape.HasType : Shape n → Shape n → Prop := (hasType · ·)

/-- A function shape's domain entries cover the argument-shape `a`:
every `(x, y) ∈ f` is dominated by some `(x', y') ∈ f` with `x' : a`. -/
def Shape.HasDom (f : ShapeFun n) (a : Shape n) :=
  ∀ x y, (x, y) ∈ f → ∃ x' y', (x', y') ∈ f ∧ x' ≤ x ∧ y ≤ y' ∧ x'.HasType a

/-- A Π-type signature is well-formed at `(a, rel)` iff its codomain function
has domain `a` and lands in `sort rel`. -/
def Shape.HasTypePi (b : ShapeFun n) (a : Shape n) (rel : Bool) :=
  Shape.HasDom b a ∧ ∀ x y, (x, y) ∈ b → y.HasType (.sort rel)

/-- A λ-abstraction shape is well-typed at `(a, b)` iff `b` is a `Π a Type`
codomain spec and each `(x, y) ∈ f` lies in `b.app x`. -/
def Shape.HasTypeLam (f : ShapeFun n) (a : Shape n) (b : ShapeFun n) :=
  Shape.HasTypePi b a true ∧ Shape.HasDom f a ∧ ∀ x y, (x, y) ∈ f → y.HasType (b.app x)

theorem Shape.hasType.core.iff {a : Shape n} :
    hasType.core hasType f a G ↔ HasDom f a ∧ ∀ x y, (x, y) ∈ f → y.HasType (G x) := by
  simp [hasType.core, HasDom, forall_and, HasType, and_assoc]

inductive Shape.HasTypeU : ∀ {n}, Shape n → Shape n → Prop
  | bot : HasType x .type → HasTypeU .bot x
  | sort : HasTypeU (.sort r) .type
  | forallE : HasTypePi (n := n) b a r → HasTypeU (n := n+1) (.forallE a b) (.sort r)
  | lam : HasTypeLam (n := n) f a b → HasTypeU (n := n+1) (.lam f) (.forallE a b)

theorem Shape.HasType.unfold {m a : Shape n} : HasType m a → HasTypeU m a := by
  unfold HasType Shape.hasType
  split <;> (try simp [hasType.core.iff]) <;> intros <;> subst_vars <;> try constructor
  · simp [HasType, hasType.core.iff, hasType]; exact ⟨‹_›, ‹_›⟩
  · simp [HasTypePi]; exact ⟨‹_›, ‹_›⟩
  · rename_i x; cases x <;> rfl
  · rfl
  · rfl
  · simp only [HasTypeLam, HasTypePi]; exact ⟨⟨‹_›, ‹_›⟩, ⟨‹_›, ‹_›⟩⟩

theorem Shape.HasType.unfold_iff {m a : Shape n} : HasType m a ↔ HasTypeU m a := by
  refine ⟨(·.unfold), fun h => ?_⟩
  cases h with
  | bot h =>
    cases h.unfold with
    | bot | sort => cases n <;> rfl
    | forallE => simpa [HasType, hasType] using h
  | sort => cases n <;> rfl
  | forallE H => simpa [HasType, hasType, hasType.core.iff] using H
  | lam H => simp [HasType, hasType, hasType.core.iff]; exact H

protected theorem Shape.HasType.lift (le : n ≤ n') :
    Shape.HasType (m.lift n') (a.lift n') ↔ Shape.HasType (n := n) m a := by
  dsimp [HasType]; rw [← Bool.eq_iff_iff]
  induction n generalizing n' with
  | zero =>
    cases n' with | zero => simp [Shape.lift_self] | succ n'
    cases m <;> cases a <;> simp [Shape.lift, hasType]
  | succ n ih =>
    let n' + 1 := n'; replace le := Nat.le_of_succ_le_succ le
    replace ih {m a} := @ih _ m a le
    have core {a : ShapeFun n} {a' : Shape n} {G G'} (H : ∀ {x}, G' (lift n' x) = lift n' (G x)) :
        hasType.core hasType (ShapeFun.lift (lift n') a) (lift n' a') G' =
        hasType.core hasType a a' G := by
      rw [Bool.eq_iff_iff]; simp [hasType.core, ShapeFun.lift, H, ih, lift_le_lift le]
    cases m <;> cases a <;> simp only [lift, hasType, type] <;> try rw [core lift_sort.symm]
    · rw [core (ShapeFun.lift_app le).symm]

protected theorem Shape.HasDom.lift (le : n ≤ n') :
    HasDom (ShapeFun.lift (lift n') m) (a.lift n') ↔ HasDom (n := n) m a := by
  simp only [HasDom, ShapeFun.lift, List.mem_map, Prod.mk.injEq]
  constructor <;> [intro H x y h; rintro H x y ⟨_, h, rfl, rfl⟩]
  · obtain ⟨_, _, ⟨_, h1, rfl, rfl⟩, h2, h3, h4⟩ := H _ _ ⟨_, h, rfl, rfl⟩
    exact ⟨_, _, h1, (Shape.lift_le_lift le).1 h2,
      (Shape.lift_le_lift le).1 h3, (Shape.HasType.lift le).1 h4⟩
  · have ⟨_, _, h1, h2, h3, h4⟩ := H _ _ h
    exact ⟨_, _, ⟨_, h1, rfl, rfl⟩, Shape.lift_mono h2,
      Shape.lift_mono h3, (Shape.HasType.lift le).2 h4⟩

protected theorem Shape.HasTypePi.lift (le : n ≤ n') :
    HasTypePi (ShapeFun.lift (lift n') m) (a.lift n') rel ↔ HasTypePi (n := n) m a rel := by
  simp only [HasTypePi]
  exact and_congr (HasDom.lift le) <| by
    simp only [ShapeFun.lift, List.mem_map, Prod.mk.injEq]
    constructor <;> [intro H x y h; rintro H _ _ ⟨⟨x, y⟩, h, rfl, rfl⟩]
    · exact (Shape.HasType.lift le).1 (Shape.lift_sort.symm ▸ H _ _ ⟨_, h, rfl, rfl⟩)
    · exact Shape.lift_sort ▸ (Shape.HasType.lift le).2 (H _ _ h)

theorem Shape.HasTypeLam.lift (le : n ≤ n') :
    HasTypeLam (ShapeFun.lift (lift n') f) (a.lift n') (ShapeFun.lift (lift n') b) ↔
    HasTypeLam (n := n) f a b := by
  simp only [HasTypeLam]
  refine and_congr (HasTypePi.lift le) <| and_congr (HasDom.lift le) ⟨?_, ?_⟩ <;> intro H x y h
  · have h' : (x.lift n', y.lift n') ∈ ShapeFun.lift (Shape.lift n') f :=
      List.mem_map.2 ⟨_, h, rfl⟩
    have := H _ _ h'
    rw [← ShapeFun.lift_app le] at this
    exact (Shape.HasType.lift le).1 this
  · obtain ⟨⟨x₀, y₀⟩, h₀, heq⟩ := List.mem_map.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    rw [← ShapeFun.lift_app le]
    exact (Shape.HasType.lift le).2 (H _ _ h₀)

protected theorem Shape.HasType.bot {a : Shape n} (H : HasType a .type) : HasType .bot a :=
  unfold_iff.2 (.bot H)
protected theorem Shape.HasType.sort : HasType (n := n) (.sort rel) .type := unfold_iff.2 .sort
protected theorem Shape.HasType.forallE (H : HasTypePi (n := n) b a r) :
    HasType (n := n+1) (.forallE a b) (.sort r) := unfold_iff.2 (.forallE H)
protected theorem Shape.HasType.lam (H : HasTypeLam (n := n) f a b) :
    HasType (n := n+1) (.lam f) (.forallE a b) := unfold_iff.2 (.lam H)

theorem Shape.HasType.toType (H : HasType (n := n) m (.sort r)) : HasType m .type := by
  unfold HasType hasType at H; revert H; generalize eq : sort r = s
  split <;> cases eq <;> simp [HasType, hasType]
  · simp only [hasType.core.iff]; refine fun ⟨h1, h2⟩ => ⟨h1, fun _ _ h3 => toType (h2 _ _ h3)⟩

theorem Shape.HasType.isType (H : HasType m a) : a.HasType .type := by
  cases H.unfold with
  | bot H => exact H
  | sort | forallE => exact .sort
  | lam H' => exact .forallE H'.1

theorem Shape.HasTypePi.toType (H : HasTypePi b a r) : HasTypePi b a true :=
  ⟨H.1, fun _ _ h => (H.2 _ _ h).toType⟩

def WShape.HasType (m a : WShape n) : Prop := Shape.HasType m.1 a.1
def WShape.HasDom (f : WShapeFun n) (a : WShape n) := Shape.HasDom f.1 a.1
def WShape.HasTypePi (b : WShapeFun n) (a : WShape n) := Shape.HasTypePi b.1 a.1
def WShape.HasTypeLam (f : WShapeFun n) (a : WShape n) (b : WShapeFun n) :=
  Shape.HasTypeLam f.1 a.1 b.1

theorem WShape.HasDom.def : HasDom f a ↔
    ∀ x y, (x, y) ∈ f → ∃ x' y', (x', y') ∈ f ∧ x' ≤ x ∧ y ≤ y' ∧ x'.HasType a :=
  ⟨fun H _ _ h => have ⟨_, _, h1, h2⟩ := H _ _ h; ⟨_, _, f.mem_val h1, h2⟩,
   fun H _ _ h => have ⟨_, _, h1, h2⟩ := H _ _ (f.mem_val h); ⟨_, _, h1, h2⟩⟩

def WShape.HasTypePi.def {b : WShapeFun n} :
    HasTypePi b a rel ↔ HasDom b a ∧ ∀ x y, (x, y) ∈ b → y.HasType (.sort rel) :=
  and_congr_right' ⟨fun H _ _ h => H _ _ h, fun H _ _ h => H _ _ (b.mem_val h)⟩

theorem WShape.HasTypeLam.def {f : WShapeFun n} {a b} :
  HasTypeLam f a b ↔ HasTypePi b a true ∧ HasDom f a ∧ ∀ x y, (x, y) ∈ f → y.HasType (b.app x) :=
  and_congr_right' <| and_congr_right' ⟨fun H _ _ h => H _ _ h, fun H _ _ h => H _ _ (f.mem_val h)⟩

theorem WShape.HasDom.lift (le : n ≤ m) :
    HasDom (f.lift m) (a.lift m) ↔ HasDom (n := n) f a := by
  simp only [HasDom, Shape.HasDom, WShapeFun.lift_val le, ShapeFun.lift, List.mem_map,
    Prod.mk.injEq, WShape.lift_val le]
  constructor <;> [intro H x y h; rintro H x y ⟨_, h, rfl, rfl⟩]
  · obtain ⟨_, _, ⟨_, h1, rfl, rfl⟩, h2, h3, h4⟩ := H _ _ ⟨_, h, rfl, rfl⟩
    exact ⟨_, _, h1, (Shape.lift_le_lift le).1 h2,
      (Shape.lift_le_lift le).1 h3, (Shape.HasType.lift le).1 h4⟩
  · have ⟨_, _, h1, h2, h3, h4⟩ := H _ _ h
    exact ⟨_, _, ⟨_, h1, rfl, rfl⟩, Shape.lift_mono h2,
      Shape.lift_mono h3, (Shape.HasType.lift le).2 h4⟩

theorem WShape.HasType.toType : HasType (n := n) x (.sort r) → HasType x .type :=
  Shape.HasType.toType

theorem WShape.HasType.isType : HasType m a → a.HasType .type := Shape.HasType.isType

theorem WShape.HasDom.isType (H : WShape.HasDom f a) : a.HasType .type := by
  have ⟨_, h⟩ := f.bot_mem
  have ⟨_, _, _, h2, _, h4⟩ := HasDom.def.1 H _ _ h
  cases le_bot.1 h2; exact h4.isType

theorem WShape.HasType.mono_r {m a a' : WShape n} (ha : a ≤ a')
    (Ha : HasType a' (.sort r)) (H : HasType m a) : HasType m a' := by
  have ⟨m, mwf⟩ := m; have ⟨a, awf⟩ := a; have ⟨a', awf'⟩ := a'
  simp only [HasType, sort, WShape.LE.def] at *
  cases H.unfold with
  | bot H => exact .bot Ha.toType
  | sort | forallE => cases Shape.sort_le.1 ha; exact H
  | @lam n _ _ _ H' =>
    obtain ⟨_, _, h1, h2, ⟨⟩⟩ := Shape.forallE_le.1 ha
    let .forallE Ha := Ha.unfold
    have ih := @WShape.HasType.mono_r n
    let rec ih_dom {f : WShapeFun n} {a a' r} (ha : a ≤ a') (Ha : HasType a' (.sort r))
        (H : HasDom (n := n) f a) : HasDom f a' := by
      rw [WShape.HasDom.def] at H ⊢; intro _ _ h
      have ⟨_, _, h1, h2, h3, h4⟩ := H _ _ h
      exact ⟨_, _, h1, h2, h3, ih ha Ha h4⟩
    let rec ih_lam {f : WShapeFun n} {a a' b b'} (Ha : HasTypePi b' a' r)
        (ha : a ≤ a') (hb : b ≤ b') (H : HasTypeLam f a b) : HasTypeLam f a' b' := by
      rw [HasTypeLam.def] at H ⊢
      have ht := (HasTypePi.def.1 Ha).1.isType
      refine ⟨Ha.toType, ih_dom ha ht H.2.1, fun x y h => ?_⟩
      have ⟨_, h1, h2⟩ := b'.app_eq x
      exact .mono_r (WShapeFun.app_mono_l hb _) ((HasTypePi.def.1 Ha).2 _ _ h2) (H.2.2 _ _ h)
    exact .lam (ih_lam (f := ⟨_, mwf.1⟩) (a := ⟨_, awf.1⟩)
      (a' := ⟨_, awf'.1⟩) (b := ⟨_, awf.2⟩) (b' := ⟨_, awf'.2⟩) Ha h1 h2 H')

theorem WShape.HasDom.mono_r {f : WShapeFun n} {a a' r} :
    a ≤ a' → HasType a' (.sort r) → HasDom f a → HasDom f a' := HasType.mono_r.ih_dom HasType.mono_r

private theorem find_cycle (R : α → α → Prop)
    (trans : ∀ {x y z}, R x y → R y z → R x z) (l : List α)
    (H : ∀ x ∈ l, ∃ y ∈ l, R x y) : ∀ x ∈ l, ∃ y ∈ l, R x y ∧ R y y := by
  intro x h
  suffices ∀ l₁ l₂, l.Perm (l₁ ++ l₂) → (∀ y ∈ l₂, ∀ z ∈ l, R x z → R y z) →
      ∃ y ∈ l, R x y ∧ R y y from this l [] (by simp) nofun
  intro l₁; generalize eq : l₁.length = i; revert x l₁
  refine i.strongRecOn ?_; rintro i ih x₀ h₀ l₁ rfl l₂ he hl
  have ⟨x', a1, a2⟩ := H x₀ h₀
  obtain hm | hm := List.mem_append.1 (he.mem_iff.1 a1)
  · have ⟨l', hp⟩ := List.perm_cons_of_mem hm
    have he' := he.trans (.append_right _ hp) |>.trans List.perm_middle.symm
    refine have ⟨_, c1, c2, c3⟩ := ih l'.length ?_ _ a1 _ rfl _ he' ?_; ⟨_, c1, trans a2 c2, c3⟩
    · rw [hp.length_eq]; apply Nat.lt_succ_self
    · rintro x' (⟨⟩ | ⟨_, hx⟩) z hz hr <;> [exact hr; exact hl _ hx _ hz (trans a2 hr)]
  · exact ⟨_, a1, a2, hl _ hm _ a1 a2⟩

namespace WShape.HasType.mono_l
variable (ih : ∀ {m m' a : WShape n}, m ≤ m' → m' ≤ m → HasType m a → HasType m' a)
include ih

theorem ih_dom {f f' : WShapeFun n} (hf1 : f ≤ f') (hf2 : f' ≤ f)
    (H : HasDom f a) : HasDom f' a := by
  rw [HasDom.def] at H ⊢; intro x y h
  have ⟨z, h1, ⟨c, c1, c2, c3, _⟩, d, d1, d2, _, d4⟩ := find_cycle ?_ f'.1 ?_ _ h
    (R := fun x y => ∃ z : WShape n, y.1 ≤ z.1 ∧ z.1 ≤ x.1 ∧ x.2 ≤ y.2 ∧ z.HasType a)
  · exact ⟨_, _, f'.mem_val h1, c1.trans c2, c3, ih d2 d1 d4⟩
  · rintro x y z ⟨_, a1, a2, a3, a4⟩ ⟨_, b1, b2, b3, b4⟩
    exact ⟨_, b1, b2.trans (a1.trans a2), a3.trans b3, b4⟩
  · rintro x h
    have ⟨x₁, y₁, a1, a2, a3⟩ := WShapeFun.LE.def'.1 hf2 _ _ (f'.mem_val h)
    have ⟨x₂, y₂, b1, b2, b3, b4⟩ := H _ _ a1
    have ⟨x₃, y₃, c1, c2, c3⟩ := WShapeFun.LE.def'.1 hf1 _ _ b1
    exact ⟨_, c1, _, c2, b2.trans a2, a3.trans (b3.trans c3), b4⟩

theorem ih_pi {b b'} {a a' : WShape n}
    (hb1 : b ≤ b') (hb2 : b' ≤ b) (ha1 : a ≤ a') (ha2 : a' ≤ a)
    (H : HasTypePi b a r) : HasTypePi b' a' r := by
  rw [HasTypePi.def] at H ⊢
  refine ⟨ih_dom ih hb1 hb2 H.1 |>.mono_r ha1 (ih ha1 ha2 H.1.isType), fun x y h => ?_⟩
  have ⟨x₁, y₁, a1, a2, a3⟩ := WShapeFun.LE.def'.1 hb2 _ _ h
  have ⟨x₂, y₂, b1, b2, b3⟩ := WShapeFun.LE.def'.1 hb1 _ _ a1
  have ⟨_, c1, c2⟩ := b.app_eq x
  exact ih (b3.trans <| b'.mem_mono b1 h (b2.trans a2)) a3 (H.2 _ _ a1)

theorem ih_lam {f f' : WShapeFun n} (hf1 : f ≤ f') (hf2 : f' ≤ f)
    (H : HasTypeLam f a b) : HasTypeLam f' a b := by
  rw [HasTypeLam.def] at H ⊢; refine ⟨H.1, ih_dom ih hf1 hf2 H.2.1, fun x y h => ?_⟩
  have ⟨x₁, y₁, a1, a2, a3⟩ := WShapeFun.LE.def'.1 hf2 _ _ h
  have ⟨x₂, y₂, b1, b2, b3⟩ := WShapeFun.LE.def'.1 hf1 _ _ a1
  have ⟨_, c1, c2⟩ := b.app_eq x
  refine .mono_r (b.app_mono_r a2) ((HasTypePi.def.1 H.1).2 _ _ c2) ?_
  exact ih (b3.trans <| f'.mem_mono b1 h (b2.trans a2)) a3 (H.2.2 _ _ a1)

end WShape.HasType.mono_l

theorem WShape.HasType.mono_l {m m' a : WShape n}
    (hm1 : m ≤ m') (hm2 : m' ≤ m) (H : HasType m a) : HasType m' a := by
  have ⟨m, mwf⟩ := m; have ⟨m', mwf'⟩ := m'; have ⟨a, awf⟩ := a
  simp only [HasType, WShape.LE.def] at *
  cases H.unfold with
  | bot => cases Shape.le_bot.1 hm2; exact H
  | sort => cases Shape.sort_le.1 hm1; exact H
  | forallE H' =>
    obtain ⟨_, _, a1, a2, ⟨⟩⟩ := Shape.forallE_le.1 hm1
    have ⟨b1, b2⟩ := Shape.forallE_le_forallE.1 hm2
    exact .forallE <| mono_l.ih_pi mono_l (b := ⟨_, mwf.2⟩) (b' := ⟨_, mwf'.2⟩)
      (a := ⟨_, mwf.1⟩) (a' := ⟨_, mwf'.1⟩) a2 b2 a1 b1 H'
  | lam H' =>
    obtain ⟨_, a1, ⟨⟩⟩ := Shape.lam_le.1 hm1; have b1 := Shape.lam_le_lam.1 hm2
    exact .lam <| mono_l.ih_lam mono_l (f := ⟨_, mwf.1⟩) (f' := ⟨_, mwf'.1⟩)
      (a := ⟨_, awf.1⟩) (b := ⟨_, awf.2⟩) hm1 hm2 H'

theorem WShape.HasDom.mono_l {f f' : WShapeFun n} : f ≤ f' → f' ≤ f →
    HasDom f a → HasDom f' a := WShape.HasType.mono_l.ih_dom WShape.HasType.mono_l

theorem WShape.HasDom.iff {f : WShapeFun n} :
    HasDom f a ↔ ∀ x, ∃ x', x' ≤ x ∧ x'.HasType a ∧ f.app x ≤ f.app x' := by
  refine WShape.HasDom.def.trans ⟨fun H x => ?_, fun H x₀ y₀ h₀ => ?_⟩
  · have ⟨x', a1, a2⟩ := WShapeFun.app_eq f x
    have ⟨x₂, y₂, b1, b2, b3, b4⟩ := H _ _ a2
    exact ⟨_, b2.trans a1, b4, .trans b3 (f.app_of_mem b1).2⟩
  · have ⟨z, h1, ⟨c, c1, c2, c3, _⟩, d, d1, d2, _, d4⟩ := find_cycle ?_ f.1 ?_ _ h₀
      (R := fun x y => ∃ z : WShape n, y.1 ≤ z.1 ∧ z.1 ≤ x.1 ∧ x.2 ≤ y.2 ∧ z.HasType a)
    · exact ⟨_, _, f.mem_val h1, c1.trans c2, c3, d4.mono_l d2 d1⟩
    · rintro x y z ⟨_, a1, a2, a3, a4⟩ ⟨_, b1, b2, b3, b4⟩
      exact ⟨_, b1, b2.trans (a1.trans a2), a3.trans b3, b4⟩
    · rintro x h
      have ⟨x', a1, a2, a3⟩ := H ⟨_, (f.2.2 _ h).1⟩
      have ⟨x₁, b1, b2⟩ := f.app_eq x'
      exact ⟨_, b2, _, b1, a1, (f.app_of_mem (f.mem_val h)).2.trans a3, a2⟩

def WShape.HasTypePi.iff {b : WShapeFun n} :
    HasTypePi b a rel ↔ HasDom b a ∧ ∀ x, x.HasType a → (b.app x).HasType (.sort rel) := by
  refine WShape.HasTypePi.def.trans <| and_congr_right fun hd =>
    ⟨fun H x h => ?_, fun H x y h => ?_⟩
  · have ⟨_, h1, h2⟩ := b.app_eq x; exact H _ _ h2
  · have ⟨h1, h2⟩ := b.app_of_mem h
    have ⟨x', a1, a2, a3⟩ := HasDom.iff.1 hd x
    exact (H _ a2).mono_l (b.app_mono_r a1 |>.trans h1) (h2.trans a3)

def WShape.HasTypePi.iff' {b : WShapeFun n} :
    HasTypePi b a rel ↔ HasDom b a ∧ ∀ x, (b.app x).HasType (.sort rel) := by
  refine WShape.HasTypePi.iff.trans <| and_congr_right fun h1 => ⟨fun H x => ?_, fun H _ _ => H _⟩
  have ⟨x', a1, a2, a3⟩ := HasDom.iff.1 h1 x
  exact (H _ a2).mono_l (WShapeFun.app_mono_r a1) a3

theorem WShape.HasTypeLam.iff {f : WShapeFun n} {a b} :
    HasTypeLam f a b ↔ HasTypePi b a true ∧ HasDom f a ∧
      ∀ x, x.HasType a → (f.app x).HasType (b.app x) := by
  refine WShape.HasTypeLam.def.trans <| and_congr_right fun hp => and_congr_right fun hd =>
    ⟨fun H x h => ?_, fun H x y h => ?_⟩
  · have ⟨_, h1, h2⟩ := f.app_eq x
    exact .mono_r (b.app_mono_r h1) ((WShape.HasTypePi.iff.1 hp).2 _ h) <| H _ _ h2
  · have ⟨h1, h2⟩ := f.app_of_mem h
    have ⟨x', a1, a2, a3⟩ := HasDom.iff.1 hd x
    have ⟨x₂, b1, b2, b3⟩ := HasDom.iff.1 hp.1 x
    exact .mono_r (b.app_mono_r a1)
      ((WShape.HasTypePi.iff.1 hp).2 _ b2 |>.mono_l (b.app_mono_r b1) b3)
      ((H _ a2).mono_l (.trans (f.app_mono_r a1) h1) (h2.trans a3))

def WShape.HasTypeLam.iff' {b : WShapeFun n} :
    HasTypeLam f a b ↔ HasTypePi b a true ∧ HasDom f a ∧ ∀ x, (f.app x).HasType (b.app x) := by
  refine WShape.HasTypeLam.iff.trans <| and_congr_right fun h1 => and_congr_right fun h2 =>
    ⟨fun H x => ?_, fun H _ _ => H _⟩
  have ⟨x', a1, a2, a3⟩ := HasDom.iff.1 h2 x
  have := (H _ a2).mono_l (WShapeFun.app_mono_r a1) a3
  exact ((HasTypePi.iff'.1 h1).2 _).mono_r (WShapeFun.app_mono_r a1) this

theorem WShape.HasTypePi.lift (le : n ≤ m) :
    HasTypePi (b.lift m) (a.lift m) rel ↔ HasTypePi (n := n) b a rel := by
  simp only [HasTypePi, WShapeFun.lift_val le, WShape.lift_val le]
  exact Shape.HasTypePi.lift le

theorem WShape.HasTypeLam.lift (le : n ≤ m) :
    HasTypeLam (f.lift m) (a.lift m) (b.lift m) ↔
    HasTypeLam (n := n) f a b := by
  simp only [HasTypeLam, WShapeFun.lift_val le, WShape.lift_val le]
  exact Shape.HasTypeLam.lift le

inductive WShape.HasTypeU : ∀ {n}, WShape n → WShape n → Prop
  | bot : HasType x .type → HasTypeU .bot x
  | sort : HasTypeU (.sort r) .type
  | forallE : HasTypePi (n := n) b a r → HasTypeU (n := n+1) (.forallE a b) (.sort r)
  | lam : HasTypeLam (n := n) f a b → HasTypeU (n := n+1) (.lam' f) (.forallE a b)

theorem WShape.HasType.unfold {m a : WShape n} (H : HasType m a) : HasTypeU m a := by
  let ⟨m, mwf⟩ := m; let ⟨a, awf⟩ := a
  dsimp only [HasType] at H
  cases H.unfold with
  | bot h => exact .bot h
  | sort => exact .sort
  | forallE h => exact .forallE (a := ⟨_, mwf.1⟩) (b := ⟨_, mwf.2⟩) h
  | lam h =>
    have := HasTypeU.lam (f := ⟨_, mwf.1⟩) (a := ⟨_, awf.1⟩) (b := ⟨_, awf.2⟩) h
    rwa [lam', dif_pos (by exact mwf.2)] at this

theorem WShape.HasType.unfold_iff {m a : WShape n} : HasType m a ↔ HasTypeU m a := by
  refine ⟨(·.unfold), fun h => ?_⟩
  cases h with
  | bot h => exact .bot h
  | sort => exact .sort
  | forallE h => exact .forallE h
  | @lam _ f a b h => unfold lam'; split <;> [exact .lam h; exact .bot (.forallE h.1)]

theorem WShape.HasType.bot' : HasType (n := n) x .type → HasType .bot x :=
  (unfold_iff.2 <| .bot ·)
theorem WShape.HasType.sort : HasType (n := n) (.sort r) .type := unfold_iff.2 .sort
theorem WShape.HasType.forallE : HasTypePi (n := n) b a r →
    HasType (n := n+1) (.forallE a b) (.sort r) := (unfold_iff.2 <| .forallE ·)
theorem WShape.HasType.lam : HasTypeLam (n := n) f a b →
    HasType (n := n+1) (.lam' f) (.forallE a b) := (unfold_iff.2 <| .lam ·)

theorem WShape.HasTypePi.toType (H : HasTypePi (n := n) b a r) : HasTypePi (n := n) b a true :=
  ⟨H.1, fun _ _ h' => (H.2 _ _ h').toType⟩

theorem WShape.HasType.lam_isType {f : WShapeFun n} {hf} :
    ¬HasType (WShape.lam f hf) (.sort r) := nofun

theorem WShape.HasType.bot : HasType (n := n) x (.sort r) → HasType .bot x := (.bot' ·.toType)

theorem WShape.HasType.bot_r (H : HasType (n := n) x .bot) : x = .bot := by
  cases n <;> cases H.unfold <;> rfl

theorem WShape.HasType.bot_iff : HasType (n := n) .bot x ↔ HasType x .type := ⟨.isType, .bot'⟩

theorem WShape.HasDom.bot_iff {a : WShape n} : HasDom .bot a ↔ a.HasType .type := by
  simp [HasDom.def, WShapeFun.mem_bot, HasType.bot_iff]

theorem WShape.HasDom.bot : a.HasType .type → HasDom .bot a := bot_iff.2

theorem WShape.HasTypeLam.bot {b : WShapeFun n} : HasTypeLam .bot a b ↔ HasTypePi b a true := by
  simp only [HasTypeLam.def, WShapeFun.mem_bot, and_imp, forall_eq_apply_imp_iff,
    forall_eq, and_iff_left_iff_imp]
  exact fun h => ⟨.bot (HasDom.isType h.1), .bot' ((HasTypePi.iff'.1 h).2 _)⟩

theorem WShape.HasType.lift (h : n ≤ n') :
    HasType (m.lift n') (a.lift n') ↔ HasType (n := n) m a := by
  simp only [HasType, lift_val h]; exact Shape.HasType.lift h

theorem WShape.HasType.forallE_l {a : WShape n} {f : WShapeFun n} :
    HasType (.forallE a f) t ↔ ∃ r, HasTypePi f a r ∧ t = .sort r := by
  simp only [HasType, WShape.forallE, HasTypePi, WShape.sort,
    WShape.ext_iff, Shape.HasType.unfold_iff]
  generalize a.1 = a₁, f.1 = f₁, t.1 = t₁
  refine ⟨fun (.forallE H) => ⟨_, H, rfl⟩, fun ⟨_, H, eq⟩ => eq ▸ .forallE H⟩

theorem WShape.HasType.forallE_inv {m : WShape (n+1)} {a : WShape n} {f : WShapeFun n}
    (H : HasType m (.forallE a f)) : ∃ g, m = .lam' g ∧ HasTypeLam g a f := by
  generalize eq : a.forallE f = a' at H
  cases H.unfold with
  | bot H' =>
    refine ⟨.bot, by simp, ?_⟩; subst eq
    obtain ⟨_, H, ⟨⟩⟩ := HasType.forallE_l.1 H'
    simp [HasTypeLam.def, WShapeFun.mem_bot, HasDom.def]
    have ⟨h1, h2⟩ := HasTypePi.iff.1 H
    exact have := .bot h1.isType; ⟨H, this, .bot (h2 _ this)⟩
  | lam H' => obtain ⟨rfl, rfl⟩ := forallE.inj.1 eq; exact ⟨_, rfl, H'⟩
  | _ => cases congrArg (·.1) eq

theorem WShape.HasType.join {m₁ m₂ a : WShape n} (hJ : m₁.Compat m₂)
    (h1 : m₁.HasType a) (h2 : m₂.HasType a) : (m₁.join m₂).HasType a := by
  obtain ⟨m₁, wf₁⟩ := m₁; obtain ⟨m₂, wf₂⟩ := m₂; obtain ⟨a, wf'⟩ := a
  simp [HasType, WShape.join_val hJ, Compat] at h1 h2 hJ ⊢
  cases n with
  | zero =>
    cases m₂ with | bot => exact h1 | sort
    cases m₁ with | bot => exact h2 | sort
    simp only [Shape.Compat, decide_eq_true_eq] at hJ
    simpa only [Shape.join, hJ]
  | succ n
  have ih := @join n
  let rec go_dom {a a' : WShape n} {f f' : WShapeFun n}
      (hf : f.Compat f') (ha : a.Compat a')
      (h1 : WShape.HasDom f a) (h2 : WShape.HasDom f' a') :
      WShape.HasDom (f.join f') (a.join a') := by
    rw [WShape.HasDom.iff] at h1 h2 ⊢
    have hJa := WShape.Join.mk ha
    have hJf := WShapeFun.Join.mk hf
    intro x
    have ⟨x₁, a1, a2, a3⟩ := h1 x
    have ⟨x₂, b1, b2, b3⟩ := h2 x
    have hcx := Compat.iff.2 ⟨_, a1, b1⟩; have hjx := WShape.Join.mk hcx
    have ajt := ih ha a2.isType b2.isType
    have := ih hcx (.mono_r hJa.le.1 ajt a2) (.mono_r hJa.le.2 ajt b2)
    refine ⟨_, (hjx _).2 ⟨a1, b1⟩, this, ?_⟩
    refine (hJf.app_l x _).2 ⟨a3.trans ?_, b3.trans ?_⟩
    · exact (WShapeFun.app_mono_r hjx.le.1).trans (hJf.app_l _).le.1
    · exact (WShapeFun.app_mono_r hjx.le.2).trans (hJf.app_l _).le.2
  let rec go_pi {a a' : WShape n} {b b' : WShapeFun n} {r}
      (ha : a.Compat a') (hb : b.Compat b')
      (h1 : WShape.HasTypePi b a r) (h2 : WShape.HasTypePi b' a' r) :
      WShape.HasTypePi (b.join b') (a.join a') r := by
    rw [WShape.HasTypePi.iff'] at h1 h2 ⊢
    have hJa := WShape.Join.mk ha
    have hJb := WShapeFun.Join.mk hb
    refine ⟨go_dom hb ha h1.1 h2.1, fun x => ?_⟩
    have ⟨a1, a2, a3⟩ := Join.iff.1 (hJb.app_l x)
    exact ih a1 (h1.2 _) (h2.2 _) |>.mono_l a2 a3
  let rec go_lam {f f' : WShapeFun n} {a b} (hf : f.Compat f')
      (h1 : WShape.HasTypeLam f a b) (h2 : WShape.HasTypeLam f' a b) :
      WShape.HasTypeLam (f.join f') a b := by
    rw [WShape.HasTypeLam.iff'] at h1 h2 ⊢
    have := Join.iff.1 <| (join_self (x := a)).2 ⟨.rfl, .rfl⟩
    refine ⟨h1.1, go_dom hf .rfl h1.2.1 h2.2.1 |>.mono_r this.2.1 h1.2.1.isType, fun x => ?_⟩
    have hJf := WShapeFun.Join.mk hf
    have ⟨a1, a2, a3⟩ := Join.iff.1 (hJf.app_l x)
    exact ih a1 (h1.2.2 _) (h2.2.2 _) |>.mono_l a2 a3
  cases h1.unfold with
  | bot => exact h2
  | sort =>
    (cases m₂ with | bot => exact h1 | _) <;>
      simp only [Shape.Compat, decide_eq_true_eq, Bool.false_eq_true] at hJ
    simpa only [Shape.join, hJ]
  | forallE h1' =>
    (cases h2.unfold with | bot => exact h1 | forallE h2' | _) <;>
      simp only [Shape.Compat, Bool.false_eq_true, Bool.and_eq_true] at hJ
    have := go_pi (b := ⟨_, wf₁.2⟩) (b' := ⟨_, wf₂.2⟩)
      (a := ⟨_, wf₁.1⟩) (a' := ⟨_, wf₂.1⟩) hJ.1 hJ.2 h1' h2'
    rw [HasTypePi, WShape.join_val (by exact hJ.1), WShapeFun.join_val (by exact hJ.2)] at this
    exact .forallE this
  | lam h1' =>
    (cases h2.unfold with | bot => exact h1 | lam h2' | _) <;> simp only [Shape.Compat] at hJ
    have := go_lam (f := ⟨_, wf₁.1⟩) (f' := ⟨_, wf₂.1⟩)
      (a := ⟨_, wf'.1⟩) (b := ⟨_, wf'.2⟩) hJ h1' h2'
    rw [HasTypeLam, WShapeFun.join_val (by exact hJ)] at this
    exact .lam this

theorem WShape.HasDom.join {a a' : WShape n} {f f' : WShapeFun n} :
    f.Compat f' → a.Compat a' → HasDom f a → HasDom f' a' →
    HasDom (f.join f') (a.join a') := HasType.join.go_dom _ HasType.join

theorem WShape.HasType.join' {m₁ m₂ m a : WShape n} (hJ : m₁.Join m₂ m)
    (h1 : m₁.HasType a) (h2 : m₂.HasType a) : m.HasType a :=
  have ⟨a1, a2, a3⟩ := Join.iff.1 hJ
  h1.join a1 h2 |>.mono_l a2 a3

theorem WShape.HasDom.join' (h1 : HasDom f₁ a₁) (h2 : HasDom f₂ a₂)
    (hJ : WShapeFun.Join f₁ f₂ h') (hJa : WShape.Join a₁ a₂ a') : HasDom h' a' := by
  have ⟨a1, a2, a3⟩ := WShapeFun.Join.iff.1 hJ
  have ⟨b1, b2, b3⟩ := WShape.Join.iff.1 hJa
  have := h1.join a1 b1 h2 |>.mono_l a2 a3
  exact this.mono_r b2 <| this.isType.mono_l b2 b3

def TShape.HasType (x y : TShape) : Prop := (x.2.lift (max x.1 y.1)).HasType (y.2.lift _)

theorem TShape.HasType.def {x y : TShape} (h1 : x.1 ≤ m) (h2 : y.1 ≤ m) :
    x.HasType y ↔ (x.2.lift m).HasType (y.2.lift m) := by
  refine (WShape.HasType.lift (Nat.max_le.2 ⟨h1, h2⟩)).symm.trans ?_
  rw [WShape.lift_lift (.inl (Nat.le_max_left ..)), WShape.lift_lift (.inl (Nat.le_max_right ..))]

theorem WShape.HasType.T_iff {x y : WShape n} : x.T.HasType y.T ↔ x.HasType y := by
  refine (TShape.HasType.def (x := x.T) (y := y.T) (Nat.le_refl _) (Nat.le_refl _)).trans ?_
  simp [WShape.HasType, WShape.lift_self]

theorem WShape.HasType.T {x y : WShape n} : x.HasType y → x.T.HasType y.T := T_iff.2

theorem TShape.HasType.bot_r (H : HasType x .bot) : x ≤ .bot := by
  simp only [TShape.HasType, bot, WShape.lift_bot] at H
  have h := WShape.HasType.bot_r H
  simp only [TShape.LE.def', bot, WShape.lift_bot]
  exact (h : x.2.lift _ = .bot) ▸ WShape.LE.rfl

theorem TShape.HasType.mono_r {m a a' : TShape} (ha : a ≤ a')
    (h1 : HasType a' (.sort r)) (h2 : HasType m a) : HasType m a' := by
  let k := max (max m.1 a.1) a'.1
  have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
  have h1 := (TShape.HasType.def hk.2 (Nat.zero_le _)).1 h1
  have h2 := (TShape.HasType.def hk.1.1 hk.1.2).1 h2
  have ha := (TShape.LE.def hk.1.2 hk.2).1 ha
  exact (TShape.HasType.def hk.1.1 hk.2).2 (h1.mono_r ha h2)

theorem TShape.HasType.bot : HasType x (.sort r) → HasType .bot x := by
  rw [TShape.HasType.def (Nat.le_refl _) (Nat.zero_le _),
    TShape.HasType.def (Nat.zero_le _) (Nat.le_refl _)]
  simp [sort]; exact .bot

theorem TShape.HasType.bot' : HasType x .type → HasType .bot x := .bot

theorem TShape.HasType.sort : HasType (.sort r) .type := by
  simp [HasType, TShape.sort, TShape.type, WShape.lift_sort, WShape.HasType]
  exact WShape.HasType.sort

theorem TShape.HasType.join' (hJ : Join m₁ m₂ m)
    (h1 : HasType m₁ a) (h2 : HasType m₂ a) : HasType m a := by
  let k := max (max m₁.1 m₂.1) (max m.1 a.1)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  have h1 := (TShape.HasType.def hk.1.1 hk.2.2).1 h1
  have h2 := (TShape.HasType.def hk.1.2 hk.2.2).1 h2
  have hJ := (TShape.Join.def hk.1.1 hk.1.2 hk.2.1).1 hJ
  exact (TShape.HasType.def hk.2.1 hk.2.2).2 (h1.join' hJ h2)

theorem TShape.HasType.bot_r' (ha : a ≤ .bot) (H : HasType x a) : x ≤ .bot :=
  (mono_r (r := true) ha (.bot' .sort) H).bot_r

inductive LE_Forall {n} : TShape → WShape n → WShapeFun n → Prop where
  | bot : a ≤ .bot → LE_Forall a b f
  | forallE : b'.T ≤ b.T → TShapeFun.LE (n := m) f' f →
    LE_Forall (WShape.T (n := m+1) (.forallE b' f')) b f

theorem TShape.LE.le_forall (ha : a ≤ WShape.T (n := n+1) (.forallE b f)) :
    LE_Forall a b f := by
  by_cases h : a ≤ .bot; · exact .bot h
  obtain ⟨an, aw⟩ := a
  cases an with
  | zero =>
    exfalso; apply h; rw [TShape.le_bot]
    have hle := (TShape.LE.def (Nat.zero_le _) (Nat.le_refl _)).1 ha
    have hle_raw : (aw.lift _).1 ≤ ((WShape.forallE b f).lift _).1 := hle
    rw [WShape.lift_val (Nat.zero_le _), WShape.lift_val (Nat.le_refl _)] at hle_raw
    obtain ⟨val, wf⟩ := aw
    cases val with | bot => rfl | sort r
    simp [Shape.lift, WShape.forallE, Shape.LE.def] at hle_raw
  | succ m =>
    have hle := (TShape.LE.def (Nat.succ_le_succ (Nat.le_max_left m n))
        (Nat.succ_le_succ (Nat.le_max_right m n))).1 ha
    have hle_raw : (aw.lift _).1 ≤ ((WShape.forallE b f).lift _).1 := hle
    rw [WShape.lift_val (Nat.succ_le_succ (Nat.le_max_left m n)),
        WShape.lift_val (Nat.succ_le_succ (Nat.le_max_right m n))] at hle_raw
    simp only [WShape.forallE, Shape.lift] at hle_raw
    obtain ⟨val, wf⟩ := aw
    cases val with
    | bot => exfalso; apply h; rw [TShape.le_bot]; rfl
    | forallE b' f' =>
      simp [Shape.lift, Shape.LE.def] at hle_raw
      let b'w : WShape m := ⟨b', wf.1⟩; let f'w : WShapeFun m := ⟨f', wf.2⟩
      have le₁ := Nat.le_max_left m n; have le₂ := Nat.le_max_right m n
      refine .forallE
        ((TShape.LE.def le₁ le₂).2 (?_ : (b'w.lift _).1 ≤ (b.lift _).1))
        ((TShapeFun.LE.def le₁ le₂).2 (?_ : (f'w.lift _).1.LE (f.lift _).1))
      · rw [WShape.lift_val le₁, WShape.lift_val le₂]; exact hle_raw.1
      · rw [WShapeFun.lift_val le₁, WShapeFun.lift_val le₂]; exact hle_raw.2
    | _ => simp [Shape.lift, Shape.LE.def] at hle_raw

def TShape.HasTypeLam (f : WShapeFun n) (a : WShape m) (b : WShapeFun m) :=
  WShape.HasTypeLam (f.lift (max n m)) (a.lift (max n m)) (b.lift (max n m))

theorem TShape.HasTypeLam.def (le₁ : n ≤ k) (le₂ : m ≤ k) :
    HasTypeLam (n := n) (m := m) f a b ↔
    WShape.HasTypeLam (f.lift k) (a.lift k) (b.lift k) := by
  rw [TShape.HasTypeLam, ← WShape.HasTypeLam.lift (Nat.max_le.2 ⟨le₁, le₂⟩),
    WShapeFun.lift_lift (.inl (Nat.le_max_left ..)), WShape.lift_lift (.inl (Nat.le_max_right ..)),
    WShapeFun.lift_lift (.inl (Nat.le_max_right ..))]

theorem TShape.HasType.ty_forallE_inv
    {x : TShape} (H : x.HasType (WShape.T (n := m+1) (.forallE b f))) :
    x = .bot ∨ ∃ n g, x = WShape.T (n := n+1) (.lam' g) ∧ TShape.HasTypeLam g b f := by
  refine have le₁ := Nat.le_succ_of_le (Nat.le_max_left ..)
    have le₂ := Nat.succ_le_succ (Nat.le_max_right ..)
    have H := (TShape.HasType.def le₁ le₂).1 H; ?_
  rw [WShape.lift_forallE (Nat.le_of_succ_le_succ le₂)] at H
  have ⟨g, hg, htl⟩ := WShape.HasType.forallE_inv H
  obtain ⟨_|n, x⟩ := x
  · unfold WShape.lam' at hg; split at hg
    · obtain ⟨⟨⟩, _⟩ := x <;> cases congrArg (·.1) hg
    · dsimp at le₁; cases (WShape.lift_eq_bot le₁).1 hg; exact .inl rfl
  refine .inr ⟨n, ?_⟩; dsimp at *
  obtain ⟨rfl, h⟩ | ⟨g, rfl, rfl⟩ := WShape.lift_eq_lam' (Nat.le_of_succ_le_succ le₁) hg
  · refine ⟨.bot, by simp, ?_⟩
    rw [HasTypeLam, WShapeFun.lift_bot, ← WShapeFun.lift_bot,
      WShape.HasTypeLam.lift (Nat.le_max_right ..), WShape.HasTypeLam.bot]
    obtain ⟨_, h, _⟩ := WShape.HasType.forallE_l.1 <| WShape.HasType.bot_iff.1 H
    exact (WShape.HasTypePi.lift (Nat.le_of_succ_le_succ le₂)).1 h |>.toType
  · exact ⟨_, rfl, (HasTypeLam.def (by omega) (by omega)).2 htl⟩

theorem TShape.HasType.mono_l {m a : TShape}
    (hm1 : m ≤ m') (hm2 : m' ≤ m) (H : HasType m a) : HasType m' a := by
  let k := max (max m.1 a.1) m'.1
  have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
  have H := (TShape.HasType.def hk.1.1 hk.1.2).1 H
  have hm1 := (TShape.LE.def hk.1.1 hk.2).1 hm1
  have hm2 := (TShape.LE.def hk.2 hk.1.1).1 hm2
  exact (TShape.HasType.def hk.2 hk.1.2).2 (H.mono_l hm1 hm2)

theorem TShape.HasType.sort_T : HasType (WShape.T (n := n) (.sort r)) .type :=
  mono_l TShape.sort_eqv.2 TShape.sort_eqv.1 .sort

theorem TShape.HasType.sort_r {x : WShape n} : x.T.HasType (.sort r) ↔ x.HasType (.sort r) :=
  .trans ⟨mono_r TShape.sort_eqv.2 .sort_T, mono_r TShape.sort_eqv.1 .sort⟩ WShape.HasType.T_iff

theorem TShape.HasType.bot_T (H : HasType x (.sort r)) : HasType (WShape.T (n := n) .bot) x :=
  H.bot.mono_l bot_eqv.2 bot_eqv.1
theorem TShape.HasType.bot_T' (H : HasType x .type) : HasType (WShape.T (n := n) .bot) x := H.bot_T

theorem WShape.HasType.proofIrrel
    (ha : HasType (n := n) a .prop) (hx : HasType x a) : x = .bot := by
  cases n with | zero => cases ha.unfold; exact hx.bot_r | succ n
  cases ha.unfold with | bot => exact hx.bot_r | @forallE _ b a _ ha
  generalize eq : WShape.forallE .. = t at hx
  cases hx.unfold with | bot => rfl | @lam _ f a' b' hx' => ?_ | _ => cases eq
  obtain ⟨rfl, rfl⟩ : a = a' ∧ b = b' := by
    cases a'; cases b'; cases congrArg (·.1) eq; exact ⟨rfl, rfl⟩
  unfold lam'; split <;> [rename_i hf; rfl]
  obtain ⟨⟨x, y⟩, h1, h2⟩ := hf; have ⟨hx, hy⟩ := f.2.2 _ h1; change (⟨x,hx⟩, ⟨y,hy⟩) ∈ f at h1
  have ⟨x', a1, a2, a3⟩ := WShape.HasDom.iff.1 hx'.2.1 ⟨x, hx⟩
  have hfx := (WShape.HasTypeLam.iff.1 hx').2.2 x' a2
  have hba := (WShape.HasTypePi.iff.1 ha).2 x' a2
  cases h2 <| (f.app_of_mem h1).2.trans <| a3.trans <| le_bot.2 <| proofIrrel hba hfx

theorem TShape.HasType.proofIrrel
    (ha : HasType a (.sort false)) (hx : HasType x a) : x ≤ .bot := by
  let k := max x.1 a.1; have hk := Nat.max_le.1 (Nat.le_refl k)
  have ha' := (TShape.HasType.def hk.2 (Nat.zero_le _)).1 ha
  have hx' := (TShape.HasType.def hk.1 hk.2).1 hx
  simp [TShape.sort] at ha'
  have := ha'.proofIrrel hx'
  rw [TShape.LE.def hk.1 (Nat.zero_le _)]
  simp [TShape.bot, WShape.lift_bot, this]

theorem WShape.HasType.retype (ha : HasType (n := n) a (.sort r))
    (ha' : HasType a' (.sort r')) (le : a ≤ a') : HasType a (.sort r') := by
  cases n with
  | zero =>
    cases ha.unfold with
    | bot => exact .bot .sort
    | sort => exact sort_le.1 le ▸ ha'
  | succ n
  cases ha.unfold with
  | bot => exact .bot .sort
  | sort => exact sort_le.1 le ▸ ha'
  | forallE Ha
  obtain ⟨_, _, le₁, le₂, rfl⟩ := WShape.forallE_le.1 le
  have ⟨H1, H2⟩ := HasTypePi.iff'.1 Ha
  obtain ⟨_, Ha', ⟨⟩⟩ := forallE_l.1 ha'
  refine .forallE <| HasTypePi.iff'.2 ⟨H1, fun x => ?_⟩
  exact retype (H2 _) ((HasTypePi.iff'.1 Ha').2 x) (WShapeFun.app_mono_l le₂ _)

theorem TShape.HasType.retype (ha : HasType a (.sort r))
    (ha' : HasType a' (.sort r')) (le : a ≤ a') : HasType a (.sort r') := by
  let k := max a.1 a'.1; have hk := Nat.max_le.1 (Nat.le_refl k)
  have ha := (TShape.HasType.def hk.1 (Nat.zero_le _)).1 ha
  have ha' := (TShape.HasType.def hk.2 (Nat.zero_le _)).1 ha'
  exact (TShape.HasType.def hk.1 (Nat.zero_le _)).2 <| ha.retype ha' le

theorem WShape.HasDom.single :
    HasDom (WShapeFun.single x y) a ↔ x.HasType a ∨ y ≤ .bot ∧ a.HasType .type := by
  simp [HasDom.def, WShapeFun.mem_single]
  refine ⟨fun H => ?_, ?_⟩
  · obtain ⟨x, y, ⟨rfl, rfl⟩ | ⟨h, rfl, rfl⟩, h2, h3, h4⟩ := H _ _ (.inl ⟨rfl, rfl⟩)
    · exact .inl h4
    · exact .inr ⟨h3, h4.isType⟩
  · rintro H x y (⟨rfl, rfl⟩ | ⟨h, rfl, rfl⟩)
    · obtain h | ⟨h1, h2⟩ := H
      · exact ⟨_, _, .inl ⟨rfl, rfl⟩, .rfl, .rfl, h⟩
      · by_cases hx : x ≤ .bot
        · exact ⟨_, _, .inl ⟨rfl, rfl⟩, .rfl, .rfl, le_bot.1 hx ▸ .bot' h2⟩
        · exact ⟨_, _, .inr ⟨hx, rfl, rfl⟩, bot_le, h1, .bot' h2⟩
    · refine ⟨_, _, .inr ⟨h, rfl, rfl⟩, .rfl, .rfl, .bot' ?_⟩
      obtain h | ⟨_, h⟩ := H <;> [exact h.isType; exact h]
