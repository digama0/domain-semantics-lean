import DomainSemantics.Basic

/-! # Lifts on de Bruijn indices

This file defines `Lift`, a compact term-level representation of the
weakening / extension transformations applied to de Bruijn indices when
crossing binders. A `Lift` is a sequence of `skip` (insert a fresh
variable) and `cons` (pin variable 0, recurse) constructors built from a
`refl` base, and is evaluated by `liftVar : Lift → Nat → Nat`.

`Lift` and its operations (`comp`, `consN`, `depth`) are the bookkeeping
device that lets every later weakening lemma (`Lookup.weak'`,
`IsDefEq.weak'`, `Ctx.Lift'`, …) be parameterised uniformly. -/

namespace DomainSemantics

/-- A *lift* is a transformation on de Bruijn indices, built from:
* `refl`: identity on indices;
* `skip l`: under-the-binder shift — bumps every index in the codomain by
  one (i.e. introduces a fresh variable);
* `cons l`: pointwise extension under one extra binder (variable `0` is
  pinned and indices `i+1` go through `l`).
Lifts compose under `comp`. `liftVar` evaluates a lift on a single index. -/
inductive Lift : Type where
  | refl : Lift
  | skip : Lift → Lift
  | cons : Lift → Lift

namespace Lift

/-- `consN l k` applies `cons` to `l` exactly `k` times — i.e. pins the first
`k` variables and passes the rest through `l`. -/
@[simp] def consN (l : Lift) : Nat → Lift
  | 0  => l
  | k+1 => .cons (consN l k)

/-- Composition of lifts: `comp l₁ l₂` is the lift that first applies `l₁`
to an index and then `l₂`. The pattern-matching unfolds by *outermost*
constructor of `l₂`. -/
@[simp] def comp (l₁ l₂ : Lift) : Lift :=
  match l₂, l₁ with
  | .refl,    l₁       => l₁
  | .skip l₂, l₁       => .skip (l₁.comp l₂)
  | .cons l₂, .refl    => .cons l₂
  | .cons l₂, .skip l₁ => .skip (l₁.comp l₂)
  | .cons l₂, .cons l₁ => .cons (l₁.comp l₂)

@[simp] theorem refl_comp : comp refl l = l := by induction l <;> simp [*]

/-- The number of `skip` constructors in a lift — i.e. the net shift it
applies to large indices. A lift of depth zero acts as the identity. -/
@[simp] def depth : Lift → Nat
  | .refl   => 0
  | .skip l => l.depth + 1
  | .cons l => l.depth

@[simp] protected def liftVar : Lift → Nat → Nat
  | .refl, n => n
  | .skip l, n => l.liftVar n + 1
  | .cons _, 0 => 0
  | .cons l, n+1 => l.liftVar n + 1

theorem liftVar_comp : (comp l₁ l₂).liftVar n = l₂.liftVar (l₁.liftVar n) := by
  induction l₂ generalizing l₁ n <;> [skip; skip; cases l₁ <;> [skip; skip; cases n]] <;> simp [*]

theorem liftVar_depth_zero (H : depth l = 0) : l.liftVar n = n := by
  induction l generalizing n <;> [skip; skip; cases n] <;> simp_all [depth]
