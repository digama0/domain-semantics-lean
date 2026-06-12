import DomainSemantics.Basic

namespace DomainSemantics

inductive Lift : Type where
  | refl : Lift
  | skip : Lift → Lift
  | cons : Lift → Lift

namespace Lift

@[simp] def consN (l : Lift) : Nat → Lift
  | 0  => l
  | k+1 => .cons (consN l k)

@[simp] def comp (l₁ l₂ : Lift) : Lift :=
  match l₂, l₁ with
  | .refl,    l₁       => l₁
  | .skip l₂, l₁       => .skip (l₁.comp l₂)
  | .cons l₂, .refl    => .cons l₂
  | .cons l₂, .skip l₁ => .skip (l₁.comp l₂)
  | .cons l₂, .cons l₁ => .cons (l₁.comp l₂)

@[simp] theorem refl_comp : comp refl l = l := by induction l <;> simp [*]

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

end Lift

end DomainSemantics
