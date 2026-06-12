import DomainSemantics.Basic

namespace DomainSemantics

def liftVar (n i : Nat) (k := 0) : Nat := if i < k then i else n + i

theorem liftVar_lt (h : i < k) : liftVar n i k = i := if_pos h
theorem liftVar_le (h : k ≤ i) : liftVar n i k = n + i := if_neg (Nat.not_lt.2 h)

theorem liftVar_base : liftVar n i = n + i := liftVar_le (Nat.zero_le _)
@[simp] theorem liftVar_base' : liftVar n i = i + n := Nat.add_comm .. ▸ liftVar_le (Nat.zero_le _)

@[simp] theorem liftVar_zero : liftVar n 0 (k+1) = 0 := by simp [liftVar]
@[simp] theorem liftVar_succ : liftVar n (i+1) (k+1) = liftVar n i k + 1 := by
  simp [liftVar, Nat.succ_lt_succ_iff]; split <;> simp [Nat.add_assoc]

theorem liftVar_lt_add (self : i < k) : liftVar n i j < k + n := by
  simp [liftVar]
  split <;> rename_i h
  · exact Nat.lt_of_lt_of_le self (Nat.le_add_right ..)
  · rw [Nat.add_comm]; exact Nat.add_lt_add_right self _

inductive Lift : Type where
  | refl : Lift
  | skip : Lift → Lift
  | cons : Lift → Lift

namespace Lift

@[simp] def skipN (l : Lift) : Nat → Lift
  | 0   => l
  | n+1 => .skip (skipN l n)

theorem skipN_one : skipN l 1 = .skip l := rfl

theorem skipN_skipN : skipN (skipN l n) k = skipN l (n + k) := by induction k <;> simp [*]

@[simp] def consN (l : Lift) : Nat → Lift
  | 0  => l
  | k+1 => .cons (consN l k)

theorem consN_consN : consN (.consN l a) b = .consN l (a + b) := by
  induction b <;> simp [*]

@[simp] def comp (l₁ l₂ : Lift) : Lift :=
  match l₂, l₁ with
  | .refl,    l₁       => l₁
  | .skip l₂, l₁       => .skip (l₁.comp l₂)
  | .cons l₂, .refl    => .cons l₂
  | .cons l₂, .skip l₁ => .skip (l₁.comp l₂)
  | .cons l₂, .cons l₁ => .cons (l₁.comp l₂)

@[simp] theorem refl_comp : comp refl l = l := by induction l <;> simp [*]

theorem consN_comp : consN (.comp l₁ l₂) n = .comp (.consN l₁ n) (.consN l₂ n) := by
  induction n <;> simp [*]

@[simp] def dom : Lift → Nat
  | .refl   => 0
  | .skip l => l.dom
  | .cons l => l.dom + 1

@[simp] def size : Lift → Nat
  | .refl   => 0
  | .skip l => l.size + 1
  | .cons l => l.size + 1

@[simp] def depth : Lift → Nat
  | .refl   => 0
  | .skip l => l.depth + 1
  | .cons l => l.depth

theorem dom_add_depth : dom l + depth l = size l := by induction l <;> simp! <;> omega

theorem depth_comp : depth (.comp l₁ l₂) = l₁.depth + l₂.depth :=
  match l₂, l₁ with
  | .refl,    _        => rfl
  | .skip _,  _        => congrArg Nat.succ depth_comp
  | .cons _,  .refl    => (Nat.zero_add _).symm
  | .cons _,  .skip _  => (congrArg Nat.succ depth_comp).trans (Nat.succ_add ..).symm
  | .cons l₂, .cons l₁ => @depth_comp l₁ l₂

@[simp] theorem depth_consN : depth (.consN l n) = l.depth := by induction n <;> simp [*]

@[simp] theorem depth_skipN : depth (.skipN l n) = l.depth + n := by
  induction n <;> simp [Nat.add_assoc, *]

theorem consN_skip_eq : consN (skip l) k = comp (consN l k) (consN (skip refl) k) := by
  rw [← consN_comp]; rfl

theorem depth_succ (H : l.depth = n + 1) :
    ∃ l' k, depth l' = n ∧ l = consN (.skip l') k := by
  match l with
  | .skip l => cases H; exact ⟨l, 0, rfl, rfl⟩
  | .cons l =>
    obtain ⟨l, k, rfl, ⟨⟩⟩ := depth_succ (l := l) H
    exact ⟨l, k+1, rfl, rfl⟩

theorem depth_succ' (H : l.depth = n + 1) :
    ∃ l' k, depth l' = n ∧ l = comp l' (.consN (.skip refl) k) := by
  let ⟨l', k, h1, h2⟩ := depth_succ H
  exact ⟨.consN l' k, k, by simp [h1], by rwa [← consN_skip_eq]⟩

theorem comp_skipN : comp l₁ (skipN l₂ k) = skipN (comp l₁ l₂) k := by
  induction k <;> simp [*]

theorem skipN_comp_consN : comp (skipN l₁ k) (consN l₂ k) = skipN (comp l₁ l₂) k := by
  induction k <;> simp [*]

@[simp] protected def liftVar : Lift → Nat → Nat
  | .refl, n => n
  | .skip l, n => l.liftVar n + 1
  | .cons _, 0 => 0
  | .cons l, n+1 => l.liftVar n + 1

theorem liftVar_comp : (comp l₁ l₂).liftVar n = l₂.liftVar (l₁.liftVar n) := by
  induction l₂ generalizing l₁ n <;> [skip; skip; cases l₁ <;> [skip; skip; cases n]] <;> simp [*]

theorem liftVar_skipN : (skipN l n).liftVar i = l.liftVar i + n := by
  induction n generalizing i with
  | zero => rfl
  | succ _ ih => simp [ih]; rfl

theorem liftVar_consN_skipN : (consN (skipN refl n) k).liftVar i = liftVar n i k := by
  induction k generalizing i with
  | zero => simp [liftVar_skipN]
  | succ k ih =>
    cases i with simp [liftVar, Nat.succ_lt_succ_iff, ih]
    | succ i => split <;> rfl

theorem liftVar_depth_zero (H : depth l = 0) : l.liftVar n = n := by
  induction l generalizing n <;> [skip; skip; cases n] <;> simp_all [depth]

theorem le_liftVar {l : Lift} : n ≤ l.liftVar n := by
  induction l generalizing n <;> [skip; skip; cases n] <;> simp_all; grind

def inter : Lift → Lift → Lift
  | refl, l | l, refl => l
  | skip l₁, skip l₂ | skip l₁, cons l₂ | cons l₁, skip l₂ => skip (l₁.inter l₂)
  | cons l₁, cons l₂ => cons (l₁.inter l₂)

theorem inter_self : inter l l = l := by induction l <;> simp! [*]

theorem inter_comm : inter l₁ l₂ = inter l₂ l₁ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp! [*]

theorem inter_assoc : inter (inter l₁ l₂) l₃ = inter l₁ (inter l₂ l₃) := by
  induction l₁ generalizing l₂ l₃ <;> cases l₂ <;> cases l₃ <;> simp! [*]

@[simp] def diff : Lift → Lift → Lift
  | refl, _ => refl
  | l, refl => l
  | skip l₁, skip l₂ | cons l₁, skip l₂ => diff l₁ l₂
  | skip l₁, cons l₂ => skip (diff l₁ l₂)
  | cons l₁, cons l₂ => cons (l₁.diff l₂)

@[simp] theorem diff_refl : diff l refl = l := by cases l <;> simp!

theorem diff_comp : comp (diff l₁ l₂) l₂ = inter l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp! [*]

def Fixes : Nat → Lift → Prop
  | 0,   _       => True
  | _,   .refl   => True
  | _+1, .skip _ => False
  | n+1, .cons l => Fixes n l

theorem Fixes.zero : Fixes 0 ρ := by simp [Fixes]

theorem Fixes.liftVar_eq {ρ : Lift} (H : ρ.Fixes k) (h2 : i < k) : ρ.liftVar i = i := by
  induction ρ generalizing i k with
  | refl => rfl
  | skip => let k+1 := k; cases H
  | cons ρ ih =>
    let k+1 := k
    cases i with
    | zero => rfl
    | succ k => exact congrArg Nat.succ <| ih H (Nat.lt_of_succ_lt_succ h2)

end Lift

end DomainSemantics
