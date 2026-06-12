import Lean
import DomainSemantics.VLevel
import DomainSemantics.Lift

namespace DomainSemantics

inductive VExpr where
  | bvar (deBruijnIndex : Nat)
  | sort (u : Bool)
  | app (fn arg : VExpr)
  | lam (binderType body : VExpr)
  | forallE (binderType body : VExpr)

instance : Inhabited VExpr := ⟨.sort false⟩


namespace VExpr

variable (n : Nat) in
def liftN : VExpr → (k :_:= 0) → VExpr
  | .bvar i, k => .bvar (liftVar n i k)
  | .sort u, _ => .sort u
  | .app fn arg, k => .app (fn.liftN k) (arg.liftN k)
  | .lam ty body, k => .lam (ty.liftN k) (body.liftN (k+1))
  | .forallE ty body, k => .forallE (ty.liftN k) (body.liftN (k+1))

abbrev lift := liftN 1

@[simp] theorem liftN_zero (e : VExpr) (k : Nat) : liftN 0 e k = e := by
  induction e generalizing k <;> simp [liftN, liftVar, *]

theorem liftN'_liftN' {e : VExpr} {n1 n2 k1 k2 : Nat} (h1 : k1 ≤ k2) (h2 : k2 ≤ n1 + k1) :
    liftN n2 (liftN n1 e k1) k2 = liftN (n1+n2) e k1 := by
  induction e generalizing k1 k2 with simp [liftN, liftVar, Nat.add_assoc, *]
  | bvar i =>
    split <;> rename_i h
    · rw [if_pos (Nat.lt_of_lt_of_le h h1)]
    · rw [if_neg (mt (fun h => ?_) h), Nat.add_left_comm]
      exact (Nat.add_lt_add_iff_left ..).1 (Nat.lt_of_lt_of_le h h2)
  | lam _ _ _ IH2 | forallE _ _ _ IH2 =>
    rw [IH2 (Nat.succ_le_succ h1) (Nat.succ_le_succ h2)]

theorem liftN'_liftN_lo (e : VExpr) (n k : Nat) : liftN n (liftN k e) k = liftN (n+k) e := by
  simpa [Nat.add_comm] using liftN'_liftN' (n1 := k) (n2 := n) (Nat.zero_le _) (Nat.le_refl _)

theorem liftN'_liftN_hi (e : VExpr) (n1 n2 k : Nat) :
    liftN n2 (liftN n1 e k) k = liftN (n1+n2) e k :=
  liftN'_liftN' (Nat.le_refl _) (Nat.le_add_left ..)

theorem liftN_liftN (e : VExpr) (n1 n2 : Nat) : liftN n2 (liftN n1 e) = liftN (n1+n2) e := by
  simpa using liftN'_liftN' (Nat.zero_le _) (Nat.zero_le _)

theorem liftN_succ (e : VExpr) (n : Nat) : liftN (n+1) e = lift (liftN n e) :=
  (liftN_liftN ..).symm

theorem liftN'_comm (e : VExpr) (n1 n2 k1 k2 : Nat) (h : k2 ≤ k1) :
    liftN n2 (liftN n1 e k1) k2 = liftN n1 (liftN n2 e k2) (n2+k1) := by
  induction e generalizing k1 k2 with
    simp [liftN, liftVar, Nat.add_assoc, Nat.succ_le_succ, *]
  | bvar i =>
    split <;> rename_i h'
    · rw [if_pos (c := _ < n2 + k1)]; split
      · exact Nat.lt_add_left _ h'
      · exact Nat.add_lt_add_left h' _
    · have := mt (Nat.lt_of_lt_of_le · h) h'
      rw [if_neg (mt (Nat.lt_of_le_of_lt (Nat.le_add_left _ n1)) this),
        if_neg this, if_neg (mt (Nat.add_lt_add_iff_left ..).1 h'), Nat.add_left_comm]

theorem lift_liftN' (e : VExpr) (k : Nat) : lift (liftN n e k) = liftN n (lift e) (k+1) :=
  Nat.add_comm .. ▸ liftN'_comm (h := Nat.zero_le _) ..

theorem sizeOf_liftN (e : VExpr) (k : Nat) : sizeOf e ≤ sizeOf (liftN n e k) := by
  induction e generalizing k with simp [liftN, Nat.add_assoc, Nat.add_le_add_iff_left]
  | bvar => simp [liftVar]; split <;> simp [Nat.le_add_left]
  | _ => rename_i ih1 ih2; exact Nat.add_le_add (ih1 _) (ih2 _)

@[simp] theorem liftN_default (n k : Nat) : liftN n default k = default := rfl
@[simp] theorem lift_default : lift default = default := rfl

def ClosedN : VExpr → (k :_:= 0) → Prop
  | .bvar i, k => i < k
  | .sort .., _ => True
  | .app fn arg, k => fn.ClosedN k ∧ arg.ClosedN k
  | .lam ty body, k => ty.ClosedN k ∧ body.ClosedN (k+1)
  | .forallE ty body, k => ty.ClosedN k ∧ body.ClosedN (k+1)

abbrev Closed := ClosedN

@[simp] theorem ClosedN.default : ClosedN default k := trivial

theorem ClosedN.mono (h : k ≤ k') (self : ClosedN e k) : ClosedN e k' := by
  induction e generalizing k k' with (simp [ClosedN] at self ⊢; try simp [self, *])
  | bvar i => exact Nat.lt_of_lt_of_le self h
  | app _ _ ih1 ih2 => exact ⟨ih1 h self.1, ih2 h self.2⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    exact ⟨ih1 h self.1, ih2 (Nat.succ_le_succ h) self.2⟩

theorem ClosedN.liftN_eq (self : ClosedN e k) (h : k ≤ j) : liftN n e j = e := by
  induction e generalizing k j with
    (simp [ClosedN] at self; simp [liftN, *])
  | bvar i => exact liftVar_lt (Nat.lt_of_lt_of_le self h)
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    exact ⟨ih1 self.1 h, ih2 self.2 (Nat.succ_le_succ h)⟩

theorem ClosedN.lift_eq (self : ClosedN e) : lift e = e := self.liftN_eq (Nat.zero_le _)

protected theorem ClosedN.liftN (self : ClosedN e k) : ClosedN (e.liftN n j) (k+n) := by
  induction e generalizing k j with
    (simp [ClosedN] at self; simp [VExpr.liftN, ClosedN, *])
  | bvar i => exact liftVar_lt_add self
  | lam _ _ _ ih2 | forallE _ _ _ ih2 => exact Nat.add_right_comm .. ▸ ih2 self.2

theorem ClosedN.liftN_eq_rev (self : ClosedN (liftN n e j) k) (h : k ≤ j) : liftN n e j = e := by
  induction e generalizing k j with
    (simp [liftN, ClosedN] at self; simp [liftN, *])
  | bvar i =>
    refine liftVar_lt (Nat.lt_of_lt_of_le ?_ h)
    unfold liftVar at self; split at self <;>
      [exact self; exact Nat.lt_of_le_of_lt (Nat.le_add_left ..) self]
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    exact ⟨ih1 self.1 h, ih2 self.2 (Nat.succ_le_succ h)⟩


def instVar (i : Nat) (e : VExpr) (k := 0) : VExpr :=
  if i < k then .bvar i else if i = k then liftN k e else .bvar (i - 1)

@[simp] theorem instVar_zero : instVar 0 e = e := liftN_zero ..
@[simp] theorem instVar_upper : instVar (i+1) e = .bvar i := rfl
@[simp] theorem instVar_lower : instVar 0 e (k+1) = .bvar 0 := by simp [instVar]
@[simp] theorem instVar_succ : instVar (i+1) e (k+1) = (instVar i e k).lift := by
  simp [instVar, Nat.succ_lt_succ_iff]; split <;> simp [lift, liftN]
  split <;> simp [liftN_liftN, liftN]
  have := Nat.lt_of_le_of_ne (Nat.not_lt.1 ‹_›) (Ne.symm ‹_›)
  let i+1 := i; rfl

theorem liftN_instVar_lo (n : Nat) (e : VExpr) (j k : Nat) (hj : k ≤ j) :
    liftN n (instVar i e j) k = instVar (liftVar n i k) e (n+j) := by
  simp [instVar]; split <;> rename_i h
  · rw [if_pos]; · rfl
    simp only [liftVar]; split <;> rename_i hk
    · exact Nat.lt_add_left _ h
    · exact Nat.add_lt_add_left h _
  split <;> rename_i h'
  · subst i
    rw [liftN'_liftN' (h1 := Nat.zero_le _) (h2 := hj), liftVar_le hj,
      if_neg (by simp), if_pos rfl, Nat.add_comm]
  · rw [Nat.not_lt] at h; rw [liftVar_le (Nat.le_trans hj h)]
    have hk := Nat.lt_of_le_of_ne h (Ne.symm h')
    let i+1 := i
    have := Nat.add_lt_add_left hk n
    rw [if_neg (Nat.lt_asymm this), if_neg (Nat.ne_of_gt this)]
    simp only [liftN]
    rw [liftVar_le (Nat.le_trans hj <| by exact Nat.le_of_lt_succ hk)]; rfl

theorem liftN_instVar_hi (i : Nat) (e2 : VExpr) (n k j : Nat) :
    liftN n (instVar i e2 j) (k+j) = instVar (liftVar n i (k+j+1)) (liftN n e2 k) j := by
  simp [instVar]; split <;> rename_i h
  · have := Nat.lt_add_left k h
    rw [liftVar_lt <| Nat.lt_succ_of_lt this, if_pos h]
    simp [liftN, liftVar_lt this]
  split <;> rename_i h'
  · subst i
    have := Nat.le_add_left j k
    simp [liftVar_lt (by exact Nat.lt_succ_of_le this)]
    rw [liftN'_comm (h := Nat.zero_le _), Nat.add_comm]
  · have hk := Nat.lt_of_le_of_ne (Nat.not_lt.1 h) (Ne.symm h')
    let i+1 := i
    simp [liftVar, Nat.succ_lt_succ_iff]; split <;> rename_i hi
    · simp [liftN, liftVar_lt hi]
    · have := Nat.lt_add_left n hk
      rw [if_neg (Nat.lt_asymm this), if_neg (Nat.ne_of_gt this)]
      simp [liftN]; rw [liftVar_le (Nat.not_lt.1 hi)]

def inst : VExpr → VExpr → (k :_:= 0) → VExpr
  | .bvar i, e, k => instVar i e k
  | .sort u, _, _ => .sort u
  | .app fn arg, e, k => .app (fn.inst e k) (arg.inst e k)
  | .lam ty body, e, k => .lam (ty.inst e k) (body.inst e (k+1))
  | .forallE ty body, e, k => .forallE (ty.inst e k) (body.inst e (k+1))

@[simp] theorem inst_default : inst default e k = default := rfl

theorem liftN_instN_lo (n : Nat) (e1 e2 : VExpr) (j k : Nat) (hj : k ≤ j) :
    liftN n (e1.inst e2 j) k = (liftN n e1 k).inst e2 (n+j) := by
  induction e1 generalizing k j with
    simp [liftN, inst, instVar, Nat.add_le_add_iff_right, *]
  | bvar i => apply liftN_instVar_lo (hj := hj)
  | _ => rfl

theorem liftN_instN_hi (e1 e2 : VExpr) (n k j : Nat) :
    liftN n (e1.inst e2 j) (k+j) = (liftN n e1 (k+j+1)).inst (liftN n e2 k) j := by
  induction e1 generalizing j with simp [liftN, inst, instVar, *]
  | bvar i => apply liftN_instVar_hi
  | _ => rename_i IH; apply IH

theorem liftN_inst_hi (e1 e2 : VExpr) (n k : Nat) :
    liftN n (e1.inst e2) k = (liftN n e1 (k+1)).inst (liftN n e2 k) := liftN_instN_hi ..

theorem lift_instN_lo (e1 e2 : VExpr) : lift (e1.inst e2 k) = (lift e1).inst e2 (k + 1) :=
  Nat.add_comm .. ▸ liftN_instN_lo (hj := Nat.zero_le _) ..

theorem lift_inst_hi (e1 e2 : VExpr) : lift (e1.inst e2) = (liftN 1 e1 1).inst (lift e2) :=
  liftN_instN_hi ..

theorem inst_liftN (e1 e2 : VExpr) : (liftN 1 e1 k).inst e2 k = e1 := by
  induction e1 generalizing k with simp [liftN, inst, *]
  | bvar i =>
    simp only [liftVar, instVar, Nat.add_comm 1]; split <;> [rfl; rename_i h]
    rw [if_neg (mt (Nat.lt_of_le_of_lt (Nat.le_succ _)) h),
      if_neg (mt (by rintro rfl; apply Nat.lt_succ_self) h)]; rfl

theorem inst_liftN' (e1 e2 : VExpr) : (liftN (n+1) e1 k).inst e2 k = liftN n e1 k := by
  rw [← liftN'_liftN_hi, inst_liftN]

theorem inst_lift (e1 e2 : VExpr) : (lift e1).inst e2 = e1 := inst_liftN ..

def unliftN (e : VExpr) (n k : Nat) : VExpr :=
  match n with
  | 0 => e
  | n+1 => unliftN (e.inst default k) n k

@[simp] theorem unliftN_liftN : unliftN (liftN n e k) n k = e := by
  induction n <;> simp [unliftN, inst_liftN', *]

theorem unliftN_add : unliftN e (n1+n2) k = unliftN (unliftN e n1 k) n2 k := by
  induction n1 generalizing e <;> simp [unliftN, Nat.succ_add, *]

theorem unliftN_succ' : unliftN e (n+1) k = (unliftN e n k).inst default k := by
  rw [unliftN_add]; rfl

theorem liftN_unliftN_hi (h : k2 ≤ k1) :
    liftN n1 (unliftN e n2 k2) k1 = unliftN (liftN n1 e (k1+n2)) n2 k2 := by
  obtain ⟨k1, rfl⟩ := Nat.le_iff_exists_add'.1 h
  induction n2 generalizing e with simp [unliftN]
  | succ n2 ih =>
    rw [ih, Nat.add_right_comm, liftN_instN_hi e default n1 (k1+n2) k2,
      Nat.add_right_comm k1]; rfl

def Skips (e : VExpr) (n k : Nat) : Prop := liftN n (unliftN e n k) k = e

protected theorem Skips.liftN : Skips (liftN n e k) n k := by simp [Skips]

theorem skips_iff_exists : Skips e n k ↔ ∃ e', e = liftN n e' k :=
  ⟨fun h => ⟨_, h.symm⟩, fun ⟨_, h⟩ => h ▸ .liftN⟩

theorem Skips.zero : Skips e 0 k := by simp [Skips, unliftN]

theorem liftN_inj : liftN n e1 k = liftN n e2 k ↔ e1 = e2 :=
  ⟨fun H => by rw [← unliftN_liftN (e := e1), H, unliftN_liftN], (· ▸ rfl)⟩

theorem liftVar_inj : liftVar n i k = liftVar n i' k ↔ i = i' := by
  simpa [liftN] using @liftN_inj n (.bvar i) k (.bvar i')

theorem Skips.of_liftN_hi (self : (liftN n1 e k1).Skips n2 k2) (h : n2 + k2 ≤ k1) :
    e.Skips n2 k2 := by
  obtain ⟨k1, rfl⟩ := Nat.le_iff_exists_add'.1 h
  rwa [Skips, Nat.add_comm n2, ← Nat.add_assoc, ← liftN_unliftN_hi (Nat.le_add_left ..),
    liftN'_comm (h := Nat.le_add_left ..), Nat.add_comm, liftN_inj] at self

theorem skips_add : Skips e (n1+n2) k ↔ ∃ e', Skips e' n1 k ∧ e = liftN n2 e' k := by
  simp [skips_iff_exists, ← liftN'_liftN_hi]
  exact ⟨fun ⟨_, h⟩ => ⟨_, ⟨_, rfl⟩, h⟩, fun ⟨_, ⟨_, rfl⟩, h⟩ => ⟨_, h⟩⟩

def Skips' (n : Nat) : VExpr → (k :_:= 0) → Prop
  | .bvar i, k => i < k + n → i < k
  | .sort .., _ => True
  | .app fn arg, k => fn.Skips' n k ∧ arg.Skips' n k
  | .lam ty body, k => ty.Skips' n k ∧ body.Skips' n (k+1)
  | .forallE ty body, k => ty.Skips' n k ∧ body.Skips' n (k+1)

theorem skips_iff : Skips e n k ↔ Skips' n e k := by
  induction n generalizing e with
  | zero => simp [Skips, unliftN]; induction e generalizing k <;> simp [Skips', *]
  | succ n ih =>
    simp [skips_add, ih]; clear ih
    induction e generalizing k with
    | bvar i =>
      refine ⟨fun ⟨e', h1, h2⟩ => ?_, fun h => ?_⟩
      · cases e' <;> cases h2; simp [Skips', liftVar]; split
        · intro; assumption
        · next h2 =>
          rw [Nat.add_comm, ← Nat.add_assoc, Nat.succ_lt_succ_iff]
          exact fun h => h2.elim (h1 h)
      · simp [Skips'] at h
        if h' : i < k + n + 1 then
          exact ⟨.bvar i, fun _ => h h', by simp [liftN, liftVar, h h']⟩
        else
          have := Nat.not_lt.1 h'
          let i+1 := i; rw [Nat.add_lt_add_iff_right] at h'
          have := mt (Nat.lt_of_lt_of_le · (Nat.le_add_right ..)) h'
          exact ⟨.bvar i, h'.elim, by simp [liftN, liftVar]; rw [if_neg this, Nat.add_comm]⟩
    | sort u =>
      refine ⟨fun ⟨e', h1, h2⟩ => ?_, fun _ => ⟨.sort u, by simp [Skips', liftN]⟩⟩
      cases e' <;> cases h2; simp [Skips']
    | app f a fIH aIH =>
      simp [Skips', ← fIH, ← aIH]; refine ⟨fun ⟨e', h1, h2⟩ => ?_, ?_⟩
      · cases e' <;> cases h2; exact ⟨⟨_, h1.1, rfl⟩, ⟨_, h1.2, rfl⟩⟩
      · rintro ⟨⟨e1, h1, rfl⟩, ⟨e2, h2, rfl⟩⟩; exact ⟨.app .., ⟨h1, h2⟩, rfl⟩
    | forallE f a fIH aIH =>
      simp [Skips', ← fIH, ← aIH]; refine ⟨fun ⟨e', h1, h2⟩ => ?_, ?_⟩
      · cases e' <;> cases h2; exact ⟨⟨_, h1.1, rfl⟩, ⟨_, h1.2, rfl⟩⟩
      · rintro ⟨⟨e1, h1, rfl⟩, ⟨e2, h2, rfl⟩⟩; exact ⟨.forallE .., ⟨h1, h2⟩, rfl⟩
    | lam f a fIH aIH =>
      simp [Skips', ← fIH, ← aIH]; refine ⟨fun ⟨e', h1, h2⟩ => ?_, ?_⟩
      · cases e' <;> cases h2; exact ⟨⟨_, h1.1, rfl⟩, ⟨_, h1.2, rfl⟩⟩
      · rintro ⟨⟨e1, h1, rfl⟩, ⟨e2, h2, rfl⟩⟩; exact ⟨.lam .., ⟨h1, h2⟩, rfl⟩

theorem of_liftN_eq_liftN (h : liftN n1 e1 (k1+n2+k2) = liftN n2 e2 k2) :
    ∃ e', e1 = liftN n2 e' k2 ∧ e2 = liftN n1 e' (k1+k2) := by
  have : (liftN n1 e1 (k1+n2+k2)).Skips n2 k2 := h ▸ .liftN
  obtain ⟨e', rfl⟩ := skips_iff_exists.1 <|
    this.of_liftN_hi (Nat.add_assoc .. ▸ Nat.le_add_left ..)
  refine ⟨e', rfl, ?_⟩
  rw [← liftN_inj, ← h, liftN'_comm (n1 := n1) (h := Nat.le_add_left ..),
    Nat.add_left_comm, Nat.add_assoc]

theorem ClosedN.instN_eq (self : ClosedN e1 k) (h : k ≤ j) : e1.inst e2 j = e1 := by
  conv => lhs; rw [← self.liftN_eq (n := 1) h]
  rw [inst_liftN]

theorem ClosedN.instN (h1 : ClosedN e (k+j+1)) (h2 : ClosedN e2 k) : ClosedN (e.inst e2 j) (k+j) :=
  match e, h1 with
  | .bvar i, h => by
    simp [inst, instVar]; split <;> rename_i h1
    · exact Nat.lt_of_lt_of_le h1 (Nat.le_add_left ..)
    split <;> rename_i h1'
    · exact h2.liftN
    · have hk := Nat.lt_of_le_of_ne (Nat.not_lt.1 h1) (Ne.symm h1')
      let i+1 := i
      exact Nat.lt_of_succ_lt_succ h
  | .sort .., h => h
  | .app .., h => ⟨h.1.instN h2, h.2.instN h2⟩
  | .lam .., h | .forallE .., h => ⟨h.1.instN h2, h.2.instN (j := j+1) h2⟩

theorem ClosedN.inst (h1 : ClosedN e (k+1)) (h2 : ClosedN e2 k) : ClosedN (e.inst e2) k :=
  h1.instN (j := 0) h2

theorem inst_instVar_hi (i : Nat) (e2 e3 : VExpr) (k j : Nat) :
    inst (instVar i e2 k) e3 (j+k) = (instVar i e3 (j+k+1)).inst (e2.inst e3 j) k := by
  simp [instVar]; split <;> rename_i h
  · simp [Nat.lt_succ_of_lt, inst, instVar, h, Nat.lt_of_lt_of_le h (Nat.le_add_left k j)]
  split <;> rename_i h'
  · subst i
    simp [Nat.lt_succ_of_le, Nat.le_add_left, inst, instVar]
    rw [liftN_instN_lo k e2 e3 j _ (Nat.zero_le _), Nat.add_comm]
  · have hk := Nat.lt_of_le_of_ne (Nat.not_lt.1 h) (Ne.symm h')
    let i+1 := i
    simp [inst, instVar]; split <;> rename_i hi
    · simp [inst, instVar, h, h']
    split <;> rename_i hi'
    · subst i
      suffices liftN (j+k+1) .. = _ by rw [this]; exact (inst_liftN ..).symm
      exact (liftN'_liftN' (Nat.zero_le _) (Nat.le_add_left k j)).symm
    · have hk := Nat.lt_of_le_of_ne (Nat.not_lt.1 hi) (Ne.symm hi')
      let i+1 := i
      simp [inst, instVar]
      have := Nat.lt_of_le_of_lt (Nat.le_add_left ..) hk
      rw [if_neg (Nat.lt_asymm this), if_neg (Nat.ne_of_gt this)]

theorem inst_inst_hi (e1 e2 e3 : VExpr) (k j : Nat) :
    inst (e1.inst e2 k) e3 (j+k) = (e1.inst e3 (j+k+1)).inst (e2.inst e3 j) k := by
  induction e1 generalizing k with simp [inst, instVar, *]
  | bvar i => apply inst_instVar_hi
  | _ => rename_i IH; apply IH

theorem inst0_inst_hi (e1 e2 e3 : VExpr) (j : Nat) :
    inst (e1.inst e2) e3 j = (e1.inst e3 (j+1)).inst (e2.inst e3 j) := inst_inst_hi ..

theorem inst_instVar_lo (i : Nat) (e2 e3 : VExpr) (k j : Nat) :
    inst (instVar i e2 (k+j+1)) e3 j =
    (instVar i (e3.liftN 1 k) j).inst e2 (k+j) := by
  simp [instVar]; split <;> rename_i h
  · split <;> rename_i h1
    · simp only [inst, instVar, h1, reduceIte]
      rw [if_pos (Nat.lt_of_lt_of_le h1 (Nat.le_add_left ..))]
    split <;> rename_i h1'
    · subst i
      simp [inst, instVar]; rw [liftN'_comm (h := Nat.zero_le _), Nat.add_comm]
      exact (inst_liftN ..).symm
    · have hj := Nat.lt_of_le_of_ne (Nat.not_lt.1 h1) (Ne.symm h1')
      let i+1 := i
      simp [inst, instVar, h1, h1', Nat.lt_of_succ_lt_succ h]
  split <;> rename_i h'
  · subst i
    have := Nat.lt_succ_of_le (Nat.le_add_left j k)
    rw [if_neg (Nat.lt_asymm this), if_neg (Nat.ne_of_gt this)]
    simp [inst, instVar]
    suffices liftN (k+j+1) .. = _ by rw [this]; exact inst_liftN ..
    exact (liftN'_liftN' (Nat.zero_le _) (Nat.le_add_left j k)).symm
  · have hk := Nat.lt_of_le_of_ne (Nat.not_lt.1 h) (Ne.symm h')
    let i+1 := i
    have hk := Nat.lt_of_add_lt_add_right hk
    simp [inst, instVar]
    have := Nat.lt_of_le_of_lt (Nat.le_add_left ..) hk
    rw [if_neg (Nat.lt_asymm this), if_neg (Nat.ne_of_gt this)]
    have := Nat.lt_succ_of_lt this
    rw [if_neg (Nat.lt_asymm this), if_neg (Nat.ne_of_gt this)]
    simp [inst, instVar]
    rw [if_neg (Nat.lt_asymm hk), if_neg (Nat.ne_of_gt hk)]

theorem inst_inst_lo (e1 e2 e3 : VExpr) (k j : Nat) :
    inst (e1.inst e2 (k+j+1)) e3 j =
    (e1.inst (e3.liftN 1 k) j).inst e2 (k+j) := by
  induction e1 generalizing j with simp [inst, instVar, *]
  | bvar i => apply inst_instVar_lo
  | _ => rename_i IH; exact IH (j+1)

theorem instN_bvar0 (e : VExpr) (k : Nat) :
    inst (e.liftN 1 (k+1)) (.bvar 0) k = e := by
  induction e generalizing k with simp [liftN, inst, *]
  | bvar i => induction i generalizing k <;> cases k <;> simp [*, lift, liftN]

end VExpr


namespace VExpr

@[simp] def lift' : VExpr → Lift → VExpr
  | .bvar i, k => .bvar (k.liftVar i)
  | .sort u, _ => .sort u
  | .app fn arg, k => .app (fn.lift' k) (arg.lift' k)
  | .lam ty body, k => .lam (ty.lift' k) (body.lift' k.cons)
  | .forallE ty body, k => .forallE (ty.lift' k) (body.lift' k.cons)

theorem lift'_consN_skipN : e.lift' (.consN (.skipN .refl n) k) = liftN n e k := Eq.symm <| by
  induction e generalizing k <;> simp [liftN, Lift.liftVar_consN_skipN, *]

theorem lift'_comp {e : VExpr} : e.lift' (.comp l₁ l₂) = (e.lift' l₁).lift' l₂ := Eq.symm <| by
  induction e generalizing l₁ l₂ <;> simp [Lift.liftVar_comp, *]

theorem lift'_depth_zero {e : VExpr} (H : l.depth = 0) : e.lift' l = e := by
  induction e generalizing l <;> simp_all [Lift.liftVar_depth_zero]

@[simp] theorem lift'_refl {e : VExpr} : e.lift' .refl = e := lift'_depth_zero rfl

theorem lift_eq_lift' {e : VExpr} : e.lift = e.lift' (.skip .refl) := by
  rw [lift, ← lift'_consN_skipN]; rfl

theorem ClosedN.lift'_eq (self : ClosedN e k) (h : ρ.Fixes k) : lift' e ρ = e := by
  induction e generalizing k ρ with (simp [ClosedN] at self; simp [*])
  | bvar i => exact h.liftVar_eq self
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩

def Subst := Nat → VExpr

def Subst.Depth (σ : Subst) (n n' : Nat) := ∀ i, σ (i + n') = .bvar (i + n)

def Subst.lift (σ : Subst) : Subst
  | 0 => .bvar 0
  | i+1 => (σ i).lift

def Subst.liftN (σ : Subst) : Nat → Subst
  | 0 => σ
  | k+1 => (σ.liftN k).lift

def subst : VExpr → Subst → VExpr
  | .bvar i, σ => σ i
  | .sort u, _ => .sort u
  | .app fn arg, σ => .app (fn.subst σ) (arg.subst σ)
  | .lam ty body, σ => .lam (ty.subst σ) (body.subst σ.lift)
  | .forallE ty body, σ => .forallE (ty.subst σ) (body.subst σ.lift)

def Subst.lift_r (σ : Subst) (ρ : Lift) : Subst := fun x => (σ x).lift' ρ
def Subst.lift_l (ρ : Lift) (σ : Subst) : Subst := fun x => σ (ρ.liftVar x)

theorem Subst.lift_l_lift {σ : Subst} {ρ} : (σ.lift_l ρ).lift = σ.lift.lift_l ρ.cons := by
  funext i; cases i <;> simp! [lift_l]

theorem Subst.lift_r_lift {σ : Subst} {ρ} : (σ.lift_r ρ).lift = σ.lift.lift_r ρ.cons := by
  funext i; cases i <;> simp! [lift, lift_r, ← lift'_comp, lift_eq_lift']

theorem subst_lift' {e : VExpr} : (e.lift' ρ).subst σ = subst e (.lift_l ρ σ) := by
  induction e generalizing ρ σ <;> simp! [*, Subst.lift_l_lift]; rfl

theorem lift'_subst {e : VExpr} : (e.subst σ).lift' ρ = subst e (.lift_r σ ρ) := by
  induction e generalizing ρ σ <;> simp! [*, Subst.lift_r, Subst.lift_r_lift]

def Subst.id : Subst := .bvar
def Subst.head (σ : Subst) : VExpr := σ 0
def Subst.tail (σ : Subst) : Subst := fun n => σ (n+1)

theorem Subst.Depth.id : Subst.id.Depth 0 0 := fun _ => rfl

@[simp] theorem id_lift : Subst.id.lift = Subst.id := by
  funext i; cases i <;> simp [Subst.id, Subst.lift, liftN]

@[simp] theorem subst_id {e : VExpr} : e.subst .id = e := by
  induction e <;> simp! [*, id_lift]; rfl

def Subst.cons (σ : Subst) (e : VExpr) : Subst
  | 0 => e
  | i+1 => σ i

abbrev Subst.one (e : VExpr) : Subst := .cons .id e

theorem Subst.Depth.one : (Subst.one e).Depth 0 1 := .id

def _root_.DomainSemantics.Lift.inv : Lift → Subst
  | .refl => .id
  | .skip ρ => ρ.inv.cons default
  | .cons ρ => ρ.inv.lift

theorem lift_l_inv {ρ : Lift} : .lift_l ρ ρ.inv = Subst.id := by
  funext i; simp [Subst.lift_l, Subst.id]
  induction ρ generalizing i with
  | refl => rfl
  | skip ρ ih => simp [Lift.inv, Subst.cons, ih]
  | cons ρ ih => cases i <;> simp [Lift.inv, Subst.lift, ih, lift_eq_lift']

theorem lift'_inj {e e' : VExpr} {ρ : Lift} : e.lift' ρ = e'.lift' ρ ↔ e = e' :=
  ⟨(by simpa [subst_lift', lift_l_inv] using congrArg (·.subst ρ.inv) ·), (· ▸ rfl)⟩

theorem instN_eq (e a : VExpr) : e.inst a k = e.subst (.liftN (.one a) k) := by
  induction e generalizing k with simp_all [inst, subst, Subst.liftN] | bvar i
  induction k generalizing i <;> cases i <;> simp [Subst.liftN, Subst.lift, Subst.cons, Subst.id, *]

theorem inst_eq (e a : VExpr) : e.inst a = e.subst (.one a) := instN_eq ..

def Subst.trunc (σ : Subst) (n n' : Nat) : Subst :=
  fun i => if n' ≤ i then .bvar (i - n' + n) else σ i

theorem Subst.lift_r_comm (σ : Subst) (ρ : Lift) (H : Subst.Depth σ 0 n) :
    σ.lift_r ρ = .lift_l (ρ.consN n) ((σ.lift_r ρ).trunc 0 n) := by
  funext i; simp [Subst.lift_l, Subst.lift_r, Subst.trunc]
  have : (ρ.consN n).liftVar i = if n ≤ i then ρ.liftVar (i-n) + n else i := by
    clear H; induction n generalizing i <;> [skip; cases i] <;> simp! [*]; split <;> rfl
  rw [this]; split <;> simp
  have := H (i - n); rw [Nat.sub_add_cancel ‹_›] at this; simp [this]

theorem lift_r_one (e : VExpr) (ρ : Lift) :
    (Subst.one e).lift_r ρ = .lift_l ρ.cons (Subst.one (e.lift' ρ)) := by
  refine (Subst.lift_r_comm (Subst.one e) ρ .one).trans ?_; congr 1
  funext i; simp [Subst.trunc]
  cases i <;> simp [Subst.one, Subst.cons, Subst.lift_r, Subst.id]

theorem lift'_inst_hi (e1 e2 : VExpr) (ρ : Lift) :
    lift' (e1.inst e2) ρ = (lift' e1 ρ.cons).inst (lift' e2 ρ) := by
  simp [subst_lift', lift'_subst, lift_r_one, inst_eq]
