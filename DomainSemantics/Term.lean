import DomainSemantics.Lift

namespace DomainSemantics

inductive Term where
  | bvar (i : Nat)
  | sort (u : Bool)
  | app (f a : Term)
  | lam (A e : Term)
  | forallE (A B : Term)

instance : Inhabited Term := ⟨.sort false⟩

namespace Term

@[simp] def lift' : Term → Lift → Term
  | .bvar i, k => .bvar (k.liftVar i)
  | .sort u, _ => .sort u
  | .app fn arg, k => .app (fn.lift' k) (arg.lift' k)
  | .lam ty body, k => .lam (ty.lift' k) (body.lift' k.cons)
  | .forallE ty body, k => .forallE (ty.lift' k) (body.lift' k.cons)

abbrev lift e := lift' e (.skip .refl)

theorem lift'_comp {e : Term} : e.lift' (.comp l₁ l₂) = (e.lift' l₁).lift' l₂ := Eq.symm <| by
  induction e generalizing l₁ l₂ <;> simp [Lift.liftVar_comp, *]

theorem lift'_depth_zero {e : Term} (H : l.depth = 0) : e.lift' l = e := by
  induction e generalizing l <;> simp_all [Lift.liftVar_depth_zero]

@[simp] theorem lift'_refl {e : Term} : e.lift' .refl = e := lift'_depth_zero rfl

def ClosedN : Term → (k :_:= 0) → Prop
  | .bvar i, k => i < k
  | .sort .., _ => True
  | .app fn arg, k => fn.ClosedN k ∧ arg.ClosedN k
  | .lam ty body, k => ty.ClosedN k ∧ body.ClosedN (k+1)
  | .forallE ty body, k => ty.ClosedN k ∧ body.ClosedN (k+1)

theorem ClosedN.mono (h : k ≤ k') (self : ClosedN e k) : ClosedN e k' := by
  induction e generalizing k k' with (simp [ClosedN] at self ⊢; try simp [self, *])
  | bvar i => exact Nat.lt_of_lt_of_le self h
  | app _ _ ih1 ih2 => exact ⟨ih1 h self.1, ih2 h self.2⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    exact ⟨ih1 h self.1, ih2 (Nat.succ_le_succ h) self.2⟩

theorem ClosedN.lift'_eq (self : ClosedN e k) (h : ρ.Fixes k) : lift' e ρ = e := by
  induction e generalizing k ρ with (simp [ClosedN] at self; simp [*])
  | bvar i => exact h.liftVar_eq self
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩

theorem ClosedN.lift_eq (self : ClosedN e) : lift e = e := self.lift'_eq ⟨⟩

def instL (ls : List SLevel) : Term → Term
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .app fn arg => .app (instL ls fn) (instL ls arg)
  | .lam ty body => .lam (instL ls ty) (instL ls body)
  | .forallE ty body => .forallE (instL ls ty) (instL ls body)

theorem ClosedN.instL : ∀ {e}, ClosedN e k → ClosedN (e.instL ls) k
  | .bvar .., h | .sort .., h => h
  | .app .., h | .lam .., h | .forallE .., h => ⟨h.1.instL, h.2.instL⟩

end Term
open Term

def Subst := Nat → Term

def Subst.Depth (σ : Subst) (n n' : Nat) := ∀ i, σ (i + n') = .bvar (i + n)

def Subst.Fixes (σ : Subst) (n : Nat) := ∀ i < n, σ i = .bvar i

theorem Subst.Fixes.zero : Fixes σ 0 := nofun

theorem Subst.Depth.add {σ : Subst} (H : σ.Depth n n') : σ.Depth (n + k) (n' + k) :=
  fun i => cast (by congr 2 <;> omega) <| H (k + i)

def Subst.lift (σ : Subst) : Subst
  | 0 => .bvar 0
  | i+1 => (σ i).lift

theorem Subst.Depth.lift {σ : Subst} (H : σ.Depth n n') : σ.lift.Depth (n + 1) (n' + 1) :=
  fun i => by simp [Subst.lift, H i]; rfl

theorem Subst.Fixes.lift {σ : Subst} (H : σ.Fixes n) : σ.lift.Fixes (n + 1) := fun
  | 0, _ => rfl
  | n+1, h => by simp [Subst.lift, H _ (Nat.lt_of_succ_lt_succ h)]

def Subst.id : Subst := .bvar
def Subst.head (σ : Subst) : Term := σ 0
def Subst.tail (σ : Subst) : Subst := fun n => σ (n+1)

theorem Subst.Depth.id : Subst.id.Depth 0 0 := fun _ => rfl
theorem Subst.Depth.tail {σ : Subst} (H : σ.Depth n (n' + 1)) : σ.tail.Depth n n' := H

def Subst.cons (σ : Subst) (e : Term) : Subst
  | 0 => e
  | i+1 => σ i

theorem Subst.Depth.cons {σ : Subst} (H : σ.Depth n n') : (σ.cons e).Depth n (n' + 1) := H

abbrev Subst.one (e : Term) : Subst := .cons .id e

theorem Subst.Depth.one : (Subst.one e).Depth 0 1 := .id

def Subst.trunc (σ : Subst) (n n' : Nat) : Subst :=
  fun i => if n' ≤ i then .bvar (i - n' + n) else σ i

theorem Subst.Depth.trunc {σ : Subst} : (σ.trunc n n').Depth n n' := by
  intro i; simp [Subst.trunc]

def _root_.DomainSemantics.Lift.invS : Lift → Subst
  | .refl => .id
  | .skip ρ => ρ.invS.cons default
  | .cons ρ => ρ.invS.lift

theorem Subst.Depth.invS : ∀ (ρ : Lift), ρ.invS.Depth ρ.dom ρ.size
  | .refl => .id
  | .skip l => (invS l).cons
  | .cons l => (invS l).lift

@[simp] theorem Subst.head_cons : (cons σ e).head = e := rfl
@[simp] theorem Subst.tail_cons : (cons σ e).tail = σ := rfl

def Subst.lift_r (σ : Subst) (ρ : Lift) : Subst := fun x => (σ x).lift' ρ
def Subst.lift_l (ρ : Lift) (σ : Subst) : Subst := fun x => σ (ρ.liftVar x)

theorem Subst.tail_eq_lift_l {σ : Subst} : σ.tail = σ.lift_l Lift.refl.skip := rfl

theorem Subst.lift_l_lift {σ : Subst} {ρ} : (σ.lift_l ρ).lift = σ.lift.lift_l ρ.cons := by
  funext i; cases i <;> simp! [lift_l]

theorem Subst.lift_r_lift {σ : Subst} {ρ} : (σ.lift_r ρ).lift = σ.lift.lift_r ρ.cons := by
  funext i; cases i <;> simp! [lift_r, ← lift'_comp]

theorem lift_l_inv {ρ : Lift} : .lift_l ρ ρ.invS = Subst.id := by
  funext i; simp [Subst.lift_l, Subst.id]
  induction ρ generalizing i with
  | refl => rfl
  | skip ρ ih => simp [Lift.invS, Subst.cons, ih]
  | cons ρ ih => cases i <;> simp [Lift.invS, Subst.lift, ih]

@[simp] theorem instL_lift' : (lift' e ρ).instL ls = lift' (e.instL ls) ρ := by
  cases e <;> simp [lift', instL, instL_lift']

def _root_.DomainSemantics.Lift.toSubst (ρ : Lift) : Subst := .lift_l ρ .id

theorem _root_.DomainSemantics.Lift.toSubst_apply (ρ : Lift) (i) : ρ.toSubst i = bvar (ρ.liftVar i) := rfl

theorem Subst.Depth.toSubst (ρ : Lift) : ρ.toSubst.Depth ρ.size ρ.dom := by
  intro i; simp [Lift.toSubst_apply]
  induction ρ <;> simp! [*] <;> omega

def Term.subst : Term → Subst → Term
  | .bvar i, σ => σ i
  | .sort u, _ => .sort u
  | .app fn arg, σ => .app (fn.subst σ) (arg.subst σ)
  | .lam ty body, σ => .lam (ty.subst σ) (body.subst σ.lift)
  | .forallE ty body, σ => .forallE (ty.subst σ) (body.subst σ.lift)

@[simp] theorem id_lift : Subst.id.lift = Subst.id := by funext i; cases i <;> rfl

@[simp] theorem subst_id {e : Term} : e.subst .id = e := by
  induction e <;> simp! [*]; rfl

theorem subst_lift' {e : Term} : (e.lift' ρ).subst σ = subst e (.lift_l ρ σ) := by
  induction e generalizing ρ σ <;> simp! [*, Subst.lift_l_lift]; rfl

theorem lift'_subst {e : Term} : (e.subst σ).lift' ρ = subst e (.lift_r σ ρ) := by
  induction e generalizing ρ σ <;> simp! [*, Subst.lift_r, Subst.lift_r_lift]

theorem lift'_inj {e e' : Term} {ρ : Lift} : e.lift' ρ = e'.lift' ρ ↔ e = e' :=
  ⟨(by simpa [subst_lift', lift_l_inv] using congrArg (·.subst ρ.invS) ·), (· ▸ rfl)⟩

theorem subst_toSubst {e : Term} : subst e ρ.toSubst = lift' e ρ := by
  simp [Lift.toSubst, ← subst_lift']

theorem subst_lift'_inv {e : Term} {ρ : Lift} : (e.lift' ρ).subst ρ.invS = e := by
  rw [subst_lift', lift_l_inv, subst_id]

nonrec def Subst.instL (ls : List SLevel) (σ : Subst) : Subst := instL ls ∘ σ

theorem Subst.instL_lift {σ : Subst} : (σ.instL ls).lift = σ.lift.instL ls := by
  funext i; obtain _|i := i <;> simp [Subst.instL, lift, Term.instL]

@[simp] theorem instL_subst : (subst e σ).instL ls = subst (e.instL ls) (σ.instL ls) := by
  cases e <;> simp [subst, instL, instL_subst, Subst.instL_lift] <;> simp [Subst.instL]

def Subst.comp (σ σ' : Subst) : Subst := fun x => (σ x).subst σ'

theorem Subst.comp_lift {σ σ' : Subst} : (σ.comp σ').lift = σ.lift.comp σ'.lift := by
  funext i; cases i <;> simp! [comp, Term.lift]
  rw [Term.lift, Term.lift, lift'_subst, subst_lift']; rfl

theorem subst_subst {e : Term} : (e.subst σ).subst σ' = subst e (.comp σ σ') := by
  induction e generalizing σ σ' <;> simp! [*, Subst.comp, Subst.comp_lift]

theorem lift_subst {e : Term} : e.lift.subst σ = e.subst σ.tail := by
  rw [lift, subst_lift', ← Subst.tail_eq_lift_l]

theorem lift_subst_cons {e : Term} : e.lift.subst (σ.cons t) = e.subst σ := by
  rw [lift_subst, Subst.tail_cons]

theorem Subst.lift_l_eq : Subst.lift_l ρ σ = Subst.comp ρ.toSubst σ := by
  funext; simp [lift_l, comp, Lift.toSubst_apply, Term.subst]

theorem Subst.lift_r_eq : Subst.lift_r σ ρ = Subst.comp σ ρ.toSubst := by
  funext i; simp [lift_r, comp, subst_toSubst]

theorem Subst.Depth.comp {σ σ' : Subst}
    (H : σ.Depth n₁ n₂) (H2 : σ'.Depth n₂ n₃) : (σ'.comp σ).Depth n₁ n₃ := by
  intro i; simp [Subst.comp, subst, H2 i, H i]

theorem Subst.Depth.lift_l {σ : Subst}
    (H : σ.Depth n ρ.size) : (Subst.lift_l ρ σ).Depth n ρ.dom := by
  rw [lift_l_eq]; exact .comp H (.toSubst _)

theorem Subst.Depth.lift_r {σ : Subst}
    (H : σ.Depth ρ.dom n) : (Subst.lift_r σ ρ).Depth ρ.size n := by
  rw [lift_r_eq]; exact .comp (.toSubst _) H

theorem ClosedN.subst_eq {e : Term} (self : ClosedN e k) (h : σ.Fixes k) : e.subst σ = e := by
  induction e generalizing k σ with (simp [ClosedN] at self; simp [*, Term.subst])
  | bvar i => exact h _ self
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h.lift⟩

def Term.inst (e a : Term) : Term := e.subst (.one a)

def Term.Skips (e : Term) (ρ : Lift) : Prop := lift' (e.subst ρ.invS) ρ = e

theorem Term.Skips.lift (e : Term) (ρ : Lift) : Skips (e.lift' ρ) ρ := by
  rw [Skips, subst_lift'_inv]

def Term.Skips' : Term → (ρ : Lift) → Prop
  | .bvar i, ρ => ∃ j, ρ.liftVar j = i
  | .sort .., _ => True
  | .app fn arg, ρ => fn.Skips' ρ ∧ arg.Skips' ρ
  | .lam ty body, ρ => ty.Skips' ρ ∧ body.Skips' ρ.cons
  | .forallE ty body, ρ => ty.Skips' ρ ∧ body.Skips' ρ.cons

theorem skips_iff {e : Term} {ρ : Lift} : Skips e ρ ↔ Skips' e ρ := by
  simp [Skips]; induction e generalizing ρ with simp!
  | app _ _ ih1 ih2 => exact and_congr ih1 ih2
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact and_congr ih1 (@ih2 ρ.cons)
  | bvar i =>
    constructor <;> [intro h; intro ⟨j, h⟩]
    · refine (?_ : have := (match ρ.invS i with | Term.bvar .. => True | _ => True); _); split
      · rename_i eq; cases eq ▸ h; exact ⟨_, rfl⟩
      · suffices ρ.invS i = default by cases this ▸ h
        clear h; rename_i h
        induction ρ generalizing i <;> simp [Lift.invS, Subst.id] at * <;>
          cases i <;> simp [Subst.cons, Subst.lift] at *
        case skip.succ ih i => exact ih _ h
        case cons.succ ih i => rw [ih i fun j h' => h _ (by rw [h']; rfl)]; rfl
    · refine .trans (?_ : _ = (bvar j).lift' ρ) (congrArg bvar h); congr 1
      rw [← h]; exact congrFun (@lift_l_inv ρ) j

theorem skips_inter {e : Term} : Skips e (ρ.inter ρ') ↔ Skips e ρ ∧ Skips e ρ' := by
  simp [skips_iff]
  induction e generalizing ρ ρ' with simp_all!
  | app => grind
  | lam _ _ _ ih2 | forallE _ _ _ ih2 => have := @ih2 ρ.cons ρ'.cons; grind [Lift.inter]
  | bvar =>
    constructor
    · rintro ⟨j, rfl⟩; constructor
      · rw [Lift.inter_comm, ← Lift.diff_comp]; exact ⟨_, Lift.liftVar_comp.symm⟩
      · rw [← Lift.diff_comp]; exact ⟨_, Lift.liftVar_comp.symm⟩
    · rintro ⟨⟨i, h⟩, ⟨j, rfl⟩⟩
      induction ρ generalizing i j ρ' with
      | refl => simp [Lift.inter]
      | skip ρ ih =>
        cases ρ' with
        | refl => simp [Lift.inter]; cases h; exact ⟨_, rfl⟩
        | skip => simp_all [Lift.inter]; exact ih _ _ h
        | cons => cases j <;> simp_all [Lift.inter, Lift.liftVar]; exact ih _ _ h
      | cons ρ ih =>
        cases i <;> simp_all [Lift.liftVar]
        · cases ρ' with
          | refl => simp [Lift.inter]; cases h; exact ⟨0, rfl⟩
          | skip => let 0 := j; simp_all
          | cons => let 0 := j; exact ⟨0, rfl⟩
        · cases ρ' with
          | refl => cases h; exact ⟨_+1, rfl⟩
          | skip => simp_all [Lift.liftVar, Lift.inter]; exact ih _ _ h
          | cons =>
            let _+1 := j; simp_all [Lift.inter]
            have ⟨_, h⟩ := ih _ _ h; exact ⟨_+1, congrArg (·+1) h⟩

theorem lift_r_inj {σ σ' : Subst} : σ.lift_r ρ = σ'.lift_r ρ ↔ σ = σ' := by
  refine ⟨fun h => funext fun i => ?_, (· ▸ rfl)⟩
  simpa [Subst.lift_r, lift'_inj] using congrFun h i

theorem Subst.lift_r_comm (σ : Subst) (ρ : Lift) (H : Subst.Depth σ 0 n) :
    σ.lift_r ρ = .lift_l (ρ.consN n) ((σ.lift_r ρ).trunc 0 n) := by
  funext i; simp [Subst.lift_l, Subst.lift_r, Subst.trunc]
  have : (ρ.consN n).liftVar i = if n ≤ i then ρ.liftVar (i-n) + n else i := by
    clear H; induction n generalizing i <;> [skip; cases i] <;> simp! [*]; split <;> rfl
  rw [this]; split <;> simp
  have := H (i - n); rw [Nat.sub_add_cancel ‹_›] at this; simp [this]

theorem lift_r_one (e : Term) (ρ : Lift) :
    (Subst.one e).lift_r ρ = .lift_l ρ.cons (Subst.one (e.lift' ρ)) := by
  refine (Subst.lift_r_comm (Subst.one e) ρ .one).trans ?_; congr 1
  funext i; simp [Subst.trunc]
  cases i <;> simp [Subst.one, Subst.cons, Subst.lift_r, Subst.id]

theorem lift_inst (e : Term) : e.lift.inst e' = e := by
  rw [inst, Subst.one, lift, subst_lift', ← Subst.tail_eq_lift_l, Subst.tail_cons, subst_id]

theorem lift'_inst_hi (e1 e2 : Term) (ρ : Lift) :
    lift' (e1.inst e2) ρ = (lift' e1 ρ.cons).inst (lift' e2 ρ) := by
  simp [inst, subst_lift', lift'_subst, lift_r_one]

theorem subst_inst {e : Term} : (e.inst a).subst σ = (e.subst σ.lift).inst (a.subst σ) := by
  rw [Term.inst, Term.inst, subst_subst, subst_subst]; congr 1
  funext i; obtain _|i := i <;> simp [Subst.comp, Subst.lift, Term.subst]
  · simp [Subst.one, Subst.cons]
  · rw [← Term.inst, lift_inst]; rfl

theorem inst_lift_cons {e : Term} {σ : Subst} :
    (e.subst σ.lift).inst x = e.subst (σ.cons x) := by
  rw [Term.inst, subst_subst, Subst.one]; congr 1
  funext i; obtain _|i := i <;>
    simp [Subst.comp, Subst.lift, Term.subst, Subst.cons, lift_subst_cons]

inductive Ctx.Lift' : Lift → List Term → List Term → Prop where
  | refl : Ctx.Lift' .refl Γ Γ
  | skip : Ctx.Lift' l Γ Γ' → Ctx.Lift' (.skip l) Γ (A :: Γ')
  | cons : Ctx.Lift' l Γ Γ' → Ctx.Lift' (.cons l) (A::Γ) (A.lift' l :: Γ')

theorem Ctx.Lift'.one : Ctx.Lift' (.skip .refl) Γ (A::Γ) := .skip .refl

theorem Ctx.Lift'.comp (H1 : Ctx.Lift' l Γ₀ Γ₁) (H2 : Ctx.Lift' l' Γ₁ Γ₂) : Ctx.Lift' (l.comp l') Γ₀ Γ₂ := by
  induction H2 generalizing l Γ₀ with
  | refl => exact H1
  | skip _ ih => exact (ih H1).skip
  | cons H2 ih =>
    cases H1 with
    | refl => exact .cons H2
    | skip H1 => exact .skip (ih H1)
    | cons H1 => exact Term.lift'_comp ▸ .cons (ih H1)

inductive Ctx.Inter : List Term → List Term → Lift → List Term → Lift → List Term → Prop where
  | refl_l : Ctx.Lift' ρ Γ Δ → Ctx.Inter Γ Δ .refl Γ ρ Δ
  | refl_r : Ctx.Lift' ρ Γ Δ → Ctx.Inter Γ Γ ρ Δ .refl Δ
  | skip_skip : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ → Ctx.Inter Γ Γ₁ (.skip ρ₁) Γ₂ (.skip ρ₂) (A::Δ)
  | skip_cons : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ →
    Ctx.Inter Γ Γ₁ (.skip ρ₁) (A :: Γ₂) (.cons ρ₂) (A.lift' ρ₂ :: Δ)
  | cons_skip : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ →
    Ctx.Inter Γ (A :: Γ₁) (.cons ρ₁) Γ₂ (.skip ρ₂) (A.lift' ρ₁ :: Δ)
  | cons_cons : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ →
    Ctx.Inter (A :: Γ) (A.lift' (ρ₂.diff ρ₁) :: Γ₁) (.cons ρ₁)
      (A.lift' (ρ₁.diff ρ₂) :: Γ₂) (.cons ρ₂) (A.lift' (ρ₁.inter ρ₂) :: Δ)

theorem lift_eq_lift {e₁ e₂ : Term} (H : e₁.lift' ρ₁ = e₂.lift' ρ₂) :
    ∃ e, .lift' e (ρ₂.diff ρ₁) = e₁ ∧ e.lift' (ρ₁.diff ρ₂) = e₂ := by
  have := Skips.lift e₁ ρ₁
  have h1 : _ = _ := skips_inter.2 ⟨.lift e₁ ρ₁, H ▸ Skips.lift e₂ ρ₂⟩
  have h2 := h1; conv at h1 => enter [1,2]; rw [← Lift.diff_comp]
  conv at h2 => enter [1,2]; rw [Lift.inter_comm, ← Lift.diff_comp]
  rw [lift'_comp] at h1 h2
  exact ⟨_, lift'_inj.1 h2, lift'_inj.1 (h1.trans H)⟩

theorem Ctx.Inter.mk (H1 : Ctx.Lift' l₁ Γ₁ Δ) (H2 : Ctx.Lift' l₂ Γ₂ Δ) :
    ∃ Γ, Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ := by
  induction H1 generalizing l₂ Γ₂ with
  | refl => exact ⟨_, .refl_l H2⟩
  | skip H1 ih =>
    cases H2 with
    | refl => exact ⟨_, .refl_r (.skip H1)⟩
    | skip H2 => let ⟨_, H⟩ := ih H2; exact ⟨_, .skip_skip H⟩
    | cons H2 => let ⟨_, H⟩ := ih H2; exact ⟨_, .skip_cons H⟩
  | @cons l₁ _ _ A₁ H1 ih =>
    generalize eq : A₁.lift' l₁ = A' at H2
    cases H2 with
    | refl => subst eq; exact ⟨_, .refl_r (.cons H1)⟩
    | skip H2 => subst eq; let ⟨_, H⟩ := ih H2; exact ⟨_, .cons_skip H⟩
    | @cons l₂ _ _ A₂ H2 =>
      obtain ⟨_, rfl, rfl⟩ := lift_eq_lift eq
      rw [← lift'_comp, Lift.diff_comp]
      let ⟨_, H⟩ := ih H2; exact ⟨_, .cons_cons H⟩

theorem Ctx.Inter.symm (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Inter Γ Γ₂ l₂ Γ₁ l₁ Δ := by
  induction H with
  | refl_l h => exact .refl_r h
  | refl_r h => exact .refl_l h
  | skip_skip _ ih => exact .skip_skip ih
  | skip_cons _ ih => exact .cons_skip ih
  | cons_skip _ ih => exact .skip_cons ih
  | cons_cons _ ih => rw [Lift.inter_comm]; exact .cons_cons ih

theorem Ctx.Inter.diff (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Lift' (l₁.diff l₂) Γ Γ₂ := by
  induction H with
  | refl_l h => exact .refl
  | refl_r h => simpa
  | skip_skip _ ih | cons_skip _ ih => exact ih
  | skip_cons _ ih => exact ih.skip
  | cons_cons _ ih => exact ih.cons

theorem Ctx.Inter.right (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Lift' l₂ Γ₂ Δ := by
  induction H with
  | refl_l h => exact h
  | refl_r h => exact .refl
  | skip_skip _ ih => exact ih.skip
  | cons_skip _ ih => exact ih.skip
  | skip_cons _ ih => exact ih.cons
  | cons_cons _ ih => rw [← Lift.diff_comp, Term.lift'_comp]; exact ih.cons

theorem Ctx.Inter.left (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Lift' l₁ Γ₁ Δ := H.symm.right

section
set_option hygiene false

inductive Lookup : List Term → Nat → Term → Prop where
  | zero : Lookup (ty::Γ) 0 ty.lift
  | succ : Lookup Γ n ty → Lookup (A::Γ) (n+1) ty.lift

theorem Lookup.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Lookup Γ i A) :
    Lookup Γ' (ρ.liftVar i) (A.lift' ρ) := by
  induction W generalizing i A with
  | refl => simp; exact H
  | skip W ih => have' := (ih H).succ; rwa [Term.lift, ← Term.lift'_comp] at this
  | cons W ih =>
    cases H with
    | zero => refine' cast _ Lookup.zero; congr 1; simp [Term.lift, ← Term.lift'_comp]
    | succ H => refine' cast _ (ih H).succ; congr 1; simp [Term.lift, ← Term.lift'_comp]

theorem Lookup.weakU_inv (W : Ctx.Lift' ρ Γ Γ')
    (H : Lookup Γ' (ρ.liftVar i) A') : ∃ A, A' = A.lift' ρ ∧ Lookup Γ i A := by
  induction W generalizing i A' with
  | refl => simpa using H
  | @skip ρ W _ _ _ ih =>
    simp at H; let .succ H := H
    obtain ⟨_, rfl, h2⟩ := ih H; refine ⟨_, ?_, h2⟩
    rw [Term.lift, ← Term.lift'_comp]; rfl
  | @cons ρ Γ Δ B W ih =>
    cases i with
    | zero => cases H; exact ⟨_, by simp [Term.lift, ← Term.lift'_comp], .zero⟩
    | succ i =>
      let .succ (ty := C) H := H
      obtain ⟨C, rfl, h⟩ := ih H
      refine ⟨_, ?_, .succ h⟩
      simp [Term.lift, ← Term.lift'_comp]

theorem Lookup.weak'_inv (W : Ctx.Lift' ρ Γ Γ')
    (H : Lookup Γ' (ρ.liftVar i) (A.lift' ρ)) : Lookup Γ i A := by
  let ⟨_, h1, h2⟩ := H.weakU_inv W
  exact lift'_inj.1 h1 ▸ h2

theorem Lookup.uniq (hA : Lookup Γ i A) (hB : Lookup Γ i B) : A = B :=
  match hA, hB with
  | .zero, .zero => rfl
  | .succ hA, .succ hB => Lookup.uniq hA hB ▸ rfl

theorem Lookup.determ (H1 : Lookup Γ i A) (H2 : Lookup Γ i A') : A = A' := by
  induction H1 generalizing A' with obtain _ | r1 := H2
  | zero => rfl
  | succ _ ih => cases ih r1; rfl

section
local notation:65 (priority := high) Γ " ⊢ " e1 " : " A:36 => IsDefEq Γ e1 e1 A
local notation:65 (priority := high) Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEq Γ e1 e2 A
inductive IsDefEq : List Term → Term → Term → Term → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ A : .sort u → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  /-- Heterogeneous transitivity: middle term may be at a different sort. -/
  | trans' : Γ ⊢ A ≡ B : .sort u → Γ ⊢ B ≡ C : .sort v → Γ ⊢ A ≡ C : .sort u
  | sort : Γ ⊢ .sort l : .sort true
  | appDF : Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v →
    Γ ⊢ f ≡ f' : .forallE A B → Γ ⊢ a ≡ a' : A →
    Γ ⊢ B.inst a ≡ B.inst a' : .sort v →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | lamDF : Γ ⊢ A ≡ A' : .sort u → A::Γ ⊢ B : .sort v →
    A::Γ ⊢ body ≡ body' : B → A'::Γ ⊢ body ≡ body' : B →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF : Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : .sort v → A'::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort v
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B
  | beta : Γ ⊢ A : .sort u → A::Γ ⊢ e : B → Γ ⊢ e' : A →
    Γ ⊢ .app (.lam A e) e' : B.inst e' → Γ ⊢ e.inst e' : B.inst e' →
    Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta : Γ ⊢ e : .forallE A B → Γ ⊢ .lam A (.app e.lift (.bvar 0)) : .forallE A B →
    Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel : Γ ⊢ p : .sort false → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ h' : p
end
scoped notation:65 Γ " ⊢ " e1 " : " A:36 => IsDefEq Γ e1 e1 A
scoped notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEq Γ e1 e2 A

theorem IsDefEq.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ' ⊢ e1.lift' ρ ≡ e2.lift' ρ : A.lift' ρ := by
  induction H generalizing ρ Γ' with
  | bvar h1 _ ih => refine .bvar (h1.weak' W) (ih W)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | trans' _ _ ih1 ih2 => exact .trans' (ih1 W) (ih2 W)
  | sort => exact .sort
  | appDF _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact lift'_inst_hi .. ▸ .appDF (ih1 W) (ih2 W.cons) (ih3 W) (ih4 W)
      (lift'_inst_hi .. ▸ lift'_inst_hi .. ▸ ih5 W)
  | lamDF _ _ _ _ ih1 ih2 ih3 ih4 =>
    exact .lamDF (ih1 W) (ih2 W.cons) (ih3 W.cons) (ih4 W.cons)
  | forallEDF _ _ _ ih1 ih2 ih3 => exact .forallEDF (ih1 W) (ih2 W.cons) (ih3 W.cons)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  | beta _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    rw [lift'_inst_hi, lift'_inst_hi]
    refine .beta (ih1 W) (ih2 W.cons) (ih3 W) ?_ ?_
    · rw [← lift'_inst_hi]; exact ih4 W
    · rw [← lift'_inst_hi, ← lift'_inst_hi]; exact ih5 W
  | eta _ _ ih1 ih2 =>
    refine cast ?_ (IsDefEq.eta (ih1 W) (cast ?_ (ih2 W)))
    all_goals simp [lift', ← lift'_comp]
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)

theorem IsDefEq.hasType (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ ⊢ e1 : A ∧ Γ ⊢ e2 : A :=
  ⟨H.trans H.symm, H.symm.trans H⟩

/-- Each variable's type in the context has a sort-typing derivation in IsDefEq. -/
def Ctx.WF : List Term → Prop
  | [] => True
  | A :: Γ => Ctx.WF Γ ∧ ∃ u, Γ ⊢ A : .sort u
scoped notation:65 "⊢ " Γ:36 => Ctx.WF Γ

theorem Ctx.WF.lookup {Γ} (H : ⊢ Γ) (h : Lookup Γ i A) :
    ∃ u, Γ ⊢ A : .sort u := by
  induction h with
  | zero => let ⟨_, _, hA⟩ := H; exact ⟨_, hA.weak' (.skip .refl)⟩
  | @succ Γ n ty A h ih =>
    let ⟨H', _⟩ := H
    let ⟨_, hA⟩ := ih H'
    exact ⟨_, hA.weak' (.skip .refl)⟩

theorem IsDefEq.isType (hΓ : ⊢ Γ) (H : Γ ⊢ e1 ≡ e2 : A) : ∃ u, Γ ⊢ A : .sort u := by
  induction H with
  | bvar h _ => exact hΓ.lookup h
  | symm _ ih => exact ih hΓ
  | trans _ _ ih1 _ => exact ih1 hΓ
  | trans' _ _ _ _ => exact ⟨_, .sort⟩
  | sort => exact ⟨_, .sort⟩
  | appDF _ _ _ _ h5 _ _ _ _ _ => exact ⟨_, h5.hasType.1⟩
  | lamDF h1 h2 _ _ => exact ⟨_, .forallEDF h1.hasType.1 h2 h2⟩
  | forallEDF => exact ⟨_, .sort⟩
  | defeqDF h1 _ _ _ => exact ⟨_, h1.hasType.2⟩
  | beta _ _ _ _ _ _ _ _ ih _ => exact ih hΓ
  | eta _ _ ih _ => exact ih hΓ
  | proofIrrel h1 _ _ _ _ _ => exact ⟨_, h1⟩

@[simp] theorem Subst.lift_r_head {σ : Subst} {ρ : Lift} :
    (σ.lift_r ρ).head = σ.head.lift' ρ := rfl
theorem Subst.lift_r_tail {σ : Subst} {ρ : Lift} :
    (σ.lift_r ρ).tail = σ.tail.lift_r ρ := by
  funext i; rfl
theorem Subst.lift_r_toSubst {ρ ρ' : Lift} :
    ρ.toSubst.lift_r ρ' = (ρ.comp ρ').toSubst := by
  funext i
  show (Term.bvar (ρ.liftVar i)).lift' ρ' = Term.bvar ((ρ.comp ρ').liftVar i)
  simp [lift', Lift.liftVar_comp]

/-- Two-sided strong substitution structure. Each `.cons` entry carries
`` ⊢ witnesses ≡ sort proof in source `Γ` and head-equality in target
`Γ₀` : . The `.nil` constructor allows arbitrary `σ`, `σ'` for an empty source. -/
inductive Ctx.SubstEq (Γ₀ : List Term) : Subst → Subst → List Term → Prop where
  | nil : Ctx.SubstEq Γ₀ σ σ' []
  | cons : Ctx.SubstEq Γ₀ σ.tail σ'.tail Γ →
    Γ ⊢ A : .sort u →
    Γ₀ ⊢ σ.head ≡ σ'.head : A.subst σ.tail →
    Ctx.SubstEq Γ₀ σ σ' (A :: Γ)

/-- Diagonal left-projection: extract `SubstEq Γ₀ σ σ Γ` from a two-sided
`SubstEq Γ₀ σ σ' Γ` using `.hasType.1` of each head witness. -/
theorem Ctx.SubstEq.left (W : Ctx.SubstEq Γ₀ σ σ' Γ) : Ctx.SubstEq Γ₀ σ σ Γ := by
  induction W with
  | nil => exact .nil
  | cons _ hA hhead ih => exact .cons ih hA hhead.hasType.1

/-- Variable substitution lookup. -/
theorem Ctx.SubstEq.lookup (W : Ctx.SubstEq Γ₀ σ σ' Γ) :
    Lookup Γ i A → Γ₀ ⊢ σ i ≡ σ' i : A.subst σ := by
  intro h
  induction W generalizing i A with
  | nil => nomatch h
  | cons W' hA' hhead ih =>
    cases h with
    | zero =>
      simp only [show ∀ (s : Subst), s 0 = s.head from fun _ => rfl, lift_subst]
      exact hhead
    | @succ Γ'' n ty B h' =>
      simp only [show ∀ (s : Subst) n, s (n+1) = s.tail n from fun _ _ => rfl, lift_subst]
      exact ih h'

/-- Codomain-weakening of a `SubstEq` by one fresh variable. -/
theorem Ctx.SubstEq.skip (W : Ctx.SubstEq Γ₀ σ σ' Γ) :
    Ctx.SubstEq (B :: Γ₀) (σ.lift_r (.skip .refl)) (σ'.lift_r (.skip .refl)) Γ := by
  induction W with
  | nil => exact .nil
  | @cons _ _ _ _ _ _ hA' hhead ih =>
    refine .cons (Subst.lift_r_tail ▸ ih) hA' ?_
    rw [Subst.lift_r_tail]
    have := IsDefEq.weak' (Ctx.Lift'.skip (A := B) .refl) hhead
    rw [lift'_subst] at this
    exact this

/-- Extension of a `SubstEq` under a binder. -/
theorem Ctx.SubstEq.lift (W : Ctx.SubstEq Γ₀ σ σ' Γ)
    (hA : Γ ⊢ A : .sort u)
    (hA' : Γ₀ ⊢ A.subst σ : .sort u) :
    Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift σ'.lift (A :: Γ) := by
  have htail : σ.lift.tail = σ.lift_r (.skip .refl) := by
    funext i; simp [Subst.tail, Subst.lift, Subst.lift_r]
  have htail' : σ'.lift.tail = σ'.lift_r (.skip .refl) := by
    funext i; simp [Subst.tail, Subst.lift, Subst.lift_r]
  refine .cons (htail ▸ htail' ▸ W.skip) hA ?_
  show A.subst σ :: Γ₀ ⊢ .bvar 0 : A.subst σ.lift.tail
  rw [htail]
  rw [show A.subst (σ.lift_r (.skip .refl)) = (A.subst σ).lift' (.skip .refl) from
    (lift'_subst (e := A) (σ := σ) (ρ := .skip .refl)).symm]
  exact .bvar Lookup.zero (hA'.weak' (.skip .refl))

/-- Identity substitution from any well-formed context to itself. -/
theorem Ctx.SubstEq.id : ∀ {Γ}, ⊢ Γ → Ctx.SubstEq Γ .id .id Γ
  | [], _ => .nil
  | A::Γ, ⟨hΓ, _, hA⟩ => by
    refine .cons (id hΓ).skip hA ?_
    rw [show A.subst Subst.id.tail = A.lift' (.skip .refl) by
      show A.subst (Subst.id.lift_r (.skip .refl)) = _
      rw [← lift'_subst, subst_id]]
    exact .bvar Lookup.zero (hA.weak' (.skip .refl))

section
set_option hygiene false
local notation:65 Γ " ⊢₀ " e " : " A:36 " !! " n:36 => HasTypeStratifiedS Γ e A true n
local notation:65 Γ " ⊢₀ " e " :! " A:36 " !! " n:36 => HasTypeStratifiedS Γ e A false n

/-- The source context of any `SubstEq` is strong (recoverable from the per-`cons`
sort proofs of each variable's type). -/
theorem Ctx.SubstEq.ctxStrong : ∀ {Γ₀ σ σ' Γ}, Ctx.SubstEq Γ₀ σ σ' Γ → ⊢ Γ
  | _, _, _, _, .nil => True.intro
  | _, _, _, _, .cons inner hA _ => ⟨inner.ctxStrong, _, hA⟩

/-- Generalized lift extending `W` into `X :: Γ₀` for any sort-typed `X` that is
defeq to `A.subst σ` in `Γ₀`. When `X = A.subst σ` this reduces to `SubstEq.lift`. -/
theorem Ctx.SubstEq.lift_at (W : Ctx.SubstEq Γ₀ σ σ' Γ)
    (hA : Γ ⊢ A : .sort u)
    (hX : Γ₀ ⊢ X : .sort u)
    (hAX : Γ₀ ⊢ A.subst σ ≡ X : .sort u) :
    Ctx.SubstEq (X :: Γ₀) σ.lift σ'.lift (A :: Γ) := by
  have htail : σ.lift.tail = σ.lift_r (.skip .refl) := by
    funext i; simp [Subst.tail, Subst.lift, Subst.lift_r]
  have htail' : σ'.lift.tail = σ'.lift_r (.skip .refl) := by
    funext i; simp [Subst.tail, Subst.lift, Subst.lift_r]
  refine .cons (htail ▸ htail' ▸ W.skip) hA ?_
  show X :: Γ₀ ⊢ .bvar 0 : A.subst σ.lift.tail
  rw [htail,
      show A.subst (σ.lift_r (.skip .refl)) = (A.subst σ).lift' (.skip .refl) from
        (lift'_subst (e := A) (σ := σ) (ρ := .skip .refl)).symm]
  exact .defeqDF (hAX.symm.weak' (.skip .refl))
    (.bvar .zero (hX.weak' (.skip .refl)))

theorem IsDefEq.substEq' {Γ₀ Γ : List Term} {σ τ : Subst} {e1 e2 A : Term}
    (hΓ₀ : ⊢ Γ₀) (hΓ : ⊢ Γ)
    (W : Ctx.SubstEq Γ₀ σ τ Γ) (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ₀ ⊢ e1.subst σ ≡ e1.subst τ : A.subst σ ∧
    Γ₀ ⊢ e2.subst σ ≡ e2.subst τ : A.subst σ ∧
    Γ₀ ⊢ e1.subst σ ≡ e2.subst τ : A.subst σ := by
  induction H generalizing Γ₀ σ τ with
  | bvar h _ => exact ⟨W.lookup h, W.lookup h, W.lookup h⟩
  | sort => exact ⟨.sort, .sort, .sort⟩
  | symm _ ih => let ⟨l, r, c⟩ := ih hΓ₀ hΓ W; exact ⟨r, l, (r.trans c.symm).trans l⟩
  | trans _ _ ih1 ih2 =>
    let ⟨l1, _, c1⟩ := ih1 hΓ₀ hΓ W
    let ⟨l2, r2, c2⟩ := ih2 hΓ₀ hΓ W
    exact ⟨l1, r2, c1.trans (l2.symm.trans c2)⟩
  | trans' _ _ ih1 ih2 =>
    let ⟨l1, _, c1⟩ := ih1 hΓ₀ hΓ W
    let ⟨l2, _, c2⟩ := ih2 hΓ₀ hΓ W
    have cross := c1.trans' (l2.symm.trans c2)
    exact ⟨l1, ((ih1 hΓ₀ hΓ W.left).2.2.trans' (ih2 hΓ₀ hΓ W.left).2.2).symm.trans cross, cross⟩
  | defeqDF _ _ ih1 ih2 =>
    have := (ih1 hΓ₀ hΓ W.left).2.2
    let ⟨l2, r2, c2⟩ := ih2 hΓ₀ hΓ W
    exact ⟨.defeqDF this l2, .defeqDF this r2, .defeqDF this c2⟩
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    let ⟨ihp, _, _⟩ := ih1 hΓ₀ hΓ W
    let ⟨ihh, _, _⟩ := ih2 hΓ₀ hΓ W
    let ⟨ihh', _, _⟩ := ih3 hΓ₀ hΓ W
    refine ⟨ihh, ihh', .proofIrrel ihp.hasType.1 ihh.hasType.1 ihh'.hasType.2⟩
  | @eta Γ e A B _ _ ih1 ih2 =>
    have ih1_l := (ih1 hΓ₀ hΓ W).1
    have ih2_l := (ih2 hΓ₀ hΓ W).1
    have he_σ := (ih1 hΓ₀ hΓ W.left).1
    have hlam_σ := (ih2 hΓ₀ hΓ W.left).1
    have h_lift_subst : e.lift.subst σ.lift = (e.subst σ).lift := by
      rw [subst_lift', lift, lift'_subst]; rfl
    have h_lam_eq : (Term.lam A (.app e.lift (.bvar 0))).subst σ =
        .lam (A.subst σ) (.app (e.subst σ).lift (.bvar 0)) := by
      show Term.lam (A.subst σ) (.app (e.lift.subst σ.lift) ((Term.bvar 0).subst σ.lift)) = _
      rw [h_lift_subst]; rfl
    have H_σ : Γ₀ ⊢ (Term.lam A (.app e.lift (.bvar 0))).subst σ ≡ e.subst σ : (Term.forallE A B).subst σ := h_lam_eq ▸ .eta he_σ (h_lam_eq ▸ hlam_σ)
    exact ⟨ih2_l, ih1_l, H_σ.trans ih1_l⟩
  | @beta Γ A u e B e' hA _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    have ih5_l := (ih5 hΓ₀ hΓ W).1
    have ih4_l := (ih4 hΓ₀ hΓ W).1
    have hA_σ := (ih1 hΓ₀ hΓ W.left).1
    have W_A_left : Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift σ.lift (A :: Γ) :=
      W.left.lift hA hA_σ
    have hΓ_A : ⊢ A :: Γ := ⟨hΓ, _, hA⟩
    have hΓ_A_subst : ⊢ A.subst σ :: Γ₀ := ⟨hΓ₀, _, hA_σ⟩
    have he_σ := (ih2 hΓ_A_subst hΓ_A W_A_left).1
    have he'_σ := (ih3 hΓ₀ hΓ W.left).1
    have happ_σ := (ih4 hΓ₀ hΓ W.left).1
    have heinst_σ := (ih5 hΓ₀ hΓ W.left).1
    have H_σ : Γ₀ ⊢ (Term.app (Term.lam A e) e').subst σ ≡ (e.inst e').subst σ : (B.inst e').subst σ := by
      show Γ₀ ⊢ Term.app (Term.lam (A.subst σ) (e.subst σ.lift)) (e'.subst σ) ≡ _ : _
      rw [show ((e.inst e').subst σ) = (e.subst σ.lift).inst (e'.subst σ) from subst_inst,
          show ((B.inst e').subst σ) = (B.subst σ.lift).inst (e'.subst σ) from subst_inst]
      refine .beta hA_σ he_σ he'_σ ?_ ?_
      · rw [show ((B.subst σ.lift).inst (e'.subst σ)) = (B.inst e').subst σ from subst_inst.symm]
        exact happ_σ
      · rw [show ((B.subst σ.lift).inst (e'.subst σ)) = (B.inst e').subst σ from subst_inst.symm,
            show ((e.subst σ.lift).inst (e'.subst σ)) = (e.inst e').subst σ from subst_inst.symm]
        exact heinst_σ
    exact ⟨ih4_l, ih5_l, H_σ.trans ih5_l⟩
  | @appDF Γ A u B v f f' a a' hA _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    have hA' := (ih1 hΓ₀ hΓ W).1.hasType.1
    have hΓ_A : ⊢ A :: Γ := ⟨hΓ, _, hA⟩
    have hΓ_A_subst : ⊢ A.subst σ :: Γ₀ := ⟨hΓ₀, _, hA'⟩
    have W_A_diag : Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift σ.lift (A :: Γ) :=
      W.left.lift hA hA'
    have hB' := (ih2 hΓ_A_subst hΓ_A W_A_diag).1
    have ⟨ihf_l, ihf_r, ihf_c⟩ := ih3 hΓ₀ hΓ W
    have ⟨iha_l, iha_r, iha_c⟩ := ih4 hΓ₀ hΓ W
    have ⟨_, _, iha_cleft⟩ := ih4 hΓ₀ hΓ W.left
    -- Construct (B.σ.lift).inst x ≡ (B.σ.lift).inst y at sort v from ih2 at SubstEq.cons.
    have ih2_cons : ∀ {x y : Term}, Γ₀ ⊢ x ≡ y : A.subst σ →
        Γ₀ ⊢ (B.subst σ.lift).inst x ≡ (B.subst σ.lift).inst y : .sort v := by
      intro x y hxy
      have htail_x : (σ.cons x).tail = σ := by funext i; rfl
      have htail_y : (σ.cons y).tail = σ := by funext i; rfl
      have W_cons : Ctx.SubstEq Γ₀ (σ.cons x) (σ.cons y) (A :: Γ) := by
        refine .cons (htail_x ▸ htail_y ▸ W.left) hA ?_
        show Γ₀ ⊢ x ≡ y : A.subst (σ.cons x).tail
        rw [htail_x]; exact hxy
      have := (ih2 hΓ₀ hΓ_A W_cons).1
      rwa [← inst_lift_cons, ← inst_lift_cons] at this
    refine subst_inst ▸ ⟨?_, .defeqDF (ih2_cons iha_cleft.symm) ?_, ?_⟩
    · exact .appDF hA' hB' ihf_l iha_l (ih2_cons iha_l)
    · exact .appDF hA' hB' ihf_r iha_r (ih2_cons iha_r)
    · exact .appDF hA' hB' ihf_c iha_c (ih2_cons iha_c)
  | @lamDF Γ A A' u B v body body' h1 _ _ _ ih1 ih2 ih3 ih4 =>
    -- h1 : A ≡ A' : sort u; h2 : A::Γ ⊢₀ B : sort v (diagonal);
    -- h3 : A::Γ ⊢₀ body ≡ body' : B; h4 : A'::Γ ⊢₀ body ≡ body' : B.
    let ⟨ihA_l, ihA_r, ihA_c⟩ := ih1 hΓ₀ hΓ W
    have hA_in_Γ : Γ ⊢ A : .sort u := h1.hasType.1
    have hA'_in_Γ : Γ ⊢ A' : .sort u := h1.hasType.2
    have hA_subst : Γ₀ ⊢ A.subst σ : .sort u := ihA_l.hasType.1
    have hA_τ_subst : Γ₀ ⊢ A.subst τ : .sort u := ihA_l.hasType.2
    have hA'_subst : Γ₀ ⊢ A'.subst σ : .sort u := ihA_r.hasType.1
    have hA'_τ_subst : Γ₀ ⊢ A'.subst τ : .sort u := ihA_r.hasType.2
    have hΓ_A : ⊢ A :: Γ := ⟨hΓ, _, hA_in_Γ⟩
    have hΓ_A' : ⊢ A' :: Γ := ⟨hΓ, _, hA'_in_Γ⟩
    have hΓ_A_subst : ⊢ A.subst σ :: Γ₀ := ⟨hΓ₀, _, hA_subst⟩
    have hΓ_A_τ_subst : ⊢ A.subst τ :: Γ₀ := ⟨hΓ₀, _, hA_τ_subst⟩
    have hΓ_A'_subst : ⊢ A'.subst σ :: Γ₀ := ⟨hΓ₀, _, hA'_subst⟩
    have hΓ_A'_τ_subst : ⊢ A'.subst τ :: Γ₀ := ⟨hΓ₀, _, hA'_τ_subst⟩
    have hAA'_σ : Γ₀ ⊢ A.subst σ ≡ A'.subst σ : .sort u :=
      (ih1 hΓ₀ hΓ W.left).2.2
    -- W extensions to all four "front element" choices.
    have W_A : Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift τ.lift (A :: Γ) :=
      W.lift hA_in_Γ hA_subst
    have W_A_τ : Ctx.SubstEq (A.subst τ :: Γ₀) σ.lift τ.lift (A :: Γ) :=
      W.lift_at hA_in_Γ hA_τ_subst ihA_l
    have W_A' : Ctx.SubstEq (A'.subst σ :: Γ₀) σ.lift τ.lift (A' :: Γ) :=
      W.lift hA'_in_Γ hA'_subst
    have W_A'_τ : Ctx.SubstEq (A'.subst τ :: Γ₀) σ.lift τ.lift (A' :: Γ) :=
      W.lift_at hA'_in_Γ hA'_τ_subst ihA_r
    -- For the cross conjunct: extend `h3` (whose source ctx is `A::Γ`) into `A'.τ::Γ₀`.
    have W_A_to_A'τ : Ctx.SubstEq (A'.subst τ :: Γ₀) σ.lift τ.lift (A :: Γ) :=
      W.lift_at hA_in_Γ hA'_τ_subst ihA_c
    -- B sort proof at A'.σ::Γ₀ via diagonal-σ lift_at + ih2.
    have W_left_A'σ : Ctx.SubstEq (A'.subst σ :: Γ₀) σ.lift σ.lift (A :: Γ) :=
      W.left.lift_at hA_in_Γ hA'_subst hAA'_σ
    let ⟨ihB_l, _, _⟩ := ih2 hΓ_A_subst hΓ_A W_A
    have hB_at_A'σ := (ih2 hΓ_A'_subst hΓ_A W_left_A'σ).1
    let ⟨ih3body_l, _, ih3body_c⟩ := ih3 hΓ_A_subst hΓ_A W_A
    have ih3body_l_at_Aτ := (ih3 hΓ_A_τ_subst hΓ_A W_A_τ).1
    have ih3body_c_at_A'τ := (ih3 hΓ_A'_τ_subst hΓ_A W_A_to_A'τ).2.2
    let ⟨_, ih4body_r, _⟩ := ih4 hΓ_A'_subst hΓ_A' W_A'
    have ih4body_r_at_A'τ := (ih4 hΓ_A'_τ_subst hΓ_A' W_A'_τ).2.1
    refine ⟨?_, ?_, ?_⟩
    · exact .lamDF ihA_l ihB_l.hasType.1 ih3body_l ih3body_l_at_Aτ
    · have lamform :=
        IsDefEq.lamDF ihA_r hB_at_A'σ ih4body_r ih4body_r_at_A'τ
      have hforallE_eq :
          Γ₀ ⊢ (A'.subst σ).forallE (B.subst σ.lift) ≡ (A.subst σ).forallE (B.subst σ.lift) : .sort v :=
        .forallEDF hAA'_σ.symm hB_at_A'σ ihB_l.hasType.1
      exact .defeqDF hforallE_eq lamform
    · exact .lamDF ihA_c ihB_l.hasType.1 ih3body_c ih3body_c_at_A'τ
  | @forallEDF Γ A A' u body body' v h1 h2 _ ih1 ih2 ih3 =>
    -- h1 : Γ ⊢₀ A ≡ A' : sort u; h2 : A::Γ ⊢₀ body ≡ body' : sort v;
    -- h3 : A'::Γ ⊢₀ body ≡ body' : sort v (3rd premise).
    let ⟨ihA_l, ihA_r, ihA_c⟩ := ih1 hΓ₀ hΓ W
    have hA_in_Γ : Γ ⊢ A : .sort u := h1.hasType.1
    have hA'_in_Γ : Γ ⊢ A' : .sort u := h1.hasType.2
    have hA_subst : Γ₀ ⊢ A.subst σ : .sort u := ihA_l.hasType.1
    have hA'_subst : Γ₀ ⊢ A'.subst σ : .sort u := ihA_r.hasType.1
    have hΓ_A : ⊢ A :: Γ := ⟨hΓ, _, hA_in_Γ⟩
    have hΓ_A' : ⊢ A' :: Γ := ⟨hΓ, _, hA'_in_Γ⟩
    have hΓ_A_subst : ⊢ A.subst σ :: Γ₀ := ⟨hΓ₀, _, hA_subst⟩
    have hΓ_A'_subst : ⊢ A'.subst σ :: Γ₀ := ⟨hΓ₀, _, hA'_subst⟩
    have hA_τ_subst : Γ₀ ⊢ A.subst τ : .sort u := ihA_l.hasType.2
    have hA'_τ_subst : Γ₀ ⊢ A'.subst τ : .sort u := ihA_r.hasType.2
    have hΓ_A_τ_subst : ⊢ A.subst τ :: Γ₀ := ⟨hΓ₀, _, hA_τ_subst⟩
    have hΓ_A'_τ_subst : ⊢ A'.subst τ :: Γ₀ := ⟨hΓ₀, _, hA'_τ_subst⟩
    have W_A : Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift τ.lift (A :: Γ) :=
      W.lift hA_in_Γ hA_subst
    have W_A' : Ctx.SubstEq (A'.subst σ :: Γ₀) σ.lift τ.lift (A' :: Γ) :=
      W.lift hA'_in_Γ hA'_subst
    -- Each conjunct's 3rd .forallEDF arg lives in A_right::Γ; build by re-calling
    -- ih2/ih3 at a `lift_at`-extended W where the front element is `A_right.subst τ`.
    have W_A_τ : Ctx.SubstEq (A.subst τ :: Γ₀) σ.lift τ.lift (A :: Γ) :=
      W.lift_at hA_in_Γ hA_τ_subst ihA_l
    have W_A'_τ : Ctx.SubstEq (A'.subst τ :: Γ₀) σ.lift τ.lift (A' :: Γ) :=
      W.lift_at hA'_in_Γ hA'_τ_subst ihA_r
    have W_A_to_A'τ : Ctx.SubstEq (A'.subst τ :: Γ₀) σ.lift τ.lift (A :: Γ) :=
      W.lift_at hA_in_Γ hA'_τ_subst ihA_c
    let ⟨ihB_l, _, ihB_c⟩ := ih2 hΓ_A_subst hΓ_A W_A
    have ihB_l_at_Aτ := (ih2 hΓ_A_τ_subst hΓ_A W_A_τ).1
    have ihB_c_at_A'τ := (ih2 hΓ_A'_τ_subst hΓ_A W_A_to_A'τ).2.2
    let ⟨_, ihB'_r, _⟩ := ih3 hΓ_A'_subst hΓ_A' W_A'
    have ihB'_r_at_A'τ := (ih3 hΓ_A'_τ_subst hΓ_A' W_A'_τ).2.1
    refine ⟨.forallEDF ihA_l ihB_l ihB_l_at_Aτ,
            .forallEDF ihA_r ihB'_r ihB'_r_at_A'τ,
            .forallEDF ihA_c ihB_c ihB_c_at_A'τ⟩

/-- Main substitution lemma for ``, ⊢ derived ≡ as : a corollary of the
two-sided `substEq'`. Takes a diagonal `Ctx.SubstEq Γ₀ σ σ Γ`; the cross conjunct
of `substEq'` at diagonal `W` gives `e1.subst σ ≡ e2.subst σ`. -/
theorem IsDefEq.subst (hΓ₀ : ⊢ Γ₀) (hΓ : ⊢ Γ)
    (W : Ctx.SubstEq Γ₀ σ σ Γ) (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ₀ ⊢ e1.subst σ ≡ e2.subst σ : A.subst σ :=
  (H.substEq' hΓ₀ hΓ W).2.2

/-- Non-diagonal substitution: takes a two-sided `SubstEq Γ₀ σ σ' Γ` and yields
`e1.subst σ ≡ e2.subst σ'` (the cross conjunct of `substEq'`). -/
theorem IsDefEq.subst' (hΓ₀ : ⊢ Γ₀) (hΓ : ⊢ Γ)
    (W : Ctx.SubstEq Γ₀ σ σ' Γ) (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ₀ ⊢ e1.subst σ ≡ e2.subst σ' : A.subst σ :=
  (H.substEq' hΓ₀ hΓ W).2.2

theorem Ctx.SubstEq.symm (hΓ₀ : ⊢ Γ₀) (W : Ctx.SubstEq Γ₀ σ σ' Γ) :
    Ctx.SubstEq Γ₀ σ' σ Γ := by
  induction W with
  | nil => exact .nil
  | cons inner hA hhead ih =>
    exact .cons ih hA
      (.defeqDF (hA.substEq' hΓ₀ inner.ctxStrong inner).2.2 hhead.symm)

/-- Diagonal right-projection: from a two-sided `SubstEq Γ₀ σ σ' Γ`, extract the
diagonal `SubstEq Γ₀ σ' σ' Γ` using `.hasType.2` of each head witness, with the
type on each head adjusted (`A.subst σ.tail` vs `A.subst σ'.tail`) via the cross
conjunct of `substEq'` on `hA`. -/
theorem Ctx.SubstEq.right (hΓ₀ : ⊢ Γ₀) (W : Ctx.SubstEq Γ₀ σ σ' Γ) :
    Ctx.SubstEq Γ₀ σ' σ' Γ := by
  induction W with
  | nil => exact .nil
  | cons inner hA hhead ih =>
    exact .cons ih hA
      (.defeqDF (hA.substEq' hΓ₀ inner.ctxStrong inner).2.2 hhead.hasType.2)

/-- Substitution at position 0 (single-variable instantiation), derived from
the general `IsDefEq.subst` lemma using
`SubstS.cons (SubstS.weak .refl) hA₀ h₀`. -/
theorem IsDefEq.inst0 (hΓ : ⊢ Γ)
    (h₀ : Γ ⊢ e₀ : A₀)
    (H : A₀::Γ ⊢ e1 ≡ e2 : A) :
    Γ ⊢ e1.inst e₀ ≡ e2.inst e₀ : A.inst e₀ := by
  have ⟨_, hA₀⟩ := h₀.isType hΓ
  have hΓ' : ⊢ A₀ :: Γ := ⟨hΓ, _, hA₀⟩
  have W₀ : Ctx.SubstEq Γ Subst.id Subst.id Γ := Ctx.SubstEq.id hΓ
  have hhead : Γ ⊢ (Subst.one e₀).head : A₀.subst (Subst.one e₀).tail := by
    show Γ ⊢ e₀ : A₀.subst Subst.id
    rw [subst_id]
    exact h₀
  have W : Ctx.SubstEq Γ (Subst.one e₀) (Subst.one e₀) (A₀ :: Γ) := by
    have htail : (Subst.one e₀).tail = Subst.id := by funext i; rfl
    refine .cons (σ := Subst.one e₀) (σ' := Subst.one e₀) ?_ hA₀ hhead
    rw [htail]; exact W₀
  exact H.subst hΓ hΓ' W

theorem IsDefEq.instDF (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A : .sort u)
    (hB : A::Γ ⊢ B : .sort v)
    (hf : A::Γ ⊢ f ≡ f' : B)
    (ha : Γ ⊢ a ≡ a' : A) :
    Γ ⊢ f.inst a ≡ f'.inst a' : B.inst a :=
  have H2 {f f' B v}
      (hB : A::Γ ⊢ B : .sort v)
      (hf : A::Γ ⊢ f ≡ f' : B)
      (hi : Γ ⊢ B.inst a ≡ B.inst a' : .sort v) :
      Γ ⊢ f.inst a ≡ f'.inst a' : B.inst a :=
    have H1 {a f}
        (hf : A::Γ ⊢ f ≡ f' : B)
        (ha : Γ ⊢ a : A) :
        Γ ⊢ .app (.lam A f) a ≡ f.inst a : B.inst a :=
      .beta hA hf.hasType.1 ha
        (.appDF hA hB (.lamDF hA hB hf.hasType.1 hf.hasType.1) ha
          (.inst0 hΓ ha.hasType.1 hB))
        (.inst0 hΓ ha.hasType.1 hf.hasType.1)
    (H1 hf ha.hasType.1).symm.trans <|
      .trans (.appDF hA hB (.lamDF hA hB hf hf) ha hi) <|
      .defeqDF (.symm hi) (H1 hf.hasType.2 ha.hasType.2)
  H2 hB hf <| H2 .sort hB .sort

theorem lift_cons_skip_inst_bvar0 {X : Term} :
    (X.lift' (.cons (.skip .refl))).inst (.bvar 0) = X := by
  have hsub : (Subst.lift_l (.cons (.skip .refl)) (Subst.one (.bvar 0))) = (Subst.id : Subst) := by
    funext i; cases i with
    | zero => rfl
    | succ i => rfl
  show (X.lift' (.cons (.skip .refl))).subst (.one (.bvar 0)) = X
  rw [subst_lift', hsub, subst_id]

theorem IsDefEq.defeqDF_l (hΓ : ⊢ Γ)
    (h1 : Γ ⊢ A ≡ A' : .sort u)
    (h2 : A::Γ ⊢ e1 ≡ e2 : B) : A'::Γ ⊢ e1 ≡ e2 : B := by
  have hΓ_A' : ⊢ A' :: Γ := ⟨hΓ, _, h1.hasType.2⟩
  have h1w : A' :: Γ ⊢ A.lift ≡ A'.lift : .sort u := h1.weak' (.skip .refl)
  have hbvar : A' :: Γ ⊢ .bvar 0 : A.lift :=
    .defeqDF h1w.symm (.bvar .zero (h1.hasType.2.weak' (.skip .refl)))
  have h2w : A.lift :: A' :: Γ ⊢ e1.lift' (.cons (.skip .refl)) ≡ e2.lift' (.cons (.skip .refl)) : B.lift' (.cons (.skip .refl)) :=
    h2.weak' (.cons (.skip .refl))
  have := IsDefEq.inst0 hΓ_A' hbvar h2w
  rwa [lift_cons_skip_inst_bvar0, lift_cons_skip_inst_bvar0, lift_cons_skip_inst_bvar0] at this

theorem IsDefEq.forallE_inv' (hΓ : ⊢ Γ)
    (H : Γ ⊢ e1 ≡ e2 : V) (eq : e1 = A.forallE B ∨ e2 = A.forallE B) :
    (∃ u, Γ ⊢ A : .sort u) ∧
    ∃ v, A::Γ ⊢ B : .sort v := by
  induction H generalizing A B with
  | symm _ ih => exact ih hΓ eq.symm
  | trans _ _ ih1 ih2
  | trans' _ _ ih1 ih2
  | proofIrrel _ _ _ _ ih1 ih2 =>
    obtain eq | eq := eq
    · exact ih1 hΓ (.inl eq)
    · exact ih2 hΓ (.inr eq)
  | forallEDF h1 h2 _ =>
    obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := eq
    · exact ⟨⟨_, h1.hasType.1⟩, _, h2.hasType.1⟩
    · exact ⟨⟨_, h1.hasType.2⟩, _, h1.defeqDF_l hΓ h2.hasType.2⟩
  | defeqDF _ _ _ ih2 => exact ih2 hΓ eq
  | @beta Γ_c A_c u_c e_body B_c e'_c hA he he' happ heinst ihA ihe ihe' ihapp iheinst =>
    obtain ⟨⟨⟩⟩ | eq := eq
    cases e_body with
    | bvar i =>
      cases i with
      | zero =>
        simp [Term.inst, Term.subst, Subst.one, Subst.cons] at eq
        exact ihe' hΓ (.inl eq)
      | succ n =>
        simp [Term.inst, Term.subst, Subst.one, Subst.cons, Subst.id] at eq
    | forallE A_e B_e =>
      cases eq
      have hΓ' : ⊢ A_c::Γ_c := ⟨hΓ, _, hA⟩
      have ⟨⟨u_A, A1⟩, u_B, A2⟩ := ihe hΓ' (.inl rfl)
      have sort_A : Γ_c ⊢ A_e.inst e'_c : .sort u_A :=
        .inst0 hΓ he' A1
      have W_base : Ctx.SubstEq Γ_c (Subst.one e'_c) (Subst.one e'_c) (A_c :: Γ_c) := by
        refine .cons (σ := Subst.one e'_c) (σ' := Subst.one e'_c) ?_ hA ?_
        · show Ctx.SubstEq Γ_c (Subst.one e'_c).tail (Subst.one e'_c).tail Γ_c
          have htail : (Subst.one e'_c).tail = Subst.id := by funext i; rfl
          rw [htail]; exact Ctx.SubstEq.id hΓ
        · show Γ_c ⊢ e'_c : A_c.subst (Subst.one e'_c).tail
          have htail : (Subst.one e'_c).tail = Subst.id := by funext i; rfl
          rw [htail, subst_id]; exact he'
      have W_lift : Ctx.SubstEq (A_e.inst e'_c :: Γ_c) (Subst.one e'_c).lift
          (Subst.one e'_c).lift (A_e :: A_c :: Γ_c) :=
        W_base.lift A1 sort_A
      have hΓ_lift : ⊢ A_e.inst e'_c :: Γ_c := ⟨hΓ, _, sort_A⟩
      have hΓ_AcAe : ⊢ A_e :: A_c :: Γ_c := ⟨hΓ', _, A1⟩
      have sort_B : A_e.inst e'_c :: Γ_c ⊢ B_e.subst (Subst.one e'_c).lift : .sort u_B :=
        A2.subst hΓ_lift hΓ_AcAe W_lift
      exact ⟨⟨u_A, sort_A⟩, u_B, sort_B⟩
    | _ => cases eq
  | eta _ _ ih _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih hΓ (.inr eq)
  | _ => nomatch eq

theorem IsDefEq.bvar₀ (hΓ : ⊢ Γ) (h : Lookup Γ i A) : Γ ⊢ .bvar i : A :=
  let ⟨_, hA⟩ := hΓ.lookup h; .bvar h hA

theorem IsDefEq.appDF₀ (hΓ : ⊢ Γ)
    (hf : Γ ⊢ f ≡ f' : .forallE A B) (ha : Γ ⊢ a ≡ a' : A) :
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a :=
  let ⟨_, h3⟩ := hf.isType hΓ
  let ⟨⟨_, hA⟩, _, hB⟩ := h3.forallE_inv' hΓ (.inl rfl)
  .appDF hA hB hf ha (.instDF hΓ hA .sort hB ha)

theorem IsDefEq.lamDF₀ (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A ≡ A' : .sort u) (hbody : A::Γ ⊢ body ≡ body' : B) :
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B :=
  let ⟨_, hB⟩ := hbody.isType (Γ := _::_) ⟨hΓ, _, hA.hasType.1⟩
  .lamDF hA hB hbody (hA.defeqDF_l hΓ hbody)

theorem IsDefEq.forallEDF₀ (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A ≡ A' : .sort u) (hbody : A::Γ ⊢ body ≡ body' : .sort v) :
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort v :=
  .forallEDF hA hbody (hA.defeqDF_l hΓ hbody)

theorem IsDefEq.beta₀ (hΓ : ⊢ Γ) (he : A::Γ ⊢ e : B) (he' : Γ ⊢ e' : A) :
    Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e' :=
  have ⟨_, hA⟩ := he'.isType hΓ
  have ⟨_, hB⟩ := he.isType (Γ := _::_) ⟨hΓ, _, hA⟩
  .beta hA he he' (.appDF hA hB (.lamDF hA hB he he) he' (he'.inst0 hΓ hB)) (he'.inst0 hΓ he)

theorem IsDefEq.eta₀ {Γ e A B} (hΓ : ⊢ Γ) (he : Γ ⊢ e : .forallE A B) :
    Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B := by
  let ⟨_, hAB⟩ := he.isType hΓ
  let ⟨⟨_, hA⟩, v, hB⟩ := hAB.forallE_inv' hΓ (.inl rfl)
  have : A::Γ ⊢ .app e.lift (.bvar 0) : (B.lift' (.cons (.skip .refl))).inst (.bvar 0) := by
    refine have hA' := hA.weak' (.skip .refl)
      .appDF (v := v) hA' ?_ (he.weak' (.skip .refl)) (.bvar .zero hA') ?_
    · exact hB.weak' (Ctx.Lift'.cons (Ctx.Lift'.skip (A := A) .refl))
    · rw [lift_cons_skip_inst_bvar0]; exact hB
  rw [lift_cons_skip_inst_bvar0] at this
  exact .eta he (.lamDF hA hB this this)

/-- Context-conversion at arbitrary depth: convert `Δ++A::Γ` to `Δ++A'::Γ` given
`A ≡ A'`. Proved by constructing a `SubstEq (Δ++A'::Γ) Subst.id Subst.id (Δ++A::Γ)`
inductively on `Δ`, then applying `IsDefEq.subst`. -/
theorem IsDefEq.defeqDF_l' (hΓ : ⊢ Γ) (h1 : Γ ⊢ A ≡ A' : .sort u)
    (hΔ : ⊢ Δ++A::Γ) (h2 : Δ++A::Γ ⊢ e1 ≡ e2 : B) :
    Δ++A'::Γ ⊢ e1 ≡ e2 : B := by
  suffices h : ⊢ Δ++A'::Γ ∧ Ctx.SubstEq (Δ++A'::Γ) Subst.id Subst.id (Δ++A::Γ) by
    obtain ⟨hΓ', W⟩ := h
    simpa [subst_id] using h2.subst hΓ' hΔ W
  clear h2
  induction Δ with
  | nil =>
    refine ⟨⟨hΓ, _, h1.hasType.2⟩, ?_⟩
    have htail : (Subst.id : Subst).tail = Subst.id.lift_r (.skip .refl) := by funext i; rfl
    refine .cons (htail ▸ htail ▸ (Ctx.SubstEq.id hΓ).skip) h1.hasType.1 ?_
    show A'::Γ ⊢ .bvar 0 : A.subst Subst.id.tail
    rw [htail, show A.subst (Subst.id.lift_r (.skip .refl)) = A.lift' (.skip .refl) by
      rw [← lift'_subst, subst_id]]
    exact .defeqDF (h1.symm.weak' (.skip .refl))
      (.bvar Lookup.zero (h1.hasType.2.weak' (.skip .refl)))
  | cons X Δ' ih =>
    have ⟨hΔ, _, hX⟩ := hΔ
    obtain ⟨hΓ', W⟩ := ih hΔ
    have hX' := hX.subst hΓ' hΔ W
    refine ⟨⟨hΓ', _, by simpa [subst_id] using hX'⟩, ?_⟩
    have W := W.lift hX hX'
    rwa [show X.subst Subst.id = X from subst_id, id_lift] at W

variable (Γ₀ : List Term) in
inductive IsDefEqCtx : List Term → List Term → Prop
  | zero : ⊢ Γ₀ → IsDefEqCtx Γ₀ Γ₀
  | succ :  IsDefEqCtx Γ₁ Γ₂ → Γ₁ ⊢ A₁ ≡ A₂ : .sort u → IsDefEqCtx (A₁ :: Γ₁) (A₂ :: Γ₂)

theorem IsDefEqCtx.wf₀ : IsDefEqCtx Γ₀ Γ₁ Γ₂ → ⊢ Γ₀
  | .zero h => h
  | .succ inner _ => inner.wf₀

theorem IsDefEqCtx.wf₁ : IsDefEqCtx Γ₀ Γ₁ Γ₂ → ⊢ Γ₁
  | .zero h => h
  | .succ inner AA => ⟨inner.wf₁, _, AA.hasType.1⟩

/-- Wellformedness conversion: `⊢ Δ++A::Γ` and `Γ ⊢ A ≡ A' : sort u` give
`⊢ Δ++A'::Γ`. Inductive on `Δ`; uses `defeqDF_l'` on each level's sort proof. -/
theorem Ctx.WF.defeqSwap (hΓ : ⊢ Γ) (h1 : Γ ⊢ A ≡ A' : .sort u) :
    ∀ {Δ}, ⊢ Δ++A::Γ → ⊢ Δ++A'::Γ
  | [], _ => ⟨hΓ, _, h1.hasType.2⟩
  | _::Δ', h =>
    have ⟨h_inner, u, hX⟩ := h
    have h_inner' : ⊢ Δ'++A'::Γ := defeqSwap hΓ h1 h_inner
    ⟨h_inner', u, h1.defeqDF_l' (Δ := Δ') hΓ h_inner hX⟩

theorem IsDefEq.defeqDFC' {Γ₀ Γ₁ Γ₂ Δ e₁ e₂ A} (h1 : IsDefEqCtx Γ₀ Γ₁ Γ₂)
    (hΓΔ : ⊢ Δ ++ Γ₁) (h2 : Δ ++ Γ₁ ⊢ e₁ ≡ e₂ : A) : Δ ++ Γ₂ ⊢ e₁ ≡ e₂ : A := by
  induction h1 generalizing e₁ e₂ A Δ with
  | zero _ => exact h2
  | @succ Γ₁_inner _ _ A₂ _ inner AA ih =>
    have hΓ_inner : ⊢ Γ₁_inner := inner.wf₁
    have h2' : Δ ++ A₂ :: Γ₁_inner ⊢ e₁ ≡ e₂ : A := AA.defeqDF_l' hΓ_inner hΓΔ h2
    have hΓΔ' : ⊢ Δ ++ A₂ :: Γ₁_inner := Ctx.WF.defeqSwap hΓ_inner AA hΓΔ
    simpa using ih (Δ := Δ ++ [A₂]) (by simpa using hΓΔ') (by simpa using h2')

theorem IsDefEq.defeqDFC (h1 : IsDefEqCtx Γ₀ Γ₁ Γ₂)
    (h2 : Γ₁ ⊢ e₁ ≡ e₂ : A) : Γ₂ ⊢ e₁ ≡ e₂ : A :=
  .defeqDFC' (Δ := []) h1 h1.wf₁ h2

theorem IsDefEqCtx.symm : IsDefEqCtx Γ₀ Γ₁ Γ₂ → IsDefEqCtx Γ₀ Γ₂ Γ₁
  | .zero h => .zero h
  | .succ hΓ hA => .succ hΓ.symm (hA.symm.defeqDFC hΓ)

theorem IsDefEqCtx.wf₂ (H : IsDefEqCtx Γ₀ Γ₁ Γ₂) : ⊢ Γ₂ := H.symm.wf₁

scoped notation:65 Γ " ⊢ " e1 " ⤳ " e2:36 => WHRed Γ e1 e2
inductive WHRed (Γ : List Term) : Term → Term → Prop where
  | app : Γ ⊢ f ⤳ f' → Γ ⊢ .app f a ⤳ .app f' a
  | beta : Γ ⊢ .app (.lam A e) a ⤳ e.inst a

theorem WHRed.weak' (W : Ctx.Lift' ρ Γ Γ') :
    Γ ⊢ e1 ⤳ e2 → Γ' ⊢ e1.lift' ρ ⤳ e2.lift' ρ
  | .app h1 => .app (h1.weak' W)
  | .beta => by rw [lift'_inst_hi]; exact .beta

theorem WHRed.weakU_inv (H : Γ' ⊢ e1.lift' ρ ⤳ e2') :
    ∃ e2, e2' = e2.lift' ρ ∧ Γ ⊢ e1 ⤳ e2 := by
  generalize he : e1.lift' ρ = e1' at H
  induction H generalizing e1 with
  | app h1 ih => let .app .. := e1; cases he; obtain ⟨_, rfl, a1⟩ := ih rfl; exact ⟨_, rfl, .app a1⟩
  | beta =>
    let .app e1 _ := e1; let .lam .. := e1; cases he
    simp [← lift'_inst_hi, lift'_inj]; exact .beta

def WHNF (Γ : List Term) (e : Term) := ∀ e', ¬Γ ⊢ e ⤳ e'

theorem WHNF.lam : WHNF Γ (.lam A e) := nofun
theorem WHNF.sort : WHNF Γ (.sort A) := nofun
theorem WHNF.forallE : WHNF Γ (.forallE A B) := nofun

theorem WHRed.determ (H1 : Γ ⊢ e ⤳ e₁) (H2 : Γ ⊢ e ⤳ e₂) : e₁ = e₂ := by
  induction H1 generalizing e₂ with
  | app h1 ih =>
    cases H2 with
    | app h2 => congr 1; exact ih h2
    | beta => cases h1
  | beta =>
    cases H2 with
    | app h2 => cases h2
    | beta => rfl

def WHRedS (Γ : List Term) : Term → Term → Prop := ReflTransGen (WHRed Γ)
scoped notation:65 Γ " ⊢ " e1 " ⤳* " e2:36 => WHRedS Γ e1 e2

theorem WHRedS.weak' (W : Ctx.Lift' ρ Γ Δ) (H : Γ ⊢ e1 ⤳* e2) :
    Δ ⊢ e1.lift' ρ ⤳* e2.lift' ρ := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.weak' W)

theorem WHRedS.app (H : Γ ⊢ e1 ⤳* e2) : Γ ⊢ e1.app a ⤳* e2.app a := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih h2.app

theorem WHRedS.weakU_inv (H : Δ ⊢ e1.lift' ρ ⤳* e2') :
    ∃ e2, e2' = e2.lift' ρ ∧ Γ ⊢ e1 ⤳* e2 := by
  induction H with
  | rfl => exact ⟨_, rfl, .rfl⟩
  | tail _ h2 ih =>
    obtain ⟨_, rfl, a1⟩ := ih
    obtain ⟨_, rfl, a2⟩ := h2.weakU_inv
    exact ⟨_, rfl, .tail a1 a2⟩

theorem WHRedS.determ_l (H1 : Γ ⊢ e ⤳* e₁) (H2 : Γ ⊢ e ⤳* e₂) (W2 : WHNF Γ e₂) : Γ ⊢ e₁ ⤳* e₂ := by
  induction H1 using ReflTransGen.headIndOn generalizing e₂ with
  | rfl => exact H2
  | head l1 l2 ih =>
    cases H2 using ReflTransGen.headIndOn with
    | rfl => cases W2 _ l1
    | head r1 r2 => cases l1.determ r1; exact ih r2 W2

theorem WHNF.whRedS (W : WHNF Γ e) (H : Γ ⊢ e ⤳* e') : e = e' := by
  cases H using ReflTransGen.headIndOn with
  | rfl => rfl
  | head h1 => cases W _ h1

theorem WHRedS.determ
    (H1 : Γ ⊢ e ⤳* e₁) (W1 : WHNF Γ e₁)
    (H2 : Γ ⊢ e ⤳* e₂) (W2 : WHNF Γ e₂) : e₁ = e₂ := W1.whRedS (H1.determ_l H2 W2)
