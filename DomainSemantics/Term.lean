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

end Term
open Term

def Subst := Nat → Term

def Subst.Depth (σ : Subst) (n n' : Nat) := ∀ i, σ (i + n') = .bvar (i + n)

def Subst.lift (σ : Subst) : Subst
  | 0 => .bvar 0
  | i+1 => (σ i).lift

def Subst.id : Subst := .bvar
def Subst.head (σ : Subst) : Term := σ 0
def Subst.tail (σ : Subst) : Subst := fun n => σ (n+1)

theorem Subst.Depth.id : Subst.id.Depth 0 0 := fun _ => rfl
def Subst.cons (σ : Subst) (e : Term) : Subst
  | 0 => e
  | i+1 => σ i

abbrev Subst.one (e : Term) : Subst := .cons .id e

theorem Subst.Depth.one : (Subst.one e).Depth 0 1 := .id

def Subst.trunc (σ : Subst) (n n' : Nat) : Subst :=
  fun i => if n' ≤ i then .bvar (i - n' + n) else σ i

@[simp] theorem Subst.tail_cons : (cons σ e).tail = σ := rfl

def Subst.lift_r (σ : Subst) (ρ : Lift) : Subst := fun x => (σ x).lift' ρ
def Subst.lift_l (ρ : Lift) (σ : Subst) : Subst := fun x => σ (ρ.liftVar x)

theorem Subst.tail_eq_lift_l {σ : Subst} : σ.tail = σ.lift_l Lift.refl.skip := rfl

theorem Subst.lift_l_lift {σ : Subst} {ρ} : (σ.lift_l ρ).lift = σ.lift.lift_l ρ.cons := by
  funext i; cases i <;> simp! [lift_l]

theorem Subst.lift_r_lift {σ : Subst} {ρ} : (σ.lift_r ρ).lift = σ.lift.lift_r ρ.cons := by
  funext i; cases i <;> simp! [lift_r, ← lift'_comp]

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

def Term.inst (e a : Term) : Term := e.subst (.one a)

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

theorem Subst.lift_r_tail {σ : Subst} {ρ : Lift} :
    (σ.lift_r ρ).tail = σ.tail.lift_r ρ := by
  funext i; rfl

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
    have H_σ : Γ₀ ⊢ (Term.lam A (.app e.lift (.bvar 0))).subst σ ≡ e.subst σ :
        (Term.forallE A B).subst σ := h_lam_eq ▸ .eta he_σ (h_lam_eq ▸ hlam_σ)
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
  have hhead : Γ ⊢ (Subst.one e₀).head : A₀.subst (Subst.one e₀).tail :=
    show Γ ⊢ e₀ : A₀.subst Subst.id from subst_id ▸ h₀
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
  have h2w : A.lift :: A' :: Γ ⊢ e1.lift' (.cons (.skip .refl)) ≡
      e2.lift' (.cons (.skip .refl)) : B.lift' (.cons (.skip .refl)) :=
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

scoped notation:65 Γ " ⊢ " e1 " ⤳ " e2:36 => WHRed Γ e1 e2
inductive WHRed (Γ : List Term) : Term → Term → Prop where
  | app : Γ ⊢ f ⤳ f' → Γ ⊢ .app f a ⤳ .app f' a
  | beta : Γ ⊢ .app (.lam A e) a ⤳ e.inst a

def WHNF (Γ : List Term) (e : Term) := ∀ e', ¬Γ ⊢ e ⤳ e'

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

theorem WHRedS.app (H : Γ ⊢ e1 ⤳* e2) : Γ ⊢ e1.app a ⤳* e2.app a := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih h2.app

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
