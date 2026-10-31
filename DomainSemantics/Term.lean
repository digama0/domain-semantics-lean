import DomainSemantics.Lift

/-! # Terms and substitution

The syntactic core of the project; the judgments over this syntax are in
`DefEq.lean`.

* `Term` is the untyped pre-syntax: de Bruijn variables, sorts indexed by
  a `Bool` (proof-relevant vs proof-irrelevant), application, the binders
  `lam`/`forallE`, `sigma` with `pair`/`fst`/`snd`, `unit`/`star`, `nat`
  with `zero`/`succ`/`natCase`, the fixpoint `Y`, and the proof-relevant
  identity type `id` with `refl`/`tr`.
* `Subst := Nat → Term` is the substitution monoid, with operations
  `id`, `cons`, `one e`, `lift`, `comp`, `tail`, and the action
  `Term.subst : Term → Subst → Term`. β-instantiation is the special
  case `Term.inst e a = e.subst (Subst.one a)`.
* `Lookup` and `Ctx.Lift'` formalise context membership and context
  weakening. -/

namespace DomainSemantics

/-- Raw pre-terms of the dependent λ-calculus the project models. Variables
are de Bruijn indices, sorts are indexed by a `Bool` (`true` ↦ proof-relevant
universe `Type`, `false` ↦ proof-irrelevant universe `Prop`), and binders
(`lam`, `forallE`, `sigma`, `pair`) carry the domain type explicitly.
Σ-types come with the fully type-annotated introduction `pair A B a b` and
the eliminators `fst`/`snd`. The natural numbers `nat` come with constructors
`zero` and `succ` and a dependent eliminator `natCase C M a b` whose motive `C`
and succ-branch `b` are binders (single-variable abstractions, not functions).
Identity types `id r A a b` are universe-polymorphic in the same `Bool` flag `r`
as `unit`/`sort` (`Id r A a b : Sort r`); they come with introduction `refl r a`
and the transport eliminator `tr r C x h`. When `r = false` the identity type
lives in `Prop` and `proofIrrel` collapses every proof, so genuine `refl` values
exist only for `r = true`. Well-typed terms are carved out by `IsDefEq` in `DefEq.lean`. -/
inductive Term where
  | bvar (i : Nat)
  | sort (u : Bool)
  | unit (r : Bool)
  | star (r : Bool)
  | app (f a : Term)
  | lam (A e : Term)
  | forallE (A B : Term)
  | sigma (A B : Term)
  | pair (A B a b : Term)
  | fst (p : Term)
  | snd (p : Term)
  | nat
  | zero
  | succ (n : Term)
  | natCase (C M a b : Term)
  | Y (A b : Term)
  | protected id (r : Bool) (A a b : Term)
  | refl (r : Bool) (a : Term)
  | tr (r : Bool) (A a b C x h : Term)

abbrev Term.type := sort true
abbrev Term.prop := sort false

instance : Inhabited Term := ⟨.prop⟩

namespace Term

/-- Apply a `Lift` to every free variable of a term. Under each binder the
lift is extended with `Lift.cons` so that the bound variable is pinned. -/
@[simp] def lift' : Term → Lift → Term
  | .bvar i, k => .bvar (k.liftVar i)
  | .sort u, _ => .sort u
  | .unit r, _ => .unit r
  | .star r, _ => .star r
  | .app fn arg, k => .app (fn.lift' k) (arg.lift' k)
  | .lam ty body, k => .lam (ty.lift' k) (body.lift' k.cons)
  | .forallE ty body, k => .forallE (ty.lift' k) (body.lift' k.cons)
  | .sigma ty body, k => .sigma (ty.lift' k) (body.lift' k.cons)
  | .pair ty body a b, k =>
    .pair (ty.lift' k) (body.lift' k.cons) (a.lift' k) (b.lift' k)
  | .fst p, k => .fst (p.lift' k)
  | .snd p, k => .snd (p.lift' k)
  | .nat, _ => .nat
  | .zero, _ => .zero
  | .succ n, k => .succ (n.lift' k)
  | .natCase C M a b, k => .natCase (C.lift' k.cons) (M.lift' k) (a.lift' k) (b.lift' k.cons)
  | .Y ty body, k => .Y (ty.lift' k) (body.lift' k.cons)
  | .id r A a b, k => .id r (A.lift' k) (a.lift' k) (b.lift' k)
  | .refl r a, k => .refl r (a.lift' k)
  | .tr r A a b C x h, k =>
    .tr r (A.lift' k) (a.lift' k) (b.lift' k) (C.lift' k.cons) (x.lift' k) (h.lift' k)

/-- Shorthand for the single-skip lift `lift' e (skip refl)`, i.e. the
weakening that bumps every free index by one. -/
abbrev lift e := lift' e (.skip .refl)

theorem lift'_comp {e : Term} : e.lift' (.comp l₁ l₂) = (e.lift' l₁).lift' l₂ := Eq.symm <| by
  induction e generalizing l₁ l₂ <;> simp [Lift.liftVar_comp, *]

theorem lift'_depth_zero {e : Term} (H : l.depth = 0) : e.lift' l = e := by
  induction e generalizing l <;> simp_all [Lift.liftVar_depth_zero]

@[simp] theorem lift'_refl {e : Term} : e.lift' .refl = e := lift'_depth_zero rfl

end Term
open Term

/-- A substitution is a function from de Bruijn indices to terms. -/
def Subst := Nat → Term

/-- `σ.Depth n n'` says `σ` shifts the suffix `[n', ∞)` by a constant offset:
each index `i + n'` maps to the variable `i + n`. This characterises the
"closed below `n'`, identity above" substitutions used by lifts and lifts
restricted by truncation. -/
def Subst.Depth (σ : Subst) (n n' : Nat) := ∀ i, σ (i + n') = .bvar (i + n)

/-- Extend a substitution under a binder: variable `0` stays put, and
indices `i+1` are mapped through `σ` and then weakened. -/
def Subst.lift (σ : Subst) : Subst
  | 0 => .bvar 0
  | i+1 => (σ i).lift

/-- The identity substitution `i ↦ bvar i`. -/
protected def Subst.id : Subst := .bvar
/-- First component of a substitution viewed as a stream. -/
def Subst.head (σ : Subst) : Term := σ 0
/-- Drop the head — `σ.tail i := σ (i+1)`. -/
def Subst.tail (σ : Subst) : Subst := fun n => σ (n+1)

protected theorem Subst.Depth.id : Subst.id.Depth 0 0 := fun _ => rfl
/-- Prepend a term to a substitution. `(σ.cons e) 0 = e` and
`(σ.cons e) (i+1) = σ i`. -/
def Subst.cons (σ : Subst) (e : Term) : Subst
  | 0 => e
  | i+1 => σ i

/-- The substitution that sends `bvar 0` to `e` and leaves the rest as the
identity — used to encode β-reduction (`e.subst (.one a) = e.inst a`). -/
abbrev Subst.one (e : Term) : Subst := .cons .id e

theorem Subst.Depth.one : (Subst.one e).Depth 0 1 := .id

/-- Truncate `σ` above index `n'`: indices `≥ n'` become a shifted identity
landing at `n`, and indices `< n'` use the original `σ`. -/
def Subst.trunc (σ : Subst) (n n' : Nat) : Subst :=
  fun i => if n' ≤ i then .bvar (i - n' + n) else σ i

@[simp] theorem Subst.tail_cons : (cons σ e).tail = σ := rfl

/-- Post-compose a substitution with a lift on the codomain (lift each
output term by `ρ`). -/
def Subst.lift_r (σ : Subst) (ρ : Lift) : Subst := fun x => (σ x).lift' ρ
/-- Pre-compose a substitution with a lift on the domain (re-index the input
through `ρ.liftVar`). -/
def Subst.lift_l (ρ : Lift) (σ : Subst) : Subst := fun x => σ (ρ.liftVar x)

@[simp] theorem Subst.lift_id : Subst.id.lift = .id := by
  funext i; cases i <;> rfl

theorem Subst.tail_eq_lift_l {σ : Subst} : σ.tail = σ.lift_l Lift.refl.skip := rfl

theorem Subst.lift_l_lift {σ : Subst} {ρ} : (σ.lift_l ρ).lift = σ.lift.lift_l ρ.cons := by
  funext i; cases i <;> simp! [lift_l]

theorem Subst.lift_r_lift {σ : Subst} {ρ} : (σ.lift_r ρ).lift = σ.lift.lift_r ρ.cons := by
  funext i; cases i <;> simp! [lift_r, ← lift'_comp]

/-- Apply a substitution to every free variable of a term, extending `σ`
under each binder with `Subst.lift`. -/
def Term.subst : Term → Subst → Term
  | .bvar i, σ => σ i
  | .sort u, _ => .sort u
  | .unit r, _ => .unit r
  | .star r, _ => .star r
  | .app fn arg, σ => .app (fn.subst σ) (arg.subst σ)
  | .lam ty body, σ => .lam (ty.subst σ) (body.subst σ.lift)
  | .forallE ty body, σ => .forallE (ty.subst σ) (body.subst σ.lift)
  | .sigma ty body, σ => .sigma (ty.subst σ) (body.subst σ.lift)
  | .pair ty body a b, σ =>
    .pair (ty.subst σ) (body.subst σ.lift) (a.subst σ) (b.subst σ)
  | .fst p, σ => .fst (p.subst σ)
  | .snd p, σ => .snd (p.subst σ)
  | .nat, _ => .nat
  | .zero, _ => .zero
  | .succ n, σ => .succ (n.subst σ)
  | .natCase C M a b, σ => .natCase (C.subst σ.lift) (M.subst σ) (a.subst σ) (b.subst σ.lift)
  | .Y ty body, σ => .Y (ty.subst σ) (body.subst σ.lift)
  | .id r A a b, σ => .id r (A.subst σ) (a.subst σ) (b.subst σ)
  | .refl r a, σ => .refl r (a.subst σ)
  | .tr r A a b C x h, σ =>
    .tr r (A.subst σ) (a.subst σ) (b.subst σ) (C.subst σ.lift) (x.subst σ) (h.subst σ)

@[simp] theorem id_lift : Subst.id.lift = .id := by funext i; cases i <;> rfl

@[simp] theorem subst_id {e : Term} : e.subst .id = e := by
  induction e <;> simp! [*]; rfl

theorem subst_lift' {e : Term} : (e.lift' ρ).subst σ = subst e (.lift_l ρ σ) := by
  induction e generalizing ρ σ <;> simp! [*, Subst.lift_l_lift]; rfl

theorem lift'_subst {e : Term} : (e.subst σ).lift' ρ = subst e (.lift_r σ ρ) := by
  induction e generalizing ρ σ <;> simp! [*, Subst.lift_r, Subst.lift_r_lift]

/-- Composition of substitutions: `(σ.comp σ') i = (σ i).subst σ'`. Together
with `Subst.id` this makes `Subst` a monoid acting on `Term`. -/
def Subst.comp (σ σ' : Subst) : Subst := fun x => (σ x).subst σ'

theorem Subst.comp_lift {σ σ' : Subst} : (σ.comp σ').lift = σ.lift.comp σ'.lift := by
  funext i; cases i <;> simp! [comp, Term.lift]
  rw [Term.lift, Term.lift, lift'_subst, subst_lift']; rfl

theorem Subst.cons_comp {sig tau : Subst} {e : Term} :
    (sig.cons e).comp tau = (sig.comp tau).cons (e.subst tau) := by
  funext i; cases i <;> rfl

theorem subst_subst {e : Term} : (e.subst σ).subst σ' = subst e (.comp σ σ') := by
  induction e generalizing σ σ' <;> simp! [*, Subst.comp, Subst.comp_lift]

@[simp] theorem Subst.id_comp {σ : Subst} : Subst.id.comp σ = σ := by
  funext i; rfl

@[simp] theorem Subst.comp_id {σ : Subst} : σ.comp .id = σ := by
  funext i; exact subst_id

theorem Subst.comp_assoc {σ τ υ : Subst} : (σ.comp τ).comp υ = σ.comp (τ.comp υ) := by
  funext i; exact subst_subst

/-- Re-indexing the domain commutes with post-composition. -/
theorem Subst.lift_l_comp {σ τ : Subst} {l : Lift} :
    (σ.comp τ).lift_l l = (σ.lift_l l).comp τ := rfl

theorem lift_subst {e : Term} : e.lift.subst σ = e.subst σ.tail := by
  rw [lift, subst_lift', ← Subst.tail_eq_lift_l]

theorem lift_subst_cons {e : Term} : e.lift.subst (σ.cons t) = e.subst σ := by
  rw [lift_subst, Subst.tail_cons]

/-- Instantiate the outermost bound variable of `e` with `a` — i.e. the
β-redex substitution `e[a/0]`. Implemented as `e.subst (.one a)`. -/
def Term.inst (e a : Term) : Term := e.subst (.one a)

theorem Subst.lift_r_comm (σ : Subst) (ρ : Lift) (H : σ.Depth 0 n) :
    σ.lift_r ρ = .lift_l (ρ.consN n) ((σ.lift_r ρ).trunc 0 n) := by
  funext i; simp [lift_l, lift_r, trunc]
  have : (ρ.consN n).liftVar i = if n ≤ i then ρ.liftVar (i-n) + n else i := by
    clear H; induction n generalizing i <;> [skip; cases i] <;> simp! [*]; split <;> rfl
  rw [this]; split <;> simp
  have := H (i - n); rw [Nat.sub_add_cancel ‹_›] at this; simp [this]

theorem lift_r_one (e : Term) (ρ : Lift) :
    (Subst.one e).lift_r ρ = .lift_l ρ.cons (.one (e.lift' ρ)) := by
  refine ((Subst.one e).lift_r_comm ρ .one).trans ?_; congr 1
  funext i; simp [Subst.trunc]
  cases i <;> simp [Subst.one, Subst.cons, Subst.lift_r, Subst.id]

theorem lift_inst (e : Term) : e.lift.inst e' = e := by
  rw [inst, Subst.one, lift, subst_lift', ← Subst.tail_eq_lift_l, Subst.tail_cons, subst_id]

theorem lift'_inst_hi (e1 e2 : Term) (ρ : Lift) :
    lift' (e1.inst e2) ρ = (lift' e1 ρ.cons).inst (lift' e2 ρ) := by
  simp [inst, subst_lift', lift'_subst, lift_r_one]

theorem lift'_succ_branch_swap (C : Term) (ρ : Lift) :
    ((C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0))).lift' ρ.cons =
    ((C.lift' ρ.cons).lift' (.cons (.skip .refl))).inst (.succ (.bvar 0)) := by
  rw [lift'_inst_hi, ← lift'_comp, ← lift'_comp]; congr 1; simp

theorem lift_lift' {A : Term} {l : Lift} : A.lift.lift' l.cons = (A.lift' l).lift := by
  show (A.lift' (.skip .refl)).lift' l.cons = (A.lift' l).lift' (.skip .refl)
  rw [← lift'_comp, ← lift'_comp]; simp

theorem lift_subst_lift {A : Term} {σ : Subst} : A.lift.subst σ.lift = (A.subst σ).lift := by
  have : σ.lift.tail = σ.lift_r (.skip .refl) := by
    funext i; simp [Subst.tail, Subst.lift, Subst.lift_r]
  rw [lift_subst, this, ← lift'_subst]

theorem subst_inst {e : Term} : (e.inst a).subst σ = (e.subst σ.lift).inst (a.subst σ) := by
  rw [inst, inst, subst_subst, subst_subst]; congr 1
  funext i; obtain _|i := i <;> simp [Subst.comp, Subst.lift, subst]
  · simp [Subst.one, Subst.cons]
  · rw [← inst, lift_inst]; rfl

theorem subst_succ_branch_swap (C : Term) (σ : Subst) :
    ((C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0))).subst σ.lift =
    ((C.subst σ.lift).lift' (.cons (.skip .refl))).inst (.succ (.bvar 0)) := by
  rw [subst_inst]; congr 1
  rw [subst_lift', lift'_subst]; congr 1
  funext i; cases i with | zero => rfl | succ n
  show ((σ n).lift' (.skip .refl)).lift' (.skip .refl) =
    ((σ n).lift' (.skip .refl)).lift' (.cons (.skip .refl))
  rw [← lift'_comp, ← lift'_comp]; rfl

theorem inst_lift_cons {e : Term} {σ : Subst} :
    (e.subst σ.lift).inst x = e.subst (σ.cons x) := by
  rw [inst, subst_subst, Subst.one]; congr 1
  funext i; obtain _|i := i <;>
    simp [Subst.comp, Subst.lift, subst, Subst.cons, lift_subst_cons]

/-- Context weakening witness: `Ctx.Lift' l Γ Γ'` says `Γ'` is obtained from
`Γ` by inserting fresh entries (per `skip`) and applying `l` to the kept
ones (per `cons`). This is the source-of-truth for the weakening lemma
`IsDefEq.weak'`. -/
inductive Ctx.Lift' : Lift → List Term → List Term → Prop where
  | refl : Ctx.Lift' .refl Γ Γ
  | skip : Ctx.Lift' l Γ Γ' → Ctx.Lift' (.skip l) Γ (A :: Γ')
  | cons : Ctx.Lift' l Γ Γ' → Ctx.Lift' (.cons l) (A::Γ) (A.lift' l :: Γ')

section
set_option hygiene false

/-- de Bruijn lookup: `Lookup Γ i A` says the `i`th entry of `Γ` is `A`,
already weakened over the binders crossed to reach it. The `.lift` in each
constructor accounts for that crossing. -/
inductive Lookup : List Term → Nat → Term → Prop where
  | zero : Lookup (ty::Γ) 0 ty.lift
  | succ : Lookup Γ n ty → Lookup (A::Γ) (n+1) ty.lift

/-- Weakening for `Lookup`: applying a context weakening `Ctx.Lift' ρ Γ Γ'`
to both the index and the type preserves the lookup. The de Bruijn index
moves through `ρ.liftVar`, and the type is lifted by `ρ` to track the
binders crossed. -/
theorem Lookup.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Lookup Γ i A) :
    Lookup Γ' (ρ.liftVar i) (A.lift' ρ) := by
  induction W generalizing i A with
  | refl => simp; exact H
  | skip W ih => have' := (ih H).succ; rwa [lift, ← lift'_comp] at this
  | cons W ih
  cases H with
  | zero => refine' cast _ Lookup.zero; congr 1; simp [lift, ← lift'_comp]
  | succ H => refine' cast _ (ih H).succ; congr 1; simp [lift, ← lift'_comp]

theorem Lookup.uniq (hA : Lookup Γ i A) (hB : Lookup Γ i B) : A = B :=
  match hA, hB with
  | .zero, .zero => rfl
  | .succ hA, .succ hB => hA.uniq hB ▸ rfl

theorem Lookup.determ (H1 : Lookup Γ i A) (H2 : Lookup Γ i A') : A = A' := by
  induction H1 generalizing A' with obtain _ | r1 := H2
  | zero => rfl
  | succ _ ih => cases ih r1; rfl
