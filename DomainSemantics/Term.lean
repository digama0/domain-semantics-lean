import DomainSemantics.Lift

/-! # Terms and the core typing/defeq judgments

The syntactic core of the project.

* `Term` is the untyped pre-syntax: de Bruijn variables, sorts indexed by
  a `Bool` (proof-relevant vs proof-irrelevant), application, and the two
  binders `lam` and `forallE`.
* `Subst := Nat → Term` is the substitution monoid, with operations
  `id`, `cons`, `one e`, `lift`, `comp`, `tail`, and the action
  `Term.subst : Term → Subst → Term`. β-instantiation is the special
  case `Term.inst e a = e.subst (Subst.one a)`.
* `Lookup`, `Ctx.Lift'` and `Ctx.WF` formalise context membership,
  context weakenings, and well-formedness.
* `IsDefEq₀` (notation `Γ ⊢₀ e₁ ≡ e₂ : A`) is the actual definitional-
  equality judgment we care about — the standard set of congruence,
  β, η and proof-irrelevance rules with ordinary homogeneous
  transitivity, and no sort-proof bookkeeping at the leaves.
* `IsDefEq` (notation `Γ ⊢ e₁ ≡ e₂ : A`) is a formalisation trick
  built around the same syntax. It augments `IsDefEq₀` with
  - a heterogeneous transitivity rule `trans'` whose middle term may
    live at a different sort, and
  - explicit sort-typing premises at every congruence rule (so e.g.
    `appDF` carries `Γ ⊢ A : sort u` and `A::Γ ⊢ B : sort v`).

  These extras make `IsDefEq` *easier* to work with internally —
  inductions get stronger inversion data, and `trans'` lets us defer
  sort uniqueness until after Adequacy proves it. Once `uniq_sort` is
  available, `IsDefEq.iff` shows the two systems are equivalent on
  well-formed contexts, so we can prove the key theorems about the
  original judgment as well.
* `Ctx.SubstEq` is the two-sided substitution judgment used to derive
  the substitution lemma `IsDefEq.subst'`.
* `WHRed` / `WHNF` / `WHRedS` set up weak-head reduction and its
  reflexive-transitive closure, the workhorses of the logical relation. -/

namespace DomainSemantics

/-- Raw pre-terms of the dependent λ-calculus the project models. Variables
are de Bruijn indices, sorts are indexed by a `Bool` (`true` ↦ proof-relevant
universe `Type`, `false` ↦ proof-irrelevant universe `Prop`), and binders
(`lam`, `forallE`, `sigma`, `pair`) carry the domain type explicitly.
Σ-types come with the fully type-annotated introduction `pair A B a b` and
the eliminators `fst`/`snd`. The natural numbers `nat` come with constructors
`zero` and `succ` and a dependent eliminator `natCase C M a b` whose motive `C`
and succ-branch `b` are binders (single-variable abstractions, not functions).
Identity types `id A a b` come with introduction `refl a` and the transport
eliminator `tr C x h`. Well-typed terms are carved out by `IsDefEq` below. -/
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
  | id (A a b : Term)
  | refl (a : Term)
  | tr (A a b C x h : Term)

abbrev Term.type := Term.sort true
abbrev Term.prop := Term.sort false

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
  | .id A a b, k => .id (A.lift' k) (a.lift' k) (b.lift' k)
  | .refl a, k => .refl (a.lift' k)
  | .tr A a b C x h, k =>
    .tr (A.lift' k) (a.lift' k) (b.lift' k) (C.lift' k.cons) (x.lift' k) (h.lift' k)

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
def Subst.id : Subst := .bvar
/-- First component of a substitution viewed as a stream. -/
def Subst.head (σ : Subst) : Term := σ 0
/-- Drop the head — `σ.tail i := σ (i+1)`. -/
def Subst.tail (σ : Subst) : Subst := fun n => σ (n+1)

theorem Subst.Depth.id : Subst.id.Depth 0 0 := fun _ => rfl
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
  | .id A a b, σ => .id (A.subst σ) (a.subst σ) (b.subst σ)
  | .refl a, σ => .refl (a.subst σ)
  | .tr A a b C x h, σ =>
    .tr (A.subst σ) (a.subst σ) (b.subst σ) (C.subst σ.lift) (x.subst σ) (h.subst σ)

@[simp] theorem id_lift : Subst.id.lift = Subst.id := by funext i; cases i <;> rfl

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

theorem subst_subst {e : Term} : (e.subst σ).subst σ' = subst e (.comp σ σ') := by
  induction e generalizing σ σ' <;> simp! [*, Subst.comp, Subst.comp_lift]

theorem lift_subst {e : Term} : e.lift.subst σ = e.subst σ.tail := by
  rw [lift, subst_lift', ← Subst.tail_eq_lift_l]

theorem lift_subst_cons {e : Term} : e.lift.subst (σ.cons t) = e.subst σ := by
  rw [lift_subst, Subst.tail_cons]

/-- Instantiate the outermost bound variable of `e` with `a` — i.e. the
β-redex substitution `e[a/0]`. Implemented as `e.subst (.one a)`. -/
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

theorem lift'_succ_branch_swap (C : Term) (ρ : Lift) :
    ((C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0))).lift' ρ.cons =
    ((C.lift' ρ.cons).lift' (.cons (.skip .refl))).inst (.succ (.bvar 0)) := by
  rw [lift'_inst_hi, ← lift'_comp, ← lift'_comp]; congr 1; simp

theorem lift_lift' {A : Term} {l : Lift} : A.lift.lift' l.cons = (A.lift' l).lift := by
  show (A.lift' (.skip .refl)).lift' l.cons = (A.lift' l).lift' (.skip .refl)
  rw [← lift'_comp, ← lift'_comp]; simp

theorem lift_subst_lift {A : Term} {σ : Subst} : A.lift.subst σ.lift = (A.subst σ).lift := by
  rw [lift_subst, show σ.lift.tail = σ.lift_r (.skip .refl) from by
        funext i; simp [Subst.tail, Subst.lift, Subst.lift_r], ← lift'_subst]

theorem subst_inst {e : Term} : (e.inst a).subst σ = (e.subst σ.lift).inst (a.subst σ) := by
  rw [Term.inst, Term.inst, subst_subst, subst_subst]; congr 1
  funext i; obtain _|i := i <;> simp [Subst.comp, Subst.lift, Term.subst]
  · simp [Subst.one, Subst.cons]
  · rw [← Term.inst, lift_inst]; rfl

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
  rw [Term.inst, subst_subst, Subst.one]; congr 1
  funext i; obtain _|i := i <;>
    simp [Subst.comp, Subst.lift, Term.subst, Subst.cons, lift_subst_cons]

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

/-! ## `IsDefEq₀`: the standard definitional-equality judgment

`IsDefEq₀` is the "real" defeq relation — the one we'd write down by
default for a dependently-typed λ-calculus, with the usual congruence
rules, β, η, proof-irrelevance and *homogeneous* transitivity. The
sister relation `IsDefEq` (below) is a formalisation trick that adds
heterogeneous transitivity (`trans'`) and beefier sort-proof premises
to make internal proofs go through; `IsDefEq.iff` (in `UniqueTyping.lean`)
shows it is equivalent to `IsDefEq₀` on well-formed contexts. -/

section
set_option hygiene false
local notation:65 Γ " ⊢₀ " e " : " A:36 => IsDefEq₀ Γ e e A
local notation:65 Γ " ⊢₀ " e1 " ≡ " e2 " : " A:36 => IsDefEq₀ Γ e1 e2 A

/--
The standard definitional-equality judgment on `Term`. Has the usual
congruence, β, η and proof-irrelevance rules and ordinary homogeneous
transitivity. The sister relation `IsDefEq` adds heterogeneous
transitivity `trans'` plus explicit sort-typing premises at every
congruence site as an internal scaffolding; `IsDefEq.iff` discharges
the equivalence after `uniq_sort`.
-/
inductive IsDefEq₀ : List Term → Term → Term → Term → Prop where
  | bvar : Lookup Γ i A → Γ ⊢₀ .bvar i : A
  | symm : Γ ⊢₀ e ≡ e' : A → Γ ⊢₀ e' ≡ e : A
  | trans : Γ ⊢₀ e₁ ≡ e₂ : A → Γ ⊢₀ e₂ ≡ e₃ : A → Γ ⊢₀ e₁ ≡ e₃ : A
  | sort : Γ ⊢₀ .sort l : .type
  | unit : Γ ⊢₀ .unit r : .sort r
  | star : Γ ⊢₀ .star r : .unit r
  | appDF : Γ ⊢₀ f ≡ f' : .forallE A B → Γ ⊢₀ a ≡ a' : A →
    Γ ⊢₀ .app f a ≡ .app f' a' : B.inst a
  | lamDF : Γ ⊢₀ A ≡ A' : .sort u → A::Γ ⊢₀ body ≡ body' : B →
    Γ ⊢₀ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF : Γ ⊢₀ A ≡ A' : .sort u → A::Γ ⊢₀ body ≡ body' : .sort v →
    Γ ⊢₀ .forallE A body ≡ .forallE A' body' : .sort v
  | sigmaDF : Γ ⊢₀ A ≡ A' : .sort u → A::Γ ⊢₀ B ≡ B' : .sort v →
    Γ ⊢₀ .sigma A B ≡ .sigma A' B' : .type
  | pairDF : Γ ⊢₀ A ≡ A' : .sort u → A::Γ ⊢₀ B ≡ B' : .sort v →
    Γ ⊢₀ a ≡ a' : A → Γ ⊢₀ b ≡ b' : B.inst a →
    Γ ⊢₀ .pair A B a b ≡ .pair A' B' a' b' : .sigma A B
  | fstDF : Γ ⊢₀ p ≡ p' : .sigma A B → Γ ⊢₀ .fst p ≡ .fst p' : A
  | sndDF : Γ ⊢₀ p ≡ p' : .sigma A B → Γ ⊢₀ .snd p ≡ .snd p' : B.inst (.fst p)
  | defeqDF : Γ ⊢₀ A ≡ B : .sort u → Γ ⊢₀ e1 ≡ e2 : A → Γ ⊢₀ e1 ≡ e2 : B
  | beta : A::Γ ⊢₀ e : B → Γ ⊢₀ e' : A →
    Γ ⊢₀ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta : Γ ⊢₀ e : .forallE A B →
    Γ ⊢₀ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | unit_eta : Γ ⊢₀ e : .unit r → Γ ⊢₀ .star r ≡ e : .unit r
  | pair_fst : A::Γ ⊢₀ B : .sort v →
    Γ ⊢₀ a : A → Γ ⊢₀ b : B.inst a →
    Γ ⊢₀ .fst (.pair A B a b) ≡ a : A
  | pair_snd : A::Γ ⊢₀ B : .sort v →
    Γ ⊢₀ a : A → Γ ⊢₀ b : B.inst a →
    Γ ⊢₀ .snd (.pair A B a b) ≡ b : B.inst a
  | fst_snd : Γ ⊢₀ p : .sigma A B →
    Γ ⊢₀ .pair A B (.fst p) (.snd p) ≡ p : .sigma A B
  | nat : Γ ⊢₀ .nat : .type
  | zero : Γ ⊢₀ .zero : .nat
  | succDF : Γ ⊢₀ n ≡ n' : .nat → Γ ⊢₀ .succ n ≡ .succ n' : .nat
  | natCaseDF :
    .nat::Γ ⊢₀ C ≡ C' : .sort v →
    Γ ⊢₀ M ≡ M' : .nat →
    Γ ⊢₀ a ≡ a' : C.inst .zero →
    .nat::Γ ⊢₀ b ≡ b' : (C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0)) →
    Γ ⊢₀ .natCase C M a b ≡ .natCase C' M' a' b' : C.inst M
  | natCase_zero :
    .nat::Γ ⊢₀ C : .sort v →
    Γ ⊢₀ a : C.inst .zero →
    .nat::Γ ⊢₀ b : (C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0)) →
    Γ ⊢₀ .natCase C .zero a b ≡ a : C.inst .zero
  | natCase_succ :
    .nat::Γ ⊢₀ C : .sort v →
    Γ ⊢₀ n : .nat →
    Γ ⊢₀ a : C.inst .zero →
    .nat::Γ ⊢₀ b : (C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0)) →
    Γ ⊢₀ .natCase C (.succ n) a b ≡ b.inst n : C.inst (.succ n)
  | YDF : Γ ⊢₀ A ≡ A' : .sort u → A::Γ ⊢₀ b ≡ b' : A.lift →
    Γ ⊢₀ .Y A b ≡ .Y A' b' : A
  | Y_unfold : Γ ⊢₀ A : .sort u → A::Γ ⊢₀ b : A.lift →
    Γ ⊢₀ .Y A b ≡ b.inst (.Y A b) : A
  | idDF : Γ ⊢₀ A ≡ A' : .sort u →
    Γ ⊢₀ a ≡ a' : A → Γ ⊢₀ b ≡ b' : A →
    Γ ⊢₀ .id A a b ≡ .id A' a' b' : .type
  | reflDF : Γ ⊢₀ a ≡ a' : A → Γ ⊢₀ .refl a ≡ .refl a' : .id A a a
  | trDF : Γ ⊢₀ A ≡ A' : .sort u →
    Γ ⊢₀ a ≡ a' : A → Γ ⊢₀ b ≡ b' : A →
    A::Γ ⊢₀ C ≡ C' : .sort v → A'::Γ ⊢₀ C ≡ C' : .sort v →
    Γ ⊢₀ x ≡ x' : C.inst a → Γ ⊢₀ h ≡ h' : .id A a b →
    Γ ⊢₀ .tr A a b C x h ≡ .tr A' a' b' C' x' h' : C.inst b
  | tr_refl : Γ ⊢₀ a : A → A::Γ ⊢₀ C : .sort v → Γ ⊢₀ x : C.inst a →
    Γ ⊢₀ .tr A a a C x (.refl a) ≡ x : C.inst a
  | proofIrrel : Γ ⊢₀ p : .prop → Γ ⊢₀ h : p → Γ ⊢₀ h' : p → Γ ⊢₀ h ≡ h' : p

end

scoped notation:65 Γ " ⊢₀ " e " : " A:36 => IsDefEq₀ Γ e e A
scoped notation:65 Γ " ⊢₀ " e1 " ≡ " e2 " : " A:36 => IsDefEq₀ Γ e1 e2 A

section
local notation:65 (priority := high) Γ " ⊢ " e1 " : " A:36 => IsDefEq Γ e1 e1 A
local notation:65 (priority := high) Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEq Γ e1 e2 A

/-- An instrumented variant of `IsDefEq₀` used as internal scaffolding.

Two features distinguish it from `IsDefEq₀`:
* every congruence constructor (`bvar`, `appDF`, `lamDF`, `forallEDF`,
  `beta`, `eta`) carries explicit sort-typing premises for its
  subterms, so structural inversion gives back the sort proofs for
  free; and
* a heterogeneous transitivity `trans'` allows the middle term to live
  at a different sort, making it admissible to chain `A ≡ B : sort u`
  with `B ≡ C : sort v` before we have proved sort uniqueness.

Both features are technically removable: `IsDefEq.iff` in
`UniqueTyping.lean` exhibits an equivalence with `IsDefEq₀` on
well-formed contexts, and the strengthened premises are recoverable
via `IsDefEq.hasType` / `IsDefEq.isType`. We keep `IsDefEq` as the
working judgment because it streamlines the soundness and adequacy
proofs that have to lift the relation pointwise. -/
inductive IsDefEq : List Term → Term → Term → Term → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ A : .sort u → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  /-- Heterogeneous transitivity: middle term may be at a different sort. -/
  | trans' : Γ ⊢ A ≡ B : .sort u → Γ ⊢ B ≡ C : .sort v → Γ ⊢ A ≡ C : .sort u
  | sort : Γ ⊢ .sort l : .type
  | unit : Γ ⊢ .unit r : .sort r
  | star : Γ ⊢ .star r : .unit r
  | appDF : Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v →
    Γ ⊢ f ≡ f' : .forallE A B → Γ ⊢ a ≡ a' : A →
    Γ ⊢ B.inst a ≡ B.inst a' : .sort v →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | lamDF : Γ ⊢ A ≡ A' : .sort u → A::Γ ⊢ B : .sort v →
    A::Γ ⊢ body ≡ body' : B → A'::Γ ⊢ body ≡ body' : B →
    Γ ⊢ .forallE A B : .sort v →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF : Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : .sort v → A'::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort v
  | sigmaDF : Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ B ≡ B' : .sort v → A'::Γ ⊢ B ≡ B' : .sort v →
    Γ ⊢ .sigma A B ≡ .sigma A' B' : .type
  | pairDF : Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ B ≡ B' : .sort v → A'::Γ ⊢ B ≡ B' : .sort v →
    Γ ⊢ a ≡ a' : A → Γ ⊢ b ≡ b' : B.inst a →
    Γ ⊢ B.inst a ≡ B'.inst a' : .sort v →
    Γ ⊢ .sigma A B : .type →
    Γ ⊢ .pair A B a b ≡ .pair A' B' a' b' : .sigma A B
  | fstDF : Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v →
    Γ ⊢ p ≡ p' : .sigma A B →
    Γ ⊢ .fst p ≡ .fst p' : A
  | sndDF : Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v →
    Γ ⊢ p ≡ p' : .sigma A B →
    Γ ⊢ B.inst (.fst p) ≡ B.inst (.fst p') : .sort v →
    Γ ⊢ .snd p ≡ .snd p' : B.inst (.fst p)
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B
  | beta : Γ ⊢ A : .sort u → A::Γ ⊢ e : B → Γ ⊢ e' : A →
    Γ ⊢ .app (.lam A e) e' : B.inst e' → Γ ⊢ e.inst e' : B.inst e' →
    Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta : Γ ⊢ e : .forallE A B → Γ ⊢ .lam A (.app e.lift (.bvar 0)) : .forallE A B →
    Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | unit_eta : Γ ⊢ e : .unit r → Γ ⊢ .star r ≡ e : .unit r
  | pair_fst : Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v →
    Γ ⊢ a : A → Γ ⊢ b : B.inst a →
    Γ ⊢ .fst (.pair A B a b) : A →
    Γ ⊢ .fst (.pair A B a b) ≡ a : A
  | pair_snd : Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v →
    Γ ⊢ a : A → Γ ⊢ b : B.inst a →
    Γ ⊢ .snd (.pair A B a b) : B.inst a →
    Γ ⊢ .snd (.pair A B a b) ≡ b : B.inst a
  | fst_snd : Γ ⊢ p : .sigma A B →
    Γ ⊢ .pair A B (.fst p) (.snd p) : .sigma A B →
    Γ ⊢ .pair A B (.fst p) (.snd p) ≡ p : .sigma A B
  | nat : Γ ⊢ .nat : .type
  | zero : Γ ⊢ .zero : .nat
  | succDF : Γ ⊢ n ≡ n' : .nat → Γ ⊢ .succ n ≡ .succ n' : .nat
  | natCaseDF :
    .nat::Γ ⊢ C ≡ C' : .sort v →
    Γ ⊢ M ≡ M' : .nat →
    Γ ⊢ a ≡ a' : C.inst .zero →
    .nat::Γ ⊢ b ≡ b' : (C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0)) →
    Γ ⊢ C.inst M ≡ C'.inst M' : .sort v →
    Γ ⊢ .natCase C M a b ≡ .natCase C' M' a' b' : C.inst M
  | natCase_zero :
    .nat::Γ ⊢ C : .sort v →
    Γ ⊢ a : C.inst .zero →
    .nat::Γ ⊢ b : (C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0)) →
    Γ ⊢ .natCase C .zero a b : C.inst .zero →
    Γ ⊢ .natCase C .zero a b ≡ a : C.inst .zero
  | natCase_succ :
    .nat::Γ ⊢ C : .sort v →
    Γ ⊢ n : .nat →
    Γ ⊢ a : C.inst .zero →
    .nat::Γ ⊢ b : (C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0)) →
    Γ ⊢ .natCase C (.succ n) a b : C.inst (.succ n) →
    Γ ⊢ b.inst n : C.inst (.succ n) →
    Γ ⊢ .natCase C (.succ n) a b ≡ b.inst n : C.inst (.succ n)
  | YDF : Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ b ≡ b' : A.lift → A'::Γ ⊢ b ≡ b' : A'.lift →
    Γ ⊢ .Y A b ≡ .Y A' b' : A
  | Y_unfold : Γ ⊢ A : .sort u → A::Γ ⊢ b : A.lift →
    Γ ⊢ .Y A b : A → Γ ⊢ b.inst (.Y A b) : A →
    Γ ⊢ .Y A b ≡ b.inst (.Y A b) : A
  | idDF : Γ ⊢ A ≡ A' : .sort u →
    Γ ⊢ a ≡ a' : A → Γ ⊢ b ≡ b' : A →
    Γ ⊢ .id A a b ≡ .id A' a' b' : .type
  | reflDF : Γ ⊢ A : .sort u → Γ ⊢ a ≡ a' : A →
    Γ ⊢ .id A a a : .type →
    Γ ⊢ .refl a ≡ .refl a' : .id A a a
  | trDF : Γ ⊢ A ≡ A' : .sort u →
    Γ ⊢ a ≡ a' : A → Γ ⊢ b ≡ b' : A →
    A::Γ ⊢ C ≡ C' : .sort v → A'::Γ ⊢ C ≡ C' : .sort v →
    Γ ⊢ x ≡ x' : C.inst a → Γ ⊢ h ≡ h' : .id A a b →
    Γ ⊢ C.inst b ≡ C'.inst b' : .sort v →
    Γ ⊢ .id A a b : .type →
    Γ ⊢ .tr A a b C x h ≡ .tr A' a' b' C' x' h' : C.inst b
  | tr_refl : Γ ⊢ A : .sort u → Γ ⊢ a : A →
    A::Γ ⊢ C : .sort v → Γ ⊢ x : C.inst a →
    Γ ⊢ .tr A a a C x (.refl a) : C.inst a →
    Γ ⊢ .tr A a a C x (.refl a) ≡ x : C.inst a
  | proofIrrel : Γ ⊢ p : .prop → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ h' : p
end
scoped notation:65 Γ " ⊢ " e1 " : " A:36 => IsDefEq Γ e1 e1 A
scoped notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEq Γ e1 e2 A

/-- Weakening for `IsDefEq`: every definitional equality lifts along a
context weakening. Proved by induction on the derivation, with each
constructor preserving its sort proofs under the lift. -/
theorem IsDefEq.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ' ⊢ e1.lift' ρ ≡ e2.lift' ρ : A.lift' ρ := by
  induction H generalizing ρ Γ' with
  | bvar h1 _ ih => refine .bvar (h1.weak' W) (ih W)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | trans' _ _ ih1 ih2 => exact .trans' (ih1 W) (ih2 W)
  | sort => exact .sort
  | unit => exact .unit
  | star => exact .star
  | appDF _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact lift'_inst_hi .. ▸ .appDF (ih1 W) (ih2 W.cons) (ih3 W) (ih4 W)
      (lift'_inst_hi .. ▸ lift'_inst_hi .. ▸ ih5 W)
  | lamDF _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact .lamDF (ih1 W) (ih2 W.cons) (ih3 W.cons) (ih4 W.cons) (ih5 W)
  | forallEDF _ _ _ ih1 ih2 ih3 => exact .forallEDF (ih1 W) (ih2 W.cons) (ih3 W.cons)
  | sigmaDF _ _ _ ih1 ih2 ih3 => exact .sigmaDF (ih1 W) (ih2 W.cons) (ih3 W.cons)
  | @pairDF _ A A' u B B' v a a' b b' _ _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 ih7 =>
    refine .pairDF (ih1 W) (ih2 W.cons) (ih3 W.cons) (ih4 W) ?_ ?_ (ih7 W)
    · exact lift'_inst_hi B a ρ ▸ ih5 W
    · exact lift'_inst_hi B a ρ ▸ lift'_inst_hi B' a' ρ ▸ ih6 W
  | fstDF _ _ _ ih1 ih2 ih3 => exact .fstDF (ih1 W) (ih2 W.cons) (ih3 W)
  | @sndDF _ A u B v p p' _ _ _ _ ih1 ih2 ih3 ih4 =>
    refine lift'_inst_hi B (.fst p) ρ ▸ .sndDF (ih1 W) (ih2 W.cons) (ih3 W) ?_
    exact lift'_inst_hi B (.fst p) ρ ▸ lift'_inst_hi B (.fst p') ρ ▸ ih4 W
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  | beta _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    rw [lift'_inst_hi, lift'_inst_hi]
    refine .beta (ih1 W) (ih2 W.cons) (ih3 W) ?_ ?_
    · rw [← lift'_inst_hi]; exact ih4 W
    · rw [← lift'_inst_hi, ← lift'_inst_hi]; exact ih5 W
  | eta _ _ ih1 ih2 =>
    refine cast ?_ (IsDefEq.eta (ih1 W) (cast ?_ (ih2 W)))
    all_goals simp [lift', ← lift'_comp]
  | @pair_fst _ A u B v a b _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    refine .pair_fst (ih1 W) (ih2 W.cons) (ih3 W) ?_ (ih5 W)
    exact lift'_inst_hi B a ρ ▸ ih4 W
  | @pair_snd _ A u B v a b _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    refine lift'_inst_hi B a ρ ▸ .pair_snd (ih1 W) (ih2 W.cons) (ih3 W) ?_ ?_
    · exact lift'_inst_hi B a ρ ▸ ih4 W
    · exact lift'_inst_hi B a ρ ▸ ih5 W
  | fst_snd _ _ ih1 ih2 => exact .fst_snd (ih1 W) (ih2 W)
  | nat => exact .nat
  | zero => exact .zero
  | succDF _ ih1 => exact .succDF (ih1 W)
  | @natCaseDF _ C C' v M M' a a' b b' _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    refine lift'_inst_hi C M ρ ▸ .natCaseDF (ih1 W.cons) (ih2 W) ?_ ?_ ?_
    · exact lift'_inst_hi C .zero ρ ▸ ih3 W
    · exact lift'_succ_branch_swap C ρ ▸ ih4 W.cons
    · exact lift'_inst_hi C M ρ ▸ lift'_inst_hi C' M' ρ ▸ ih5 W
  | @natCase_zero _ C v a b _ _ _ _ ih1 ih2 ih3 ih4 =>
    refine lift'_inst_hi C .zero ρ ▸ .natCase_zero (ih1 W.cons) ?_ ?_ ?_
    · exact lift'_inst_hi C .zero ρ ▸ ih2 W
    · exact lift'_succ_branch_swap C ρ ▸ ih3 W.cons
    · exact lift'_inst_hi C .zero ρ ▸ ih4 W
  | @natCase_succ _ C v n a b _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    refine lift'_inst_hi b n ρ ▸ lift'_inst_hi C (.succ n) ρ ▸
      .natCase_succ (ih1 W.cons) (ih2 W) ?_ ?_ ?_ ?_
    · exact lift'_inst_hi C .zero ρ ▸ ih3 W
    · exact lift'_succ_branch_swap C ρ ▸ ih4 W.cons
    · exact lift'_inst_hi C (.succ n) ρ ▸ ih5 W
    · exact lift'_inst_hi C (.succ n) ρ ▸ lift'_inst_hi b n ρ ▸ ih6 W
  | unit_eta _ ih => exact .unit_eta (ih W)
  | YDF _ _ _ ih1 ih2 ih3 =>
    exact .YDF (ih1 W) (lift_lift' ▸ ih2 W.cons) (lift_lift' ▸ ih3 W.cons)
  | @Y_unfold _ A _ b _ _ _ _ ih1 ih2 ih3 ih4 =>
    rw [lift'_inst_hi]
    exact .Y_unfold (ih1 W) (lift_lift' ▸ ih2 W.cons) (ih3 W) (lift'_inst_hi b (.Y A b) ρ ▸ ih4 W)
  | idDF _ _ _ ih1 ih2 ih3 => exact .idDF (ih1 W) (ih2 W) (ih3 W)
  | @reflDF _ A u a a' _ _ _ ih1 ih2 ih3 => exact .reflDF (ih1 W) (ih2 W) (ih3 W)
  | @trDF _ A A' u a a' b b' C C' v x x' h h' _ _ _ _ _ _ _ _ _
      ih1 ih2 ih3 ih4 ih4' ih5 ih6 ih7 ih8 =>
    refine lift'_inst_hi C b ρ ▸ .trDF (ih1 W) (ih2 W) (ih3 W) (ih4 W.cons) (ih4' W.cons) ?_
      (ih6 W) ?_ (ih8 W)
    · exact lift'_inst_hi C a ρ ▸ ih5 W
    · exact lift'_inst_hi C b ρ ▸ lift'_inst_hi C' b' ρ ▸ ih7 W
  | @tr_refl _ A u a C v x _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    refine lift'_inst_hi C a ρ ▸ .tr_refl (ih1 W) (ih2 W) (ih3 W.cons) ?_ ?_
    · exact lift'_inst_hi C a ρ ▸ ih4 W
    · exact lift'_inst_hi C a ρ ▸ ih5 W
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)

theorem IsDefEq.hasType (H : Γ ⊢ e1 ≡ e2 : A) : Γ ⊢ e1 : A ∧ Γ ⊢ e2 : A :=
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
  | unit => exact ⟨_, .sort⟩
  | star => exact ⟨_, .unit⟩
  | appDF _ _ _ _ h5 _ _ _ _ _ => exact ⟨_, h5.hasType.1⟩
  | lamDF h1 h2 _ _ => exact ⟨_, .forallEDF h1.hasType.1 h2 h2⟩
  | forallEDF => exact ⟨_, .sort⟩
  | sigmaDF _ _ _ _ _ _ => exact ⟨_, .sort⟩
  | pairDF h1 h2 _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨_, .sigmaDF h1.hasType.1 h2.hasType.1 h2.hasType.1⟩
  | fstDF h1 _ _ _ _ _ => exact ⟨_, h1⟩
  | sndDF _ _ _ h4 _ _ _ _ => exact ⟨_, h4.hasType.1⟩
  | defeqDF h1 _ _ _ => exact ⟨_, h1.hasType.2⟩
  | beta _ _ _ _ _ _ _ _ ih _ => exact ih hΓ
  | eta _ _ ih _ => exact ih hΓ
  | unit_eta _ _ => exact ⟨_, .unit⟩
  | pair_fst h1 _ _ _ _ _ _ _ _ _ => exact ⟨_, h1⟩
  | pair_snd _ _ _ _ _ _ _ _ _ ih5 => exact ih5 hΓ
  | fst_snd _ _ ih1 _ => exact ih1 hΓ
  | nat => exact ⟨_, .sort⟩
  | zero => exact ⟨_, .nat⟩
  | succDF _ _ => exact ⟨_, .nat⟩
  | natCaseDF _ _ _ _ h5 _ _ _ _ _ => exact ⟨_, h5.hasType.1⟩
  | natCase_zero _ _ _ _ _ ih2 _ _ => exact ih2 hΓ
  | natCase_succ _ _ _ _ _ _ _ _ _ _ _ ih6 => exact ih6 hΓ
  | YDF hA _ _ _ _ _ => exact ⟨_, hA.hasType.1⟩
  | Y_unfold hA _ _ _ _ _ _ _ => exact ⟨_, hA⟩
  | idDF _ _ _ _ _ _ => exact ⟨_, .sort⟩
  | reflDF _ _ h3 _ _ _ => exact ⟨_, h3⟩
  | trDF _ _ _ _ _ _ _ h8 _ _ _ _ _ _ _ _ _ _ => exact ⟨_, h8.hasType.1⟩
  | tr_refl _ _ _ _ _ _ _ _ _ ih5 => exact ih5 hΓ
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

theorem Ctx.SubstEq.wf (W : Ctx.SubstEq Γ₀ σ σ' Γ) : ⊢ Γ := by
  induction W with
  | nil => trivial
  | cons _ hA _ ih => exact ⟨ih, _, hA⟩

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

theorem IsDefEq.substEq' {Γ₀ Γ : List Term} {σ τ : Subst} {e1 e2 A : Term} (hΓ₀ : ⊢ Γ₀)
    (W : Ctx.SubstEq Γ₀ σ τ Γ) (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ₀ ⊢ e1.subst σ ≡ e1.subst τ : A.subst σ ∧
    Γ₀ ⊢ e2.subst σ ≡ e2.subst τ : A.subst σ ∧
    Γ₀ ⊢ e1.subst σ ≡ e2.subst τ : A.subst σ := by
  induction H generalizing Γ₀ σ τ with
  | bvar h _ => exact ⟨W.lookup h, W.lookup h, W.lookup h⟩
  | sort => exact ⟨.sort, .sort, .sort⟩
  | unit => exact ⟨.unit, .unit, .unit⟩
  | star => exact ⟨.star, .star, .star⟩
  | symm _ ih => let ⟨l, r, c⟩ := ih hΓ₀ W; exact ⟨r, l, (r.trans c.symm).trans l⟩
  | trans _ _ ih1 ih2 =>
    let ⟨l1, _, c1⟩ := ih1 hΓ₀ W
    let ⟨l2, r2, c2⟩ := ih2 hΓ₀ W
    exact ⟨l1, r2, c1.trans (l2.symm.trans c2)⟩
  | trans' _ _ ih1 ih2 =>
    let ⟨l1, _, c1⟩ := ih1 hΓ₀ W
    let ⟨l2, _, c2⟩ := ih2 hΓ₀ W
    have cross := c1.trans' (l2.symm.trans c2)
    exact ⟨l1, ((ih1 hΓ₀ W.left).2.2.trans' (ih2 hΓ₀ W.left).2.2).symm.trans cross, cross⟩
  | defeqDF _ _ ih1 ih2 =>
    have := (ih1 hΓ₀ W.left).2.2
    let ⟨l2, r2, c2⟩ := ih2 hΓ₀ W
    exact ⟨.defeqDF this l2, .defeqDF this r2, .defeqDF this c2⟩
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    let ⟨ihp, _, _⟩ := ih1 hΓ₀ W
    let ⟨ihh, _, _⟩ := ih2 hΓ₀ W
    let ⟨ihh', _, _⟩ := ih3 hΓ₀ W
    refine ⟨ihh, ihh', .proofIrrel ihp.hasType.1 ihh.hasType.1 ihh'.hasType.2⟩
  | @eta Γ e A B _ _ ih1 ih2 =>
    have ih1_l := (ih1 hΓ₀ W).1
    have ih2_l := (ih2 hΓ₀ W).1
    have he_σ := (ih1 hΓ₀ W.left).1
    have hlam_σ := (ih2 hΓ₀ W.left).1
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
    have ih5_l := (ih5 hΓ₀ W).1
    have ih4_l := (ih4 hΓ₀ W).1
    have hA_σ := (ih1 hΓ₀ W.left).1
    have W_A_left : Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift σ.lift (A :: Γ) :=
      W.left.lift hA hA_σ
    have hΓ_A_subst : ⊢ A.subst σ :: Γ₀ := ⟨hΓ₀, _, hA_σ⟩
    have he_σ := (ih2 hΓ_A_subst W_A_left).1
    have he'_σ := (ih3 hΓ₀ W.left).1
    have happ_σ := (ih4 hΓ₀ W.left).1
    have heinst_σ := (ih5 hΓ₀ W.left).1
    have H_σ : Γ₀ ⊢ (Term.app (Term.lam A e) e').subst σ ≡ (e.inst e').subst σ :
        (B.inst e').subst σ := by
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
    have hA' := (ih1 hΓ₀ W).1.hasType.1
    have hΓ_A_subst : ⊢ A.subst σ :: Γ₀ := ⟨hΓ₀, _, hA'⟩
    have W_A_diag : Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift σ.lift (A :: Γ) :=
      W.left.lift hA hA'
    have hB' := (ih2 hΓ_A_subst W_A_diag).1
    have ⟨ihf_l, ihf_r, ihf_c⟩ := ih3 hΓ₀ W
    have ⟨iha_l, iha_r, iha_c⟩ := ih4 hΓ₀ W
    have ⟨_, _, iha_cleft⟩ := ih4 hΓ₀ W.left
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
      have := (ih2 hΓ₀ W_cons).1
      rwa [← inst_lift_cons, ← inst_lift_cons] at this
    refine subst_inst ▸ ⟨?_, .defeqDF (ih2_cons iha_cleft.symm) ?_, ?_⟩
    · exact .appDF hA' hB' ihf_l iha_l (ih2_cons iha_l)
    · exact .appDF hA' hB' ihf_r iha_r (ih2_cons iha_r)
    · exact .appDF hA' hB' ihf_c iha_c (ih2_cons iha_c)
  | @lamDF Γ A A' u B v body body' h1 _ _ _ _ ih1 ih2 ih3 ih4 _ =>
    -- h1 : A ≡ A' : sort u; h2 : A::Γ ⊢ B : sort v (diagonal);
    -- h3 : A::Γ ⊢ body ≡ body' : B; h4 : A'::Γ ⊢ body ≡ body' : B.
    let ⟨ihA_l, ihA_r, ihA_c⟩ := ih1 hΓ₀ W
    have hA_in_Γ : Γ ⊢ A : .sort u := h1.hasType.1
    have hA'_in_Γ : Γ ⊢ A' : .sort u := h1.hasType.2
    have hA_subst : Γ₀ ⊢ A.subst σ : .sort u := ihA_l.hasType.1
    have hA_τ_subst : Γ₀ ⊢ A.subst τ : .sort u := ihA_l.hasType.2
    have hA'_subst : Γ₀ ⊢ A'.subst σ : .sort u := ihA_r.hasType.1
    have hA'_τ_subst : Γ₀ ⊢ A'.subst τ : .sort u := ihA_r.hasType.2
    have hΓ_A_subst : ⊢ A.subst σ :: Γ₀ := ⟨hΓ₀, _, hA_subst⟩
    have hΓ_A_τ_subst : ⊢ A.subst τ :: Γ₀ := ⟨hΓ₀, _, hA_τ_subst⟩
    have hΓ_A'_subst : ⊢ A'.subst σ :: Γ₀ := ⟨hΓ₀, _, hA'_subst⟩
    have hΓ_A'_τ_subst : ⊢ A'.subst τ :: Γ₀ := ⟨hΓ₀, _, hA'_τ_subst⟩
    have hAA'_σ : Γ₀ ⊢ A.subst σ ≡ A'.subst σ : .sort u :=
      (ih1 hΓ₀ W.left).2.2
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
    let ⟨ihB_l, _, _⟩ := ih2 hΓ_A_subst W_A
    have hB_at_A'σ := (ih2 hΓ_A'_subst W_left_A'σ).1
    let ⟨ih3body_l, _, ih3body_c⟩ := ih3 hΓ_A_subst W_A
    have ih3body_l_at_Aτ := (ih3 hΓ_A_τ_subst W_A_τ).1
    have ih3body_c_at_A'τ := (ih3 hΓ_A'_τ_subst W_A_to_A'τ).2.2
    let ⟨_, ih4body_r, _⟩ := ih4 hΓ_A'_subst W_A'
    have ih4body_r_at_A'τ := (ih4 hΓ_A'_τ_subst W_A'_τ).2.1
    refine ⟨?_, .defeqDF (hAA'_σ.symm.forallEDF hB_at_A'σ ihB_l.hasType.1) ?_, ?_⟩
    · exact .lamDF ihA_l ihB_l.hasType.1 ih3body_l ih3body_l_at_Aτ
        (.forallEDF ihA_l.hasType.1 ihB_l.hasType.1 ihB_l.hasType.1)
    · exact .lamDF ihA_r hB_at_A'σ ih4body_r ih4body_r_at_A'τ
        (.forallEDF ihA_r.hasType.1 hB_at_A'σ hB_at_A'σ)
    · exact .lamDF ihA_c ihB_l.hasType.1 ih3body_c ih3body_c_at_A'τ
        (.forallEDF ihA_c.hasType.1 ihB_l.hasType.1 ihB_l.hasType.1)
  | @forallEDF Γ A A' u body body' v h1 h2 _ ih1 ih2 ih3 =>
    -- h1 : Γ ⊢ A ≡ A' : sort u; h2 : A::Γ ⊢ body ≡ body' : sort v;
    -- h3 : A'::Γ ⊢ body ≡ body' : sort v (3rd premise).
    let ⟨ihA_l, ihA_r, ihA_c⟩ := ih1 hΓ₀ W
    have hA_in_Γ : Γ ⊢ A : .sort u := h1.hasType.1
    have hA'_in_Γ : Γ ⊢ A' : .sort u := h1.hasType.2
    have hA_subst : Γ₀ ⊢ A.subst σ : .sort u := ihA_l.hasType.1
    have hA'_subst : Γ₀ ⊢ A'.subst σ : .sort u := ihA_r.hasType.1
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
    let ⟨ihB_l, _, ihB_c⟩ := ih2 hΓ_A_subst W_A
    have ihB_l_at_Aτ := (ih2 hΓ_A_τ_subst W_A_τ).1
    have ihB_c_at_A'τ := (ih2 hΓ_A'_τ_subst W_A_to_A'τ).2.2
    let ⟨_, ihB'_r, _⟩ := ih3 hΓ_A'_subst W_A'
    have ihB'_r_at_A'τ := (ih3 hΓ_A'_τ_subst W_A'_τ).2.1
    refine ⟨.forallEDF ihA_l ihB_l ihB_l_at_Aτ,
            .forallEDF ihA_r ihB'_r ihB'_r_at_A'τ,
            .forallEDF ihA_c ihB_c ihB_c_at_A'τ⟩
  | @sigmaDF Γ A A' u B B' v h1 _ _ ih1 ih2 ih3 =>
    let ⟨ihA_l, ihA_r, ihA_c⟩ := ih1 hΓ₀ W
    have hA_in_Γ : Γ ⊢ A : .sort u := h1.hasType.1
    have hA'_in_Γ : Γ ⊢ A' : .sort u := h1.hasType.2
    have hA_subst : Γ₀ ⊢ A.subst σ : .sort u := ihA_l.hasType.1
    have hA'_subst : Γ₀ ⊢ A'.subst σ : .sort u := ihA_r.hasType.1
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
    have W_A_τ : Ctx.SubstEq (A.subst τ :: Γ₀) σ.lift τ.lift (A :: Γ) :=
      W.lift_at hA_in_Γ hA_τ_subst ihA_l
    have W_A'_τ : Ctx.SubstEq (A'.subst τ :: Γ₀) σ.lift τ.lift (A' :: Γ) :=
      W.lift_at hA'_in_Γ hA'_τ_subst ihA_r
    have W_A_to_A'τ : Ctx.SubstEq (A'.subst τ :: Γ₀) σ.lift τ.lift (A :: Γ) :=
      W.lift_at hA_in_Γ hA'_τ_subst ihA_c
    let ⟨ihB_l, _, ihB_c⟩ := ih2 hΓ_A_subst W_A
    have ihB_l_at_Aτ := (ih2 hΓ_A_τ_subst W_A_τ).1
    have ihB_c_at_A'τ := (ih2 hΓ_A'_τ_subst W_A_to_A'τ).2.2
    let ⟨_, ihB'_r, _⟩ := ih3 hΓ_A'_subst W_A'
    have ihB'_r_at_A'τ := (ih3 hΓ_A'_τ_subst W_A'_τ).2.1
    refine ⟨.sigmaDF ihA_l ihB_l ihB_l_at_Aτ,
            .sigmaDF ihA_r ihB'_r ihB'_r_at_A'τ,
            .sigmaDF ihA_c ihB_c ihB_c_at_A'τ⟩
  | @pairDF Γ A A' u B B' v a a' b b' h1 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 _ =>
    -- Setup analogous to lamDF, with additional `a`, `b` and a `B.inst a`-equality.
    let ⟨ihA_l, ihA_r, ihA_c⟩ := ih1 hΓ₀ W
    have hA_in_Γ : Γ ⊢ A : .sort u := h1.hasType.1
    have hA'_in_Γ : Γ ⊢ A' : .sort u := h1.hasType.2
    have hA_subst : Γ₀ ⊢ A.subst σ : .sort u := ihA_l.hasType.1
    have hA_τ_subst : Γ₀ ⊢ A.subst τ : .sort u := ihA_l.hasType.2
    have hA'_subst : Γ₀ ⊢ A'.subst σ : .sort u := ihA_r.hasType.1
    have hA'_τ_subst : Γ₀ ⊢ A'.subst τ : .sort u := ihA_r.hasType.2
    have hΓ_A_subst : ⊢ A.subst σ :: Γ₀ := ⟨hΓ₀, _, hA_subst⟩
    have hΓ_A_τ_subst : ⊢ A.subst τ :: Γ₀ := ⟨hΓ₀, _, hA_τ_subst⟩
    have hΓ_A'_subst : ⊢ A'.subst σ :: Γ₀ := ⟨hΓ₀, _, hA'_subst⟩
    have hΓ_A'_τ_subst : ⊢ A'.subst τ :: Γ₀ := ⟨hΓ₀, _, hA'_τ_subst⟩
    have hAA'_σ : Γ₀ ⊢ A.subst σ ≡ A'.subst σ : .sort u :=
      (ih1 hΓ₀ W.left).2.2
    have W_A : Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift τ.lift (A :: Γ) :=
      W.lift hA_in_Γ hA_subst
    have W_A' : Ctx.SubstEq (A'.subst σ :: Γ₀) σ.lift τ.lift (A' :: Γ) :=
      W.lift hA'_in_Γ hA'_subst
    have W_A_τ : Ctx.SubstEq (A.subst τ :: Γ₀) σ.lift τ.lift (A :: Γ) :=
      W.lift_at hA_in_Γ hA_τ_subst ihA_l
    have W_A'_τ : Ctx.SubstEq (A'.subst τ :: Γ₀) σ.lift τ.lift (A' :: Γ) :=
      W.lift_at hA'_in_Γ hA'_τ_subst ihA_r
    have W_A_to_A'τ : Ctx.SubstEq (A'.subst τ :: Γ₀) σ.lift τ.lift (A :: Γ) :=
      W.lift_at hA_in_Γ hA'_τ_subst ihA_c
    have W_left_A'σ : Ctx.SubstEq (A'.subst σ :: Γ₀) σ.lift σ.lift (A :: Γ) :=
      W.left.lift_at hA_in_Γ hA'_subst hAA'_σ
    -- ih2 (A::Γ ⊢ B ≡ B' : sort v)
    let ⟨ihB_l, _, ihB_c⟩ := ih2 hΓ_A_subst W_A
    have ihB_l_at_Aτ := (ih2 hΓ_A_τ_subst W_A_τ).1
    have ihB_c_at_A'τ := (ih2 hΓ_A'_τ_subst W_A_to_A'τ).2.2
    have hB_at_A'σ := (ih2 hΓ_A'_subst W_left_A'σ).1
    -- ih3 (A'::Γ ⊢ B ≡ B' : sort v)
    let ⟨_, ihB'_r, _⟩ := ih3 hΓ_A'_subst W_A'
    have ihB'_r_at_A'τ := (ih3 hΓ_A'_τ_subst W_A'_τ).2.1
    -- ih4 (a ≡ a' : A)
    have ⟨iha_l, iha_r, iha_c⟩ := ih4 hΓ₀ W
    have ⟨_, _, iha_cleft⟩ := ih4 hΓ₀ W.left
    -- ih5 (b ≡ b' : B.inst a). Three conjuncts at type (B.inst a).subst σ;
    -- convert each via subst_inst.
    have ⟨ihb_l_raw, ihb_r_raw, ihb_c_raw⟩ := ih5 hΓ₀ W
    have ihb_l : Γ₀ ⊢ b.subst σ ≡ b.subst τ : (B.subst σ.lift).inst (a.subst σ) :=
      subst_inst ▸ ihb_l_raw
    have ihb_r : Γ₀ ⊢ b'.subst σ ≡ b'.subst τ : (B.subst σ.lift).inst (a.subst σ) :=
      subst_inst ▸ ihb_r_raw
    have ihb_c : Γ₀ ⊢ b.subst σ ≡ b'.subst τ : (B.subst σ.lift).inst (a.subst σ) :=
      subst_inst ▸ ihb_c_raw
    -- ih6 (B.inst a ≡ B'.inst a' : sort v). Three conjuncts; convert via subst_inst.
    have ⟨ihBinst_l_raw, ihBinst_r_raw, ihBinst_c_raw⟩ := ih6 hΓ₀ W
    have ihBinst_l : Γ₀ ⊢ (B.subst σ.lift).inst (a.subst σ) ≡
        (B.subst τ.lift).inst (a.subst τ) : .sort v := by
      have := ihBinst_l_raw
      rwa [show (B.inst a).subst σ = (B.subst σ.lift).inst (a.subst σ) from subst_inst,
           show (B.inst a).subst τ = (B.subst τ.lift).inst (a.subst τ) from subst_inst] at this
    have ihBinst_r : Γ₀ ⊢ (B'.subst σ.lift).inst (a'.subst σ) ≡
        (B'.subst τ.lift).inst (a'.subst τ) : .sort v := by
      have := ihBinst_r_raw
      rwa [show (B'.inst a').subst σ = (B'.subst σ.lift).inst (a'.subst σ) from subst_inst,
           show (B'.inst a').subst τ = (B'.subst τ.lift).inst (a'.subst τ) from subst_inst] at this
    have ihBinst_c : Γ₀ ⊢ (B.subst σ.lift).inst (a.subst σ) ≡
        (B'.subst τ.lift).inst (a'.subst τ) : .sort v := by
      have := ihBinst_c_raw
      rwa [show (B.inst a).subst σ = (B.subst σ.lift).inst (a.subst σ) from subst_inst,
           show (B'.inst a').subst τ = (B'.subst τ.lift).inst (a'.subst τ) from subst_inst] at this
    have ihBinst_cleft : Γ₀ ⊢ (B.subst σ.lift).inst (a.subst σ) ≡
        (B'.subst σ.lift).inst (a'.subst σ) : .sort v := by
      have := (ih6 hΓ₀ W.left).2.2
      rwa [show (B.inst a).subst σ = (B.subst σ.lift).inst (a.subst σ) from subst_inst,
           show (B'.inst a').subst σ = (B'.subst σ.lift).inst (a'.subst σ) from subst_inst] at this
    have sigma_r_to_l : Γ₀ ⊢ Term.sigma (A'.subst σ) (B'.subst σ.lift) ≡
        Term.sigma (A.subst σ) (B.subst σ.lift) : .type :=
      .sigmaDF (v := v) hAA'_σ.symm
        ((ih3 hΓ_A'_subst W_A'.left).2.2).symm
        ((ih2 hΓ_A_subst W_A.left).2.2).symm
    have iha_r_at_A'σ : Γ₀ ⊢ a'.subst σ ≡ a'.subst τ : A'.subst σ :=
      .defeqDF hAA'_σ iha_r
    have ihb_r_at_A'B' : Γ₀ ⊢ b'.subst σ ≡ b'.subst τ : (B'.subst σ.lift).inst (a'.subst σ) :=
      .defeqDF ihBinst_cleft ihb_r
    have hSigma_l := ihA_l.hasType.1.sigmaDF ihB_l.hasType.1 ihB_l.hasType.1
    have hSigma_r := ihA_r.hasType.1.sigmaDF ihB'_r.hasType.1 ihB'_r.hasType.1
    have res_l : Γ₀ ⊢ (Term.pair A B a b).subst σ ≡ (Term.pair A B a b).subst τ :
        (Term.sigma A B).subst σ :=
      .pairDF ihA_l ihB_l ihB_l_at_Aτ iha_l ihb_l ihBinst_l hSigma_l
    have res_c : Γ₀ ⊢ (Term.pair A B a b).subst σ ≡ (Term.pair A' B' a' b').subst τ :
        (Term.sigma A B).subst σ :=
      .pairDF ihA_c ihB_c ihB_c_at_A'τ iha_c ihb_c ihBinst_c hSigma_l
    have res_r_natural : Γ₀ ⊢ (Term.pair A' B' a' b').subst σ ≡ (Term.pair A' B' a' b').subst τ :
        Term.sigma (A'.subst σ) (B'.subst σ.lift) :=
      .pairDF ihA_r ihB'_r ihB'_r_at_A'τ iha_r_at_A'σ ihb_r_at_A'B' ihBinst_r hSigma_r
    have res_r : Γ₀ ⊢ (Term.pair A' B' a' b').subst σ ≡ (Term.pair A' B' a' b').subst τ :
        (Term.sigma A B).subst σ :=
      .defeqDF sigma_r_to_l res_r_natural
    exact ⟨res_l, res_r, res_c⟩
  | @fstDF Γ A u B v p p' hA _ _ ih1 ih2 ih3 =>
    have hA_σ : Γ₀ ⊢ A.subst σ : .sort u := (ih1 hΓ₀ W.left).1
    have hΓ_A_σ : ⊢ A.subst σ :: Γ₀ := ⟨hΓ₀, _, hA_σ⟩
    have W_A_diag : Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift σ.lift (A :: Γ) :=
      W.left.lift hA hA_σ
    have hB_σ : (A.subst σ) :: Γ₀ ⊢ B.subst σ.lift : .sort v :=
      (ih2 hΓ_A_σ W_A_diag).1
    have ⟨ihp_l, ihp_r, ihp_c⟩ := ih3 hΓ₀ W
    exact ⟨.fstDF hA_σ hB_σ ihp_l, .fstDF hA_σ hB_σ ihp_r, .fstDF hA_σ hB_σ ihp_c⟩
  | @sndDF Γ A u B v p p' hA _ _ _ ih1 ih2 ih3 _ih4 =>
    have hA_σ : Γ₀ ⊢ A.subst σ : .sort u := (ih1 hΓ₀ W.left).1
    have hΓ_A_σ : ⊢ A.subst σ :: Γ₀ := ⟨hΓ₀, _, hA_σ⟩
    have W_A_diag : Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift σ.lift (A :: Γ) :=
      W.left.lift hA hA_σ
    have hB_σ : (A.subst σ) :: Γ₀ ⊢ B.subst σ.lift : .sort v :=
      (ih2 hΓ_A_σ W_A_diag).1
    have ⟨ihp_l, ihp_r, ihp_c⟩ := ih3 hΓ₀ W
    have ⟨_, _, ihp_cleft⟩ := ih3 hΓ₀ W.left
    have ih2_cons : ∀ {x y : Term}, Γ₀ ⊢ x ≡ y : A.subst σ →
        Γ₀ ⊢ (B.subst σ.lift).inst x ≡ (B.subst σ.lift).inst y : .sort v := by
      intro x y hxy
      have htail_x : (σ.cons x).tail = σ := by funext i; rfl
      have htail_y : (σ.cons y).tail = σ := by funext i; rfl
      have W_cons : Ctx.SubstEq Γ₀ (σ.cons x) (σ.cons y) (A :: Γ) := by
        refine .cons (htail_x ▸ htail_y ▸ W.left) hA ?_
        show Γ₀ ⊢ x ≡ y : A.subst (σ.cons x).tail
        rw [htail_x]; exact hxy
      have := (ih2 hΓ₀ W_cons).1
      rwa [← inst_lift_cons, ← inst_lift_cons] at this
    have hfst_l : Γ₀ ⊢ .fst (p.subst σ) ≡ .fst (p.subst τ) : A.subst σ :=
      .fstDF hA_σ hB_σ ihp_l
    have hfst_r : Γ₀ ⊢ .fst (p'.subst σ) ≡ .fst (p'.subst τ) : A.subst σ :=
      .fstDF hA_σ hB_σ ihp_r
    have hfst_c : Γ₀ ⊢ .fst (p.subst σ) ≡ .fst (p'.subst τ) : A.subst σ :=
      .fstDF hA_σ hB_σ ihp_c
    have hfst_pσ_p'σ : Γ₀ ⊢ .fst (p.subst σ) ≡ .fst (p'.subst σ) : A.subst σ :=
      .fstDF hA_σ hB_σ ihp_cleft
    have res_l := IsDefEq.sndDF hA_σ hB_σ ihp_l (ih2_cons hfst_l)
    have res_r := IsDefEq.sndDF hA_σ hB_σ ihp_r (ih2_cons hfst_r)
    have res_c := IsDefEq.sndDF hA_σ hB_σ ihp_c (ih2_cons hfst_c)
    have res_r' := IsDefEq.defeqDF (ih2_cons hfst_pσ_p'σ).symm res_r
    refine ⟨subst_inst ▸ res_l, subst_inst ▸ res_r', subst_inst ▸ res_c⟩
  | @pair_fst Γ A u B v a b hA _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    have ih5_l := (ih5 hΓ₀ W).1
    have ih3_l := (ih3 hΓ₀ W).1
    have hA_σ : Γ₀ ⊢ A.subst σ : .sort u := (ih1 hΓ₀ W.left).1
    have hΓ_A_σ : ⊢ A.subst σ :: Γ₀ := ⟨hΓ₀, _, hA_σ⟩
    have W_A_diag : Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift σ.lift (A :: Γ) :=
      W.left.lift hA hA_σ
    have hB_σ : (A.subst σ) :: Γ₀ ⊢ B.subst σ.lift : .sort v :=
      (ih2 hΓ_A_σ W_A_diag).1
    have ha_σ : Γ₀ ⊢ a.subst σ : A.subst σ := (ih3 hΓ₀ W.left).1
    have hb_σ : Γ₀ ⊢ b.subst σ : (B.subst σ.lift).inst (a.subst σ) := by
      have := (ih4 hΓ₀ W.left).1
      rwa [show (B.inst a).subst σ = (B.subst σ.lift).inst (a.subst σ) from subst_inst] at this
    have hLHS_σ : Γ₀ ⊢ Term.fst (Term.pair (A.subst σ) (B.subst σ.lift) (a.subst σ) (b.subst σ)) :
        A.subst σ :=
      show Γ₀ ⊢ (Term.fst (Term.pair A B a b)).subst σ : A.subst σ from (ih5 hΓ₀ W.left).1
    have H_σ : Γ₀ ⊢ (Term.fst (Term.pair A B a b)).subst σ ≡ a.subst σ : A.subst σ :=
      show Γ₀ ⊢ Term.fst (Term.pair (A.subst σ) (B.subst σ.lift) (a.subst σ) (b.subst σ)) ≡
          a.subst σ : A.subst σ from
      .pair_fst hA_σ hB_σ ha_σ hb_σ hLHS_σ
    exact ⟨ih5_l, ih3_l, H_σ.trans ih3_l⟩
  | @pair_snd Γ A u B v a b hA _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    have ih5_l := (ih5 hΓ₀ W).1
    have ih4_l := (ih4 hΓ₀ W).1
    have hA_σ : Γ₀ ⊢ A.subst σ : .sort u := (ih1 hΓ₀ W.left).1
    have hΓ_A_σ : ⊢ A.subst σ :: Γ₀ := ⟨hΓ₀, _, hA_σ⟩
    have W_A_diag : Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift σ.lift (A :: Γ) :=
      W.left.lift hA hA_σ
    have hB_σ : (A.subst σ) :: Γ₀ ⊢ B.subst σ.lift : .sort v :=
      (ih2 hΓ_A_σ W_A_diag).1
    have ha_σ : Γ₀ ⊢ a.subst σ : A.subst σ := (ih3 hΓ₀ W.left).1
    have hb_σ : Γ₀ ⊢ b.subst σ : (B.subst σ.lift).inst (a.subst σ) := by
      have := (ih4 hΓ₀ W.left).1
      rwa [show (B.inst a).subst σ = (B.subst σ.lift).inst (a.subst σ) from subst_inst] at this
    have hLHS_σ : Γ₀ ⊢ Term.snd (Term.pair (A.subst σ) (B.subst σ.lift) (a.subst σ) (b.subst σ)) :
        (B.subst σ.lift).inst (a.subst σ) :=
      subst_inst ▸ (ih5 hΓ₀ W.left).1
    have H_σ : Γ₀ ⊢ (Term.snd (Term.pair A B a b)).subst σ ≡ b.subst σ :
        (B.inst a).subst σ :=
      subst_inst.symm ▸ (show Γ₀ ⊢ Term.snd
          (Term.pair (A.subst σ) (B.subst σ.lift) (a.subst σ) (b.subst σ))
          ≡ b.subst σ : (B.subst σ.lift).inst (a.subst σ) from
        .pair_snd hA_σ hB_σ ha_σ hb_σ hLHS_σ)
    exact ⟨ih5_l, ih4_l, H_σ.trans ih4_l⟩
  | @fst_snd Γ p A B _ _ ih1 ih2 =>
    have ih2_l := (ih2 hΓ₀ W).1
    have ih1_l := (ih1 hΓ₀ W).1
    have hp_σ : Γ₀ ⊢ p.subst σ : (Term.sigma A B).subst σ := (ih1 hΓ₀ W.left).1
    have hLHS_σ : Γ₀ ⊢ (Term.pair A B (.fst p) (.snd p)).subst σ : (Term.sigma A B).subst σ :=
      (ih2 hΓ₀ W.left).1
    have H_σ : Γ₀ ⊢ (Term.pair A B (.fst p) (.snd p)).subst σ ≡ p.subst σ :
        (Term.sigma A B).subst σ :=
      show Γ₀ ⊢ Term.pair (A.subst σ) (B.subst σ.lift) (.fst (p.subst σ)) (.snd (p.subst σ)) ≡
          p.subst σ : Term.sigma (A.subst σ) (B.subst σ.lift) from
      .fst_snd hp_σ hLHS_σ
    exact ⟨ih2_l, ih1_l, H_σ.trans ih1_l⟩
  | nat => exact ⟨.nat, .nat, .nat⟩
  | zero => exact ⟨.zero, .zero, .zero⟩
  | succDF _ ih1 => let ⟨l, r, c⟩ := ih1 hΓ₀ W; exact ⟨.succDF l, .succDF r, .succDF c⟩
  | @natCaseDF Γ C C' v M M' a a' b b' _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    have hΓ_Nat : ⊢ .nat :: Γ₀ := ⟨hΓ₀, _, .nat⟩
    have Wl := W.lift .nat .nat
    let ⟨ihC_l, _, ihC_c⟩ := ih1 hΓ_Nat Wl
    have ihC_cleft := (ih1 hΓ_Nat Wl.left).2.2
    let ⟨ihM_l, _, ihM_c⟩ := ih2 hΓ₀ W
    have ihM_cleft := (ih2 hΓ₀ W.left).2.2
    have iha_l := subst_inst ▸ (ih3 hΓ₀ W).1
    have iha_c := subst_inst ▸ (ih3 hΓ₀ W).2.2
    have iha_cleft := subst_inst ▸ (ih3 hΓ₀ W.left).2.2
    have ihb_l := subst_succ_branch_swap C σ ▸ (ih4 hΓ_Nat Wl).1
    have ihb_c := subst_succ_branch_swap C σ ▸ (ih4 hΓ_Nat Wl).2.2
    have ihb_cleft := subst_succ_branch_swap C σ ▸ (ih4 hΓ_Nat Wl.left).2.2
    have ⟨ihCM_l, _, ihCM_c⟩ := ih5 hΓ₀ W; have ihCM_cleft := (ih5 hΓ₀ W.left).2.2
    rw [subst_inst, subst_inst] at ihCM_l ihCM_c ihCM_cleft
    have res_l : Γ₀ ⊢ (Term.natCase C M a b).subst σ ≡
        (Term.natCase C M a b).subst τ : (C.inst M).subst σ := by
      rw [subst_inst]; exact .natCaseDF ihC_l ihM_l iha_l ihb_l ihCM_l
    have res_c : Γ₀ ⊢ (Term.natCase C M a b).subst σ ≡
        (Term.natCase C' M' a' b').subst τ : (C.inst M).subst σ := by
      rw [subst_inst]; exact .natCaseDF ihC_c ihM_c iha_c ihb_c ihCM_c
    have res_c' : Γ₀ ⊢ (Term.natCase C M a b).subst σ ≡
        (Term.natCase C' M' a' b').subst σ : (C.inst M).subst σ := by
      rw [subst_inst]; exact .natCaseDF ihC_cleft ihM_cleft iha_cleft ihb_cleft ihCM_cleft
    exact ⟨res_l, res_c'.symm.trans res_c, res_c⟩
  | @natCase_zero Γ C v a b _ _ _ _ ih1 ih2 ih3 ih4 =>
    have hΓ_Nat : ⊢ .nat :: Γ₀ := ⟨hΓ₀, _, .nat⟩
    have Wl := W.lift .nat .nat |>.left
    refine ⟨(ih4 hΓ₀ W).1, (ih2 hΓ₀ W).1, .trans ?_ (ih2 hΓ₀ W).1⟩
    refine subst_inst.symm ▸ .natCase_zero (ih1 hΓ_Nat Wl).1
      (subst_inst ▸ (ih2 hΓ₀ W.left).1 :)
      (subst_succ_branch_swap C σ ▸ (ih3 hΓ_Nat Wl).1 :)
      (subst_inst ▸ (ih4 hΓ₀ W.left).1 :)
  | @natCase_succ Γ C v n a b _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    have hΓ_Nat : ⊢ .nat :: Γ₀ := ⟨hΓ₀, _, .nat⟩
    have Wl := W.lift .nat .nat |>.left
    refine ⟨(ih5 hΓ₀ W).1, (ih6 hΓ₀ W).1, .trans ?_ (ih6 hΓ₀ W).1⟩
    rw [subst_inst, subst_inst]
    refine .natCase_succ (ih1 hΓ_Nat Wl).1 (ih2 hΓ₀ W.left).1
      (subst_inst ▸ (ih3 hΓ₀ W.left).1 :)
      (subst_succ_branch_swap C σ ▸ (ih4 hΓ_Nat Wl).1 :)
      (subst_inst ▸ (ih5 hΓ₀ W.left).1 :) ?_
    have := (ih6 hΓ₀ W.left).1; rwa [subst_inst, subst_inst] at this
  | unit_eta _ ih => have ⟨l, _, _⟩ := ih hΓ₀ W; exact ⟨.star, l, .unit_eta l.hasType.2⟩
  | @YDF Γ A A' u b b' h1 _ _ ih1 ih2 ih3 =>
    let ⟨ihA_l, ihA_r, ihA_c⟩ := ih1 hΓ₀ W
    have hA_in_Γ : Γ ⊢ A : .sort u := h1.hasType.1
    have hA'_in_Γ : Γ ⊢ A' : .sort u := h1.hasType.2
    have hA_subst : Γ₀ ⊢ A.subst σ : .sort u := ihA_l.hasType.1
    have hA_τ_subst : Γ₀ ⊢ A.subst τ : .sort u := ihA_l.hasType.2
    have hA'_subst : Γ₀ ⊢ A'.subst σ : .sort u := ihA_r.hasType.1
    have hA'_τ_subst : Γ₀ ⊢ A'.subst τ : .sort u := ihA_r.hasType.2
    have hΓ_A_subst : ⊢ A.subst σ :: Γ₀ := ⟨hΓ₀, _, hA_subst⟩
    have hΓ_A_τ_subst : ⊢ A.subst τ :: Γ₀ := ⟨hΓ₀, _, hA_τ_subst⟩
    have hΓ_A'_subst : ⊢ A'.subst σ :: Γ₀ := ⟨hΓ₀, _, hA'_subst⟩
    have hΓ_A'_τ_subst : ⊢ A'.subst τ :: Γ₀ := ⟨hΓ₀, _, hA'_τ_subst⟩
    have hAA'_σ : Γ₀ ⊢ A.subst σ ≡ A'.subst σ : .sort u := (ih1 hΓ₀ W.left).2.2
    have W_A : Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift τ.lift (A :: Γ) :=
      W.lift hA_in_Γ hA_subst
    have W_A_τ : Ctx.SubstEq (A.subst τ :: Γ₀) σ.lift τ.lift (A :: Γ) :=
      W.lift_at hA_in_Γ hA_τ_subst ihA_l
    have W_A_to_A'τ : Ctx.SubstEq (A'.subst τ :: Γ₀) σ.lift τ.lift (A :: Γ) :=
      W.lift_at hA_in_Γ hA'_τ_subst ihA_c
    have W_left_A'σ : Ctx.SubstEq (A'.subst σ :: Γ₀) σ.lift σ.lift (A :: Γ) :=
      W.left.lift_at hA_in_Γ hA'_subst hAA'_σ
    have body_l : (A.subst σ) :: Γ₀ ⊢ b.subst σ.lift ≡ b.subst τ.lift : (A.subst σ).lift :=
      lift_subst_lift ▸ (ih2 hΓ_A_subst W_A).1
    have body_l_at_Aτ_raw := lift_subst_lift ▸ (ih2 hΓ_A_τ_subst W_A_τ).1
    have body_l_at_Aτ : (A.subst τ) :: Γ₀ ⊢ b.subst σ.lift ≡ b.subst τ.lift : (A.subst τ).lift :=
      .defeqDF (ihA_l.weak' (.skip .refl)) body_l_at_Aτ_raw
    have body_c : (A.subst σ) :: Γ₀ ⊢ b.subst σ.lift ≡ b'.subst τ.lift : (A.subst σ).lift :=
      lift_subst_lift ▸ (ih2 hΓ_A_subst W_A).2.2
    have body_c_at_A'τ_raw := lift_subst_lift ▸ (ih2 hΓ_A'_τ_subst W_A_to_A'τ).2.2
    have body_c_at_A'τ := (ihA_c.weak' (.skip .refl)).defeqDF body_c_at_A'τ_raw
    have body_cd : (A.subst σ) :: Γ₀ ⊢ b.subst σ.lift ≡ b'.subst σ.lift : (A.subst σ).lift :=
      lift_subst_lift ▸ (ih2 hΓ_A_subst W_A.left).2.2
    have body_cd_at_A'σ_raw := lift_subst_lift ▸ (ih2 hΓ_A'_subst W_left_A'σ).2.2
    have body_cd_at_A'σ := (hAA'_σ.weak' (.skip .refl)).defeqDF body_cd_at_A'σ_raw
    have res_l : Γ₀ ⊢ (Term.Y A b).subst σ ≡ (Term.Y A b).subst τ : A.subst σ :=
      .YDF ihA_l body_l body_l_at_Aτ
    have res_c : Γ₀ ⊢ (Term.Y A b).subst σ ≡ (Term.Y A' b').subst τ : A.subst σ :=
      .YDF ihA_c body_c body_c_at_A'τ
    have res_cd : Γ₀ ⊢ (Term.Y A b).subst σ ≡ (Term.Y A' b').subst σ : A.subst σ :=
      .YDF hAA'_σ body_cd body_cd_at_A'σ
    exact ⟨res_l, res_cd.symm.trans res_c, res_c⟩
  | @Y_unfold Γ A u b h1 _ _ _ ih1 ih2 ih3 ih4 =>
    have ih3_l := (ih3 hΓ₀ W).1
    have ih4_l := (ih4 hΓ₀ W).1
    have hA_σ : Γ₀ ⊢ A.subst σ : .sort u := (ih1 hΓ₀ W.left).1
    have hΓ_A_σ : ⊢ A.subst σ :: Γ₀ := ⟨hΓ₀, _, hA_σ⟩
    have W_A_diag : Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift σ.lift (A :: Γ) :=
      W.left.lift h1 hA_σ
    have hb_σ : (A.subst σ) :: Γ₀ ⊢ b.subst σ.lift : (A.subst σ).lift :=
      lift_subst_lift ▸ (ih2 hΓ_A_σ W_A_diag).1
    have hy_σ : Γ₀ ⊢ Term.Y (A.subst σ) (b.subst σ.lift) : A.subst σ := (ih3 hΓ₀ W.left).1
    have hbinst_σ : Γ₀ ⊢ (b.subst σ.lift).inst (Term.Y (A.subst σ) (b.subst σ.lift)) :
        A.subst σ := by
      have := (ih4 hΓ₀ W.left).1
      rwa [show ((b.inst (Term.Y A b)).subst σ) =
            (b.subst σ.lift).inst (Term.Y (A.subst σ) (b.subst σ.lift)) from subst_inst] at this
    have H_σ : Γ₀ ⊢ (Term.Y A b).subst σ ≡ (b.inst (Term.Y A b)).subst σ : A.subst σ := by
      rw [show ((b.inst (Term.Y A b)).subst σ) =
            (b.subst σ.lift).inst (Term.Y (A.subst σ) (b.subst σ.lift)) from subst_inst]
      exact .Y_unfold hA_σ hb_σ hy_σ hbinst_σ
    exact ⟨ih3_l, ih4_l, H_σ.trans ih4_l⟩
  | @idDF Γ A A' u a a' b b' _ _ _ ih1 ih2 ih3 =>
    let ⟨ihA_l, ihA_r, ihA_c⟩ := ih1 hΓ₀ W
    let ⟨iha_l, iha_r, iha_c⟩ := ih2 hΓ₀ W
    let ⟨ihb_l, ihb_r, ihb_c⟩ := ih3 hΓ₀ W
    have hAA'_σ : Γ₀ ⊢ A.subst σ ≡ A'.subst σ : .sort u := (ih1 hΓ₀ W.left).2.2
    exact ⟨.idDF ihA_l iha_l ihb_l,
           .idDF ihA_r (.defeqDF hAA'_σ iha_r) (.defeqDF hAA'_σ ihb_r),
           .idDF ihA_c iha_c ihb_c⟩
  | @reflDF Γ A u a a' _hA _ha _h_id ih1 ih2 ih3 =>
    let ⟨iha_l, iha_r, iha_c⟩ := ih2 hΓ₀ W
    have ⟨_, _, iha_cleft⟩ := ih2 hΓ₀ W.left
    have ihA_σ : Γ₀ ⊢ A.subst σ : .sort u := (ih1 hΓ₀ W).1.hasType.1
    have ih_id_σ : Γ₀ ⊢ (Term.id A a a).subst σ : .type := (ih3 hΓ₀ W).1.hasType.1
    have res_l : Γ₀ ⊢ (Term.refl a).subst σ ≡ (Term.refl a).subst τ : (Term.id A a a).subst σ :=
      .reflDF ihA_σ iha_l ih_id_σ
    have ih_id_a'σ : Γ₀ ⊢ Term.id (A.subst σ) (a'.subst σ) (a'.subst σ) : .type :=
      (IsDefEq.idDF (A := A.subst σ) (A' := A.subst σ)
        ihA_σ iha_r.hasType.1 iha_r.hasType.1).hasType.1
    have res_r_natural : Γ₀ ⊢ (Term.refl a').subst σ ≡ (Term.refl a').subst τ :
        Term.id (A.subst σ) (a'.subst σ) (a'.subst σ) :=
      .reflDF ihA_σ iha_r ih_id_a'σ
    have id_r_to_l : Γ₀ ⊢ Term.id (A.subst σ) (a'.subst σ) (a'.subst σ) ≡
        Term.id (A.subst σ) (a.subst σ) (a.subst σ) : .type :=
      .idDF ihA_σ iha_cleft.symm iha_cleft.symm
    have res_r : Γ₀ ⊢ (Term.refl a').subst σ ≡ (Term.refl a').subst τ :
        (Term.id A a a).subst σ :=
      .defeqDF id_r_to_l res_r_natural
    have res_c : Γ₀ ⊢ (Term.refl a).subst σ ≡ (Term.refl a').subst τ : (Term.id A a a).subst σ :=
      .reflDF ihA_σ iha_c ih_id_σ
    exact ⟨res_l, res_r, res_c⟩
  | @trDF Γ A A' u a a' b b' C C' v x x' h h' _hA _ha _hb _hC _hC' _hx _hh _hCb _h_id
        ih1 ih2 ih3 ih4 ih4' ih5 ih6 ih7 ih8 =>
    have hA_in_Γ : Γ ⊢ A : .sort u := _hA.hasType.1
    have hA'_in_Γ : Γ ⊢ A' : .sort u := _hA.hasType.2
    let ⟨ihA_l, ihA_r, ihA_c⟩ := ih1 hΓ₀ W
    have hA_σ : Γ₀ ⊢ A.subst σ : .sort u := ihA_l.hasType.1
    have hA_τ : Γ₀ ⊢ A.subst τ : .sort u := ihA_l.hasType.2
    have hA'_σ : Γ₀ ⊢ A'.subst σ : .sort u := ihA_r.hasType.1
    have hA'_τ : Γ₀ ⊢ A'.subst τ : .sort u := ihA_r.hasType.2
    have hAA'_σ : Γ₀ ⊢ A.subst σ ≡ A'.subst σ : .sort u := (ih1 hΓ₀ W.left).2.2
    have hΓ_A_σ : ⊢ A.subst σ :: Γ₀ := ⟨hΓ₀, _, hA_σ⟩
    have hΓ_A'_σ : ⊢ A'.subst σ :: Γ₀ := ⟨hΓ₀, _, hA'_σ⟩
    have hΓ_A_τ : ⊢ A.subst τ :: Γ₀ := ⟨hΓ₀, _, hA_τ⟩
    have hΓ_A'_τ : ⊢ A'.subst τ :: Γ₀ := ⟨hΓ₀, _, hA'_τ⟩
    have W_A : Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift τ.lift (A :: Γ) :=
      W.lift hA_in_Γ hA_σ
    have W_A_τ : Ctx.SubstEq (A.subst τ :: Γ₀) σ.lift τ.lift (A :: Γ) :=
      W.lift_at hA_in_Γ hA_τ ihA_l
    have ⟨iha_l, iha_r, iha_c⟩ := ih2 hΓ₀ W
    have ha'_σ : Γ₀ ⊢ a'.subst σ : A.subst σ := iha_r.hasType.1
    have ⟨ihb_l, ihb_r, ihb_c⟩ := ih3 hΓ₀ W
    let ⟨ihC_l, _, ihC_c⟩ := ih4 hΓ_A_σ W_A
    let ⟨ihx_l_raw, ihx_r_raw, ihx_c_raw⟩ := ih5 hΓ₀ W
    have ihx_l : Γ₀ ⊢ x.subst σ ≡ x.subst τ : (C.subst σ.lift).inst (a.subst σ) :=
      subst_inst ▸ ihx_l_raw
    have ihx_r : Γ₀ ⊢ x'.subst σ ≡ x'.subst τ : (C.subst σ.lift).inst (a.subst σ) :=
      subst_inst ▸ ihx_r_raw
    have ihx_c : Γ₀ ⊢ x.subst σ ≡ x'.subst τ : (C.subst σ.lift).inst (a.subst σ) :=
      subst_inst ▸ ihx_c_raw
    let ⟨ihh_l, ihh_r, ihh_c⟩ := ih6 hΓ₀ W
    have ⟨ihCb_l_raw, ihCb_r_raw, ihCb_c_raw⟩ := ih7 hΓ₀ W
    have ihCb_l : Γ₀ ⊢ (C.subst σ.lift).inst (b.subst σ) ≡
        (C.subst τ.lift).inst (b.subst τ) : .sort v := by
      rwa [subst_inst, subst_inst] at ihCb_l_raw
    have ihCb_c : Γ₀ ⊢ (C.subst σ.lift).inst (b.subst σ) ≡
        (C'.subst τ.lift).inst (b'.subst τ) : .sort v := by
      rwa [subst_inst, subst_inst] at ihCb_c_raw
    have ihCb_r : Γ₀ ⊢ (C'.subst σ.lift).inst (b'.subst σ) ≡
        (C'.subst τ.lift).inst (b'.subst τ) : .sort v := by
      rwa [subst_inst, subst_inst] at ihCb_r_raw
    have ihCb_cleft : Γ₀ ⊢ (C.subst σ.lift).inst (b.subst σ) ≡
        (C'.subst σ.lift).inst (b'.subst σ) : .sort v := by
      simpa [subst_inst] using (ih7 hΓ₀ W.left).2.2
    let ⟨ih_id_l, _, _⟩ := ih8 hΓ₀ W
    have hId_l : Γ₀ ⊢ .id (A.subst σ) (a.subst σ) (b.subst σ) : .type :=
      .idDF ihA_l.hasType.1 iha_l.hasType.1 ihb_l.hasType.1
    have W_A'_τ : Ctx.SubstEq (A'.subst τ :: Γ₀) σ.lift τ.lift (A' :: Γ) :=
      W.lift_at hA'_in_Γ hA'_τ ihA_r
    have ihC_l_dual : (A.subst τ) :: Γ₀ ⊢ C.subst σ.lift ≡ C.subst τ.lift : .sort v :=
      (ih4 hΓ_A_τ W_A_τ).1
    have ihC_c_dual : (A'.subst τ) :: Γ₀ ⊢ C.subst σ.lift ≡ C'.subst τ.lift : .sort v :=
      (ih4' hΓ_A'_τ W_A'_τ).2.2
    have res_l : Γ₀ ⊢ (Term.tr A a b C x h).subst σ ≡ (Term.tr A a b C x h).subst τ :
        (C.inst b).subst σ := by
      rw [subst_inst]
      exact .trDF ihA_l iha_l ihb_l ihC_l ihC_l_dual ihx_l ihh_l ihCb_l hId_l
    have res_c : Γ₀ ⊢ (Term.tr A a b C x h).subst σ ≡ (Term.tr A' a' b' C' x' h').subst τ :
        (C.inst b).subst σ := by
      rw [subst_inst]
      exact .trDF ihA_c iha_c ihb_c ihC_c ihC_c_dual ihx_c ihh_c ihCb_c hId_l
    have iha_r_at_A'σ : Γ₀ ⊢ a'.subst σ ≡ a'.subst τ : A'.subst σ :=
      .defeqDF hAA'_σ iha_r
    have ihb_r_at_A'σ : Γ₀ ⊢ b'.subst σ ≡ b'.subst τ : A'.subst σ :=
      .defeqDF hAA'_σ ihb_r
    have W_A'_σ : Ctx.SubstEq (A'.subst σ :: Γ₀) σ.lift τ.lift (A' :: Γ) :=
      W.lift hA'_in_Γ hA'_σ
    have ihC_r_at_A'binder : (A'.subst σ) :: Γ₀ ⊢ C'.subst σ.lift ≡ C'.subst τ.lift : .sort v :=
      (ih4' hΓ_A'_σ W_A'_σ).2.1
    have ihC_r_dual : (A'.subst τ) :: Γ₀ ⊢ C'.subst σ.lift ≡ C'.subst τ.lift : .sort v :=
      (ih4' hΓ_A'_τ W_A'_τ).2.1
    have W_cons_a_at_A'σ : Ctx.SubstEq Γ₀ (σ.cons (a'.subst σ)) (σ.cons (a'.subst σ)) (A :: Γ) := by
      have htail : (σ.cons (a'.subst σ)).tail = σ := by funext i; rfl
      refine .cons (htail ▸ W.left) hA_in_Γ ?_
      rw [htail]; exact ha'_σ
    have hCa'_C_to_C' : Γ₀ ⊢ (C.subst σ.lift).inst (a'.subst σ) ≡
        (C'.subst σ.lift).inst (a'.subst σ) : .sort v := by
      have := (ih4 hΓ₀ W_cons_a_at_A'σ).2.2
      rwa [← inst_lift_cons (e := C), ← inst_lift_cons (e := C')] at this
    have W_cons_a_to_a' : Ctx.SubstEq Γ₀ (σ.cons (a.subst σ)) (σ.cons (a'.subst σ)) (A :: Γ) := by
      have htail : (σ.cons (a.subst σ)).tail = σ := by funext i; rfl
      have htail' : (σ.cons (a'.subst σ)).tail = σ := by funext i; rfl
      refine .cons (htail ▸ htail' ▸ W.left) hA_in_Γ ?_
      rw [htail]; exact (ih2 hΓ₀ W.left).2.2
    have hC_a_to_a' : Γ₀ ⊢ (C.subst σ.lift).inst (a.subst σ) ≡
        (C.subst σ.lift).inst (a'.subst σ) : .sort v := by
      have := (ih4 hΓ₀ W_cons_a_to_a').1
      rwa [← inst_lift_cons (e := C), ← inst_lift_cons (e := C)] at this
    have ihx_r_at_C' : Γ₀ ⊢ x'.subst σ ≡ x'.subst τ :
        (C'.subst σ.lift).inst (a'.subst σ) :=
      .defeqDF hCa'_C_to_C' (.defeqDF hC_a_to_a' ihx_r)
    have hId_r_iff : Γ₀ ⊢ Term.id (A.subst σ) (a.subst σ) (b.subst σ) ≡
        Term.id (A'.subst σ) (a'.subst σ) (b'.subst σ) : .type :=
      .idDF hAA'_σ ((ih2 hΓ₀ W.left).2.2) ((ih3 hΓ₀ W.left).2.2)
    have ihh_r_at_A' : Γ₀ ⊢ h'.subst σ ≡ h'.subst τ :
        Term.id (A'.subst σ) (a'.subst σ) (b'.subst σ) :=
      .defeqDF hId_r_iff ihh_r
    have hId_r : Γ₀ ⊢ .id (A'.subst σ) (a'.subst σ) (b'.subst σ) : .type :=
      .idDF ihA_r.hasType.1 iha_r_at_A'σ.hasType.1 ihb_r_at_A'σ.hasType.1
    have res_r_natural : Γ₀ ⊢ (Term.tr A' a' b' C' x' h').subst σ ≡
        (Term.tr A' a' b' C' x' h').subst τ : (C'.subst σ.lift).inst (b'.subst σ) := by
      show Γ₀ ⊢ Term.tr _ _ _ _ _ _ ≡ Term.tr _ _ _ _ _ _ : _
      exact .trDF ihA_r iha_r_at_A'σ ihb_r_at_A'σ ihC_r_at_A'binder ihC_r_dual
        ihx_r_at_C' ihh_r_at_A' ihCb_r hId_r
    have res_r : Γ₀ ⊢ (Term.tr A' a' b' C' x' h').subst σ ≡
        (Term.tr A' a' b' C' x' h').subst τ : (C.inst b).subst σ := by
      rw [subst_inst]
      exact .defeqDF ihCb_cleft.symm res_r_natural
    exact ⟨res_l, res_r, res_c⟩
  | @tr_refl Γ A u a C v x _hA _ha _hC _hx _hLHS ih1 ih2 ih3 ih4 ih5 =>
    have ih4_l := (ih4 hΓ₀ W).1
    have hA_σ : Γ₀ ⊢ A.subst σ : .sort u := (ih1 hΓ₀ W.left).1
    have ha_σ : Γ₀ ⊢ a.subst σ : A.subst σ := (ih2 hΓ₀ W.left).1
    have hΓ_A_σ : ⊢ A.subst σ :: Γ₀ := ⟨hΓ₀, _, hA_σ⟩
    have W_A : Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift σ.lift (A :: Γ) :=
      W.left.lift _hA hA_σ
    have hC_σ : A.subst σ :: Γ₀ ⊢ C.subst σ.lift : .sort v := (ih3 hΓ_A_σ W_A).1
    have hx_σ : Γ₀ ⊢ x.subst σ : (C.subst σ.lift).inst (a.subst σ) := by
      have := (ih4 hΓ₀ W.left).1
      rwa [subst_inst] at this
    have hLHS_σ : Γ₀ ⊢ (Term.tr A a a C x (.refl a)).subst σ :
        (C.subst σ.lift).inst (a.subst σ) := by
      have := (ih5 hΓ₀ W.left).1
      rwa [subst_inst] at this
    have H_σ : Γ₀ ⊢ (Term.tr A a a C x (.refl a)).subst σ ≡ x.subst σ :
        (C.inst a).subst σ := by
      rw [subst_inst]
      exact .tr_refl hA_σ ha_σ hC_σ hx_σ hLHS_σ
    exact ⟨(ih5 hΓ₀ W).1, ih4_l, H_σ.trans ih4_l⟩

/-- Main substitution lemma: from `Γ ⊢ e₁ ≡ e₂ : A` and a diagonal
two-sided substitution `Ctx.SubstEq Γ₀ σ σ Γ` we get
`Γ₀ ⊢ e₁.subst σ ≡ e₂.subst σ : A.subst σ`. Derived as a corollary of the
three-conjunct `substEq'` at diagonal `W`. -/
theorem IsDefEq.subst (hΓ₀ : ⊢ Γ₀)
    (W : Ctx.SubstEq Γ₀ σ σ Γ) (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ₀ ⊢ e1.subst σ ≡ e2.subst σ : A.subst σ :=
  (H.substEq' hΓ₀ W).2.2

/-- Non-diagonal substitution lemma: from `Γ ⊢ e₁ ≡ e₂ : A` and a two-sided
`SubstEq Γ₀ σ σ' Γ` we get `Γ₀ ⊢ e₁.subst σ ≡ e₂.subst σ' : A.subst σ`
(the cross conjunct of the three-conjunct `substEq'`). The diagonal
version `IsDefEq.subst` falls out by taking `σ' = σ`. -/
theorem IsDefEq.subst' (hΓ₀ : ⊢ Γ₀)
    (W : Ctx.SubstEq Γ₀ σ σ' Γ) (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ₀ ⊢ e1.subst σ ≡ e2.subst σ' : A.subst σ :=
  (H.substEq' hΓ₀ W).2.2

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
  exact H.subst hΓ W

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
        (.appDF hA hB (.lamDF hA hB hf.hasType.1 hf.hasType.1 (.forallEDF hA hB hB)) ha
          (.inst0 hΓ ha.hasType.1 hB))
        (.inst0 hΓ ha.hasType.1 hf.hasType.1)
    (H1 hf ha.hasType.1).symm.trans <|
      .trans (.appDF hA hB (.lamDF hA hB hf hf (.forallEDF hA hB hB)) ha hi) <|
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

theorem IsDefEq.sigma_inv' (hΓ : ⊢ Γ)
    (H : Γ ⊢ e1 ≡ e2 : V) (eq : e1 = A.sigma B ∨ e2 = A.sigma B) :
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
  | sigmaDF h1 h2 _ =>
    obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := eq
    · exact ⟨⟨_, h1.hasType.1⟩, _, h2.hasType.1⟩
    · exact ⟨⟨_, h1.hasType.2⟩, _, h1.defeqDF_l hΓ h2.hasType.2⟩
  | defeqDF _ _ _ ih2 => exact ih2 hΓ eq
  | beta _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih hΓ (.inr eq)
  | eta _ _ ih _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih hΓ (.inr eq)
  | unit_eta _ ih =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih hΓ (.inr eq)
  | pair_fst _ _ _ _ _ _ _ ih3 _ _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih3 hΓ (.inl eq)
  | pair_snd _ _ _ _ _ _ _ _ ih4 _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih4 hΓ (.inl eq)
  | fst_snd _ _ ih1 _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih1 hΓ (.inr eq)
  | natCase_zero _ _ _ _ _ ih2 _ _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih2 hΓ (.inl eq)
  | natCase_succ _ _ _ _ _ _ _ _ _ _ _ ih6 =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih6 hΓ (.inl eq)
  | Y_unfold _ _ _ _ _ _ _ ihred =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ihred hΓ (.inl eq)
  | tr_refl _ _ _ _ _ _ _ _ ih_x _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih_x hΓ (.inr eq)
  | _ => nomatch eq

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
  | beta _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih hΓ (.inr eq)
  | eta _ _ ih _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih hΓ (.inr eq)
  | unit_eta _ ih =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih hΓ (.inr eq)
  | pair_fst _ _ _ _ _ _ _ ih3 _ _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih3 hΓ (.inl eq)
  | pair_snd _ _ _ _ _ _ _ _ ih4 _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih4 hΓ (.inl eq)
  | fst_snd _ _ ih1 _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih1 hΓ (.inr eq)
  | natCase_zero _ _ _ _ _ ih2 _ _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih2 hΓ (.inl eq)
  | natCase_succ _ _ _ _ _ _ _ _ _ _ _ ih6 =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih6 hΓ (.inl eq)
  | Y_unfold _ _ _ _ _ _ _ ihred =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ihred hΓ (.inl eq)
  | tr_refl _ _ _ _ _ _ _ _ ih_x _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih_x hΓ (.inr eq)
  | _ => nomatch eq

theorem IsDefEq.id_inv' (hΓ : ⊢ Γ)
    (H : Γ ⊢ e1 ≡ e2 : V) (eq : e1 = Term.id A a b ∨ e2 = Term.id A a b) :
    (∃ u, Γ ⊢ A : .sort u) ∧ (Γ ⊢ a : A) ∧ (Γ ⊢ b : A) := by
  induction H generalizing A a b with
  | symm _ ih => exact ih hΓ eq.symm
  | trans _ _ ih1 ih2
  | trans' _ _ ih1 ih2
  | proofIrrel _ _ _ _ ih1 ih2 =>
    obtain eq | eq := eq
    · exact ih1 hΓ (.inl eq)
    · exact ih2 hΓ (.inr eq)
  | idDF hA ha hb =>
    obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := eq
    · exact ⟨⟨_, hA.hasType.1⟩, ha.hasType.1, hb.hasType.1⟩
    · exact ⟨⟨_, hA.hasType.2⟩, .defeqDF hA ha.hasType.2, .defeqDF hA hb.hasType.2⟩
  | defeqDF _ _ _ ih2 => exact ih2 hΓ eq
  | beta _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih hΓ (.inr eq)
  | eta _ _ ih _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih hΓ (.inr eq)
  | pair_fst _ _ _ _ _ _ _ ih3 _ _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih3 hΓ (.inl eq)
  | pair_snd _ _ _ _ _ _ _ _ ih4 _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih4 hΓ (.inl eq)
  | fst_snd _ _ ih1 _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih1 hΓ (.inr eq)
  | tr_refl _ _ _ _ _ _ _ _ ih_x _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih_x hΓ (.inr eq)
  | @Y_unfold _ _ _ _ _ _ _ _ _ _ _ ih4 =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih4 hΓ (.inr eq)
  | unit_eta _ ih =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih hΓ (.inl eq)
  | natCase_zero _ _ _ _ _ ih2 _ _ =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih2 hΓ (.inl eq)
  | natCase_succ _ _ _ _ _ _ _ _ _ _ _ ih6 =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih6 hΓ (.inl eq)
  | _ => nomatch eq

theorem IsDefEq.bvar₀ (hΓ : ⊢ Γ) (h : Lookup Γ i A) : Γ ⊢ .bvar i : A :=
  let ⟨_, hA⟩ := hΓ.lookup h; .bvar h hA

theorem IsDefEq.appDF₀ (hΓ : ⊢ Γ)
    (hf : Γ ⊢ f ≡ f' : .forallE A B) (ha : Γ ⊢ a ≡ a' : A) :
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a :=
  let ⟨_, h3⟩ := hf.isType hΓ
  let ⟨⟨_, hA⟩, _, hB⟩ := h3.forallE_inv' hΓ (.inl rfl)
  .appDF hA hB hf ha (.instDF hΓ hA .sort hB ha)

theorem IsDefEq.forallEDF₀ (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A ≡ A' : .sort u) (hbody : A::Γ ⊢ body ≡ body' : .sort v) :
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort v :=
  .forallEDF hA hbody (hA.defeqDF_l hΓ hbody)

theorem IsDefEq.lamDF₀ (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A ≡ A' : .sort u) (hbody : A::Γ ⊢ body ≡ body' : B) :
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B :=
  let ⟨_, hB⟩ := hbody.isType (Γ := _::_) ⟨hΓ, _, hA.hasType.1⟩
  .lamDF hA hB hbody (hA.defeqDF_l hΓ hbody) (.forallEDF₀ hΓ hA.hasType.1 hB)

theorem IsDefEq.beta₀ (hΓ : ⊢ Γ) (he : A::Γ ⊢ e : B) (he' : Γ ⊢ e' : A) :
    Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e' :=
  have ⟨_, hA⟩ := he'.isType hΓ
  .beta hA he he' (.appDF₀ hΓ (.lamDF₀ hΓ hA he) he') (he'.inst0 hΓ he)

theorem IsDefEq.eta₀ {Γ e A B} (hΓ : ⊢ Γ) (he : Γ ⊢ e : .forallE A B) :
    Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B := by
  let ⟨_, hAB⟩ := he.isType hΓ
  let ⟨⟨_, hA⟩, v, hB⟩ := hAB.forallE_inv' hΓ (.inl rfl)
  have : A::Γ ⊢ .app e.lift (.bvar 0) : (B.lift' (.cons (.skip .refl))).inst (.bvar 0) :=
    .appDF₀ ⟨hΓ, _, hA⟩ (he.weak' (.skip .refl)) (.bvar .zero (hA.weak' (.skip .refl)))
  rw [lift_cons_skip_inst_bvar0] at this
  exact .eta he (.lamDF₀ hΓ hA this)

theorem IsDefEq.sigmaDF₀ (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A ≡ A' : .sort u) (hB : A::Γ ⊢ B ≡ B' : .sort v) :
    Γ ⊢ .sigma A B ≡ .sigma A' B' : .type :=
  .sigmaDF hA hB (hA.defeqDF_l hΓ hB)

theorem IsDefEq.pairDF₀ (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A ≡ A' : .sort u) (hB : A::Γ ⊢ B ≡ B' : .sort v)
    (ha : Γ ⊢ a ≡ a' : A) (hb : Γ ⊢ b ≡ b' : B.inst a) :
    Γ ⊢ .pair A B a b ≡ .pair A' B' a' b' : .sigma A B :=
  .pairDF hA hB (hA.defeqDF_l hΓ hB) ha hb
    (.instDF hΓ hA.hasType.1 .sort hB ha)
    (.sigmaDF₀ hΓ hA.hasType.1 hB.hasType.1)

theorem IsDefEq.fstDF₀ (hΓ : ⊢ Γ)
    (hp : Γ ⊢ p ≡ p' : .sigma A B) :
    Γ ⊢ .fst p ≡ .fst p' : A :=
  let ⟨_, hsigma⟩ := hp.isType hΓ
  let ⟨⟨_, hA⟩, _, hB⟩ := hsigma.sigma_inv' hΓ (.inl rfl)
  .fstDF hA hB hp

theorem IsDefEq.sndDF₀ (hΓ : ⊢ Γ)
    (hp : Γ ⊢ p ≡ p' : .sigma A B) :
    Γ ⊢ .snd p ≡ .snd p' : B.inst (.fst p) :=
  let ⟨_, hsigma⟩ := hp.isType hΓ
  let ⟨⟨_, hA⟩, _, hB⟩ := hsigma.sigma_inv' hΓ (.inl rfl)
  .sndDF hA hB hp (hA.instDF hΓ .sort hB (.fstDF₀ hΓ hp))

theorem IsDefEq.pair_fst₀ (hΓ : ⊢ Γ)
    (hB : A::Γ ⊢ B : .sort v) (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : B.inst a) :
    Γ ⊢ .fst (.pair A B a b) ≡ a : A :=
  have ⟨_, hA⟩ := ha.isType hΓ
  .pair_fst hA hB ha hb (.fstDF₀ hΓ (.pairDF₀ hΓ hA hB ha hb))

theorem IsDefEq.pair_snd₀ (hΓ : ⊢ Γ)
    (hB : A::Γ ⊢ B : .sort v) (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : B.inst a) :
    Γ ⊢ .snd (.pair A B a b) ≡ b : B.inst a := by
  have ⟨_, hA⟩ := ha.isType hΓ
  refine .pair_snd hA hB ha hb <| .defeqDF (hA.instDF hΓ .sort hB (.pair_fst₀ hΓ hB ha hb)) ?_
  exact .sndDF₀ hΓ (.pairDF₀ hΓ hA hB ha hb)

theorem IsDefEq.fst_snd₀ (hΓ : ⊢ Γ)
    (hp : Γ ⊢ p : .sigma A B) :
    Γ ⊢ .pair A B (.fst p) (.snd p) ≡ p : .sigma A B :=
  let ⟨_, hAB⟩ := hp.isType hΓ
  let ⟨⟨_, hA⟩, _, hB⟩ := hAB.sigma_inv' hΓ (.inl rfl)
  .fst_snd hp (.pairDF₀ hΓ hA hB (.fstDF₀ hΓ hp) (.sndDF₀ hΓ hp))

theorem lift_cons_skip_inst_succ_inst {X n : Term} :
    ((X.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0))).inst n = X.inst (.succ n) := by
  rw [inst, inst, subst_lift', subst_subst]; congr 1; funext i; obtain _|_|_ := i <;> rfl

theorem IsDefEq.natCaseDF₀ (hΓ : ⊢ Γ)
    (hC : .nat::Γ ⊢ C ≡ C' : .sort v)
    (hM : Γ ⊢ M ≡ M' : .nat)
    (ha : Γ ⊢ a ≡ a' : C.inst .zero)
    (hb : .nat::Γ ⊢ b ≡ b' : (C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0))) :
    Γ ⊢ .natCase C M a b ≡ .natCase C' M' a' b' : C.inst M :=
  .natCaseDF hC hM ha hb (.instDF hΓ .nat .sort hC hM)

theorem IsDefEq.natCase_zero₀ (hΓ : ⊢ Γ)
    (hC : .nat::Γ ⊢ C : .sort v)
    (ha : Γ ⊢ a : C.inst .zero)
    (hb : .nat::Γ ⊢ b : (C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0))) :
    Γ ⊢ .natCase C .zero a b ≡ a : C.inst .zero :=
  .natCase_zero hC ha hb (.natCaseDF₀ hΓ hC .zero ha hb)

theorem IsDefEq.natCase_succ₀ (hΓ : ⊢ Γ)
    (hC : .nat::Γ ⊢ C : .sort v)
    (hn : Γ ⊢ n : .nat)
    (ha : Γ ⊢ a : C.inst .zero)
    (hb : .nat::Γ ⊢ b : (C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0))) :
    Γ ⊢ .natCase C (.succ n) a b ≡ b.inst n : C.inst (.succ n) := by
  refine .natCase_succ hC hn ha hb (.natCaseDF₀ hΓ hC (.succDF hn) ha hb) ?_
  have h := IsDefEq.inst0 hΓ hn hb
  rwa [lift_cons_skip_inst_succ_inst] at h

theorem IsDefEq.YDF₀ (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A ≡ A' : .sort u) (hb : A::Γ ⊢ b ≡ b' : A.lift) :
    Γ ⊢ .Y A b ≡ .Y A' b' : A :=
  .YDF hA hb (.defeqDF (hA.weak' (.skip .refl)) (hA.defeqDF_l hΓ hb))

theorem IsDefEq.Y_unfold₀ (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A : .sort u) (hb : A::Γ ⊢ b : A.lift) :
    Γ ⊢ .Y A b ≡ b.inst (.Y A b) : A := by
  have hy : Γ ⊢ Term.Y A b : A := .YDF₀ hΓ hA hb
  have hbinst : Γ ⊢ b.inst (Term.Y A b) : A := by
    have := IsDefEq.inst0 hΓ hy hb
    rwa [lift_inst] at this
  exact .Y_unfold hA hb hy hbinst

theorem IsDefEq.reflDF₀ (hΓ : ⊢ Γ) (ha : Γ ⊢ a ≡ a' : A) :
    Γ ⊢ .refl a ≡ .refl a' : .id A a a :=
  let ⟨_, hA⟩ := ha.isType hΓ
  .reflDF hA ha (.idDF hA ha.hasType.1 ha.hasType.1)

theorem IsDefEq.trDF₀ (hΓ : ⊢ Γ)
    (hC : A::Γ ⊢ C ≡ C' : .sort v)
    (hx : Γ ⊢ x ≡ x' : C.inst a)
    (hh : Γ ⊢ h ≡ h' : .id A a b) :
    Γ ⊢ .tr A a b C x h ≡ .tr A a b C' x' h' : C.inst b := by
  let ⟨_, h_id_some⟩ := hh.isType hΓ
  let ⟨⟨_, hA⟩, ha, hb⟩ := h_id_some.id_inv' hΓ (.inl rfl)
  exact .trDF hA ha hb hC hC hx hh (.instDF hΓ hA .sort hC hb) (.idDF hA ha hb)

theorem IsDefEq.tr_refl₀ (hΓ : ⊢ Γ)
    (ha : Γ ⊢ a : A) (hC : A::Γ ⊢ C : .sort v) (hx : Γ ⊢ x : C.inst a) :
    Γ ⊢ .tr A a a C x (.refl a) ≡ x : C.inst a := by
  let ⟨_, hA⟩ := ha.isType hΓ
  have h_id_aa : Γ ⊢ .id A a a : .type := .idDF hA ha ha
  exact .tr_refl hA ha hC hx
    (.trDF hA ha ha hC hC hx (.reflDF hA ha h_id_aa) (.instDF hΓ hA .sort hC ha) h_id_aa)

scoped notation:65 e1 " ⤳ " e2:36 => WHRed e1 e2
/-- Single-step weak-head reduction `Γ ⊢ e ⤳ e'`. Only the head position is
reduced: either β-reduce a `lam`-headed application, or recurse on the
function side of an `app`. Right-context-indexed for uniformity with the
typing judgment, although the rules never inspect `Γ`. -/
inductive WHRed : Term → Term → Prop where
  | app : f ⤳ f' → .app f a ⤳ .app f' a
  | beta : .app (.lam A e) a ⤳ e.inst a
  | fst : p ⤳ p' → .fst p ⤳ .fst p'
  | snd : p ⤳ p' → .snd p ⤳ .snd p'
  | pair_fst : .fst (.pair A B a b) ⤳ a
  | pair_snd : .snd (.pair A B a b) ⤳ b
  | natCase : M ⤳ M' → .natCase C M a b ⤳ .natCase C M' a b
  | natCase_zero : .natCase C .zero a b ⤳ a
  | natCase_succ : .natCase C (.succ n) a b ⤳ b.inst n
  | Y : .Y A b ⤳ b.inst (.Y A b)
  | tr : h ⤳ h' → .tr A a b C x h ⤳ .tr A a b C x h'
  | tr_refl : .tr A a b C x (.refl y) ⤳ x

/-- `WHNF e` says `e` is in weak head-normal form: no `⤳` step applies. -/
def WHNF (e : Term) := ∀ e', ¬e ⤳ e'

theorem WHNF.sort : WHNF (.sort A) := nofun
theorem WHNF.unit : WHNF (.unit r) := nofun
theorem WHNF.star : WHNF (.star r) := nofun
theorem WHNF.forallE : WHNF (.forallE A B) := nofun
theorem WHNF.sigma : WHNF (.sigma A B) := nofun
theorem WHNF.nat : WHNF .nat := nofun
theorem WHNF.zero : WHNF .zero := nofun
theorem WHNF.succ : WHNF (.succ n) := nofun
theorem WHNF.id : WHNF (.id A a b) := nofun
theorem WHNF.refl : WHNF (.refl a) := nofun

theorem WHRed.determ (H1 : e ⤳ e₁) (H2 : e ⤳ e₂) : e₁ = e₂ := by
  induction H1 generalizing e₂ with
  | app h1 ih => cases H2 with | app h2 => congr 1; exact ih h2 | beta => cases h1
  | beta => cases H2 with | app h2 => cases h2 | beta => rfl
  | fst h1 ih => cases H2 with | fst h2 => congr 1; exact ih h2 | pair_fst => cases h1
  | snd h1 ih => cases H2 with | snd h2 => congr 1; exact ih h2 | pair_snd => cases h1
  | pair_fst => cases H2 with | fst h2 => cases h2 | pair_fst => rfl
  | pair_snd => cases H2 with | snd h2 => cases h2 | pair_snd => rfl
  | natCase h1 ih => cases H2 with
    | natCase h2 => congr 1; exact ih h2
    | natCase_zero => cases h1
    | natCase_succ => cases h1
  | natCase_zero => cases H2 with | natCase h2 => cases h2 | natCase_zero => rfl
  | natCase_succ => cases H2 with | natCase h2 => cases h2 | natCase_succ => rfl
  | Y => let .Y := H2; rfl
  | tr h1 ih => cases H2 with | tr h2 => congr 1; exact ih h2 | tr_refl => cases h1
  | tr_refl => cases H2 with | tr h2 => cases h2 | tr_refl => rfl

/-- Multi-step weak-head reduction: the reflexive-transitive closure of `WHRed`. -/
def WHRedS : Term → Term → Prop := ReflTransGen WHRed
scoped notation:65 e1 " ⤳* " e2:36 => WHRedS e1 e2

theorem WHRedS.app (H : e1 ⤳* e2) : e1.app a ⤳* e2.app a := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih h2.app

theorem WHRedS.fst (H : e1 ⤳* e2) : .fst e1 ⤳* .fst e2 := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih h2.fst

theorem WHRedS.snd (H : e1 ⤳* e2) : .snd e1 ⤳* .snd e2 := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih h2.snd

theorem WHRedS.natCase (H : M ⤳* M') :
    Term.natCase C M a b ⤳* Term.natCase C M' a b := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih h2.natCase

theorem WHRedS.tr (H : e1 ⤳* e2) : Term.tr A a b C x e1 ⤳* Term.tr A a b C x e2 := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih h2.tr

theorem WHRedS.determ_l (H1 : e ⤳* e₁) (H2 : e ⤳* e₂) (W2 : WHNF e₂) : e₁ ⤳* e₂ := by
  induction H1 using ReflTransGen.headIndOn generalizing e₂ with | rfl => exact H2 | head l1 l2 ih
  cases H2 using ReflTransGen.headIndOn with | rfl => cases W2 _ l1 | head r1 r2
  cases l1.determ r1; exact ih r2 W2

theorem WHNF.whRedS (W : WHNF e) (H : e ⤳* e') : e = e' := by
  cases H using ReflTransGen.headIndOn with
  | rfl => rfl
  | head h1 => cases W _ h1

theorem WHRedS.determ
    (H1 : e ⤳* e₁) (W1 : WHNF e₁)
    (H2 : e ⤳* e₂) (W2 : WHNF e₂) : e₁ = e₂ := W1.whRedS (H1.determ_l H2 W2)
