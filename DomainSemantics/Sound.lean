import DomainSemantics.Term
import DomainSemantics.Shape

/-! # Semantic interpretation and soundness

This file bridges `Term` and `Shape`: it defines what it means for a
shape to interpret a term, and packages the data needed to state the
soundness theorem for `IsDefEq`.

* `Valuation := Nat → TShape` assigns a shape to each free variable.
* `LE_Interp ρ m M` is the *interpretation relation*: shape `m` is a
  lower bound on an interpretation of term `M` under valuation `ρ`. It
  is monotone in `m` and the structure of `M`.
* `Valuation.Fits Γ Δ ρ` says `ρ` realises a semantic substitution from
  `Δ` into `Γ`, with saturation hypotheses on each domain type.
* `InterpTyped ρ m M A` is the saturated form: there are witnesses
  `m'`, `a` interpreting `M`, `A` with `m ≤ m'` and `m'.HasType a`.
* `SoundEq Γ M N` / `SoundTy Γ M A` collect these as predicates on
  judgments; `StrongSound` and `StrongSoundEq` are the mutual fixed
  point used to express soundness inductively over the term structure.

The actual soundness theorem `LE_Interp.sound` (mid-file) is the main
output: every `IsDefEq` derivation produces both an iff on `M`/`N` and a
saturated `InterpTyped`. -/

namespace DomainSemantics

/-- A valuation assigns each de Bruijn index a `TShape`. Used to interpret
the free variables of a term in the logical-relation domain. -/
def Valuation := Nat → TShape

/-- The empty valuation: every index maps to `(0, .bot)`. -/
def Valuation.nil : Valuation := fun _ => ⟨0, .bot⟩
/-- Push a new value onto the front of a valuation (under-binder extension). -/
def Valuation.push (ρ : Valuation) (u : TShape) : Valuation
  | 0 => u
  | n+1 => ρ n

/-- Pointwise order on valuations. -/
def Valuation.LE (ρ ρ' : Valuation) : Prop := ∀ n, ρ n ≤ ρ' n

theorem Valuation.LE.rfl {ρ : Valuation} : ρ.LE ρ := fun _ => .rfl

theorem Valuation.LE.push {ρ ρ' : Valuation} :
    (ρ.push a).LE (ρ'.push a') ↔ ρ.LE ρ' ∧ a ≤ a' :=
  ⟨fun H => ⟨fun _ => H (_+1), H 0⟩, fun ⟨H1, H2⟩ => fun | 0 => H2 | _+1 => H1 _⟩

/-- Two valuations are compatible if their entries are compatible at each index
(after lifting to a common level). -/
def Valuation.Compat (ρ₁ ρ₂ : Valuation) : Prop := ∀ i, (ρ₁ i).Compat (ρ₂ i)

/-- Pointwise join of two valuations. Each entry is lifted to a common level and joined. -/
def Valuation.join (ρ₁ ρ₂ : Valuation) : Valuation := fun i => (ρ₁ i).join (ρ₂ i)

theorem Valuation.Compat.le_join {ρ₁ ρ₂ : Valuation}
    (hc : ρ₁.Compat ρ₂) : ρ₁.LE (ρ₁.join ρ₂) ∧ ρ₂.LE (ρ₁.join ρ₂) :=
  ⟨fun i => (TShape.Join.mk (hc i)).le.1, fun i => (TShape.Join.mk (hc i)).le.2⟩

/-- The semantic interpretation relation: `LE_Interp ρ m M` says that the
type-shape `m` is below an interpretation of the term `M` under valuation
`ρ`. Reading `m` as a *lower bound* makes the relation monotone in `m`
(see `LE_Interp.mono`). The five constructors mirror the term syntax
(`bvar`, `sort`, `app`, `lam`, `forallE`) plus a `bot` rule that always
succeeds at the bottom shape. -/
inductive LE_Interp : Valuation → TShape → Term → Prop
  | bot : LE_Interp ρ (WShape.T (n := n) .bot) M
  | bvar : m ≤ ρ i → LE_Interp ρ m (.bvar i)
  | sort : m ≤ .sort l → LE_Interp ρ m (.sort l)
  | unit : m ≤ .unit r → LE_Interp ρ m (.unit r)
  | app : LE_Interp ρ (WShape.T f) F → LE_Interp ρ a.T A →
    m ≤ (f.app a).T → LE_Interp ρ m (.app F A)
  | lam : LE_Interp ρ (WShape.T (n := n) a) A →
    WShape.HasDom f a → (∀ x, x.HasType a → LE_Interp (ρ.push x.T) (f.app x).T F) →
    m ≤ WShape.T (n := _+1) (.lam' f) → LE_Interp ρ m (.lam A F)
  | forallE : LE_Interp ρ (WShape.T (n := n) b) B → LE_Interp ρ (WShape.T (n := n) b') B →
    WShape.HasDom f b' → (∀ x, x.HasType b' → LE_Interp (ρ.push x.T) (f.app x).T F) →
    m ≤ WShape.T (n := n+1) (.forallE b f) → LE_Interp ρ m (.forallE B F)
  | sigma : LE_Interp ρ (WShape.T (n := n) b) B → LE_Interp ρ (WShape.T (n := n) b') B →
    WShape.HasDom f b' → (∀ x, x.HasType b' → LE_Interp (ρ.push x.T) (f.app x).T F) →
    m ≤ WShape.T (n := n+1) (.sigma b f) → LE_Interp ρ m (.sigma B F)
  | pair {xV yV : WShape n} :
    LE_Interp ρ (WShape.T xV) X →
    LE_Interp ρ (WShape.T yV) Y →
    m ≤ WShape.T (n := n+1) (.pair' xV yV) →
    LE_Interp ρ m (.pair A B X Y)
  | fst {s : WShape (n+1)} : LE_Interp ρ s.T P →
    m ≤ (WShape.fst s).T → LE_Interp ρ m (.fst P)
  | snd {s : WShape (n+1)} : LE_Interp ρ s.T P →
    m ≤ (WShape.snd s).T → LE_Interp ρ m (.snd P)
  | nat : m ≤ (.nat : WShape (n+1)).T → LE_Interp ρ m .nat
  | zero : m ≤ (.zero : WShape (n+1)).T → LE_Interp ρ m .zero
  | succ : LE_Interp ρ v.T N → m ≤ (.succ v : WShape (n+1)).T → LE_Interp ρ m (.succ N)
  | natCase_zero : LE_Interp ρ (.zero : WShape (n+1)).T M →
    LE_Interp ρ m a → LE_Interp ρ m (.natCase C M a b)
  | natCase_succ : LE_Interp ρ (.succ v : WShape (n+1)).T M →
    LE_Interp (ρ.push v.T) m b → LE_Interp ρ m (.natCase C M a b)
  | protected Y {s : TShape} : LE_Interp (ρ.push s) m b → LE_Interp ρ s (.Y A b) →
    LE_Interp ρ m (.Y A b)
  | id : LE_Interp ρ AV.T A → LE_Interp ρ aV.T a → LE_Interp ρ bV.T b →
    m ≤ WShape.T (n := n+1) (.id AV aV bV) → LE_Interp ρ m (.id A a b)
  | refl {v : WShape n} : LE_Interp ρ v.T a →
    m ≤ WShape.T (n := n+1) (.refl v) → LE_Interp ρ m (.refl a)
  | tr {v vA m' cb : TShape} : m ≤ m' → LE_Interp ρ m' X →
    LE_Interp ρ v a → LE_Interp ρ v b →
    LE_Interp ρ vA A → v.HasType vA →
    LE_Interp (ρ.push v) cb C → m'.HasType cb →
    LE_Interp ρ (WShape.refl v.2).T H →
    LE_Interp ρ m (.tr A a b C X H)

theorem LE_Interp.bvar' : LE_Interp ρ (ρ i) (.bvar i) := .bvar .rfl
theorem LE_Interp.bvar0 : LE_Interp (.push ρ x) x (.bvar 0) := .bvar' (ρ := ρ.push x) (i := 0)
theorem LE_Interp.sort' : LE_Interp ρ (.sort l) (.sort l) := .sort .rfl
theorem LE_Interp.unit' : LE_Interp ρ (.unit r) (.unit r) := .unit .rfl
theorem LE_Interp.app' (h1 : LE_Interp ρ (WShape.T f) F) (h2 : LE_Interp ρ a.T A) :
    LE_Interp ρ (f.app a).T (.app F A) := .app h1 h2 .rfl
theorem LE_Interp.lam' {f : WShapeFun n} {a : WShape n}
    (h1 : LE_Interp ρ (WShape.T a) A) (h2 : WShape.HasDom f a)
    (h3 : ∀ x, x.HasType a → LE_Interp (ρ.push x.T) (f.app x).T F) :
    LE_Interp ρ (WShape.T (n := n+1) (WShape.lam' f)) (.lam A F) := .lam h1 h2 h3 .rfl
theorem LE_Interp.forallE' {f : WShapeFun n} {b b' : WShape n}
    (h1 : LE_Interp ρ b.T B) (h2 : LE_Interp ρ b'.T B) (h3 : WShape.HasDom f b')
    (h4 : ∀ x, x.HasType b' → LE_Interp (ρ.push x.T) (f.app x).T F) :
    LE_Interp ρ (WShape.T (n := n+1) (.forallE b f)) (.forallE B F) := .forallE h1 h2 h3 h4 .rfl
theorem LE_Interp.sigma' {f : WShapeFun n} {b b' : WShape n}
    (h1 : LE_Interp ρ b.T B) (h2 : LE_Interp ρ b'.T B) (h3 : WShape.HasDom f b')
    (h4 : ∀ x, x.HasType b' → LE_Interp (ρ.push x.T) (f.app x).T F) :
    LE_Interp ρ (WShape.T (n := n+1) (.sigma b f)) (.sigma B F) := .sigma h1 h2 h3 h4 .rfl
theorem LE_Interp.pair' {xV yV : WShape n}
    (h1 : LE_Interp ρ xV.T X) (h2 : LE_Interp ρ yV.T Y) :
    LE_Interp ρ (WShape.T (n := n+1) (.pair' xV yV)) (.pair A B X Y) :=
  .pair h1 h2 .rfl
theorem LE_Interp.fst' {s : WShape (n+1)} (h : LE_Interp ρ s.T P) :
    LE_Interp ρ (WShape.fst s).T (.fst P) := .fst h .rfl
theorem LE_Interp.snd' {s : WShape (n+1)} (h : LE_Interp ρ s.T P) :
    LE_Interp ρ (WShape.snd s).T (.snd P) := .snd h .rfl
theorem LE_Interp.nat' : LE_Interp ρ (WShape.nat : WShape (n+1)).T .nat := .nat .rfl
theorem LE_Interp.zero' : LE_Interp ρ (WShape.zero : WShape (n+1)).T .zero := .zero .rfl
theorem LE_Interp.succ' {v : WShape n} (h : LE_Interp ρ v.T N) :
    LE_Interp ρ (WShape.succ v : WShape (n+1)).T (.succ N) := .succ h .rfl

theorem LE_Interp.bvar_iff : LE_Interp ρ m (.bvar i) ↔ m ≤ ρ i :=
  ⟨fun | .bot => TShape.bot_le' | .bvar h => h, .bvar⟩

theorem LE_Interp.le_sort (H : LE_Interp ρ m (.sort u)) : m ≤ .sort u := by
  generalize eq : Term.sort u = M at H
  induction H with cases eq
  | bot => exact TShape.bot_le'
  | sort h => exact h.trans TShape.sort_eqv.1

theorem LE_Interp.le_nat (H : LE_Interp ρ m .nat) :
    ∃ n, m ≤ (WShape.nat : WShape (n+1)).T := by
  cases H with | bot => exact ⟨0, TShape.bot_le'⟩ | nat h => exact ⟨_, h⟩

theorem LE_Interp.le_zero (H : LE_Interp ρ m .zero) :
    ∃ n, m ≤ (WShape.zero : WShape (n+1)).T := by
  cases H with | bot => exact ⟨0, TShape.bot_le'⟩ | zero h => exact ⟨_, h⟩

theorem LE_Interp.le_succ (H : LE_Interp ρ m (.succ N)) :
    ∃ n, ∃ v : WShape n, LE_Interp ρ v.T N ∧ m ≤ (WShape.succ v : WShape (n+1)).T := by
  cases H with | bot => exact ⟨0, .bot, .bot, TShape.bot_le'⟩ | succ hv h1 => exact ⟨_, _, hv, h1⟩

theorem LE_Interp.le_sort' (H : LE_Interp ρ m (.sort u)) : m.2 ≤ .sort u :=
  (TShape.LE.lift_r (Nat.zero_le _)).1 H.le_sort

theorem LE_Interp.le_unit (H : LE_Interp ρ m (.unit r)) : m ≤ .unit r := by
  generalize eq : Term.unit r = M at H
  induction H with cases eq
  | bot => exact TShape.bot_le'
  | unit h => exact h.trans TShape.unit_eqv.1

theorem LE_Interp.mono (h : m ≤ m') (H : LE_Interp ρ m' M) : LE_Interp ρ m M := by
  induction H generalizing m with
  | bot => exact TShape.le_bot'.1 (h.trans TShape.bot_eqv.1) ▸ .bot
  | bvar h1 => exact .bvar (h.trans h1)
  | sort h1 => exact .sort (h.trans h1)
  | unit h1 => exact .unit (h.trans h1)
  | app hf ha h1 => exact .app hf ha (h.trans h1)
  | lam ha hdom hbody h1 => exact .lam ha hdom hbody (h.trans h1)
  | forallE hb hb' hdom hbody h1 => exact .forallE hb hb' hdom hbody (h.trans h1)
  | sigma hb hb' hdom hbody h1 => exact .sigma hb hb' hdom hbody (h.trans h1)
  | pair hX hY h1 => exact .pair hX hY (h.trans h1)
  | fst hP h1 => exact .fst hP (h.trans h1)
  | snd hP h1 => exact .snd hP (h.trans h1)
  | nat h1 => exact .nat (h.trans h1)
  | zero h1 => exact .zero (h.trans h1)
  | succ hv h1 => exact .succ hv (h.trans h1)
  | natCase_zero hM ha _ iha => exact .natCase_zero hM (iha h)
  | natCase_succ hM hb _ ihb => exact .natCase_succ hM (ihb h)
  | Y ih_body ih_self ihb ihs => exact .Y (ihb h) ih_self
  | id hA ha hb h1 => exact .id hA ha hb (h.trans h1)
  | refl hv h1 => exact .refl hv (h.trans h1)
  | tr le hx' hva hvb hvA hv_ty_vA hc_C hty hH_refl _ _ _ _ _ _ =>
    exact .tr (h.trans le) hx' hva hvb hvA hv_ty_vA hc_C hty hH_refl

theorem LE_Interp.mono_l (hρ : ρ.LE ρ') (H : LE_Interp ρ m M) : LE_Interp ρ' m M := by
  induction H generalizing ρ' with
  | bot => exact .bot
  | bvar h1 => exact .bvar (h1.trans (hρ _))
  | sort h1 => exact .sort h1
  | unit h1 => exact .unit h1
  | app _ _ h1 ih_f ih_a => exact .app (ih_f hρ) (ih_a hρ) h1
  | lam _ hdom _ h1 ih_a ih_body =>
    exact .lam (ih_a hρ) hdom (fun x hx => ih_body x hx (Valuation.LE.push.2 ⟨hρ, .rfl⟩)) h1
  | forallE _ _ hdom _ h1 ih_b ih_b' ih_body =>
    refine .forallE (ih_b hρ) (ih_b' hρ) hdom ?_ h1
    exact fun x hx => ih_body x hx (Valuation.LE.push.2 ⟨hρ, .rfl⟩)
  | sigma _ _ hdom _ h1 ih_b ih_b' ih_body =>
    refine .sigma (ih_b hρ) (ih_b' hρ) hdom ?_ h1
    exact fun x hx => ih_body x hx (Valuation.LE.push.2 ⟨hρ, .rfl⟩)
  | pair _ _ h1 ih_X ih_Y => exact .pair (ih_X hρ) (ih_Y hρ) h1
  | fst _ h1 ih => exact .fst (ih hρ) h1
  | snd _ h1 ih => exact .snd (ih hρ) h1
  | nat h1 => exact .nat h1
  | zero h1 => exact .zero h1
  | succ _ h1 ihv => exact .succ (ihv hρ) h1
  | natCase_zero hM ha ihM iha => exact .natCase_zero (ihM hρ) (iha hρ)
  | natCase_succ hM hb ihM ihb => exact .natCase_succ (ihM hρ) (ihb (Valuation.LE.push.2 ⟨hρ, .rfl⟩))
  | Y ih_body ih_self ihb ihs => exact .Y (ihb (Valuation.LE.push.2 ⟨hρ, .rfl⟩)) (ihs hρ)
  | id _ _ _ h1 ihA iha ihb => exact .id (ihA hρ) (iha hρ) (ihb hρ) h1
  | refl _ h1 ihv => exact .refl (ihv hρ) h1
  | tr le _ _ _ _ hv_ty_vA _ hty _ ihx ihva ihvb ihvA ihc_C ihH =>
    refine .tr le (ihx hρ) (ihva hρ) (ihvb hρ) (ihvA hρ) hv_ty_vA ?_ hty (ihH hρ)
    exact ihc_C (Valuation.LE.push.2 ⟨hρ, .rfl⟩)

theorem LE_Interp.unlift (le : m.1 ≤ n)
    (H : LE_Interp ρ (m.2.lift n).T M) : LE_Interp ρ m M := H.mono (TShape.lift_eqv le).2

theorem LE_Interp.lift (le : m.1 ≤ n)
    (H : LE_Interp ρ m M) : LE_Interp ρ (m.2.lift n).T M := H.mono (TShape.lift_eqv le).1

theorem LE_Interp.weak'_iff (l : Lift) (h : ∀ i, ρ i = ρ' (l.liftVar i)) :
    LE_Interp ρ' m (M.lift' l) ↔ LE_Interp ρ m M := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · generalize eq : M.lift' l = M' at H
    induction H generalizing M ρ l with first
      | subst eq | cases M <;> cases eq
    | bot => exact .bot
    | sort h1 => exact .sort h1
    | unit h1 => exact .unit h1
    | bvar h1 => exact .bvar (h _ ▸ h1)
    | app _ _ h1 ih_f ih_a => exact .app (ih_f _ h rfl) (ih_a _ h rfl) h1
    | lam _ hdom _ h1 ih_a ih_body =>
      refine .lam (ih_a _ h rfl) hdom (fun y hy => ?_) h1
      exact ih_body y hy _ (fun i => by cases i <;> simp [Valuation.push, h]) rfl
    | forallE _ _ hdom _ h1 ih_b ih_b' ih_body =>
      refine .forallE (ih_b _ h rfl) (ih_b' _ h rfl) hdom (fun y hy => ?_) h1
      exact ih_body y hy _ (fun i => by cases i <;> simp [Valuation.push, h]) rfl
    | sigma _ _ hdom _ h1 ih_b ih_b' ih_body =>
      refine .sigma (ih_b _ h rfl) (ih_b' _ h rfl) hdom (fun y hy => ?_) h1
      exact ih_body y hy _ (fun i => by cases i <;> simp [Valuation.push, h]) rfl
    | pair _ _ h1 ih_X ih_Y =>
      exact .pair (ih_X _ h rfl) (ih_Y _ h rfl) h1
    | fst _ h1 ih => exact .fst (ih _ h rfl) h1
    | snd _ h1 ih => exact .snd (ih _ h rfl) h1
    | nat h1 => exact .nat h1
    | zero h1 => exact .zero h1
    | succ _ h1 ihv => exact .succ (ihv _ h rfl) h1
    | natCase_zero hM ha ihM iha => exact .natCase_zero (ihM _ h rfl) (iha _ h rfl)
    | natCase_succ hM hb ihM ihb =>
      refine .natCase_succ (ihM _ h rfl) <| ihb _ ?_ rfl
      rintro ⟨⟩ <;> simp [Valuation.push, h]
    | Y ih_body ih_self ihb ihs => exact .Y (ihb l.cons (fun i => by cases i <;> simp [Valuation.push, h]) rfl) (ihs l h rfl)
    | id _ _ _ h1 ihA iha ihb =>
      exact .id (ihA _ h rfl) (iha _ h rfl) (ihb _ h rfl) h1
    | refl _ h1 ihv => exact .refl (ihv _ h rfl) h1
    | tr le _ _ _ _ hv_ty_vA _ hty _ ihx ihva ihvb ihvA ihc_C ihH =>
      refine .tr le (ihx _ h rfl) (ihva _ h rfl) (ihvb _ h rfl)
        (ihvA _ h rfl) hv_ty_vA ?_ hty (ihH _ h rfl)
      exact ihc_C _ (fun i => by cases i <;> simp [Valuation.push, h]) rfl
  · induction H generalizing ρ' l with
    | bot => exact .bot
    | sort h1 => exact .sort h1
    | unit h1 => exact .unit h1
    | bvar h1 => exact .bvar (h _ ▸ h1)
    | app _ _ h1 ih_f ih_a => exact .app (ih_f l h) (ih_a l h) h1
    | lam _ hdom _ h1 ih_a ih_body =>
      refine .lam (ih_a l h) hdom (fun y hy => ?_) h1
      exact ih_body y hy l.cons fun i => by cases i <;> simp [Valuation.push, h]
    | forallE _ _ hdom _ h1 ih_b ih_b' ih_body =>
      refine .forallE (ih_b l h) (ih_b' l h) hdom (fun y hy => ?_) h1
      exact ih_body y hy l.cons fun i => by cases i <;> simp [Valuation.push, h]
    | sigma _ _ hdom _ h1 ih_b ih_b' ih_body =>
      refine .sigma (ih_b l h) (ih_b' l h) hdom (fun y hy => ?_) h1
      exact ih_body y hy l.cons fun i => by cases i <;> simp [Valuation.push, h]
    | pair _ _ h1 ih_X ih_Y =>
      exact .pair (ih_X l h) (ih_Y l h) h1
    | fst _ h1 ih => exact .fst (ih l h) h1
    | snd _ h1 ih => exact .snd (ih l h) h1
    | nat h1 => exact .nat h1
    | zero h1 => exact .zero h1
    | succ _ h1 ihv => exact .succ (ihv l h) h1
    | natCase_zero hM ha ihM iha => exact .natCase_zero (ihM l h) (iha l h)
    | natCase_succ hM hb ihM ihb =>
      refine .natCase_succ (ihM l h) <| ihb l.cons ?_
      rintro ⟨⟩ <;> simp [Valuation.push, h]
    | Y ih_body ih_self ihb ihs => exact .Y (ihb l.cons (fun i => by cases i <;> simp [Valuation.push, h])) (ihs l h)
    | id _ _ _ h1 ihA iha ihb =>
      exact .id (ihA l h) (iha l h) (ihb l h) h1
    | refl _ h1 ihv => exact .refl (ihv l h) h1
    | tr le _ _ _ _ hv_ty_vA _ hty _ ihx ihva ihvb ihvA ihc_C ihH =>
      refine .tr le (ihx l h) (ihva l h) (ihvb l h) (ihvA l h) hv_ty_vA ?_ hty (ihH l h)
      exact ihc_C l.cons fun i => by cases i <;> simp [Valuation.push, h]

theorem LE_Interp.weak_iff : LE_Interp (ρ.push x) m M.lift ↔ LE_Interp ρ m M :=
  LE_Interp.weak'_iff (.skip .refl) (fun _ => rfl)

theorem LE_Interp.weak (H : LE_Interp ρ m M) : LE_Interp (ρ.push x) m M.lift :=
  weak_iff.2 H

theorem LE_Interp.compat_join {m₁ m₂ : TShape}
    (hρ : ρ'.LE ρ) (H1 : LE_Interp ρ' m₁ M) (H2 : LE_Interp ρ m₂ M) :
    m₁.Compat m₂ ∧ LE_Interp ρ (m₁.join m₂) M := by
  have mk {m₁ m₂ m ρ M} (H1 : m₁ ≤ m) (H2 : m₂ ≤ m) (H : LE_Interp ρ m M) :
      m₁.Compat m₂ ∧ LE_Interp ρ (m₁.join m₂) M :=
    have := TShape.Compat.def'.2 ⟨_, H1, H2⟩
    ⟨this, H.mono ((TShape.Join.mk this _).2 ⟨H1, H2⟩)⟩
  have bot_r {m₁ n₂ ρ' ρ M} (hρ : ρ'.LE ρ) (H : LE_Interp ρ' m₁ M) :
      m₁.Compat (WShape.bot (n := n₂)).T ∧ LE_Interp ρ (m₁.join (WShape.bot (n := n₂)).T) M :=
    mk .rfl TShape.bot_le' (H.mono_l hρ)
  induction H1 generalizing ρ m₂ with
  | bot => exact mk TShape.bot_le' .rfl H2
  | sort h1 =>
    cases H2 with | bot => exact bot_r hρ (.sort h1) | sort h2
    exact mk h1 (h2.trans TShape.sort_eqv.2) (.sort .rfl)
  | unit h1 =>
    cases H2 with | bot => exact bot_r hρ (.unit h1) | unit h2
    exact mk h1 (h2.trans TShape.unit_eqv.2) (.unit .rfl)
  | bvar h1 =>
    cases H2 with | bot => exact bot_r hρ (.bvar h1) | bvar h2
    exact mk (h1.trans (hρ _)) h2 .bvar'
  | app hf ha h1 ih_f ih_a =>
    cases H2 with | bot => exact bot_r hρ (.app hf ha h1) | app hf' ha' h1'
    have ⟨cf, jf⟩ := ih_f hρ hf'
    have ⟨ca, ja⟩ := ih_a hρ ha'
    have hf := (TShape.Join.mk cf).le
    have ha := (TShape.Join.mk ca).le
    refine have le' := Nat.add_max_add_right .. ▸ Nat.le_refl _; mk ?_ ?_ ((jf.lift le').app' ja)
    · exact h1.trans <| TShape.app_mono (hf.1.trans (TShape.lift_eqv le').2) ha.1
    · exact h1'.trans <| TShape.app_mono (hf.2.trans (TShape.lift_eqv le').2) ha.2
  | lam ha hdom he h1 ih_a ih_f =>
    cases H2 with | bot => exact bot_r hρ (.lam ha hdom he h1) | lam ha' hdom' he' h1'
    rename_i ρ n₁ a₁ A f₁ F m₁ n₂ a₂ f₂
    have ⟨ca, ia⟩ := ih_a hρ ha'
    have hC {x₁ y₁ x₂ y₂} (h1 : (x₁, y₁) ∈ f₁) (h2 : (x₂, y₂) ∈ f₂) (hc : x₁.T.Compat x₂.T) :
        y₁.T.Compat y₂.T ∧ LE_Interp (ρ.push (x₁.T.join x₂.T)) (y₁.T.join y₂.T) F := by
      have ⟨j1, j2⟩ := (TShape.Join.mk hc).le
      have ⟨x'₁, hx1_le, hx1, happ1⟩ := WShape.HasDom.iff.1 hdom x₁
      have ⟨x'₂, hx2_le, hx2, happ2⟩ := WShape.HasDom.iff.1 hdom' x₂
      have hi1 := (he x'₁ hx1).mono (WShape.LE.T happ1)
        |>.mono_l (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j1⟩)
      have hi2 := (he' x'₂ hx2).mono (WShape.LE.T happ2)
        |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hx2_le.T.trans j2⟩)
      have ⟨hc', hle'⟩ := ih_f x'₁ hx1 (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j1⟩) hi2
      refine mk ?_ ?_ hle'
      · exact (WShapeFun.app_of_mem h1).2.T.trans happ1.T |>.trans (TShape.Join.mk hc').le.1
      · exact (WShapeFun.app_of_mem h2).2.T.trans (TShape.Join.mk hc').le.2
    have le₁ := Nat.le_max_left n₁ n₂; have le₂ := Nat.le_max_right n₁ n₂
    have cf : WShapeFun.Compat (f₁.lift (max n₁ n₂)) (f₂.lift (max n₁ n₂)) := by
      simp only [WShapeFun.Compat.def, Prod.forall, le₂, WShapeFun.mem_lift, le₁]
      rintro _ _ ⟨x₁, y₁, h1, rfl, rfl⟩ _ _ ⟨x₂, y₂, h2, rfl, rfl⟩ hc; exact (hC h1 h2 hc).1
    have jf := WShapeFun.Join.mk cf
    have hdom := (WShape.HasDom.lift le₁).2 hdom
    have hdom' := (WShape.HasDom.lift le₂).2 hdom'
    have ca_w : WShape.Compat (a₁.lift _) (a₂.lift _) := (TShape.Compat.def le₁ le₂).1 ca
    refine mk (h1.trans ?_) (h1'.trans ?_) <| .lam' ia (hdom.join cf ca_w hdom') fun x hx => ?_
    · exact (TShape.LE.lift_l (Nat.succ_le_succ le₁)).2 <|
        WShape.lift_lam' le₁ ▸ WShape.lam'_le_lam'.2 jf.le.1
    · exact (TShape.LE.lift_l (Nat.succ_le_succ le₂)).2 <|
        WShape.lift_lam' le₂ ▸ WShape.lam'_le_lam'.2 jf.le.2
    have ⟨x₁', a1, a2'⟩ := WShapeFun.app_eq (f₁.lift _) x
    have ⟨x₂', b1, b2'⟩ := WShapeFun.app_eq (f₂.lift _) x
    have ⟨ox₁, oy₁, hm₁, hx₁eq, hy₁eq⟩ := (WShapeFun.mem_lift le₁).1 a2'
    have ⟨ox₂, oy₂, hm₂, hx₂eq, hy₂eq⟩ := (WShapeFun.mem_lift le₂).1 b2'
    have a1' : ox₁.T ≤ x.T := ((TShape.LE.lift_l le₁).2 .rfl).trans (hx₁eq ▸ a1).T
    have b1' : ox₂.T ≤ x.T := ((TShape.LE.lift_l le₂).2 .rfl).trans (hx₂eq ▸ b1).T
    have hc := TShape.Compat.def'.2 ⟨x.T, a1', b1'⟩
    have ⟨_, hj⟩ := hC hm₁ hm₂ hc
    refine hj.mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.Join.mk hc x.T).2 ⟨a1', b1'⟩⟩) |>.mono ?_
    have ja := hy₁eq ▸ hy₂eq ▸ jf.app_l x
    have oy_c := WShape.Compat.iff.2 ⟨_, ja.le.1, ja.le.2⟩
    exact (ja _).2 (WShape.Join.mk oy_c).le |>.T
  | forallE hb ha hdom he h1 ih_b ih_a ih_f =>
    cases H2 with
    | bot => exact bot_r hρ (.forallE hb ha hdom he h1) | forallE hb2 ha2 hdom2 he2 h12
    rename_i ρ n₁ b₁ B b₁' f₁ F m₁ n₂ b₂ b₂' f₂
    have ⟨cb, ib⟩ := ih_b hρ hb2
    have ⟨ca, ia⟩ := ih_a hρ ha2
    have hC {x₁ y₁ x₂ y₂} (h1 : (x₁, y₁) ∈ f₁) (h2 : (x₂, y₂) ∈ f₂) (hc : x₁.T.Compat x₂.T) :
        y₁.T.Compat y₂.T ∧ LE_Interp (ρ.push (x₁.T.join x₂.T)) (y₁.T.join y₂.T) F := by
      have ⟨j1, j2⟩ := (TShape.Join.mk hc).le
      have ⟨x'₁, hx1_le, hx1, happ1⟩ := WShape.HasDom.iff.1 hdom x₁
      have ⟨x'₂, hx2_le, hx2, happ2⟩ := WShape.HasDom.iff.1 hdom2 x₂
      have hi1 := (he x'₁ hx1).mono (WShape.LE.T happ1)
        |>.mono_l (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j1⟩)
      have hi2 := (he2 x'₂ hx2).mono (WShape.LE.T happ2)
        |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hx2_le.T.trans j2⟩)
      have ⟨hc', hle'⟩ := ih_f x'₁ hx1 (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j1⟩) hi2
      exact mk ((WShapeFun.app_of_mem h1).2.T.trans happ1.T |>.trans (TShape.Join.mk hc').le.1)
        ((WShapeFun.app_of_mem h2).2.T.trans (TShape.Join.mk hc').le.2) hle'
    have le₁ := Nat.le_max_left n₁ n₂; have le₂ := Nat.le_max_right n₁ n₂
    have cf : (f₁.lift (max n₁ n₂)).Compat (f₂.lift (max n₁ n₂)) := by
      simp only [WShapeFun.Compat.def, Prod.forall, le₂, WShapeFun.mem_lift, le₁]
      rintro _ _ ⟨x₁, y₁, h1, rfl, rfl⟩ _ _ ⟨x₂, y₂, h2, rfl, rfl⟩ hc; exact (hC h1 h2 hc).1
    have cb_w := (TShape.Compat.def le₁ le₂).1 cb
    have jb := WShape.Join.mk cb_w; have jf := WShapeFun.Join.mk cf
    have hdom := (WShape.HasDom.lift le₁).2 hdom
    have hdom2 := (WShape.HasDom.lift le₂).2 hdom2
    have ca_w := (TShape.Compat.def le₁ le₂).1 ca
    refine mk (h1.trans ?_) (h12.trans ?_) <|
      .forallE' ib ia (hdom.join cf ca_w hdom2) fun x hx => ?_
    · refine (TShape.LE.lift_l (Nat.succ_le_succ le₁)).2 ?_
      exact WShape.lift_forallE le₁ ▸ WShape.forallE_le_forallE.2 ⟨jb.le.1, jf.le.1⟩
    · refine (TShape.LE.lift_l (Nat.succ_le_succ le₂)).2 ?_
      exact WShape.lift_forallE le₂ ▸ WShape.forallE_le_forallE.2 ⟨jb.le.2, jf.le.2⟩
    have ⟨x₁', a1, a2'⟩ := WShapeFun.app_eq (f₁.lift _) x
    have ⟨x₂', b1, b2'⟩ := WShapeFun.app_eq (f₂.lift _) x
    have ⟨ox₁, oy₁, hm₁, hx₁eq, hy₁eq⟩ := (WShapeFun.mem_lift le₁).1 a2'
    have ⟨ox₂, oy₂, hm₂, hx₂eq, hy₂eq⟩ := (WShapeFun.mem_lift le₂).1 b2'
    have a1' : ox₁.T ≤ x.T := ((TShape.LE.lift_l le₁).2 .rfl).trans (hx₁eq ▸ a1).T
    have b1' : ox₂.T ≤ x.T := ((TShape.LE.lift_l le₂).2 .rfl).trans (hx₂eq ▸ b1).T
    have hc := TShape.Compat.def'.2 ⟨x.T, a1', b1'⟩
    have ⟨_, hj⟩ := hC hm₁ hm₂ hc
    refine hj.mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.Join.mk hc x.T).2 ⟨a1', b1'⟩⟩) |>.mono ?_
    have ja := hy₁eq ▸ hy₂eq ▸ jf.app_l x
    exact (ja _).2 (WShape.Join.mk <| WShape.Compat.iff.2 ⟨_, ja.le.1, ja.le.2⟩).le |>.T
  | sigma hb ha hdom he h1 ih_b ih_a ih_f =>
    cases H2 with
    | bot => exact bot_r hρ (.sigma hb ha hdom he h1) | sigma hb2 ha2 hdom2 he2 h12
    rename_i ρ n₁ b₁ B b₁' f₁ F m₁ n₂ b₂ b₂' f₂
    have ⟨cb, ib⟩ := ih_b hρ hb2
    have ⟨ca, ia⟩ := ih_a hρ ha2
    have hC {x₁ y₁ x₂ y₂} (h1 : (x₁, y₁) ∈ f₁) (h2 : (x₂, y₂) ∈ f₂) (hc : x₁.T.Compat x₂.T) :
        y₁.T.Compat y₂.T ∧ LE_Interp (ρ.push (x₁.T.join x₂.T)) (y₁.T.join y₂.T) F := by
      have ⟨j1, j2⟩ := (TShape.Join.mk hc).le
      have ⟨x'₁, hx1_le, hx1, happ1⟩ := WShape.HasDom.iff.1 hdom x₁
      have ⟨x'₂, hx2_le, hx2, happ2⟩ := WShape.HasDom.iff.1 hdom2 x₂
      have hi1 := (he x'₁ hx1).mono (WShape.LE.T happ1)
        |>.mono_l (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j1⟩)
      have hi2 := (he2 x'₂ hx2).mono (WShape.LE.T happ2)
        |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hx2_le.T.trans j2⟩)
      have ⟨hc', hle'⟩ := ih_f x'₁ hx1 (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j1⟩) hi2
      exact mk ((WShapeFun.app_of_mem h1).2.T.trans happ1.T |>.trans (TShape.Join.mk hc').le.1)
        ((WShapeFun.app_of_mem h2).2.T.trans (TShape.Join.mk hc').le.2) hle'
    have le₁ := Nat.le_max_left n₁ n₂; have le₂ := Nat.le_max_right n₁ n₂
    have cf : (f₁.lift (max n₁ n₂)).Compat (f₂.lift (max n₁ n₂)) := by
      simp only [WShapeFun.Compat.def, Prod.forall, le₂, WShapeFun.mem_lift, le₁]
      rintro _ _ ⟨x₁, y₁, h1, rfl, rfl⟩ _ _ ⟨x₂, y₂, h2, rfl, rfl⟩ hc; exact (hC h1 h2 hc).1
    have cb_w := (TShape.Compat.def le₁ le₂).1 cb
    have jb := WShape.Join.mk cb_w; have jf := WShapeFun.Join.mk cf
    have hdom := (WShape.HasDom.lift le₁).2 hdom
    have hdom2 := (WShape.HasDom.lift le₂).2 hdom2
    have ca_w := (TShape.Compat.def le₁ le₂).1 ca
    refine mk (h1.trans ?_) (h12.trans ?_) <|
      .sigma' ib ia (hdom.join cf ca_w hdom2) fun x hx => ?_
    · refine (TShape.LE.lift_l (Nat.succ_le_succ le₁)).2 ?_
      exact WShape.lift_sigma le₁ ▸ WShape.sigma_le_sigma.2 ⟨jb.le.1, jf.le.1⟩
    · refine (TShape.LE.lift_l (Nat.succ_le_succ le₂)).2 ?_
      exact WShape.lift_sigma le₂ ▸ WShape.sigma_le_sigma.2 ⟨jb.le.2, jf.le.2⟩
    have ⟨x₁', a1, a2'⟩ := WShapeFun.app_eq (f₁.lift _) x
    have ⟨x₂', b1, b2'⟩ := WShapeFun.app_eq (f₂.lift _) x
    have ⟨ox₁, oy₁, hm₁, hx₁eq, hy₁eq⟩ := (WShapeFun.mem_lift le₁).1 a2'
    have ⟨ox₂, oy₂, hm₂, hx₂eq, hy₂eq⟩ := (WShapeFun.mem_lift le₂).1 b2'
    have a1' : ox₁.T ≤ x.T := ((TShape.LE.lift_l le₁).2 .rfl).trans (hx₁eq ▸ a1).T
    have b1' : ox₂.T ≤ x.T := ((TShape.LE.lift_l le₂).2 .rfl).trans (hx₂eq ▸ b1).T
    have hc := TShape.Compat.def'.2 ⟨x.T, a1', b1'⟩
    have ⟨_, hj⟩ := hC hm₁ hm₂ hc
    refine hj.mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.Join.mk hc x.T).2 ⟨a1', b1'⟩⟩) |>.mono ?_
    have ja := hy₁eq ▸ hy₂eq ▸ jf.app_l x
    exact (ja _).2 (WShape.Join.mk <| WShape.Compat.iff.2 ⟨_, ja.le.1, ja.le.2⟩).le |>.T
  | pair hX hY h1 ih_X ih_Y =>
    cases H2 with | bot => exact bot_r hρ (.pair hX hY h1) | pair hX2 hY2 h12
    rename_i n₁ _ρ_in X Y _m_in A B xV₁ yV₁ n₂ xV₂ yV₂
    have ⟨cX, iX⟩ := ih_X hρ hX2
    have ⟨cY, iY⟩ := ih_Y hρ hY2
    have le₁ := Nat.le_max_left n₁ n₂; have le₂ := Nat.le_max_right n₁ n₂
    have cX_w : WShape.Compat (xV₁.lift _) (xV₂.lift _) := (TShape.Compat.def le₁ le₂).1 cX
    have cY_w : WShape.Compat (yV₁.lift _) (yV₂.lift _) := (TShape.Compat.def le₁ le₂).1 cY
    have jX := WShape.Join.mk cX_w
    have jY := WShape.Join.mk cY_w
    refine mk (h1.trans ?_) (h12.trans ?_) <| .pair' iX iY
    · refine (TShape.LE.lift_l (Nat.succ_le_succ le₁)).2 ?_
      exact WShape.lift_pair' le₁ ▸ WShape.pair'_le_pair'.2 ⟨jX.le.1, jY.le.1⟩
    · refine (TShape.LE.lift_l (Nat.succ_le_succ le₂)).2 ?_
      exact WShape.lift_pair' le₂ ▸ WShape.pair'_le_pair'.2 ⟨jX.le.2, jY.le.2⟩
  | fst hP h1 ih_P =>
    cases H2 with | bot => exact bot_r hρ (.fst hP h1) | fst hP2 h12
    rename_i n₁ _ρ_in P _m s n₂ s'
    have ⟨cP, iP⟩ := ih_P hρ hP2
    have hLvl : (s.T.join s'.T).fst ≤ max n₁ n₂ + 1 :=
      Nat.add_max_add_right .. ▸ Nat.le_refl _
    have iP' : LE_Interp ρ ((s.T.join s'.T).snd.lift (max n₁ n₂ + 1)).T P :=
      iP.mono (TShape.lift_eqv hLvl).1
    have hJ := TShape.Join.mk cP
    refine mk (h1.trans ?_) (h12.trans ?_) (.fst' iP')
    · exact TShape.fst_mono (hJ.le.1.trans (TShape.lift_eqv hLvl).2)
    · exact TShape.fst_mono (hJ.le.2.trans (TShape.lift_eqv hLvl).2)
  | snd hP h1 ih_P =>
    cases H2 with | bot => exact bot_r hρ (.snd hP h1) | snd hP2 h12
    rename_i n₁ _ρ_in P _m s n₂ s'
    have ⟨cP, iP⟩ := ih_P hρ hP2
    have hLvl : (s.T.join s'.T).fst ≤ max n₁ n₂ + 1 :=
      Nat.add_max_add_right .. ▸ Nat.le_refl _
    have iP' : LE_Interp ρ ((s.T.join s'.T).snd.lift (max n₁ n₂ + 1)).T P :=
      iP.mono (TShape.lift_eqv hLvl).1
    have hJ := TShape.Join.mk cP
    refine mk (h1.trans ?_) (h12.trans ?_) (.snd' iP')
    · exact TShape.snd_mono (hJ.le.1.trans (TShape.lift_eqv hLvl).2)
    · exact TShape.snd_mono (hJ.le.2.trans (TShape.lift_eqv hLvl).2)
  | @nat _ n₁ _ h1 =>
    cases H2 with | bot => exact bot_r hρ (.nat h1) | @nat _ n₂ _ h2
    exact mk (h1.trans TShape.nat_eqv) (h2.trans TShape.nat_eqv) (.nat' (n := 0))
  | @zero _ n₁ _ h1 =>
    cases H2 with | bot => exact bot_r hρ (.zero h1) | @zero _ n₂ _ h2
    exact mk (h1.trans TShape.zero_eqv) (h2.trans TShape.zero_eqv) (.zero' (n := 0))
  | succ hv h1 ih_v =>
    cases H2 with | bot => exact bot_r hρ (.succ hv h1) | succ hv2 h12
    have ⟨cv, jv⟩ := ih_v hρ hv2
    have hJ := TShape.Join.mk cv |>.le
    exact mk (h1.trans (TShape.succ_le_succ.2 hJ.1))
      (h12.trans (TShape.succ_le_succ.2 hJ.2)) (.succ' jv)
  | natCase_zero hM₁ ha₁ ihM iha =>
    cases H2 with
    | bot => exact bot_r hρ (.natCase_zero hM₁ ha₁)
    | natCase_succ hM₂ => cases TShape.zero_compat_succ_false (ihM hρ hM₂).1
    | natCase_zero hM₂ ha₂
    have ⟨ca, ja⟩ := iha hρ ha₂
    exact ⟨ca, .natCase_zero (hM₁.mono_l hρ) ja⟩
  | @natCase_succ _ n₁ v Mtm _ btm _ _ hM₁ hb₁ ihM ihb =>
    cases H2 with
    | bot => exact bot_r hρ (.natCase_succ hM₁ hb₁)
    | natCase_zero hM₂ => cases TShape.succ_compat_zero_false (ihM hρ hM₂).1
    | @natCase_succ _ n₂ v' _ _ _ _ _ hM₂ hb₂
    have ⟨cs, jsM⟩ := ihM hρ hM₂
    have hcv := TShape.succ_compat_succ_decomp cs
    have hjv := TShape.Join.mk hcv |>.le
    have ⟨cb, jb⟩ := ihb (Valuation.LE.push.2 ⟨hρ, hjv.1⟩) <|
      hb₂.mono_l (Valuation.LE.push.2 ⟨.rfl, hjv.2⟩)
    refine ⟨cb, .natCase_succ ?_ jb⟩
    exact jsM.mono <| (TShape.Join.succ_succ hcv _).2 (TShape.Join.mk cs).le
  | Y ih_body ih_self ihb ihs =>
    cases H2 with | bot => exact bot_r hρ (.Y ih_body ih_self) | Y hb2 hs2
    have ⟨cs, is⟩ := ihs hρ hs2
    have ⟨cm, im⟩ := ihb (Valuation.LE.push.2 ⟨hρ, (TShape.Join.mk cs).le.1⟩)
      (hb2.mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.Join.mk cs).le.2⟩))
    exact ⟨cm, .Y im is⟩
  | id hA ha hb h1 ihA iha ihb =>
    cases H2 with | bot => exact bot_r hρ (.id hA ha hb h1) | id hA2 ha2 hb2 h12
    rename_i _ρ_in A a b _m n₁ AV₁ aV₁ bV₁ n₂ AV₂ aV₂ bV₂
    have ⟨cA, iA⟩ := ihA hρ hA2
    have ⟨ca, ia⟩ := iha hρ ha2
    have ⟨cb, ib⟩ := ihb hρ hb2
    have le₁ := Nat.le_max_left n₁ n₂; have le₂ := Nat.le_max_right n₁ n₂
    have jA := WShape.Join.mk ((TShape.Compat.def le₁ le₂).1 cA)
    have ja := WShape.Join.mk ((TShape.Compat.def le₁ le₂).1 ca)
    have jb := WShape.Join.mk ((TShape.Compat.def le₁ le₂).1 cb)
    refine mk (h1.trans ?_) (h12.trans ?_) (.id iA ia ib .rfl)
    · refine (TShape.LE.lift_l (Nat.succ_le_succ le₁)).2 ?_
      exact WShape.lift_id le₁ ▸ WShape.id_le_id.2 ⟨jA.le.1, ja.le.1, jb.le.1⟩
    · refine (TShape.LE.lift_l (Nat.succ_le_succ le₂)).2 ?_
      exact WShape.lift_id le₂ ▸ WShape.id_le_id.2 ⟨jA.le.2, ja.le.2, jb.le.2⟩
  | refl hv h1 ihv =>
    cases H2 with | bot => exact bot_r hρ (.refl hv h1) | refl hv2 h12
    rename_i n₁ _ρ_in _a _m v₁ n₂ v₂
    have ⟨cv, jv⟩ := ihv hρ hv2
    have le₁ := Nat.le_max_left n₁ n₂; have le₂ := Nat.le_max_right n₁ n₂
    have jv_w := WShape.Join.mk ((TShape.Compat.def le₁ le₂).1 cv)
    refine mk (h1.trans ?_) (h12.trans ?_)
      (.refl (v := (v₁.lift (max n₁ n₂)).join (v₂.lift (max n₁ n₂))) jv .rfl)
    · refine (TShape.LE.lift_l (Nat.succ_le_succ le₁)).2 ?_
      rw [WShape.lift_refl le₁]
      exact Shape.refl_le.2 ⟨_, rfl, jv_w.le.1⟩
    · refine (TShape.LE.lift_l (Nat.succ_le_succ le₂)).2 ?_
      rw [WShape.lift_refl le₂]
      exact Shape.refl_le.2 ⟨_, rfl, jv_w.le.2⟩
  | tr le hx hva hvb hvA hv_ty_vA hc_C hty hH_refl ihx ihva ihvb ihvA ihc_C ihH =>
    cases H2 with
    | bot => exact bot_r hρ (.tr le hx hva hvb hvA hv_ty_vA hc_C hty hH_refl)
    | tr le2 hx2 hva2 hvb2 hvA2 hv_ty_vA2 hc_C2 hty2 hH2_refl =>
    have ⟨cx, jx⟩ := ihx hρ hx2
    have ⟨_cva, jva⟩ := ihva hρ hva2
    have ⟨cvb, jvb⟩ := ihvb hρ hvb2
    have ⟨_cvA, jvA⟩ := ihvA hρ hvA2
    have ⟨cH, jH⟩ := ihH hρ hH2_refl
    have vb_J := TShape.Join.mk cvb
    have ⟨ca, ja⟩ := ihc_C (Valuation.LE.push.2 (And.intro hρ vb_J.le.1))
      (hc_C2.mono_l (Valuation.LE.push.2 (And.intro .rfl vb_J.le.2)))
    have a_J := TShape.Join.mk ca
    have m'_J := TShape.Join.mk cx
    have aJ_isType := TShape.HasType.join' a_J hty.isType hty2.isType
    have hty_J := TShape.HasType.join' m'_J (TShape.HasType.mono_r a_J.le.1 aJ_isType hty)
      (TShape.HasType.mono_r a_J.le.2 aJ_isType hty2)
    have vA_J := TShape.Join.mk _cvA
    have tJ := TShape.HasType.join' vA_J hv_ty_vA.isType hv_ty_vA2.isType
    refine mk (le.trans m'_J.le.1) (le2.trans m'_J.le.2) <|
      .tr .rfl jx jva jvb jvA (.join' vb_J ?_ ?_) ja hty_J (jH.mono ?_)
    · exact .mono_r vA_J.le.1 tJ hv_ty_vA
    · exact .mono_r vA_J.le.2 tJ hv_ty_vA2
    · rw [TShape.LE.def (Nat.le_refl _)
        (Nat.max_le.2 ⟨Nat.succ_le_succ (Nat.le_max_left ..),
          Nat.succ_le_succ (Nat.le_max_right ..)⟩)]
      simp only [TShape.join, WShape.lift_self]
      rw [Nat.add_max_add_right, WShape.lift_refl (Nat.le_max_left ..),
        WShape.lift_refl (Nat.le_max_right ..), WShape.refl_join_refl _cva, WShape.lift_self]
      exact WShape.LE.rfl

theorem LE_Interp.compat (H1 : LE_Interp ρ m₁ M) (H2 : LE_Interp ρ m₂ M) : m₁.Compat m₂ :=
  (compat_join .rfl H1 H2).1

theorem LE_Interp.join' (H1 : LE_Interp ρ m₁ M) (H2 : LE_Interp ρ m₂ M) :
    LE_Interp ρ (m₁.join m₂) M :=
  (compat_join .rfl H1 H2).2

theorem LE_Interp.join (J : m₁.Join m₂ m) (H1 : LE_Interp ρ m₁ M) (H2 : LE_Interp ρ m₂ M) :
    LE_Interp ρ m M :=
  (H1.join' H2).mono ((J _).2 (TShape.Join.mk (H1.compat H2)).le)

theorem LE_Interp.subst : LE_Interp ρ m (M.subst σ) ↔
    ∃ ρ', LE_Interp ρ' m M ∧ ∀ i, LE_Interp ρ (ρ' i) (σ i) := by
  refine ⟨fun H => ?_, ?_⟩
  · suffices ∀ {ρ m N}, LE_Interp ρ m N → ∀ (M : Term) (σ : Subst), M.subst σ = N →
        ∃ ρ', LE_Interp ρ' m M ∧ ∀ i, LE_Interp ρ (ρ' i) (σ i) from this H M σ rfl
    intro ρ m N H M σ eq
    have bvar {ρ : Valuation} {m N} {σ : Subst} {j} (hσj : σ j = N) (hN : LE_Interp ρ m N) :
        ∃ ρ', LE_Interp ρ' m (.bvar j) ∧ ∀ i, LE_Interp ρ (ρ' i) (σ i) := by
      refine ⟨fun k => if k = j then m else ⟨0, .bot⟩, .bvar (if_pos rfl ▸ .rfl), fun k => ?_⟩
      dsimp; split <;> rename_i ek
      · subst ek; exact hσj ▸ hN
      · exact .bot
    induction H generalizing M σ with
    | bot => exact ⟨.nil, .bot, fun _ => .bot⟩
    | sort h1 =>
      cases M with | bvar => exact bvar eq (.sort h1) | sort => ?_ | _ => cases eq
      cases eq; exact ⟨.nil, .sort h1, fun _ => .bot⟩
    | unit h1 =>
      cases M with | bvar => exact bvar eq (.unit h1) | unit => ?_ | _ => cases eq
      cases eq; exact ⟨.nil, .unit h1, fun _ => .bot⟩
    | bvar h1 => cases M with | bvar => exact bvar eq (.bvar h1) | _ => cases eq
    | app hf ha h1 ih_f ih_a =>
      cases M with | bvar => exact bvar eq (.app hf ha h1) | app F' A' => ?_ | _ => cases eq
      cases eq
      have ⟨ρ₁, hF, h₁⟩ := ih_f F' σ rfl
      have ⟨ρ₂, hA, h₂⟩ := ih_a A' σ rfl
      have hc : ρ₁.Compat ρ₂ := fun i => (h₁ i).compat (h₂ i)
      have ⟨hj1, hj2⟩ := hc.le_join
      refine ⟨ρ₁.join ρ₂, .app (hF.mono_l hj1) (hA.mono_l hj2) h1, fun i => ?_⟩
      exact (h₁ i).join' (h₂ i)
    | @lam ρ n₁ a A f F m_orig ha hdom hbody h1 ih_a ih_body =>
      cases M with | bvar => exact bvar eq (.lam ha hdom hbody h1) | lam A' F' => ?_ | _ => cases eq
      cases eq
      suffices ∃ ρ', LE_Interp ρ' a.T A' ∧ (∀ i, LE_Interp ρ (ρ' i) (σ i)) ∧
          ∀ x ∈ f, LE_Interp (ρ'.push x.1.T) x.2.T F' by
        have ⟨ρ', ha', hρ, H⟩ := this
        refine ⟨ρ', .lam ha' hdom (fun x h => ?_) h1, hρ⟩
        obtain ⟨x', a1, a2⟩ := WShapeFun.app_eq f x
        exact (H _ a2).mono_l (Valuation.LE.push.2 ⟨.rfl, a1.T⟩)
      have H x (h : x ∈ f) :
          ∃ ρ', LE_Interp ρ' x.2.T F' ∧ ∀ i, LE_Interp (ρ.push x.1.T) (ρ' i) (σ.lift i) := by
        have ⟨x', hle, hht, happ⟩ := WShape.HasDom.iff.1 hdom x.1
        have ⟨ρ_x, hF_x, hρ_x⟩ := ih_body x' hht F' σ.lift rfl
        refine ⟨ρ_x, hF_x.mono ((WShapeFun.app_of_mem h).2.trans happ).T, fun i => ?_⟩
        exact (hρ_x i).mono_l (Valuation.LE.push.2 ⟨.rfl, hle.T⟩)
      have ⟨ρA, ha', hρA⟩ := ih_a A' σ rfl
      suffices ∀ (fl : List (Shape n₁ × Shape n₁))
          (wf : ∀ x ∈ fl, x.1.WF ∧ x.2.WF),
          (∀ (x : WShape n₁ × WShape n₁), (x.1.1, x.2.1) ∈ fl →
            ∃ ρ', LE_Interp ρ' x.2.T F' ∧ ∀ i, LE_Interp (ρ.push x.1.T) (ρ' i) (σ.lift i)) →
          ∃ ρ', LE_Interp ρ' a.T A' ∧ (∀ i, LE_Interp ρ (ρ' i) (σ i)) ∧
            ∀ (x : WShape n₁ × WShape n₁), (x.1.1, x.2.1) ∈ fl →
              LE_Interp (ρ'.push x.1.T) x.2.T F' from this f.1 f.2.2 H
      intro fl wf H
      induction fl with | nil => exact ⟨ρA, ha', hρA, nofun⟩ | cons p fl ih
      have ⟨hwf1, hwf2⟩ := wf _ (List.mem_cons_self ..)
      have ⟨ρ₁, hy, hρ₁⟩ := H ⟨⟨p.1, hwf1⟩, ⟨p.2, hwf2⟩⟩ (List.mem_cons_self ..)
      have ⟨ρ₂, ha₂, hρ₂, H_tl⟩ := ih (fun x h => wf x (List.mem_cons.2 (.inr h)))
        (fun x h => H x (List.mem_cons.2 (.inr h)))
      let ρ₁' : Valuation := fun i => ρ₁ (i + 1)
      have hρ₁' i : LE_Interp ρ (ρ₁' i) (σ i) := weak_iff.1 (hρ₁ (i + 1))
      have : ρ₁'.Compat ρ₂ := fun i => (hρ₁' i).compat (hρ₂ i)
      have ⟨hj1, hj2⟩ := this.le_join
      refine ⟨ρ₁'.join ρ₂, ha₂.mono_l hj2, fun i => (hρ₁' i).join' (hρ₂ i), fun x h => ?_⟩
      cases List.mem_cons.1 h with
      | inl h =>
        have heq : x = ⟨⟨p.1, hwf1⟩, ⟨p.2, hwf2⟩⟩ := by
          ext <;> [exact (Prod.ext_iff.1 h).1; exact (Prod.ext_iff.1 h).2]
        subst heq
        exact hy.mono_l <| by
          rw [← (show ρ₁'.push (ρ₁ 0) = ρ₁ by funext i; cases i <;> rfl)]
          exact Valuation.LE.push.2 ⟨hj1, bvar_iff.1 (hρ₁ 0)⟩
      | inr h => exact (H_tl x h).mono_l (Valuation.LE.push.2 ⟨hj2, .rfl⟩)
    | @forallE ρ n₁ b B b' f F m_orig hb hb' hdom hbody h1 ih_b ih_b' ih_body =>
      cases M with
      | bvar => exact bvar eq (.forallE hb hb' hdom hbody h1) | forallE B' F' => ?_ | _ => cases eq
      cases eq
      suffices ∃ ρ', LE_Interp ρ' b.T B' ∧ LE_Interp ρ' b'.T B' ∧
          (∀ i, LE_Interp ρ (ρ' i) (σ i)) ∧ ∀ x ∈ f, LE_Interp (ρ'.push x.1.T) x.2.T F' by
        have ⟨ρ', hb, hb', hρ, H⟩ := this
        refine ⟨ρ', .forallE hb hb' hdom (fun x h => ?_) h1, hρ⟩
        obtain ⟨x', a1, a2⟩ := WShapeFun.app_eq f x
        exact (H _ a2).mono_l <| Valuation.LE.push.2 ⟨.rfl, a1.T⟩
      have H x (h : x ∈ f) :
          ∃ ρ', LE_Interp ρ' x.2.T F' ∧ ∀ i, LE_Interp (ρ.push x.1.T) (ρ' i) (σ.lift i) := by
        have ⟨x', hle, hht, happ⟩ := WShape.HasDom.iff.1 hdom x.1
        have ⟨ρ_x, hF_x, hρ_x⟩ := ih_body x' hht F' σ.lift rfl
        refine ⟨ρ_x, hF_x.mono ((WShapeFun.app_of_mem h).2.trans happ).T, fun i => ?_⟩
        exact (hρ_x i).mono_l (Valuation.LE.push.2 ⟨.rfl, hle.T⟩)
      have ⟨ρ₁, hb₁, hρ₁⟩ := ih_b B' σ rfl
      have ⟨ρ₂, hb₂, hρ₂⟩ := ih_b' B' σ rfl
      have hc₀ : ρ₁.Compat ρ₂ := fun i => (hρ₁ i).compat (hρ₂ i)
      have ⟨hj1₀, hj2₀⟩ := hc₀.le_join
      let ρ₀ := ρ₁.join ρ₂
      suffices ∀ (fl : List (Shape n₁ × Shape n₁))
          (wf : ∀ x ∈ fl, x.1.WF ∧ x.2.WF),
          (∀ (x : WShape n₁ × WShape n₁), (x.1.1, x.2.1) ∈ fl →
            ∃ ρ', LE_Interp ρ' x.2.T F' ∧ ∀ i, LE_Interp (ρ.push x.1.T) (ρ' i) (σ.lift i)) →
          ∃ ρ', LE_Interp ρ' b.T B' ∧ LE_Interp ρ' b'.T B' ∧ (∀ i, LE_Interp ρ (ρ' i) (σ i)) ∧
            ∀ (x : WShape n₁ × WShape n₁), (x.1.1, x.2.1) ∈ fl →
              LE_Interp (ρ'.push x.1.T) x.2.T F' from this f.1 f.2.2 H
      intro fl wf H
      induction fl with
      | nil => exact ⟨ρ₀, hb₁.mono_l hj1₀, hb₂.mono_l hj2₀,
          fun i => (hρ₁ i).join' (hρ₂ i), fun _ h => absurd h List.not_mem_nil⟩
      | cons p fl ih
      have ⟨hwf1, hwf2⟩ := wf _ (List.mem_cons_self ..)
      have ⟨ρ₁, hy, hρ₁⟩ := H ⟨⟨p.1, hwf1⟩, ⟨p.2, hwf2⟩⟩ (List.mem_cons_self ..)
      have ⟨ρ₂, hb₂, hb'₂, hρ₂, H_tl⟩ := ih (fun x h => wf x (List.mem_cons.2 (.inr h)))
        (fun x h => H x (List.mem_cons.2 (.inr h)))
      let ρ₁' : Valuation := fun i => ρ₁ (i + 1)
      have hρ₁' i : LE_Interp ρ (ρ₁' i) (σ i) := weak_iff.1 (hρ₁ (i + 1))
      have : ρ₁'.Compat ρ₂ := fun i => (hρ₁' i).compat (hρ₂ i)
      have ⟨hj1, hj2⟩ := this.le_join
      refine ⟨ρ₁'.join ρ₂, hb₂.mono_l hj2, hb'₂.mono_l hj2,
        fun i => (hρ₁' i).join' (hρ₂ i), fun x h => ?_⟩
      cases List.mem_cons.1 h with
      | inl h =>
        have heq : x = ⟨⟨p.1, hwf1⟩, ⟨p.2, hwf2⟩⟩ := by
          ext <;> [exact (Prod.ext_iff.1 h).1; exact (Prod.ext_iff.1 h).2]
        subst heq
        refine hy.mono_l ?_
        rw [← show ρ₁'.push (ρ₁ 0) = ρ₁ from by funext i; cases i <;> rfl]
        exact Valuation.LE.push.2 ⟨hj1, bvar_iff.1 (hρ₁ 0)⟩
      | inr h => exact (H_tl x h).mono_l (Valuation.LE.push.2 ⟨hj2, .rfl⟩)
    | @sigma ρ n₁ b B b' f F m_orig hb hb' hdom hbody h1 ih_b ih_b' ih_body =>
      cases M with
      | bvar => exact bvar eq (.sigma hb hb' hdom hbody h1) | sigma B' F' => ?_ | _ => cases eq
      cases eq
      suffices ∃ ρ', LE_Interp ρ' b.T B' ∧ LE_Interp ρ' b'.T B' ∧
          (∀ i, LE_Interp ρ (ρ' i) (σ i)) ∧ ∀ x ∈ f, LE_Interp (ρ'.push x.1.T) x.2.T F' by
        have ⟨ρ', hb, hb', hρ, H⟩ := this
        refine ⟨ρ', .sigma hb hb' hdom (fun x h => ?_) h1, hρ⟩
        obtain ⟨x', a1, a2⟩ := WShapeFun.app_eq f x
        exact (H _ a2).mono_l <| Valuation.LE.push.2 ⟨.rfl, a1.T⟩
      have H x (h : x ∈ f) :
          ∃ ρ', LE_Interp ρ' x.2.T F' ∧ ∀ i, LE_Interp (ρ.push x.1.T) (ρ' i) (σ.lift i) := by
        have ⟨x', hle, hht, happ⟩ := WShape.HasDom.iff.1 hdom x.1
        have ⟨ρ_x, hF_x, hρ_x⟩ := ih_body x' hht F' σ.lift rfl
        refine ⟨ρ_x, hF_x.mono ((WShapeFun.app_of_mem h).2.trans happ).T, fun i => ?_⟩
        exact (hρ_x i).mono_l (Valuation.LE.push.2 ⟨.rfl, hle.T⟩)
      have ⟨ρ₁, hb₁, hρ₁⟩ := ih_b B' σ rfl
      have ⟨ρ₂, hb₂, hρ₂⟩ := ih_b' B' σ rfl
      have hc₀ : ρ₁.Compat ρ₂ := fun i => (hρ₁ i).compat (hρ₂ i)
      have ⟨hj1₀, hj2₀⟩ := hc₀.le_join
      let ρ₀ := ρ₁.join ρ₂
      suffices ∀ (fl : List (Shape n₁ × Shape n₁))
          (wf : ∀ x ∈ fl, x.1.WF ∧ x.2.WF),
          (∀ (x : WShape n₁ × WShape n₁), (x.1.1, x.2.1) ∈ fl →
            ∃ ρ', LE_Interp ρ' x.2.T F' ∧ ∀ i, LE_Interp (ρ.push x.1.T) (ρ' i) (σ.lift i)) →
          ∃ ρ', LE_Interp ρ' b.T B' ∧ LE_Interp ρ' b'.T B' ∧ (∀ i, LE_Interp ρ (ρ' i) (σ i)) ∧
            ∀ (x : WShape n₁ × WShape n₁), (x.1.1, x.2.1) ∈ fl →
              LE_Interp (ρ'.push x.1.T) x.2.T F' from this f.1 f.2.2 H
      intro fl wf H
      induction fl with
      | nil => exact ⟨ρ₀, hb₁.mono_l hj1₀, hb₂.mono_l hj2₀,
          fun i => (hρ₁ i).join' (hρ₂ i), fun _ h => absurd h List.not_mem_nil⟩
      | cons p fl ih
      have ⟨hwf1, hwf2⟩ := wf _ (List.mem_cons_self ..)
      have ⟨ρ₁, hy, hρ₁⟩ := H ⟨⟨p.1, hwf1⟩, ⟨p.2, hwf2⟩⟩ (List.mem_cons_self ..)
      have ⟨ρ₂, hb₂, hb'₂, hρ₂, H_tl⟩ := ih (fun x h => wf x (List.mem_cons.2 (.inr h)))
        (fun x h => H x (List.mem_cons.2 (.inr h)))
      let ρ₁' : Valuation := fun i => ρ₁ (i + 1)
      have hρ₁' i : LE_Interp ρ (ρ₁' i) (σ i) := weak_iff.1 (hρ₁ (i + 1))
      have : ρ₁'.Compat ρ₂ := fun i => (hρ₁' i).compat (hρ₂ i)
      have ⟨hj1, hj2⟩ := this.le_join
      refine ⟨ρ₁'.join ρ₂, hb₂.mono_l hj2, hb'₂.mono_l hj2,
        fun i => (hρ₁' i).join' (hρ₂ i), fun x h => ?_⟩
      cases List.mem_cons.1 h with
      | inl h =>
        have heq : x = ⟨⟨p.1, hwf1⟩, ⟨p.2, hwf2⟩⟩ := by
          ext <;> [exact (Prod.ext_iff.1 h).1; exact (Prod.ext_iff.1 h).2]
        subst heq
        exact hy.mono_l <| by
          rw [← (show ρ₁'.push (ρ₁ 0) = ρ₁ by funext i; cases i <;> rfl)]
          exact Valuation.LE.push.2 ⟨hj1, bvar_iff.1 (hρ₁ 0)⟩
      | inr h => exact (H_tl x h).mono_l (Valuation.LE.push.2 ⟨hj2, .rfl⟩)
    | pair hX hY h1 ih_X ih_Y =>
      cases M with | bvar => exact bvar eq (.pair hX hY h1) | pair _ _ X' Y' => ?_ | _ => cases eq
      cases eq
      have ⟨ρ₁, hX', h₁⟩ := ih_X X' σ rfl
      have ⟨ρ₂, hY', h₂⟩ := ih_Y Y' σ rfl
      have hc : ρ₁.Compat ρ₂ := fun i => (h₁ i).compat (h₂ i)
      have ⟨hj1, hj2⟩ := hc.le_join
      refine ⟨ρ₁.join ρ₂, .pair (hX'.mono_l hj1) (hY'.mono_l hj2) h1, fun i => ?_⟩
      exact (h₁ i).join' (h₂ i)
    | fst hP h1 ih_P =>
      cases M with | bvar => exact bvar eq (.fst hP h1) | fst P' => ?_ | _ => cases eq
      cases eq
      have ⟨ρ, hP', h'⟩ := ih_P P' σ rfl
      exact ⟨ρ, .fst hP' h1, h'⟩
    | snd hP h1 ih_P =>
      cases M with | bvar => exact bvar eq (.snd hP h1) | snd P' => ?_ | _ => cases eq
      cases eq
      have ⟨ρ', hP', h'⟩ := ih_P P' σ rfl
      exact ⟨ρ', .snd hP' h1, h'⟩
    | nat h1 =>
      cases M with | bvar => exact bvar eq (.nat h1) | nat => ?_ | _ => cases eq
      exact ⟨.nil, .nat h1, fun _ => .bot⟩
    | zero h1 =>
      cases M with | bvar => exact bvar eq (.zero h1) | zero => ?_ | _ => cases eq
      exact ⟨.nil, .zero h1, fun _ => .bot⟩
    | succ hv h1 ih_v =>
      cases M with | bvar => exact bvar eq (.succ hv h1) | succ N' => ?_ | _ => cases eq
      cases eq
      have ⟨ρ', hv', h'⟩ := ih_v N' σ rfl
      exact ⟨ρ', .succ hv' h1, h'⟩
    | natCase_zero hM ha ihM iha =>
      cases M with
      | bvar => exact bvar eq (.natCase_zero hM ha)
      | natCase C' M' a' b' => ?_
      | _ => cases eq
      cases eq
      have ⟨ρ₁, hM', h₁⟩ := ihM M' σ rfl
      have ⟨ρ₂, ha', h₂⟩ := iha a' σ rfl
      have hc : ρ₁.Compat ρ₂ := fun i => (h₁ i).compat (h₂ i)
      have ⟨hj1, hj2⟩ := hc.le_join
      refine ⟨ρ₁.join ρ₂, .natCase_zero (hM'.mono_l hj1) (ha'.mono_l hj2), fun i => ?_⟩
      exact (h₁ i).join' (h₂ i)
    | @natCase_succ ρ_c m_c C_c M_c a_c b_c n v hM hb ihM ihb =>
      cases M with
      | bvar => exact bvar eq (.natCase_succ hM hb)
      | natCase C' M' a' b' => ?_
      | _ => cases eq
      cases eq
      have ⟨ρ₁, hM', h₁⟩ := ihM M' σ rfl
      have ⟨ρ₂, hb', h₂⟩ := ihb b' σ.lift rfl
      have hρ₂' i : LE_Interp ρ_c (ρ₂ (i + 1)) (σ i) := weak_iff.1 (h₂ (i + 1))
      let ρ₂' : Valuation := fun i => ρ₂ (i + 1)
      have hc : ρ₁.Compat ρ₂' := fun i => (h₁ i).compat (hρ₂' i)
      have ⟨hj1, hj2⟩ := hc.le_join
      refine ⟨ρ₁.join ρ₂', .natCase_succ (hM'.mono_l hj1) (hb'.mono_l ?_), fun i => ?_⟩
      · rw [← (show ρ₂'.push (ρ₂ 0) = ρ₂ by funext i; cases i <;> rfl)]
        refine Valuation.LE.push.2 ⟨hj2, ?_⟩
        exact bvar_iff.1 (h₂ 0)
      · exact (h₁ i).join' (hρ₂' i)
    | Y ih_body ih_self ihb ihs =>
      cases M with | bvar => exact bvar eq (.Y ih_body ih_self) | Y A' b' => ?_ | _ => cases eq
      cases eq
      have ⟨ρ_b, hb, hρ_b⟩ := ihb b' σ.lift rfl
      have ⟨ρ_s, hs, hρ_s⟩ := ihs (A'.Y b') σ rfl
      let ρ_b' : Valuation := fun i => ρ_b (i + 1)
      have hρ_b' i := weak_iff.1 (hρ_b (i + 1))
      have hc : ρ_b'.Compat ρ_s := fun i => (hρ_b' i).compat (hρ_s i)
      have ⟨hj_b, hj_s⟩ := hc.le_join
      refine ⟨ρ_b'.join ρ_s, .Y (hb.mono_l ?_) (hs.mono_l hj_s), fun i => (hρ_b' i).join' (hρ_s i)⟩
      rw [← (show ρ_b'.push (ρ_b 0) = ρ_b by funext i; cases i <;> rfl)]
      exact Valuation.LE.push.2 ⟨hj_b, bvar_iff.1 (hρ_b 0)⟩
    | id hA ha hb h1 ihA iha ihb =>
      cases M with | bvar => exact bvar eq (.id hA ha hb h1) | id A' a' b' => ?_ | _ => cases eq
      cases eq
      have ⟨ρA, hA', hρA⟩ := ihA A' σ rfl
      have ⟨ρa, ha', hρa⟩ := iha a' σ rfl
      have ⟨ρb, hb', hρb⟩ := ihb b' σ rfl
      have hcAa : ρA.Compat ρa := fun i => (hρA i).compat (hρa i)
      have hjAa_i := fun i => (hρA i).join' (hρa i)
      have hcAab : (ρA.join ρa).Compat ρb := fun i => (hjAa_i i).compat (hρb i)
      have ⟨hj_Aa, hj_Aab_b⟩ := hcAab.le_join
      have ⟨hj_A_Aa, hj_a_Aa⟩ := hcAa.le_join
      exact ⟨(ρA.join ρa).join ρb,
        .id (hA'.mono_l fun i => (hj_A_Aa i).trans (hj_Aa i))
            (ha'.mono_l fun i => (hj_a_Aa i).trans (hj_Aa i))
            (hb'.mono_l hj_Aab_b) h1,
        fun i => (hjAa_i i).join' (hρb i)⟩
    | refl hv h1 ihv =>
      cases M with | bvar => exact bvar eq (.refl hv h1) | refl a' => ?_ | _ => cases eq
      cases eq
      have ⟨ρv, hv', hρv⟩ := ihv a' σ rfl
      exact ⟨ρv, .refl hv' h1, hρv⟩
    | tr le hx hva hvb hvA hv_ty_vA hc_C hty hH_refl ihx ihva ihvb ihvA ihc_C ihH =>
      cases M with
      | bvar => exact bvar eq (.tr le hx hva hvb hvA hv_ty_vA hc_C hty hH_refl)
      | tr A' a' b' C' X' H' => ?_ | _ => cases eq
      cases eq
      have ⟨ρ_x, hX', hρ_x⟩ := ihx X' σ rfl
      have ⟨ρ_va, hva', hρ_va⟩ := ihva a' σ rfl
      have ⟨ρ_vb, hvb', hρ_vb⟩ := ihvb b' σ rfl
      have ⟨ρ_vA, hvA', hρ_vA⟩ := ihvA A' σ rfl
      have ⟨ρ_C, hc_C', hρ_C⟩ := ihc_C C' σ.lift rfl
      have ⟨ρ_H, hH_refl', hρ_H⟩ := ihH H' σ rfl
      let ρ_C' : Valuation := fun i => ρ_C (i + 1)
      have hρ_C_skip (i) := weak_iff.1 (hρ_C (i + 1))
      have h_ρ_C_0 := bvar_iff.1 (hρ_C 0)
      have h_ρ_C_eq : ρ_C = ρ_C'.push (ρ_C 0) := by funext i; cases i <;> rfl
      have c_xx'_va : ρ_x.Compat ρ_va := fun i => (hρ_x i).compat (hρ_va i)
      have hj_xx'_to_va := c_xx'_va.le_join.1
      have hj_va_to_va := c_xx'_va.le_join.2
      have hρ_x_va i := (hρ_x i).join' (hρ_va i)
      have c_va_vb : (ρ_x.join ρ_va).Compat ρ_vb :=
        fun i => (hρ_x_va i).compat (hρ_vb i)
      have hj_va_to_vb := c_va_vb.le_join.1
      have hj_vb_to_vb := c_va_vb.le_join.2
      have hρ_x_va_vb i := (hρ_x_va i).join' (hρ_vb i)
      have c_vb_vA : ((ρ_x.join ρ_va).join ρ_vb).Compat ρ_vA :=
        fun i => (hρ_x_va_vb i).compat (hρ_vA i)
      have hj_vb_to_vA := c_vb_vA.le_join.1
      have hj_vA_to_vA := c_vb_vA.le_join.2
      have hρ_x_va_vb_vA i := (hρ_x_va_vb i).join' (hρ_vA i)
      have c_full_C : (((ρ_x.join ρ_va).join ρ_vb).join ρ_vA).Compat ρ_C' :=
        fun i => (hρ_x_va_vb_vA i).compat (hρ_C_skip i)
      have hj_vA_to_full := c_full_C.le_join.1
      have hj_C'_to_full := c_full_C.le_join.2
      have hρ_x_va_vb_vA_C i := (hρ_x_va_vb_vA i).join' (hρ_C_skip i)
      have c_full_H :
          ((((ρ_x.join ρ_va).join ρ_vb).join ρ_vA).join ρ_C').Compat ρ_H :=
        fun i => (hρ_x_va_vb_vA_C i).compat (hρ_H i)
      have hj_full_to_H := c_full_H.le_join.1
      have hj_H_to_full := c_full_H.le_join.2
      have hρ_full i := (hρ_x_va_vb_vA_C i).join' (hρ_H i)
      refine ⟨_,
        .tr le
          (hX'.mono_l (fun i => (hj_xx'_to_va i).trans ((hj_va_to_vb i).trans
              ((hj_vb_to_vA i).trans ((hj_vA_to_full i).trans (hj_full_to_H i))))))
          (hva'.mono_l (fun i => (hj_va_to_va i).trans
            ((hj_va_to_vb i).trans
              ((hj_vb_to_vA i).trans ((hj_vA_to_full i).trans (hj_full_to_H i))))))
          (hvb'.mono_l (fun i => (hj_vb_to_vb i).trans
            ((hj_vb_to_vA i).trans ((hj_vA_to_full i).trans (hj_full_to_H i)))))
          (hvA'.mono_l (fun i => (hj_vA_to_vA i).trans
            ((hj_vA_to_full i).trans (hj_full_to_H i))))
          hv_ty_vA
          (hc_C'.mono_l ?_)
          hty
          (hH_refl'.mono_l hj_H_to_full),
        hρ_full⟩
      rw [h_ρ_C_eq]
      exact Valuation.LE.push.2 ⟨fun i => (hj_C'_to_full i).trans (hj_full_to_H i), h_ρ_C_0⟩
  · rintro ⟨ρ', H, h⟩
    induction H generalizing ρ σ with
    | bot => exact .bot
    | sort h1 => exact .sort h1
    | unit h1 => exact .unit h1
    | bvar h1 => exact (h _).mono h1
    | app hf ha h1 ih_f ih_a => exact .app (ih_f h) (ih_a h) h1
    | lam ha hdom hbody h1 ih_a ih_body =>
      refine .lam (ih_a h) hdom (fun y hy => ?_) h1
      exact ih_body y hy fun | 0 => .bvar0 | i + 1 => (h i).weak
    | forallE hb hb' hdom hbody h1 ih_b ih_b' ih_body =>
      refine .forallE (ih_b h) (ih_b' h) hdom (fun y hy => ?_) h1
      exact ih_body y hy fun | 0 => .bvar0 | i + 1 => (h i).weak
    | sigma hb hb' hdom hbody h1 ih_b ih_b' ih_body =>
      refine .sigma (ih_b h) (ih_b' h) hdom (fun y hy => ?_) h1
      exact ih_body y hy fun | 0 => .bvar0 | i + 1 => (h i).weak
    | pair _ _ h1 ih_X ih_Y => exact .pair (ih_X h) (ih_Y h) h1
    | fst hP h1 ih => exact .fst (ih h) h1
    | snd hP h1 ih => exact .snd (ih h) h1
    | nat h1 => exact .nat h1
    | zero h1 => exact .zero h1
    | succ _ h1 ih_v => exact .succ (ih_v h) h1
    | natCase_zero hM ha ihM iha => exact .natCase_zero (ihM h) (iha h)
    | natCase_succ hM hb ihM ihb =>
      refine .natCase_succ (ihM h) (ihb fun i => ?_)
      cases i <;> [exact .bvar0; exact (h _).weak]
    | Y ih_body ih_self ihb ihs => exact .Y (ihb (fun | 0 => .bvar0 | i+1 => (h i).weak)) (ihs h)
    | id _ _ _ h1 ihA iha ihb => exact .id (ihA h) (iha h) (ihb h) h1
    | refl _ h1 ihv => exact .refl (ihv h) h1
    | tr le _ _ _ _ hv_ty_vA _ hty _ ihx ihva ihvb ihvA ihc_C ihH =>
      refine .tr le (ihx h) (ihva h) (ihvb h) (ihvA h) hv_ty_vA ?_ hty (ihH h)
      exact ihc_C fun | 0 => .bvar0 | i + 1 => (h i).weak

theorem LE_Interp.inst : LE_Interp ρ f (F.inst A) ↔
    ∃ a, LE_Interp (ρ.push a) f F ∧ LE_Interp ρ a A := by
  refine ⟨fun H => ?_, fun ⟨a, hF, hA⟩ => ?_⟩
  · have ⟨ρ, hF, hσ⟩ := LE_Interp.subst.1 H
    refine ⟨_, hF.mono_l ?_, hσ 0⟩
    intro | 0 => exact .rfl | i+1 => exact (bvar_iff.1 (hσ (i+1)) :)
  · exact (LE_Interp.subst (σ := .one A)).2 ⟨_, hF, fun | 0 => hA | _+1 => .bvar'⟩

theorem LE_Interp.Y_iff : LE_Interp ρ m (.Y A b) ↔ LE_Interp ρ m (b.inst (.Y A b)) := by
  refine .trans ⟨fun H => ?_, fun ⟨s, hb, hs⟩ => .Y hb hs⟩ LE_Interp.inst.symm
  cases H with | bot => exact ⟨.bot, .bot, .bot⟩ | Y hb hs => exact ⟨_, hb, hs⟩

theorem LE_Interp.forallE_inv {b} {f : WShapeFun n} {B F}
    (H : LE_Interp ρ (WShape.T (n := n+1) (.forallE b f)) (.forallE B F)) :
    LE_Interp ρ b.T B ∧ ∀ {{X x}}, LE_Interp ρ x.T X → LE_Interp ρ (f.app x).T (F.inst X) := by
  let .forallE (n := n') (f := f₁) hb₁ hb₂ hd hiB le := H
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have ⟨hle_b, hle_f⟩ := TShape.LE.forallE_decomp le
  refine ⟨hb₁.mono ((TShape.LE.def le₁ le₂).2 hle_b), fun X x hx => ?_⟩
  obtain ⟨x', le1, hf⟩ := WShapeFun.app_eq f x
  have hle_f_raw : ShapeFun.LE
      (ShapeFun.lift (Shape.lift (max n n')) f.1)
      (ShapeFun.lift (Shape.lift (max n n')) f₁.1) := by
    rw [← WShapeFun.lift_val le₁, ← WShapeFun.lift_val le₂]; exact hle_f
  obtain ⟨_, _, hf', le2, lf⟩ := ShapeFun.LE.def.1 hle_f_raw _ _
    (List.mem_map.2 ⟨_, hf, rfl⟩)
  obtain ⟨⟨x₁, y₁⟩, hfm, ⟨⟩⟩ := List.mem_map.1 hf'
  have ⟨x₁_wf, y₁_wf⟩ : x₁.WF ∧ y₁.WF := f₁.2.2 _ hfm
  let x₁w : WShape n' := ⟨x₁, x₁_wf⟩
  let y₁w : WShape n' := ⟨y₁, y₁_wf⟩
  have hfm_w : (x₁w, y₁w) ∈ f₁ := (hfm : (x₁w.1, y₁w.1) ∈ f₁.1)
  have ⟨x'dom, hle_dom, hdom_mem, happ_dom⟩ := WShape.HasDom.iff.1 hd x₁w
  have le2_w : x₁w.lift (max n n') ≤ x'.lift (max n n') := by
    show (x₁w.lift _).1 ≤ (x'.lift _).1
    rw [WShape.lift_val le₂, WShape.lift_val le₁]; exact le2
  have le2_T : x₁w.T ≤ x'.T := (TShape.LE.def le₂ le₁).2 le2_w
  refine inst.2 ⟨_, ?_, hx.mono le1.T⟩
  refine hiB x'dom hdom_mem
    |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hle_dom.T.trans le2_T⟩)
    |>.mono (WShape.LE.T happ_dom) |>.mono ?_
  show (f.app x).T ≤ (f₁.app x₁w).T
  have lf : (f.app x).lift (max n n') ≤ y₁w.lift (max n n') := by
    change ((f.app x).lift _).1 ≤ (y₁w.lift _).1
    rw [WShape.lift_val le₁, WShape.lift_val le₂]; exact lf
  exact ((TShape.LE.def le₁ le₂).2 lf).trans (WShape.LE.T (WShapeFun.app_of_mem hfm_w).2)

theorem LE_Interp.forallE_inv' {b} {f : WShapeFun n} {B F}
    (H : LE_Interp ρ (WShape.T (n := n+1) (.forallE b f)) (.forallE B F)) :
    LE_Interp ρ b.T B ∧ ∀ x, LE_Interp (ρ.push x.T) (f.app x).T F := by
  refine ⟨H.forallE_inv.1, fun x => ?_⟩
  have := (LE_Interp.weak (x := x.T) H).forallE_inv.2 .bvar0
  rwa [Term.inst, subst_lift', (?_ : Subst.lift_l _ _ = Subst.id), subst_id] at this
  funext i; cases i <;> rfl

theorem LE_Interp.id_inv {AV aV bV : WShape n} {A a b : Term}
    (H : LE_Interp ρ (WShape.T (n := n+1) (.id AV aV bV)) (.id A a b)) :
    LE_Interp ρ AV.T A ∧ LE_Interp ρ aV.T a ∧ LE_Interp ρ bV.T b := by
  let .id (n := n') hA₁ ha₁ hb₁ le := H
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have ⟨hle_A, hle_a, hle_b⟩ := TShape.LE.id_decomp le
  refine ⟨hA₁.mono ((TShape.LE.def le₁ le₂).2 hle_A),
          ha₁.mono ((TShape.LE.def le₁ le₂).2 hle_a),
          hb₁.mono ((TShape.LE.def le₁ le₂).2 hle_b)⟩

theorem LE_Interp.sigma_inv {b} {f : WShapeFun n} {B F}
    (H : LE_Interp ρ (WShape.T (n := n+1) (.sigma b f)) (.sigma B F)) :
    LE_Interp ρ b.T B ∧ ∀ {{X x}}, LE_Interp ρ x.T X → LE_Interp ρ (f.app x).T (F.inst X) := by
  let .sigma (n := n') (f := f₁) hb₁ hb₂ hd hiB le := H
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have ⟨hle_b, hle_f⟩ := TShape.LE.sigma_decomp le
  refine ⟨hb₁.mono ((TShape.LE.def le₁ le₂).2 hle_b), fun X x hx => ?_⟩
  obtain ⟨x', le1, hf⟩ := WShapeFun.app_eq f x
  have hle_f_raw : ShapeFun.LE
      (ShapeFun.lift (Shape.lift (max n n')) f.1)
      (ShapeFun.lift (Shape.lift (max n n')) f₁.1) := by
    rw [← WShapeFun.lift_val le₁, ← WShapeFun.lift_val le₂]; exact hle_f
  obtain ⟨_, _, hf', le2, lf⟩ := ShapeFun.LE.def.1 hle_f_raw _ _
    (List.mem_map.2 ⟨_, hf, rfl⟩)
  obtain ⟨⟨x₁, y₁⟩, hfm, ⟨⟩⟩ := List.mem_map.1 hf'
  have ⟨x₁_wf, y₁_wf⟩ : x₁.WF ∧ y₁.WF := f₁.2.2 _ hfm
  let x₁w : WShape n' := ⟨x₁, x₁_wf⟩
  let y₁w : WShape n' := ⟨y₁, y₁_wf⟩
  have hfm_w : (x₁w, y₁w) ∈ f₁ := (hfm : (x₁w.1, y₁w.1) ∈ f₁.1)
  have ⟨x'dom, hle_dom, hdom_mem, happ_dom⟩ := WShape.HasDom.iff.1 hd x₁w
  have le2_w : x₁w.lift (max n n') ≤ x'.lift (max n n') := by
    show (x₁w.lift _).1 ≤ (x'.lift _).1
    rw [WShape.lift_val le₂, WShape.lift_val le₁]; exact le2
  have le2_T : x₁w.T ≤ x'.T := (TShape.LE.def le₂ le₁).2 le2_w
  refine inst.2 ⟨_, ?_, hx.mono le1.T⟩
  refine hiB x'dom hdom_mem
    |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hle_dom.T.trans le2_T⟩)
    |>.mono (WShape.LE.T happ_dom) |>.mono ?_
  show (f.app x).T ≤ (f₁.app x₁w).T
  have lf : (f.app x).lift (max n n') ≤ y₁w.lift (max n n') := by
    change ((f.app x).lift _).1 ≤ (y₁w.lift _).1
    rw [WShape.lift_val le₁, WShape.lift_val le₂]; exact lf
  exact ((TShape.LE.def le₁ le₂).2 lf).trans (WShape.LE.T (WShapeFun.app_of_mem hfm_w).2)

theorem LE_Interp.sigma_inv' {b} {f : WShapeFun n} {B F}
    (H : LE_Interp ρ (WShape.T (n := n+1) (.sigma b f)) (.sigma B F)) :
    LE_Interp ρ b.T B ∧ ∀ x, LE_Interp (ρ.push x.T) (f.app x).T F := by
  refine ⟨H.sigma_inv.1, fun x => ?_⟩
  have := (LE_Interp.weak (x := x.T) H).sigma_inv.2 .bvar0
  rwa [Term.inst, subst_lift', (?_ : Subst.lift_l _ _ = Subst.id), subst_id] at this
  funext i; cases i <;> rfl

theorem LE_Interp.lam_inv {f : WShapeFun n} {B F}
    (H : LE_Interp ρ (WShape.T (n := n+1) (.lam' f)) (.lam B F))
    {{X x}} (hx : LE_Interp ρ x.T X) : LE_Interp ρ (f.app x).T (F.inst X) := by
  unfold WShape.lam' at H; split at H <;> rename_i hn; rotate_left
  · by_cases hl : f.app x ≤ .bot; · exact .mono hl.T .bot
    have ⟨_, _, h⟩ := f.app_eq x; exact absurd ⟨_, h, hl⟩ hn
  let .lam (n := n') (f := f₁) _ hd hiF le := H
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have hle_f : f.lift (max n n') ≤ f₁.lift (max n n') := by
    rw [WShape.lam_eq_lam' (hl := hn)] at le; exact le.lam'_decomp
  obtain ⟨x', le1, hf⟩ := WShapeFun.app_eq f x
  have hle_f_raw : ShapeFun.LE
      (ShapeFun.lift (Shape.lift (max n n')) f.1)
      (ShapeFun.lift (Shape.lift (max n n')) f₁.1) := by
    rw [← WShapeFun.lift_val le₁, ← WShapeFun.lift_val le₂]; exact hle_f
  obtain ⟨_, _, hf', le2, lf⟩ := ShapeFun.LE.def.1 hle_f_raw _ _ (List.mem_map.2 ⟨_, hf, rfl⟩)
  obtain ⟨⟨x₁, y₁⟩, hfm, ⟨⟩⟩ := List.mem_map.1 hf'
  have ⟨x₁_wf, y₁_wf⟩ : x₁.WF ∧ y₁.WF := f₁.2.2 _ hfm
  let x₁w : WShape n' := ⟨x₁, x₁_wf⟩
  let y₁w : WShape n' := ⟨y₁, y₁_wf⟩
  have le2_w : x₁w.lift (max n n') ≤ x'.lift (max n n') := by
    rw [WShape.LE.def, WShape.lift_val le₂, WShape.lift_val le₁]; exact le2
  have hfm_w : (x₁w, y₁w) ∈ f₁ := (hfm : (x₁w.1, y₁w.1) ∈ f₁.1)
  have ⟨x'dom, hle_dom, hdom_mem, happ_dom⟩ := WShape.HasDom.iff.1 hd x₁w
  refine inst.2 ⟨_, ?_, hx.mono le1.T⟩
  refine hiF x'dom hdom_mem
    |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hle_dom.T.trans ((TShape.LE.def le₂ le₁).2 le2_w)⟩)
    |>.mono (WShape.LE.T happ_dom) |>.mono (?_ : (f.app x).T ≤ (f₁.app x₁w).T)
  have lf : (f.app x).lift (max n n') ≤ y₁w.lift (max n n') := by
    show ((f.app x).lift _).1 ≤ (y₁w.lift _).1
    rw [WShape.lift_val le₁, WShape.lift_val le₂]; exact lf
  exact ((TShape.LE.def le₁ le₂).2 lf).trans (WShape.LE.T (WShapeFun.app_of_mem hfm_w).2)

theorem LE_Interp.lam_inv' {f : WShapeFun n} {hl : f.NonZero} {B F}
    (H : LE_Interp ρ (WShape.T (n := n+1) (WShape.lam f hl)) (.lam B F)) (x : WShape n) :
    LE_Interp (ρ.push x.T) (f.app x).T F := by
  have := (WShape.lam_eq_lam' ▸ LE_Interp.weak (x := x.T) H).lam_inv .bvar0
  rwa [Term.inst, subst_lift', (?_ : Subst.lift_l _ _ = Subst.id), subst_id] at this
  funext i; cases i <;> rfl

/-- "Fits" relation: `ρ.Fits Γ Δ` says the valuation `ρ` is a semantic
substitution from the source context `Δ` into the target context `Γ`,
with each cons step requiring (i) a saturation witness on `A`, (ii) an
interpretation of the value, and (iii) a typing constraint
`x.HasType a`. -/
inductive Valuation.Fits : (Γ Δ : List Term) → Valuation → Prop
  | nil : Valuation.Fits Γ Γ .nil
  | cons : Valuation.Fits Γ Δ ρ →
    (∀ {a}, LE_Interp ρ a A → ∃ a', a ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .type) →
    LE_Interp ρ a A → x.HasType a →
    Valuation.Fits Γ (A::Δ) (ρ.push x)

theorem Valuation.Fits.lift (hL : Ctx.Lift' l Γ Δ) (W : Valuation.Fits Γ₀ Δ ρ') :
    ∃ Γ₀' ρ, Valuation.Fits Γ₀' Γ ρ ∧ ∀ i, ρ i = ρ' (l.liftVar i) := by
  induction hL generalizing Γ₀ ρ' with
  | refl => exact ⟨_, _, W, fun _ => rfl⟩
  | skip _ ih => cases W with | nil => exact ⟨_, _, .nil, fun _ => rfl⟩ | cons W => exact ih W
  | @cons l' _ _ A _ ih =>
    cases W with | nil => exact ⟨_, _, .nil, fun _ => rfl⟩ | cons W hsat ha hty
    obtain ⟨_, _, W', h⟩ := ih W
    have h_iff {m} := LE_Interp.weak'_iff (m := m) (M := A) l' h
    refine ⟨_, _, W'.cons (fun h => ?_) (h_iff.1 ha) hty, (·.casesOn rfl h)⟩
    obtain ⟨_, h1, h2, h3⟩ := hsat (h_iff.2 h)
    exact ⟨_, h1, h_iff.1 h2, h3⟩

/-- Typed interpretation: there exist witnesses `m'` and `a` interpreting
`M` and `A` such that `m ≤ m'` and `m'.HasType a`. This is the
"saturated" form of `LE_Interp` used in the soundness theorem statements. -/
def InterpTyped (ρ : Valuation) (m : TShape) (M A : Term) :=
  ∃ m' a, m ≤ m' ∧ LE_Interp ρ m' M ∧ LE_Interp ρ a A ∧ m'.HasType a

theorem InterpTyped.bot : InterpTyped ρ (WShape.T (n := n) .bot) M A := by
  refine ⟨WShape.T (n := n) .bot, WShape.T (n := n) .bot, TShape.bot_le', .bot, .bot, ?_⟩
  exact WShape.HasType.T_iff.2 <| .bot' <| .bot' .sort

theorem InterpTyped.mk (le : m ≤ m') (h_m : LE_Interp ρ m' M) (h_a : LE_Interp ρ a A)
    (h_type : m'.HasType a) : InterpTyped ρ m M A := ⟨_, _, le, h_m, h_a, h_type⟩

theorem InterpTyped.out (H : InterpTyped ρ m M A) :
    ∃ n', ∃ m' : WShape n', ∃ a : WShape n', m.1 ≤ n' ∧ m ≤ m'.T ∧
      LE_Interp ρ m'.T M ∧ LE_Interp ρ a.T A ∧ m'.HasType a := by
  obtain ⟨m', a, hle, hm, ha, hty⟩ := H
  let k := max m.1 (max m'.1 a.1)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  refine ⟨k, m'.2.lift k, a.2.lift k, hk.1, ?_, hm.lift hk.2.1, ha.lift hk.2.2, ?_⟩
  · exact hle.trans (TShape.lift_eqv hk.2.1).2
  · exact (TShape.HasType.def hk.2.1 hk.2.2).1 hty

theorem InterpTyped.hsort' {ρ A U}
    (H : ∀ {a}, LE_Interp ρ a A → InterpTyped ρ a A (.sort U))
    {a} (h : LE_Interp ρ a A) :
    ∃ a', a ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType (.sort U) :=
  have ⟨_, _, h1, h2, h3, h4⟩ := H h; ⟨_, h1, h2, .mono_r h3.le_sort .sort h4⟩

theorem InterpTyped.hsort {ρ A U}
    (H : ∀ {a}, LE_Interp ρ a A → InterpTyped ρ a A (.sort U))
    {a} (h : LE_Interp ρ a A) : ∃ a', a ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .type :=
  have ⟨a', h1, h2, h3⟩ := hsort' H h; ⟨a', h1, h2, h3.toType⟩

theorem LE_Interp.sound_bot :
    (LE_Interp ρ (WShape.T (n := n) .bot) M ↔ LE_Interp ρ (WShape.T (n := n) .bot) N) ∧
    (LE_Interp ρ (WShape.T (n := n) .bot) M → InterpTyped ρ (WShape.T (n := n) .bot) M A) :=
  ⟨⟨fun _ => .bot, fun _ => .bot⟩, fun _ => .bot⟩

theorem LE_Interp.sound_app
    (H1 : ∀ {m}, LE_Interp ρ m F → InterpTyped ρ m F (.forallE A B))
    (H2 : ∀ {b}, LE_Interp ρ b (B.inst X) →
      ∃ b', b ≤ b' ∧ LE_Interp ρ b' (B.inst X) ∧ b'.HasType .type)
    (h1 : LE_Interp ρ m (F.app X)) : InterpTyped ρ m (F.app X) (B.inst X) := by
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ .bot
  cases h1 with | bot => exact .bot | app h1 h2 h3
  rename_i nf f_shape a_sh
  have ⟨f_ts, s_ts, le_f, a2, a3, a4⟩ := H1 h1
  have hf : ¬f_ts ≤ .bot := fun h => by
    rw [show f_shape = .bot from TShape.le_bot.1 (le_f.trans h), WShape.bot_app] at h3
    exact hm (h3.trans TShape.bot_le')
  have hs : ¬s_ts ≤ .bot := fun h => hf (a4.bot_r' h)
  cases a3 with | bot => cases hs TShape.bot_le' | forallE b1 b2 b3 b4 b5
  rename_i npi b_pi b_pi' f_pi
  cases b5.le_forall with | bot b5 => cases hs b5 | @forallE m _ _ _ _ b5 b6
  obtain c1 | ⟨n₂, g_lam, rfl, c1⟩ := a4.ty_forallE_inv; · cases hf (c1 ▸ .rfl)
  let k := max (max n₂ m) (max npi nf)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  have a3' := LE_Interp.forallE b1 b2 b3 b4 (TShape.lift_eqv (Nat.succ_le_succ hk.2.1)).1
  rw [WShape.lift_forallE hk.2.1] at a3'
  have h_Binst := a3'.forallE_inv.2 (h2.lift hk.2.2)
  have ⟨a', le', g1, g2⟩ := H2 h_Binst
  have c1 := (TShape.HasTypeLam.def hk.1.1 hk.1.2).1 c1
  have c1_d := WShape.HasDom.iff.1 c1.2.1
  have c1_f := (WShape.HasTypeLam.iff.1 c1).2.2
  have ⟨_, e1, e2, e3⟩ := c1_d (a_sh.lift k)
  refine ⟨_, a', ?_, .app' (a2.lift (Nat.succ_le_succ hk.1.1)) (h2.lift hk.2.2), g1, ?_⟩
  · refine h3.trans <| TShape.app_mono ?_ (TShape.lift_eqv hk.2.2).2
    exact le_f.trans (TShape.lift_eqv (Nat.succ_le_succ hk.1.1)).2
  · have b6 := (TShapeFun.LE.def hk.1.2 hk.2.1).1 b6
    rw [WShape.lift_lam' hk.1.1, WShape.lam'_app]
    refine g2.mono_r ((WShapeFun.app_mono_l b6 _).trans (WShapeFun.app_mono_r e1) |>.T.trans le') ?_
    exact (WShape.HasTypeLam.iff.1 c1).2.2 _ e2 |>.mono_l (WShapeFun.app_mono_r e1) e3 |>.T

theorem LE_Interp.sound_lam
    (H1 : ∀ {m}, LE_Interp ρ m A →
      ∃ a', m ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .type)
    (H2 : ∀ {a x}, LE_Interp ρ a A → x.HasType a →
      ∀ {e}, LE_Interp (ρ.push x) e F → InterpTyped (ρ.push x) e F B)
    (h1 : LE_Interp ρ m (A.lam F)) : InterpTyped ρ m (A.lam F) (A.forallE B) := by
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ .bot
  cases h1 with | bot => cases hm TShape.bot_le' | @lam _ n a _ f _ _ h1 h2 h3 h4
  have ⟨a', a1, a2, a3⟩ := H1 h1
  suffices ∀ (fl : List (WShape n × WShape n)),
      (∀ p ∈ fl, p ∈ f ∧ LE_Interp (ρ.push p.1.T) p.2.T F) →
      ∃ n', n ≤ n' ∧ ∀ k, n' ≤ k → ∃ f' b : WShapeFun k,
        (∀ p ∈ fl, WShapeFun.single (p.1.lift k) (p.2.lift k) ≤ f') ∧
        WShape.HasDom f' (a.lift k) ∧ WShape.HasDom b (a.lift k) ∧
        (∀ x, x.HasType (a.lift k) → LE_Interp (ρ.push x.T) (f'.app x).T F) ∧
        (∀ x, x.HasType (a.lift k) → LE_Interp (ρ.push x.T) (b.app x).T B) ∧
        (∀ x, x.HasType (a.lift k) → (f'.app x).HasType (b.app x)) by
    have ⟨n', le, H⟩ := this f.elems fun p h => by
      have := WShapeFun.mem_elems.1 h
      have ⟨x', hle, hht, happ⟩ := WShape.HasDom.iff.1 h2 p.1
      refine ⟨this, .mono ((WShapeFun.app_of_mem this).2.trans happ).T ?_⟩
      exact (h3 x' hht).mono_l (Valuation.LE.push.2 ⟨.rfl, hle.T⟩)
    have ⟨f', b, hsingle, hd1, hd2, hi1, hi2, hi3⟩ := H _ (Nat.le_refl _)
    have h1' := h1.lift le
    refine ⟨_, _, ?_, .lam' h1' hd1 hi1, .forallE' h1' h1' hd2 hi2, ?_⟩
    · refine h4.trans <| (TShape.LE.lift_l (Nat.succ_le_succ le)).2 (WShape.lift_lam' le ▸ ?_)
      refine WShape.lam'_le_lam'.2 <| WShapeFun.LE.def'.2 fun x y hm => ?_
      obtain ⟨x₀, y₀, h₀, rfl, rfl⟩ := (WShapeFun.mem_lift le).1 hm
      exact WShapeFun.single_le.1 (hsingle _ (WShapeFun.mem_elems.2 h₀))
    · exact WShape.HasType.T <| .lam <| WShape.HasTypeLam.iff.2
        ⟨WShape.HasTypePi.iff.2 ⟨hd2, fun x h => (hi3 x h).isType⟩, hd1, hi3⟩
  intro fl H
  induction fl with
  | nil =>
    refine ⟨_, Nat.le_refl _, fun k hk => ?_⟩
    have ha : (a.lift k).HasType .type :=
      WShape.lift_type.symm ▸ (WShape.HasType.lift hk).2 h2.isType
    refine ⟨.bot, .bot, nofun, .bot ha, .bot ha, fun x h => ?_, fun x h => ?_, fun x h => ?_⟩
    · exact WShapeFun.bot_app ▸ .bot
    · exact WShapeFun.bot_app ▸ .bot
    · simp [WShapeFun.bot_app]; exact .bot' (.bot' .sort)
  | cons p fl ih =>
    have ⟨⟨sub1, h3a⟩, H⟩ := List.forall_mem_cons.1 H
    have ⟨k₁, le1, H1⟩ := ih H
    have ⟨x', x'le, hx', happ⟩ := WShape.HasDom.iff.1 h2 p.1
    have ⟨e', b', le_e, he', hb', heb'⟩ := H2 h1 (WShape.HasType.T hx') (h3 x' hx')
    let m' := max e'.1 b'.1; have ⟨lf, lb⟩ := Nat.max_le.1 (Nat.le_refl m')
    refine ⟨k₁.max m', Nat.le_trans le1 (Nat.le_max_left ..), fun k le' => ?_⟩
    have ⟨le₁, le₂⟩ := Nat.max_le.1 le'
    have le_nk : n ≤ k := Nat.le_trans le1 le₁
    have le_ek := Nat.le_trans lf le₂; have le_bk := Nat.le_trans lb le₂
    have ⟨f₁, b₁, hsingle₁, hd1₁, hd2₁, hi1₁, hi2₁, hi3₁⟩ := H1 _ le₁
    let sf := WShapeFun.single (x'.lift k) (e'.2.lift k)
    let sb := WShapeFun.single (x'.lift k) (b'.2.lift k)
    have hi1_any z : LE_Interp (ρ.push z.T) (f₁.app z).T F :=
      have ⟨z', z'le, z'ht, z'app⟩ := WShape.HasDom.iff.1 hd1₁ z
      (hi1₁ z' z'ht).mono z'app.T |>.mono_l (Valuation.LE.push.2 ⟨.rfl, z'le.T⟩)
    have hi2_any z : LE_Interp (ρ.push z.T) (b₁.app z).T B :=
      have ⟨z', z'le, z'ht, z'app⟩ := WShape.HasDom.iff.1 hd2₁ z
      (hi2₁ z' z'ht).mono z'app.T |>.mono_l (Valuation.LE.push.2 ⟨.rfl, z'le.T⟩)
    have he'_at_x' : LE_Interp (ρ.push (x'.lift k).T) (e'.2.lift k).T F :=
      (he'.lift le_ek).mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.LE.lift_l le_nk).2 .rfl⟩)
    have hb'_at_x' : LE_Interp (ρ.push (x'.lift k).T) (b'.2.lift k).T B :=
      (hb'.lift le_bk).mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.LE.lift_l le_nk).2 .rfl⟩)
    have hc : f₁.Compat sf := by
      rw [WShapeFun.compat_single]; intro ⟨xj, yj⟩ hmem hc
      have ⟨z, hz1, hz2⟩ := WShape.Compat.iff.1 hc
      have sf_app : sf.app z = e'.2.lift k := by rw [WShapeFun.single_app, if_pos hz2]
      refine .mono ?_ (sf_app ▸ .rfl) <| WShape.Compat.T_iff.2 <|
        (hi1_any z).compat (sf_app ▸ he'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, hz2.T⟩))
      exact (WShapeFun.app_of_mem hmem).2.trans (WShapeFun.app_mono_r hz1)
    have hcb : b₁.Compat sb := by
      rw [WShapeFun.compat_single]; intro ⟨xj, yj⟩ hmem hc
      have ⟨z, hz1, hz2⟩ := WShape.Compat.iff.1 hc
      have sb_app : sb.app z = b'.2.lift k := by rw [WShapeFun.single_app, if_pos hz2]
      refine .mono ?_ (sb_app ▸ .rfl) <| WShape.Compat.T_iff.2 <|
        (hi2_any z).compat (sb_app ▸ hb'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, hz2.T⟩))
      exact (WShapeFun.app_of_mem hmem).2.trans (WShapeFun.app_mono_r hz1)
    have jf := WShapeFun.Join.mk hc
    have jb := WShapeFun.Join.mk hcb
    refine ⟨f₁.join sf, b₁.join sb, ?_, ?_, ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · refine List.forall_mem_cons.2 ⟨?_, fun r hr => (hsingle₁ r hr).trans jf.le.1⟩
      refine (WShapeFun.single_le.2 ⟨_, _, WShapeFun.mem_single.2 (.inl rfl), ?_, ?_⟩).trans jf.le.2
      · exact WShape.lift_mono le_nk x'le
      · exact WShape.lift_mono le_nk ((WShapeFun.app_of_mem sub1).2.trans happ)
          |>.trans ((TShape.LE.def le_nk le_ek).1 le_e)
    · refine hd1₁.join' ?_ jf (WShape.join_self.2 ⟨.rfl, .rfl⟩)
      exact WShape.HasDom.single.2 <| .inl <| (WShape.HasType.lift le_nk).2 hx'
    · refine hd2₁.join' ?_ jb (WShape.join_self.2 ⟨.rfl, .rfl⟩)
      exact WShape.HasDom.single.2 <| .inl <| (WShape.HasType.lift le_nk).2 hx'
    · refine (hi1_any x).join (jf.app_l x).T (WShapeFun.single_app ▸ ?_); split
      · exact he'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T ‹_›⟩)
      · exact .bot
    · refine LE_Interp.join (jb.app_l x).T (hi2_any x) (WShapeFun.single_app ▸ ?_); split
      · exact hb'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T ‹_›⟩)
      · exact .bot
    · have hT1 := hi3₁ x hx
      have hT2 : (sf.app x).HasType (sb.app x) := by
        rw [WShapeFun.single_app, WShapeFun.single_app]; split
        · exact (TShape.HasType.def le_ek le_bk).1 heb'
        · exact .bot' (.bot' .sort)
      have jb_x := jb.app_l x
      have := hT1.isType.join' jb_x hT2.isType
      exact (this.mono_r jb_x.le.1 hT1).join' (jf.app_l x) (this.mono_r jb_x.le.2 hT2)

theorem LE_Interp.sound_forallE
    (H1 : ∀ {m}, LE_Interp ρ m A →
      ∃ a', m ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType (.sort U))
    (H2 : ∀ {a x}, LE_Interp ρ a A → x.HasType a →
      ∀ {e}, LE_Interp (ρ.push x) e B → InterpTyped (ρ.push x) e B (.sort v))
    (h1 : LE_Interp ρ m (A.forallE B)) :
    InterpTyped ρ m (A.forallE B) (.sort v) := by
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ .bot
  cases h1 with | bot => cases hm TShape.bot_le' | @forallE _ n b₀ _ b f _ _ h1 h2 h3 h4 h5
  have ⟨a', a1, a2, a3⟩ := H1 h2
  suffices ∀ (fl : List (WShape n × WShape n)),
      (∀ p ∈ fl, p ∈ f ∧ LE_Interp (ρ.push p.1.T) p.2.T B) →
      ∃ n', n ≤ n' ∧ ∀ k, n' ≤ k → ∃ f' : WShapeFun k,
        (∀ p ∈ fl, WShapeFun.single (p.1.lift k) (p.2.lift k) ≤ f') ∧
        WShape.HasDom f' (b.lift k) ∧
        (∀ x, x.HasType (b.lift k) → LE_Interp (ρ.push x.T) (f'.app x).T B) ∧
        (∀ x, x.HasType (b.lift k) → (f'.app x).HasType (.sort v)) by
    have ⟨n', le, H⟩ := this f.elems fun p h => by
      have := WShapeFun.mem_elems.1 h
      have ⟨x', hle, hht, happ⟩ := WShape.HasDom.iff.1 h3 p.1
      refine ⟨this, .mono ((WShapeFun.app_of_mem this).2.trans happ).T ?_⟩
      exact (h4 x' hht).mono_l (Valuation.LE.push.2 ⟨.rfl, hle.T⟩)
    have ⟨f', hsingle, hd1, hi1, hi2⟩ := H _ (Nat.le_refl _)
    have hJ := WShape.Join.mk <| WShape.Compat.T_iff.2 <| h1.compat h2
    have ⟨b₂, c1, c2, c3⟩ := H1 (h1.join hJ.T h2)
    let k := max n' b₂.1; have ⟨le₂, le₁⟩ := Nat.max_le.1 (Nat.le_refl k)
    have b2' := (WShape.HasDom.lift le₂).2 hd1
    refine ⟨((b₂.2.lift k).forallE (f'.lift k)).T, _, h5.trans ?_, ?_, .sort .rfl, ?_⟩
    · rw [TShape.LE.lift_l (Nat.succ_le_succ (Nat.le_trans le le₂)),
        WShape.lift_forallE (Nat.le_trans le le₂)]
      refine WShape.forallE_le_forallE.2 ⟨?_, WShapeFun.lift_lift (.inl le) ▸ ?_⟩
      · exact (TShape.LE.def (Nat.le_trans le le₂) le₁).1 (hJ.le.1.T.trans c1)
      refine WShapeFun.lift_mono le₂ <| WShapeFun.LE.def'.2 fun x y hm => ?_
      obtain ⟨x₀, y₀, h₀, rfl, rfl⟩ := (WShapeFun.mem_lift le).1 hm
      exact WShapeFun.single_le.1 <| hsingle _ (WShapeFun.mem_elems.2 h₀)
    · refine .forallE' (c2.lift le₁) ((h2.lift le).lift le₂) b2' fun x h => ?_
      have ⟨x', d1, dmem⟩ := (f'.lift k).app_eq x
      refine .mono (WShapeFun.app_of_mem dmem).2.T ?_
      obtain ⟨z₀, -, -, rfl, -⟩ := (WShapeFun.mem_lift le₂).1 dmem
      have ⟨z', z'le, z'ht, z'app⟩ := WShape.HasDom.iff.1 hd1 z₀
      refine WShapeFun.lift_app le₂ ▸ .lift (m := (f'.app _).T) le₂ ?_
      refine hi1 _ z'ht |>.mono z'app.T |>.mono_l <| Valuation.LE.push.2 ⟨.rfl, ?_⟩
      exact z'le.T.trans <| (TShape.LE.lift_l le₂).2 d1
    · apply (TShape.HasType.def (Nat.le_refl _) (Nat.zero_le _)).2
      simp only [WShape.lift_self, TShape.sort, WShape.lift_sort]
      have b2' := WShape.lift_lift (.inl le) ▸ b2'
      have := (TShape.HasType.def le₁ (Nat.zero_le k)).1 c3
      refine .forallE <| WShape.HasTypePi.iff.2 ⟨b2'.mono_r ?_ this, fun x hx => ?_⟩
      · exact (TShape.LE.def (Nat.le_trans le le₂) le₁).1 (hJ.le.2.T.trans c1)
      have ⟨x', _, dmem⟩ := (f'.lift k).app_eq x
      obtain ⟨x', y', e1, rfl, eq⟩ := (WShapeFun.mem_lift le₂).1 dmem
      have ⟨e2, e3⟩ := WShapeFun.app_of_mem e1
      refine eq ▸ WShape.lift_sort.symm ▸ (WShape.HasType.lift le₂).2 (.mono_l e2 e3 ?_)
      have ⟨y, d1, d2, d3⟩ := WShape.HasDom.iff.1 hd1 x'
      exact (hi2 _ d2).mono_l (WShapeFun.app_mono_r d1) d3
  intro fl H
  induction fl with
  | nil =>
    refine ⟨_, Nat.le_refl _, fun k hk => ?_⟩
    refine ⟨.bot, nofun, .bot ?_, fun x h => WShapeFun.bot_app ▸ .bot, fun x h => ?_⟩
    · simpa [WShape.lift_sort] using (WShape.HasType.lift hk).2 h3.isType
    · simp [WShapeFun.bot_app]; exact .bot' .sort
  | cons p fl ih =>
    have ⟨⟨sub1, h3a⟩, H⟩ := List.forall_mem_cons.1 H
    have ⟨k₁, le1, H1⟩ := ih H
    have ⟨x', x'le, hx', happ⟩ := WShape.HasDom.iff.1 h3 p.1
    have ⟨f'x, _, le_e, he', hb', heb'⟩ := H2 h2 hx'.T (h4 x' hx')
    replace heb' : f'x.HasType (.sort v) := .mono_r hb'.le_sort .sort heb'
    refine ⟨k₁.max f'x.1, Nat.le_trans le1 (Nat.le_max_left ..), fun k le' => ?_⟩
    have ⟨le₁, le₂⟩ := Nat.max_le.1 le'
    have le_nk := Nat.le_trans le1 le₁
    have ⟨f₁, hsingle₁, hd1₁, hi1₁, hi2₁⟩ := H1 _ le₁
    let sf := WShapeFun.single (x'.lift k) (f'x.2.lift k)
    have hi1_any z : LE_Interp (ρ.push z.T) (f₁.app z).T B :=
      have ⟨z', z'le, z'ht, z'app⟩ := WShape.HasDom.iff.1 hd1₁ z
      (hi1₁ z' z'ht).mono z'app.T |>.mono_l (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T z'le⟩)
    have he'_at_x' : LE_Interp (ρ.push (x'.lift k).T) (f'x.2.lift k).T B :=
      (he'.lift le₂).mono_l <| Valuation.LE.push.2 ⟨.rfl, (TShape.LE.lift_l le_nk).2 .rfl⟩
    have hc : f₁.Compat sf := by
      rw [WShapeFun.compat_single]; intro ⟨xj, yj⟩ hmem hc
      have ⟨z, hz1, hz2⟩ := WShape.Compat.iff.1 hc
      have sf_app : sf.app z = f'x.2.lift k := by rw [WShapeFun.single_app, if_pos hz2]
      refine .mono ?_ (sf_app ▸ .rfl) <| WShape.Compat.T_iff.2 <|
        (hi1_any z).compat (sf_app ▸ he'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, hz2.T⟩))
      exact (WShapeFun.app_of_mem hmem).2.trans (WShapeFun.app_mono_r hz1)
    have jf := WShapeFun.Join.mk hc
    refine ⟨f₁.join sf, ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
    · refine List.forall_mem_cons.2 ⟨?_, fun r hr => (hsingle₁ r hr).trans jf.le.1⟩
      refine (WShapeFun.single_le.2 ⟨_, _, WShapeFun.mem_single.2 (.inl rfl), ?_, ?_⟩).trans jf.le.2
      · exact WShape.lift_mono le_nk x'le
      · exact WShape.lift_mono le_nk ((WShapeFun.app_of_mem sub1).2.trans happ)
          |>.trans ((TShape.LE.def le_nk le₂).1 le_e)
    · refine hd1₁.join' ?_ jf (WShape.join_self.2 ⟨.rfl, .rfl⟩)
      exact WShape.HasDom.single.2 <| .inl <| (WShape.HasType.lift le_nk).2 hx'
    · refine (hi1_any x).join (jf.app_l x).T (WShapeFun.single_app ▸ ?_); split
      · exact he'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T ‹_›⟩)
      · exact .bot
    · refine (hi2₁ x hx).join' (jf.app_l x) (WShapeFun.single_app ▸ ?_); split
      · exact (TShape.HasType.def le₂ (Nat.zero_le k)).1 heb'
      · exact .bot' .sort

theorem LE_Interp.sound_sigma
    (H1 : ∀ {m}, LE_Interp ρ m A →
      ∃ a', m ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType (.sort U))
    (H2 : ∀ {a x}, LE_Interp ρ a A → x.HasType a →
      ∀ {e}, LE_Interp (ρ.push x) e B → InterpTyped (ρ.push x) e B (.sort v))
    (h1 : LE_Interp ρ m (A.sigma B)) :
    InterpTyped ρ m (A.sigma B) (.sort true) := by
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ .bot
  cases h1 with | bot => cases hm TShape.bot_le' | @sigma _ n b₀ _ b f _ _ h1 h2 h3 h4 h5
  have ⟨a', a1, a2, a3⟩ := H1 h2
  suffices ∀ (fl : List (WShape n × WShape n)),
      (∀ p ∈ fl, p ∈ f ∧ LE_Interp (ρ.push p.1.T) p.2.T B) →
      ∃ n', n ≤ n' ∧ ∀ k, n' ≤ k → ∃ f' : WShapeFun k,
        (∀ p ∈ fl, WShapeFun.single (p.1.lift k) (p.2.lift k) ≤ f') ∧
        WShape.HasDom f' (b.lift k) ∧
        (∀ x, x.HasType (b.lift k) → LE_Interp (ρ.push x.T) (f'.app x).T B) ∧
        (∀ x, x.HasType (b.lift k) → (f'.app x).HasType (.sort true)) by
    have ⟨n', le, H⟩ := this f.elems fun p h => by
      have := WShapeFun.mem_elems.1 h
      have ⟨x', hle, hht, happ⟩ := WShape.HasDom.iff.1 h3 p.1
      refine ⟨this, .mono ((WShapeFun.app_of_mem this).2.trans happ).T ?_⟩
      exact (h4 x' hht).mono_l (Valuation.LE.push.2 ⟨.rfl, hle.T⟩)
    have ⟨f', hsingle, hd1, hi1, hi2⟩ := H _ (Nat.le_refl _)
    have hJ := WShape.Join.mk <| WShape.Compat.T_iff.2 <| h1.compat h2
    have ⟨b₂, c1, c2, c3⟩ := H1 (h1.join hJ.T h2)
    let k := max n' b₂.1; have ⟨le₂, le₁⟩ := Nat.max_le.1 (Nat.le_refl k)
    have b2' := (WShape.HasDom.lift le₂).2 hd1
    refine ⟨((b₂.2.lift k).sigma (f'.lift k)).T, _, h5.trans ?_, ?_, .sort .rfl, ?_⟩
    · rw [TShape.LE.lift_l (Nat.succ_le_succ (Nat.le_trans le le₂)),
        WShape.lift_sigma (Nat.le_trans le le₂)]
      refine WShape.sigma_le_sigma.2 ⟨?_, WShapeFun.lift_lift (.inl le) ▸ ?_⟩
      · exact (TShape.LE.def (Nat.le_trans le le₂) le₁).1 (hJ.le.1.T.trans c1)
      refine WShapeFun.lift_mono le₂ <| WShapeFun.LE.def'.2 fun x y hm => ?_
      obtain ⟨x₀, y₀, h₀, rfl, rfl⟩ := (WShapeFun.mem_lift le).1 hm
      exact WShapeFun.single_le.1 <| hsingle _ (WShapeFun.mem_elems.2 h₀)
    · refine .sigma' (c2.lift le₁) ((h2.lift le).lift le₂) b2' fun x h => ?_
      have ⟨x', d1, dmem⟩ := (f'.lift k).app_eq x
      refine .mono (WShapeFun.app_of_mem dmem).2.T ?_
      obtain ⟨z₀, -, -, rfl, -⟩ := (WShapeFun.mem_lift le₂).1 dmem
      have ⟨z', z'le, z'ht, z'app⟩ := WShape.HasDom.iff.1 hd1 z₀
      refine WShapeFun.lift_app le₂ ▸ .lift (m := (f'.app _).T) le₂ ?_
      refine hi1 _ z'ht |>.mono z'app.T |>.mono_l <| Valuation.LE.push.2 ⟨.rfl, ?_⟩
      exact z'le.T.trans <| (TShape.LE.lift_l le₂).2 d1
    · apply (TShape.HasType.def (Nat.le_refl _) (Nat.zero_le _)).2
      simp only [WShape.lift_self, TShape.sort, WShape.lift_sort]
      have b2' := WShape.lift_lift (.inl le) ▸ b2'
      have := (TShape.HasType.def le₁ (Nat.zero_le k)).1 c3
      refine .sigma <| WShape.HasTypeSigma.def.2 ⟨b2'.mono_r ?_ this, fun x y hxy => ?_⟩
      · exact (TShape.LE.def (Nat.le_trans le le₂) le₁).1 (hJ.le.2.T.trans c1)
      obtain ⟨x', y', e1, rfl, eq⟩ := (WShapeFun.mem_lift le₂).1 hxy
      have ⟨e2, e3⟩ := WShapeFun.app_of_mem e1
      have ⟨y, d1, d2, d3⟩ := WShape.HasDom.iff.1 hd1 x'
      have h0 : y'.HasType .type := (.mono_l e2 e3 ((hi2 _ d2).mono_l (WShapeFun.app_mono_r d1) d3))
      have h1 : (WShape.lift k y').HasType (WShape.lift k WShape.type) :=
        (WShape.HasType.lift le₂).2 h0
      rw [WShape.lift_type] at h1
      exact eq ▸ h1
  intro fl H
  induction fl with
  | nil =>
    refine ⟨_, Nat.le_refl _, fun k hk => ?_⟩
    refine ⟨.bot, nofun, .bot ?_, fun x h => WShapeFun.bot_app ▸ .bot, fun x h => ?_⟩
    · simpa [WShape.lift_sort] using (WShape.HasType.lift hk).2 h3.isType
    · simp [WShapeFun.bot_app]; exact .bot' .sort
  | cons p fl ih =>
    have ⟨⟨sub1, h3a⟩, H⟩ := List.forall_mem_cons.1 H
    have ⟨k₁, le1, H1⟩ := ih H
    have ⟨x', x'le, hx', happ⟩ := WShape.HasDom.iff.1 h3 p.1
    have ⟨f'x, _, le_e, he', hb', heb'⟩ := H2 h2 hx'.T (h4 x' hx')
    replace heb' : f'x.HasType (.sort true) :=
      (TShape.HasType.mono_r hb'.le_sort .sort heb').toType
    refine ⟨k₁.max f'x.1, Nat.le_trans le1 (Nat.le_max_left ..), fun k le' => ?_⟩
    have ⟨le₁, le₂⟩ := Nat.max_le.1 le'
    have le_nk := Nat.le_trans le1 le₁
    have ⟨f₁, hsingle₁, hd1₁, hi1₁, hi2₁⟩ := H1 _ le₁
    let sf := WShapeFun.single (x'.lift k) (f'x.2.lift k)
    have hi1_any z : LE_Interp (ρ.push z.T) (f₁.app z).T B :=
      have ⟨z', z'le, z'ht, z'app⟩ := WShape.HasDom.iff.1 hd1₁ z
      (hi1₁ z' z'ht).mono z'app.T |>.mono_l (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T z'le⟩)
    have he'_at_x' : LE_Interp (ρ.push (x'.lift k).T) (f'x.2.lift k).T B :=
      (he'.lift le₂).mono_l <| Valuation.LE.push.2 ⟨.rfl, (TShape.LE.lift_l le_nk).2 .rfl⟩
    have hc : f₁.Compat sf := by
      rw [WShapeFun.compat_single]; intro ⟨xj, yj⟩ hmem hc
      have ⟨z, hz1, hz2⟩ := WShape.Compat.iff.1 hc
      have sf_app : sf.app z = f'x.2.lift k := by rw [WShapeFun.single_app, if_pos hz2]
      refine .mono ?_ (sf_app ▸ .rfl) <| WShape.Compat.T_iff.2 <|
        (hi1_any z).compat (sf_app ▸ he'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, hz2.T⟩))
      exact (WShapeFun.app_of_mem hmem).2.trans (WShapeFun.app_mono_r hz1)
    have jf := WShapeFun.Join.mk hc
    refine ⟨f₁.join sf, ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
    · refine List.forall_mem_cons.2 ⟨?_, fun r hr => (hsingle₁ r hr).trans jf.le.1⟩
      refine (WShapeFun.single_le.2 ⟨_, _, WShapeFun.mem_single.2 (.inl rfl), ?_, ?_⟩).trans jf.le.2
      · exact WShape.lift_mono le_nk x'le
      · exact WShape.lift_mono le_nk ((WShapeFun.app_of_mem sub1).2.trans happ)
          |>.trans ((TShape.LE.def le_nk le₂).1 le_e)
    · refine hd1₁.join' ?_ jf (WShape.join_self.2 ⟨.rfl, .rfl⟩)
      exact WShape.HasDom.single.2 <| .inl <| (WShape.HasType.lift le_nk).2 hx'
    · refine (hi1_any x).join (jf.app_l x).T (WShapeFun.single_app ▸ ?_); split
      · exact he'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T ‹_›⟩)
      · exact .bot
    · refine (hi2₁ x hx).join' (jf.app_l x) (WShapeFun.single_app ▸ ?_); split
      · exact (TShape.HasType.def le₂ (Nat.zero_le k)).1 heb'
      · exact .bot' .sort

theorem LE_Interp.sound_id {A a b : Term} {U : Bool}
    (HA : ∀ {m}, LE_Interp ρ m A → InterpTyped ρ m A (.sort U))
    (Ha : ∀ {m}, LE_Interp ρ m a → InterpTyped ρ m a A)
    (Hb : ∀ {m}, LE_Interp ρ m b → InterpTyped ρ m b A)
    (h : LE_Interp ρ m (.id A a b)) :
    InterpTyped ρ m (.id A a b) (.sort true) := by
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ .bot
  cases h with | bot => cases hm TShape.bot_le' | id hA_li ha_li hb_li h_le
  rename_i n0 AV0 aV0 bV0
  have ⟨nA, AV_w, _sA_w, hn0_nA, hAV0_le, hAV_w_li, _, _⟩ := (HA hA_li).out
  have ⟨na, av_w, Aa_w, _, haV0_le, hav_w_li, hAa_w_li, hav_w_ty⟩ := (Ha ha_li).out
  have ⟨nb, bv_w, Ab_w, _, hbV0_le, hbv_w_li, hAb_w_li, hbv_w_ty⟩ := (Hb hb_li).out
  have hkA : nA ≤ max (max nA na) nb :=
    Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..)
  have hka : na ≤ max (max nA na) nb :=
    Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..)
  have hkb : nb ≤ max (max nA na) nb := Nat.le_max_right ..
  have hAV_li_k := hAV_w_li.lift hkA
  have hAa_li_k := hAa_w_li.lift hka
  have hAb_li_k := hAb_w_li.lift hkb
  have hJ12 := hAV_li_k.join' hAa_li_k
  have hJfull := hJ12.join' hAb_li_k
  have ⟨W_T, h_leW, hW_li, hW_ty_T⟩ := InterpTyped.hsort HA hJfull
  have hk_k1 : max (max nA na) nb ≤ max (max (max nA na) nb) W_T.1 := Nat.le_max_left ..
  have hW_k1 : W_T.1 ≤ max (max (max nA na) nb) W_T.1 := Nat.le_max_right ..
  have hW_k1_type :
      (W_T.2.lift _).HasType (WShape.type : WShape (max (max (max nA na) nb) W_T.1)) := by
    have := (TShape.HasType.def hW_k1 (Nat.zero_le _)).1 hW_ty_T
    simpa [WShape.lift_type] using this
  have hav_ty_k1 :
      (av_w.lift (max (max (max nA na) nb) W_T.1)).HasType (Aa_w.lift _) :=
    (WShape.HasType.lift (Nat.le_trans hka hk_k1)).2 hav_w_ty
  have hbv_ty_k1 :
      (bv_w.lift (max (max (max nA na) nb) W_T.1)).HasType (Ab_w.lift _) :=
    (WShape.HasType.lift (Nat.le_trans hkb hk_k1)).2 hbv_w_ty
  have hAa_le_W_T : (Aa_w.lift (max (max nA na) nb)).T ≤ W_T :=
    (TShape.Join.mk (hAV_li_k.compat hAa_li_k)).le.2.trans
      ((TShape.Join.mk (hJ12.compat hAb_li_k)).le.1.trans h_leW)
  have hAb_le_W_T : (Ab_w.lift (max (max nA na) nb)).T ≤ W_T :=
    (TShape.Join.mk (hJ12.compat hAb_li_k)).le.2.trans h_leW
  have hAa_le_W :
      (Aa_w.lift (max (max (max nA na) nb) W_T.1)) ≤ (W_T.2.lift _) := by
    have h1 : (Aa_w.lift (max (max nA na) nb)).T ≤
        (W_T.2.lift (max (max (max nA na) nb) W_T.1)).T :=
      hAa_le_W_T.trans (TShape.lift_eqv hW_k1).2
    have := (TShape.LE.def hk_k1 (Nat.le_refl _)).1 h1
    rwa [WShape.lift_lift (.inl hka), WShape.lift_self] at this
  have hAb_le_W :
      (Ab_w.lift (max (max (max nA na) nb) W_T.1)) ≤ (W_T.2.lift _) := by
    have h1 : (Ab_w.lift (max (max nA na) nb)).T ≤
        (W_T.2.lift (max (max (max nA na) nb) W_T.1)).T :=
      hAb_le_W_T.trans (TShape.lift_eqv hW_k1).2
    have := (TShape.LE.def hk_k1 (Nat.le_refl _)).1 h1
    rwa [WShape.lift_lift (.inl hkb), WShape.lift_self] at this
  have hav_ty_W :
      (av_w.lift (max (max (max nA na) nb) W_T.1)).HasType (W_T.2.lift _) :=
    WShape.HasType.mono_r hAa_le_W hW_k1_type hav_ty_k1
  have hbv_ty_W :
      (bv_w.lift (max (max (max nA na) nb) W_T.1)).HasType (W_T.2.lift _) :=
    WShape.HasType.mono_r hAb_le_W hW_k1_type hbv_ty_k1
  have h_idty :
      WShape.HasTypeId (W_T.2.lift (max (max (max nA na) nb) W_T.1))
        (av_w.lift _) (bv_w.lift _) :=
    ⟨hav_ty_W, hbv_ty_W⟩
  have h_shape_ty :
      (WShape.id (W_T.2.lift (max (max (max nA na) nb) W_T.1)) (av_w.lift _) (bv_w.lift _)).HasType
        (WShape.type : WShape (max (max (max nA na) nb) W_T.1 + 1)) :=
    WShape.HasType.id_l.2 ⟨h_idty, rfl⟩
  have hav_li_k1 : LE_Interp ρ (av_w.lift (max (max (max nA na) nb) W_T.1)).T a :=
    hav_w_li.lift (Nat.le_trans hka hk_k1)
  have hbv_li_k1 : LE_Interp ρ (bv_w.lift (max (max (max nA na) nb) W_T.1)).T b :=
    hbv_w_li.lift (Nat.le_trans hkb hk_k1)
  have hW_li_k1 : LE_Interp ρ (W_T.2.lift (max (max (max nA na) nb) W_T.1)).T A :=
    hW_li.mono (TShape.lift_eqv hW_k1).1
  have hAV0_T_le_Wk1 : AV0.T ≤ (W_T.2.lift (max (max (max nA na) nb) W_T.1)).T := by
    refine hAV0_le.trans ?_
    refine (TShape.lift_eqv hkA).2.trans ?_
    refine (TShape.Join.mk (hAV_li_k.compat hAa_li_k)).le.1.trans ?_
    refine (TShape.Join.mk (hJ12.compat hAb_li_k)).le.1.trans ?_
    exact h_leW.trans (TShape.lift_eqv hW_k1).2
  have haV0_T_le_avk1 : aV0.T ≤ (av_w.lift (max (max (max nA na) nb) W_T.1)).T :=
    haV0_le.trans (TShape.lift_eqv (Nat.le_trans hka hk_k1)).2
  have hbV0_T_le_bvk1 : bV0.T ≤ (bv_w.lift (max (max (max nA na) nb) W_T.1)).T :=
    hbV0_le.trans (TShape.lift_eqv (Nat.le_trans hkb hk_k1)).2
  have hn0_k1 : n0 ≤ max (max (max nA na) nb) W_T.1 :=
    Nat.le_trans hn0_nA (Nat.le_trans hkA hk_k1)
  have hAV0_le_W :
      AV0.lift (max (max (max nA na) nb) W_T.1) ≤ (W_T.2.lift _) := by
    have := (TShape.LE.def hn0_k1 (Nat.le_refl _)).1 hAV0_T_le_Wk1
    simpa [WShape.lift_self] using this
  have haV0_le_av :
      aV0.lift (max (max (max nA na) nb) W_T.1) ≤ (av_w.lift _) := by
    have := (TShape.LE.def hn0_k1 (Nat.le_refl _)).1 haV0_T_le_avk1
    simpa [WShape.lift_self] using this
  have hbV0_le_bv :
      bV0.lift (max (max (max nA na) nb) W_T.1) ≤ (bv_w.lift _) := by
    have := (TShape.LE.def hn0_k1 (Nat.le_refl _)).1 hbV0_T_le_bvk1
    simpa [WShape.lift_self] using this
  have h_le_id : m ≤
      (WShape.id (W_T.2.lift _) (av_w.lift _) (bv_w.lift _) :
        WShape (max (max (max nA na) nb) W_T.1 + 1)).T := by
    refine h_le.trans ?_
    refine (TShape.LE.lift_l (Nat.succ_le_succ hn0_k1)).2 ?_
    rw [WShape.lift_id hn0_k1]
    exact WShape.id_le_id.2 ⟨hAV0_le_W, haV0_le_av, hbV0_le_bv⟩
  refine .mk h_le_id (.id hW_li_k1 hav_li_k1 hbv_li_k1 .rfl) (.sort .rfl) ?_
  apply (TShape.HasType.def (Nat.le_refl _) (Nat.zero_le _)).2
  simpa [WShape.lift_self, TShape.sort, WShape.lift_sort] using h_shape_ty

theorem LE_Interp.sound_pair {A B X Y : Term}
    (H2 : ∀ {a x}, LE_Interp ρ a A → x.HasType a →
      ∀ {e}, LE_Interp (ρ.push x) e B →
        ∃ b', e ≤ b' ∧ LE_Interp (ρ.push x) b' B ∧ b'.HasType .type)
    (H3 : ∀ {m}, LE_Interp ρ m X → InterpTyped ρ m X A)
    (H4 : ∀ {m}, LE_Interp ρ m Y → InterpTyped ρ m Y (B.inst X))
    (h : LE_Interp ρ m (.pair A B X Y)) :
    InterpTyped ρ m (.pair A B X Y) (.sigma A B) := by
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ .bot
  cases h with | bot => cases hm TShape.bot_le' | pair h_x h_y le_p
  rename_i n0 xV yV
  have ⟨_nxw, xV_w, _a_w, _, le_xV_T, hxV_li, _, _⟩ := (H3 h_x).out
  have ⟨nyw, yV_w, c_y, _, le_yV_T, hyV_li, hc_y_li, hyV_ty⟩ := (H4 h_y).out
  have ⟨x_v, h_c_B, h_xv_X⟩ := LE_Interp.inst.1 hc_y_li
  have hcompat_X : x_v.Compat xV_w.T := h_xv_X.compat hxV_li
  have hJ_X := TShape.Join.mk hcompat_X
  have hxj_X : LE_Interp ρ (x_v.join xV_w.T) X := h_xv_X.join' hxV_li
  have h_c_B_xj : LE_Interp (ρ.push (x_v.join xV_w.T)) c_y.T B :=
    h_c_B.mono_l (Valuation.LE.push.2 ⟨.rfl, hJ_X.le.1⟩)
  have ⟨nxj, xj_w, a_xj, _, le_xj_T, hxj_w_li, ha_xj_li, hxj_w_ty⟩ := (H3 hxj_X).out
  have h_c_B_xjw : LE_Interp (ρ.push xj_w.T) c_y.T B :=
    h_c_B_xj.mono_l (Valuation.LE.push.2 ⟨.rfl, le_xj_T⟩)
  have ⟨c_w, _le_c, hc_w_li, hc_w_ty⟩ := H2 ha_xj_li hxj_w_ty.T h_c_B_xjw
  let k := max (max nxj nyw) c_w.1
  have hkxj : nxj ≤ k := Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..)
  have hkyw : nyw ≤ k := Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..)
  have hkcw : c_w.1 ≤ k := Nat.le_max_right ..
  let xj_k : WShape k := xj_w.lift k
  let a_k : WShape k := a_xj.lift k
  let y_k : WShape k := yV_w.lift k
  let c_y_k : WShape k := c_y.lift k
  let c_k : WShape k := c_w.2.lift k
  have hxj_ty_k : xj_k.HasType a_k := (WShape.HasType.lift hkxj).2 hxj_w_ty
  have hyV_ty_k : y_k.HasType c_y_k := (WShape.HasType.lift hkyw).2 hyV_ty
  have hak_type : a_k.HasType .type := by
    have := (WShape.HasType.lift hkxj).2 hxj_w_ty.isType
    simpa [WShape.lift_type] using this
  have hck_type : c_k.HasType .type := by
    have hcty_W : c_w.2.HasType WShape.type := by
      have hcw1 : c_w.1 ≤ c_w.1 := Nat.le_refl _
      have := (TShape.HasType.def hcw1 (Nat.zero_le _)).1 hc_w_ty
      simp only [TShape.type, TShape.sort, WShape.lift_self, WShape.lift_sort] at this
      exact this
    have := (WShape.HasType.lift hkcw).2 hcty_W
    simpa [WShape.lift_type] using this
  have hcy_le_ck_W : c_y_k ≤ c_k := by
    have h1 : c_y_k.T ≤ c_y.T := (TShape.lift_eqv hkyw).1
    have h2 : c_w ≤ c_k.T := (TShape.lift_eqv hkcw).2
    have htchain : c_y_k.T ≤ c_k.T := (h1.trans _le_c).trans h2
    have := (TShape.LE.def (a := c_y_k.T) (b := c_k.T) (Nat.le_refl _)
      (Nat.le_refl _)).1 htchain
    simpa [WShape.lift_self] using this
  have hy_ty_ck : y_k.HasType c_k :=
    WShape.HasType.mono_r hcy_le_ck_W hck_type hyV_ty_k
  let f : WShapeFun k := WShapeFun.single xj_k c_k
  have hf_sigma : WShape.HasTypeSigma f a_k := by
    refine WShape.HasTypeSigma.def.2 ⟨?_, ?_⟩
    · exact WShape.HasDom.single.2 (.inl hxj_ty_k)
    · intro x y hxy
      obtain ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ := WShapeFun.mem_single.1 hxy
      · exact hck_type
      · exact .bot' .sort
  have hf_app_xj : f.app xj_k = c_k := by
    show (WShapeFun.single xj_k c_k).app xj_k = c_k
    rw [WShapeFun.single_app, if_pos .rfl]
  have h_pair_ty : WShape.HasTypePair xj_k y_k a_k f := by
    refine ⟨hf_sigma, hxj_ty_k, ?_⟩
    have hf_app_val : f.1.app xj_k.1 = c_k.1 := congrArg (·.1) hf_app_xj
    rw [hf_app_val]
    exact hy_ty_ck
  have hxj_w_li_k : LE_Interp ρ xj_k.T X := hxj_w_li.mono (TShape.lift_eqv hkxj).1
  have hyV_li_k : LE_Interp ρ y_k.T Y := hyV_li.mono (TShape.lift_eqv hkyw).1
  have h_pair_li : LE_Interp ρ ((WShape.pair' xj_k y_k).T) (.pair A B X Y) :=
    .pair' hxj_w_li_k hyV_li_k
  have ha_li_k : LE_Interp ρ a_k.T A := ha_xj_li.mono (TShape.lift_eqv hkxj).1
  have hsigma_li : LE_Interp ρ ((WShape.sigma a_k f).T) (.sigma A B) := by
    refine .sigma' ha_li_k ha_li_k ?_ ?_
    · exact WShape.HasDom.single.2 (.inl hxj_ty_k)
    · intro x hx
      show LE_Interp (ρ.push x.T) ((WShapeFun.single xj_k c_k).app x).T B
      rw [WShapeFun.single_app]
      split <;> [rename_i hxle; exact .bot]
      have hxj_T : xj_w.T ≤ x.T := by
        refine (TShape.lift_eqv hkxj).2.trans ?_
        have := (TShape.LE.def (a := xj_k.T) (b := x.T)
          (Nat.le_refl _) (Nat.le_refl _)).2 (by simpa [WShape.lift_self] using hxle)
        exact this
      refine hc_w_li.mono_l (Valuation.LE.push.2 ⟨.rfl, hxj_T⟩) |>.mono ?_
      exact (TShape.lift_eqv hkcw).1
  have h_pair_HasType : (WShape.pair' xj_k y_k).HasType (WShape.sigma a_k f) := by
    by_cases hbot : xj_k ≤ .bot ∧ y_k ≤ .bot
    · rw [WShape.le_bot.1 hbot.1, WShape.le_bot.1 hbot.2]
      simp only [WShape.pair'_bot_bot]
      exact .bot' (.sigma hf_sigma)
    · have hbot' : ¬xj_k ≤ .bot ∨ ¬y_k ≤ .bot := by
        by_cases hxk : xj_k ≤ .bot
        · refine .inr fun h => hbot ⟨hxk, h⟩
        · exact .inl hxk
      have hcond : ¬xj_k.1 ≤ Shape.bot ∨ ¬y_k.1 ≤ Shape.bot := hbot'
      have h_pair_eq : WShape.pair' xj_k y_k = WShape.pair xj_k y_k hcond := by
        unfold WShape.pair'; rw [dif_pos hcond]
      rw [h_pair_eq]
      exact .pair h_pair_ty
  refine ⟨(WShape.pair' xj_k y_k).T, (WShape.sigma a_k f).T, ?_, h_pair_li, hsigma_li,
    h_pair_HasType.T⟩
  refine le_p.trans ?_
  have hxV_le_xjk : xV.T ≤ xj_k.T := by
    refine le_xV_T.trans ?_
    refine hJ_X.le.2.trans ?_
    refine le_xj_T.trans ?_
    exact (TShape.lift_eqv hkxj).2
  have hyV_le_yk : yV.T ≤ y_k.T := le_yV_T.trans (TShape.lift_eqv hkyw).2
  exact TShape.pair'_le_pair' hxV_le_xjk hyV_le_yk

def SoundEq (Γ : List Term) (M N : Term) : Prop :=
  ∀ {{Γ₀ ρ}}, Valuation.Fits Γ₀ Γ ρ → ∀ {m}, LE_Interp ρ m M ↔ LE_Interp ρ m N
/-- Semantic typing: under every fits valuation, every `m ≤` `M` is saturated
to an `InterpTyped` witness at `A`. -/
def SoundTy (Γ : List Term) (M A : Term) : Prop :=
  ∀ {{Γ₀ ρ}}, Valuation.Fits Γ₀ Γ ρ → ∀ {m}, LE_Interp ρ m M → InterpTyped ρ m M A

theorem LE_Interp.sound_Y {Γ : List Term} {A b : Term} {u} {Γ₀ ρ}
    (hA : ∀ {a}, LE_Interp ρ a A → InterpTyped ρ a A (.sort u))
    (hb : SoundTy (A::Γ) b A.lift)
    (W : Valuation.Fits Γ₀ Γ ρ)
    {m} (h : LE_Interp ρ m (.Y A b)) : InterpTyped ρ m (.Y A b) A := by
  generalize eqM : Term.Y A b = M at h
  induction h with cases eqM
  | bot => exact InterpTyped.bot
  | Y hbody hself ihbody ihself =>
    obtain ⟨_, _, sle, hsY, haA, htyp⟩ := ihself hA W rfl
    have Wc := W.cons (InterpTyped.hsort hA) haA htyp
    have hbody' := hbody.mono_l (Valuation.LE.push.2 ⟨.rfl, sle⟩)
    obtain ⟨m', a', mle, hm'b, ha'A, hm'ty⟩ := hb Wc hbody'
    exact InterpTyped.mk mle (.Y hm'b hsY) (LE_Interp.weak_iff.1 ha'A) hm'ty

theorem LE_Interp.Y_cong {Γ : List Term} {A A' b b' : Term} {u} {Γ₀ ρ}
    (hA : ∀ {a}, LE_Interp ρ a A → InterpTyped ρ a A (.sort u))
    (hbTy : SoundTy (A::Γ) b A.lift) (hbEq : SoundEq (A::Γ) b b')
    (W : Valuation.Fits Γ₀ Γ ρ) {m} (h : LE_Interp ρ m (.Y A b)) : LE_Interp ρ m (.Y A' b') := by
  suffices ∀ {m}, LE_Interp ρ m (.Y A b) →
      ∃ m'' a, m ≤ m'' ∧ LE_Interp ρ a A ∧ m''.HasType a ∧ LE_Interp ρ m'' (.Y A' b') by
    obtain ⟨_, _, hle, _, _, hY'⟩ := this h; exact hY'.mono hle
  clear h m; intro m h; generalize eqM : Term.Y A b = M at h
  induction h with cases eqM
  | bot =>
    refine ⟨WShape.T (n := 0) .bot, WShape.T (n := 0) .bot, TShape.bot_le', .bot, ?_, .bot⟩
    exact WShape.HasType.T_iff.2 (.bot' (.bot' .sort))
  | Y hbody hself ihbody ihself
  obtain ⟨_, _, sle, ha_s, hs_ty, hsY'⟩ := ihself hA W rfl
  have Wc := W.cons (fun h => InterpTyped.hsort hA h) ha_s hs_ty
  have hbody' := hbody.mono_l (Valuation.LE.push.2 ⟨.rfl, sle⟩)
  obtain ⟨m'', a'', mle, hm''b, ha''A, hm''ty⟩ := hbTy Wc hbody'
  exact ⟨m'', a'', mle, LE_Interp.weak_iff.1 ha''A, hm''ty, .Y ((hbEq Wc).1 hm''b) hsY'⟩

mutual
/-- `StrongSound Γ M A`: `M` is semantically typed at `A` *and* there is a
structural derivation at some `A'` related to `A` by `SoundEq`. The
intermediate `A'` lets the structural rules use whatever Π/sort form is
natural while still concluding at the desired `A`. -/
inductive StrongSound : List Term → Term → Term → Prop where
  | mk : SoundTy Γ M A →
    StrongSoundCore Γ M A' → SoundEq Γ A' A → StrongSound Γ M A

/-- Structural typing relation: one constructor per term former
(`bvar`/`sort`/`lam`/`app`/`forallE`). Mutually recursive with
`StrongSound`, which is what each sub-derivation actually produces. -/
inductive StrongSoundCore : List Term → Term → Term → Prop where
  | bvar : Lookup Γ i A → StrongSoundCore Γ (.bvar i) A
  | sort : StrongSoundCore Γ (.sort l) (.sort true)
  | lam : SoundTy Γ A (.sort u) →
    StrongSound (A::Γ) e B → StrongSoundCore Γ (.lam A e) (.forallE A B)
  | app : SoundTy Γ A (.sort u) →
    StrongSound Γ f (.forallE A B) → StrongSound Γ a A →
    StrongSoundCore Γ (.app f a) (B.inst a)
  | forallE : StrongSound Γ A (.sort u) → StrongSound (A::Γ) B (.sort v) →
    StrongSoundCore Γ (.forallE A B) (.sort v)
  | sigma : StrongSound Γ A (.sort u) → StrongSound (A::Γ) B (.sort v) →
    StrongSoundCore Γ (.sigma A B) (.sort true)
  | unit : StrongSoundCore Γ (.unit r) (.sort r)
  | star : StrongSoundCore Γ (.star r) (.unit r)
  | pair : SoundTy Γ A (.sort u) → SoundTy (A::Γ) B (.sort v) →
    StrongSound Γ X A → StrongSound Γ Y (B.inst X) →
    StrongSoundCore Γ (.pair A B X Y) (.sigma A B)
  | fst : SoundTy Γ A (.sort u) → SoundTy (A::Γ) B (.sort v) →
    StrongSound Γ p (.sigma A B) →
    StrongSoundCore Γ (.fst p) A
  | snd : SoundTy Γ A (.sort u) → SoundTy (A::Γ) B (.sort v) →
    StrongSound Γ p (.sigma A B) →
    StrongSoundCore Γ (.snd p) (B.inst (.fst p))
  | nat : StrongSoundCore Γ .nat (.sort true)
  | zero : StrongSoundCore Γ .zero .nat
  | succ : StrongSound Γ n .nat → StrongSoundCore Γ (.succ n) .nat
  | natCase : StrongSound (.nat::Γ) C (.sort v) →
    StrongSound Γ M .nat →
    StrongSound Γ a (C.inst .zero) →
    StrongSound (.nat::Γ) b ((C.lift' (.cons (.skip .refl))).inst (.succ (.bvar 0))) →
    StrongSoundCore Γ (.natCase C M a b) (C.inst M)
  | Y : SoundTy Γ A (.sort u) → StrongSound (A::Γ) b A.lift → StrongSoundCore Γ (.Y A b) A
  | id : StrongSound Γ A (.sort u) →
    StrongSound Γ a A → StrongSound Γ b A →
    StrongSoundCore Γ (.id A a b) (.sort true)
  | refl : SoundTy Γ A (.sort u) → StrongSound Γ a A →
    StrongSoundCore Γ (.refl a) (.id A a a)
  | tr : SoundTy Γ A (.sort u) → SoundTy Γ a A → SoundTy Γ b A →
    StrongSound (A::Γ) C (.sort v) →
    StrongSound Γ x (C.inst a) → StrongSound Γ h (.id A a b) →
    StrongSoundCore Γ (.tr A a b C x h) (C.inst b)
end
/-- Strong soundness for an equality judgment: both sides are individually
`StrongSound` at `A`, and they are semantically equal. -/
structure StrongSoundEq (Γ : List Term) (M N A : Term) : Prop where
  sound : SoundEq Γ M N
  left : StrongSound Γ M A
  right : StrongSound Γ N A

theorem SoundEq.rfl : SoundEq Γ M M := fun _ _ _ _ => .rfl
theorem SoundEq.symm : SoundEq Γ M N → SoundEq Γ N M := fun H _ _ W _ => (H W).symm
theorem StrongSoundEq.symm : StrongSoundEq Γ M N A → StrongSoundEq Γ N M A
  | ⟨h2, h3, h4⟩ => ⟨h2.symm, h4, h3⟩
theorem StrongSound.sound : StrongSound Γ M A → SoundTy Γ M A
  | ⟨h, _, _⟩ => h
theorem StrongSoundEq.rfl (H : StrongSound Γ M A) : StrongSoundEq Γ M M A := ⟨.rfl, H, H⟩
theorem SoundEq.trans (H1 : SoundEq Γ M N) (H2 : SoundEq Γ N P) : SoundEq Γ M P :=
  fun _ _ W _ => (H1 W).trans (H2 W)
theorem StrongSoundEq.trans :
    StrongSoundEq Γ M N A → StrongSoundEq Γ N P A → StrongSoundEq Γ M P A
  | ⟨a2, a3, _⟩, ⟨b2, _, b4⟩ => ⟨a2.trans b2, a3, b4⟩
theorem SoundTy.defeq_l (H1 : SoundEq Γ M N) (H : SoundTy Γ M A) : SoundTy Γ N A := fun _ _ W _ h =>
  have ⟨_, _, a1, a2, a3, a4⟩ := H W ((H1 W).2 h); ⟨_, _, a1, (H1 W).1 a2, a3, a4⟩
theorem SoundTy.defeq_r (H1 : SoundEq Γ A B) (H : SoundTy Γ M A) : SoundTy Γ M B := fun _ _ W _ h =>
  have ⟨_, _, a1, a2, a3, a4⟩ := H W h; ⟨_, _, a1, a2, (H1 W).1 a3, a4⟩

theorem StrongSound.defeq_r (H1 : SoundEq Γ A B) : StrongSound Γ M A → StrongSound Γ M B
  | ⟨sound, core, eq⟩ => ⟨sound.defeq_r H1, core, eq.trans H1⟩

theorem StrongSoundEq.mk'
    (h2 : StrongSoundCore Γ M A₁) (h2' : SoundEq Γ A₁ A)
    (h3 : StrongSoundCore Γ N A₂) (h3' : SoundEq Γ A₂ A)
    (h4 : ∀ {{Γ₀ ρ}}, Valuation.Fits Γ₀ Γ ρ → ∀ {m},
      (LE_Interp ρ m M ↔ LE_Interp ρ m N) ∧ (LE_Interp ρ m M → InterpTyped ρ m M A)) :
    StrongSoundEq Γ M N A := by
  refine have ha := ?_; have ht := ?_
    ⟨ha, ⟨ht, h2, h2'⟩, ht.defeq_l ha, h3, h3'⟩
  · exact fun _ _ W _ => (h4 W).1
  · exact fun _ _ W _ => (h4 W).2

theorem SoundEq.inst (ht : SoundTy Γ X A) (hA : SoundTy Γ A (.sort u))
    (H : SoundEq (A::Γ) M N) : SoundEq Γ (M.inst X) (N.inst X) := fun _ ρ W m => by
  suffices ∀ M N, SoundEq (A::Γ) M N → LE_Interp ρ m (M.inst X) → LE_Interp ρ m (N.inst X) from
    ⟨this _ _ H, this _ _ H.symm⟩
  simp only [LE_Interp.inst]; intro M N H ⟨x, h1, h2⟩
  have ⟨x', a, a1, a2, a3, a4⟩ := ht W h2
  refine ⟨_, (H (W.cons (InterpTyped.hsort (hA W)) a3 a4)).1 ?_, a2⟩
  exact h1.mono_l <| Valuation.LE.push.2 ⟨.rfl, a1⟩

theorem SoundTy.bvar (H : Lookup Γ i A) : SoundTy Γ (.bvar i) A := fun _ _ W _ h => by
  cases h with | bot => exact .bot | bvar a1
  induction W generalizing i A with | nil => exact TShape.le_bot'.1 a1 ▸ .bot | cons _ h1 h2 h3 ih
  cases H with | zero => exact ⟨_, _, a1, .bvar .rfl, h2.weak, h3⟩ | succ h
  have ⟨_, _, le, h1, h2, h3⟩ := ih h a1; exact ⟨_, _, le, h1.weak, h2.weak, h3⟩

theorem SoundTy.nat : SoundTy Γ .nat (.sort true) := fun _ _ _ _ h => by
  cases h with | bot => exact .bot | nat h1
  exact .mk h1 .nat' .sort' (.mono_r TShape.sort_eqv.1 .sort WShape.HasType.nat.T)

theorem SoundTy.zero : SoundTy Γ .zero .nat := fun _ _ _ _ h => by
  cases h with | bot => exact .bot | zero h1
  exact .mk h1 .zero' .nat' WShape.HasType.zero.T

theorem SoundTy.succ (H : SoundTy Γ n .nat) : SoundTy Γ (.succ n) .nat := fun _ ρ W m h => by
  cases h with | bot => exact .bot | @succ _ _ _ n v hv h1
  have ⟨nk, v_w, a_w, hle_nk, hv_le, hv_w_li, ha_w_li, hv_w_ty⟩ := (H W hv).out
  obtain ⟨n_a, ha_nat⟩ := ha_w_li.le_nat
  let k := max nk n_a; have ⟨le₁, le₂⟩ := Nat.max_le.1 (Nat.le_refl k)
  have le₁' : nk ≤ k+1 := Nat.le_succ_of_le le₁
  refine .mk ?_ (.succ' (hv_w_li.lift le₁')) .nat' (WShape.HasType.succ (n := _+1)
    (WShape.HasType.mono_r ?_ .nat ((WShape.HasType.lift le₁').2 hv_w_ty))).T
  · exact h1.trans <| TShape.succ_le_succ.2 <| hv_le.trans (TShape.lift_eqv (a := v_w.T) le₁').2
  · exact WShape.lift_nat le₂ ▸ (TShape.LE.def le₁' (Nat.succ_le_succ le₂)).1 ha_nat

theorem SoundEq.lift' (hL : Ctx.Lift' l Γ Δ) (H : SoundEq Γ M N) :
    SoundEq Δ (M.lift' l) (N.lift' l) := fun _ _ W _ =>
  have ⟨_, _, W', h⟩ := W.lift hL
  (LE_Interp.weak'_iff l h).trans <| (H W').trans (LE_Interp.weak'_iff l h).symm

theorem SoundEq.sort : SoundEq Γ (.sort u) (.sort v) ↔ u = v := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · injection congrArg (·.1) <| WShape.sort_le.1 <| ((H .nil).1 .sort').le_sort' with eq
  · intro _ ρ W m
    suffices ∀ {u v}, u = v →
        LE_Interp ρ m (Term.sort u) → LE_Interp ρ m (Term.sort v) from ⟨this H, this H.symm⟩
    intro u v H h; exact .mono (H ▸ h.le_sort) .sort'

theorem SoundEq.forallE (hA : SoundTy Γ A (.sort u))
    (H1 : SoundEq Γ A A') (H2 : SoundEq (A::Γ) B B') :
    SoundEq Γ (.forallE A B) (.forallE A' B') := by
  intro _ ρ W m
  suffices ∀ {A₁ A₂ B₁ B₂}, SoundEq Γ A A₁ → SoundEq Γ A A₂ → SoundEq (A::Γ) B₁ B₂ →
      LE_Interp ρ m (.forallE A₁ B₁) → LE_Interp ρ m (.forallE A₂ B₂) from
    ⟨this .rfl H1 H2, this H1 .rfl H2.symm⟩
  intro A₁ A₂ B₁ B₂ H1 H2 H3 h
  cases h with | bot => exact .bot | forallE h1 h2 h3 h4 h5
  have HA := H1.symm.trans H2
  refine .forallE ((HA W).1 h1) ((HA W).1 h2) h3 (fun _ h' => ?_) h5
  exact (H3 (W.cons (InterpTyped.hsort (hA W)) ((H1 W).2 h2) h'.T)).1 (h4 _ h')

theorem SoundEq.sigma (hA : SoundTy Γ A (.sort u))
    (H1 : SoundEq Γ A A') (H2 : SoundEq (A::Γ) B B') :
    SoundEq Γ (.sigma A B) (.sigma A' B') := by
  intro _ ρ W m
  suffices ∀ {A₁ A₂ B₁ B₂}, SoundEq Γ A A₁ → SoundEq Γ A A₂ → SoundEq (A::Γ) B₁ B₂ →
      LE_Interp ρ m (.sigma A₁ B₁) → LE_Interp ρ m (.sigma A₂ B₂) from
    ⟨this .rfl H1 H2, this H1 .rfl H2.symm⟩
  intro A₁ A₂ B₁ B₂ H1 H2 H3 h
  cases h with | bot => exact .bot | sigma h1 h2 h3 h4 h5
  have HA := H1.symm.trans H2
  refine .sigma ((HA W).1 h1) ((HA W).1 h2) h3 (fun _ h' => ?_) h5
  exact (H3 (W.cons (InterpTyped.hsort (hA W)) ((H1 W).2 h2) h'.T)).1 (h4 _ h')

theorem SoundEq.id (H1 : SoundEq Γ A A') (H2 : SoundEq Γ a a') (H3 : SoundEq Γ b b') :
    SoundEq Γ (.id A a b) (.id A' a' b') := by
  intro _ ρ W m
  suffices ∀ {A₁ A₂ a₁ a₂ b₁ b₂},
      SoundEq Γ A₁ A₂ → SoundEq Γ a₁ a₂ → SoundEq Γ b₁ b₂ →
      LE_Interp ρ m (.id A₁ a₁ b₁) → LE_Interp ρ m (.id A₂ a₂ b₂) from
    ⟨this H1 H2 H3, this H1.symm H2.symm H3.symm⟩
  intro A₁ A₂ a₁ a₂ b₁ b₂ HA Ha Hb h
  cases h with | bot => exact .bot | id h1 h2 h3 h4
  exact .id ((HA W).1 h1) ((Ha W).1 h2) ((Hb W).1 h3) h4

theorem SoundEq.inst_arg {C : Term} (hX : SoundEq Γ X X') :
    SoundEq Γ (C.inst X) (C.inst X') := fun _ ρ W m => by
  simp only [LE_Interp.inst]
  refine ⟨fun ⟨x, h1, h2⟩ => ⟨x, h1, (hX W).1 h2⟩,
    fun ⟨x, h1, h2⟩ => ⟨x, h1, (hX W).2 h2⟩⟩

theorem SoundEq.id_inv (H : SoundEq Γ (.id A a b) (.id A' a' b')) :
    SoundEq Γ A A' ∧ SoundEq Γ a a' ∧ SoundEq Γ b b' := by
  refine ⟨?_, ?_, ?_⟩
  · intro _ ρ W m
    suffices ∀ {A B a₁ b₁ a₂ b₂}, SoundEq Γ (.id A a₁ b₁) (.id B a₂ b₂) →
        LE_Interp ρ m A → LE_Interp ρ m B from ⟨this H, this H.symm⟩
    intro A B a₁ b₁ a₂ b₂ H h_A
    have h_id : LE_Interp ρ (WShape.T (n := m.1+1) (.id m.2 .bot .bot)) (.id A a₁ b₁) :=
      .id h_A .bot .bot .rfl
    exact ((H W).1 h_id).id_inv.1
  · intro _ ρ W m
    suffices ∀ {A B a₁ b₁ a₂ b₂}, SoundEq Γ (.id A a₁ b₁) (.id B a₂ b₂) →
        LE_Interp ρ m a₁ → LE_Interp ρ m a₂ from ⟨this H, this H.symm⟩
    intro A B a₁ b₁ a₂ b₂ H h_a
    have h_id : LE_Interp ρ (WShape.T (n := m.1+1) (.id .bot m.2 .bot)) (.id A a₁ b₁) :=
      .id .bot h_a .bot .rfl
    exact ((H W).1 h_id).id_inv.2.1
  · intro _ ρ W m
    suffices ∀ {A B a₁ b₁ a₂ b₂}, SoundEq Γ (.id A a₁ b₁) (.id B a₂ b₂) →
        LE_Interp ρ m b₁ → LE_Interp ρ m b₂ from ⟨this H, this H.symm⟩
    intro A B a₁ b₁ a₂ b₂ H h_b
    have h_id : LE_Interp ρ (WShape.T (n := m.1+1) (.id .bot .bot m.2)) (.id A a₁ b₁) :=
      .id .bot .bot h_b .rfl
    exact ((H W).1 h_id).id_inv.2.2

theorem SoundEq.sigma_inv (H : SoundEq Γ (.sigma A B) (.sigma A' B'))
    (hA : SoundTy Γ A (.sort u)) (hA' : SoundTy Γ A' (.sort u')) :
    SoundEq Γ A A' ∧ SoundEq (A::Γ) B B' := by
  refine have hAA _ ρ W m := ?_; ⟨hAA, fun Γ₀ ρ W m => ?_⟩
  · suffices ∀ {A A' B B' u}, SoundEq Γ (.sigma A B) (.sigma A' B') → SoundTy Γ A (.sort u) →
        LE_Interp ρ m A → LE_Interp ρ m A' from ⟨this H hA, this H.symm hA'⟩
    intro A A' B B' u H hA h
    have ⟨_, a1, a2, a3⟩ := InterpTyped.hsort (hA W) h
    refine (H W).1 (.sigma' a2 a2 (.bot (TShape.HasType.sort_r.1 a3)) ?_) |>.sigma_inv.1.mono a1
    intro x _; simpa using .bot
  · suffices ∀ {A₁ A₂ B₁ B₂}, SoundEq Γ (.sigma A₁ B₁) (.sigma A₂ B₂) →
        SoundEq Γ A A₁ → LE_Interp ρ m B₁ → LE_Interp ρ m B₂ from ⟨this H .rfl, this H.symm hAA⟩
    intro A A' B B' H hAA h
    cases W with
    | nil =>
      have := (H .nil).1 <| .sigma' (f := .single .bot m.2) .bot .bot (WShape.HasDom.iff.2 ?_) ?_
      · have := this.sigma_inv'.2 .bot
        simp [WShapeFun.single_app] at this
        refine this.mono_l ?_; rintro ⟨⟩ <;> exact TShape.bot_eqv.1
      · refine fun _ => ⟨_, WShape.bot_le, .bot' (.bot' .sort), ?_⟩
        simpa [WShapeFun.single_app] using .rfl
      · intro x h'; cases h'.bot_r
        simpa [WShapeFun.single_app] using h.mono_l fun _ => TShape.bot_le'
    | @cons Γ ρ A a x b1 b2 b3 b4 =>
      let k := max (max x.1 m.1) a.1
      have hk := Nat.max_le.1 (Nat.le_refl k); simp [Nat.max_le] at hk
      have b4' := (TShape.HasType.def hk.1.1 hk.2).1 b4
      have := (hAA b1).1 (b3.lift hk.2)
      have := (H b1).1 <| .sigma' (f := .single (x.2.lift k) (m.2.lift k))
        this this (WShape.HasDom.iff.2 ?_) ?_
      · have := this.sigma_inv'.2 (x.2.lift k)
        simp [WShapeFun.single_app, WShape.LE.rfl] at this
        exact this.mono (TShape.lift_eqv hk.1.2).2 |>.mono_l <|
          Valuation.LE.push.2 ⟨.rfl, (TShape.lift_eqv hk.1.1).1⟩
      · intro x'; simp [WShapeFun.single_app]
        split <;> [rename_i h; exact ⟨_, WShape.bot_le, .bot' b4'.isType, WShape.bot_le⟩]
        refine ⟨_, h, b4', if_pos ?_ ▸ .rfl⟩; exact .rfl
      · intro x' h1; simp [WShapeFun.single_app]; split <;> [rename_i h2; exact .bot]
        refine h.mono (TShape.lift_eqv hk.1.2).1 |>.mono_l <| Valuation.LE.push.2 ⟨.rfl, ?_⟩
        exact (TShape.LE.lift_l hk.1.1).2 h2

theorem SoundEq.forallE_inv (H : SoundEq Γ (.forallE A B) (.forallE A' B'))
    (hA : SoundTy Γ A (.sort u)) (hA' : SoundTy Γ A' (.sort u')) :
    SoundEq Γ A A' ∧ SoundEq (A::Γ) B B' := by
  refine have hAA _ ρ W m := ?_; ⟨hAA, fun Γ₀ ρ W m => ?_⟩
  · suffices ∀ {A A' B B' u}, SoundEq Γ (.forallE A B) (.forallE A' B') → SoundTy Γ A (.sort u) →
        LE_Interp ρ m A → LE_Interp ρ m A' from ⟨this H hA, this H.symm hA'⟩
    intro A A' B B' u H hA h
    have ⟨_, a1, a2, a3⟩ := InterpTyped.hsort (hA W) h
    refine (H W).1 (.forallE' a2 a2 (.bot (TShape.HasType.sort_r.1 a3)) ?_) |>.forallE_inv.1.mono a1
    intro x _; simpa using .bot
  · suffices ∀ {A₁ A₂ B₁ B₂}, SoundEq Γ (.forallE A₁ B₁) (.forallE A₂ B₂) →
        SoundEq Γ A A₁ → LE_Interp ρ m B₁ → LE_Interp ρ m B₂ from ⟨this H .rfl, this H.symm hAA⟩
    intro A A' B B' H hAA h
    cases W with
    | nil =>
      have := (H .nil).1 <| .forallE' (f := .single .bot m.2) .bot .bot (WShape.HasDom.iff.2 ?_) ?_
      · have := this.forallE_inv'.2 .bot
        simp [WShapeFun.single_app] at this
        refine this.mono_l ?_; rintro ⟨⟩ <;> exact TShape.bot_eqv.1
      · refine fun _ => ⟨_, WShape.bot_le, .bot' (.bot' .sort), ?_⟩
        simpa [WShapeFun.single_app] using .rfl
      · intro x h'; cases h'.bot_r
        simpa [WShapeFun.single_app] using h.mono_l fun _ => TShape.bot_le'
    | @cons Γ ρ A a x b1 b2 b3 b4 =>
      let k := max (max x.1 m.1) a.1
      have hk := Nat.max_le.1 (Nat.le_refl k); simp [Nat.max_le] at hk
      have b4' := (TShape.HasType.def hk.1.1 hk.2).1 b4
      have := (hAA b1).1 (b3.lift hk.2)
      have := (H b1).1 <| .forallE' (f := .single (x.2.lift k) (m.2.lift k))
        this this (WShape.HasDom.iff.2 ?_) ?_
      · have := this.forallE_inv'.2 (x.2.lift k)
        simp [WShapeFun.single_app, WShape.LE.rfl] at this
        exact this.mono (TShape.lift_eqv hk.1.2).2 |>.mono_l <|
          Valuation.LE.push.2 ⟨.rfl, (TShape.lift_eqv hk.1.1).1⟩
      · intro x'; simp [WShapeFun.single_app]
        split <;> [rename_i h; exact ⟨_, WShape.bot_le, .bot' b4'.isType, WShape.bot_le⟩]
        refine ⟨_, h, b4', if_pos ?_ ▸ .rfl⟩; exact .rfl
      · intro x' h1; simp [WShapeFun.single_app]; split <;> [rename_i h2; exact .bot]
        refine h.mono (TShape.lift_eqv hk.1.2).1 |>.mono_l <| Valuation.LE.push.2 ⟨.rfl, ?_⟩
        exact (TShape.LE.lift_l hk.1.1).2 h2

theorem StrongSound.uniq_of_core
    (H : ∀ {A B}, StrongSoundCore Γ M A → StrongSoundCore Γ M B → SoundEq Γ A B) :
    StrongSound Γ M A → StrongSound Γ M B → SoundEq Γ A B
  | ⟨_, a3, a4⟩, ⟨_, b3, b4⟩ => a4.symm.trans <| (H a3 b3).trans b4

theorem SoundTy.fstsnd {A B : Term} (hP : SoundTy Γ p (.sigma A B)) :
    SoundTy Γ (.fst p) A ∧ SoundTy Γ (.snd p) (B.inst (.fst p)) := by
  -- Shared key lemma: given an interpretation `hsT : LE_Interp ρ s.T p`
  -- of `p` at the sigma type, produce both the `fst` and `snd` saturated witnesses
  -- parameterised by the source bound `m`.
  suffices key : ∀ {Γ₀ ρ} (W : Valuation.Fits Γ₀ Γ ρ) {n} {s : WShape (n+1)}
      (hsT : LE_Interp ρ s.T p) {m : TShape},
      (m ≤ s.fst.T → InterpTyped ρ m (.fst p) A) ∧
      (m ≤ s.snd.T → InterpTyped ρ m (.snd p) (B.inst (.fst p))) by
    refine ⟨?_, ?_⟩
    · intro Γ₀ ρ W m h
      by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ InterpTyped.bot
      cases h with | bot => cases hm TShape.bot_le' | fst hsT le_msf
      exact (key W hsT).1 le_msf
    · intro Γ₀ ρ W m h
      by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ InterpTyped.bot
      cases h with | bot => cases hm TShape.bot_le' | snd hsT le_msn
      exact (key W hsT).2 le_msn
  -- Body of the key lemma
  intros Γ₀ ρ W n s hsT m
  have ⟨nk, m'_w, a_w, _, sleT, h_pT, h_aT, h_tyT⟩ := (hP W hsT).out
  -- Reduce to the case where m'_w is not bot.
  -- (If m'_w ≤ .bot then so does s.T, hence s.fst.T and s.snd.T, so m ≤ .bot → trivial.)
  -- We use this dispatcher in both branches.
  have hm' (hbot : m'_w ≤ .bot) :
      (m ≤ s.fst.T → InterpTyped ρ m (.fst p) A) ∧
      (m ≤ s.snd.T → InterpTyped ρ m (.snd p) (B.inst (.fst p))) := by
    refine ⟨fun le => ?_, fun le => ?_⟩ <;>
    · cases WShape.le_bot.1 hbot
      cases show s = WShape.bot from TShape.le_bot.1 <| sleT.trans TShape.bot_le'
      exact (TShape.le_bot'.1 (le.trans TShape.bot_le')) ▸ InterpTyped.bot
  cases h_aT with
  | bot => exact hm' (WShape.HasType.bot_r h_tyT ▸ WShape.le_bot.2 rfl)
  | sigma hb_T _hb'_T _hd _hf le_a_sig
  rename_i na bv bv' fv
  cases le_a_sig.le_sigma with
  | bot ha_bot =>
    cases show a_w = WShape.bot from TShape.le_bot.1 ha_bot
    cases h_tyT.bot_r
    exact hm' (WShape.le_bot.2 rfl)
  | sigma hb_le _hf_le
  rename_i fpp_fun bpp _xx
  have hbpp_type := (WShape.HasTypeSigma.def.1 (WShape.HasType.sigma_l.1 h_tyT.isType).1).1.isType
  have ⟨_, _, mem_app⟩ := fpp_fun.app_eq m'_w.fst
  have hba_type : (fpp_fun.app m'_w.fst).HasType .type :=
    (WShape.HasTypeSigma.def.1 (WShape.HasType.sigma_l.1 h_tyT.isType).1).2 _ _ mem_app
  have h_aT' : LE_Interp ρ (bpp.sigma fpp_fun).T (.sigma A B) :=
    .sigma hb_T _hb'_T _hd _hf le_a_sig
  have hxT : LE_Interp ρ m'_w.fst.T (.fst p) := .fst' h_pT
  have hf_inst : LE_Interp ρ (fpp_fun.app m'_w.fst).T (B.inst (.fst p)) :=
    h_aT'.sigma_inv.2 hxT
  refine ⟨fun le_msf => ?_, fun le_msn => ?_⟩
  · refine ⟨m'_w.fst.T, bpp.T, ?_, .fst' h_pT, hb_T.mono hb_le, (hbpp_type.fst_proj h_tyT).T⟩
    exact le_msf.trans <| TShape.fst_mono sleT
  · refine ⟨m'_w.snd.T, (fpp_fun.app m'_w.fst).T, ?_, .snd' h_pT, hf_inst,
      (hba_type.snd_proj h_tyT).T⟩
    exact le_msn.trans <| TShape.snd_mono sleT

theorem StrongSound.uniq : StrongSound Γ M A → StrongSound Γ M B → SoundEq Γ A B := by
  induction M generalizing Γ A B with refine uniq_of_core fun {A B} H1 H2 => ?_
  | bvar => let .bvar a1 := H1; let .bvar b1 := H2; exact a1.uniq b1 ▸ .rfl
  | sort => let .sort := H1; let .sort := H2; exact .rfl
  | app _ _ ihf =>
    let .app a1 a2 a3 := H1; let .app b1 b2 b3 := H2
    exact .inst a3.sound a1 ((ihf a2 b2).forallE_inv a1 b1).2
  | lam _ _ _ ihe => let .lam a1 a2 := H1; let .lam b1 b2 := H2; exact .forallE a1 .rfl (ihe a2 b2)
  | forallE _ _ ihA ihB =>
    let .forallE a1 a2 := H1; let .forallE b1 b2 := H2
    simp only [SoundEq.sort]
    exact SoundEq.sort.1 (ihB a2 b2)
  | sigma => let .sigma .. := H1; let .sigma .. := H2; exact .rfl
  | pair => let .pair .. := H1; let .pair .. := H2; exact .rfl
  | unit => let .unit := H1; let .unit := H2; exact .rfl
  | star => let .star := H1; let .star := H2; exact .rfl
  | fst _ ihP =>
    let .fst a1 a2 a3 := H1; let .fst b1 b2 b3 := H2
    exact ((ihP a3 b3).sigma_inv a1 b1).1
  | snd _ ihP =>
    let .snd a1 a2 a3 := H1; let .snd b1 b2 b3 := H2
    have ⟨_, c2⟩ := (ihP a3 b3).sigma_inv a1 b1
    exact .inst (SoundTy.fstsnd a3.sound).1 a1 c2
  | nat => let .nat := H1; let .nat := H2; exact .rfl
  | zero => let .zero := H1; let .zero := H2; exact .rfl
  | succ => let .succ .. := H1; let .succ .. := H2; exact .rfl
  | natCase => let .natCase .. := H1; let .natCase .. := H2; exact .rfl
  | Y _ _ => let .Y _ _ := H1; let .Y _ _ := H2; exact .rfl
  | id => let .id .. := H1; let .id .. := H2; exact .rfl
  | refl _ ih =>
    let .refl _ a2 := H1; let .refl _ b2 := H2
    exact SoundEq.id (ih a2 b2) .rfl .rfl
  | tr _ _ _ _ _ _ _ _ _ _ _ ih_h =>
    let .tr _ _ _ _ _ a6 := H1
    let .tr _ _ _ _ _ b6 := H2
    have ⟨_, _, Hb⟩ := SoundEq.id_inv (ih_h a6 b6)
    exact SoundEq.inst_arg Hb

theorem LE_Interp.strongSound (H : Γ ⊢ M ≡ N : A) : StrongSoundEq Γ M N A := by
  induction H with
  | @bvar _ i A _ h h2 ih => exact .rfl ⟨.bvar h, .bvar h, .rfl⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | trans' _ _ ih1 ih2 =>
    have ⟨a2, a3, a4, a6, a7⟩ := ih1; have ⟨b2, _, b5, b6, b7⟩ := ih2
    have := ih2.left.uniq ih1.right
    exact ⟨a2.trans b2, a3, b5.defeq_r this, b6, b7.trans this⟩
  | @sort _ l =>
    refine .rfl ⟨fun _ _ W _ h => ?_, .sort, .rfl⟩
    generalize eq : Term.sort l = M at h
    induction h with cases eq
    | bot => exact .mk .rfl .bot .bot (.bot_T' <| .bot .sort)
    | sort h1 => exact .mk h1 (.sort .rfl) (.sort .rfl) (by simpa using .sort)
  | appDF _ _ _ _ _ ihA _ ih1 ih2 ih3 =>
    refine .mk' (.app ihA.left.sound ih1.left ih2.left) .rfl
      (.app ihA.left.sound ih1.right ih2.right) ih3.sound.symm fun _ _ W m => ?_
    by_cases hm : m ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩,
      sound_app (ih1.left.sound W) (InterpTyped.hsort (ih3.left.sound W))⟩ <;>
      cases h with | bot => cases hm TShape.bot_le' | app h1 h2 h3
    · exact .app ((ih1.sound W).1 h1) ((ih2.sound W).1 h2) h3
    · exact .app ((ih1.sound W).2 h1) ((ih2.sound W).2 h2) h3
  | lamDF _ _ _ _ _ ih1 _ ih2 ih3 _ =>
    refine .mk' (.lam ih1.left.sound ih2.left) .rfl (.lam ih1.right.sound ih3.right)
      (.symm <| .forallE ih1.left.sound ih1.sound .rfl) fun _ _ W m => ?_
    by_cases hm : m ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩,
      sound_lam (InterpTyped.hsort (ih1.left.sound W)) fun h1 h2 =>
      (ih2.left.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h1 h2))⟩ <;>
      cases h with | bot => cases hm TShape.bot_le' | lam h1 h2 h3 h4
    · refine .lam ((ih1.sound W).1 h1) h2 (fun _ h => ?_) h4
      exact (ih2.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h1 h.T)).1 (h3 _ h)
    · refine .lam ((ih1.sound W).2 h1) h2 (fun _ h => ?_) h4
      refine (ih2.sound (W.cons ?_ ((ih1.sound W).2 h1) h.T)).2 (h3 _ h)
      exact InterpTyped.hsort (ih1.left.sound W)
  | forallEDF _ _ _ ih1 ih2 ih3 =>
    refine .mk' (.forallE ih1.left ih2.left) .rfl
      (.forallE ih1.right ih3.right) .rfl fun _ _ W m => ?_
    by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩,
      sound_forallE (InterpTyped.hsort' (ih1.left.sound W)) fun h1 h2 =>
      (ih2.left.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h1 h2))⟩ <;>
      try cases h with | bot => cases hm TShape.bot_le' | forallE h1 h2 h3 h4 h5
    · refine .forallE ((ih1.sound W).1 h1) ((ih1.sound W).1 h2) h3 (fun _ h => ?_) h5
      exact (ih2.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h2 h.T)).1 (h4 _ h)
    · refine .forallE ((ih1.sound W).2 h1) ((ih1.sound W).2 h2) h3 (fun _ h => ?_) h5
      refine (ih2.sound (W.cons ?_ ((ih1.sound W).2 h2) h.T)).2 (h4 _ h)
      exact InterpTyped.hsort (ih1.left.sound W)
  | defeqDF h1 h2 ih1 ih2 =>
    have ⟨a2, a3, a4⟩ := ih2.left
    have ⟨b2, b3, b4⟩ := ih2.right
    refine ⟨ih2.sound, ?_, ?_⟩
    · exact ⟨a2.defeq_r ih1.sound, a3, a4.trans ih1.sound⟩
    · exact ⟨ih2.right.sound.defeq_r ih1.sound, b3, b4.trans ih1.sound⟩
  | beta _ _ _ _ _ _ ih1 ih2 ih3 ih4 =>
    refine ⟨fun _ _ W m => ?_, ih3.left, ih4.left⟩
    by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ (sound_bot (A := default)).1
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases h with | bot => cases hm TShape.bot_le' | @app _ n₁ _ _ _ _ a h1 h2 h3
      cases h1 with | bot => cases hm (h3.trans TShape.bot_eqv.1) | @lam _ n₂ _ _ f' _ _ h4 h5 h6 h7
      let k := max n₂ n₁; have hk := Nat.max_le.1 (Nat.le_refl k)
      have ⟨_, _, a1, a2, a3, a4⟩ := ih2.left.sound W h2
      obtain ⟨_, b1, b2⟩ := WShapeFun.app_eq (f'.lift k) (a.lift k)
      obtain ⟨a', y', b2', rfl, yb_eq⟩ := (WShapeFun.mem_lift hk.1).1 b2
      obtain ⟨bx', bxle, bx_ht, bapp⟩ := WShape.HasDom.iff.1 h5 a'
      refine LE_Interp.inst.2 ⟨_, ?_, (h2.lift hk.2).mono b1.T⟩
      refine .mono_l (Valuation.LE.push.2 ⟨.rfl, bxle.T.trans (TShape.lift_eqv hk.1).2⟩) ?_
      refine (h6 bx' bx_ht).mono <| h3.trans <| .trans ?_ bapp.T
      rw [TShape.LE.def hk.2 hk.1, WShape.lift_app hk.2]
      have h7' := (TShape.LE.def (Nat.succ_le_succ hk.2) (Nat.succ_le_succ hk.1)).1 h7
      refine (WShape.app_mono_l h7' _).trans ?_
      rw [WShape.lift_lam' hk.1, WShape.lam'_app, yb_eq]
      exact WShape.lift_mono hk.1 (WShapeFun.app_of_mem b2').2
    · have ⟨_, h1, h2⟩ := LE_Interp.inst.1 h
      have ⟨e, a, a1, a2, a3, a4⟩ := ih2.left.sound W h2
      let k := max m.1 (max e.1 a.1); have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
      have := (WShape.HasDom.single (y := m.2.lift k)).2 <| .inl <|
        (TShape.HasType.def hk.2.1 hk.2.2).1 a4
      refine .mono ?_ <| .app' (.lam' (a3.lift hk.2.2) this fun _ hx => ?_) (a2.lift hk.2.1)
      · rw [WShape.lam'_app, WShapeFun.single_app, if_pos .rfl]; exact (TShape.lift_eqv hk.1).2
      · simp [WShapeFun.single_app]; split <;> [rename_i h; exact .bot]
        refine (h1.lift hk.1).mono_l <| Valuation.LE.push.2 ⟨.rfl, a1.trans ?_⟩
        exact (TShape.LE.lift_l hk.2.1).2 h
  | @eta _ F _ _ _ _ ih1 ih2 =>
    refine ⟨fun _ ρ W m => ?_, ih2.left, ih1.left⟩
    by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ (sound_bot (A := default)).1
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have ⟨e, t, h1, h2, h3, h4⟩ := ih2.left.sound W h
      have ht : ¬t ≤ .bot := fun h => hm (h1.trans (h4.bot_r' h))
      cases h2 with
      | bot => cases hm (h1.trans TShape.bot_le')
      | @lam _ n _ _ f' _ _ h2a h2d h2f h2le
      cases h3 with | bot => cases ht TShape.bot_le' | forallE b1 b2 b3 b4 b5
      cases b5.le_forall with | bot b5 => cases ht b5 | forallE b5 b6
      obtain rfl | ⟨n₂, g, rfl, c1⟩ := h4.ty_forallE_inv; · cases hm (h1.trans TShape.bot_le')
      have key {x y} (hmem : (x, y) ∈ f') :
          LE_Interp ρ (WShape.T (n := n+1) (.lam' (WShapeFun.single x y))) F := by
        by_cases hy : y ≤ .bot
        · refine .mono (WShape.LE.T (?_ : _ ≤ .bot)) .bot
          rw [← WShape.lam'_bot, WShape.lam'_le_lam', WShapeFun.single_le]
          exact ⟨_, _, by simp [WShapeFun.mem_bot], WShape.bot_le, hy⟩
        rw [WShape.le_bot] at hy
        obtain ⟨x', x'le, x'ht, x'app⟩ := WShape.HasDom.iff.1 h2d x
        have := (h2f x' x'ht)
          |>.mono_l (Valuation.LE.push.2 ⟨.rfl, x'le.T⟩)
          |>.mono (WShape.LE.T <| (WShapeFun.app_of_mem hmem).2.trans x'app)
        cases this with | bot => cases hy rfl | @app _ n' f _ _ _ a' c1 c2 c3
        cases f using WShape.casesOn' with
        | lam g => ?_
        | _ => cases hy (TShape.le_bot.1 (c3.trans TShape.bot_le'))
        obtain ⟨x'', hle, mem⟩ := WShapeFun.app_eq g a'
        have le₁ := Nat.le_max_left n' n; have le₂ := Nat.le_max_right n' n
        refine (LE_Interp.weak_iff.1 c1).mono ?_
        refine (TShape.LE.def (Nat.succ_le_succ le₂) (Nat.succ_le_succ le₁)).2 ?_
        rw [WShape.lift_lam' le₂, WShapeFun.lift_single le₂, WShape.lam_eq_lam',
          WShape.lift_lam' le₁, WShape.lam'_le_lam', WShapeFun.single_le]
        exact ⟨_, _, (WShapeFun.mem_lift le₁).2 ⟨_, _, mem, rfl, rfl⟩,
          hle.T.trans (LE_Interp.bvar_iff.1 c2), (TShape.LE.def le₂ le₁).1 c3⟩
      have main (l : List (WShape n × WShape n)) (H : ∀ p, p ∈ l → p ∈ f') :
          ∃ g, (∀ z : WShapeFun n, g ≤ z ↔ ∀ x ∈ l, .single x.1 x.2 ≤ z) ∧
            LE_Interp ρ (WShape.T (.lam' g)) F := by
        induction l with | nil => exact ⟨.bot, by simp, WShape.lam'_bot ▸ .bot⟩ | cons p l ih
        obtain ⟨x, y⟩ := p; simp only [List.mem_cons, forall_eq_or_imp] at H
        have ⟨g, a1, a2⟩ := ih H.2
        have hc := (key H.1).compat a2
        have hJ := WShapeFun.Join.mk <| WShape.Compat.lam'.1 <| WShape.Compat.T_iff.2 hc
        refine ⟨_, fun z => (hJ _).trans <| .trans ?_ List.forall_mem_cons.symm, ?_⟩
        · exact and_congr_right' (a1 _)
        · exact (key H.1).join (WShape.Join.lam'.2 hJ).T a2
      have ⟨g, a1, a2⟩ := main f'.elems fun _ => WShapeFun.mem_elems.1
      refine a2.mono (h2le.trans (WShape.lam'_le_lam'.2 ?_).T) |>.mono h1
      refine WShapeFun.LE.def'.2 fun x' y' hmem => WShapeFun.single_le.1 ?_
      exact (a1 _).1 .rfl _ (WShapeFun.mem_elems.2 hmem)
    · have ⟨m', f, a1, a2, a3, a4⟩ := ih1.left.sound W h
      have hm' : ¬m' ≤ .bot := fun h => hm (a1.trans h)
      have hf : ¬f ≤ .bot := fun h => hm' (a4.bot_r' h)
      cases a3 with | bot => cases hf TShape.bot_le' | forallE b1 b2 b3 b4 b5
      cases b5.le_forall with | bot b5 => cases hf b5 | @forallE m _ _ _ _ b5 b6
      obtain rfl | ⟨n₂, g, rfl, c1⟩ := a4.ty_forallE_inv; · cases hm' TShape.bot_le'
      have le_k := Nat.le_max_left n₂ m; have le_m := Nat.le_max_right n₂ m
      refine .mono (WShape.lift_lam' le_k ▸ a1.trans (TShape.lift_eqv (Nat.succ_le_succ le_k)).2) <|
        .lam' ((b1.mono b5).lift (Nat.le_max_right ..)) c1.2.1 fun _ _ => ?_
      simpa only [WShape.lift_lam' le_k, WShape.lam'_app] using
        (a2.lift (Nat.succ_le_succ le_k)).weak.app' .bvar0
  | sigmaDF _ _ _ ih1 ih2 ih3 =>
    refine .mk' (.sigma ih1.left ih2.left) .rfl
      (.sigma ih1.right ih3.right) .rfl fun _ _ W m => ?_
    by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩,
      sound_sigma (InterpTyped.hsort' (ih1.left.sound W)) fun h1 h2 =>
      (ih2.left.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h1 h2))⟩ <;>
      try cases h with | bot => cases hm TShape.bot_le' | sigma h1 h2 h3 h4 h5
    · refine .sigma ((ih1.sound W).1 h1) ((ih1.sound W).1 h2) h3 (fun _ h => ?_) h5
      exact (ih2.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h2 h.T)).1 (h4 _ h)
    · refine .sigma ((ih1.sound W).2 h1) ((ih1.sound W).2 h2) h3 (fun _ h => ?_) h5
      refine (ih2.sound (W.cons ?_ ((ih1.sound W).2 h2) h.T)).2 (h4 _ h)
      exact InterpTyped.hsort (ih1.left.sound W)
  | pairDF _ _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 _ =>
    refine .mk' (.pair ih1.left.sound ih2.left.sound ih4.left ih5.left) .rfl
      (.pair ih1.right.sound ih3.right.sound (ih4.right.defeq_r ih1.sound)
        ((ih5.right.defeq_r ih6.sound)))
      (.symm <| .sigma ih1.left.sound ih1.sound ih2.sound) fun _ _ W m => ?_
    by_cases hm : m ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩,
      sound_pair
        (fun h1 h2 => InterpTyped.hsort
          (ih2.left.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h1 h2)))
        (ih4.left.sound W)
        (ih5.left.sound W)⟩ <;>
      cases h with | bot => cases hm TShape.bot_le' | pair h1 h2 h3
    · exact .pair ((ih4.sound W).1 h1) ((ih5.sound W).1 h2) h3
    · exact .pair ((ih4.sound W).2 h1) ((ih5.sound W).2 h2) h3
  | fstDF _ _ _ ih1 ih2 ih3 =>
    refine .mk' (.fst ih1.left.sound ih2.left.sound ih3.left) .rfl
      (.fst ih1.right.sound ih2.right.sound ih3.right) .rfl fun _ _ W m => ?_
    by_cases hm : m ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, (SoundTy.fstsnd ih3.left.sound).1 W⟩ <;>
      cases h with | bot => cases hm TShape.bot_le' | fst h1 h2
    · exact .fst ((ih3.sound W).1 h1) h2
    · exact .fst ((ih3.sound W).2 h1) h2
  | sndDF _ _ _ _ ih1 ih2 ih3 ih4 =>
    refine .mk' (.snd ih1.left.sound ih2.left.sound ih3.left) .rfl
      (.snd ih1.right.sound ih2.right.sound ih3.right) ih4.sound.symm fun _ _ W m => ?_
    by_cases hm : m ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, (SoundTy.fstsnd ih3.left.sound).2 W⟩ <;>
      cases h with | bot => cases hm TShape.bot_le' | snd h1 h2
    · exact .snd ((ih3.sound W).1 h1) h2
    · exact .snd ((ih3.sound W).2 h1) h2
  | @pair_fst _ A u B v a b _ _ _ _ _ _ _ ih3 _ ih5 =>
    refine ⟨fun _ ρ W m => ?_, ih5.left, ih3.left⟩
    by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ (sound_bot (A := default)).1
    refine ⟨fun h => ?_, fun h => ?_⟩
    · -- Forward: LE_Interp m (.fst (.pair A B a b)) → LE_Interp m a
      cases h with | bot => cases hm TShape.bot_le' | fst hsT le_msf
      cases hsT with | bot => cases hm (le_msf.trans TShape.bot_le') | pair h_x _h_y le_s
      rename_i xV yV
      refine h_x.mono <| le_msf.trans <| (TShape.fst_mono le_s).trans ?_
      show ((WShape.pair' xV yV).fst).T ≤ xV.T
      unfold WShape.pair'
      split
      · exact .rfl
      · simp; exact TShape.bot_le'
    · -- Backward: LE_Interp m a → LE_Interp m (.fst (.pair A B a b))
      by_cases hxbot : m.2 ≤ .bot; · cases hm (TShape.le_bot.2 (WShape.le_bot.1 hxbot))
      have h_fst_T : LE_Interp ρ ((WShape.pair' m.2 (WShape.bot : WShape m.1)).fst).T
          (.fst (.pair A B a b)) := .fst' (.pair' h .bot)
      have hfst_eq : (WShape.pair' m.2 (WShape.bot : WShape m.1)).fst = m.2 := by
        unfold WShape.pair'; split; · rfl
        rename_i hcond; simp at hcond; exact absurd hcond.1 hxbot
      rw [hfst_eq] at h_fst_T
      exact h_fst_T
  | @pair_snd _ A u B v a b _ _ _ _ _ _ _ _ ih4 ih5 =>
    refine ⟨fun _ ρ W m => ?_, ih5.left, ih4.left⟩
    by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ (sound_bot (A := default)).1
    refine ⟨fun h => ?_, fun h => ?_⟩
    · -- Forward: LE_Interp m (.snd (.pair A B a b)) → LE_Interp m b
      cases h with | bot => cases hm TShape.bot_le' | snd hsT le_msn
      cases hsT with | bot => cases hm (le_msn.trans TShape.bot_le') | pair _h_x h_y le_s
      rename_i xV yV
      refine h_y.mono <| le_msn.trans <| (TShape.snd_mono le_s).trans ?_
      show ((WShape.pair' xV yV).snd).T ≤ yV.T
      unfold WShape.pair'; split; · exact .rfl
      simp; exact TShape.bot_le'
    · -- Backward: LE_Interp m b → LE_Interp m (.snd (.pair A B a b))
      by_cases hybot : m.2 ≤ .bot; · cases hm (TShape.le_bot.2 (WShape.le_bot.1 hybot))
      have h_snd_T : LE_Interp ρ ((WShape.pair' .bot m.2).snd).T (.snd (.pair A B a b)) :=
        .snd' (.pair' .bot h)
      have hsnd_eq : (WShape.pair' (WShape.bot : WShape m.1) m.2).snd = m.2 := by
        unfold WShape.pair'; split; · rfl
        rename_i hcond; simp at hcond; cases hybot hcond.2
      rw [hsnd_eq] at h_snd_T
      exact h_snd_T
  | @fst_snd _ p A B _ _ ih1 ih2 =>
    refine ⟨fun _ ρ W m => ?_, ih2.left, ih1.left⟩
    by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ (sound_bot (A := default)).1
    refine ⟨fun h => ?_, fun h => ?_⟩
    · -- Forward: LE_Interp m (.pair A B (.fst p) (.snd p)) → LE_Interp m p
      cases h with | bot => cases hm TShape.bot_le' | pair h_x h_y le_p
      rename_i nxy xV yV
      -- h_x : LE_Interp ρ xV.T (.fst p), h_y : LE_Interp ρ yV.T (.snd p)
      -- We pick one of {h_x, h_y} to saturate via ih1. If both project from p,
      -- saturate either; their joins give the same bound on m. We need at least
      -- one non-bot to extract a p-interpretation; the both-bot case is ruled
      -- out by `hm` since (.bot.pair' .bot).T = .bot.T.
      -- For uniformity, dispatch on yV ≤ .bot (which is the "pair-bound on snd" side).
      cases h_x with
      | bot =>
        -- xV unified to .bot (at level nxy). Need yV-side info via h_y.
        cases h_y with
        | bot => refine (hm <| le_p.trans ?_).elim; exact WShape.pair'_bot_bot ▸ TShape.bot_le'
        | snd hsy le_y
        rename_i ny sy
        -- Saturate hsy via ih1 → pair shape sy_w via sigma_r → m ≤ sy_w.T.
        have ⟨nk, sy_w, a_w, _, sy_T_le, h_sy_w_li, h_aw_li, h_sy_w_ty⟩ :=
          (ih1.left.sound W hsy).out
        -- Handle bot-cases of saturation: sy_w = .bot ⇒ yV ≤ .bot ⇒ pair' = .bot
        -- ⇒ m ≤ .bot, contradiction
        by_cases hyV_bot : yV ≤ .bot
        · refine (hm <| le_p.trans ?_).elim
          have hyV_eq : yV = WShape.bot := WShape.le_bot.1 hyV_bot
          rw [hyV_eq]; simp [WShape.pair'_bot_bot]; exact TShape.bot_le'
        -- yV not bot ⇒ pair' = .pair .bot yV (.inr _)
        -- From hsy's saturation: get sigma structure of sy_w
        cases h_aw_li with
        | bot =>
          -- a_w = .bot, sy_w = .bot, sy ≤ .bot, sy.snd ≤ .bot, yV ≤ .bot ⇒ contradiction
          exfalso; apply hyV_bot
          have hsy_w_bot : sy_w = .bot := WShape.HasType.bot_r h_sy_w_ty
          have hsy_T_bot : sy.T ≤ TShape.bot :=
            sy_T_le.trans (hsy_w_bot ▸ TShape.bot_le')
          have : sy = WShape.bot := TShape.le_bot.1 hsy_T_bot
          have : sy.snd ≤ WShape.bot := this ▸ WShape.le_bot.2 rfl
          exact WShape.le_bot.2 (TShape.le_bot.1
            ((le_y.trans this.T).trans TShape.bot_le'))
        | sigma _ _ _ _ le_a_sig
        cases le_a_sig.le_sigma with
        | bot ha_bot =>
          exfalso; apply hyV_bot
          cases show a_w = WShape.bot from TShape.le_bot.1 ha_bot
          have hsy_w_bot : sy_w = .bot := WShape.HasType.bot_r h_sy_w_ty
          have hsy_T_bot : sy.T ≤ TShape.bot :=
            sy_T_le.trans (hsy_w_bot ▸ TShape.bot_le')
          have : sy = WShape.bot := TShape.le_bot.1 hsy_T_bot
          have : sy.snd ≤ WShape.bot := this ▸ WShape.le_bot.2 rfl
          exact WShape.le_bot.2 (TShape.le_bot.1
          ((le_y.trans this.T).trans TShape.bot_le'))
        | sigma
        rename_i fpp_fun bpp _xx
        obtain hbot | ⟨sxv, syv, sh, sy_w_eq, _⟩ := WShape.HasType.sigma_r h_sy_w_ty
        · exfalso; apply hyV_bot
          have hsy_T_bot : sy.T ≤ TShape.bot :=
            sy_T_le.trans (hbot ▸ TShape.bot_le')
          have : sy = WShape.bot := TShape.le_bot.1 hsy_T_bot
          have : sy.snd ≤ WShape.bot := this ▸ WShape.le_bot.2 rfl
          exact WShape.le_bot.2 (TShape.le_bot.1
            ((le_y.trans this.T).trans TShape.bot_le'))
        · subst sy_w_eq
          refine h_sy_w_li.mono <| le_p.trans <| ?_
          have hyV_le_syv : yV.T ≤ syv.T := le_y.trans <| by
            show sy.snd.T ≤ (WShape.pair sxv syv sh).snd.T
            exact TShape.snd_mono sy_T_le
          rw [show WShape.pair sxv syv sh = WShape.pair' sxv syv from
            WShape.pair_eq_pair']
          exact TShape.pair'_le_pair' TShape.bot_le' hyV_le_syv
      | fst hsx le_x
      rename_i nx sx
      cases h_y with
      | bot =>
        -- Mirror: yV unified to .bot, use hsx-saturation
        by_cases hxV_bot : xV ≤ .bot
        · exact (hm <| le_p.trans <| by
            have hxV_eq : xV = WShape.bot := WShape.le_bot.1 hxV_bot
            rw [hxV_eq]; simp [WShape.pair'_bot_bot]; exact TShape.bot_le').elim
        have ⟨nk, sx_w, a_w, _, sx_T_le, h_sx_w_li, h_aw_li, h_sx_w_ty⟩ :=
          (ih1.left.sound W hsx).out
        have hxV_to_fst : xV.T ≤ sx.fst.T := le_x
        cases h_aw_li with
        | bot =>
          exfalso; apply hxV_bot
          have hsx_w_bot : sx_w = .bot := WShape.HasType.bot_r h_sx_w_ty
          have hsx_T_bot : sx.T ≤ TShape.bot :=
            sx_T_le.trans (hsx_w_bot ▸ TShape.bot_le')
          have : sx = WShape.bot := TShape.le_bot.1 hsx_T_bot
          have : sx.fst ≤ WShape.bot := this ▸ WShape.le_bot.2 rfl
          exact WShape.le_bot.2 (TShape.le_bot.1
            ((hxV_to_fst.trans this.T).trans TShape.bot_le'))
        | sigma _ _ _ _ le_a_sig
        cases le_a_sig.le_sigma with
        | bot ha_bot =>
          exfalso; apply hxV_bot
          cases show a_w = WShape.bot from TShape.le_bot.1 ha_bot
          have hsx_w_bot : sx_w = .bot := WShape.HasType.bot_r h_sx_w_ty
          have hsx_T_bot : sx.T ≤ TShape.bot :=
            sx_T_le.trans (hsx_w_bot ▸ TShape.bot_le')
          have : sx = WShape.bot := TShape.le_bot.1 hsx_T_bot
          have : sx.fst ≤ WShape.bot := this ▸ WShape.le_bot.2 rfl
          exact WShape.le_bot.2 (TShape.le_bot.1
            ((hxV_to_fst.trans this.T).trans TShape.bot_le'))
        | sigma
        obtain hbot | ⟨sxv, syv, sh, sx_w_eq, _⟩ := h_sx_w_ty.sigma_r
        · exfalso; apply hxV_bot
          have hsx_T_bot : sx.T ≤ TShape.bot :=
            sx_T_le.trans (hbot ▸ TShape.bot_le')
          have : sx = WShape.bot := TShape.le_bot.1 hsx_T_bot
          have : sx.fst ≤ WShape.bot := this ▸ WShape.le_bot.2 rfl
          exact WShape.le_bot.2 (TShape.le_bot.1
            ((hxV_to_fst.trans this.T).trans TShape.bot_le'))
        · subst sx_w_eq
          refine h_sx_w_li.mono <| le_p.trans <| ?_
          have hxV_le_sxv : xV.T ≤ sxv.T := hxV_to_fst.trans <| by
            show sx.fst.T ≤ (WShape.pair sxv syv sh).fst.T
            exact TShape.fst_mono sx_T_le
          rw [show WShape.pair sxv syv sh = WShape.pair' sxv syv from
            WShape.pair_eq_pair']
          exact TShape.pair'_le_pair' hxV_le_sxv TShape.bot_le'
      | snd hsy le_y
      rename_i ny sy
      -- Both projections at p. Join their interpretations and saturate via ih1.
      have hsj_li : LE_Interp ρ (sx.T.join sy.T) p := hsx.join' hsy
      have ⟨nk, sj_w, a_w, _, sj_T_le, h_sj_w_li, h_aw_li, h_sj_w_ty⟩ :=
        (ih1.left.sound W hsj_li).out
      have hsx_le_sj : sx.T ≤ (sx.T.join sy.T) :=
        (TShape.Join.mk (hsx.compat hsy)).le.1
      have hsy_le_sj : sy.T ≤ (sx.T.join sy.T) :=
        (TShape.Join.mk (hsx.compat hsy)).le.2
      cases h_aw_li with
      | bot =>
        -- sj_w = .bot ⇒ sj ≤ .bot ⇒ sx ≤ .bot ⇒ xV ≤ .bot, similarly yV ≤ .bot
        -- ⇒ pair' ≤ .bot ⇒ m ≤ .bot, contradicts hm
        exfalso; apply hm
        have hsj_w_bot : sj_w = .bot := WShape.HasType.bot_r h_sj_w_ty
        have hsj_T_bot : (sx.T.join sy.T) ≤ TShape.bot :=
          sj_T_le.trans (hsj_w_bot ▸ TShape.bot_le')
        have hsx_bot : sx.T ≤ TShape.bot := hsx_le_sj.trans hsj_T_bot
        have hsy_bot : sy.T ≤ TShape.bot := hsy_le_sj.trans hsj_T_bot
        have : sx = WShape.bot := TShape.le_bot.1 hsx_bot
        have hsx_fst_bot : sx.fst ≤ WShape.bot := this ▸ WShape.le_bot.2 rfl
        have : sy = WShape.bot := TShape.le_bot.1 hsy_bot
        have hsy_snd_bot : sy.snd ≤ WShape.bot := this ▸ WShape.le_bot.2 rfl
        have hxV_bot : xV.T ≤ TShape.bot :=
          ((le_x.trans hsx_fst_bot.T).trans TShape.bot_le')
        have hyV_bot : yV.T ≤ TShape.bot :=
          ((le_y.trans hsy_snd_bot.T).trans TShape.bot_le')
        have hxV_w : xV ≤ WShape.bot := WShape.le_bot.2 (TShape.le_bot.1 hxV_bot)
        have hyV_w : yV ≤ WShape.bot := WShape.le_bot.2 (TShape.le_bot.1 hyV_bot)
        refine le_p.trans ?_
        rw [show xV = WShape.bot from WShape.le_bot.1 hxV_w,
            show yV = WShape.bot from WShape.le_bot.1 hyV_w]
        simp [WShape.pair'_bot_bot]
        exact TShape.bot_le'
      | sigma _ _ _ _ le_a_sig
      cases le_a_sig.le_sigma with
      | bot ha_bot =>
        exfalso; apply hm
        cases show a_w = WShape.bot from TShape.le_bot.1 ha_bot
        have hsj_w_bot : sj_w = .bot := WShape.HasType.bot_r h_sj_w_ty
        have hsj_T_bot : (sx.T.join sy.T) ≤ TShape.bot :=
          sj_T_le.trans (hsj_w_bot ▸ TShape.bot_le')
        have hsx_bot : sx.T ≤ TShape.bot := hsx_le_sj.trans hsj_T_bot
        have hsy_bot : sy.T ≤ TShape.bot := hsy_le_sj.trans hsj_T_bot
        have : sx = WShape.bot := TShape.le_bot.1 hsx_bot
        have hsx_fst_bot : sx.fst ≤ WShape.bot := this ▸ WShape.le_bot.2 rfl
        have : sy = WShape.bot := TShape.le_bot.1 hsy_bot
        have hsy_snd_bot : sy.snd ≤ WShape.bot := this ▸ WShape.le_bot.2 rfl
        have hxV_bot : xV.T ≤ TShape.bot :=
          ((le_x.trans hsx_fst_bot.T).trans TShape.bot_le')
        have hyV_bot : yV.T ≤ TShape.bot :=
          ((le_y.trans hsy_snd_bot.T).trans TShape.bot_le')
        have hxV_w : xV ≤ WShape.bot := WShape.le_bot.2 (TShape.le_bot.1 hxV_bot)
        have hyV_w : yV ≤ WShape.bot := WShape.le_bot.2 (TShape.le_bot.1 hyV_bot)
        refine le_p.trans ?_
        rw [show xV = WShape.bot from WShape.le_bot.1 hxV_w,
            show yV = WShape.bot from WShape.le_bot.1 hyV_w]
        simp [WShape.pair'_bot_bot]
        exact TShape.bot_le'
      | sigma
      obtain hbot | ⟨sxv, syv, sh, sj_w_eq, _⟩ := h_sj_w_ty.sigma_r
      · exfalso; apply hm
        have hsj_T_bot : (sx.T.join sy.T) ≤ TShape.bot :=
          sj_T_le.trans (hbot ▸ TShape.bot_le')
        have hsx_bot : sx.T ≤ TShape.bot := hsx_le_sj.trans hsj_T_bot
        have hsy_bot : sy.T ≤ TShape.bot := hsy_le_sj.trans hsj_T_bot
        have : sx = WShape.bot := TShape.le_bot.1 hsx_bot
        have hsx_fst_bot : sx.fst ≤ WShape.bot := this ▸ WShape.le_bot.2 rfl
        have : sy = WShape.bot := TShape.le_bot.1 hsy_bot
        have hsy_snd_bot : sy.snd ≤ WShape.bot := this ▸ WShape.le_bot.2 rfl
        have hxV_bot : xV.T ≤ TShape.bot :=
          ((le_x.trans hsx_fst_bot.T).trans TShape.bot_le')
        have hyV_bot : yV.T ≤ TShape.bot :=
          ((le_y.trans hsy_snd_bot.T).trans TShape.bot_le')
        have hxV_w : xV ≤ WShape.bot := WShape.le_bot.2 (TShape.le_bot.1 hxV_bot)
        have hyV_w : yV ≤ WShape.bot := WShape.le_bot.2 (TShape.le_bot.1 hyV_bot)
        refine le_p.trans ?_
        rw [show xV = WShape.bot from WShape.le_bot.1 hxV_w,
            show yV = WShape.bot from WShape.le_bot.1 hyV_w]
        simp [WShape.pair'_bot_bot]
        exact TShape.bot_le'
      · subst sj_w_eq
        refine h_sj_w_li.mono <| le_p.trans <| ?_
        have hxV_le_sxv : xV.T ≤ sxv.T := by
          have hsx_to_sj_w : sx.T ≤ (WShape.pair sxv syv sh).T :=
            hsx_le_sj.trans sj_T_le
          have := TShape.fst_mono hsx_to_sj_w
          rw [WShape.pair_fst] at this
          exact le_x.trans this
        have hyV_le_syv : yV.T ≤ syv.T := by
          have hsy_to_sj_w : sy.T ≤ (WShape.pair sxv syv sh).T :=
            hsy_le_sj.trans sj_T_le
          have := TShape.snd_mono hsy_to_sj_w
          rw [WShape.pair_snd] at this
          exact le_y.trans this
        rw [show WShape.pair sxv syv sh = WShape.pair' sxv syv from
          WShape.pair_eq_pair']
        exact TShape.pair'_le_pair' hxV_le_sxv hyV_le_syv
    · -- Backward: LE_Interp m p → LE_Interp m (.pair A B (.fst p) (.snd p))
      have ⟨nk, m_w, a_w, _, sleT, h_pT, h_aT, h_tyT⟩ := (ih1.left.sound W h).out
      have hm_not_bot : ¬m_w ≤ .bot := by
        intro hbot
        cases WShape.le_bot.1 hbot
        exact hm (sleT.trans TShape.bot_le')
      cases h_aT with
      | bot => cases hm_not_bot (WShape.HasType.bot_r h_tyT ▸ WShape.le_bot.2 rfl)
      | sigma _ _ _ _ le_a_sig
      cases le_a_sig.le_sigma with
      | bot ha_bot =>
        cases show a_w = WShape.bot from TShape.le_bot.1 ha_bot
        exact (hm_not_bot (WShape.HasType.bot_r h_tyT ▸ WShape.le_bot.2 rfl)).elim
      | sigma
      rename_i fpp_fun bpp _xx
      obtain hbot | ⟨mxV, myV, mh, rfl, _⟩ := WShape.HasType.sigma_r h_tyT
      · exact (hm_not_bot (hbot ▸ WShape.le_bot.2 rfl)).elim
      refine LE_Interp.pair (.fst' h_pT) (.snd' h_pT) ?_
      show m ≤ (WShape.pair' mxV myV).T
      have heq : WShape.pair' mxV myV = WShape.pair mxV myV mh := by
        unfold WShape.pair'; rw [dif_pos mh]
      rw [heq]
      exact sleT
  | idDF _ _ _ ihA iha ihb =>
    refine .mk' (.id ihA.left iha.left ihb.left) .rfl
      (.id ihA.right (iha.right.defeq_r ihA.sound) (ihb.right.defeq_r ihA.sound)) .rfl
      fun _ _ W m => ?_
    by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩,
      sound_id (fun ha => ihA.left.sound W ha)
        (fun hx => iha.left.sound W hx) (fun hx => ihb.left.sound W hx)⟩ <;>
      try cases h with | bot => cases hm TShape.bot_le' | id h1 h2 h3 h4
    · exact .id ((ihA.sound W).1 h1) ((iha.sound W).1 h2) ((ihb.sound W).1 h3) h4
    · exact .id ((ihA.sound W).2 h1) ((iha.sound W).2 h2) ((ihb.sound W).2 h3) h4
  | @reflDF Γ A u a a' _hA _ha _h_id ihA iha _ih_id =>
    refine .mk' (.refl ihA.left.sound iha.left) .rfl
      (.refl ihA.left.sound iha.right)
      (SoundEq.id .rfl iha.sound.symm iha.sound.symm) fun _ _ W m => ?_
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩ <;>
      cases h with | bot => exact .bot | refl hv h_le
    · exact .refl ((iha.sound W).1 hv) h_le
    · exact .refl ((iha.sound W).2 hv) h_le
    · rename_i n_v v_w
      have ⟨n_vs, v_sat, A_sat, _, le_v_sat, hv_sat_li, hA_sat_li, hv_sat_ty⟩ :=
        (iha.left.sound W hv).out
      refine ⟨(WShape.refl v_sat : WShape (n_vs + 1)).T,
        (WShape.id A_sat v_sat v_sat : WShape (n_vs + 1)).T, ?_, ?_, ?_, ?_⟩
      · refine h_le.trans ?_
        have hk_v : n_v ≤ max n_v n_vs := Nat.le_max_left ..
        have hk_vs : n_vs ≤ max n_v n_vs := Nat.le_max_right ..
        refine (TShape.LE.def (Nat.succ_le_succ hk_v) (Nat.succ_le_succ hk_vs)).2 ?_
        rw [WShape.lift_refl hk_v, WShape.lift_refl hk_vs]
        exact Shape.refl_le.2 ⟨_, rfl, (TShape.LE.def hk_v hk_vs).1 le_v_sat⟩
      · exact .refl hv_sat_li .rfl
      · exact .id hA_sat_li hv_sat_li hv_sat_li .rfl
      · exact WShape.HasType.T_iff.2 (Shape.HasType.refl
          ⟨⟨hv_sat_ty, hv_sat_ty⟩, hv_sat_ty, Shape.LE.rfl, Shape.LE.rfl⟩)
  | @trDF Γ A A' u a a' b b' C C' v x x' h h' _hA _ha _hb _hC _hC' _hx _hh _hCb _h_id
      ihA iha ihb ihC ihC' ihx ihh ihCb _ih_id =>
    have eq_Cinst : SoundEq Γ (C.inst a) (C'.inst a') :=
      (SoundEq.inst iha.left.sound ihA.left.sound ihC.sound).trans (SoundEq.inst_arg iha.sound)
    refine .mk'
      (.tr ihA.left.sound iha.left.sound ihb.left.sound ihC.left ihx.left ihh.left) .rfl
      (.tr ihA.right.sound (iha.right.defeq_r ihA.sound).sound
        (ihb.right.defeq_r ihA.sound).sound
        ihC'.right
        (ihx.right.defeq_r eq_Cinst)
        (ihh.right.defeq_r (SoundEq.id ihA.sound iha.sound ihb.sound)))
      ihCb.sound.symm
      fun _ ρ W m => ?_
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
    · cases h with | bot => exact .bot | tr le hx hva hvb hvA hvv hc_C hty hH_refl
      refine .tr le ((ihx.sound W).1 hx) ((iha.sound W).1 hva)
        ((ihb.sound W).1 hvb) ((ihA.sound W).1 hvA) hvv ?_ hty ((ihh.sound W).1 hH_refl)
      exact (ihC.sound (W.cons (InterpTyped.hsort (ihA.left.sound W)) hvA hvv)).1 hc_C
    · cases h with | bot => exact .bot | tr le hx hva hvb hvA hvv hc_C hty hH_refl
      refine .tr le ((ihx.sound W).2 hx) ((iha.sound W).2 hva)
        ((ihb.sound W).2 hvb) ((ihA.sound W).2 hvA) hvv ?_ hty ((ihh.sound W).2 hH_refl)
      exact (ihC'.sound (W.cons (InterpTyped.hsort (ihA.right.sound W)) hvA hvv)).2 hc_C
    · by_cases hm : m ≤ .bot
      · exact TShape.le_bot'.1 hm ▸ .bot
      cases h with
      | bot => cases hm TShape.bot_le'
      | tr le hx hva hvb hvA hvv hc_C hty hH_refl
      refine ⟨_, _, le, ?_, LE_Interp.inst.2 ⟨_, hc_C, hvb⟩, hty⟩
      exact .tr .rfl hx hva hvb hvA hvv hc_C hty hH_refl
  | @tr_refl _ A u a C v x _hA _ha _hC _hx _h_tr ihA iha ihC ihx ih_tr =>
    obtain ⟨_, ih_tr_core, ih_tr_eq⟩ := ih_tr.left
    obtain ⟨_, ihx_core, ihx_eq⟩ := ihx.left
    refine .mk' ih_tr_core ih_tr_eq ihx_core ihx_eq fun _ ρ W m => ?_
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
    · cases h with | bot => exact .bot | tr le hx => exact hx.mono le
    · have ⟨m_sat, a_w, le_m_sat, hm_x_sat, ha_C, hty_x⟩ := ihx.left.sound W h
      have ⟨vb, hc_C, hvb⟩ := LE_Interp.inst.1 ha_C
      have ⟨m_sat_a, a_sat_A, le_a, hm_sat_a, ha_sat_A, hm_sat_ty⟩ := iha.left.sound W hvb
      exact .tr le_m_sat hm_x_sat hm_sat_a hm_sat_a ha_sat_A hm_sat_ty
        (hc_C.mono_l (Valuation.LE.push.2 ⟨.rfl, le_a⟩)) hty_x (.refl hm_sat_a .rfl)
    · cases h with | bot => exact .bot | tr le hx
      have ⟨m', a_w, le_m, hm_x, ha_C, hty⟩ := ihx.left.sound W (hx.mono le)
      have ⟨vb, hc_C, hvb⟩ := LE_Interp.inst.1 ha_C
      have ⟨m_sat_a, a_sat_A, le_a, hm_sat_a, ha_sat_A, hm_sat_ty⟩ := iha.left.sound W hvb
      refine ⟨m', a_w, le_m, ?_, ha_C, hty⟩
      exact .tr .rfl hm_x hm_sat_a hm_sat_a ha_sat_A hm_sat_ty
        (hc_C.mono_l (Valuation.LE.push.2 ⟨.rfl, le_a⟩)) hty (.refl hm_sat_a .rfl)
  | @proofIrrel _ p h h' _ _ _ ih1 ih2 ih3 =>
    refine ⟨fun _ ρ W m => ?_, ih2.left, ih3.left⟩
    suffices ∀ {h h'}, InterpTyped ρ m h p → LE_Interp ρ m h → LE_Interp ρ m h' from
      ⟨fun h => this (ih2.left.sound W h) h, fun h => this (ih3.left.sound W h) h⟩
    refine fun ⟨_, _, a1, a2, a3, a4⟩ h1 => .mono (?_ : m ≤ .bot) .bot
    have ⟨_, _, b1, b2, b3, b4⟩ := ih1.left.sound W a3
    have b4' := TShape.HasType.mono_r (by simpa using b3.le_sort) .sort b4
    exact a1.trans (b4'.proofIrrel (b4'.mono_r b1 a4))
  | nat => exact .rfl ⟨.nat, .nat, .rfl⟩
  | zero => exact .rfl ⟨.zero, .zero, .rfl⟩
  | succDF _ ih2 =>
    refine .mk' (.succ ih2.left) .rfl (.succ ih2.right) .rfl fun _ _ W m => ?_
    by_cases hm : m ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩ <;>
      cases h with | bot => cases hm TShape.bot_le' | succ hv h1
    · exact .succ ((ih2.sound W).1 hv) h1
    · exact .succ ((ih2.sound W).2 hv) h1
    · exact ih2.left.sound.succ W (.succ hv h1)
  | @natCaseDF Γ C C' v M M' a a' b b' _ _ _ _ _ ihC ihM iha ihb ihCM =>
    refine .mk' (.natCase ihC.left ihM.left iha.left ihb.left) .rfl
      (.natCase ihC.right ihM.right ?_ ?_) ihCM.sound.symm fun _ ρ W m => ?_
    · exact iha.right.defeq_r <| ihC.sound.inst .zero .nat
    · exact ihb.right.defeq_r <| ihC.sound.lift' (.cons (.skip .refl))
        |>.inst (.succ <| .bvar (.zero (ty := .nat))) .nat
    by_cases hm : m ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨?_, fun h => ?_⟩
    · suffices ∀ {C₁ C₂ M₁ M₂ a₁ a₂ b₁ b₂},
          StrongSoundEq Γ M₁ M₂ .nat → StrongSoundEq Γ a₁ a₂ (C.inst .zero) →
          StrongSoundEq (.nat :: Γ) b₁ b₂ ((C.lift' Lift.refl.skip.cons).inst (.succ (.bvar 0))) →
          LE_Interp ρ m (.natCase C₁ M₁ a₁ b₁) → LE_Interp ρ m (.natCase C₂ M₂ a₂ b₂) from
        ⟨this ihM iha ihb, this ihM.symm iha.symm ihb.symm⟩
      intro C₁ C₂ M₁ M₂ a₁ a₂ b₁ b₂ ihM iha ihb h
      cases h with
      | bot => cases hm TShape.bot_le'
      | natCase_zero hM ha => exact .natCase_zero ((ihM.sound W).1 hM) ((iha.sound W).1 ha)
      | @natCase_succ _ n_v v _ _ _ _ _ hM hb =>
        have ⟨nk, m'_w, a_w, _, hle_sv_mw, hM_sat, ha_w_li, hM_ty⟩ := ihM.left.sound W hM |>.out
        obtain ⟨n_a, ha_nat⟩ := ha_w_li.le_nat
        let k := max nk n_a
        have hnk_k2 : nk ≤ k+2 := Nat.le_add_right_of_le (Nat.le_max_left ..)
        have hna_k1 : n_a ≤ k+1 := Nat.le_succ_of_le (Nat.le_max_right ..)
        have hM'_nat : (m'_w.lift (k+2)).HasType .nat := by
          refine .mono_r (WShape.lift_nat hna_k1 ▸ ?_) .nat <| (WShape.HasType.lift hnk_k2).2 hM_ty
          exact (TShape.LE.def hnk_k2 (Nat.succ_le_succ hna_k1)).1 ha_nat
        have hle_sv_lifted := hle_sv_mw.trans (TShape.lift_eqv (a := m'_w.T) hnk_k2).2
        obtain h_bot | h_zero | ⟨v_w, h_eq_succ, h_v_w_ty : v_w.HasType .nat⟩ := hM'_nat.nat_r
        · exact (TShape.succ_not_le_bot (h_bot ▸ hle_sv_lifted)).elim
        · exact (TShape.succ_not_le_zero (h_zero ▸ hle_sv_lifted)).elim
        refine .natCase_succ ((ihM.sound W).1 (h_eq_succ ▸ hM_sat.lift hnk_k2)) ?_
        refine (ihb.sound (W.cons (InterpTyped.hsort (SoundTy.nat W)) .nat' h_v_w_ty.T)).1 ?_
        refine hb.mono_l (Valuation.LE.push.2 ⟨.rfl, ?_⟩)
        exact TShape.succ_le_succ.1 (h_eq_succ ▸ hle_sv_lifted)
    · cases h with
      | bot => cases hm TShape.bot_le'
      | @natCase_zero _ n_h _ _ _ _ _ hM ha =>
        obtain ⟨m_a, a_ty, hle_m_ma, hma_a, ha_ty_Cz, hty_a⟩ := iha.left.sound W ha
        obtain ⟨a_zero, hCa_zero, hazero_zero⟩ := LE_Interp.inst.1 ha_ty_Cz
        obtain ⟨n_z, hazero_le⟩ := hazero_zero.le_zero
        refine ⟨m_a, a_ty, hle_m_ma, .natCase_zero hM hma_a, ?_, hty_a⟩
        exact LE_Interp.inst.2 ⟨a_zero, hCa_zero, hM.mono (hazero_le.trans TShape.zero_eqv)⟩
      | @natCase_succ _ n_v v _ _ _ _ _ hM hb =>
        have ⟨nk, m'_w, a_w, _, hle_sv_mw, hM_sat, ha_w_li, hM_ty⟩ := ihM.left.sound W hM |>.out
        obtain ⟨n_a, ha_nat⟩ := ha_w_li.le_nat
        let k := max nk n_a
        have hnk_k2 : nk ≤ k+2 := Nat.le_add_right_of_le (Nat.le_max_left ..)
        have hna_k1 : n_a ≤ k+1 := Nat.le_succ_of_le (Nat.le_max_right ..)
        have hM'_nat : (m'_w.lift (k+2)).HasType .nat := by
          refine .mono_r (WShape.lift_nat hna_k1 ▸ ?_) .nat <| (WShape.HasType.lift hnk_k2).2 hM_ty
          exact (TShape.LE.def hnk_k2 (Nat.succ_le_succ hna_k1)).1 ha_nat
        have hle_sv_lifted := hle_sv_mw.trans (TShape.lift_eqv hnk_k2).2
        obtain h_bot | h_zero | ⟨v_w, h_eq_succ, h_v_w_ty⟩ := hM'_nat.nat_r
        · exact (TShape.succ_not_le_bot (h_bot ▸ hle_sv_lifted)).elim
        · exact (TShape.succ_not_le_zero (h_zero ▸ hle_sv_lifted)).elim
        have hle_v : v.T ≤ v_w.T := TShape.succ_le_succ.1 (h_eq_succ ▸ hle_sv_lifted)
        have hv_w_nat : (v_w : WShape (k+1)).HasType (WShape.nat : WShape (k+1)) := h_v_w_ty
        have W' := W.cons (InterpTyped.hsort (SoundTy.nat W)) .nat' hv_w_nat.T
        have hb_pushed :=
          hb.mono_l (Valuation.LE.push.2 ⟨.rfl, TShape.succ_le_succ.1 (h_eq_succ ▸ hle_sv_lifted)⟩)
        obtain ⟨m_b, b_ty, hle_m_mb, hmb_b, hb_ty_C_succ, hty_b⟩ := ihb.left.sound W' hb_pushed
        refine ⟨m_b, b_ty, hle_m_mb, .natCase_succ ?_ hmb_b, ?_, hty_b⟩
        · exact h_eq_succ ▸ hM_sat.lift hnk_k2
        obtain ⟨a_succ, hCb_succ, hasucc_succ⟩ := LE_Interp.inst.1 hb_ty_C_succ
        refine LE_Interp.inst.2 ⟨a_succ, ?_, ?_⟩
        · refine (LE_Interp.weak'_iff (.cons (.skip .refl)) ?_).1 hCb_succ; rintro ⟨⟩ <;> rfl
        obtain ⟨n_a_pred, v_pred, hv_pred_interp, ha_succ_le⟩ := hasucc_succ.le_succ
        refine (h_eq_succ ▸ hM_sat.lift hnk_k2).mono (ha_succ_le.trans ?_)
        have lm₁ := Nat.le_max_left n_a_pred (k+1)
        have lm₂ := Nat.le_max_right n_a_pred (k+1)
        rw [TShape.LE.def (Nat.succ_le_succ lm₁) (Nat.succ_le_succ lm₂),
          WShape.lift_succ lm₁, WShape.lift_succ lm₂, WShape.LE.def, ← Shape.succ_le_succ]
        exact (TShape.LE.def lm₁ lm₂).1 (LE_Interp.bvar_iff.1 hv_pred_interp)
  | natCase_zero _ _ _ _ ihC iha ihb ihLHS =>
    refine ⟨fun _ _ W m => ?_, ihLHS.left, iha.left⟩
    by_cases hm : m ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ (sound_bot (A := default)).1
    refine ⟨fun h => ?_, .natCase_zero (n := 0) .zero'⟩
    cases h with
    | bot => cases hm TShape.bot_le'
    | natCase_zero _ ha => exact ha
    | natCase_succ hM => obtain ⟨_, hle⟩ := hM.le_zero; cases TShape.succ_not_le_zero hle
  | @natCase_succ _ C v n a b _ _ _ _ _ _ ihC ihn iha ihb ihLHS ihb_inst =>
    refine ⟨fun _ ρ W m => ?_, ihLHS.left, ihb_inst.left⟩
    by_cases hm : m ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ (sound_bot (A := default)).1
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases h with
      | bot => cases hm TShape.bot_le'
      | natCase_zero hM => let ⟨_, _, _, hle⟩ := hM.le_succ; cases TShape.zero_not_le_succ hle
      | natCase_succ hM hb =>
        let ⟨_, _, hv_hi, hle_sv⟩ := hM.le_succ
        exact LE_Interp.inst.2 ⟨_, hb, hv_hi.mono (TShape.succ_le_succ.1 hle_sv)⟩
    · have ⟨a_val, h_m_b, h_a_n⟩ := LE_Interp.inst.1 h
      have ⟨nk, v_w, a_w, _, hv_le_a, hv_w_li, ha_w_li, hv_w_ty⟩ := ihn.left.sound W h_a_n |>.out
      let ⟨n_a, ha_nat⟩ := ha_w_li.le_nat
      let k := max nk n_a
      have ⟨le₁, le₂⟩ := Nat.max_le.1 (Nat.le_refl k)
      have hk1nk := Nat.le_succ_of_le le₁
      refine .natCase_succ (v := v_w.lift (k+1)) (.succ' (hv_w_li.lift hk1nk)) ?_
      refine h_m_b.mono_l (Valuation.LE.push.2 ⟨.rfl, ?_⟩)
      exact hv_le_a.trans (TShape.lift_eqv (a := v_w.T) hk1nk).2
  | @unit _ r =>
    refine .rfl ⟨fun _ _ W _ h => ?_, .unit, .rfl⟩
    generalize eq : Term.unit r = M at h
    induction h with cases eq | bot => exact .mk .rfl .bot .bot (.bot_T' <| .bot .sort) | unit h1
    exact .mk h1 (.unit .rfl) (.sort .rfl) (by simpa using TShape.HasType.unit (Bool.le_refl r))
  | @star _ r =>
    refine .rfl ⟨fun _ _ W _ h => ?_, .star, .rfl⟩
    cases h with | bot => exact .bot
  | @unit_eta _ e r _ ih =>
    refine ⟨fun _ _ W _ => ⟨fun h => ?_, fun h => ?_⟩,
      ⟨fun _ _ W _ h => ?_, .star, .rfl⟩, ih.left⟩
    · cases h with | bot => exact .bot
    · have ⟨m', a', le, hm', ha', hty⟩ := ih.left.sound W h
      exact LE_Interp.bot.mono <| le.trans <|
        TShape.HasType.eq_bot_of_unit (.mono_r ha'.le_unit (.unit (Bool.le_refl _)) hty)
    · cases h with | bot => exact .bot
  | YDF _ _ _ ihA ihb ihb' =>
    refine ⟨fun _ _ W _ => ⟨fun h => ?_, fun h => ?_⟩, ?_, ?_⟩
    · exact .Y_cong (ihA.left.sound W) ihb.left.sound ihb.sound W h
    · exact .Y_cong (ihA.right.sound W) ihb'.right.sound ihb'.sound.symm W h
    · refine ⟨?_, .Y ihA.left.sound ihb.left, .rfl⟩
      exact fun _ _ W _ h => LE_Interp.sound_Y (ihA.left.sound W) ihb.left.sound W h
    · refine ⟨.defeq_r ihA.sound.symm ?_, .Y ihA.right.sound ihb'.right, ihA.sound.symm⟩
      exact fun _ _ W _ h => LE_Interp.sound_Y (ihA.right.sound W) ihb'.right.sound W h
  | Y_unfold _ _ _ _ ih1 ih2 ih3 ih4 => exact ⟨fun _ _ _ _ => LE_Interp.Y_iff, ih3.left, ih4.left⟩

/-- **Soundness of the interpretation.** Every `IsDefEq` derivation yields,
under any fitting valuation, both
* a semantic iff `LE_Interp ρ m M ↔ LE_Interp ρ m N` (the two sides have
  the same interpretation), and
* a saturation `LE_Interp ρ m M → InterpTyped ρ m M A` (any lower bound
  for `M` is realised at a well-typed shape).

Proved by induction on `H` using the mutual `StrongSound` / `StrongSoundCore`
scaffold (`strongSound`). This is the main output of `Sound.lean` and the
entry point used by `Adequacy.lean` to derive `LR.adequacy`. -/
theorem LE_Interp.sound (H : Γ ⊢ M ≡ N : A) (W : Valuation.Fits Γ₀ Γ ρ) {m} :
    (LE_Interp ρ m M ↔ LE_Interp ρ m N) ∧ (LE_Interp ρ m M → InterpTyped ρ m M A) :=
  ⟨(strongSound H).sound W, (strongSound H).left.sound W⟩
