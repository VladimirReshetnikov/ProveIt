import Std

-- Compatibility notation supplied by Mathlib in the original files.
notation "ℕ" => Nat

/-!
# Standalone object iPRA kernel

Adapted from VladimirReshetnikov/ProveIt at
42c64ff3a9f56f2a9edc1525e75ece3b720c7f77:
ConciseIPRA/Syntax.lean, Deduction.lean, PR.lean, in this order.
The original imports are replaced by `import Std` and concatenation.
Original declarations and proofs are preserved unless explicitly annotated.
See README.md for provenance and the source repository license.
-/

-- BEGIN UPSTREAM Syntax.lean

/-!
# Scoped syntax with simultaneous substitution

A term syntax is a family `T : ℕ → Type`, where `T n` is the type of terms whose
free variables are among `n` de Bruijn indices, together with variables and
capture-avoiding simultaneous substitution satisfying the three monad laws.
The class `Syn` records exactly this.  First-order formulas `Fm T n` with
equality, and their substitution calculus, are developed once for every such
syntax; the bound variable of a quantifier is index `0`.
-/

namespace LeanProofs.ConciseIPRA

/-- Case analysis on `Fin (n + 2)` at index `1`, which `simp` writes as a numeral. -/
@[simp] theorem finCases_one {α : Sort _} {n : ℕ} (a : α) (f : Fin (n + 1) → α) :
    (Fin.cases a f : Fin (n + 2) → α) 1 = f 0 := rfl

/-- A scoped term syntax: variables and simultaneous substitution with the
monad laws. -/
class Syn (T : ℕ → Type) where
  /-- The variable with a given index. -/
  var : {n : ℕ} → Fin n → T n
  /-- Simultaneous capture-avoiding substitution. -/
  subst : {n m : ℕ} → (Fin n → T m) → T n → T m
  subst_var : ∀ {n m : ℕ} (σ : Fin n → T m) (i : Fin n), subst σ (var i) = σ i
  subst_id : ∀ {n : ℕ} (t : T n), subst var t = t
  subst_subst : ∀ {n m k : ℕ} (σ : Fin n → T m) (τ : Fin m → T k) (t : T n),
    subst τ (subst σ t) = subst (fun i => subst τ (σ i)) t

attribute [simp] Syn.subst_var Syn.subst_id

namespace Syn

variable {T : ℕ → Type} [Syn T] {n m k : ℕ}

/-- Weakening by one new variable, which receives index `0`. -/
def shift (t : T n) : T (n + 1) := subst (fun i => var i.succ) t

/-- Lifting of a substitution under one binder. -/
def up (σ : Fin n → T m) : Fin (n + 1) → T (m + 1) :=
  Fin.cases (var 0) (fun i => shift (σ i))

/-- The substitution instantiating variable `0`. -/
def inst (t : T n) : Fin (n + 1) → T n := Fin.cases t var

@[simp] theorem up_zero (σ : Fin n → T m) : up σ 0 = var 0 := rfl

@[simp] theorem up_succ (σ : Fin n → T m) (i : Fin n) : up σ i.succ = shift (σ i) := by
  simp [up]

@[simp] theorem inst_zero (t : T n) : inst t 0 = t := rfl

@[simp] theorem inst_succ (t : T n) (i : Fin n) : inst t i.succ = var i := by
  simp [inst]

@[simp] theorem shift_var (i : Fin n) : shift (var i : T n) = var i.succ := by
  simp [shift]

/-- The substitution replacing variable `0` by a term that may mention it. -/
def repl (s : T (n + 1)) : Fin (n + 1) → T (n + 1) := Fin.cases s (fun i => var i.succ)

@[simp] theorem repl_zero (s : T (n + 1)) : repl s 0 = s := rfl

@[simp] theorem repl_succ (s : T (n + 1)) (i : Fin n) : repl s i.succ = var i.succ := by
  simp [repl]

@[simp] theorem up_one (σ : Fin (n + 1) → T m) : up σ 1 = shift (σ 0) := up_succ σ 0

@[simp] theorem inst_one (t : T (n + 1)) : inst t 1 = var 0 := inst_succ t 0

theorem up_var : up (var : Fin n → T n) = var := by
  refine funext (Fin.cases ?_ fun j => ?_) <;> simp

theorem subst_shift (σ : Fin (n + 1) → T m) (t : T n) :
    subst σ (shift t) = subst (fun i => σ i.succ) t := by
  simp [shift, subst_subst]

theorem shift_subst (σ : Fin n → T m) (t : T n) :
    shift (subst σ t) = subst (fun i => shift (σ i)) t :=
  subst_subst _ _ _

theorem up_comp (σ : Fin n → T m) (τ : Fin m → T k) :
    (fun i => subst (up τ) (up σ i)) = up (fun i => subst τ (σ i)) := by
  refine funext (Fin.cases ?_ fun j => ?_)
  · simp
  · simp [subst_shift, shift_subst]

@[simp] theorem subst_inst_shift (t s : T n) : subst (inst t) (shift s) = s := by
  simp [subst_shift]

theorem inst_comp_up (σ : Fin n → T m) (t : T n) :
    (fun i => subst (inst (subst σ t)) (up σ i)) = fun i => subst σ (inst t i) := by
  refine funext (Fin.cases ?_ fun j => ?_) <;> simp

end Syn

open Syn

/-- First-order formulas with equality over a scoped term syntax. -/
inductive Fm (T : ℕ → Type) : ℕ → Type
  | eq {n : ℕ} (s t : T n) : Fm T n
  | bot {n : ℕ} : Fm T n
  | and {n : ℕ} (φ ψ : Fm T n) : Fm T n
  | or {n : ℕ} (φ ψ : Fm T n) : Fm T n
  | imp {n : ℕ} (φ ψ : Fm T n) : Fm T n
  | all {n : ℕ} (φ : Fm T (n + 1)) : Fm T n
  | ex {n : ℕ} (φ : Fm T (n + 1)) : Fm T n

namespace Fm

variable {T : ℕ → Type} [Syn T] {n m k : ℕ}

scoped infix:50 " ≐ " => Fm.eq
scoped infixr:35 " ⋏ " => Fm.and
scoped infixr:30 " ⋎ " => Fm.or
scoped infixr:25 " ⟶ " => Fm.imp

/-- Simultaneous substitution in a formula. -/
def subst : {n m : ℕ} → Fm T n → (Fin n → T m) → Fm T m
  | _, _, eq s t, σ => eq (Syn.subst σ s) (Syn.subst σ t)
  | _, _, bot, _ => bot
  | _, _, and φ ψ, σ => and (φ.subst σ) (ψ.subst σ)
  | _, _, or φ ψ, σ => or (φ.subst σ) (ψ.subst σ)
  | _, _, imp φ ψ, σ => imp (φ.subst σ) (ψ.subst σ)
  | _, _, all φ, σ => all (φ.subst (up σ))
  | _, _, ex φ, σ => ex (φ.subst (up σ))

/-- Weakening of a formula by one new variable with index `0`. -/
def shift (φ : Fm T n) : Fm T (n + 1) := φ.subst (fun i => var i.succ)

/-- Biimplication. -/
def iff (φ ψ : Fm T n) : Fm T n := and (imp φ ψ) (imp ψ φ)

/-- Quantifier-free formulas. -/
def QF : {n : ℕ} → Fm T n → Prop
  | _, eq _ _ => True
  | _, bot => True
  | _, and φ ψ => φ.QF ∧ ψ.QF
  | _, or φ ψ => φ.QF ∧ ψ.QF
  | _, imp φ ψ => φ.QF ∧ ψ.QF
  | _, all _ => False
  | _, ex _ => False

@[simp] theorem subst_eq (s t : T n) (σ : Fin n → T m) :
    (eq s t).subst σ = eq (Syn.subst σ s) (Syn.subst σ t) := rfl
@[simp] theorem subst_bot (σ : Fin n → T m) : (bot : Fm T n).subst σ = bot := rfl
@[simp] theorem subst_and (φ ψ : Fm T n) (σ : Fin n → T m) :
    (and φ ψ).subst σ = and (φ.subst σ) (ψ.subst σ) := rfl
@[simp] theorem subst_or (φ ψ : Fm T n) (σ : Fin n → T m) :
    (or φ ψ).subst σ = or (φ.subst σ) (ψ.subst σ) := rfl
@[simp] theorem subst_imp (φ ψ : Fm T n) (σ : Fin n → T m) :
    (imp φ ψ).subst σ = imp (φ.subst σ) (ψ.subst σ) := rfl
@[simp] theorem subst_all (φ : Fm T (n + 1)) (σ : Fin n → T m) :
    (all φ).subst σ = all (φ.subst (up σ)) := rfl
@[simp] theorem subst_ex (φ : Fm T (n + 1)) (σ : Fin n → T m) :
    (ex φ).subst σ = ex (φ.subst (up σ)) := rfl

@[simp] theorem subst_id (φ : Fm T n) : φ.subst var = φ := by
  induction φ <;> simp_all [up_var]

theorem subst_subst (φ : Fm T n) :
    ∀ {m k : ℕ} (σ : Fin n → T m) (τ : Fin m → T k),
      (φ.subst σ).subst τ = φ.subst (fun i => Syn.subst τ (σ i)) := by
  induction φ <;> intro m k σ τ <;> simp_all [Syn.subst_subst, up_comp]

theorem shift_subst (φ : Fm T n) (σ : Fin n → T m) :
    (φ.subst σ).shift = φ.subst (fun i => Syn.shift (σ i)) := by
  simp [shift, subst_subst, Syn.shift]

theorem subst_shift (φ : Fm T n) (σ : Fin (n + 1) → T m) :
    φ.shift.subst σ = φ.subst (fun i => σ i.succ) := by
  simp [shift, subst_subst]

/-- Weakening commutes with substitution, in the form used under binders. -/
theorem shift_subst_up (φ : Fm T n) (σ : Fin n → T m) :
    φ.shift.subst (up σ) = (φ.subst σ).shift := by
  simp [subst_shift, shift_subst]

/-- Instantiation of the bound variable commutes with substitution. -/
theorem subst_inst (φ : Fm T (n + 1)) (σ : Fin n → T m) (t : T n) :
    (φ.subst (inst t)).subst σ = (φ.subst (up σ)).subst (inst (Syn.subst σ t)) := by
  simp [subst_subst, inst_comp_up]

end Fm

end LeanProofs.ConciseIPRA
-- END UPSTREAM Syntax.lean

-- BEGIN UPSTREAM Deduction.lean

/-!
# Intuitionistic natural deduction with equality

`Prf Ax Γ φ` is derivability of `φ` from the hypotheses `Γ` in intuitionistic
first-order logic with equality over the theory `Ax`.  Everything is scoped:
a sequent lives over a fixed number `n` of free variables, and the quantifier
rules move between `n` and `n + 1`.

A theory is a family of open axioms.  The axiom rule instantiates the free
variables of an axiom by arbitrary terms, so an axiom is read universally and
derivability is closed under substitution for every theory (`Prf.subst`).

Equality is governed by reflexivity and a simultaneous Leibniz rule: two
pointwise provably equal substitutions may be exchanged in any formula.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {T : ℕ → Type} [Syn T]

/-- A theory: a family of open axioms, one set for each number of free
variables. -/
abbrev Theory (T : ℕ → Type) := (k : ℕ) → Fm T k → Prop

/-- Intuitionistic natural deduction with equality over a theory. -/
inductive Prf (Ax : Theory T) : {n : ℕ} → List (Fm T n) → Fm T n → Prop
  | hyp {n : ℕ} {Γ : List (Fm T n)} {φ : Fm T n} (h : φ ∈ Γ) : Prf Ax Γ φ
  | ax {n k : ℕ} {Γ : List (Fm T n)} {φ : Fm T k} (h : Ax k φ) (σ : Fin k → T n) :
      Prf Ax Γ (φ.subst σ)
  | botE {n : ℕ} {Γ : List (Fm T n)} (φ : Fm T n) (h : Prf Ax Γ Fm.bot) : Prf Ax Γ φ
  | andI {n : ℕ} {Γ : List (Fm T n)} {φ ψ : Fm T n}
      (h₁ : Prf Ax Γ φ) (h₂ : Prf Ax Γ ψ) : Prf Ax Γ (φ ⋏ ψ)
  | andE₁ {n : ℕ} {Γ : List (Fm T n)} {φ ψ : Fm T n} (h : Prf Ax Γ (φ ⋏ ψ)) : Prf Ax Γ φ
  | andE₂ {n : ℕ} {Γ : List (Fm T n)} {φ ψ : Fm T n} (h : Prf Ax Γ (φ ⋏ ψ)) : Prf Ax Γ ψ
  | orI₁ {n : ℕ} {Γ : List (Fm T n)} {φ ψ : Fm T n} (h : Prf Ax Γ φ) : Prf Ax Γ (φ ⋎ ψ)
  | orI₂ {n : ℕ} {Γ : List (Fm T n)} {φ ψ : Fm T n} (h : Prf Ax Γ ψ) : Prf Ax Γ (φ ⋎ ψ)
  | orE {n : ℕ} {Γ : List (Fm T n)} {φ ψ χ : Fm T n} (h : Prf Ax Γ (φ ⋎ ψ))
      (h₁ : Prf Ax (φ :: Γ) χ) (h₂ : Prf Ax (ψ :: Γ) χ) : Prf Ax Γ χ
  | impI {n : ℕ} {Γ : List (Fm T n)} {φ ψ : Fm T n} (h : Prf Ax (φ :: Γ) ψ) :
      Prf Ax Γ (φ ⟶ ψ)
  | impE {n : ℕ} {Γ : List (Fm T n)} {φ ψ : Fm T n}
      (h₁ : Prf Ax Γ (φ ⟶ ψ)) (h₂ : Prf Ax Γ φ) : Prf Ax Γ ψ
  | allI {n : ℕ} {Γ : List (Fm T n)} {φ : Fm T (n + 1)}
      (h : Prf Ax (Γ.map Fm.shift) φ) : Prf Ax Γ (Fm.all φ)
  | allE {n : ℕ} {Γ : List (Fm T n)} {φ : Fm T (n + 1)} (t : T n)
      (h : Prf Ax Γ (Fm.all φ)) : Prf Ax Γ (φ.subst (inst t))
  | exI {n : ℕ} {Γ : List (Fm T n)} {φ : Fm T (n + 1)} (t : T n)
      (h : Prf Ax Γ (φ.subst (inst t))) : Prf Ax Γ (Fm.ex φ)
  | exE {n : ℕ} {Γ : List (Fm T n)} {φ : Fm T (n + 1)} {ψ : Fm T n}
      (h₁ : Prf Ax Γ (Fm.ex φ)) (h₂ : Prf Ax (φ :: Γ.map Fm.shift) ψ.shift) : Prf Ax Γ ψ
  | eqRefl {n : ℕ} {Γ : List (Fm T n)} (t : T n) : Prf Ax Γ (t ≐ t)
  | eqSubst {n k : ℕ} {Γ : List (Fm T n)} (φ : Fm T k) (σ σ' : Fin k → T n)
      (h₁ : ∀ i, Prf Ax Γ (σ i ≐ σ' i)) (h₂ : Prf Ax Γ (φ.subst σ)) :
      Prf Ax Γ (φ.subst σ')

@[inherit_doc] scoped notation:20 Γ:21 " ⊢[" Ax "] " φ:20 => Prf Ax Γ φ

namespace Fm

variable {n m : ℕ}

theorem map_shift_subst (Γ : List (Fm T n)) (σ : Fin n → T m) :
    (Γ.map Fm.shift).map (fun φ => φ.subst (up σ))
      = (Γ.map (fun φ => φ.subst σ)).map Fm.shift := by
  induction Γ with
  | nil => rfl
  | cons φ Γ ih => simp only [List.map_cons, ih, Fm.shift_subst_up]

/-- Opening a binder and instantiating it by its own variable is the identity. -/
theorem subst_up_succ_inst (φ : Fm T (n + 1)) :
    (φ.subst (up (fun i => var i.succ))).subst (inst (var 0)) = φ := by
  have e : (fun i => Syn.subst (inst (var 0 : T (n + 1)))
      (up (fun j : Fin n => (var j.succ : T (n + 1))) i)) = var := by
    refine funext (Fin.cases ?_ fun j => ?_) <;> simp
  rw [Fm.subst_subst, e, Fm.subst_id]

end Fm

namespace Prf

variable {Ax : Theory T} {n m : ℕ} {Γ Δ : List (Fm T n)} {φ ψ χ : Fm T n}

/-- Derivability is closed under substitution of terms for free variables and
under weakening of the context, in one induction. -/
theorem substWeaken (h : Γ ⊢[Ax] φ) : ∀ {m : ℕ} (σ : Fin n → T m) {Δ : List (Fm T m)},
    Γ.map (fun ψ => ψ.subst σ) ⊆ Δ → (Δ ⊢[Ax] φ.subst σ) := by
  induction h with intro m σ Δ s
  | hyp h => exact .hyp (s (List.mem_map_of_mem h))
  | ax h ρ => rw [Fm.subst_subst]; exact .ax h _
  | botE φ _ ih => exact .botE _ (ih σ s)
  | andI _ _ ih₁ ih₂ => exact .andI (ih₁ σ s) (ih₂ σ s)
  | andE₁ _ ih => exact .andE₁ (ih σ s)
  | andE₂ _ ih => exact .andE₂ (ih σ s)
  | orI₁ _ ih => exact .orI₁ (ih σ s)
  | orI₂ _ ih => exact .orI₂ (ih σ s)
  | orE _ _ _ ih ih₁ ih₂ =>
    exact .orE (ih σ s) (ih₁ σ (List.cons_subset_cons _ s)) (ih₂ σ (List.cons_subset_cons _ s))
  | impI _ ih => exact .impI (ih σ (List.cons_subset_cons _ s))
  | impE _ _ ih₁ ih₂ => exact .impE (ih₁ σ s) (ih₂ σ s)
  | allI _ ih =>
    exact .allI (ih (up σ) (by rw [Fm.map_shift_subst]; exact List.map_subset _ s))
  | allE t _ ih => rw [Fm.subst_inst]; exact .allE _ (ih σ s)
  | exI t _ ih =>
    have h := ih σ s
    rw [Fm.subst_inst] at h
    exact .exI _ h
  | exE _ _ ih₁ ih₂ =>
    have h := ih₂ (up σ) (Δ := _ :: Δ.map Fm.shift) (by
      rw [List.map_cons, Fm.map_shift_subst]
      exact List.cons_subset_cons _ (List.map_subset _ s))
    rw [Fm.shift_subst_up] at h
    exact .exE (ih₁ σ s) h
  | eqRefl t => exact .eqRefl _
  | eqSubst φ ρ ρ' _ _ ih₁ ih₂ =>
    have h := ih₂ σ s
    rw [Fm.subst_subst] at h ⊢
    exact .eqSubst φ _ _ (fun i => ih₁ i σ s) h

/-- Weakening. -/
theorem weaken (h : Γ ⊢[Ax] φ) {Δ : List (Fm T n)} (s : Γ ⊆ Δ) : Δ ⊢[Ax] φ := by
  simpa using h.substWeaken var (Δ := Δ) (by simpa using s)

/-- Derivability is closed under substitution of terms for free variables. -/
theorem subst (h : Γ ⊢[Ax] φ) {m : ℕ} (σ : Fin n → T m) :
    Γ.map (fun ψ => ψ.subst σ) ⊢[Ax] φ.subst σ :=
  h.substWeaken σ (List.Subset.refl _)

/-- Derivability is closed under weakening by a fresh variable. -/
theorem shift (h : Γ ⊢[Ax] φ) : Γ.map Fm.shift ⊢[Ax] φ.shift :=
  h.subst _

theorem liftCons (s : ∀ ψ ∈ Γ, Δ ⊢[Ax] ψ) (χ : Fm T n) :
    ∀ ψ ∈ χ :: Γ, (χ :: Δ ⊢[Ax] ψ) :=
  List.forall_mem_cons.2 ⟨.hyp List.mem_cons_self, fun ψ hψ => (s ψ hψ).weaken (by simp)⟩

/-- Simultaneous cut: the hypotheses may be replaced by anything deriving them.
Each hypothesis is discharged by an implication and restored by modus ponens. -/
theorem trans (h : Γ ⊢[Ax] φ) {Δ : List (Fm T n)} (s : ∀ ψ ∈ Γ, Δ ⊢[Ax] ψ) : Δ ⊢[Ax] φ := by
  induction Γ generalizing φ with
  | nil => exact h.weaken (List.nil_subset _)
  | cons ψ Γ ih =>
    exact .impE (ih (.impI h) fun χ hχ => s χ (List.mem_cons_of_mem _ hχ))
      (s ψ List.mem_cons_self)

/-! ### Structural conveniences -/

theorem hyp0 : φ :: Γ ⊢[Ax] φ := .hyp List.mem_cons_self

theorem hyp1 : ψ :: φ :: Γ ⊢[Ax] φ := .hyp (List.mem_cons_of_mem _ List.mem_cons_self)

theorem wk (h : Γ ⊢[Ax] φ) : ψ :: Γ ⊢[Ax] φ := h.weaken (List.subset_cons_self _ _)

/-- A closed derivation may be used under any hypotheses. -/
theorem ofNil (h : [] ⊢[Ax] φ) : Γ ⊢[Ax] φ := h.weaken (List.nil_subset _)

theorem impTrans (h₁ : Γ ⊢[Ax] φ ⟶ ψ) (h₂ : Γ ⊢[Ax] ψ ⟶ χ) : Γ ⊢[Ax] φ ⟶ χ :=
  .impI (.impE h₂.wk (.impE h₁.wk hyp0))

/-- An axiom, used as stated. -/
theorem axm (h : Ax n φ) : Γ ⊢[Ax] φ := by
  simpa only [Fm.subst_id] using Prf.ax (Γ := Γ) h var

/-- Universal elimination onto the bound variable itself. -/
theorem allOpen {φ : Fm T (n + 1)} (h : Γ ⊢[Ax] Fm.all φ) : Γ.map Fm.shift ⊢[Ax] φ := by
  have h' := Prf.allE (var 0) h.shift
  rwa [Fm.subst_up_succ_inst] at h'

/-! ### Biimplication -/

theorem iffI (h₁ : Γ ⊢[Ax] φ ⟶ ψ) (h₂ : Γ ⊢[Ax] ψ ⟶ φ) : Γ ⊢[Ax] Fm.iff φ ψ := .andI h₁ h₂

theorem iffMp (h : Γ ⊢[Ax] Fm.iff φ ψ) (h₁ : Γ ⊢[Ax] φ) : Γ ⊢[Ax] ψ := .impE (.andE₁ h) h₁

theorem iffMpr (h : Γ ⊢[Ax] Fm.iff φ ψ) (h₁ : Γ ⊢[Ax] ψ) : Γ ⊢[Ax] φ := .impE (.andE₂ h) h₁

theorem iffRefl (φ : Fm T n) : Γ ⊢[Ax] Fm.iff φ φ := .andI (.impI hyp0) (.impI hyp0)

theorem iffSymm (h : Γ ⊢[Ax] Fm.iff φ ψ) : Γ ⊢[Ax] Fm.iff ψ φ := .andI (.andE₂ h) (.andE₁ h)

theorem iffTrans (h₁ : Γ ⊢[Ax] Fm.iff φ ψ) (h₂ : Γ ⊢[Ax] Fm.iff ψ χ) : Γ ⊢[Ax] Fm.iff φ χ :=
  .andI (impTrans (.andE₁ h₁) (.andE₁ h₂)) (impTrans (.andE₂ h₂) (.andE₂ h₁))

/-! ### Equality -/

/-- Leibniz' rule for one variable. -/
theorem eqSubst1 (φ : Fm T (n + 1)) {s t : T n} (h : Γ ⊢[Ax] s ≐ t)
    (hφ : Γ ⊢[Ax] φ.subst (inst s)) : Γ ⊢[Ax] φ.subst (inst t) :=
  .eqSubst φ (inst s) (inst t) (fun i => Fin.cases h (fun _ => .eqRefl _) i) hφ

theorem eqSymm {s t : T n} (h : Γ ⊢[Ax] s ≐ t) : Γ ⊢[Ax] t ≐ s := by
  simpa using eqSubst1 (Fm.eq (var 0) (Syn.shift s)) h (by simpa using Prf.eqRefl s)

theorem eqTrans {s t u : T n} (h₁ : Γ ⊢[Ax] s ≐ t) (h₂ : Γ ⊢[Ax] t ≐ u) : Γ ⊢[Ax] s ≐ u := by
  simpa using eqSubst1 (Fm.eq (Syn.shift s) (var 0)) h₂ (by simpa using h₁)

/-- Congruence: provably equal substitutions give provably equal instances of a
term. -/
theorem eqCongr {k : ℕ} (t : T k) {σ σ' : Fin k → T n} (h : ∀ i, Γ ⊢[Ax] σ i ≐ σ' i) :
    Γ ⊢[Ax] Syn.subst σ t ≐ Syn.subst σ' t := by
  simpa [Syn.subst_shift] using Prf.eqSubst (Fm.eq (var 0) (Syn.shift t))
    (Fin.cases (Syn.subst σ t) σ) (Fin.cases (Syn.subst σ t) σ')
    (fun i => Fin.cases (.eqRefl _) h i)
    (by simpa [Syn.subst_shift] using Prf.eqRefl (Ax := Ax) (Γ := Γ) (Syn.subst σ t))

/-- Congruence for one variable. -/
theorem eqCongr1 (u : T (n + 1)) {s t : T n} (h : Γ ⊢[Ax] s ≐ t) :
    Γ ⊢[Ax] Syn.subst (inst s) u ≐ Syn.subst (inst t) u :=
  eqCongr u fun i => Fin.cases h (fun _ => .eqRefl _) i

end Prf

end LeanProofs.ConciseIPRA
-- END UPSTREAM Deduction.lean

-- BEGIN UPSTREAM PR.lean

/-!
# Intuitionistic primitive recursive arithmetic

`iPRA` in its usual first-order presentation.

* `PR k` is the type of primitive recursive function symbols of arity `k`,
  generated by zero, successor, projections, composition and primitive
  recursion.  In `prec f g` the recursion argument comes first:
  `prec f g (0, x⃗) = f x⃗` and
  `prec f g (S y, x⃗) = g (y, prec f g (y, x⃗), x⃗)`.
* `PTm n` is the type of terms built from variables and function symbols.
* `PRAAx` consists of the defining equations of all symbols, `S x = 0 → ⊥`,
  injectivity of successor, and induction for quantifier-free formulas.

The logic is the intuitionistic natural deduction of `ConciseIPRA.Deduction`.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

/-- Primitive recursive function symbols of a given arity. -/
inductive PR : ℕ → Type
  | zero : PR 0
  | succ : PR 1
  | proj {k : ℕ} (i : Fin k) : PR k
  | comp {m k : ℕ} (f : PR m) (gs : Fin m → PR k) : PR k
  | prec {k : ℕ} (f : PR k) (g : PR (k + 2)) : PR (k + 1)

/-- Terms of primitive recursive arithmetic over `n` free variables. -/
inductive PTm (n : ℕ) : Type
  | var (i : Fin n) : PTm n
  | app {k : ℕ} (f : PR k) (ts : Fin k → PTm n) : PTm n

namespace PTm

variable {n m k : ℕ}

/-- Simultaneous substitution. -/
def sub (σ : Fin n → PTm m) : PTm n → PTm m
  | var i => σ i
  | app f ts => app f (fun i => sub σ (ts i))

theorem sub_var (t : PTm n) : sub var t = t := by
  induction t <;> simp_all [sub]

theorem sub_sub (σ : Fin n → PTm m) (τ : Fin m → PTm k) (t : PTm n) :
    sub τ (sub σ t) = sub (fun i => sub τ (σ i)) t := by
  induction t <;> simp_all [sub]

instance : Syn PTm where
  var := PTm.var
  subst := PTm.sub
  subst_var _ _ := rfl
  subst_id := sub_var
  subst_subst σ τ t := sub_sub σ τ t

/-- The generic variable `Syn.var` is the normal form for variables. -/
@[simp] theorem var_eq (i : Fin n) : (var i : PTm n) = Syn.var i := rfl

@[simp] theorem subst_app (σ : Fin n → PTm m) (f : PR k) (ts : Fin k → PTm n) :
    Syn.subst σ (app f ts) = app f (fun i => Syn.subst σ (ts i)) := rfl

/-- The numeral `0`. -/
def zero : PTm n := app .zero Fin.elim0

/-- The successor of a term. -/
def succ (t : PTm n) : PTm n := app .succ (fun _ => t)

@[simp] theorem subst_zero (σ : Fin n → PTm m) : Syn.subst σ (zero : PTm n) = zero :=
  congrArg (app PR.zero) (funext fun i => i.elim0)

@[simp] theorem subst_succ (σ : Fin n → PTm m) (t : PTm n) :
    Syn.subst σ (succ t) = succ (Syn.subst σ t) := rfl

@[simp] theorem shift_zero : Syn.shift (zero : PTm n) = zero := subst_zero _

@[simp] theorem shift_succ (t : PTm n) : Syn.shift (succ t) = succ (Syn.shift t) := rfl

end PTm

open PTm (app zero succ)

/-- The axioms of `iPRA`. -/
inductive PRAAx : Theory PTm
  | proj {k : ℕ} (i : Fin k) : PRAAx k (app (.proj i) var ≐ var i)
  | comp {m k : ℕ} (f : PR m) (gs : Fin m → PR k) :
      PRAAx k (app (.comp f gs) var ≐ app f (fun j => app (gs j) var))
  | precZero {k : ℕ} (f : PR k) (g : PR (k + 2)) :
      PRAAx k (app (.prec f g) (inst zero) ≐ app f var)
  | precSucc {k : ℕ} (f : PR k) (g : PR (k + 2)) :
      PRAAx (k + 1) (app (.prec f g) (repl (succ (var 0)))
        ≐ app g (Fin.cases (var 0) (repl (app (.prec f g) var))))
  | succNeZero : PRAAx 1 ((succ (var 0) ≐ zero) ⟶ Fm.bot)
  | succInj : PRAAx 2 ((succ (var 0) ≐ succ (var 1)) ⟶ (var 0 ≐ var 1))
  | ind {n : ℕ} (φ : Fm PTm (n + 1)) (h : φ.QF) :
      PRAAx n (φ.subst (inst zero) ⟶
        Fm.all (φ ⟶ φ.subst (repl (succ (var 0)))) ⟶ Fm.all φ)

namespace PRA

variable {n k m : ℕ} {Γ : List (Fm PTm n)}

/-- Projection, at arbitrary arguments. -/
theorem proj (i : Fin k) (ts : Fin k → PTm n) : Γ ⊢[PRAAx] app (.proj i) ts ≐ ts i := by
  simpa using Prf.ax (Γ := Γ) (PRAAx.proj i) ts

/-- Composition, at arbitrary arguments. -/
theorem comp (f : PR m) (gs : Fin m → PR k) (ts : Fin k → PTm n) :
    Γ ⊢[PRAAx] app (.comp f gs) ts ≐ app f (fun j => app (gs j) ts) := by
  simpa using Prf.ax (Γ := Γ) (PRAAx.comp f gs) ts

/-- Primitive recursion at zero, at arbitrary parameters. -/
theorem precZero (f : PR k) (g : PR (k + 2)) (xs : Fin k → PTm n) :
    Γ ⊢[PRAAx] app (.prec f g) (Fin.cases zero xs) ≐ app f xs := by
  have h := Prf.ax (Γ := Γ) (PRAAx.precZero f g) xs
  have e : (fun i => Syn.subst xs (inst (zero : PTm k) i)) = Fin.cases zero xs := by
    refine funext (Fin.cases ?_ fun j => ?_) <;> simp
  simpa [e] using h

/-- Primitive recursion at a successor, at arbitrary arguments. -/
theorem precSucc (f : PR k) (g : PR (k + 2)) (y : PTm n) (xs : Fin k → PTm n) :
    Γ ⊢[PRAAx] app (.prec f g) (Fin.cases (succ y) xs)
      ≐ app g (Fin.cases y (Fin.cases (app (.prec f g) (Fin.cases y xs)) xs)) := by
  have h := Prf.ax (Γ := Γ) (PRAAx.precSucc f g) (Fin.cases y xs)
  have e₁ : (fun i => Syn.subst (Fin.cases y xs : Fin (k + 1) → PTm n)
      (repl (succ (var 0)) i)) = Fin.cases (succ y) xs := by
    refine funext (Fin.cases ?_ fun j => ?_) <;> simp
  have e₂ : (fun i => Syn.subst (Fin.cases y xs : Fin (k + 1) → PTm n)
      ((Fin.cases (var 0) (repl (app (.prec f g) var)) : Fin (k + 2) → PTm (k + 1)) i))
      = Fin.cases y (Fin.cases (app (.prec f g) (Fin.cases y xs)) xs) := by
    refine funext (Fin.cases ?_ fun j => ?_)
    · simp
    · refine Fin.cases ?_ (fun l => ?_) j <;> simp
  simpa [e₁, e₂] using h

theorem succNeZero (t : PTm n) : Γ ⊢[PRAAx] (succ t ≐ zero) ⟶ Fm.bot := by
  simpa using Prf.ax (Γ := Γ) PRAAx.succNeZero (fun _ => t)

/-- Induction for a quantifier-free formula. -/
theorem qfInd (φ : Fm PTm (n + 1)) (hφ : φ.QF) (h0 : Γ ⊢[PRAAx] φ.subst (inst zero))
    (hS : φ :: Γ.map Fm.shift ⊢[PRAAx] φ.subst (repl (succ (var 0)))) :
    Γ ⊢[PRAAx] Fm.all φ :=
  .impE (.impE (.axm (.ind φ hφ)) h0) (.allI (.impI hS))

end PRA

end LeanProofs.ConciseIPRA
-- END UPSTREAM PR.lean
