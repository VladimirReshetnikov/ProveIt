import Mathlib.Data.Fin.Tuple.Basic

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

theorem up_var : up (var : Fin n → T n) = var := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem subst_shift (σ : Fin (n + 1) → T m) (t : T n) :
    subst σ (shift t) = subst (fun i => σ i.succ) t := by
  simp [shift, subst_subst]

theorem shift_subst (σ : Fin n → T m) (t : T n) :
    shift (subst σ t) = subst (fun i => shift (σ i)) t :=
  subst_subst _ _ _

theorem up_comp (σ : Fin n → T m) (τ : Fin m → T k) :
    (fun i => subst (up τ) (up σ i)) = up (fun i => subst τ (σ i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [subst_shift, shift_subst]

@[simp] theorem subst_inst_shift (t s : T n) : subst (inst t) (shift s) = s := by
  simp [subst_shift]

theorem inst_comp_up (σ : Fin n → T m) (t : T n) :
    (fun i => subst (inst (subst σ t)) (up σ i)) = fun i => subst σ (inst t i) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem up_shift_comm (σ : Fin n → T m) :
    (fun i => subst (up σ) (var i.succ)) = fun i => shift (σ i) := by
  funext i; simp

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

@[inherit_doc] scoped infix:50 " ≐ " => Fm.eq
@[inherit_doc] scoped infixr:35 " ⋏ " => Fm.and
@[inherit_doc] scoped infixr:30 " ⋎ " => Fm.or
@[inherit_doc] scoped infixr:25 " ⟶ " => Fm.imp

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
@[simp] theorem subst_iff (φ ψ : Fm T n) (σ : Fin n → T m) :
    (iff φ ψ).subst σ = iff (φ.subst σ) (ψ.subst σ) := rfl

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

@[simp] theorem subst_inst_shift (φ : Fm T n) (t : T n) : φ.shift.subst (inst t) = φ := by
  simp [subst_shift]

/-- Instantiation of the bound variable commutes with substitution. -/
theorem subst_inst (φ : Fm T (n + 1)) (σ : Fin n → T m) (t : T n) :
    (φ.subst (inst t)).subst σ = (φ.subst (up σ)).subst (inst (Syn.subst σ t)) := by
  simp [subst_subst, inst_comp_up]

end Fm

end LeanProofs.ConciseIPRA
