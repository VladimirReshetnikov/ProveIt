import ConciseIPRA.Syntax

/-!
# Iterator terms

The terms of the native scalar core: variables, zero, successor and the
iterator `I(c, a; u.h)`, which binds one variable in its step term `h`.  The
bound variable has de Bruijn index `0` in `h`.  The intended reading is
`I(0, a; u.h) = a` and `I(S c, a; u.h) = h[I(c, a; u.h)/u]`.

Renaming and substitution are defined in the usual two stages, and `Tm` is
shown to be a scoped syntax in the sense of `Syn`.
-/

namespace LeanProofs.ConciseIPRA

/-- Iterator terms over `n` free variables. -/
inductive Tm : ℕ → Type
  | var {n : ℕ} (i : Fin n) : Tm n
  | zero {n : ℕ} : Tm n
  | succ {n : ℕ} (t : Tm n) : Tm n
  | iter {n : ℕ} (c a : Tm n) (h : Tm (n + 1)) : Tm n

namespace Tm

variable {n m k : ℕ}

/-- Lifting of a renaming under one binder. -/
def upRen (ξ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => (ξ i).succ)

@[simp] theorem upRen_zero (ξ : Fin n → Fin m) : upRen ξ 0 = 0 := rfl

@[simp] theorem upRen_succ (ξ : Fin n → Fin m) (i : Fin n) :
    upRen ξ i.succ = (ξ i).succ := by
  simp [upRen]

/-- Renaming of variables. -/
def ren : {n m : ℕ} → (Fin n → Fin m) → Tm n → Tm m
  | _, _, ξ, var i => var (ξ i)
  | _, _, _, zero => zero
  | _, _, ξ, succ t => succ (ren ξ t)
  | _, _, ξ, iter c a h => iter (ren ξ c) (ren ξ a) (ren (upRen ξ) h)

/-- Lifting of a substitution under one binder. -/
def upS (σ : Fin n → Tm m) : Fin (n + 1) → Tm (m + 1) :=
  Fin.cases (var 0) (fun i => ren Fin.succ (σ i))

@[simp] theorem upS_zero (σ : Fin n → Tm m) : upS σ 0 = var 0 := rfl

@[simp] theorem upS_succ (σ : Fin n → Tm m) (i : Fin n) :
    upS σ i.succ = ren Fin.succ (σ i) := by
  simp [upS]

/-- Simultaneous substitution. -/
def sub : {n m : ℕ} → (Fin n → Tm m) → Tm n → Tm m
  | _, _, σ, var i => σ i
  | _, _, _, zero => zero
  | _, _, σ, succ t => succ (sub σ t)
  | _, _, σ, iter c a h => iter (sub σ c) (sub σ a) (sub (upS σ) h)

theorem upRen_comp (ξ : Fin n → Fin m) (ζ : Fin m → Fin k) :
    (fun i => upRen ζ (upRen ξ i)) = upRen (fun i => ζ (ξ i)) := by
  refine funext (Fin.cases ?_ fun j => ?_) <;> simp

theorem ren_ren (t : Tm n) :
    ∀ {m k : ℕ} (ξ : Fin n → Fin m) (ζ : Fin m → Fin k),
      ren ζ (ren ξ t) = ren (fun i => ζ (ξ i)) t := by
  induction t <;> intro m k ξ ζ <;> simp_all [ren, upRen_comp]

theorem upS_upRen (ξ : Fin n → Fin m) (σ : Fin m → Tm k) :
    (fun i => upS σ (upRen ξ i)) = upS (fun i => σ (ξ i)) := by
  refine funext (Fin.cases ?_ fun j => ?_) <;> simp

theorem sub_ren (t : Tm n) :
    ∀ {m k : ℕ} (ξ : Fin n → Fin m) (σ : Fin m → Tm k),
      sub σ (ren ξ t) = sub (fun i => σ (ξ i)) t := by
  induction t <;> intro m k ξ σ <;> simp_all [ren, sub, upS_upRen]

theorem upRen_upS (σ : Fin n → Tm m) (ξ : Fin m → Fin k) :
    (fun i => ren (upRen ξ) (upS σ i)) = upS (fun i => ren ξ (σ i)) := by
  refine funext (Fin.cases ?_ fun j => ?_)
  · simp [ren]
  · simp [ren_ren]

theorem ren_sub (t : Tm n) :
    ∀ {m k : ℕ} (σ : Fin n → Tm m) (ξ : Fin m → Fin k),
      ren ξ (sub σ t) = sub (fun i => ren ξ (σ i)) t := by
  induction t <;> intro m k σ ξ <;> simp_all [ren, sub, upRen_upS]

theorem upS_comp (σ : Fin n → Tm m) (τ : Fin m → Tm k) :
    (fun i => sub (upS τ) (upS σ i)) = upS (fun i => sub τ (σ i)) := by
  refine funext (Fin.cases ?_ fun j => ?_)
  · simp [sub]
  · simp [sub_ren, ren_sub]

theorem sub_sub (t : Tm n) :
    ∀ {m k : ℕ} (σ : Fin n → Tm m) (τ : Fin m → Tm k),
      sub τ (sub σ t) = sub (fun i => sub τ (σ i)) t := by
  induction t <;> intro m k σ τ <;> simp_all [sub, upS_comp]

theorem upS_var : upS (var : Fin n → Tm n) = var := by
  refine funext (Fin.cases ?_ fun j => ?_) <;> simp [ren]

theorem sub_var (t : Tm n) : sub var t = t := by
  induction t <;> simp_all [sub, upS_var]

theorem upS_ren (ξ : Fin n → Fin m) :
    upS (fun i => var (ξ i)) = fun i => var (upRen ξ i) := by
  refine funext (Fin.cases ?_ fun j => ?_) <;> simp [ren]

theorem ren_eq_sub (t : Tm n) :
    ∀ {m : ℕ} (ξ : Fin n → Fin m), ren ξ t = sub (fun i => var (ξ i)) t := by
  induction t <;> intro m ξ <;> simp_all [ren, sub, upS_ren]

instance : Syn Tm where
  var := Tm.var
  subst := Tm.sub
  subst_var _ _ := rfl
  subst_id := sub_var
  subst_subst σ τ t := sub_sub t σ τ

/-- The numeral `1`. -/
def one : Tm n := succ zero

theorem shift_eq_ren (t : Tm n) : Syn.shift t = ren Fin.succ t :=
  (ren_eq_sub t Fin.succ).symm

theorem up_eq_upS (σ : Fin n → Tm m) : Syn.up σ = upS σ := by
  refine funext (Fin.cases ?_ fun j => ?_)
  · rfl
  · simp [shift_eq_ren]

/-- The generic variable `Syn.var` is the normal form for variables. -/
@[simp] theorem var_eq (i : Fin n) : (var i : Tm n) = Syn.var i := rfl

@[simp] theorem subst_zero (σ : Fin n → Tm m) : Syn.subst σ (zero : Tm n) = zero := rfl

@[simp] theorem subst_succ (σ : Fin n → Tm m) (t : Tm n) :
    Syn.subst σ (succ t) = succ (Syn.subst σ t) := rfl

@[simp] theorem subst_iter (σ : Fin n → Tm m) (c a : Tm n) (h : Tm (n + 1)) :
    Syn.subst σ (iter c a h)
      = iter (Syn.subst σ c) (Syn.subst σ a) (Syn.subst (Syn.up σ) h) := by
  rw [up_eq_upS]; rfl

@[simp] theorem subst_one (σ : Fin n → Tm m) : Syn.subst σ (one : Tm n) = one := rfl

@[simp] theorem shift_zero : Syn.shift (zero : Tm n) = zero := rfl

@[simp] theorem shift_succ (t : Tm n) : Syn.shift (succ t) = succ (Syn.shift t) := rfl

@[simp] theorem shift_iter (c a : Tm n) (h : Tm (n + 1)) :
    Syn.shift (iter c a h)
      = iter (Syn.shift c) (Syn.shift a)
          (Syn.subst (Syn.up (fun i => Syn.var i.succ)) h) := by
  simp [Syn.shift]

end Tm

end LeanProofs.ConciseIPRA
