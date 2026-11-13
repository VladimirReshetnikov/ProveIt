import ConciseIPRA.TeqEq

/-!
# Order in `T_eq`

The order of `T_eq` is `x ≤ y :⟺ monus x y = 0`.  The module proves the
cancellation laws `(a + b) ∸ a = b` and `a ∸ (a + b) = 0`, and the single
equation

  `x + monus y x = y + monus x y`,

both sides of which are the maximum.  It turns an inequality into an additive
witness: `x ≤ y` gives `x + (y ∸ x) = y`.  The powers of two satisfy `S x ≤ 2 ^ x`.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {n m : ℕ}

namespace Q

variable {Γ : List (Fm Tm n)}

/-! ### Cancellation -/

@[simp] theorem zero_monus (x : Q Γ) : monus 0 x = 0 := by
  induction x using Q.ind with | _ a
  simpa using eqInd (Γ := Γ) (Tm.monus Tm.zero (var 0)) Tm.zero a

@[simp] theorem monus_self (x : Q Γ) : monus x x = 0 := by
  induction x using Q.ind with | _ a
  simpa using eqInd (Γ := Γ) (Tm.monus (var 0) (var 0)) Tm.zero a
    (hS := fun _ => by simp)

@[simp] theorem monus_add_left (a b : Q Γ) : monus (a + b) a = b := by
  induction a, b using Q.ind₂ with | _ a b
  simpa using eqInd (Γ := Γ) (Tm.monus (Tm.add (var 0) (shift b)) (var 0)) (shift b) a
    (hS := fun ih => by simp at ih; simp [succ_add, ih])

@[simp] theorem monus_add_right (a b : Q Γ) : monus a (a + b) = 0 := by
  induction a, b using Q.ind₂ with | _ a b
  simpa using eqInd (Γ := Γ) (Tm.monus (shift a) (Tm.add (shift a) (var 0))) Tm.zero b
    (hS := fun ih => by simp at ih; simp [add_succ, ih])

theorem monus_succ_add (x d : Q Γ) : monus (succ (x + d)) x = succ d := by
  rw [← add_succ, monus_add_left]

/-! ### From an inequality to an additive witness -/

theorem add_monus_succ_of (x y : Q Γ) (hy : x + monus y x = y) :
    x + monus (succ y) x = succ y := by
  have h1 : monus (succ y) x = succ (monus y x) := by
    conv_lhs => rw [← hy]
    rw [monus_succ_add]
  rw [h1, add_succ, hy]

/-- The step of the maximum identity, by cases on `x ∸ y`. -/
theorem add_monus_step (x y : Q Γ) (ih : x + monus y x = y + monus x y) :
    x + monus (succ y) x = succ (y + pred (monus x y)) := by
  refine Q.cases (monus x y) (fun e he => ?_) (fun e z he => ?_)
  · have ih' := congrArg e.map ih
    simp only [Ext.map_add, Ext.map_monus, Ext.map_succ, Ext.map_pred] at he ih' ⊢
    rw [he, add_zero] at ih'
    rw [he, pred_zero, add_zero, add_monus_succ_of _ _ ih']
  · simp only [Ext.map_add, Ext.map_monus, Ext.map_succ, Ext.map_pred] at he ⊢
    rw [he, pred_succ, ← add_succ_of_monus_eq_succ he]
    simp

/-- The maximum identity: `x + (y ∸ x) = y + (x ∸ y)`. -/
theorem add_monus_comm (x y : Q Γ) : x + monus y x = y + monus x y := by
  induction x, y using Q.ind₂ with | _ a b
  simpa using eqInd (Γ := Γ) (Tm.add (shift a) (Tm.monus (var 0) (shift a)))
    (Tm.add (var 0) (Tm.monus (shift a) (var 0))) b
    (hS := fun ih => by simp at ih ⊢; exact add_monus_step _ _ ih)

theorem add_monus_of_le {x y : Q Γ} (h : monus x y = 0) : x + monus y x = y := by
  rw [add_monus_comm, h, add_zero]

theorem le_add_right {x y : Q Γ} (h : monus x y = 0) (z : Q Γ) : monus x (y + z) = 0 := by
  rw [← add_monus_of_le h, add_assoc, monus_add_right]

theorem le_of_succ_le {x y : Q Γ} (h : monus (succ x) y = 0) : monus x y = 0 := by
  rw [← add_monus_of_le h, succ_add, ← add_succ, monus_add_right]

theorem le_of_add_le {x y k : Q Γ} (h : monus (x + y) k = 0) : monus x k = 0 := by
  rw [← add_monus_of_le h, add_assoc, monus_add_right]

/-! ### Powers of two -/

theorem succ_le_double {x p : Q Γ} (h : monus (succ x) p = 0) :
    monus (succ (succ x)) (p + p) = 0 := by
  have hp := add_monus_of_le h
  generalize monus p (succ x) = d at hp
  subst hp
  have e : succ x + d + (succ x + d) = succ (succ x) + (x + d + d) := by
    simp only [succ_add, add_succ, succ_inj_iff]
    abel
  rw [e, monus_add_right]

/-- `S x ≤ 2 ^ x`. -/
theorem succ_le_pow2 (x : Q Γ) : monus (succ x) (pow2 x) = 0 := by
  induction x using Q.ind with | _ a
  simpa using eqInd (Γ := Γ) (Tm.monus (Tm.succ (var 0)) (Tm.pow2 (var 0))) Tm.zero a
    (hS := fun ih => by simp at ih ⊢; exact succ_le_double ih)

end Q

end LeanProofs.ConciseIPRA
