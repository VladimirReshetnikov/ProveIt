import ConciseIPRA.TeqPred

/-!
# Truncated subtraction in `T_eq`

`monus x y = I(y, x; u. pred u)` is truncated subtraction.  A single equation
invariant,

  `sel (monus x y) x (y + monus x y) = x`,

says that a positive difference is an actual difference.  The equality test
built from it is in `TeqReflect`.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {n m : ℕ}

/-- Truncated subtraction `I(y, x; u. pred u)`. -/
def Tm.monus (x y : Tm n) : Tm n := Tm.iter y x (Tm.pred (Syn.var 0))

lift_op₂ monus

namespace Q

variable {Γ : List (Fm Tm n)}

/-! ### Truncated subtraction -/

@[simp] theorem monus_zero (x : Q Γ) : monus x 0 = x := by
  induction x using Q.ind with | _ a => exact sound (Teq.iterZero a _)

@[simp] theorem monus_succ (x y : Q Γ) : monus x (succ y) = pred (monus x y) := by
  induction x, y using Q.ind₂ with | _ a b
  have h := Teq.iterSucc (Γ := Γ) b a (Tm.pred (var 0))
  simp only [Tm.subst_pred, Syn.subst_var, Syn.inst_zero] at h
  exact sound h

@[simp] theorem pred_monus_succ (x y : Q Γ) : pred (monus (succ x) y) = monus x y := by
  induction x, y using Q.ind₂ with | _ a b
  simpa using eqInd (Γ := Γ) (Tm.pred (Tm.monus (Tm.succ (shift a)) (var 0)))
    (Tm.monus (shift a) (var 0)) b

@[simp] theorem monus_succ_self (x : Q Γ) : monus (succ x) x = 1 := by
  induction x using Q.ind with | _ a
  simpa using eqInd (Γ := Γ) (Tm.monus (Tm.succ (var 0)) (var 0)) Tm.one a

/-- The step of the difference invariant. -/
theorem monus_inv_step (x v u : Q Γ) (h : sel u x (v + u) = x) :
    sel (pred u) x (succ (v + pred u)) = x := by
  refine Q.cases u (fun e he => ?_) (fun e z he => ?_)
  · simp [he]
  · have h' := congrArg e.map h
    simp [he] at h'
    simp [he, h']

/-- The difference invariant: a positive difference is an actual difference. -/
theorem sel_monus (x y : Q Γ) : sel (monus x y) x (y + monus x y) = x := by
  induction x, y using Q.ind₂ with | _ a b
  simpa using eqInd (Γ := Γ)
    (Tm.sel (Tm.monus (shift a) (var 0)) (shift a)
      (Tm.add (var 0) (Tm.monus (shift a) (var 0))))
    (shift a) b
    (hS := fun ih => by simp at ih ⊢; exact monus_inv_step _ _ _ ih)

theorem add_succ_of_monus_eq_succ {x y z : Q Γ} (h : monus x y = succ z) :
    succ (y + z) = x := by
  have h' := sel_monus x y
  rwa [h, sel_succ, add_succ] at h'

end Q

end LeanProofs.ConciseIPRA
