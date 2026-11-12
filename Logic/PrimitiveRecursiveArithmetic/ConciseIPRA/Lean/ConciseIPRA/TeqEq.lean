import ConciseIPRA.TeqPred

/-!
# Truncated subtraction and the equality test in `T_eq`

`monus x y = I(y, x; u. pred u)` is truncated subtraction.  A single equation
invariant,

  `sel (monus x y) x (y + monus x y) = x`,

says that a positive difference is an actual difference; with
`monus (S a) a = 1` it gives `monus (S a) b = 1 ↔ a = b`.  The term

  `eqt a b = sel d 1 (pred d)`,  `d = monus (S a) b`,

vanishes exactly when `d = 1`, so `eqt a b = 0 ↔ a = b` in every context.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {n m : ℕ}

/-- Truncated subtraction `I(y, x; u. pred u)`. -/
def Tm.monus (x y : Tm n) : Tm n := Tm.iter y x (Tm.pred (Syn.var 0))

/-- The equality test: zero exactly at equal arguments. -/
def Tm.eqt (a b : Tm n) : Tm n :=
  Tm.sel (Tm.monus (Tm.succ a) b) Tm.one (Tm.pred (Tm.monus (Tm.succ a) b))

@[simp] theorem Tm.subst_monus (σ : Fin n → Tm m) (x y : Tm n) :
    Syn.subst σ (Tm.monus x y) = Tm.monus (Syn.subst σ x) (Syn.subst σ y) := by
  simp [Tm.monus]

@[simp] theorem Tm.subst_eqt (σ : Fin n → Tm m) (a b : Tm n) :
    Syn.subst σ (Tm.eqt a b) = Tm.eqt (Syn.subst σ a) (Syn.subst σ b) := by
  simp [Tm.eqt]

lift_op₂ monus eqt

namespace Q

variable {Γ : List (Fm Tm n)}

/-! ### Truncated subtraction -/

@[simp] theorem monus_zero (x : Q Γ) : monus x 0 = x := by
  induction x using Q.ind with | _ a
  exact sound (Teq.iterZero a _)

@[simp] theorem monus_succ (x y : Q Γ) : monus x (succ y) = pred (monus x y) := by
  induction x using Q.ind with | _ a
  induction y using Q.ind with | _ b
  have h := Teq.iterSucc (Γ := Γ) b a (Tm.pred (var 0))
  simp only [Tm.subst_pred, Syn.subst_var, Syn.inst_zero] at h
  exact sound h

@[simp] theorem monus_one (x : Q Γ) : monus x 1 = pred x := by
  show monus x (succ 0) = pred x
  rw [monus_succ, monus_zero]

@[simp] theorem pred_monus_succ (x y : Q Γ) : pred (monus (succ x) y) = monus x y := by
  induction x using Q.ind with | _ a
  induction y using Q.ind with | _ b
  have h := eqInd (Γ := Γ) (Tm.pred (Tm.monus (Tm.succ (shift a)) (var 0)))
    (Tm.monus (shift a) (var 0)) (by simp)
    (fun ih => by simp at ih; simp [ih]) b
  simpa using h

theorem monus_succ_succ (x y : Q Γ) : monus (succ x) (succ y) = monus x y := by
  rw [monus_succ, pred_monus_succ]

@[simp] theorem monus_succ_self (x : Q Γ) : monus (succ x) x = 1 := by
  induction x using Q.ind with | _ a
  have h := eqInd (Γ := Γ) (Tm.monus (Tm.succ (var 0)) (var 0)) Tm.one (by simp)
    (fun ih => by simp at ih; simp [ih]) a
  simpa using h

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
  induction x using Q.ind with | _ a
  induction y using Q.ind with | _ b
  have h := eqInd (Γ := Γ)
    (Tm.sel (Tm.monus (shift a) (var 0)) (shift a)
      (Tm.add (var 0) (Tm.monus (shift a) (var 0))))
    (shift a) (by simp)
    (fun ih => by simp at ih ⊢; exact monus_inv_step _ _ _ ih) b
  simpa using h

theorem add_succ_of_monus_eq_succ {x y z : Q Γ} (h : monus x y = succ z) :
    succ (y + z) = x := by
  have h' := sel_monus x y
  rwa [h, sel_succ, add_succ] at h'

theorem monus_succ_eq_one_iff {a b : Q Γ} : monus (succ a) b = 1 ↔ a = b := by
  refine ⟨fun h => ?_, fun h => by rw [h, monus_succ_self]⟩
  have h' := add_succ_of_monus_eq_succ (z := 0) h
  rw [add_zero] at h'
  exact (succ_inj h').symm

/-! ### The equality test -/

theorem eqt_eq (a b : Q Γ) :
    eqt a b = sel (monus (succ a) b) 1 (pred (monus (succ a) b)) := by
  induction a using Q.ind with | _ a
  induction b using Q.ind with | _ b
  rfl

theorem eq_one_of_sel_pred (d : Q Γ) (h : sel d 1 (pred d) = 0) : d = 1 := by
  refine Q.cases d (fun e he => ?_) (fun e z he => ?_)
  · have h' := congrArg e.map h
    simp [he] at h'
    exact Q.absurd h'.symm _ _
  · have h' := congrArg e.map h
    simp [he] at h'
    simp [he, h']

/-- The equality test reflects equality, in every context. -/
@[simp] theorem eqt_eq_zero_iff {a b : Q Γ} : eqt a b = 0 ↔ a = b := by
  refine ⟨fun h => monus_succ_eq_one_iff.1 (eq_one_of_sel_pred _ (by rwa [eqt_eq] at h)),
    fun h => ?_⟩
  rw [eqt_eq, monus_succ_eq_one_iff.2 h, sel_one, pred_one]

theorem eqt_self (a : Q Γ) : eqt a a = 0 := eqt_eq_zero_iff.2 rfl

end Q

end LeanProofs.ConciseIPRA
