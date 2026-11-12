import ConciseIPRA.TeqCompare

/-!
# Predecessor in `T_eq`

A saturating counter turns the comparator into a predecessor term.  Put

  `bump k u = sel (cmp (S (S u)) k) u (S u)`,  `sat t k = I(t, 0; u. bump k u)`,

so that `sat t k` counts up to `t` but stops below `k`.  The conjugacy
`bump (S k) (S u) = S (bump k u)` gives `sat (S t) (S (S m)) = S (sat t (S m))`,
hence `sat n (S n) = n`, and the term

  `pred m = sat m m`

satisfies `pred 0 = 0` and `pred (S m) = m`.  Consequently the successor is
injective, and `S x = 0` collapses the context.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {n m : ℕ}

/-- One saturating step: increment `u` while `u + 2 ≤ k`. -/
def Tm.bump (k u : Tm n) : Tm n :=
  Tm.sel (Tm.cmp (Tm.succ (Tm.succ u)) k) u (Tm.succ u)

/-- The saturating counter `I(t, 0; u. bump k u)`. -/
def Tm.sat (t k : Tm n) : Tm n := Tm.iter t Tm.zero (Tm.bump (Syn.shift k) (Syn.var 0))

/-- The predecessor term. -/
def Tm.pred (a : Tm n) : Tm n := Tm.sat a a

lift_op₂ bump sat
lift_op₁ pred

namespace Q

variable {Γ : List (Fm Tm n)}

/-- The selector commutes with a successor on both branches. -/
theorem sel_succ_succ (c x y : Q Γ) : sel c (succ x) (succ y) = succ (sel c x y) := by
  refine Q.cases c (fun e he => ?_) (fun e z he => ?_) <;> simp [he]

/-- A selector with equal branches. -/
@[simp] theorem sel_self (c x : Q Γ) : sel c x x = x := by
  refine Q.cases c (fun e he => ?_) (fun e z he => ?_) <;> simp [he]

theorem bump_eq (k u : Q Γ) : bump k u = sel (cmp (succ (succ u)) k) u (succ u) := by
  induction k, u using Q.ind₂ with | _ a b => rfl

@[simp] theorem bump_succ_succ (k u : Q Γ) : bump (succ k) (succ u) = succ (bump k u) := by
  rw [bump_eq, cmp_succ_succ, sel_succ_succ, ← bump_eq]

@[simp] theorem bump_succ_succ_zero (k : Q Γ) : bump (succ (succ k)) 0 = 1 := by
  rw [bump_eq, cmp_succ_succ, cmp_succ_succ, cmp_zero, sel_one]
  rfl

@[simp] theorem sat_zero (k : Q Γ) : sat 0 k = 0 := by
  induction k using Q.ind with | _ a => exact sound (Teq.iterZero _ _)

@[simp] theorem sat_succ (t k : Q Γ) : sat (succ t) k = bump k (sat t k) := by
  induction t, k using Q.ind₂ with | _ a b
  have h := Teq.iterSucc (Γ := Γ) a Tm.zero (Tm.bump (shift b) (var 0))
  simp only [Tm.subst_bump, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h
  exact sound h

/-- Conjugacy of the saturating counters at consecutive caps. -/
theorem bump_sat_succ (t k : Q Γ) :
    bump (succ (succ k)) (sat t (succ (succ k))) = succ (sat t (succ k)) := by
  induction t, k using Q.ind₂ with | _ a b
  simpa using eqInd (Γ := Γ)
    (Tm.bump (Tm.succ (Tm.succ (shift b))) (Tm.sat (var 0) (Tm.succ (Tm.succ (shift b)))))
    (Tm.succ (Tm.sat (var 0) (Tm.succ (shift b)))) a

/-- Below its cap the counter does not saturate. -/
@[simp] theorem sat_self_succ (x : Q Γ) : sat x (succ x) = x := by
  induction x using Q.ind with | _ a
  simpa using eqInd (Γ := Γ) (Tm.sat (var 0) (Tm.succ (var 0))) (var 0) a
    (hS := fun ih => by simp at ih; simp [bump_sat_succ, ih])

theorem pred_eq (x : Q Γ) : pred x = sat x x := by
  induction x using Q.ind with | _ a => rfl

@[simp] theorem pred_zero : pred (0 : Q Γ) = 0 := by rw [pred_eq, sat_zero]

@[simp] theorem pred_succ (x : Q Γ) : pred (succ x) = x := by
  rw [pred_eq, sat_succ, sat_self_succ, bump_eq, cmp_succ_succ, cmp_succ_self, sel_zero]

@[simp] theorem pred_one : pred (1 : Q Γ) = 0 := pred_succ 0

/-- The successor is injective in `T_eq`. -/
theorem succ_inj {x y : Q Γ} (h : succ x = succ y) : x = y := by
  have h' := congrArg pred h
  rwa [pred_succ, pred_succ] at h'

@[simp] theorem succ_inj_iff {x y : Q Γ} : succ x = succ y ↔ x = y :=
  ⟨succ_inj, fun h => by rw [h]⟩

/-- A successor equal to zero collapses the context. -/
theorem zero_eq_one_of_succ_eq_zero {x : Q Γ} (h : succ x = 0) : (0 : Q Γ) = 1 := by
  have h' := congrArg zf h
  rwa [zf_succ, zf_zero] at h'

/-- A successor equal to zero identifies all classes. -/
theorem absurd_succ {x : Q Γ} (h : succ x = 0) (y z : Q Γ) : y = z :=
  Q.absurd (zero_eq_one_of_succ_eq_zero h) y z

end Q

end LeanProofs.ConciseIPRA
