import ConciseIPRA.EqCompare

/-!
# The predecessor in the equational calculus

The lemmas of `TeqPred` for `EQ Γ`: `EQ.pred_succ`, and so
`EqPrf.pred_succ : EqPrf Γ (Tm.pred (succ t)) t` for every term `t` and every
context.  No coverage, separation or case rule is used.
-/

namespace LeanProofs.ConciseIPRA

open Syn

variable {n m : ℕ}

lift_eop₂ bump sat
lift_eop₁ pred

namespace EQ

variable {Γ : ECtx n}

/-- The selector commutes with a successor on both branches. -/
theorem sel_succ_succ (c x y : EQ Γ) : sel c (succ x) (succ y) = succ (sel c x y) := by
  induction c, x, y using EQ.ind₃ with | _ c a b
  simpa using eqInd (Γ := Γ) (Tm.sel (var 0) (Tm.succ (shift a)) (Tm.succ (shift b)))
    (Tm.succ (Tm.sel (var 0) (shift a) (shift b))) c (hS := fun _ => by simp)

/-- A selector with equal branches. -/
@[simp] theorem sel_self (c x : EQ Γ) : sel c x x = x := by
  induction c, x using EQ.ind₂ with | _ c a
  simpa using eqInd (Γ := Γ) (Tm.sel (var 0) (shift a) (shift a)) (shift a) c
    (hS := fun _ => by simp)

theorem bump_eq (k u : EQ Γ) : bump k u = sel (cmp (succ (succ u)) k) u (succ u) := by
  induction k, u using EQ.ind₂ with | _ a b => rfl

@[simp] theorem bump_succ_succ (k u : EQ Γ) : bump (succ k) (succ u) = succ (bump k u) := by
  rw [bump_eq, cmp_succ_succ, sel_succ_succ, ← bump_eq]

@[simp] theorem bump_succ_succ_zero (k : EQ Γ) : bump (succ (succ k)) 0 = 1 := by
  rw [bump_eq, cmp_succ_succ, cmp_succ_succ, cmp_zero, sel_one]
  rfl

@[simp] theorem sat_zero (k : EQ Γ) : sat 0 k = 0 := by
  induction k using EQ.ind with | _ a => exact sound (EqPrf.iterZero _ _)

@[simp] theorem sat_succ (t k : EQ Γ) : sat (succ t) k = bump k (sat t k) := by
  induction t, k using EQ.ind₂ with | _ a b
  have h := EqPrf.iterSucc (Γ := Γ) a Tm.zero (Tm.bump (shift b) (var 0))
  simp only [Tm.subst_bump, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h
  exact sound h

/-- Conjugacy of the saturating counters at consecutive caps. -/
theorem bump_sat_succ (t k : EQ Γ) :
    bump (succ (succ k)) (sat t (succ (succ k))) = succ (sat t (succ k)) := by
  induction t, k using EQ.ind₂ with | _ a b
  simpa using eqInd (Γ := Γ)
    (Tm.bump (Tm.succ (Tm.succ (shift b))) (Tm.sat (var 0) (Tm.succ (Tm.succ (shift b)))))
    (Tm.succ (Tm.sat (var 0) (Tm.succ (shift b)))) a

/-- Below its cap the counter does not saturate. -/
@[simp] theorem sat_self_succ (x : EQ Γ) : sat x (succ x) = x := by
  induction x using EQ.ind with | _ a
  simpa using eqInd (Γ := Γ) (Tm.sat (var 0) (Tm.succ (var 0))) (var 0) a
    (hS := fun ih => by simp at ih; simp [bump_sat_succ, ih])

theorem pred_eq (x : EQ Γ) : pred x = sat x x := by
  induction x using EQ.ind with | _ a => rfl

@[simp] theorem pred_zero : pred (0 : EQ Γ) = 0 := by rw [pred_eq, sat_zero]

@[simp] theorem pred_succ (x : EQ Γ) : pred (succ x) = x := by
  rw [pred_eq, sat_succ, sat_self_succ, bump_eq, cmp_succ_succ, cmp_succ_self, sel_zero]

@[simp] theorem pred_one : pred (1 : EQ Γ) = 0 := pred_succ 0

/-- The successor is injective in `T_eq`. -/
theorem succ_inj {x y : EQ Γ} (h : succ x = succ y) : x = y := by
  have h' := congrArg pred h
  rwa [pred_succ, pred_succ] at h'

@[simp] theorem succ_inj_iff {x y : EQ Γ} : succ x = succ y ↔ x = y :=
  ⟨succ_inj, fun h => by rw [h]⟩

/-- A successor equal to zero collapses the context. -/
theorem zero_eq_one_of_succ_eq_zero {x : EQ Γ} (h : succ x = 0) : (0 : EQ Γ) = 1 := by
  have h' := congrArg zf h
  rwa [zf_succ, zf_zero] at h'

end EQ

variable {Γ : ECtx n}

/-- **The predecessor in the equational calculus.** -/
theorem EqPrf.pred_succ (t : Tm n) : EqPrf Γ (Tm.pred (Tm.succ t)) t :=
  EQ.exact (by simp)

theorem EqPrf.pred_zero : EqPrf Γ (Tm.pred (Tm.zero : Tm n)) Tm.zero :=
  EQ.exact (by simp)

/-- **The successor is injective in the equational calculus.** -/
theorem EqPrf.succ_inj {s t : Tm n} (h : EqPrf Γ (Tm.succ s) (Tm.succ t)) : EqPrf Γ s t :=
  EQ.exact (EQ.succ_inj (by simpa using EQ.sound h))

end LeanProofs.ConciseIPRA
