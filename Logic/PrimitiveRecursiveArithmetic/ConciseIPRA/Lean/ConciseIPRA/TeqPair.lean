import ConciseIPRA.TeqOrder

/-!
# Pairing in `T_eq`

The pairing function is `pair a b = 2 ^ (a + b) + a`.  Since `a < 2 ^ (a + b)`,
the exponent is the binary logarithm of the pair, and the logarithm is a
saturating counter:

  `lstep k v = sel (2 ^ (S v) ∸ k) (S v) v`,  `lgc t k = I(t, 0; v. lstep k v)`,
  `lg w = lgc w w`.

The counter follows its index up to the exponent and then stays there, so
`lg (pair a b) = a + b`, and the projections

  `pfst w = w ∸ 2 ^ (lg w)`,  `psnd w = lg w ∸ pfst w`

satisfy `pfst (pair a b) = a` and `psnd (pair a b) = b` in every context.  No
multiplication is involved.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {n m : ℕ}

/-- One step of the logarithm counter: increment `v` while `2 ^ (v + 1) ≤ k`. -/
def Tm.lstep (k v : Tm n) : Tm n :=
  Tm.sel (Tm.monus (Tm.pow2 (Tm.succ v)) k) (Tm.succ v) v

/-- The logarithm counter `I(t, 0; v. lstep k v)`. -/
def Tm.lgc (t k : Tm n) : Tm n := Tm.iter t Tm.zero (Tm.lstep (Syn.shift k) (Syn.var 0))

/-- The binary logarithm. -/
def Tm.lg (a : Tm n) : Tm n := Tm.lgc a a

/-- The pairing function `2 ^ (a + b) + a`. -/
def Tm.pair (a b : Tm n) : Tm n := Tm.add (Tm.pow2 (Tm.add a b)) a

/-- The first projection. -/
def Tm.pfst (w : Tm n) : Tm n := Tm.monus w (Tm.pow2 (Tm.lg w))

/-- The second projection. -/
def Tm.psnd (w : Tm n) : Tm n := Tm.monus (Tm.lg w) (Tm.pfst w)

lift_op₂ lstep lgc
lift_op₁ lg
lift_op₂ pair
lift_op₁ pfst psnd

namespace Q

variable {Γ : List (Fm Tm n)}

/-! ### The logarithm counter -/

theorem lstep_eq (k v : Q Γ) :
    lstep k v = sel (monus (pow2 (succ v)) k) (succ v) v := by
  induction k, v using Q.ind₂ with | _ a b => rfl

@[simp] theorem lgc_zero (k : Q Γ) : lgc 0 k = 0 := by
  induction k using Q.ind with | _ a => exact sound (Teq.iterZero _ _)

@[simp] theorem lgc_succ (t k : Q Γ) : lgc (succ t) k = lstep k (lgc t k) := by
  induction t, k using Q.ind₂ with | _ a b
  have h := Teq.iterSucc (Γ := Γ) a Tm.zero (Tm.lstep (shift b) (var 0))
  simp only [Tm.subst_lstep, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h
  exact sound h

theorem lg_eq (x : Q Γ) : lg x = lgc x x := by
  induction x using Q.ind with | _ a => rfl

/-- While `2 ^ i ≤ k` the counter follows its index: the induction step, in which
`2 ^ (i + 1) = 2 ^ i + 2 ^ i ≤ k` gives `2 ^ i ≤ k`. -/
theorem lgc_low_step (i k r : Q Γ) (ih : sel (monus (pow2 i) k) r i = i) :
    sel (monus (pow2 i + pow2 i) k) (lstep k r) (succ i) = succ i := by
  refine Q.cases (monus (pow2 i + pow2 i) k) (fun e he => ?_) (fun e z he => ?_)
  · have ih' := congrArg e.map ih
    simp only [Ext.map_sel, Ext.map_monus, Ext.map_add, Ext.map_succ, Ext.map_pow2,
      Ext.map_lstep] at he ih' ⊢
    rw [le_of_add_le he, sel_zero] at ih'
    rw [he, sel_zero, ih', lstep_eq, pow2_succ, he, sel_zero]
  · simp only [Ext.map_sel, Ext.map_succ, he, sel_succ]

/-- While `2 ^ i ≤ k` the counter follows its index. -/
theorem sel_lgc_low (k i : Q Γ) : sel (monus (pow2 i) k) (lgc i k) i = i := by
  induction k, i using Q.ind₂ with | _ k i
  simpa using eqInd (Γ := Γ)
    (Tm.sel (Tm.monus (Tm.pow2 (var 0)) (shift k)) (Tm.lgc (var 0) (shift k)) (var 0))
    (var 0) i (hS := fun ih => by simp at ih ⊢; exact lgc_low_step _ _ _ ih)

theorem lgc_low (c a : Q Γ) : lgc c (pow2 c + a) = c := by
  have h := sel_lgc_low (pow2 c + a) c
  rwa [monus_add_right, sel_zero] at h

/-- At the exponent of a pair the counter stops. -/
theorem lstep_pair (a b : Q Γ) : lstep (pow2 (a + b) + a) (a + b) = a + b := by
  have hp := add_monus_of_le (succ_le_pow2 (a + b))
  generalize monus (pow2 (a + b)) (succ (a + b)) = d at hp
  have e : pow2 (a + b) + pow2 (a + b) = (pow2 (a + b) + a) + succ (b + d) := by
    conv_lhs => rhs; rw [← hp]
    simp only [succ_add, add_succ, succ_inj_iff]
    abel
  rw [lstep_eq, pow2_succ, e, monus_add_left, sel_succ]

theorem lgc_pair_add (a b j : Q Γ) : lgc (a + b + j) (pow2 (a + b) + a) = a + b := by
  induction a, b, j using Q.ind₃ with | _ a b j
  simpa using eqInd (Γ := Γ)
    (Tm.lgc (Tm.add (Tm.add (shift a) (shift b)) (var 0))
      (Tm.add (Tm.pow2 (Tm.add (shift a) (shift b))) (shift a)))
    (Tm.add (shift a) (shift b)) j (by simp [lgc_low])
    (fun ih => by simp at ih; simp [add_succ, ih, lstep_pair])

/-! ### Pairing -/

theorem pair_eq (a b : Q Γ) : pair a b = pow2 (a + b) + a := by
  induction a, b using Q.ind₂ with | _ a b => rfl

theorem pfst_eq (w : Q Γ) : pfst w = monus w (pow2 (lg w)) := by
  induction w using Q.ind with | _ a => rfl

theorem psnd_eq (w : Q Γ) : psnd w = monus (lg w) (pfst w) := by
  induction w using Q.ind with | _ a => rfl

@[simp] theorem lg_pair (a b : Q Γ) : lg (pair a b) = a + b := by
  have hle : monus (a + b) (pow2 (a + b) + a) = 0 :=
    le_add_right (le_of_succ_le (succ_le_pow2 (a + b))) a
  have h := lgc_pair_add a b (monus (pow2 (a + b) + a) (a + b))
  rw [add_monus_of_le hle] at h
  rw [lg_eq, pair_eq]
  exact h

@[simp] theorem pfst_pair (a b : Q Γ) : pfst (pair a b) = a := by
  rw [pfst_eq, lg_pair, pair_eq, monus_add_left]

@[simp] theorem psnd_pair (a b : Q Γ) : psnd (pair a b) = b := by
  rw [psnd_eq, lg_pair, pfst_pair, monus_add_left]

end Q

end LeanProofs.ConciseIPRA
