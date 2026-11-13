import ConciseIPRA.EqArith

/-!
# Parity, the three-cycle and the ramp in the equational calculus

The lemmas of `TeqParity` for `EQ Γ`.  The Boolean case splits of that module are
replaced by equation cases on a fresh variable (`EQ.eqInd` with an unused
hypothesis), as in the note `equational_predecessor` of the package
`uniform_raw`.
-/

namespace LeanProofs.ConciseIPRA

open Syn

variable {n m : ℕ}

lift_eop₁ zf par cyc mod3 ramp hop

namespace EQ

variable {Γ : ECtx n}

/-! ### The zero test and the parity -/

theorem zf_eq (x : EQ Γ) : zf x = sel x 1 0 := by
  induction x using EQ.ind with | _ a => rfl

@[simp] theorem zf_zero : zf (0 : EQ Γ) = 1 := by rw [zf_eq, sel_zero]

@[simp] theorem zf_succ (x : EQ Γ) : zf (succ x) = 0 := by rw [zf_eq, sel_succ]

@[simp] theorem zf_one : zf (1 : EQ Γ) = 0 := zf_succ 0

@[simp] theorem par_zero : par (0 : EQ Γ) = 0 := sound (EqPrf.iterZero _ _)

@[simp] theorem par_succ (x : EQ Γ) : par (succ x) = zf (par x) := by
  induction x using EQ.ind with | _ a => exact sound (EqPrf.iterSucc a Tm.zero (Tm.zf (var 0)))

@[simp] theorem par_one : par (1 : EQ Γ) = 1 := by
  show par (succ 0) = 1
  rw [par_succ, par_zero, zf_zero]

/-- The parity is a Boolean: it is fixed by the double zero test. -/
@[simp] theorem zf_zf_par (x : EQ Γ) : zf (zf (par x)) = par x := by
  induction x using EQ.ind with | _ a
  simpa using eqInd (Γ := Γ) (Tm.zf (Tm.zf (Tm.par (var 0)))) (Tm.par (var 0)) a

/-- The zero test and its double, by cases on a fresh variable. -/
theorem zf_add_zf (v : EQ Γ) : zf v + zf (zf v) = 1 := by
  induction v using EQ.ind with | _ a
  simpa using eqInd (Γ := Γ) (Tm.add (Tm.zf (var 0)) (Tm.zf (Tm.zf (var 0)))) Tm.one a
    (hS := fun _ => by simp)

/-- The parity and its negation add up to one. -/
theorem par_add_zf (x : EQ Γ) : par x + zf (par x) = 1 := by
  have h := zf_add_zf (zf (par x))
  rwa [zf_zf_par] at h

/-- A selector of sums, by cases on its count. -/
theorem sel_add (e a b c d : EQ Γ) : sel e (a + b) (c + d) = sel e a c + sel e b d := by
  induction e using EQ.ind with | _ e
  induction a, b using EQ.ind₂ with | _ a b
  induction c, d using EQ.ind₂ with | _ c d
  simpa using eqInd (Γ := Γ)
    (Tm.sel (var 0) (Tm.add (shift a) (shift b)) (Tm.add (shift c) (shift d)))
    (Tm.add (Tm.sel (var 0) (shift a) (shift c)) (Tm.sel (var 0) (shift b) (shift d))) e
    (hS := fun _ => by simp)

/-- A selector between its count and zero. -/
theorem sel_self_zero (e : EQ Γ) : sel e e 0 = 0 := by
  induction e using EQ.ind with | _ e
  simpa using eqInd (Γ := Γ) (Tm.sel (var 0) (var 0) Tm.zero) Tm.zero e (hS := fun _ => by simp)

theorem par_double (x : EQ Γ) : par (x + x) = 0 := by
  induction x using EQ.ind with | _ a
  simpa using eqInd (Γ := Γ) (Tm.par (Tm.add (var 0) (var 0))) Tm.zero a

theorem par_triple (x : EQ Γ) : par (x + x + x) = par x := by
  induction x using EQ.ind with | _ a
  simpa using eqInd (Γ := Γ) (Tm.par (Tm.add (Tm.add (var 0) (var 0)) (var 0))) (Tm.par (var 0)) a

/-! ### The three-cycle -/

theorem cyc_eq (x : EQ Γ) : cyc x = zf x + (par x + par x) := by
  induction x using EQ.ind with | _ a => rfl

@[simp] theorem cyc_zero : cyc (0 : EQ Γ) = 1 := by simp [cyc_eq]

@[simp] theorem cyc_one : cyc (1 : EQ Γ) = succ 1 := by simp [cyc_eq]

@[simp] theorem cyc_succ_one : cyc (succ (1 : EQ Γ)) = 0 := by simp [cyc_eq]

@[simp] theorem mod3_zero : mod3 (0 : EQ Γ) = 0 := sound (EqPrf.iterZero _ _)

@[simp] theorem mod3_succ (x : EQ Γ) : mod3 (succ x) = cyc (mod3 x) := by
  induction x using EQ.ind with | _ a => exact sound (EqPrf.iterSucc a Tm.zero (Tm.cyc (var 0)))

/-! ### The ramp -/

@[simp] theorem ramp_zero : ramp (0 : EQ Γ) = 0 := sound (EqPrf.iterZero _ _)

theorem ramp_succ_mod3 (x : EQ Γ) : ramp (succ x) = succ (ramp x + mod3 (ramp x)) := by
  induction x using EQ.ind with | _ a
  exact sound (EqPrf.iterSucc a Tm.zero (Tm.succ (Tm.add (var 0) (Tm.mod3 (var 0)))))

/-- One more step of the three-cycle, by cases on a fresh variable. -/
theorem mod3_step (g v : EQ Γ) :
    mod3 (succ (g + zf v)) = sel v (cyc (cyc (mod3 g))) (cyc (mod3 g)) := by
  induction g, v using EQ.ind₂ with | _ g v
  simpa using eqInd (Γ := Γ) (Tm.mod3 (Tm.succ (Tm.add (shift g) (Tm.zf (var 0)))))
    (Tm.sel (var 0) (Tm.cyc (Tm.cyc (Tm.mod3 (shift g)))) (Tm.cyc (Tm.mod3 (shift g)))) v
    (hS := fun _ => by simp)

/-- The two cycle values selected by a Boolean, by cases on a fresh variable. -/
theorem sel_cyc_zf (v : EQ Γ) : sel v (cyc (cyc (zf v))) (cyc (zf v)) = zf (zf v) := by
  induction v using EQ.ind with | _ v
  simpa using eqInd (Γ := Γ)
    (Tm.sel (var 0) (Tm.cyc (Tm.cyc (Tm.zf (var 0)))) (Tm.cyc (Tm.zf (var 0))))
    (Tm.zf (Tm.zf (var 0))) v (hS := fun _ => by simp)

/-- The ramp invariant: the residue of the ramp is the parity of its counter. -/
@[simp] theorem mod3_ramp (x : EQ Γ) : mod3 (ramp x) = par x := by
  induction x using EQ.ind with | _ a
  simpa using eqInd (Γ := Γ) (Tm.mod3 (Tm.ramp (var 0))) (Tm.par (var 0)) a
    (hS := fun ih => by
      simp at ih
      have h1 := mod3_step (Γ := (Tm.mod3 (Tm.ramp (var 0)), Tm.par (var 0)) :: Γ.shift)
        (ramp (mk _ (var 0))) (zf (par (mk _ (var 0))))
      have h2 := sel_cyc_zf (Γ := (Tm.mod3 (Tm.ramp (var 0)), Tm.par (var 0)) :: Γ.shift)
        (zf (par (mk _ (var 0))))
      rw [zf_zf_par] at h1 h2
      rw [ih] at h1
      simp [ramp_succ_mod3, ih]
      exact (mod3_succ _).symm.trans (h1.trans h2))

@[simp] theorem ramp_succ (x : EQ Γ) : ramp (succ x) = succ (ramp x + par x) := by
  rw [ramp_succ_mod3, mod3_ramp]

theorem ramp_double (x : EQ Γ) : ramp (x + x) = x + x + x := by
  induction x using EQ.ind with | _ a
  simpa using eqInd (Γ := Γ) (Tm.ramp (Tm.add (var 0) (var 0)))
    (Tm.add (Tm.add (var 0) (var 0)) (var 0)) a
    (hS := fun ih => by simp at ih; simp [ih, par_double])

theorem ramp_triple (x : EQ Γ) : ramp (x + x + x) = ramp x + ramp x + ramp x + par x := by
  induction x using EQ.ind with | _ a
  simpa using eqInd (Γ := Γ) (Tm.ramp (Tm.add (Tm.add (var 0) (var 0)) (var 0)))
    (Tm.add (Tm.add (Tm.add (Tm.ramp (var 0)) (Tm.ramp (var 0))) (Tm.ramp (var 0)))
      (Tm.par (var 0))) a
    (hS := fun ih => by
      simp at ih
      simp [ih, par_triple]
      refine congrArg succ (congrArg succ (congrArg succ ?_))
      abel)

/-! ### The factor map -/

theorem hop_eq (x : EQ Γ) : hop x = sel (par x) (ramp x) x := by
  induction x using EQ.ind with | _ a => rfl

theorem hop_double (x : EQ Γ) : hop (x + x) = x + x + x := by
  rw [hop_eq, par_double, sel_zero, ramp_double]

@[simp] theorem hop_one : hop (1 : EQ Γ) = 1 := by
  rw [hop_eq, par_one, sel_one]

theorem hop_triple (x : EQ Γ) : hop (x + x + x) = hop x + hop x + hop x := by
  simp only [hop_eq, par_triple, ramp_triple]
  rw [← add_zero (x + x + x), sel_add, sel_add, sel_add, sel_self_zero, add_zero]

end EQ

end LeanProofs.ConciseIPRA
