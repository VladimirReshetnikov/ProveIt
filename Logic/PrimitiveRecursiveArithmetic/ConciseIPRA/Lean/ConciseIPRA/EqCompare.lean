import ConciseIPRA.EqParity

/-!
# The comparator in the equational calculus

The lemmas of `TeqCompare` for `EQ Γ`.
-/

namespace LeanProofs.ConciseIPRA

open Syn

variable {n m : ℕ}

lift_eop₂ hops
lift_eop₁ pow2
lift_eop₂ cmp

namespace EQ

variable {Γ : ECtx n}

/-! ### The iterated factor map -/

@[simp] theorem hops_zero (x : EQ Γ) : hops 0 x = x := by
  induction x using EQ.ind with | _ a => exact sound (EqPrf.iterZero a _)

@[simp] theorem hops_succ (y x : EQ Γ) : hops (succ y) x = hop (hops y x) := by
  induction y, x using EQ.ind₂ with | _ b a
  have h := EqPrf.iterSucc (Γ := Γ) b a (Tm.hop (var 0))
  simp only [Tm.subst_hop, Syn.subst_var, Syn.inst_zero] at h
  exact sound h

/-- Rotation: the factor map may be applied to the seed instead. -/
theorem hop_hops (y x : EQ Γ) : hop (hops y x) = hops y (hop x) := by
  induction y, x using EQ.ind₂ with | _ b a
  simpa using eqInd (Γ := Γ) (Tm.hop (Tm.hops (var 0) (shift a)))
    (Tm.hops (var 0) (Tm.hop (shift a))) b

/-- Scaling: the iterated factor map commutes with tripling. -/
theorem hops_triple (y x : EQ Γ) : hops y (x + x + x) = hops y x + hops y x + hops y x := by
  induction y, x using EQ.ind₂ with | _ b a
  simpa using eqInd (Γ := Γ)
    (Tm.hops (var 0) (Tm.add (Tm.add (shift a) (shift a)) (shift a)))
    (Tm.add (Tm.add (Tm.hops (var 0) (shift a)) (Tm.hops (var 0) (shift a)))
      (Tm.hops (var 0) (shift a))) b (hS := fun ih => by simp at ih; simp [ih, hop_triple])

@[simp] theorem hops_one (y : EQ Γ) : hops y 1 = 1 := by
  induction y using EQ.ind with | _ b
  simpa using eqInd (Γ := Γ) (Tm.hops (var 0) Tm.one) Tm.one b

/-! ### Powers of two and the comparator -/

@[simp] theorem pow2_zero : pow2 (0 : EQ Γ) = 1 := sound (EqPrf.iterZero _ _)

@[simp] theorem pow2_succ (x : EQ Γ) : pow2 (succ x) = pow2 x + pow2 x := by
  induction x using EQ.ind with | _ a => exact sound (EqPrf.iterSucc a Tm.one (Tm.add (var 0) (var 0)))

theorem cmp_eq (x y : EQ Γ) : cmp x y = par (hops y (pow2 x)) := by
  induction x, y using EQ.ind₂ with | _ a b => rfl

@[simp] theorem cmp_zero (y : EQ Γ) : cmp 0 y = 1 := by
  rw [cmp_eq, pow2_zero, hops_one, par_one]

@[simp] theorem cmp_succ_zero (x : EQ Γ) : cmp (succ x) 0 = 0 := by
  rw [cmp_eq, pow2_succ, hops_zero, par_double]

@[simp] theorem cmp_succ_succ (x y : EQ Γ) : cmp (succ x) (succ y) = cmp x y := by
  rw [cmp_eq, cmp_eq, pow2_succ, hops_succ, hop_hops, hop_double, hops_triple, par_triple]

@[simp] theorem cmp_one_zero : cmp (1 : EQ Γ) 0 = 0 := cmp_succ_zero 0

end EQ

end LeanProofs.ConciseIPRA
