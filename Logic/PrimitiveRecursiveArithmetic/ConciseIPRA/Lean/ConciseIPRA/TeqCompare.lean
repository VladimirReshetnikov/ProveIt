import ConciseIPRA.TeqParity

/-!
# A comparator from scalar iteration

`pow2 x = I(x, 1; u. u + u)` is `2 ^ x`, and `hops y a = I(y, a; u. hop u)`
replaces up to `y` factors two of `a` by factors three.  The parity of
`hops y (pow2 x)` is therefore `1` exactly when no factor two survives, that
is, when `x ≤ y`.  Inside `T_eq` only the three recursion equations of

  `cmp x y = par (hops y (pow2 x))`

are needed: `cmp 0 y = 1`, `cmp (S x) 0 = 0` and `cmp (S x) (S y) = cmp x y`.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {n m : ℕ}

/-- The iterated factor map `I(y, a; u. hop u)`. -/
def Tm.hops (y a : Tm n) : Tm n := Tm.iter y a (Tm.hop (Syn.var 0))

/-- The power of two `I(x, 1; u. u + u)`. -/
def Tm.pow2 (x : Tm n) : Tm n := Tm.iter x Tm.one (Tm.add (Syn.var 0) (Syn.var 0))

/-- The comparator: the indicator of `x ≤ y`. -/
def Tm.cmp (x y : Tm n) : Tm n := Tm.par (Tm.hops y (Tm.pow2 x))

@[simp] theorem Tm.subst_hops (σ : Fin n → Tm m) (y a : Tm n) :
    Syn.subst σ (Tm.hops y a) = Tm.hops (Syn.subst σ y) (Syn.subst σ a) := by
  simp [Tm.hops]

@[simp] theorem Tm.subst_pow2 (σ : Fin n → Tm m) (x : Tm n) :
    Syn.subst σ (Tm.pow2 x) = Tm.pow2 (Syn.subst σ x) := by
  simp [Tm.pow2]

@[simp] theorem Tm.subst_cmp (σ : Fin n → Tm m) (x y : Tm n) :
    Syn.subst σ (Tm.cmp x y) = Tm.cmp (Syn.subst σ x) (Syn.subst σ y) := by
  simp [Tm.cmp]

lift_op₂ hops cmp
lift_op₁ pow2

namespace Q

variable {Γ : List (Fm Tm n)}

/-! ### The iterated factor map -/

@[simp] theorem hops_zero (x : Q Γ) : hops 0 x = x := by
  induction x using Q.ind with | _ a
  exact sound (Teq.iterZero a _)

@[simp] theorem hops_succ (y x : Q Γ) : hops (succ y) x = hop (hops y x) := by
  induction y using Q.ind with | _ b
  induction x using Q.ind with | _ a
  have h := Teq.iterSucc (Γ := Γ) b a (Tm.hop (var 0))
  simp only [Tm.subst_hop, Syn.subst_var, Syn.inst_zero] at h
  exact sound h

/-- Rotation: the factor map may be applied to the seed instead. -/
theorem hop_hops (y x : Q Γ) : hop (hops y x) = hops y (hop x) := by
  induction y using Q.ind with | _ b
  induction x using Q.ind with | _ a
  have h := eqInd (Γ := Γ) (Tm.hop (Tm.hops (var 0) (shift a)))
    (Tm.hops (var 0) (Tm.hop (shift a))) (by simp)
    (fun ih => by simp at ih; simp [ih]) b
  simpa using h

/-- Scaling: the iterated factor map commutes with tripling. -/
theorem hops_triple (y x : Q Γ) : hops y (x + x + x) = hops y x + hops y x + hops y x := by
  induction y using Q.ind with | _ b
  induction x using Q.ind with | _ a
  have h := eqInd (Γ := Γ)
    (Tm.hops (var 0) (Tm.add (Tm.add (shift a) (shift a)) (shift a)))
    (Tm.add (Tm.add (Tm.hops (var 0) (shift a)) (Tm.hops (var 0) (shift a)))
      (Tm.hops (var 0) (shift a)))
    (by simp) (fun ih => by simp at ih; simp [ih, hop_triple]) b
  simpa using h

@[simp] theorem hops_one (y : Q Γ) : hops y 1 = 1 := by
  induction y using Q.ind with | _ b
  have h := eqInd (Γ := Γ) (Tm.hops (var 0) Tm.one) Tm.one (by simp)
    (fun ih => by simp at ih; simp [ih]) b
  simpa using h

/-! ### Powers of two and the comparator -/

@[simp] theorem pow2_zero : pow2 (0 : Q Γ) = 1 := by
  show mk Γ (Tm.pow2 Tm.zero) = mk Γ Tm.one
  exact sound (Teq.iterZero _ _)

@[simp] theorem pow2_succ (x : Q Γ) : pow2 (succ x) = pow2 x + pow2 x := by
  induction x using Q.ind with | _ a
  have h := Teq.iterSucc (Γ := Γ) a Tm.one (Tm.add (var 0) (var 0))
  simp only [Tm.subst_add, Syn.subst_var, Syn.inst_zero] at h
  exact sound h

theorem cmp_eq (x y : Q Γ) : cmp x y = par (hops y (pow2 x)) := by
  induction x using Q.ind with | _ a
  induction y using Q.ind with | _ b
  rfl

@[simp] theorem cmp_zero (y : Q Γ) : cmp 0 y = 1 := by
  rw [cmp_eq, pow2_zero, hops_one, par_one]

@[simp] theorem cmp_succ_zero (x : Q Γ) : cmp (succ x) 0 = 0 := by
  rw [cmp_eq, pow2_succ, hops_zero, par_double]

@[simp] theorem cmp_succ_succ (x y : Q Γ) : cmp (succ x) (succ y) = cmp x y := by
  rw [cmp_eq, cmp_eq, pow2_succ, hops_succ, hop_hops, hop_double, hops_triple, par_triple]

@[simp] theorem cmp_one_zero : cmp (1 : Q Γ) 0 = 0 := cmp_succ_zero 0

@[simp] theorem cmp_one_succ (y : Q Γ) : cmp 1 (succ y) = 1 := by
  show cmp (succ 0) (succ y) = 1
  rw [cmp_succ_succ, cmp_zero]

@[simp] theorem cmp_succ_one (x : Q Γ) : cmp (succ x) 1 = cmp x 0 := by
  show cmp (succ x) (succ 0) = cmp x 0
  rw [cmp_succ_succ]

/-- The diagonal just above the comparison threshold. -/
@[simp] theorem cmp_succ_self (x : Q Γ) : cmp (succ x) x = 0 := by
  induction x using Q.ind with | _ a
  have h := eqInd (Γ := Γ) (Tm.cmp (Tm.succ (var 0)) (var 0)) Tm.zero (by simp)
    (fun ih => by simp at ih; simp [ih]) a
  simpa using h

end Q

end LeanProofs.ConciseIPRA
