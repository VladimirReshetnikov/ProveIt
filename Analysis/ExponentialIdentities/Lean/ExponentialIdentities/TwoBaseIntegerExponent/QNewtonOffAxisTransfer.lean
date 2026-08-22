import Mathlib.Tactic

/-!
# Finite off-axis q-Newton transfer

This file isolates the bounded commutative-ring algebra in the exact off-axis
transfer recurrence for the geometric q-Newton connection construction.  It
contains no infinite products, convergence, branch choices, or analytic
hypotheses.
-/

namespace LeanProofs.TwoBaseIntegerExponent
namespace QNewtonOffAxisTransfer

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- The finite transfer denominator
`D a = ∏ j < a, (1 - q^(j+1) * s)`.

For the base-two row recurrence, take `q = 2` and `s = 3^c`.
-/
def transferDenominator (q s : R) (a : ℕ) : R :=
  ∏ j ∈ range a, (1 - q ^ (j + 1) * s)

@[simp] theorem transferDenominator_zero (q s : R) :
    transferDenominator q s 0 = 1 := by
  simp [transferDenominator]

theorem transferDenominator_succ (q s : R) (a : ℕ) :
    transferDenominator q s (a + 1) =
      transferDenominator q s a * (1 - q ^ (a + 1) * s) := by
  simp [transferDenominator, prod_range_succ]

/-- The finite convolution occurring in the closed solution of the transfer
recurrence. -/
def transferForcing (q s M : R) (a : ℕ) : R :=
  ∑ r ∈ range a, M ^ (a - 1 - r) * transferDenominator q s r

@[simp] theorem transferForcing_zero (q s M : R) :
    transferForcing q s M 0 = 0 := by
  simp [transferForcing]

/-- The forcing convolution obeys the same affine update as the transported
recurrence. -/
theorem transferForcing_succ (q s M : R) (a : ℕ) :
    transferForcing q s M (a + 1) =
      M * transferForcing q s M a + transferDenominator q s a := by
  rw [transferForcing, sum_range_succ]
  have hsum :
      (∑ r ∈ range a,
          M ^ (a + 1 - 1 - r) * transferDenominator q s r) =
        M * ∑ r ∈ range a,
          M ^ (a - 1 - r) * transferDenominator q s r := by
    rw [mul_sum]
    apply sum_congr rfl
    intro r hr
    have hra : r < a := mem_range.mp hr
    have hexp : a + 1 - 1 - r = (a - 1 - r) + 1 := by omega
    rw [hexp, pow_succ]
    ring
  rw [hsum]
  simp [transferForcing]

/-- A sequence satisfies the exact first-order transfer recurrence. -/
def SatisfiesTransfer (q s M kappa : R) (g : ℕ → R) : Prop :=
  ∀ a,
    (1 - q ^ (a + 1) * s) * g (a + 1) - M * g a = -kappa

/-- Multiplication by `D a` removes the changing coefficient and produces a
constant-shape inhomogeneous recurrence. -/
theorem transported_recurrence
    {q s M kappa : R} {g : ℕ → R}
    (h : SatisfiesTransfer q s M kappa g) (a : ℕ) :
    transferDenominator q s (a + 1) * g (a + 1) =
      M * (transferDenominator q s a * g a) -
        kappa * transferDenominator q s a := by
  have hstep :
      (1 - q ^ (a + 1) * s) * g (a + 1) = M * g a - kappa := by
    linear_combination h a
  rw [transferDenominator_succ, mul_assoc, hstep]
  ring

/-- Exact finite solution of the off-axis transfer recurrence:

`D a * g a = M^a * g 0 - kappa * ∑ r<a, M^(a-1-r) D r`.

This is valid over every commutative ring and requires no division or
nonvanishing assumption on the changing recurrence coefficient.
-/
theorem transfer_solution
    {q s M kappa : R} {g : ℕ → R}
    (h : SatisfiesTransfer q s M kappa g) (a : ℕ) :
    transferDenominator q s a * g a =
      M ^ a * g 0 - kappa * transferForcing q s M a := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [transported_recurrence h a, ih, transferForcing_succ]
      rw [pow_succ]
      ring

/-- The exact sum form, exposed without an auxiliary convolution name. -/
theorem transfer_solution_sum
    {q s M kappa : R} {g : ℕ → R}
    (h : SatisfiesTransfer q s M kappa g) (a : ℕ) :
    transferDenominator q s a * g a =
      M ^ a * g 0 -
        kappa *
          ∑ r ∈ range a,
            M ^ (a - 1 - r) * transferDenominator q s r := by
  simpa [transferForcing] using transfer_solution h a

end QNewtonOffAxisTransfer
end LeanProofs.TwoBaseIntegerExponent
