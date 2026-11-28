import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Algebra.Polynomial.Derivative

/-! Derivative identities used in identifying the local different.
The first two statements apply directly to each prime-power root. -/

namespace VacuumFrame.Cyclotomic

open Polynomial

theorem slope_at_primitive_prime_power {R : Type*} [CommRing R] [IsDomain R]
    {p : ℕ} [hp : Fact p.Prime] (k : ℕ) {ξ : R}
    (hξ : IsPrimitiveRoot ξ (p ^ (k+1))) :
    (ξ^(p^k) - 1) * (cyclotomic (p^(k+1)) R).derivative.eval ξ =
      (p^(k+1) : ℕ) * ξ^(p^(k+1) - 1) := by
  have hroot : (cyclotomic (p^(k+1)) R).eval ξ = 0 :=
    hξ.isRoot_cyclotomic (pow_pos hp.out.pos _)
  have h := congrArg (fun f : R[X] => (derivative f).eval ξ)
    (cyclotomic_prime_pow_mul_X_pow_sub_one R p k)
  simpa only [derivative_mul, derivative_sub, derivative_one, sub_zero,
    derivative_X_pow, eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow,
    eval_one, hroot, zero_mul, add_zero, mul_comm (ξ^(p^k) - 1)] using h

theorem integral_slope {R : Type*} [CommRing R] [IsDomain R]
    {p : ℕ} [hp : Fact p.Prime] (k : ℕ) {ξ : R}
    (hξ : IsPrimitiveRoot ξ (p^(k+1))) :
    (ξ^(p^k)-1) * (cyclotomic (p^(k+1)) R).derivative.eval ξ * ξ =
      (p^(k+1) : ℕ) := by
  rw [slope_at_primitive_prime_power k hξ, mul_assoc, ← pow_succ,
    Nat.sub_one_add_one (pow_ne_zero _ hp.out.ne_zero), hξ.pow_eq_one, mul_one]

/-- Extraneous roots in a local factorization contribute a unit to the
derivative, provided their factor evaluates to a unit at the chosen root. -/
theorem derivative_mul_at_root {R : Type*} [CommRing R] {F G : R[X]} {r : R}
    (hF : F.eval r = 0) (hG : IsUnit (G.eval r)) :
    Associated ((F*G).derivative.eval r) (F.derivative.eval r) := by
  simp only [derivative_mul, eval_add, eval_mul, hF, zero_mul, add_zero]
  exact associated_mul_unit_left _ _ hG

end VacuumFrame.Cyclotomic

#print axioms VacuumFrame.Cyclotomic.slope_at_primitive_prime_power
#print axioms VacuumFrame.Cyclotomic.integral_slope
#print axioms VacuumFrame.Cyclotomic.derivative_mul_at_root
