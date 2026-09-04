import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring

/-!
# Newton iteration for reciprocal power series

The update `c ↦ c * (2 - a * c)` squares the multiplicative residual `1 - a * c`.
Consequently, an inverse modulo `X^m` becomes an inverse modulo `X^(2*m)`.
The result is valid over every commutative coefficient ring, including positive
characteristic, and remains valid after actually truncating the updated series.

Invertibility of the constant coefficient is needed to initialize the algorithm;
once an approximation is given, the improvement uses only ring operations.
-/

set_option autoImplicit false

namespace Fabius

section Algebra

variable {R : Type*} [CommRing R]

/-- A Newton step for the multiplicative inverse of `a`. -/
def newtonReciprocalStep (a c : R) : R := c * (2 - a * c)

/-- A reciprocal Newton step squares the multiplicative residual exactly. -/
theorem one_sub_mul_newtonReciprocalStep (a c : R) :
    1 - a * newtonReciprocalStep a c = (1 - a * c) ^ 2 := by
  unfold newtonReciprocalStep
  ring

end Algebra

section PowerSeries

open PowerSeries

variable {R : Type*} [CommRing R]
variable {A C : R⟦X⟧} {m : ℕ}

/-- A scalar inverse of the constant coefficient initializes the reciprocal iteration
with precision one. -/
theorem X_dvd_one_sub_mul_C (c : R) (hc : constantCoeff A * c = 1) :
    (X : R⟦X⟧) ∣ 1 - A * PowerSeries.C c := by
  rw [PowerSeries.X_dvd_iff, map_sub, map_one, map_mul, constantCoeff_C, hc, sub_self]

/-- If `C` is a reciprocal of `A` through degree `m - 1`, one Newton step is a
reciprocal through degree `2*m - 1`. No separate unit hypothesis is required. -/
theorem X_pow_dvd_one_sub_mul_newtonReciprocalStep
    (h : (X : R⟦X⟧) ^ m ∣ 1 - A * C) :
    (X : R⟦X⟧) ^ (2 * m) ∣ 1 - A * newtonReciprocalStep A C := by
  obtain ⟨E, hE⟩ := h
  refine ⟨E ^ 2, ?_⟩
  rw [one_sub_mul_newtonReciprocalStep, hE, mul_pow, ← pow_mul, Nat.mul_comm m 2]

/-- The improved product has exactly the coefficients of `1` below degree `2*m`. -/
theorem coeff_mul_newtonReciprocalStep (h : (X : R⟦X⟧) ^ m ∣ 1 - A * C)
    (n : ℕ) (hn : n < 2 * m) :
    coeff n (A * newtonReciprocalStep A C) = coeff n (1 : R⟦X⟧) := by
  have hz := PowerSeries.X_pow_dvd_iff.mp
    (X_pow_dvd_one_sub_mul_newtonReciprocalStep h) n hn
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

/-- The implemented update may be reduced to its first `2*m` coefficients:
truncating the Newton step preserves its doubled reciprocal precision. -/
theorem X_pow_dvd_one_sub_mul_trunc_newtonReciprocalStep
    (h : (X : R⟦X⟧) ^ m ∣ 1 - A * C) :
    (X : R⟦X⟧) ^ (2 * m) ∣
      1 - A * (trunc (2 * m) (newtonReciprocalStep A C) : R⟦X⟧) := by
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro n hn
  have hcoeff := congrArg (fun p : Polynomial R => p.coeff n)
    (trunc_mul_trunc (n := 2 * m) A (newtonReciprocalStep A C))
  simp only [coeff_trunc, if_pos hn] at hcoeff
  rw [map_sub, hcoeff, coeff_mul_newtonReciprocalStep h n hn, sub_self]

end PowerSeries

end Fabius
