import Surreal.Algebra.PolynomialResiduePairing
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Residue as a formal Laurent coefficient at infinity

The coefficient identity `polynomial:eq:lambdaatinfinity` in
`docs/surcomplex/polynomial-algebra/article.tex`, over an arbitrary
commutative ring. The Laurent variable is `T = z⁻¹`, so the coefficient of
`z⁻¹` is the coefficient of `T¹`.

Monicity makes the reversed polynomial's constant coefficient one. Its
formal power-series inverse is therefore constructed with `invOfUnit`,
without a field or any division by a nonunit. Multiplication verifies the
actual Laurent quotient before its coefficient is identified with the
residue functional. Degree-zero monic polynomials and the zero ring are
included.
-/

namespace Surreal.FinitePolynomial

open Polynomial
open scoped PowerSeries LaurentSeries

noncomputable section

variable {R : Type*} [CommRing R]

/-- Evaluate a polynomial in the Laurent monomial `T⁻¹`, where `T = z⁻¹`. -/
def polynomialAtInfinity : R[X] →+* R⸨X⸩ :=
  Polynomial.eval₂RingHom HahnSeries.C (HahnSeries.single (-1) 1)

/-- A polynomial monomial becomes the corresponding nonpositive Laurent monomial. -/
theorem polynomialAtInfinity_monomial (j : ℕ) (c : R) :
    polynomialAtInfinity (monomial j c) = HahnSeries.single (-(j : ℤ)) c := by
  change (monomial j c).eval₂ HahnSeries.C (HahnSeries.single (-1) 1) = _
  simp [eval₂_monomial, HahnSeries.C_apply, HahnSeries.single_pow,
    HahnSeries.single_mul_single]

/-- Embedding a polynomial into Laurent series agrees with evaluation at `T`. -/
theorem polynomialAtZero_eq_eval₂ (P : R[X]) :
    ((P : PowerSeries R) : R⸨X⸩) = P.eval₂ HahnSeries.C (HahnSeries.single 1 1) := by
  rw [← Polynomial.eval₂_C_X_eq_coe]
  change (HahnSeries.ofPowerSeries ℤ R) (P.eval₂ PowerSeries.C PowerSeries.X) = _
  have hc : (HahnSeries.ofPowerSeries ℤ R).comp PowerSeries.C = HahnSeries.C := by
    exact RingHom.ext (fun r => HahnSeries.ofPowerSeries_C (Γ := ℤ) r)
  rw [Polynomial.hom_eval₂, hc, HahnSeries.ofPowerSeries_X]

/-- Reversal is exactly the finite change of variable at infinity. -/
theorem polynomialAtInfinity_eq_reverse (P : R[X]) :
    polynomialAtInfinity P = ((P.reverse : PowerSeries R) : R⸨X⸩) *
      HahnSeries.single (-(P.natDegree : ℤ)) 1 := by
  letI : Invertible (HahnSeries.single (-1) (1 : R) : R⸨X⸩) :=
    ⟨HahnSeries.single 1 1, by simp [HahnSeries.single_mul_single],
      by simp [HahnSeries.single_mul_single]⟩
  have h := Polynomial.eval₂_reverse_mul_pow HahnSeries.C
    (HahnSeries.single (-1) (1 : R) : R⸨X⸩) P
  have hi : ⅟(HahnSeries.single (-1) (1 : R) : R⸨X⸩) = HahnSeries.single 1 1 := rfl
  rw [hi] at h
  rw [polynomialAtZero_eq_eval₂]
  simpa [polynomialAtInfinity, HahnSeries.single_pow] using h.symm

/-- The inverse of the reversed polynomial, using its unit constant
coefficient when the original polynomial is monic. -/
def reciprocalReverse (P : R[X]) : PowerSeries R :=
  PowerSeries.invOfUnit (P.reverse : PowerSeries R) 1

@[simp] theorem constantCoeff_reciprocalReverse (P : R[X]) :
    PowerSeries.constantCoeff (reciprocalReverse P) = 1 := by
  simp [reciprocalReverse]

/-- Monicity verifies the unit hypothesis for the formal reciprocal. -/
theorem reverse_mul_reciprocalReverse (P : R[X]) (hP : P.Monic) :
    (P.reverse : PowerSeries R) * reciprocalReverse P = 1 := by
  apply PowerSeries.mul_invOfUnit
  simpa using hP.leadingCoeff

/-- The formal Laurent reciprocal `Tⁿ / reverse(P)(T)`. -/
def reciprocalAtInfinity (P : R[X]) : R⸨X⸩ :=
  HahnSeries.single (P.natDegree : ℤ) 1 * ((reciprocalReverse P : PowerSeries R) : R⸨X⸩)

/-- This is an actual inverse in the Laurent-series ring, including over
rings with zero divisors. -/
theorem polynomialAtInfinity_mul_reciprocal (P : R[X]) (hP : P.Monic) :
    polynomialAtInfinity P * reciprocalAtInfinity P = 1 := by
  rw [polynomialAtInfinity_eq_reverse, reciprocalAtInfinity]
  calc
    _ = (((P.reverse : PowerSeries R) : R⸨X⸩) *
        ((reciprocalReverse P : PowerSeries R) : R⸨X⸩)) *
        (HahnSeries.single (-(P.natDegree : ℤ)) 1 *
          HahnSeries.single (P.natDegree : ℤ) 1) := by ring
    _ = 1 := by
      rw [← PowerSeries.coe_mul, reverse_mul_reciprocalReverse P hP,
        PowerSeries.coe_one]
      simp [HahnSeries.single_mul_single]

/-- The genuine formal quotient `Q(z)/P(z)` expanded at infinity. -/
def quotientAtInfinity (P Q : R[X]) : R⸨X⸩ :=
  polynomialAtInfinity Q * reciprocalAtInfinity P

/-- Multiplying the formal quotient by its monic denominator recovers
the numerator. -/
theorem polynomialAtInfinity_mul_quotient (P Q : R[X]) (hP : P.Monic) :
    polynomialAtInfinity P * quotientAtInfinity P Q = polynomialAtInfinity Q := by
  rw [quotientAtInfinity, mul_left_comm, polynomialAtInfinity_mul_reciprocal P hP, mul_one]

/-- Polynomial parts at infinity have no positive Laurent exponents. -/
theorem coeff_polynomialAtInfinity_eq_zero (Q : R[X]) {g : ℤ} (hg : 0 < g) :
    (polynomialAtInfinity Q).coeff g = 0 := by
  induction Q using Polynomial.induction_on' with
  | add Q S hQ hS => simp only [map_add, HahnSeries.coeff_add, hQ, hS, add_zero]
  | monomial j c =>
    rw [polynomialAtInfinity_monomial, HahnSeries.coeff_single]
    split_ifs with h
    · omega
    · rfl

/-- A monomial below the modulus degree contributes only at the top
remainder coefficient, because the reciprocal series has constant one. -/
theorem coeff_quotientAtInfinity_monomial (P : R[X]) {j : ℕ} (hj : j < P.natDegree)
    (c : R) :
    (quotientAtInfinity P (monomial j c)).coeff 1 =
      (monomial j c).coeff (P.natDegree - 1) := by
  rw [quotientAtInfinity, polynomialAtInfinity_monomial, reciprocalAtInfinity,
    ← mul_assoc, HahnSeries.single_mul_single, HahnSeries.coeff_single_mul]
  simp only [mul_one, PowerSeries.coeff_coe]
  by_cases he : j = P.natDegree - 1
  · have hexp : (1 : ℤ) - (-(j : ℤ) + P.natDegree) = 0 := by omega
    rw [hexp]
    simp [he, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · have hneg : (1 : ℤ) - (-(j : ℤ) + P.natDegree) < 0 := by omega
    simp [hneg, he, Polynomial.coeff_monomial]

/-- A polynomial remainder contributes precisely its top coefficient to
the `T¹` term of the formal quotient. -/
theorem coeff_quotientAtInfinity_of_degree_lt (P Q : R[X])
    (hQ : Q.degree < P.natDegree) :
    (quotientAtInfinity P Q).coeff 1 = Q.coeff (P.natDegree - 1) := by
  have hsum : quotientAtInfinity P Q =
      ∑ j ∈ Q.support, quotientAtInfinity P (monomial j (Q.coeff j)) := by
    unfold quotientAtInfinity
    rw [← Finset.sum_mul, ← map_sum]
    exact congrArg (fun S => polynomialAtInfinity S * reciprocalAtInfinity P) Q.sum_monomial_eq.symm
  rw [hsum, HahnSeries.coeff_sum]
  calc
    _ = ∑ j ∈ Q.support, (monomial j (Q.coeff j)).coeff (P.natDegree - 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply coeff_quotientAtInfinity_monomial
      have hle := le_degree_of_ne_zero (mem_support_iff.mp hj)
      exact_mod_cast hle.trans_lt hQ
    _ = Q.coeff (P.natDegree - 1) := by
      rw [← finsetSum_coeff]
      exact congrArg (fun S : R[X] => S.coeff (P.natDegree - 1)) Q.sum_monomial_eq

/-- Monic division separates the formal quotient into its polynomial part
and the proper quotient of the remainder. -/
theorem quotientAtInfinity_eq_remainder_add_polynomial (P Q : R[X]) (hP : P.Monic) :
    quotientAtInfinity P Q = quotientAtInfinity P (Q %ₘ P) +
      polynomialAtInfinity (Q /ₘ P) := by
  have h := congrArg (fun S => quotientAtInfinity P S) (modByMonic_add_div Q P).symm
  calc
    _ = quotientAtInfinity P (Q %ₘ P + P * (Q /ₘ P)) := h
    _ = quotientAtInfinity P (Q %ₘ P) +
        polynomialAtInfinity (Q /ₘ P) *
          (polynomialAtInfinity P * reciprocalAtInfinity P) := by
      simp only [quotientAtInfinity, map_add, map_mul]
      ring
    _ = _ := by rw [polynomialAtInfinity_mul_reciprocal P hP, mul_one]

/-- The coefficient at `z⁻¹`, or equivalently `T¹`, is the top monic
remainder coefficient in `polynomial:eq:lambdaatinfinity`. -/
theorem coeff_quotientAtInfinity_eq_remainder (P Q : R[X]) (hP : P.Monic) :
    (quotientAtInfinity P Q).coeff 1 = (Q %ₘ P).coeff (P.natDegree - 1) := by
  nontriviality R
  rw [quotientAtInfinity_eq_remainder_add_polynomial P Q hP, HahnSeries.coeff_add,
    coeff_polynomialAtInfinity_eq_zero _ (by decide : (0 : ℤ) < 1), add_zero]
  apply coeff_quotientAtInfinity_of_degree_lt
  rw [← degree_eq_natDegree hP.ne_zero]
  exact degree_modByMonic_lt Q hP

/-- The source's residue-at-infinity identity on actual quotient classes.
The Laurent expression is an inverse verified over `R`, with no field
hypothesis or division by root separations. -/
theorem residueFunctional_eq_coeff_quotientAtInfinity (P : R[X]) (hP : P.Monic)
    (Q : R[X]) :
    residueFunctional P hP (AdjoinRoot.mk P Q) = (quotientAtInfinity P Q).coeff 1 := by
  rw [residueFunctional_mk, coeff_quotientAtInfinity_eq_remainder P Q hP]

end

end Surreal.FinitePolynomial
