import FabiusFunction.ScaledInfiniteProducts
import FabiusFunction.IntegerZeroAnalyticOrder
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Geometric reciprocal-Gamma products

The reciprocal Gamma function is entire and normalized to one at `1`.
Consequently, for every `q : ℂ` with `‖q‖ < 1`, the product

`G_q(z) = ∏' n, Gamma(1 + q^n z)⁻¹`

is an entire function.  This file develops that product from the reusable
compact-uniform convergence engine in `ScaledInfiniteProducts`.  It proves
its Mahler equation, its complete zero locus, and its reflection into the
corresponding geometric sinc product.  At `q = 1 / 2`, the latter is exactly
the standalone Rvachev Fourier product already used throughout the project.

The Gamma-side object is defined as the pointwise inverse of the entire
reciprocal product.  This is deliberate: Mathlib assigns the value `0` to
`Complex.Gamma` at its poles, and also has `0⁻¹ = 0`.  Thus a meromorphic
representatives chosen in this file have value zero at their poles; the poles
themselves are recorded by negative `meromorphicOrderAt`, not by point values.
-/

set_option autoImplicit false

open Asymptotics Filter Set
open scoped BigOperators Topology

namespace Fabius

noncomputable section

/-! ## The shifted reciprocal-Gamma factor -/

/-- The entire shifted reciprocal Gamma factor `z ↦ 1 / Gamma(1 + z)`. -/
noncomputable def shiftedReciprocalGamma (z : ℂ) : ℂ :=
  (Complex.Gamma (1 + z))⁻¹

/-- The shifted reciprocal Gamma factor is normalized at the origin. -/
@[simp]
theorem shiftedReciprocalGamma_zero : shiftedReciprocalGamma 0 = 1 := by
  simp [shiftedReciprocalGamma]

/-- The shifted reciprocal Gamma factor is entire. -/
theorem shiftedReciprocalGamma_differentiable :
    Differentiable ℂ shiftedReciprocalGamma := by
  change Differentiable ℂ (fun z : ℂ ↦ (Complex.Gamma (1 + z))⁻¹)
  have hadd : Differentiable ℂ (fun z : ℂ ↦ 1 + z) := by fun_prop
  exact Complex.differentiable_one_div_Gamma.comp hadd

/-- Near zero the shifted reciprocal Gamma factor differs from one by at
most a linear term. -/
theorem shiftedReciprocalGamma_sub_one_isBigO :
    (fun z : ℂ ↦ shiftedReciprocalGamma z - 1) =O[𝓝 0]
      (fun z : ℂ ↦ z) := by
  have h := (shiftedReciprocalGamma_differentiable 0).isBigO_sub
  simpa only [shiftedReciprocalGamma_zero, sub_zero] using h

/-- The zeros of `1 / Gamma(1 + z)` are exactly the shifted nonpositive
integers.  These are the poles of the classical Gamma function, represented
as zeros by Mathlib's totalization. -/
theorem shiftedReciprocalGamma_eq_zero_iff (z : ℂ) :
    shiftedReciprocalGamma z = 0 ↔
      ∃ m : ℕ, 1 + z = -(m : ℂ) := by
  simp [shiftedReciprocalGamma, Complex.Gamma_eq_zero_iff]

/-- Shifted Euler reflection in entire, totalized form:
`Gamma(1+z)⁻¹ Gamma(1-z)⁻¹ = sinc(πz)`. -/
theorem shiftedReciprocalGamma_mul_neg (z : ℂ) :
    shiftedReciprocalGamma z * shiftedReciprocalGamma (-z) =
      complexSinc (Real.pi * z) := by
  by_cases hz : z = 0
  · subst z
    simp [complexSinc]
  · have hpi : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    have hpiz : (Real.pi : ℂ) * z ≠ 0 := mul_ne_zero hpi hz
    have hreflection :
        (Complex.Gamma z)⁻¹ * (Complex.Gamma (1 - z))⁻¹ =
          Complex.sin (Real.pi * z) / Real.pi := by
      calc
        (Complex.Gamma z)⁻¹ * (Complex.Gamma (1 - z))⁻¹ =
            (Complex.Gamma z * Complex.Gamma (1 - z))⁻¹ := by
              rw [mul_inv_rev]
              ring
        _ = ((Real.pi : ℂ) / Complex.sin (Real.pi * z))⁻¹ := by
              rw [Complex.Gamma_mul_Gamma_one_sub]
        _ = Complex.sin (Real.pi * z) / Real.pi := by
              rw [inv_div]
    have hcross :
        z * (shiftedReciprocalGamma z * shiftedReciprocalGamma (-z)) =
          Complex.sin (Real.pi * z) / Real.pi := by
      calc
        z * (shiftedReciprocalGamma z * shiftedReciprocalGamma (-z)) =
            (z * (Complex.Gamma (z + 1))⁻¹) *
              (Complex.Gamma (1 - z))⁻¹ := by
              simp only [shiftedReciprocalGamma]
              rw [show (1 : ℂ) + z = z + 1 by ring,
                show (1 : ℂ) + -z = 1 - z by ring]
              ring
        _ = (Complex.Gamma z)⁻¹ * (Complex.Gamma (1 - z))⁻¹ := by
              rw [← Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one]
        _ = Complex.sin (Real.pi * z) / Real.pi := hreflection
    apply mul_left_cancel₀ hz
    rw [complexSinc, if_neg hpiz]
    calc
      z * (shiftedReciprocalGamma z * shiftedReciprocalGamma (-z)) =
          Complex.sin (Real.pi * z) / Real.pi := hcross
      _ = z * (Complex.sin (Real.pi * z) / ((Real.pi : ℂ) * z)) := by
          field_simp

/-! ## The geometric product -/

/-- Norms of powers of a strict contraction form a summable geometric
series.  The statement includes `q = 0`. -/
theorem summable_norm_qpow (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ ↦ ‖q ^ n‖ := by
  simpa only [norm_pow] using
    summable_geometric_of_lt_one (norm_nonneg q) hq

/-- The reciprocal-Gamma product at the geometric scales `q^n z`. -/
noncomputable def geometricReciprocalGamma (q z : ℂ) : ℂ :=
  ∏' n : ℕ, shiftedReciprocalGamma (q ^ n * z)

/-- The factors defining the geometric reciprocal-Gamma product are
genuinely multipliable whenever `q` is a strict contraction. -/
theorem geometricReciprocalGammaFactors_multipliable
    (q z : ℂ) (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ ↦ shiftedReciprocalGamma (q ^ n * z) := by
  have hprod := hasProdLocallyUniformly_scaled
    shiftedReciprocalGamma (fun n : ℕ ↦ q ^ n)
    (summable_norm_qpow q hq)
    shiftedReciprocalGamma_sub_one_isBigO
    shiftedReciprocalGamma_differentiable.continuous
  simpa only [smul_eq_mul] using
    (hprod.hasProd (x := z)).multipliable

/-- The geometric reciprocal-Gamma product is entire for every strict
contraction `q`. -/
theorem geometricReciprocalGamma_differentiable
    (q : ℂ) (hq : ‖q‖ < 1) :
    Differentiable ℂ (geometricReciprocalGamma q) := by
  change Differentiable ℂ
    (fun z ↦ ∏' n : ℕ, shiftedReciprocalGamma (q ^ n * z))
  simpa only [smul_eq_mul] using
    differentiable_tprod_scaled_of_eq_one
      shiftedReciprocalGamma (fun n : ℕ ↦ q ^ n)
      (summable_norm_qpow q hq)
      shiftedReciprocalGamma_differentiable
      shiftedReciprocalGamma_zero

/-- Every geometric reciprocal-Gamma product is normalized to one at the
origin, without any condition on `q`. -/
@[simp]
theorem geometricReciprocalGamma_zero (q : ℂ) :
    geometricReciprocalGamma q 0 = 1 := by
  simp [geometricReciprocalGamma]

set_option maxHeartbeats 600000 in
/-- The exact Mahler equation.  It remains valid at the degenerate
contraction `q = 0`. -/
theorem geometricReciprocalGamma_mahler
    (q z : ℂ) (hq : ‖q‖ < 1) :
    geometricReciprocalGamma q z =
      shiftedReciprocalGamma z * geometricReciprocalGamma q (q * z) := by
  rw [geometricReciprocalGamma]
  have htail : Multipliable fun n : ℕ ↦
      shiftedReciprocalGamma (q ^ (n + 1) * z) := by
    have h := geometricReciprocalGammaFactors_multipliable q (q * z) hq
    convert h using 1
    funext n
    rw [pow_succ]
    ring_nf
  rw [tprod_eq_zero_mul' htail]
  simp only [pow_zero, one_mul]
  congr 1
  apply tprod_congr
  intro n
  rw [pow_succ]
  congr 1
  ring

/-- A geometric reciprocal-Gamma product vanishes exactly when one of its
explicit factors vanishes.  This affine form is safe at `q = 0`; no division
by a scale occurs. -/
theorem geometricReciprocalGamma_eq_zero_iff
    (q z : ℂ) (hq : ‖q‖ < 1) :
    geometricReciprocalGamma q z = 0 ↔
      ∃ n m : ℕ, 1 + q ^ n * z = -(m : ℂ) := by
  rw [geometricReciprocalGamma]
  have hzero := tprod_scaled_eq_zero_iff
    shiftedReciprocalGamma (fun n : ℕ ↦ q ^ n)
    (summable_norm_qpow q hq)
    shiftedReciprocalGamma_sub_one_isBigO z
  simpa only [smul_eq_mul, shiftedReciprocalGamma_eq_zero_iff] using hzero

/-- The Gamma-side geometric function, defined as the meromorphic inverse of
the entire reciprocal product. -/
noncomputable def geometricGamma (q z : ℂ) : ℂ :=
  (geometricReciprocalGamma q z)⁻¹

/-- The Gamma-side geometric function is meromorphic. -/
theorem geometricGamma_meromorphic (q : ℂ) (hq : ‖q‖ < 1) :
    Meromorphic (geometricGamma q) := by
  intro z
  exact ((geometricReciprocalGamma_differentiable q hq).analyticAt z).meromorphicAt.inv

/-- The Gamma-side Mahler equation, valid as an identity of Mathlib's
totalized meromorphic representatives, including at poles. -/
theorem geometricGamma_mahler (q z : ℂ) (hq : ‖q‖ < 1) :
    geometricGamma q z =
      Complex.Gamma (1 + z) * geometricGamma q (q * z) := by
  rw [geometricGamma, geometricGamma,
    geometricReciprocalGamma_mahler q z hq, mul_inv_rev]
  simp [shiftedReciprocalGamma, mul_comm]

/-- The geometric sinc product with the same scales as
`geometricReciprocalGamma`. -/
noncomputable def geometricSincProduct (q z : ℂ) : ℂ :=
  ∏' n : ℕ, complexSinc (Real.pi * (q ^ n * z))

/-- Reflection of the reciprocal-Gamma product is the geometric sinc
product. -/
theorem geometricReciprocalGamma_mul_neg
    (q z : ℂ) (hq : ‖q‖ < 1) :
    geometricReciprocalGamma q z * geometricReciprocalGamma q (-z) =
      geometricSincProduct q z := by
  have hz := geometricReciprocalGammaFactors_multipliable q z hq
  have hn := geometricReciprocalGammaFactors_multipliable q (-z) hq
  rw [geometricReciprocalGamma, geometricReciprocalGamma,
    geometricSincProduct, ← hz.tprod_mul hn]
  apply tprod_congr
  intro n
  rw [show q ^ n * -z = -(q ^ n * z) by ring,
    shiftedReciprocalGamma_mul_neg]

/-! ## Dyadic specialization and the Rvachev bridge -/

/-- The reciprocal dyadic Gamma function. -/
noncomputable def dyadicReciprocalGamma (z : ℂ) : ℂ :=
  geometricReciprocalGamma ((2 : ℂ)⁻¹) z

/-- The meromorphic dyadic Gamma function. -/
noncomputable def dyadicGamma (z : ℂ) : ℂ :=
  (dyadicReciprocalGamma z)⁻¹

/-- The reciprocal dyadic Gamma function is entire. -/
theorem dyadicReciprocalGamma_differentiable :
    Differentiable ℂ dyadicReciprocalGamma := by
  exact geometricReciprocalGamma_differentiable (2 : ℂ)⁻¹ (by norm_num)

/-- The reciprocal dyadic Gamma function is normalized to one. -/
@[simp]
theorem dyadicReciprocalGamma_zero : dyadicReciprocalGamma 0 = 1 := by
  simp [dyadicReciprocalGamma]

/-- The geometric sinc product at ratio `1/2` is the existing Rvachev
Fourier product. -/
theorem geometricSincProduct_inv_two (z : ℂ) :
    geometricSincProduct ((2 : ℂ)⁻¹) z = rvachevFourierProduct z := by
  rw [geometricSincProduct, rvachevFourierProduct]
  apply tprod_congr
  intro n
  congr 1
  rw [inv_pow]
  ring

/-- **Dyadic Gamma reflection factorization**: the Rvachev sinc product is
the product of the negative- and positive-integer reciprocal-Gamma factors. -/
theorem dyadicReciprocalGamma_mul_neg (z : ℂ) :
    dyadicReciprocalGamma z * dyadicReciprocalGamma (-z) =
      rvachevFourierProduct z := by
  rw [dyadicReciprocalGamma, dyadicReciprocalGamma,
    geometricReciprocalGamma_mul_neg _ _ (by norm_num),
    geometricSincProduct_inv_two]

/-- The Rvachev product in the frontier document's Gamma-denominator form.
The identity is total at the integer zeros. -/
theorem rvachevFourierProduct_eq_one_div_dyadicGamma_mul (z : ℂ) :
    rvachevFourierProduct z =
      1 / (dyadicGamma z * dyadicGamma (-z)) := by
  rw [← dyadicReciprocalGamma_mul_neg z]
  simp [dyadicGamma, div_eq_mul_inv, mul_comm]

end

end Fabius
