import Mathlib.Tactic

/-!
# Polynomial core for seven constructive geometry theorems

This file is an ambient Mathlib certificate library.  Its theorems are ring
identities; they are not, by themselves, derivations in the deeply embedded
`ConciseIPRA.PRAAx` theory.  The report explains how the same certificates are
compiled to primitive-recursive polynomial checkers and then replayed in iPRA.

Formalization status: source-level proposed script, not compiled in the delivery
environment (Lean and Lake were unavailable).
-/

namespace MollweideCircleIPRA

section Ring

variable {R : Type*} [CommRing R]

/-- Squared Euclidean norm in two scalar coordinates. -/
def normSq (x y : R) : R := x ^ 2 + y ^ 2

/-- Dot product in two scalar coordinates. -/
def dot (x y u v : R) : R := x * u + y * v

/-- Sine component of the half-difference `(A-B)/2`. -/
def halfDiffSin (sA cA sB cB : R) : R := sA * cB - cA * sB

/-- Cosine component of the half-difference `(A-B)/2`. -/
def halfDiffCos (sA cA sB cB : R) : R := cA * cB + sA * sB

/-- The semiperimeter-excess substitution `a=y+z`, `b=z+x`, `c=x+y`. -/
theorem semiperimeter_excesses (x y z : R) :
    let s := x + y + z
    let a := y + z
    let b := z + x
    let c := x + y
    s - a = x ∧ s - b = y ∧ s - c = z := by
  simp
  constructor
  · ring
  constructor <;> ring

/-- Numerator identity for `sin(A/2)^2 + cos(A/2)^2 = 1`. -/
theorem halfAngleA_unit_numerator (x y z : R) :
    y * z + (x + y + z) * x = (z + x) * (x + y) := by
  ring

/-- Cyclic companion of `halfAngleA_unit_numerator`. -/
theorem halfAngleB_unit_numerator (x y z : R) :
    z * x + (x + y + z) * y = (x + y) * (y + z) := by
  ring

/-- Cyclic companion of `halfAngleA_unit_numerator`. -/
theorem halfAngleC_unit_numerator (x y z : R) :
    x * y + (x + y + z) * z = (y + z) * (z + x) := by
  ring

/-- Product-to-sum identity used by the first Mollweide formula. -/
theorem half_sum_product
    (sA cA sB cB : R)
    (hA : sA ^ 2 + cA ^ 2 = 1)
    (hB : sB ^ 2 + cB ^ 2 = 1) :
    (sA * cB + cA * sB) * (cA * cB + sA * sB) =
      sA * cA + sB * cB := by
  calc
    (sA * cB + cA * sB) * (cA * cB + sA * sB) =
        sA * cA * (cB ^ 2 + sB ^ 2) +
          sB * cB * (sA ^ 2 + cA ^ 2) := by ring
    _ = sA * cA * (sB ^ 2 + cB ^ 2) +
          sB * cB * (sA ^ 2 + cA ^ 2) := by ring
    _ = sA * cA + sB * cB := by rw [hA, hB]; ring

/-- Product-to-difference identity used by the second Mollweide formula. -/
theorem half_difference_product
    (sA cA sB cB : R)
    (hA : sA ^ 2 + cA ^ 2 = 1)
    (hB : sB ^ 2 + cB ^ 2 = 1) :
    (cA * cB - sA * sB) * (sA * cB - cA * sB) =
      sA * cA - sB * cB := by
  calc
    (cA * cB - sA * sB) * (sA * cB - cA * sB) =
        sA * cA * (cB ^ 2 + sB ^ 2) -
          sB * cB * (sA ^ 2 + cA ^ 2) := by ring
    _ = sA * cA * (sB ^ 2 + cB ^ 2) -
          sB * cB * (sA ^ 2 + cA ^ 2) := by ring
    _ = sA * cA - sB * cB := by rw [hA, hB]; ring

/-- Denominator-free first Mollweide identity. -/
theorem mollweide_sum_cross
    (a b c d sA cA sB cB sC cC : R)
    (hA : sA ^ 2 + cA ^ 2 = 1)
    (hB : sB ^ 2 + cB ^ 2 = 1)
    (hCosC : cC = sA * cB + cA * sB)
    (ha : a = 2 * d * sA * cA)
    (hb : b = 2 * d * sB * cB)
    (hc : c = 2 * d * sC * cC) :
    (a + b) * sC = c * halfDiffCos sA cA sB cB := by
  have hp := half_sum_product sA cA sB cB hA hB
  calc
    (a + b) * sC = 2 * d * (sA * cA + sB * cB) * sC := by
      rw [ha, hb]
      ring
    _ = 2 * d * ((sA * cB + cA * sB) *
          (cA * cB + sA * sB)) * sC := by rw [hp]
    _ = 2 * d * (cC * (cA * cB + sA * sB)) * sC := by rw [hCosC]
    _ = c * halfDiffCos sA cA sB cB := by
      rw [hc]
      simp only [halfDiffCos]
      ring

/-- Denominator-free second Mollweide identity. -/
theorem mollweide_difference_cross
    (a b c d sA cA sB cB sC cC : R)
    (hA : sA ^ 2 + cA ^ 2 = 1)
    (hB : sB ^ 2 + cB ^ 2 = 1)
    (hSinC : sC = cA * cB - sA * sB)
    (ha : a = 2 * d * sA * cA)
    (hb : b = 2 * d * sB * cB)
    (hc : c = 2 * d * sC * cC) :
    (a - b) * cC = c * halfDiffSin sA cA sB cB := by
  have hp := half_difference_product sA cA sB cB hA hB
  calc
    (a - b) * cC = 2 * d * (sA * cA - sB * cB) * cC := by
      rw [ha, hb]
      ring
    _ = 2 * d * ((cA * cB - sA * sB) *
          (sA * cB - cA * sB)) * cC := by rw [hp]
    _ = 2 * d * (sC * (sA * cB - cA * sB)) * cC := by rw [hSinC]
    _ = c * halfDiffSin sA cA sB cB := by
      rw [hc]
      simp only [halfDiffSin]
      ring

/-- Denominator-free law of tangents, obtained from the two Mollweide crosses. -/
theorem lawOfTangents_cross
    (a b c sC cC sD cD : R)
    (hSum : (a + b) * sC = c * cD)
    (hDiff : (a - b) * cC = c * sD) :
    (a - b) * cD * cC = (a + b) * sD * sC := by
  calc
    (a - b) * cD * cC - (a + b) * sD * sC =
        cD * ((a - b) * cC) - sD * ((a + b) * sC) := by ring
    _ = cD * (c * sD) - sD * (c * cD) := by rw [hDiff, hSum]
    _ = 0 := by ring
  exact sub_eq_zero.mp this

/-- Explicit polynomial certificate for the inradius identity.

The hypotheses represented by the residuals are
`r*cA=xA*sA`, `r*cB=xB*sB`, `r*cC=xC*sC`,
`semi=xA+xB+xC`, and `cos(A/2+B/2+C/2)=0`.
-/
theorem inradius_certificate
    (r xA xB xC semi sA cA sB cB sC cC : R) :
    (r ^ 2 * semi - xA * xB * xC) * (sA * sB * sC) =
      (r ^ 2 * (cB * cC - sB * sC)) * (r * cA - xA * sA) +
      (r * sA * (xA * cC - r * sC)) * (r * cB - xB * sB) +
      (sA * sB * (xA * xB - r ^ 2)) * (r * cC - xC * sC) -
      r ^ 3 *
        (cA * cB * cC - cA * sB * sC - sA * cB * sC - sA * sB * cC) +
      r ^ 2 * (sA * sB * sC) * (semi - (xA + xB + xC)) := by
  ring

/-- Power of a point along an affine line chart. -/
theorem power_line_expansion
    (px py ox oy vx vy t rho : R) :
    normSq (px + t * vx - ox) (py + t * vy - oy) - rho =
      (normSq (px - ox) (py - oy) - rho) +
        2 * dot (px - ox) (py - oy) vx vy * t +
        normSq vx vy * t ^ 2 := by
  simp only [normSq, dot]
  ring

/-- The cancellation-ready two-root identity for a quadratic line-circle cut. -/
theorem secant_factor_identity (p h q u w : R) :
    w * (p + 2 * h * u + q * u ^ 2) -
      u * (p + 2 * h * w + q * w ^ 2) =
      (w - u) * (p - q * u * w) := by
  ring

/-- Tangent power decomposition before using circle and orthogonality equations. -/
theorem tangent_power_decomposition
    (tx ty ox oy vx vy t rho : R) :
    normSq (tx - t * vx - ox) (ty - t * vy - oy) - rho =
      normSq vx vy * t ^ 2 +
      (normSq (tx - ox) (ty - oy) - rho) -
      2 * t * dot (tx - ox) (ty - oy) vx vy := by
  simp only [normSq, dot]
  ring

/-- Residual equation on a line through a tangent point. -/
theorem tangent_unique_residual
    (tx ty ox oy vx vy t lam rho : R) :
    normSq (tx + (lam - t) * vx - ox) (ty + (lam - t) * vy - oy) - rho =
      (normSq (tx - ox) (ty - oy) - rho) +
      2 * (lam - t) * dot (tx - ox) (ty - oy) vx vy +
      normSq vx vy * (lam - t) ^ 2 := by
  simp only [normSq, dot]
  ring

end Ring

end MollweideCircleIPRA
