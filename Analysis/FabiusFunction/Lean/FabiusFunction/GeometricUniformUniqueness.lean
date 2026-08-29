import FabiusFunction.AffineIndependentCopy
import FabiusFunction.GeometricUniformLaw

/-!
# Uniqueness of the geometric uniform law

The geometric uniform distribution is already known to satisfy the affine
head--tail equation

`X =_d (1 - q) U + q X'`.

This module combines that construction with the generic contractive affine
fixed-point theorem.  Thus the head--tail equation characterizes the law
among all probability measures for every real `q` with `|q| < 1`, including
negative `q` and the endpoint `q = 0`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set

namespace Fabius
namespace ProbabilityRepresentation

noncomputable section

/-- The geometric uniform distribution is the unique probability law
satisfying its affine independent-copy equation.  No support, density, or
moment assumption on the competing law is required. -/
theorem eq_geometricUniformDistribution_of_selfSimilar
    {q : ℝ} (hq : |q| < 1) {mu : Measure ℝ}
    [IsProbabilityMeasure mu]
    (hmu : mu =
      ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod mu).map
        (fun p => (1 - q) * (p.1 : ℝ) + q * p.2)) :
    mu = geometricUniformDistribution q := by
  letI : IsProbabilityMeasure (geometricUniformDistribution q) :=
    geometricUniformDistribution_isProbabilityMeasure hq
  exact affineIndependentCopy_map_fixedPoint_unique
    (rho := (volume : Measure (Set.Icc (0 : ℝ) 1)))
    (digit := fun u => (1 - q) * (u : ℝ))
    (q := q) (mu := mu) (nu := geometricUniformDistribution q)
    (by fun_prop) hq hmu (geometricUniformDistribution_selfSimilar hq)

end

end ProbabilityRepresentation
end Fabius
