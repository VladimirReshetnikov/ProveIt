import Trace74GenericPowerCover
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74FixedGeometryCover

/-- Fix the radix and exponents while retaining all four values as variables. -/
theorem cover (beta low defect high : ℕ)
    (hbeta : beta+1 = (2^67)^8807)
    (hlow : low+defect+1 = (2^67)^8807)
    (hdefect : defect < (2^67)^3297)
    (hhigh : (2^67)^4393 ≤ high) : beta+1 ≤ low+high := by
  exact Trace74GenericPowerCover.cover (2^67) 3297 4393 8807 beta low defect high
    (by norm_num) (by decide) hbeta hlow hdefect hhigh

#print axioms Trace74FixedGeometryCover.cover
end Trace74FixedGeometryCover
