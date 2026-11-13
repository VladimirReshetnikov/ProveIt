import Trace74FixedGeometryCover
import Trace74BetaPower
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74CoverBindBeta
open CompactFixedBeta

/-- Fix only beta, retaining low, defect and high as variables with explicit bounds. -/
theorem cover (low defect high : ℕ)
    (hlow : low+defect+1 = (2^67)^8807)
    (hdefect : defect < (2^67)^3297)
    (hhigh : (2^67)^4393 ≤ high) : betaNat+1 ≤ low+high := by
  exact Trace74FixedGeometryCover.cover betaNat low defect high
    Trace74BetaPower.beta_plus_one hlow hdefect hhigh

#print axioms Trace74CoverBindBeta.cover
end Trace74CoverBindBeta
