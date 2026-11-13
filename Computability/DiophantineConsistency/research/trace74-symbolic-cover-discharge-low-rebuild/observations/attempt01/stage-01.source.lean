import Trace74CoverBindDefect
import Trace74LowPortIdentity
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74CoverDischargeLow
open CompactListMask CompactConcreteMask CompactFixedBeta CompactSymbolicPorts

attribute [local irreducible] Nat.pow Nat.ofDigits CompactFixedBeta.betaNat
  CompactSymbolicPorts.lowNat CompactConcreteMask.support

/-- Discharge the actual low identity; retain both numeric bounds as inputs. -/
theorem cover (high : ℕ)
    (hdefect : Nat.ofDigits (2^67) ((List.range 3297).map (defect 1063 support)) <
      (2^67)^3297)
    (hhigh : (2^67)^4393 ≤ high) : betaNat+1 ≤ lowNat+high := by
  exact Trace74CoverBindDefect.cover high Trace74LowPortIdentity.low_add_defect hdefect hhigh

#print axioms Trace74CoverDischargeLow.cover
end Trace74CoverDischargeLow
