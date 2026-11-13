import Trace74CoverBindLowParametric
import DiophantineConsistency.CompactConcreteMask
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74CoverBindDefect
open CompactListMask CompactConcreteMask CompactFixedBeta CompactSymbolicPorts

-- Preserve the named expressions during elaboration; no threshold change.
attribute [local irreducible] Nat.pow Nat.ofDigits CompactFixedBeta.betaNat
  CompactSymbolicPorts.lowNat CompactConcreteMask.support

/-- Fix the actual defect, retaining its three required facts as hypotheses. -/
theorem cover (high : ℕ)
    (hlow : lowNat + Nat.ofDigits (2^67) ((List.range 3297).map (defect 1063 support)) + 1 =
      (2^67)^8807)
    (hdefect : Nat.ofDigits (2^67) ((List.range 3297).map (defect 1063 support)) <
      (2^67)^3297)
    (hhigh : (2^67)^4393 ≤ high) : betaNat+1 ≤ lowNat+high := by
  exact Trace74CoverBindLowParametric.cover
    (Nat.ofDigits (2^67) ((List.range 3297).map (defect 1063 support))) high
    hlow hdefect hhigh

#print axioms Trace74CoverBindDefect.cover
end Trace74CoverBindDefect
