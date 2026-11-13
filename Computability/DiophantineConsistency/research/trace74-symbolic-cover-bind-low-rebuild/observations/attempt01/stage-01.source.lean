import Trace74CoverBindBeta
import Trace74LowPortIdentity
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74CoverBindLow
open CompactListMask CompactConcreteMask CompactFixedBeta CompactSymbolicPorts

-- Keep large fixed symbols opaque to avoid deliberate numeral expansion.
attribute [local irreducible] Nat.pow CompactFixedBeta.betaNat CompactSymbolicPorts.lowNat

def defectNat : ℕ := Nat.ofDigits (2^67) ((List.range 3297).map (defect 1063 support))

/-- Fix beta and low; retain the high value and both remaining bounds as inputs. -/
theorem cover (high : ℕ)
    (hdefect : defectNat < (2^67)^3297)
    (hhigh : (2^67)^4393 ≤ high) : betaNat+1 ≤ lowNat+high := by
  exact Trace74CoverBindBeta.cover lowNat defectNat high
    Trace74LowPortIdentity.low_add_defect hdefect hhigh

#print axioms Trace74CoverBindLow.cover
end Trace74CoverBindLow
