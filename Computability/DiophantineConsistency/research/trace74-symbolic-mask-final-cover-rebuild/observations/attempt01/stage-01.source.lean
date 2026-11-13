import Trace74AbstractCover
import Trace74HighDigitBound
import Trace74BetaPower
import Trace74ConcreteDefectBound
import Trace74LowPortIdentity
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74FinalSymbolicCover
open CompactListMask CompactConcreteMask CompactFixedBeta CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic

def defectNat : ℕ := Nat.ofDigits (2^67) ((List.range 3297).map (defect 1063 support))

/-- The specific retained symbolic ports cover beta plus one. -/
theorem cover_nat : betaNat + 1 ≤ lowNat + highNat := by
  have hpow : (2^67:ℕ)^3297 ≤ (2^67:ℕ)^4393 :=
    Nat.pow_le_pow_right (by norm_num) (by decide)
  have hdef : defectNat < highNat :=
    lt_of_lt_of_le Trace74ConcreteDefectBound.defect_lt
      (le_trans hpow Trace74HighDigitBound.high_at_least)
  exact Trace74AbstractCover.of_identity betaNat lowNat defectNat highNat ((2^67)^8807)
    Trace74BetaPower.beta_plus_one Trace74LowPortIdentity.low_add_defect hdef

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The same fixed symbolic cover after casting into any indicated model. -/
theorem cover_model : (betaNat:V) + 1 ≤ (lowNat:V) + (highNat:V) := by
  have h := (Nat.cast_le.mpr cover_nat : ((betaNat+1:ℕ):V) ≤ ((lowNat+highNat:ℕ):V))
  simpa only [Nat.cast_add,Nat.cast_one] using h
end Model

#print axioms Trace74FinalSymbolicCover.cover_nat
#print axioms Trace74FinalSymbolicCover.cover_model
end Trace74FinalSymbolicCover
