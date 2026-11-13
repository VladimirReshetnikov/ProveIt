import DiophantineConsistency.Compact44.CompactSymbolicPorts
import DiophantineConsistency.Compact44.CompactFixedBeta

/-! Uncompiled, staged data transport for the exact symbolic masks. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactSymbolicMaskData
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open CompactSymbolicPorts

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem low_eq : (lowNat:V) = CompactConcreteIncrement.mask := rfl
theorem high_eq : (highNat:V) = ((Nat.ofDigits (2^67) CompactHighPopulation.highDigits : ℕ):V) := rfl

attribute [local irreducible] lowNat highNat CompactFixedBeta.betaNat

theorem data : (lowNat:V) < (CompactFixedBeta.betaNat:V) ∧
    (CompactFixedBeta.betaNat:V) + (highNat:V) < 2*(CompactFixedBeta.betaNat:V) ∧
    1 ≤ (highNat:V) ∧ (CompactFixedBeta.betaNat:V)+1 = Exp.exp (590069:V) := by
  have h := CompactFixedBeta.bounds (V:=V) 1 (by norm_num)
  have hb := CompactFixedBeta.beta_identity (V:=V)
  have he : ((67:V)*8807) = 590069 := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (congrArg (fun L : V => L < (CompactFixedBeta.betaNat:V)) low_eq).mpr h.2.1
  · exact (congrArg (fun H : V => (CompactFixedBeta.betaNat:V)+H <
        2*(CompactFixedBeta.betaNat:V)) high_eq).mpr h.2.2.1
  · have hp : 1 ≤ ((Nat.ofDigits (2^67) CompactHighPopulation.highDigits : ℕ):V) := by
      simpa only [mul_one] using h.2.2.2
    exact (congrArg (fun H : V => 1≤H) high_eq).mpr hp
  · exact (congrArg (fun n : V => (CompactFixedBeta.betaNat:V)+1=Exp.exp n) he).mp hb

#print axioms low_eq
#print axioms high_eq
#print axioms data
end CompactSymbolicMaskData
