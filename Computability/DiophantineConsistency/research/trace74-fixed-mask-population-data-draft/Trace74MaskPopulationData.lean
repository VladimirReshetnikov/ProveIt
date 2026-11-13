import DiophantineConsistency.CompactSymbolicPorts
import DiophantineConsistency.CompactLowExact
import DiophantineConsistency.CompactHighPopulation

/-! Source-only isolated transport of fixed symbolic population counts.
    It does not assert any graph-zero, repunit or guard consequence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74MaskPopulationData
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency CompactSymbolicPorts ArithmeticBinaryPopulation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem low_eq : (lowNat:V)=CompactConcreteIncrement.mask := rfl
theorem high_eq : (highNat:V)=((Nat.ofDigits (2^67) CompactHighPopulation.highDigits : ℕ):V) := rfl

attribute [local irreducible] lowNat highNat

theorem low_population : population (lowNat:V)=589083 := by
  have h : population (CompactConcreteIncrement.mask : V)=589083 :=
    CompactLowExact.model_population
  exact (congrArg (fun x : V => population x) low_eq).trans h

theorem high_population : population (highNat:V)=986 := by
  exact (congrArg (fun x : V => population x) high_eq).trans CompactHighPopulation.model_population

theorem population_sum : population (lowNat:V)+population (highNat:V)=(67:V)*8807 := by
  rw [low_population,high_population]
  norm_num

#print axioms low_eq
#print axioms high_eq
#print axioms low_population
#print axioms high_population
#print axioms population_sum
end Trace74MaskPopulationData
