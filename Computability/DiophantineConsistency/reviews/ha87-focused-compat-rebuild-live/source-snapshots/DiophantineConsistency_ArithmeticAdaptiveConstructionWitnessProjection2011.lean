import DiophantineConsistency.ArithmeticAdaptiveConstructionWitness2011
import DiophantineConsistency.ArithmeticAdaptivePortValues2011

/-! Small concrete witness projections used to avoid unfolding the full DAG. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionWitnessProjection2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrierRadix2011 ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveConstructionWitness2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem witness_zero (v : Fin 14 → V) (r u g : V) : witness v r u g 0=v 0 := rfl
@[simp] theorem witness_one (v : Fin 14 → V) (r u g : V) : witness v r u g 1=v 1 := rfl
@[simp] theorem witness_two (v : Fin 14 → V) (r u g : V) : witness v r u g 2=v 2 := rfl
@[simp] theorem witness_six (v : Fin 14 → V) (r u g : V) : witness v r u g 6=ArithmeticCarrierRadix2011.q v*v 8 := rfl
@[simp] theorem witness_seven (v : Fin 14 → V) (r u g : V) : witness v r u g 7=v 7*(ArithmeticCarrierRadix2011.q v)^3 := rfl
@[simp] theorem witness_eight (v : Fin 14 → V) (r u g : V) : witness v r u g 8=r := rfl
@[simp] theorem witness_nine (v : Fin 14 → V) (r u g : V) : witness v r u g 9=v 10 := rfl
@[simp] theorem witness_ten (v : Fin 14 → V) (r u g : V) : witness v r u g 10=v 11 := rfl
end DiophantineConsistency.ArithmeticAdaptiveConstructionWitnessProjection2011
