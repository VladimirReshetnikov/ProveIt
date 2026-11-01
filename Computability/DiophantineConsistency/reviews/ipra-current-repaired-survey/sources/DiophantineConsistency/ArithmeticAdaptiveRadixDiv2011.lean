import DiophantineConsistency.ArithmeticAdaptiveRadix2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveRadixDiv2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveRadix2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem current_X_divisible (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) :
    (1+v 0*(CurrentMasks2011.beta:V))∣v 6 := by
  obtain ⟨_,w,_,_,_,_,hX,_,_⟩ := current_radix v hv hz
  exact ⟨w,hX⟩
end DiophantineConsistency.ArithmeticAdaptiveRadixDiv2011
