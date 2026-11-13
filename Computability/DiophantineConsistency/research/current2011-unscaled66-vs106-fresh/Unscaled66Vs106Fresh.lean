import Current2011Unscaled66Fresh

/-! Exact strong-locus identity and all-model comparison of the 66/138
and 67/106 integer expressions on the same model valuation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Unscaled66Vs106Fresh
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open Current2011Unscaled66Fresh
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

section Ring
variable {R : Type*} [CommRing R]

/-- The graph values agree on the strong-norm-one locus. -/
theorem strong_locus_identity (p : Fin 4 → R) (v : Fin 14 → R) :
    unscaledValue p v - ModelCarrierScaled.value106 p v =
      -(Carrier65.core p v).delta *
        ((Carrier65.core p v).P * (Carrier65.core p v).Q * (Carrier65.core p v).W) *
        Carrier65.strong (Carrier65.core p v) * (Carrier65.strong (Carrier65.core p v) - 1) *
        ((Carrier65.core p v).V ^ 2 - (Carrier65.core p v).y ^ 2) := by
  have hU : (Carrier65.core p v).U =
      (Carrier65.core p v).delta ^ 2 *
        ((Carrier65.core p v).i * (Carrier65.core p v).c ^ 2) ^ 2 *
        ((Carrier65.core p v).V ^ 2 - (Carrier65.core p v).y ^ 2) +
      (Carrier65.core p v).y ^ 2 := by
    change ((Carrier65.core p v).i * (Carrier65.core p v).delta * (Carrier65.core p v).c ^ 2) ^ 2 *
      ((Carrier65.core p v).V ^ 2 - (Carrier65.core p v).y ^ 2) +
      (Carrier65.core p v).y ^ 2 = _
    ring
  dsimp only [unscaledValue, ModelCarrierScaled.value106]
  rw [hU]
  unfold Carrier65.strong
  ring

end Ring

section Model
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem sameZero138_106 (v : Fin 14 → V) :
    InternalZero (positiveShift (Current2011Unscaled66Fresh.expressionAt CurrentWindowCarry2011.ports)) v ↔
      InternalZero (positiveShift (ModelCarrierCurrent.expressionAt106 CurrentWindowCarry2011.ports)) v :=
  (sameZero138 v).trans (FreshModel106.sameZero106 v).symm

end Model

#print axioms strong_locus_identity
#print axioms sameZero138_106

end DiophantineConsistency.Unscaled66Vs106Fresh
