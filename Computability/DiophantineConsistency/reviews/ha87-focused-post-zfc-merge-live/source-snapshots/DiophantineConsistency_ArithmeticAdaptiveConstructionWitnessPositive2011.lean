import DiophantineConsistency.ArithmeticAdaptiveConstructionWitness2011

/-! Positivity of the concrete adaptive witness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionWitnessPositive2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011 ArithmeticAdaptiveConstructionWitness2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem witness_positive (v : Fin 14 → V) (r u gamma : V)
    (hv : ∀ j, 0<v j) (hr : 0<r) (hu : 0<u) (hg : 0<gamma) :
    ∀ j, 0<witness v r u gamma j := by
  let q := ArithmeticCarrierRadix2011.q v
  let X := q*v 8
  let Y := v 7*q^3
  let a := X*Y+Y
  let delta := (a+1)*(a+3)
  have hq : 0<q := by
    change 0<(CurrentMasks2011.beta:V)*v 0+1
    exact lt_of_lt_of_le (by norm_num : (0:V)<1) (le_add_of_nonneg_left (by simp))
  have hX : 0<X := mul_pos hq (hv 8)
  have hY : 0<Y := mul_pos (hv 7) (pow_pos hq _)
  have hd : 0<delta := mul_pos (by simp [a]) (by simp [a])
  intro j
  change 0<(![v 0,v 1,v 2,v 4,delta*v 5,v 6,X,Y,r,v 10,v 11,u,gamma] : Fin 13 → V) j
  fin_cases j
  exacts [hv 0,hv 1,hv 2,hv 4,mul_pos hd (hv 5),hv 6,hX,hY,hr,hv 10,hv 11,hu,hg]
end DiophantineConsistency.ArithmeticAdaptiveConstructionWitnessPositive2011
