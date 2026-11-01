import DiophantineConsistency.ArithmeticAdaptiveConstructionFirstInputProjected2011

/-! Complete the literal first-factor client from the extracted data. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionFirstWitnessProjected2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011 ArithmeticOuterSeed
  ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveFactorMagnitude2011
  ArithmeticAdaptiveConstructionFirstFactor2011 ArithmeticAdaptiveConstructionWitness2011
  ArithmeticAdaptiveConstructionFirstData2011 ArithmeticAdaptiveConstructionFirstInputProjected2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_unit_of_data (v : Fin 14 → V) (r aux gamma : V) (hdata : FirstData v r) :
    (ArithmeticAdaptiveFactorMagnitude2011.pairEval (factors CurrentWindowCarry2011.ports).1 (witness v r aux gamma)).1 =
      (ArithmeticAdaptiveFactorMagnitude2011.pairEval (factors CurrentWindowCarry2011.ports).1 (witness v r aux gamma)).2+1 := by
  let q := ArithmeticCarrierRadix2011.q v
  let tau := q*v 8*(v 7*q^3)*v 9+(v 10+v 11)-rank v
  obtain ⟨hcut,hnorm⟩ := first_input_of_data v r aux gamma hdata
  have h := first_factor_of_additive currentPorts (witness v r aux gamma) tau hcut hnorm
  rw [currentPorts_cast] at h
  exact h

theorem witness_first_unit (v : Fin 14 → V) (u aux gamma : V)
    (hv : ∀ j, 0<v j)
    (he : Equations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) v)
    (hphase : rank v%4=3)
    (hq : ArithmeticCarrierRadix2011.q v=Exp.exp u)
    (hX : Exp.exp (rank v)=ArithmeticCarrierRadix2011.q v*v 8)
    (hR : 2*u≤rank v)
    (hseed : SeedRelations u (rank v) (v 7) (v 9) (v 10) (v 11) (v 13)) :
    ∃ r : V, 0<r ∧
      (ArithmeticAdaptiveFactorMagnitude2011.pairEval (factors CurrentWindowCarry2011.ports).1 (witness v r aux gamma)).1 =
        (ArithmeticAdaptiveFactorMagnitude2011.pairEval (factors CurrentWindowCarry2011.ports).1 (witness v r aux gamma)).2+1 := by
  obtain ⟨r,hr,hdata⟩ := actual_first_data v u hv he hphase hq hX hR hseed
  exact ⟨r,hr,first_unit_of_data v r aux gamma hdata⟩
end DiophantineConsistency.ArithmeticAdaptiveConstructionFirstWitnessProjected2011
