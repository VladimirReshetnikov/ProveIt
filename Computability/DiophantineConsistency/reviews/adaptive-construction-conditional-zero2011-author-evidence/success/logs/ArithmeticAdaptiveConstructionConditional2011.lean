import DiophantineConsistency.ArithmeticAdaptiveConstructionFirstWitnessProjected2011
import DiophantineConsistency.ArithmeticAdaptiveConstructionMainChosen2011
import DiophantineConsistency.ArithmeticAdaptiveConstructionAuxChosen2011
import DiophantineConsistency.ArithmeticAdaptiveConstructionWitnessPositive2011
import DiophantineConsistency.ArithmeticAdaptiveConstructionFactorZero2011

/-! Conditional full adaptive zero from one common enriched old witness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionConditional2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011
  ArithmeticPellRecurrence ArithmeticOuterSeed ArithmeticAdaptiveScaledNorms2011
  ArithmeticAdaptiveFactorUnits2011 ArithmeticAdaptiveFactorMagnitude2011
  ArithmeticAdaptiveConstructionWitness2011 ArithmeticAdaptiveConstructionWitnessPositive2011
  ArithmeticAdaptiveConstructionFirstWitnessProjected2011 ArithmeticAdaptiveConstructionMainChosen2011
  ArithmeticAdaptiveConstructionAuxChosen2011 ArithmeticAdaptiveConstructionCorrectionSeed2011
  ArithmeticAdaptiveConstructionAuxBind2011 ArithmeticAdaptiveConstructionFirstData2011
  ArithmeticAdaptiveConstructionFactorZero2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The enriched old witness, explicitly assumed here, supplies a zero of the
literal shifted thirteen-coordinate adaptive equation. -/
theorem shifted_zero_of_enriched_witness
    (v : Fin 14 → V) (exponent b : V)
    (hv : ∀ j, 0<v j)
    (hF : v 1≤ArithmeticCarrierRadix2011.q v)
    (he : Equations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) v)
    (hphase : rank v%4=3) (hy : v 12=ycoord (rank v) b)
    (hq : ArithmeticCarrierRadix2011.q v=Exp.exp exponent)
    (hX : Exp.exp (rank v)=ArithmeticCarrierRadix2011.q v*v 8)
    (hR : 2*exponent≤rank v)
    (hseed : SeedRelations exponent (rank v) (v 7) (v 9) (v 10) (v 11) (v 13))
    (horient : let q := ArithmeticCarrierRadix2011.q v
      let Y := v 7*q^3
      let c := (v 10+v 11)*Y+v 10
      let L := v 4*v 4*c*v 6
      let M := v 4*v 4*rank v+c
      L=(L-M)+(M-L)+c+v 4*v 4*rank v) :
    ∃ x : Fin 13 → V, InternalZero naturalExpression x := by
  obtain ⟨r,hr,hdata⟩ := actual_first_data v exponent hv he hphase hq hX hR hseed
  have hXq : Exp.exp (rank v)=Exp.exp exponent*v 8 := by rw [←hq]; exact hX
  obtain ⟨t,gamma,hgamma,hk,hcorr⟩ := positive_correction_of_seed exponent (rank v)
    (v 7) (v 9) (v 10) (v 11) (v 13) (v 8) (hv 7) (hv 13) hphase hXq hseed
  rw [←hq] at hk
  obtain ⟨aux,haux,hu⟩ := adaptive_auxiliary_of_phase v he hphase b hy
  let w := witness v r aux gamma
  have hpos : ∀ j, 0<w j := witness_positive v r aux gamma hv hr haux hgamma
  have hf := first_unit_of_data v r aux gamma hdata
  have hm := main_unit_of_correction v exponent r aux gamma t hF hq hX hseed hk hcorr
  have ha := aux_unit_of_coordinate v r aux gamma hv he hF horient hu
  have hs := witness_strong_unit currentPorts v r aux gamma hv he
  rw [currentPorts_cast] at hs
  have hall : FactorUnits CurrentWindowCarry2011.ports w := ⟨hf,hm,ha,hs⟩
  exact ⟨fun j => w j-1,shifted_zero_of_factor_units w hpos hall⟩
end DiophantineConsistency.ArithmeticAdaptiveConstructionConditional2011
