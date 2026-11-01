import DiophantineConsistency.ArithmeticAdaptivePositiveAuxSeed2011
import DiophantineConsistency.ArithmeticAdaptiveConstructionConditional2011
import DiophantineConsistency.ArithmeticConstructionUnboundedCompat
import DiophantineConsistency.ArithmeticLocalNormalization

/-! Preserve the strict auxiliary orientation through the constructed adaptive witness.
The machine theorem uses the internal run and the established local normalization. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveOrientedWitness2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticAdaptivePositiveAuxSeed2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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


theorem shifted_zero_of_enriched_witness_oriented
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
    ∃ r aux gamma : V,
      let w := witness v r aux gamma
      (∀ j, 0<w j) ∧ InternalZero expression w ∧
      let q := ArithmeticCarrierRadix2011.q v
      let Y := v 7*q^3
      let c := (v 10+v 11)*Y+v 10
      v 4*v 4*rank v+c < v 4*v 4*c*v 6 := by
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
  have hs := shifted_zero_of_factor_units w hpos hall
  have hw : (fun j => (w j-1)+1)=w := by
    funext j
    exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hpos j))
  have hz : InternalZero expression w := by
    have hh := (internalZero_positiveShift expression (fun j => w j-1)).mp hs
    rw [hw] at hh
    exact hh
  exact ⟨r,aux,gamma,hpos,hz,exact_orientation_strict v hv he horient⟩


open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticCantor (first)

theorem oriented_witness_of_run (T : V)
    (hT : first (ArithmeticMachineRun215.run T)=0) :
    ∃ (v : Fin 14 → V) (r aux gamma : V),
      let w := witness v r aux gamma
      (∀ j, 0<w j) ∧ InternalZero expression w ∧
      let q := ArithmeticCarrierRadix2011.q v
      let Y := v 7*q^3
      let c := (v 10+v 11)*Y+v 10
      v 4*v 4*rank v+c < v 4*v 4*c*v 6 := by
  obtain ⟨v,hv,hF,he,hphase,⟨b,hy⟩,u,hq,hX,hR,hseed,horient⟩ :=
    ArithmeticConstructionUnboundedCompat.construction_unbounded_seed_phase_hL
      ArithmeticLocalNormalization.localNormalization T hT
  have hf : v 1≤ArithmeticCarrierRadix2011.q v := by
    change v 1≤(CurrentMasks2011.beta:V)*v 0+1
    exact hF
  obtain ⟨r,aux,gamma,hpos,hzero,hstrict⟩ :=
    shifted_zero_of_enriched_witness_oriented v u b hv hf he hphase hy hq hX hR hseed horient
  exact ⟨v,r,aux,gamma,hpos,hzero,hstrict⟩



end DiophantineConsistency.ArithmeticAdaptiveOrientedWitness2011
