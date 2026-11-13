import Trace74GenericRepunitPopulation
import Trace74MaskPopulationData
import DiophantineConsistency.CompactFixedBeta
import DiophantineConsistency.CompactLowEven
import DiophantineConsistency.CompactHighResidue

/-! Source-only split specialization. The positive repunit witness remains
    explicit; no graph-zero-to-repunit or guard theorem is claimed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74FixedMaskRepunitSplit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency CompactFixedBeta CompactSymbolicPorts
open ArithmeticBinaryPopulation ArithmeticRepunit Trace74MaskPopulationData
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] lowNat highNat CompactFixedBeta.betaNat

theorem radix_and_mask_population (N J : V) (hN : 0<N)
    (hJ : J=rep ((67:V)*8807) N) :
    (betaNat:V)*J+1=Exp.exp (((67:V)*8807)*N) ∧
      population ((lowNat:V)*J+1)+population ((highNat:V)*J-1)=
        ((67:V)*8807)*N+2 := by
  let d : V := 67*8807
  have hb : (betaNat:V)+1=Exp.exp d := CompactFixedBeta.beta_identity
  have hlow : (lowNat:V)<Exp.exp d :=
    (congrArg (fun x : V => x<Exp.exp d) low_eq).mpr CompactConcreteMask.model_lt
  have hhigh : (highNat:V)<Exp.exp d :=
    (congrArg (fun x : V => x<Exp.exp d) high_eq).mpr CompactHighPopulation.model_lt
  have hlow2 : (lowNat:V)%2=0 :=
    (congrArg (fun x : V => x%2=0) low_eq).mpr CompactLowEven.low_even
  have hhigh8 : (highNat:V)%8=4 :=
    (congrArg (fun x : V => x%8=4) high_eq).mpr CompactHighResidue.model_mod_eight
  have hsum : population (lowNat:V)+population (highNat:V)=d := population_sum
  exact Trace74GenericRepunitPopulation.radix_and_mask_population d N J (betaNat:V)
    (lowNat:V) (highNat:V) (by dsimp [d]; norm_num) hN hJ hb hlow hhigh hlow2 hhigh8 hsum

#print axioms Trace74FixedMaskRepunitSplit.radix_and_mask_population
end Trace74FixedMaskRepunitSplit
