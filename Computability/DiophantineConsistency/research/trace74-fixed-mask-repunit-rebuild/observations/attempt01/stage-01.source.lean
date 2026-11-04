import DiophantineConsistency.ArithmeticMaskPopulation
import DiophantineConsistency.CompactFixedBeta
import DiophantineConsistency.CompactSymbolicPorts
import DiophantineConsistency.CompactLowExact
import DiophantineConsistency.CompactLowEven
import DiophantineConsistency.CompactHighResidue

/-! Source draft: fixed symbolic masks and the same positive repunit witness
    supply the radix identity and exact mask-population sum. No graph zero is
    claimed to provide a repunit witness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74FixedMaskRepunit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency CompactFixedBeta CompactSymbolicPorts
open ArithmeticBinaryPopulation ArithmeticRepunit
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem radix_and_mask_population (N J : V) (hN : 0<N)
    (hJ : J=rep ((67:V)*8807) N) :
    (betaNat:V)*J+1=Exp.exp (((67:V)*8807)*N) ∧
      population ((lowNat:V)*J+1)+population ((highNat:V)*J-1)=
        ((67:V)*8807)*N+2 := by
  let d : V := 67*8807
  have hb : (betaNat:V)=Exp.exp d-1 := by
    rw [←CompactFixedBeta.beta_identity]
    simp
  have hradix : (betaNat:V)*J+1=Exp.exp (d*N) := by
    rw [hJ,hb]
    exact repunit_identity d N
  have hlow : (lowNat:V)<Exp.exp d := by
    change CompactConcreteIncrement.mask<Exp.exp ((67:V)*8807)
    exact CompactConcreteMask.model_lt
  have hhigh : (highNat:V)<Exp.exp d := by
    change ((Nat.ofDigits (2^67) CompactHighPopulation.highDigits : ℕ):V)<Exp.exp ((67:V)*8807)
    exact CompactHighPopulation.model_lt
  have hlow2 : (lowNat:V)%2=0 := by
    change CompactConcreteIncrement.mask%2=0
    exact CompactLowEven.low_even
  have hhigh8 : (highNat:V)%8=4 := by
    change ((Nat.ofDigits (2^67) CompactHighPopulation.highDigits : ℕ):V)%8=4
    exact CompactHighResidue.model_mod_eight
  have hsum : population (lowNat:V)+population (highNat:V)=d := by
    change population ((Nat.ofDigits (2^67) (CompactListMask.digits (2^67) 8807 1063 CompactConcreteMask.support) : ℕ):V)+_= _
    rw [CompactLowExact.model_population,CompactHighPopulation.model_population]
    norm_num [d]
  have hpop := ArithmeticMaskPopulation.repeated_mask_population d N (lowNat:V) (highNat:V)
    (by dsimp [d]; norm_num) hN hlow hhigh hlow2 hhigh8 hsum
  refine ⟨hradix,?_⟩
  rw [hJ]
  exact hpop

#print axioms Trace74FixedMaskRepunit.radix_and_mask_population
end Trace74FixedMaskRepunit
