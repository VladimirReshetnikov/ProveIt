import CompactSymbolicMaskCasts
import CompactSymbolicBetaCast
import CompactGenericPortProjections

/-! Pointwise cast bindings of the four compact symbolic ports. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactSymbolicPortProjections
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ArithmeticRepunit CompactSymbolicPorts CompactConstructedRank
attribute [local irreducible] CompactFixedBeta.betaNat lowNat highNat Nat.ofDigits
  CompactListMask.digits CompactConcreteMask.support CompactHighPopulation.highDigits
  CompactConcreteIncrement.mask
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def portsInt (K : ℕ) : Fin 4 → ℤ := fun j => (ports CompactFixedBeta.betaNat K lowNat highNat j:ℤ)

private theorem cast_nat (n : ℕ) : ((n:ℤ):DiffRing V)=ι (n:V) := by
  simp only [Int.cast_natCast, map_natCast]

theorem beta (K : ℕ) (N : V) :
    ι (rep 590069 N)*((portsInt K 0:ℤ):DiffRing V)=ι (Exp.exp (590069*N)-1) := by
  rw [portsInt,CompactGenericPortProjections.at_zero]
  exact CompactSymbolicBetaCast.beta_product N

theorem kernel (K : ℕ) : ((portsInt K 1:ℤ):DiffRing V)=ι (K:V) := by
  rw [portsInt,CompactGenericPortProjections.at_one]
  exact cast_nat K

theorem low (K : ℕ) : ((portsInt K 2:ℤ):DiffRing V)=ι (CompactConstructedRank.low:V) := by
  rw [portsInt,CompactGenericPortProjections.at_two]
  rw [cast_nat,CompactSymbolicMaskCasts.low_cast]

theorem high (K : ℕ) : ((portsInt K 3:ℤ):DiffRing V)=
    ι (CompactConstructedRank.high+(Exp.exp (590069:V)-1)) := by
  rw [portsInt,CompactGenericPortProjections.at_three]
  rw [cast_nat,Nat.cast_add,CompactSymbolicMaskCasts.high_cast,CompactSymbolicBetaCast.beta_model,add_comm]

#print axioms CompactSymbolicPortProjections.beta
#print axioms CompactSymbolicPortProjections.kernel
#print axioms CompactSymbolicPortProjections.low
#print axioms CompactSymbolicPortProjections.high
end CompactSymbolicPortProjections
