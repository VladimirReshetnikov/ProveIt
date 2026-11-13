import DiophantineConsistency.Compact44.CompactFixedBeta
import DiophantineConsistency.ModelDifferenceRing
import DiophantineConsistency.ArithmeticRepunit

/-! The compact symbolic beta times its repunit, in the model difference ring. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactSymbolicBetaCast
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ArithmeticRepunit
attribute [local irreducible] CompactFixedBeta.betaNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem beta_model : (CompactFixedBeta.betaNat:V)=Exp.exp (590069:V)-1 := by
  have h : (CompactFixedBeta.betaNat:V)+1=Exp.exp 590069 := by
    simpa only [show (67:V)*8807=590069 by norm_num] using (CompactFixedBeta.beta_identity (V:=V))
  rw [←h,add_tsub_cancel_right]

theorem beta_product (N : V) :
    ι (rep 590069 N)*(((CompactFixedBeta.betaNat:ℕ):ℤ):DiffRing V) =
      ι (Exp.exp (590069*N)-1) := by
  have h := repunit_identity (590069:V) N
  rw [←beta_model] at h
  have hp : (CompactFixedBeta.betaNat:V)*rep 590069 N=Exp.exp (590069*N)-1 := by
    rw [←h,add_tsub_cancel_right]
  rw [Int.cast_natCast, ←map_natCast ι, ←map_mul, mul_comm, hp]

#print axioms CompactSymbolicBetaCast.beta_model
#print axioms CompactSymbolicBetaCast.beta_product
end CompactSymbolicBetaCast
