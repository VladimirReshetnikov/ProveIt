import DirectBFSConstructedCarry
import DiophantineConsistency.CompactBitRotation

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectBFSTemporalConstructedCarry
open DiophantineConsistency DiophantineConsistency.ArithmeticWindowDigits
  DiophantineConsistency.CompactHeterogeneousCarry
open DirectBFSConstructedCarry CompactBitRotation CompactSymbolicKernel DirectBFSSymbolicKernel
open CompactGenericAlignedMass DirectBFSModelMass CompactTwoBandFlatten
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
attribute [local irreducible] rho paramKernel selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Rotate the temporal term, then construct the carry input for the exact
cyclic remainder of `(K+2^e)*C` without a separate temporal bound premise. -/
theorem temporal_product_carry (n e C : V) (hn : 0<n)
    (hM : 0<Exp.exp (67*n)-1) (hC : C<Exp.exp (67*n))
    (hcap : ∀ k<n, dig 67 C k≤3) :
    CarryInput 67 n (((((paramKernel rho:ℕ):V)+Exp.exp e)*C) % (Exp.exp (67*n)-1)) 1
      (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41)))
      (GenericBandCarryFamily.coefficient (fun x => (alignedCoeff selectors copies x:V)))
      (GenericBandCarryFamily.word n C (bandOffsets position) (temporalWord n e C)) := by
  let M : V := Exp.exp (67*n)-1
  let K : V := ((paramKernel rho:ℕ):V)
  have hT := temporal_word_lt n e C hn hC
  have hc := symbolic_product_carry n C (temporalWord n e C) hn hM hC hcap hT
  have ht := temporal_mod n e C hn hM
  have heq : (K*C+temporalWord n e C)%M=((K+Exp.exp e)*C)%M := by
    rw [add_mul]
    exact TwoBand.add_congr_mod M _ _ _ _ hM rfl ht.symm
  rwa [heq] at hc

#print axioms DirectBFSTemporalConstructedCarry.temporal_product_carry
end DirectBFSTemporalConstructedCarry
