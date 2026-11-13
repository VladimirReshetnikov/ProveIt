import DiophantineConsistency.Compact44.CompactStencilZeroCarry
import DiophantineConsistency.Compact44.CompactAlignedTemporalBoolean
import DiophantineConsistency.Compact44.CompactTemporalConstructedCarry

/-! Actual symbolic stencil: aligned Boolean source words imply zero carry. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactAlignedStencilZeroCarry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactGenericAlignedMass
open CompactConcreteIndexedMass CompactTwoBandFlatten CompactConstructedCarryInput
open CompactBitRotation CompactTemporalConstructedCarry CompactAlignedTemporalBoolean
open CompactStencilZeroCarry CompactConstructedWord CompactWordProperties
attribute [local irreducible] paramKernel rho selectors copies

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- If the source digits are Boolean and the temporal exponent is a multiple
of 67, every rotated stencil word is Boolean. Thus every cyclic carry is zero
and each digit of the exact symbolic remainder is its raw column sum. -/
theorem aligned_stencil_zero_carry (n e C : V) (hn : 0 < n)
    (hM : 0 < Exp.exp (67*n)-1) (hC : C < Exp.exp (67*n))
    (hcap : ∀ k < n, dig 67 C k ≤ 1) :
    ∀ k < n,
      carry 67 n (coeff : Idx → V)
        (GenericBandCarryFamily.word n C (bandOffsets position) (temporalWord n (67*e) C)) k = 0 ∧
      dig 67 (((((paramKernel rho : ℕ) : V) + Exp.exp (67*e))*C) % (Exp.exp (67*n)-1)) k =
        raw 67 coeff
          (GenericBandCarryFamily.word n C (bandOffsets position) (temporalWord n (67*e) C)) k := by
  have hcap3 : ∀ k < n, dig 67 C k ≤ 3 := fun k hk => le_trans (hcap k hk) (by norm_num)
  have hc := temporal_product_carry n (67*e) C hn hM hC hcap3
  have hbool : ∀ i : Idx, ∀ k < n,
      dig 67 (GenericBandCarryFamily.word n C (bandOffsets position) (temporalWord n (67*e) C) i) k ≤ 1 := by
    intro i k hk
    cases i with
    | inl i =>
      exact (BandCarryInputs.aligned_rotation_bounds n C (bandOffsets position i) 1 hn hC hcap).2 k hk
    | inr i =>
      change dig 67 (temporalWord n (67*e) C) k ≤ 1
      rw [aligned_digit C n e k hn hk hC]
      exact hcap _ (cyc_lt hn k (e%n))
  exact stencil_zero_carry hc hbool

/-- In particular, every packed compact cell word has carry-free symbolic
columns for every aligned temporal shift. -/
theorem packed_word_zero_carry (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N e : V) (hN : 0 < N) :
    ∀ k < 8807*N,
      carry 67 (8807*N) (coeff : Idx → V)
        (GenericBandCarryFamily.word (8807*N) (packedWord row dummy N) (bandOffsets position)
          (temporalWord (8807*N) (67*e) (packedWord row dummy N))) k = 0 ∧
      dig 67 (((((paramKernel rho : ℕ) : V) + Exp.exp (67*e)) * packedWord row dummy N) %
          (Exp.exp (67*(8807*N))-1)) k =
        raw 67 coeff (GenericBandCarryFamily.word (8807*N) (packedWord row dummy N)
          (bandOffsets position) (temporalWord (8807*N) (67*e) (packedWord row dummy N))) k := by
  have hn : 0 < (8807 : V)*N := mul_pos (by norm_num) hN
  have he : (1 : V) ≤ 67*((8807:V)*N) :=
    pos_iff_one_le.mp (mul_pos (by norm_num) hn)
  have htwo : (2 : V) ≤ Exp.exp (67*(8807*N)) := by
    simpa using exp_monotone_le.mpr he
  have hM : 0 < Exp.exp (67*(8807*N))-1 :=
    tsub_pos_of_lt (lt_of_lt_of_le (by norm_num) htwo)
  have hC : packedWord row dummy N < Exp.exp (67*(8807*N)) := by
    simpa only [mul_assoc] using packedWord_lt row dummy N
  exact aligned_stencil_zero_carry _ _ _ hn hM hC (word_cap row dummy N)

#print axioms CompactAlignedStencilZeroCarry.aligned_stencil_zero_carry
#print axioms CompactAlignedStencilZeroCarry.packed_word_zero_carry
end CompactAlignedStencilZeroCarry
