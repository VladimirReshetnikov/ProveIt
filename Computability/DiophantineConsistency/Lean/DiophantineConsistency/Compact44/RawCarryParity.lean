import DiophantineConsistency.Compact44.RawParityBands
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace RawCarryParity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten CompactPartialBand
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem expand (pos : Fin 41→ℕ) (n C T k c : V)
    (hn : 0<n) (hk : k<n) (hC : C<Exp.exp (67*n))
    (hpar : (raw 67 (GenericBandCarryFamily.coefficient (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V)))
      (GenericBandCarryFamily.word n C (bandOffsets pos) T) k + c)%2=0) :
    (RawParityBands.selectorsAt n C k 4393 + RawParityBands.selectorsAt n C k 5495 +
      RawColumnBands.bareColumn n C k + dig 67 T k + c)%2=0 := by
  have h := RawParityBands.raw_mod_two pos n C T k hn hk hC
  rw [mod_add (by norm_num : (0:V)<2), h, ←mod_add (by norm_num : (0:V)<2)] at hpar
  exact hpar
#print axioms RawCarryParity.expand
end RawCarryParity
