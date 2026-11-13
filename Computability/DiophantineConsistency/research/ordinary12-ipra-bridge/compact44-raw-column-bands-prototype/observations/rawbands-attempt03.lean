import DiophantineConsistency.FixedGraphCleanCarry
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace RawColumnBands
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactIndexedFlatten CompactTwoBandFlatten
open CompactPartialBandRotation
attribute [local irreducible] Compact943Data.rows
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def bareColumn (n C k : V) : V := ∑ j : Fin 5, dig 67 (rot 67 n C (TwoBand.bareOffset j%n)) k

theorem flatten (pos : Fin 41→ℕ) (n C T k : V) :
    raw 67 (GenericBandCarryFamily.coefficient (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V)))
      (GenericBandCarryFamily.word n C (bandOffsets pos) T) k =
      columnBand pos 4393 n C k + columnBand pos 5495 n C k + bareColumn n C k + dig 67 T k := by
  have h := CompactIndexedFlatten.flatten selectors copies (selectorOffset 4393)
    (selectorOffset 5495) (copyOffset pos 4393) (copyOffset pos 5495)
    TwoBand.bareOffset (fun x => dig 67 (rot 67 n C (x%n)) k)
  unfold raw
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique,GenericBandCarryFamily.coefficient,
    GenericBandCarryFamily.word,one_mul]
  have h' := congrArg (fun z : V => z+dig 67 T k) h
  simpa only [bandOffsets,columnBand,bareColumn,selectorCoeff,copyCoeff] using h'

theorem decoder_bands (pos : Fin 41→ℕ) (n C T k : V)
    (hn : 0<n) (hk : k<n) (hC : C<Exp.exp (67*n)) :
    raw 67 (GenericBandCarryFamily.coefficient (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V)))
      (GenericBandCarryFamily.word n C (bandOffsets pos) T) k =
      ((∑ j, CompactPartialBand.selectorDigit n C k 4393 j) + Exp.exp 10 *
        ((∑ j, (Exp.exp 41-Compact943Decoder.tileValue (V:=V) j)*CompactPartialBand.selectorDigit n C k 4393 j) +
         ∑ j, (2:V)^j.val*CompactPartialBand.copyDigit pos n C k 4393 j)) +
      ((∑ j, CompactPartialBand.selectorDigit n C k 5495 j) + Exp.exp 10 *
        ((∑ j, (Exp.exp 41-Compact943Decoder.tileValue (V:=V) j)*CompactPartialBand.selectorDigit n C k 5495 j) +
         ∑ j, (2:V)^j.val*CompactPartialBand.copyDigit pos n C k 5495 j)) +
      bareColumn n C k + dig 67 T k := by
  rw [flatten,band_column pos 4393 n C k hn hk hC,band_column pos 5495 n C k hn hk hC]
#print axioms RawColumnBands.flatten
#print axioms RawColumnBands.decoder_bands
end RawColumnBands
