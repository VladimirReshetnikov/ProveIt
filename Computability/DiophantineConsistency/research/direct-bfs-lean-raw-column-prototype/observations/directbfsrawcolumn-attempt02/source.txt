import DirectBFSBandCarry
import DirectBFSCoefficientDecoder
import DiophantineConsistency.RawColumnBands

/-! Direct-BFS local band and raw-column decomposition. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSRawColumn
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticCyclicWord ArithmeticWindowDigits CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactIndexedFlatten CompactTwoBandFlatten CompactPartialBandRotation CompactPartialBand
open DirectBFSModelMass
attribute [local irreducible] DirectBFSSymbolicKernel.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def columnBand (pos : Fin 41 → ℕ) (T : ℕ) (n C k : V) : V :=
  (∑ i : Fin 943, (selectors i:V)*dig 67 (rot 67 n C (selectorOffset T i%n)) k)+
  (∑ j : Fin 41, (copies j:V)*dig 67 (rot 67 n C (copyOffset pos T j%n)) k)

theorem band_column (pos : Fin 41 → ℕ) (T : ℕ) (n C k : V)
    (hn : 0<n) (hk : k<n) (hC : C<Exp.exp (67*n)) :
    columnBand pos T n C k =
    (∑ i,selectorDigit n C k T i)+Exp.exp 10*
      ((∑ i,(Exp.exp 41-DirectBFSDecoder.tileValue (V:=V) i)*selectorDigit n C k T i)+
       ∑ j,(2:V)^j.val*copyDigit pos n C k T j) := by
  have hi : ∀ i : Fin 943, dig 67 (rot 67 n C (selectorOffset T i%n)) k=selectorDigit n C k T i := by
    intro i
    unfold selectorDigit selectorOffset
    rw [dig_rot 67 n C _ k (mod_lt _ hn) hk hC,cyc_mod n k _ hn]
  have hj : ∀ j : Fin 41, dig 67 (rot 67 n C (copyOffset pos T j%n)) k=copyDigit pos n C k T j := by
    intro j
    unfold copyDigit copyOffset
    rw [dig_rot 67 n C _ k (mod_lt _ hn) hk hC,cyc_mod n k _ hn]
  unfold columnBand
  simp_rw [hi,hj]
  simpa only [selectors,copies] using
    (DirectBFSCoefficientDecoder.finite_decomposition (fun i => selectorDigit n C k T i)
      (fun j => copyDigit pos n C k T j))

theorem flatten (pos : Fin 41 → ℕ) (n C T k : V) :
    raw 67 (GenericBandCarryFamily.coefficient (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V)))
      (GenericBandCarryFamily.word n C (bandOffsets pos) T) k =
      columnBand pos 4393 n C k+columnBand pos 5495 n C k+RawColumnBands.bareColumn n C k+dig 67 T k := by
  have h := CompactIndexedFlatten.flatten selectors copies (selectorOffset 4393)
    (selectorOffset 5495) (copyOffset pos 4393) (copyOffset pos 5495)
    TwoBand.bareOffset (fun x => dig 67 (rot 67 n C (x%n)) k)
  unfold raw
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique,GenericBandCarryFamily.coefficient,GenericBandCarryFamily.word,one_mul]
  have h' := congrArg (fun z : V => z+dig 67 T k) h
  simpa only [bandOffsets,columnBand,RawColumnBands.bareColumn] using h'

theorem decoder_bands (pos : Fin 41 → ℕ) (n C T k : V)
    (hn : 0<n) (hk : k<n) (hC : C<Exp.exp (67*n)) :
    raw 67 (GenericBandCarryFamily.coefficient (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V)))
      (GenericBandCarryFamily.word n C (bandOffsets pos) T) k =
      ((∑ j,selectorDigit n C k 4393 j)+Exp.exp 10*
        ((∑ j,(Exp.exp 41-DirectBFSDecoder.tileValue (V:=V) j)*selectorDigit n C k 4393 j)+
         ∑ j,(2:V)^j.val*copyDigit pos n C k 4393 j))+
      ((∑ j,selectorDigit n C k 5495 j)+Exp.exp 10*
        ((∑ j,(Exp.exp 41-DirectBFSDecoder.tileValue (V:=V) j)*selectorDigit n C k 5495 j)+
         ∑ j,(2:V)^j.val*copyDigit pos n C k 5495 j))+
      RawColumnBands.bareColumn n C k+dig 67 T k := by
  rw [flatten,band_column pos 4393 n C k hn hk hC,band_column pos 5495 n C k hn hk hC]

#print axioms DirectBFSRawColumn.band_column
#print axioms DirectBFSRawColumn.flatten
#print axioms DirectBFSRawColumn.decoder_bands
end DirectBFSRawColumn
