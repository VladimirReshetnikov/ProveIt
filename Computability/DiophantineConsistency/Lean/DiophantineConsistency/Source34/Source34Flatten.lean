import DiophantineConsistency.Source34.Source34Rotation
import DiophantineConsistency.Mixed121.Mixed121Flatten

/-! # The flattened source34 band family

`Mixed121Flatten` at the source34 tuple. The coefficient family
(`Mixed121Flatten.selectors`, `copies`) and the carry room
(`Mixed121Flatten.clause_lt`, `W_lt`, `aligned_mass_lt`, `aligned_room`) depend
only on the shared clause coefficients and weights, and are used from
`Mixed121Flatten`. What changes is the offset family: `bandOffsets` uses the
source34 copy offsets and bare offsets of `Source34Rotation`, so
`exact_bands`, `bareColumn`, `column_flatten` and `decoder_bands` are
re-declared. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Source34Flatten
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticCyclicWord ArithmeticWindowDigits CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactIndexedFlatten Source34Rotation
open Mixed121Rotation (selectorCoeff copyCoeff selectorOffset coefficient word)
open Mixed121Flatten (selectors copies)
attribute [local irreducible] Compact943Data.rows
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def bandOffsets : Aligned (Fin 943) (Fin 44) → V :=
  offsets (selectorOffset 4393) (selectorOffset 5495) (copyOffset 4393) (copyOffset 5495)
    bareOffset

theorem exact_bands (n C : V) :
    (∑ x : Aligned (Fin 943) (Fin 44),
      (alignedCoeff selectors copies x : V) * rot 121 n C (bandOffsets x % n)) =
    rotatedBand 4393 n C + rotatedBand 5495 n C + bareRotated n C := by
  have h := CompactIndexedFlatten.flatten selectors copies (selectorOffset 4393)
    (selectorOffset 5495) (copyOffset 4393) (copyOffset 5495)
    bareOffset (fun x => rot 121 n C (x % n))
  simpa only [bandOffsets, rotatedBand, bareRotated, selectorCoeff, copyCoeff,
    selectors, copies] using h

def bareColumn (n C k : V) : V := ∑ j : Fin 5, dig 121 (rot 121 n C (bareOffset j % n)) k

theorem column_flatten (n C T k : V) :
    raw 121 (coefficient (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V)))
      (word 121 n C bandOffsets T) k =
      columnBand 4393 n C k + columnBand 5495 n C k + bareColumn n C k + dig 121 T k := by
  have h := CompactIndexedFlatten.flatten selectors copies (selectorOffset 4393)
    (selectorOffset 5495) (copyOffset 4393) (copyOffset 5495)
    bareOffset (fun x => dig 121 (rot 121 n C (x%n)) k)
  unfold raw
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique, coefficient, word, one_mul]
  have h' := congrArg (fun z : V => z+dig 121 T k) h
  simpa only [bandOffsets, columnBand, bareColumn, selectorCoeff, copyCoeff, selectors, copies]
    using h'

/-- A raw column of the flattened family: two decoder inputs, the bare column
and the temporal digit. -/
theorem decoder_bands (n C T k : V) (hn : 0<n) (hk : k<n) (hC : C<Exp.exp (121*n)) :
    raw 121 (coefficient (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V)))
      (word 121 n C bandOffsets T) k =
      ((∑ i, Mixed121Band.selDigit n C k 4393 i *
          (1 + Exp.exp 10 * ModelDigitTransfer.dsum (Exp.exp 2)
            (fun d => (Mixed121Digits.digit (Compact943Data.row i) d : V)) 44)) +
        Exp.exp 10 * ModelDigitTransfer.dsum (Exp.exp 2) (Source34Band.copyDigit n C k 4393) 44) +
      ((∑ i, Mixed121Band.selDigit n C k 5495 i *
          (1 + Exp.exp 10 * ModelDigitTransfer.dsum (Exp.exp 2)
            (fun d => (Mixed121Digits.digit (Compact943Data.row i) d : V)) 44)) +
        Exp.exp 10 * ModelDigitTransfer.dsum (Exp.exp 2) (Source34Band.copyDigit n C k 5495) 44) +
      bareColumn n C k + dig 121 T k := by
  rw [column_flatten, band_column 4393 n C k hn hk hC, band_column 5495 n C k hn hk hC]
end Source34Flatten
#print axioms Source34Flatten.exact_bands
#print axioms Source34Flatten.column_flatten
#print axioms Source34Flatten.decoder_bands
