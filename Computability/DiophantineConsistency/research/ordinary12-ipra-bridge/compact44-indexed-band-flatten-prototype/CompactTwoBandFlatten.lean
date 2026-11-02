import DiophantineConsistency.CompactIndexedFlatten
import DiophantineConsistency.CompactConcreteIndexedModel
import DiophantineConsistency.TwoBand
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Compact943Data.rows
noncomputable section
namespace CompactTwoBandFlatten
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactIndexedFlatten
open DiophantineConsistency CompactPartialBandRotation ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def bandOffsets (pos : Fin 41 → ℕ) : Aligned (Fin 943) (Fin 41) → V :=
  offsets (selectorOffset 4393) (selectorOffset 5495)
    (copyOffset pos 4393) (copyOffset pos 5495) TwoBand.bareOffset

theorem exact_bands (pos : Fin 41 → ℕ) (n C : V) :
    (∑ x : Aligned (Fin 943) (Fin 41),
      (alignedCoeff selectors copies x : V) * rot 67 n C (bandOffsets pos x % n)) =
    rotatedBand pos 4393 n C + rotatedBand pos 5495 n C + TwoBand.bareRotated n C := by
  have h := CompactIndexedFlatten.flatten selectors copies (selectorOffset 4393)
    (selectorOffset 5495) (copyOffset pos 4393) (copyOffset pos 5495)
    TwoBand.bareOffset (fun x => rot 67 n C (x % n))
  simpa only [bandOffsets, rotatedBand, TwoBand.bareRotated, selectorCoeff, copyCoeff,
    selectors, copies] using h

#print axioms CompactTwoBandFlatten.exact_bands
end CompactTwoBandFlatten
