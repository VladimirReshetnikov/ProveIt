import DiophantineConsistency.Compact44.CompactTwoBandFlatten
import DiophantineConsistency.Compact44.GenericBandCarryFamily
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Compact943Data.rows
attribute [local irreducible] CompactConcreteIndexedMass.selectors CompactConcreteIndexedMass.copies
noncomputable section
namespace CompactTwoBandCarry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticCyclicWord ArithmeticWindowDigits CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
open CompactPartialBandRotation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem carry_input (pos : Fin 41 → ℕ) (n C T F : V)
    (hn : 0<n) (hM : 0<Exp.exp (67*n)-1)
    (hC : C<Exp.exp (67*n)) (hCcap : ∀ k<n, dig 67 C k≤3)
    (hT : T<Exp.exp (67*n)) (hTcap : ∀ k<n, dig 67 T k≤Exp.exp 67-1)
    (hF : F<Exp.exp (67*n)-1)
    (hgraph : ((rotatedBand pos 4393 n C + rotatedBand pos 5495 n C +
       TwoBand.bareRotated n C)+T) % (Exp.exp (67*n)-1)=F) :
    CarryInput 67 n F 1 (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41)))
      (GenericBandCarryFamily.coefficient (fun x => (alignedCoeff selectors copies x : V)))
      (GenericBandCarryFamily.word n C (bandOffsets pos) T) := by
  apply GenericBandCarryFamily.carry_input n C T F 1
    (fun x : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies x : V))
    (bandOffsets pos) hn hM hC hCcap hT hTcap hF
  · simpa only [exact_bands] using hgraph
  · exact CompactConcreteIndexedModel.concrete_family_mass_b1

#print axioms CompactTwoBandCarry.carry_input
end CompactTwoBandCarry
