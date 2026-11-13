import CompactWordRankStaticFields
import CompactHaltPackedWord

/-! Specialize chosen rank to the actual model-halt-derived compact word. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactHaltRankStaticFields
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticPow ArithmeticPackingBlocks ArithmeticPacking
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open CompactWordLowFields CompactCanonicalPerturbation CompactRankVariation
open CompactWordRankFourFields CompactWordRankStaticFields CompactHaltPackedWord
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] paramKernel rho highNat

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The halt hypothesis is internal to the model. The four remaining
physical block fields are still assumed for the base word, and uniformly
for every admissible definable Boolean perturbation. -/
theorem halt_chosen_rank (T c : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0)
    (hbase : ResidualBlockFields 590069 (paramKernel rho : V) (highNat : V)
      (haltLength T) (haltStride T) (baseCell (haltRow T)))
    (hblocks : ∀ δ : V → V, (𝚺₁-Function₁ δ) → (∀ j, δ j ≤ 1) →
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < haltLength T ∧
        j + haltStride T < haltLength T) →
      ResidualBlockFields 590069 (paramKernel rho : V) (highNat : V)
        (haltLength T) (haltStride T) (perturb (baseCell (haltRow T)) δ)) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < haltLength T ∧
        j + haltStride T < haltLength T) ∧
      PackingInput 590069 (paramKernel rho : V) CompactConcreteIncrement.mask (highNat : V)
        (haltLength T) (haltStride T) (perturb (baseCell (haltRow T)) δ) ∧
      windowRank (paramKernel rho : V) (haltLength T) (haltStride T) c
        (perturb (baseCell (haltRow T)) δ) % (590069 * haltLength T) =
        (590069 * haltStride T) % (590069 * haltLength T) := by
  letI : 𝚺₁-Function₁ (fun _ : V => (0 : V)) := by definability
  have h := halt_packed_word T (fun _ => 0) hT
  letI : 𝚺₁-Function₁ (haltRow T) := h.1
  have hw := h.2.1
  exact chosen_rank_static_fields T c (haltRow T) hw hbase hblocks

#print axioms CompactHaltRankStaticFields.halt_chosen_rank
end CompactHaltRankStaticFields
