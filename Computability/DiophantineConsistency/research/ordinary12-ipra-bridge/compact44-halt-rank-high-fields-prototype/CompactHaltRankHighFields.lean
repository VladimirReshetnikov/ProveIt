import CompactHaltRankThreeFields
import CompactMarkedCellSum

/-! Reduce halt-to-calibrated-rank to the actual high-mask conditions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactHaltRankHighFields
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticPow ArithmeticPackingBlocks ArithmeticPacking
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open CompactWordLowFields CompactCanonicalPerturbation CompactRankVariation
open CompactHaltPackedWord CompactHaltRankThreeFields CompactMarkedCellSum
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] paramKernel rho highNat

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The origin and non-origin high-mask fields for one word. -/
structure HighMaskFields (d K HP N s : V) (X : V → V) : Prop where
  high_origin : NoCarry (blk d K N s X 0) (HP - 1)
  high : ∀ j < N, 0 < j → NoCarry (blk d K N s X j) HP

/-- The halt-derived word has all packing size and low-mask fields. The two
high-mask fields still remain explicit for the base word and universally for
every admissible definable Boolean perturbation. -/
theorem halt_chosen_rank_high_fields (T c : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0)
    (hbase : HighMaskFields 590069 (paramKernel rho : V) (highNat : V)
      (haltLength T) (haltStride T) (baseCell (haltRow T)))
    (hblocks : ∀ δ : V → V, (𝚺₁-Function₁ δ) → (∀ j, δ j ≤ 1) →
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < haltLength T ∧
        j + haltStride T < haltLength T) →
      HighMaskFields 590069 (paramKernel rho : V) (highNat : V)
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
  have hw := (halt_packed_word T (fun _ => 0) hT).2.1
  have hsum := marked_cell_sums (haltRow T) (fun _ => 0) hw (by intros; simp)
  have hb : ThreeBlockFields 590069 (paramKernel rho : V) (highNat : V)
      (haltLength T) (haltStride T) (baseCell (haltRow T)) :=
    ⟨hsum.1, hbase.high_origin, hbase.high⟩
  have hp : ∀ δ : V → V, (𝚺₁-Function₁ δ) → (∀ j, δ j ≤ 1) →
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < haltLength T ∧
        j + haltStride T < haltLength T) →
      ThreeBlockFields 590069 (paramKernel rho : V) (highNat : V)
        (haltLength T) (haltStride T) (perturb (baseCell (haltRow T)) δ) := by
    intro δ hd hbool hsupport
    have h := hblocks δ hd hbool hsupport
    have hsumδ := marked_cell_sums (haltRow T) δ hw (fun j _ => hbool j)
    exact ⟨hsumδ.2, h.high_origin, h.high⟩
  exact halt_chosen_rank_three_fields T c hT hb hp

#print axioms CompactHaltRankHighFields.halt_chosen_rank_high_fields
end CompactHaltRankHighFields
