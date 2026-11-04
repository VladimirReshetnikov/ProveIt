import DiophantineConsistency.Compact44.CompactHaltRankStaticFields
import DiophantineConsistency.Compact44.CompactWordBlockPositivity

/-! Remove origin-block positivity from the conditional halt/rank bridge. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactHaltRankThreeFields
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticPow ArithmeticPackingBlocks ArithmeticPacking
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open CompactWordLowFields CompactCanonicalPerturbation CompactRankVariation
open CompactWordRankFourFields CompactHaltPackedWord CompactHaltRankStaticFields
open CompactWordBlockPositivity
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] paramKernel rho highNat

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The remaining size and high-mask fields for one cell family. -/
structure ThreeBlockFields (d K HP N s : V) (X : V → V) : Prop where
  cell_sum : ∀ j < N, X j + blk d K N s X j < Exp.exp d
  high_origin : NoCarry (blk d K N s X 0) (HP - 1)
  high : ∀ j < N, 0 < j → NoCarry (blk d K N s X j) HP

/-- Origin-block positivity follows from the halt-derived word. The three
remaining physical fields are retained for the base family and uniformly
over all admissible definable Boolean perturbations. -/
theorem halt_chosen_rank_three_fields (T c : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0)
    (hbase : ThreeBlockFields 590069 (paramKernel rho : V) (highNat : V)
      (haltLength T) (haltStride T) (baseCell (haltRow T)))
    (hblocks : ∀ δ : V → V, (𝚺₁-Function₁ δ) → (∀ j, δ j ≤ 1) →
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < haltLength T ∧
        j + haltStride T < haltLength T) →
      ThreeBlockFields 590069 (paramKernel rho : V) (highNat : V)
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
  have hb : ResidualBlockFields 590069 (paramKernel rho : V) (highNat : V)
      (haltLength T) (haltStride T) (baseCell (haltRow T)) :=
    ⟨hbase.cell_sum, (block_pos (δ := fun _ => 0) hw 0).1, hbase.high_origin, hbase.high⟩
  have hp : ∀ δ : V → V, (𝚺₁-Function₁ δ) → (∀ j, δ j ≤ 1) →
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < haltLength T ∧
        j + haltStride T < haltLength T) →
      ResidualBlockFields 590069 (paramKernel rho : V) (highNat : V)
        (haltLength T) (haltStride T) (perturb (baseCell (haltRow T)) δ) := by
    intro δ hd hbool hsupport
    have h := hblocks δ hd hbool hsupport
    exact ⟨h.cell_sum, (block_pos (δ := δ) hw 0).2, h.high_origin, h.high⟩
  exact halt_chosen_rank T c hT hb hp

#print axioms CompactHaltRankThreeFields.halt_chosen_rank_three_fields
end CompactHaltRankThreeFields
