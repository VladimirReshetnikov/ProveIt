import DiophantineConsistency.Compact44.CompactWordPackingFields
import DiophantineConsistency.Compact44.CompactPulseChosenRankRetry

/-! Chosen calibrated rank for a constructed compact word, conditional on
the still-unproved product, block, high-mask and scalar bounds. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactWordChosenRank
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticPow ArithmeticPackingBlocks ArithmeticPacking
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactMarkedTransport
open CompactPackedCell CompactUniformPackedCell CompactBaseLowNoCarry CompactPulsePackedCell
open CompactWordLowFields CompactWordPackingFields CompactCanonicalPerturbation
open CompactPulseChosenRankRetry CompactRankVariation
attribute [local irreducible] paramKernel rho

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The base compact-cell function is uniformly model-definable in the row. -/
theorem baseCell_definable (row : V → V) [𝚺₁-Function₁ row] :
    𝚺₁-Function₁ (baseCell row) := by
  letI : 𝚺₁-Function₁ (fun _ : V => (0 : V)) := by definability
  have hd := word_definable row (fun _ => (0 : V))
  have he : (fun j => normalizedCell (row j) (0 : V)) = baseCell row := by
    funext j
    exact normalizedCell_eq (row j) 0 (by simp)
  rw [he] at hd
  exact hd

/-- Physical product/block hypotheses remain universal for every admissible
controller selector. This theorem supplies the low-mask and origin fields. -/
theorem chosen_rank_of_word (T HP c : V) (row : V → V) [𝚺₁-Function₁ row]
    (hw : CompactWord row (power 581197 ((2*T+3)+1)) (power 581197 (T+1)))
    (hN : 1 < power 581197 ((2*T+3)+1))
    (hs : power 581197 (T+1) < power 581197 ((2*T+3)+1))
    (hMC : (CompactConcreteIncrement.mask : V) + 1 < Exp.exp 590069)
    (hHPpos : 1 ≤ HP) (hHPlt : HP < Exp.exp 590069)
    (hbase : TransportFields 590069 (paramKernel rho : V) HP
      (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) (baseCell row))
    (hblocks : ∀ δ : V → V, (𝚺₁-Function₁ δ) → (∀ j, δ j ≤ 1) →
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 581197 ((2*T+3)+1) ∧
        j + power 581197 (T+1) < power 581197 ((2*T+3)+1)) →
      ProductBlockInput 590069 (paramKernel rho : V) HP
        (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) (perturb (baseCell row) δ)) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 581197 ((2*T+3)+1) ∧
        j + power 581197 (T+1) < power 581197 ((2*T+3)+1)) ∧
      PackingInput 590069 (paramKernel rho : V) CompactConcreteIncrement.mask HP
        (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) (perturb (baseCell row) δ) ∧
      windowRank (paramKernel rho : V) (power 581197 ((2*T+3)+1))
        (power 581197 (T+1)) c (perturb (baseCell row) δ) %
          (590069 * power 581197 ((2*T+3)+1)) =
        (590069 * power 581197 (T+1)) % (590069 * power 581197 ((2*T+3)+1)) := by
  letI : 𝚺₁-Function₁ (baseCell row) := baseCell_definable row
  obtain ⟨ho, hlo, hlow⟩ := base_low_fields hw
  have h0 : PackingInput 590069 (paramKernel rho : V) CompactConcreteIncrement.mask HP
      (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) (baseCell row) :=
    ⟨hN, hs, hbase.hi_lt, hMC, hHPpos, hHPlt, hbase.cell_sum, ho,
      hbase.blk_pos, hlo, fun j hj _ => hlow j hj, hbase.high_origin, hbase.high⟩
  have hpulse : ∀ j < power 581197 ((2*T+3)+1), 0 < j →
      NoCarry (baseCell row j + Exp.exp (67*1063)) CompactConcreteIncrement.mask := by
    intro j hj _
    exact packedCell_pulse_noCarry (row j) (hlow j hj)
  exact chosen_rank_of_pulse T CompactConcreteIncrement.mask HP c h0 hpulse hblocks

#print axioms CompactWordChosenRank.baseCell_definable
#print axioms CompactWordChosenRank.chosen_rank_of_word
end CompactWordChosenRank
