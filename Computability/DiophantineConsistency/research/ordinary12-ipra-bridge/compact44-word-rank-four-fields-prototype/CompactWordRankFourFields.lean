import CompactWordChosenRank
import CompactCellProductBound

/-! The actual compact-cell product bounds remove both hi_lt assumptions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactWordRankFourFields
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticPow ArithmeticPackingBlocks ArithmeticPacking
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactMarkedTransport
open CompactWordLowFields CompactWordPackingFields CompactCanonicalPerturbation
open CompactPulseChosenRankRetry CompactRankVariation CompactWordChosenRank CompactCellProductBound
attribute [local irreducible] paramKernel rho

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Remaining non-size obligations, for a particular cell family. -/
structure ResidualBlockFields (d K HP N s : V) (X : V → V) : Prop where
  cell_sum : ∀ j < N, X j + blk d K N s X j < Exp.exp d
  blk_pos : 0 < blk d K N s X 0
  high_origin : NoCarry (blk d K N s X 0) (HP - 1)
  high : ∀ j < N, 0 < j → NoCarry (blk d K N s X j) HP

/-- The chosen-rank theorem with actual product bounds discharged. Its
remaining pulsed block obligations are uniform in the admissible selector. -/
theorem chosen_rank_four_fields (T HP c : V) (row : V → V) [𝚺₁-Function₁ row]
    (hw : CompactWord row (power 581197 ((2*T+3)+1)) (power 581197 (T+1)))
    (hN : 1 < power 581197 ((2*T+3)+1))
    (hs : power 581197 (T+1) < power 581197 ((2*T+3)+1))
    (hMC : (CompactConcreteIncrement.mask : V) + 1 < Exp.exp 590069)
    (hHPpos : 1 ≤ HP) (hHPlt : HP < Exp.exp 590069)
    (hbase : ResidualBlockFields 590069 (paramKernel rho : V) HP
      (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) (baseCell row))
    (hblocks : ∀ δ : V → V, (𝚺₁-Function₁ δ) → (∀ j, δ j ≤ 1) →
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 581197 ((2*T+3)+1) ∧
        j + power 581197 (T+1) < power 581197 ((2*T+3)+1)) →
      ResidualBlockFields 590069 (paramKernel rho : V) HP
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
  have hbase' : TransportFields 590069 (paramKernel rho : V) HP
      (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) (baseCell row) := by
    refine ⟨?_, hbase.cell_sum, hbase.blk_pos, hbase.high_origin, hbase.high⟩
    intro j hj
    exact packed_cell_product_lt (row j) 0 (hw.tile_ne j hj) (by simp)
  have hblocks' : ∀ δ : V → V, (𝚺₁-Function₁ δ) → (∀ j, δ j ≤ 1) →
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 581197 ((2*T+3)+1) ∧
        j + power 581197 (T+1) < power 581197 ((2*T+3)+1)) →
      ProductBlockInput 590069 (paramKernel rho : V) HP
        (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) (perturb (baseCell row) δ) := by
    intro δ hd hb hs'
    have h := hblocks δ hd hb hs'
    refine ⟨?_, h.cell_sum, h.blk_pos, h.high_origin, h.high⟩
    intro j hj
    rcases le_one_iff_eq_zero_or_one.mp (hb j) with hz | ho
    · simpa only [perturb, baseCell, hz, mul_zero, add_zero] using
        (packed_cell_product_lt (row j) 0 (hw.tile_ne j hj) (by simp))
    · simpa only [perturb, baseCell, ho, mul_one] using
        (packed_pulse_product_lt (row j) (hw.tile_ne j hj))
  exact chosen_rank_of_word T HP c row hw hN hs hMC hHPpos hHPlt hbase' hblocks'

#print axioms CompactWordRankFourFields.chosen_rank_four_fields
end CompactWordRankFourFields
