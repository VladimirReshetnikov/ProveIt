import DiophantineConsistency.Compact44.CompactKernelBlockSize
import DiophantineConsistency.Compact44.CompactCanonicalPerturbation
import DiophantineConsistency.Compact44.CompactMarkedTransport

/-! Supply cell-sum bounds for the actual marked base and pulsed words. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactMarkedCellSum
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticPacking
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactPackedCell
open CompactCellSizeBound CompactCellProductBound CompactKernelBlockSize
open CompactCanonicalPerturbation CompactMarkedTransport
attribute [local irreducible] paramKernel rho
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- For each bounded row word, Boolean pulses preserve the small-cell size
needed for both base and perturbed transport-block size bounds. -/
theorem marked_cell_sums {N s : V} (row δ : V → V)
    (hw : CompactWord row N s) (hbool : ∀ j < N, δ j ≤ 1) :
    let X0 : V → V := fun j => packedCell (row j) 0
    (∀ j < N, X0 j + blk 590069 (paramKernel rho : V) N s X0 j < Exp.exp 590069) ∧
    (∀ j < N, perturb X0 δ j + blk 590069 (paramKernel rho : V) N s (perturb X0 δ) j < Exp.exp 590069) := by
  let X0 : V → V := fun j => packedCell (row j) 0
  have hbase : ∀ j < N, X0 j < Exp.exp (67*3297+1 : V) := by
    intro j hj
    have hs := packedCell_lt_support (row j) 0 (hw.tile_ne j hj) (by simp)
    exact lt_of_lt_of_le hs (exp_monotone_le.mpr (by norm_num))
  have hpulse : ∀ j < N, perturb X0 δ j < Exp.exp (67*3297+1 : V) := by
    intro j hj
    rcases le_one_iff_eq_zero_or_one.mp (hbool j hj) with hz | ho
    · simpa [perturb, hz] using hbase j hj
    · simpa [perturb, X0, ho] using cell_pulse_lt (row j) (hw.tile_ne j hj)
  exact ⟨cell_sum_of_small hw.pos hbase, cell_sum_of_small hw.pos hpulse⟩

#print axioms CompactMarkedCellSum.marked_cell_sums
end CompactMarkedCellSum
