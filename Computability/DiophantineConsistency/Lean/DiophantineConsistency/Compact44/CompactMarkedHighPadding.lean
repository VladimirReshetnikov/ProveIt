import DiophantineConsistency.Compact44.CompactHighPaddingSize
import DiophantineConsistency.Compact44.CompactCellPulseEquality
import DiophantineConsistency.Compact44.CompactCanonicalPerturbation
import DiophantineConsistency.Compact44.CompactMarkedTransport

/-! The actual marked base and Boolean-pulsed words have no padding digits
in their normalized transport blocks. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactMarkedHighPadding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticPacking
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactPackedCell
open CompactCellPulseEquality CompactCanonicalPerturbation CompactMarkedTransport CompactHighPaddingSize
attribute [local irreducible] paramKernel rho
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem digits_clear (z p : V) (hz : z < Exp.exp (67*8792 : V)) (hp : 8792 ≤ p) :
    dig 67 z p = 0 := by
  unfold dig
  have he : Exp.exp (67*8792 : V) ≤ Exp.exp (67*p) :=
    exp_monotone_le.mpr (mul_le_mul_of_nonneg_left hp (by norm_num))
  rw [div_eq_zero_of_lt _ (lt_of_lt_of_le hz he)]
  simp

/-- All digits in the padded tail vanish for both the base and the
perturbed compact word, at every in-range cell. -/
theorem marked_padding {N s : V} (row δ : V → V)
    (hw : CompactWord row N s) (hbool : ∀ j < N, δ j ≤ 1) :
    let X0 : V → V := fun j => packedCell (row j) 0
    (∀ j < N, ∀ p, 8792 ≤ p →
      dig 67 (blk 590069 (paramKernel rho : V) N s X0 j) p = 0) ∧
    (∀ j < N, ∀ p, 8792 ≤ p →
      dig 67 (blk 590069 (paramKernel rho : V) N s (perturb X0 δ) j) p = 0) := by
  let X0 : V → V := fun j => packedCell (row j) 0
  have hbase : ∀ j < N, X0 j < Exp.exp (67*3296+1 : V) := by
    intro j hj
    exact sharp_cell (row j) 0 (hw.tile_ne j hj) (by simp)
  have hpulse : ∀ j < N, perturb X0 δ j < Exp.exp (67*3296+1 : V) := by
    intro j hj
    rcases le_one_iff_eq_zero_or_one.mp (hbool j hj) with hz | ho
    · simpa [perturb, hz] using hbase j hj
    · change packedCell (row j) 0 + Exp.exp (67*1063) * δ j < _
      rw [ho, mul_one, ← cell_one]
      exact sharp_cell (row j) 1 (hw.tile_ne j hj) (by simp)
  constructor
  · intro j hj p hp
    exact digits_clear _ _ (block_lt_padding hw.pos hbase j hj) hp
  · intro j hj p hp
    exact digits_clear _ _ (block_lt_padding hw.pos hpulse j hj) hp

#print axioms CompactMarkedHighPadding.digits_clear
#print axioms CompactMarkedHighPadding.marked_padding
end CompactMarkedHighPadding
