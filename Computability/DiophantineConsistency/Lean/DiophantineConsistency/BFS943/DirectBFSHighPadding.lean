import DiophantineConsistency.BFS943.DirectBFSHighPaddingSize
import DiophantineConsistency.BFS943.DirectBFSConstructedWord
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSHighPadding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticPacking
open CompactSymbolicKernel DirectBFSSymbolicKernel DirectBFSConstructedWord DirectBFSHighPaddingSize
attribute [local irreducible] paramKernel rho
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem digits_clear (z p : V) (hz : z<Exp.exp (67*8792:V)) (hp : 8792≤p) : dig 67 z p=0 := by
  unfold dig
  have he : Exp.exp (67*8792:V)≤Exp.exp (67*p) :=
    exp_monotone_le.mpr (mul_le_mul_of_nonneg_left hp (by norm_num))
  rw [div_eq_zero_of_lt _ (lt_of_lt_of_le hz he)]
  simp

theorem word_padding (row dummy : V → V) {N s : V} (hw : DirectBFSLocalWord.Word row N s) :
    ∀ j<N, ∀ p, 8792≤p → dig 67 (blk 590069 (paramKernel rho:V) N s (cellWord row dummy) j) p=0 := by
  have hsmall : ∀ j<N, cellWord row dummy j<Exp.exp (67*3296+1:V) := by
    intro j hj
    have hd : dummy j%2≤1 := lt_two_iff_le_one.mp (mod_lt _ (by norm_num))
    exact sharp_cell (row j) (dummy j%2) (hw.tile_ne j hj) hd
  intro j hj p hp
  exact digits_clear _ _ (block_lt_padding hw.pos hsmall j hj) hp
#print axioms DirectBFSHighPadding.digits_clear
#print axioms DirectBFSHighPadding.word_padding
end DirectBFSHighPadding
