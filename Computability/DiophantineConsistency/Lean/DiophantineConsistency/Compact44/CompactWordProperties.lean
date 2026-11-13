import DiophantineConsistency.Compact44.CompactConstructedWord

/-! Global digit cap and marked origin for the constructed compact word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactWordProperties
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits
open DiophantineConsistency.ArithmeticPackingBlocks
open CompactForwardCellInputs CompactWordCellClient CompactMarkedTransport
open CompactConstructedWord CompactUniformPackedCell
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem word_definable_length (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy] :
    𝚺₁-Function₁ (packedWord row dummy) := by
  apply bsum_definable
  exact word_cell_lt row dummy

theorem word_cap (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N k : V) (hk : k < 8807*N) : dig 67 (packedWord row dummy N) k ≤ 1 := by
  have hj : k/8807 < N := div_lt_of_lt_mul (by simpa only [mul_comm] using hk)
  have hp : k%8807 < 8807 := mod_lt k (by norm_num)
  have he : 8807*(k/8807)+k%8807 = k := div_add_mod k 8807
  rw [← he]
  exact word_digit_cap row dummy N _ _ hj hp

theorem marked_word_origin (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N s : V) (hword : CompactWord row N s) : 1 ≤ packedWord row dummy N := by
  have h := word_selector row dummy N 0 hword.pos ⟨0, by decide⟩
  have hzero : dig 67 (packedWord row dummy N) 0 = 1 := by
    simpa [wordSelector, selector, hword.marker] using h
  rw [dig_zero_index] at hzero
  rw [← hzero]
  exact mod_le _ _

#print axioms CompactWordProperties.word_definable_length
#print axioms CompactWordProperties.word_cap
#print axioms CompactWordProperties.marked_word_origin
end CompactWordProperties
