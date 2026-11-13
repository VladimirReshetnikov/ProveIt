import DiophantineConsistency.Compact44.CompactConstructedWord
import DiophantineConsistency.Compact44.CompactCellDigitSupported
import DiophantineConsistency.Compact44.CleanMaskClasses

/-! The constructed marked word has no digits outside the coarse Bad set. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactWordCleanSupport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticWindowDigits
open CompactCellDigit CompactCellDigitSupported CompactConstructedWord CompactMarkedTransport
open CleanGeometry CleanMaskClasses
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cell_outside_bad (a d p : V) (ha : a ≠ 1) (hp : p < 8807)
    (hbad : ¬ Bad p) : cellDigit a d p = 0 := by
  by_contra hn
  obtain ⟨n, he, hs⟩ := cellDigit_supported a d p ha hp hn
  have hb : Bad (n : V) := (bad_cast n).2 (support_subset_bad n hs)
  apply hbad
  rw [he]
  exact hb

/-- No low-mask premise is used; support follows from the constructed digits. -/
theorem word_outside_bad (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s : V} (hw : CompactWord row N s) (k : V) (hk : k < 8807*N)
    (hbad : ¬ Bad (k%8807)) : dig 67 (packedWord row dummy N) k = 0 := by
  have hj : k/8807 < N := div_lt_of_lt_mul (by simpa only [mul_comm] using hk)
  have hp : k%8807 < 8807 := mod_lt k (by norm_num)
  have he : 8807*(k/8807)+k%8807 = k := div_add_mod k 8807
  rw [← he, word_digit row dummy N _ _ hj hp]
  exact cell_outside_bad (row (k/8807)) (dummy (k/8807)%2) _ (hw.tile_ne _ hj) hp hbad

#print axioms CompactWordCleanSupport.cell_outside_bad
#print axioms CompactWordCleanSupport.word_outside_bad
end CompactWordCleanSupport
