import DiophantineConsistency.BFS943.DirectBFSConstructedWord
import DiophantineConsistency.Compact44.CompactCellPulseEquality
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSCellPulseEquality
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits
open DiophantineConsistency.ArithmeticPackingBlocks
open DirectBFSCellDigit DirectBFSCellDigitUniform DirectBFSPackedCell DirectBFSUniformPackedCell DirectBFSConstructedWord
open CompactCellPulseEquality
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cell_one (a : V) : packedCell a 1 = packedCell a 0 + Exp.exp (67*1063) := by
  letI : 𝚺₁-Function₃ (cellDigit : V → V → V → V) := cellDigit_uniform
  haveI : 𝚺₁-Function₁ (cellDigit a (0:V)) := by definability
  haveI : 𝚺₁-Function₁ (cellDigit a (1:V)) := by definability
  unfold packedCell
  apply bsum_add_pt (w := (67:V)) (q := (1063:V)) (by norm_num) (by norm_num)
  · intro j _; exact cellDigit_le_one a 0 j (by simp)
  · exact dummy_digit a 0
  · intro j _
    by_cases hj : j = 1063
    · subst j
      simp [dummy_digit, pt]
    · have he : cellDigit a 1 j = cellDigit a 0 j := by simp [cellDigit, hj]
      simp [pt, hj, he]

theorem cell_pulse (row dummy : V → V) (j : V) (hd : dummy j ≤ 1) :
    cellWord row dummy j = cellWord row (fun _ => 0) j + Exp.exp (67*1063) * dummy j := by
  rcases le_one_iff_eq_zero_or_one.mp hd with h0 | h1
  · simp [cellWord, normalizedCell, h0]
  · simp [cellWord, normalizedCell, h1, cell_one]
#print axioms DirectBFSCellPulseEquality.cell_one
#print axioms DirectBFSCellPulseEquality.cell_pulse
end DirectBFSCellPulseEquality
