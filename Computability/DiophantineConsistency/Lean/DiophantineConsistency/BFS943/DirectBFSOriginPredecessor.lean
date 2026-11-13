import DiophantineConsistency.BFS943.DirectBFSModelWordTransfer
import DiophantineConsistency.BFS943.DirectBFSPackedCell
import DiophantineConsistency.Compact44.OldWordIdentification
import DiophantineConsistency.Compact44.CompactOriginPredecessor
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSOriginPredecessor
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticStandardCasts
open CompactForwardCellInputs DirectBFSPackedCell
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem predecessor_ne_marker {row : V → V} {N s : V} (hw : DirectBFSLocalWord.Word row N s)
    (hs : 0<s) (hsN : s<N) : row (cyc N 0 s)≠0 := by
  have ho := DirectBFSModelWordTransfer.transfer row N s hw
  have hc := OldWordIdentificationDraft.local_to_old ho
  have hn := CompactOriginPredecessor.predecessor_ne_marker hc hs hsN
  intro h
  apply hn
  rw [h,DirectBFSModelIndexMap.back_zero]

theorem cell_mod_four (a d : V) (ha : a≠0) (hd : d≤1) : packedCell a d%4=0 := by
  have hs := packedCell_selector a d hd ⟨0,by decide⟩
  have hz : dig 67 (packedCell a d) 0=0 := by simpa [selector,ha] using hs
  rw [dig_zero_index] at hz
  have hdiv : (4:V) ∣ Exp.exp 67 := by
    have he : Exp.exp (67:V)=(4:V)*Exp.exp 65 := by
      have he2 : Exp.exp (2:V)=(4:V) := by simpa using cast_exp (V:=V) 2
      rw [←he2,←exp_add]
      norm_num
    rw [he]
    exact dvd_mul_right _ _
  have hmod := ArithmeticModularCancellation.mod_mod_of_dvd (by norm_num : (0:V)<4) hdiv (packedCell a d)
  rw [hz] at hmod
  simpa using hmod.symm
#print axioms DirectBFSOriginPredecessor.predecessor_ne_marker
#print axioms DirectBFSOriginPredecessor.cell_mod_four
end DirectBFSOriginPredecessor
