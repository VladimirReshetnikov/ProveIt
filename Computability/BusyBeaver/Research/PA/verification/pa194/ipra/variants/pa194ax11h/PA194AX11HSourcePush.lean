import PA194AX11HSource
import PA194AX11HPrimaryPush
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HSourcePush
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194AX11HSource PA194AX11HPushRows PA194AX11HRelocation PA194AX11HPrimaryPush
open PA194SourceControllerCode

theorem block_record (i : Fin 19) :
    PA194AX11HSource.program[3553+i.val]'(by rw [program_length]; have := i.isLt; omega) =
      some (newPush.getD i.val .halt) := by
  unfold PA194AX11HSource.program
  rw [List.getElem_append_left (by simp only [List.length_append,List.length_map,beforePush_length,push_length]; have := i.isLt; omega)]
  rw [List.getElem_append_right (by rw [beforePush_length]; omega)]
  simp only [beforePush_length,Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simpa [push_length] using i.isLt)]
  simp only [List.getElem_map]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- On the inserted push block, the candidate full revised-source code and
    the actual primary full-source code make matching file updates under the
    exact offset-15 relocation. -/
theorem full_step_matches (i : Fin 19) (old revised : M)
    (ho : F pc ![old] = modelNumeral M (3568+i.val))
    (hn : F pc ![revised] = modelNumeral M (3553+i.val))
    (hf : pi₂ old = pi₂ revised) :
    related (F PA194SourceControllerCode.step ![old]) (F PA194AX11HSource.step ![revised]) := by
  have hi : 3553+i.val < 3671 := by have := i.isLt; omega
  rw [PA194AX11HSource.selected _ hi revised hn,block_record]
  exact primaryStep_matches i old revised ho hf

#print axioms block_record
#print axioms full_step_matches
end models
end PA194AX11HSourcePush
