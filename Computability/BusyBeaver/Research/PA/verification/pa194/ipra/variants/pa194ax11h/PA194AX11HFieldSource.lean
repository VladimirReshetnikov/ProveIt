import PA194AX11HFieldSemantics
import PA194MPLiteralRows3554
import PA194SourceControllerBinding
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HFieldSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceInstructionModel PA194SourceControllerCode PA194SourceControllerBinding PA194FiniteControls
open PA194AX11HFieldRows PA194AX11HFieldSemantics PA194MPLiteralRows

theorem primaryRows (i : Fin 14) :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie (3554+i.val)).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (oldField.getD i.val .halt) := by
  fin_cases i
  · exact s3554
  · exact s3555
  · exact s3556
  · exact s3557
  · exact s3558
  · exact s3559
  · exact s3560
  · exact s3561
  · exact s3562
  · exact s3563
  · exact s3564
  · exact s3565
  · exact s3566
  · exact s3567

theorem candidateRows (i : Fin 14) :
    PA194AX11HSource.program[3572+i.val]'(by rw [PA194AX11HSource.program_length]; have := i.isLt; omega) =
      some (newField.getD i.val .halt) := by
  unfold PA194AX11HSource.program
  rw [List.getElem_append_right (by simp only [List.length_append,List.length_map,PA194AX11HSource.beforePush_length,PA194AX11HSource.push_length]; have := i.isLt; omega)]
  simp only [List.length_append,List.length_map,PA194AX11HSource.beforePush_length,PA194AX11HSource.push_length]
  fin_cases i <;> rfl

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem field_step_matches (i : Fin 14) (old revised : M)
    (ho : F pc ![old] = modelNumeral M (3554+i.val))
    (hn : F pc ![revised] = modelNumeral M (3572+i.val))
    (hf : pi₂ old = pi₂ revised) :
    related (F PA194SourceControllerCode.step ![old]) (F PA194AX11HSource.step ![revised]) := by
  rw [selectActual _ (by have := i.isLt; omega) old ho, instructionModel, primaryRows,
    PA194AX11HSource.selected _ (by have := i.isLt; omega) revised hn, candidateRows]
  exact fieldInstruction_files i old revised hf

#print axioms primaryRows
#print axioms candidateRows
#print axioms field_step_matches
end models
end PA194AX11HFieldSource
