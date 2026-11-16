import PA194AX11HPrepSemantics
import PA194MPLiteralRows3594
import PA194MPLiteralRows3621
import PA194MPLiteralRows3554
import PA194SourceControllerBinding
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HPrepSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceInstructionModel PA194SourceControllerCode PA194SourceControllerBinding PA194FiniteControls
open PA194AX11HPrepRows PA194AX11HPrepSemantics PA194AX11HFieldSemantics PA194MPLiteralRows

theorem primaryRows (i : Fin 37) :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie (3587+i.val)).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (oldPrep.getD i.val .halt) := by
  fin_cases i
  · exact s3587
  · exact s3588
  · exact s3589
  · exact s3590
  · exact s3591
  · exact s3592
  · exact s3593
  · exact s3594
  · exact s3595
  · exact s3596
  · exact s3597
  · exact s3598
  · exact s3599
  · exact s3600
  · exact s3601
  · exact s3602
  · exact s3603
  · exact s3604
  · exact s3605
  · exact s3606
  · exact s3607
  · exact s3608
  · exact s3609
  · exact s3610
  · exact s3611
  · exact s3612
  · exact s3613
  · exact s3614
  · exact s3615
  · exact s3616
  · exact s3617
  · exact s3618
  · exact s3619
  · exact s3620
  · exact s3621
  · exact s3622
  · exact s3623

theorem candidateRows (i : Fin 37) :
    PA194AX11HSource.program[3605+i.val]'(by rw [PA194AX11HSource.program_length]; have := i.isLt; omega) =
      some (newPrep.getD i.val .halt) := by
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

theorem prep_step_matches (i : Fin 37) (old revised : M)
    (ho : F pc ![old] = modelNumeral M (3587+i.val))
    (hn : F pc ![revised] = modelNumeral M (3605+i.val))
    (hf : pi₂ old = pi₂ revised) :
    related (F PA194SourceControllerCode.step ![old]) (F PA194AX11HSource.step ![revised]) := by
  rw [selectActual _ (by have := i.isLt; omega) old ho, instructionModel, primaryRows,
    PA194AX11HSource.selected _ (by have := i.isLt; omega) revised hn, candidateRows]
  exact prepInstruction_files i old revised hf

#print axioms primaryRows
#print axioms candidateRows
#print axioms prep_step_matches
end models
end PA194AX11HPrepSource
