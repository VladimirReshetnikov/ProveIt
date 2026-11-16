import PA194AX11HSource
import PA194SourceControllerBinding
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HSharedRows
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SourceControllerBinding PA194AX11HSource PA194FiniteControls

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- Equal source rows give identical source steps in every model, at a standard site. -/
theorem same_step_of_row (i : Nat) (hi : i < 3671) (s : M)
    (hs : F pc ![s] = modelNumeral M i)
    (hrow : PA194AX11HSource.program[i]'(by rw [PA194AX11HSource.program_length]; exact hi) =
      ((M6.Source.PathTrie.nthSite PA194.SourceTree.trie i).bind
        (M6.FastResolve.resolveTree PA194.SourceTree.trie))) :
    F PA194AX11HSource.step ![s] = F PA194SourceControllerCode.step ![s] := by
  rw [PA194AX11HSource.selected i hi s hs, selectActual i (by omega) s hs, hrow, PA194SourceInstructionModel.instructionModel]

#print axioms same_step_of_row
end models
end PA194AX11HSharedRows
