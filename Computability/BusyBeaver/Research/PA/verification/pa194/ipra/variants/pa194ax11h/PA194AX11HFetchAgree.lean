import PA194AX11HSource
import PA194PausedDrain
import PA194SourceControllerBinding
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
namespace PA194AX11HFetchAgree
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceControllerBinding PA194SourceFetchLoop PA194SchedulerFetchPositive
open PA194PausedDrain

/-- The revised source's first 48 instructions agree exactly with the
primary resolved trie, including all jump and branch targets. -/
theorem rows (i : Fin 48) :
    PA194AX11HSource.program[i.val]'(by rw [PA194AX11HSource.program_length]; have := i.isLt; omega) =
      (M6.Source.PathTrie.nthSite PA194.SourceTree.trie i.val).bind
        (M6.FastResolve.resolveTree PA194.SourceTree.trie) := by
  fin_cases i <;> decide +kernel

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- The actual source step agrees below site 48, for arbitrary model-valued
register files; this can drive the existing generic drain and reader. -/
theorem agrees : AgreesBelow (M := M) PA194AX11HSource.step 48 := by
  intro q hq a tail
  have hc : q < 3671 := by omega
  have hp : q < 3673 := by omega
  rw [PA194AX11HSource.selected q hc _ (statePC q a tail),
    actualInstructionStep q hp _ (statePC q a tail)]
  exact congrArg (fun ins => PA194SourceInstructionModel.instructionSem ins (sourceState q a tail)) (rows ⟨q,hq⟩)

#print axioms rows
#print axioms agrees
end models
end PA194AX11HFetchAgree
