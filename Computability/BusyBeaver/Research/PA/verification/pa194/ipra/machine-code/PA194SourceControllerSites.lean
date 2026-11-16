import PA194SourceControllerBinding
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194SourceControllerSites
open M6.Source M6.Source.PathTrie PA194.SourceTree PA194SourceControllerCode

theorem programLength : program.length = 3673 := by simp [program]
theorem site10Instruction : (nthSite trie 10).bind (M6.FastResolve.resolveTree trie) = some .halt := by
  decide +kernel
theorem site25Instruction : (nthSite trie 25).bind (M6.FastResolve.resolveTree trie) =
    some (.dec 8 (some 27) (some 26)) := by decide +kernel
section models
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open TableDispatch PA194SourceControllerBinding
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
theorem selectSite10 (s : M) (h : F pc ![s] = modelNumeral M 10) :
    F step ![s] = F (instruction (some .halt)) ![s] := by
  rw [selectActual 10 (by decide) s h, site10Instruction]
theorem selectSite25 (s : M) (h : F pc ![s] = modelNumeral M 25) :
    F step ![s] = F (instruction (some (.dec 8 (some 27) (some 26)))) ![s] := by
  rw [selectActual 25 (by decide) s h, site25Instruction]
#print axioms selectSite10
#print axioms selectSite25
end models
#print axioms programLength
#print axioms site10Instruction
#print axioms site25Instruction
end PA194SourceControllerSites
