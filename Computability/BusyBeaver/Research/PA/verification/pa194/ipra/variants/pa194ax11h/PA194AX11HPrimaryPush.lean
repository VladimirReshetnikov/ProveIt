import PA194AX11HPushCongruence
import PA194SourceControllerStep
import PA194MPLiteralRows3554
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HPrimaryPush
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceInstructionModel
open PA194AX11HRelocation PA194AX11HPushRows PA194AX11HPushCongruence PA194MPLiteralRows

/-- The pinned primary source's actual resolved instructions at its push block. -/
theorem primaryRows (i : Fin 19) :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie (3568+i.val)).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (oldPush.getD i.val .halt) := by
  fin_cases i
  · exact s3568
  · exact s3569
  · exact s3570
  · exact s3571
  · exact s3572
  · exact s3573
  · exact s3574
  · exact s3575
  · exact s3576
  · exact s3577
  · exact s3578
  · exact s3579
  · exact s3580
  · exact s3581
  · exact s3582
  · exact s3583
  · exact s3584
  · exact s3585
  · exact s3586

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- Actual primary source step versus the revised block's stated instruction:
    same file, and old resulting PC is revised PC plus 15. The revised
    instruction interpreter is explicit here, not yet the revised full source. -/
theorem primaryStep_matches (i : Fin 19) (s t : M)
    (hp : F pc ![s] = modelNumeral M (3568+i.val)) (hf : pi₂ s = pi₂ t) :
    related (F step ![s]) (instructionSem (some (newPush.getD i.val .halt)) t) := by
  have hi : 3568+i.val < 3673 := by have := i.isLt; omega
  rw [actualInstructionStep _ hi s hp,primaryRows]
  exact pushInstruction_files i s t hf

#print axioms primaryRows
#print axioms primaryStep_matches
end models
end PA194AX11HPrimaryPush
