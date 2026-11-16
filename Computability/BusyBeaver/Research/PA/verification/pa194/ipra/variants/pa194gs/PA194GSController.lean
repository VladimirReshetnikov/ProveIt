import PA194GSChecks
import PA194GSBoxAgreement
import PA194GSModelStartup

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194GSController
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open ConPA.Machine ConPA.Machine.Compressed
open PA194SourceControllerCode (pc)
open PA194IteratedSimulation (iterate)
open PA194CompressedSourceArgs PA194CompressedStartup PA194FiniteControls
open PA194GSChecks (data)

theorem seedPath : PA194GSData.path 25 = PA194AX11HData.path 25 := by
  decide +kernel

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem literalBoxes (spare : M) : PA194TrieSourceController.Boxes data spare := by
  intro s count br hbranch
  exact PA194GSBoxAgreement.concreteBoxAgreement (tapeArgs s count spare) count br
    (readTail s count spare) hbranch

theorem halt_absorbs (y : M) (h : π₁ y = (194 : M)) : step PA194GSData.table y = y := by
  have he : y = PA194BModelSteps.config 194 (π₁ (π₂ y)) (π₂ (π₂ y)) := by
    unfold PA194BModelSteps.config
    change π₁ y = ((194 : Nat) : M) at h
    rw [← h, pair_unpair, pair_unpair]
  conv_lhs => rw [he]
  rw [PA194GSData.table, PA194BModelSteps.halted PA194GSData.rows PA194GSRows.rowCount, ← he]

theorem startup_root :
    ConPA.Machine.run (V := M) PA194GSData.table (57922 : M) =
      F (PA194TrieSourceController.sourceRootCode data) ![initialSource,0,modelNumeral M 25,initialSpare] :=
  PA194AX11HSharedController.startup_root_of_same_seed data 57922 seedPath
    PA194GSModelStartup.modeledStartup

theorem halt_iff_site10 (checks : PA194AX11HSharedController.AllContracts data) :
    (∃ t : M, π₁ (ConPA.Machine.run PA194GSData.table t) = (194 : M)) ↔
      ∃ n : M, F pc ![F (iterate PA194AX11HSource.step) ![n,initialSource]] = modelNumeral M 10 :=
  PA194AX11HSharedController.halt_iff_site10 data checks (literalBoxes initialSpare)
    57922 startup_root halt_absorbs

#print axioms startup_root
#print axioms halt_iff_site10
end models
end PA194GSController
