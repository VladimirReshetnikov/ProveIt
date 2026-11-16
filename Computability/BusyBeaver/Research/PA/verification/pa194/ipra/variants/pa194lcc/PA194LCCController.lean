import PA194TrieSourceController
import PA194LCCBoxAgreement
import PA194LCCPhysical

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194LCCController
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open M6.Runtime
open ConPA.Machine ConPA.Machine.Compressed
open PA194SourceControllerCode PA194CompressedSourceArgs PA194CompressedBoxFiles
open PA194CompressedBoxOracle PA194CompressedIncrementOracle PA194CompressedStartup
open PA194FiniteControls PA194StateOne

private theorem path_short (i : Nat) : (PA194LCCData.path i).length ≤ 48 :=
  PA194TrieRoot.path_short PA194LCCData.sourceTrie (by decide +kernel) i

private theorem haltCheck : PA194LCCChecks.haltContract 10 512 = true := by decide +kernel

def data : PA194TrieSourceController.Data where
  table := PA194LCCData.table
  machine := PA194LCCData.machine
  label := PA194LCCData.denseControl
  path := PA194LCCData.path
  codeAt := PA194LCCData.codeAt
  rows := PA194LCCRows.rowAgreement
  rootControl := PA194LCCPhysical.rootControl
  haltControl := PA194LCCPhysical.haltControl
  pathShort := path_short
  haltCheck := haltCheck

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
  exact PA194LCCBoxAgreement.concreteBoxAgreement (tapeArgs s count spare) count br
    (readTail s count spare) hbranch

theorem halt_absorbs (y : M) (h : π₁ y = (194 : M)) : step PA194LCCData.table y = y := by
  have he : y = PA194BModelSteps.config 194 (π₁ (π₂ y)) (π₂ (π₂ y)) := by
    unfold PA194BModelSteps.config
    change π₁ y = ((194 : Nat) : M) at h
    rw [← h,pair_unpair,pair_unpair]
  conv_lhs => rw [he]
  rw [PA194LCCData.table, PA194BModelSteps.halted PA194LCCData.rows PA194LCCPhysical.rowCount, ← he]

/-- Conditional only on the finite site checks and exact modeled startup. -/
theorem halt_iff_controller
    (checks : PA194TrieSourceController.AllContracts data) (startup : M)
    (initial : ConPA.Machine.run PA194LCCData.table startup =
      F (PA194TrieSourceController.sourceRootCode data) ![initialSource,0,modelNumeral M 25,initialSpare]) :
    (∃ t : M, π₁ (ConPA.Machine.run PA194LCCData.table t) = (194 : M)) ↔
      ∃ n : M, F pc ![F run ![n,initialSource]] = modelNumeral M 3674 :=
  PA194TrieSourceController.halt_iff_controller data checks (literalBoxes initialSpare) startup initial halt_absorbs

#print axioms path_short
#print axioms haltCheck
#print axioms literalBoxes
#print axioms halt_absorbs
#print axioms halt_iff_controller
end models
end PA194LCCController
