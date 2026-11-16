import PA194TrieSourceController
import PA194LCBBoxAgreement
import PA194LCBPhysical

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194LCBController
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open M6.Runtime
open ConPA.Machine ConPA.Machine.Compressed
open PA194SourceControllerCode PA194CompressedSourceArgs PA194CompressedBoxFiles
open PA194CompressedBoxOracle PA194CompressedIncrementOracle PA194CompressedStartup
open PA194FiniteControls PA194StateOne

private theorem path_short (i : Nat) : (PA194LCBData.path i).length ≤ 48 :=
  PA194TrieRoot.path_short PA194LCBData.sourceTrie (by decide +kernel) i

private theorem haltCheck : PA194LCBChecks.haltContract 10 512 = true := by decide +kernel

def data : PA194TrieSourceController.Data where
  table := PA194LCBData.table
  machine := PA194LCBData.machine
  label := PA194LCBData.denseControl
  path := PA194LCBData.path
  codeAt := PA194LCBData.codeAt
  rows := PA194LCBRows.rowAgreement
  rootControl := PA194LCBPhysical.rootControl
  haltControl := PA194LCBPhysical.haltControl
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
  exact PA194LCBBoxAgreement.concreteBoxAgreement (tapeArgs s count spare) count br
    (readTail s count spare) hbranch

theorem halt_absorbs (y : M) (h : π₁ y = (194 : M)) : step PA194LCBData.table y = y := by
  have he : y = PA194BModelSteps.config 194 (π₁ (π₂ y)) (π₂ (π₂ y)) := by
    unfold PA194BModelSteps.config
    change π₁ y = ((194 : Nat) : M) at h
    rw [← h,pair_unpair,pair_unpair]
  conv_lhs => rw [he]
  rw [PA194LCBData.table, PA194BModelSteps.halted PA194LCBData.rows PA194LCBPhysical.rowCount, ← he]

/-- Conditional only on the finite site checks and exact modeled startup. -/
theorem halt_iff_controller
    (checks : PA194TrieSourceController.AllContracts data) (startup : M)
    (initial : ConPA.Machine.run PA194LCBData.table startup =
      F (PA194TrieSourceController.sourceRootCode data) ![initialSource,0,modelNumeral M 25,initialSpare]) :
    (∃ t : M, π₁ (ConPA.Machine.run PA194LCBData.table t) = (194 : M)) ↔
      ∃ n : M, F pc ![F run ![n,initialSource]] = modelNumeral M 3674 :=
  PA194TrieSourceController.halt_iff_controller data checks (literalBoxes initialSpare) startup initial halt_absorbs

#print axioms path_short
#print axioms haltCheck
#print axioms literalBoxes
#print axioms halt_absorbs
#print axioms halt_iff_controller
end models
end PA194LCBController
