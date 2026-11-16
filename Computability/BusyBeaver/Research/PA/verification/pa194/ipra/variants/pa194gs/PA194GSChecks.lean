import PA194GSRows
import PA194AX11HSharedController

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194GSChecks
open PA194GSData (table machine denseControl path codeAt sourceTrie)
open PA194TrieSourceController (Data)

def data : Data where
  table := table
  machine := machine
  label := denseControl
  path := path
  codeAt := codeAt
  rows := PA194GSRows.rowAgreement
  rootControl := PA194GSRows.rootControl
  haltControl := PA194GSRows.haltControl
  pathShort := PA194TrieRoot.path_short sourceTrie (by decide +kernel)
  haltCheck := by decide +kernel

abbrev checkAt := PA194AX11HSharedController.checkAt machine path codeAt
abbrev blockCheck := PA194SourceContracts.blockCheck checkAt

theorem block_sound {base count i : Nat} (h : blockCheck base count = true)
    (lo : base ≤ i) (hi : i < base + count) : checkAt i = true :=
  PA194SourceContracts.block_sound h lo hi

theorem representative :
    checkAt 10 = true ∧ checkAt 25 = true ∧ checkAt 3523 = true ∧
      checkAt 3554 = true ∧ checkAt 3571 = true ∧ checkAt 3670 = true := by
  decide +kernel

#print axioms representative
end PA194GSChecks
