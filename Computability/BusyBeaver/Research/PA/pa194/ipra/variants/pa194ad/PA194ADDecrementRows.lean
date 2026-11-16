import ConPAMachineGenericDecrement
import PA194ADTable
import PA194BModelSteps

set_option maxRecDepth 30000

namespace PA194ADDecrementRows

/-- The exact dense literal rows used by the decrement routine. -/
def rows : ConPA.Machine.GenericDecrement.Rows (PA194BModelSteps.table PA194ADTable.adRows) where
  scanRight := 1
  testMarker := 3
  testValue := 4
  readFollowing := 5
  scanBack := 6
  returnPositive := 7
  clearMarker := 8
  returnZero := 11
  enterBlock := rfl
  scanRightOne := rfl
  enterMarked := rfl
  skipOrdinary := rfl
  readZero := rfl
  readPositive := rfl
  turnAfterZero := rfl
  finishPositiveBlock := rfl
  scanBackOne := rfl
  enterPositiveBlock := rfl
  restoreSeparator := rfl
  restoreOne := rfl
  scanZeroOne := rfl

#print axioms rows
end PA194ADDecrementRows
