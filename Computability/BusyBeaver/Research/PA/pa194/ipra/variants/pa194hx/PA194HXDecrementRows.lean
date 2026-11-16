import ConPAMachineGenericDecrement
import PA194HXDispatch

set_option maxRecDepth 30000

namespace PA194HXDecrementRows

/-- The exact dense literal rows used by the decrement routine. -/
def rows : ConPA.Machine.GenericDecrement.Rows (PA194HXDispatch.table) where
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
end PA194HXDecrementRows
