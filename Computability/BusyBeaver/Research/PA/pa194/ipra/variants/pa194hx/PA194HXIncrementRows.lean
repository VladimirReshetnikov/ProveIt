import ConPAMachineGenericIncrement
import PA194SpareSweep
import PA194HXDecrementRows

set_option maxRecDepth 30000

namespace PA194HXIncrementRows

/-- The exact dense rows used to locate a marked register before increment. -/
def increment : ConPA.Machine.GenericIncrement.Rows (PA194HXDispatch.table) PA194HXDecrementRows.rows where
  start := 2
  afterSeparator := 0
  enterBlock := rfl
  scanOnce := rfl
  skipOrdinary := rfl
  foundMark := rfl

/-- Appending a spare uses one more literal row from the dense table. -/
theorem spare : PA194SpareSweep.Rows (PA194HXDispatch.table) PA194HXDecrementRows.rows where
  sealTail := rfl

#print axioms increment
#print axioms spare
end PA194HXIncrementRows
