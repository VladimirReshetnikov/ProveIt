import ConPAMachineGenericIncrement
import PA194SpareSweep
import PA194P5DecrementRows

set_option maxRecDepth 30000

namespace PA194P5IncrementRows

/-- The exact dense rows used to locate a marked register before increment. -/
def increment : ConPA.Machine.GenericIncrement.Rows (PA194P5Data.table) PA194P5DecrementRows.rows where
  start := 2
  afterSeparator := 0
  enterBlock := rfl
  scanOnce := rfl
  skipOrdinary := rfl
  foundMark := rfl

/-- Appending a spare uses one more literal row from the dense table. -/
theorem spare : PA194SpareSweep.Rows (PA194P5Data.table) PA194P5DecrementRows.rows where
  sealTail := rfl

#print axioms increment
#print axioms spare
end PA194P5IncrementRows
