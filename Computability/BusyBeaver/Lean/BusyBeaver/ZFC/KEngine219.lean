import BusyBeaver.ZFC.KTape219
import BusyBeaver.ZFC.KTable219

/-!
The 219's table (K230 labels) keeps K230's register routines: it agrees with K230, patched at the
two changed engine rows, on the 23 engine states they read, so the register lemmas, and with them
the symbolic executor's soundness, hold for it.
-/

namespace SetTheory.BusyBeaver.ZFC.KEngine219

open KZip KRuntimeCore KTableCore KTape219

theorem tm219_agree : Agree tm219 tm230p boxStates := agree_of_agreeB (by decide)

theorem tm219_box : BoxLemmas tm219 := boxLemmas tm219_agree

end SetTheory.BusyBeaver.ZFC.KEngine219
