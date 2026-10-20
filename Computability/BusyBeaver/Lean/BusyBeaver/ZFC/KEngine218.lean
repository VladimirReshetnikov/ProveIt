import BusyBeaver.ZFC.KTape219
import BusyBeaver.ZFC.KTable218

/-!
The 218's table (K230 labels) keeps K230's register routines: it agrees with K230, patched at the
two engine rows the 219 changed (the 218 keeps them), on the 23 engine states they read, so the register lemmas, and with them
the symbolic executor's soundness, hold for it.
-/

namespace SetTheory.BusyBeaver.ZFC.KEngine218

open KZip KRuntimeCore KTableCore KTape219

theorem tm218_agree : Agree tm218 tm230p boxStates := agree_of_agreeB (by decide)

theorem tm218_box : BoxLemmas tm218 := boxLemmas tm218_agree

end SetTheory.BusyBeaver.ZFC.KEngine218
