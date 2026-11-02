# Exploratory selected graph local NoCarry

`HighTargetDigits` kernel-checks the exact symbolic high-mask list values at 4393 and 5495. `HighMaskLocal` lifts those digits and the high-mask origin into every IΣ₁ model and proves that N>0 and `NoCarry F (highNat*rep(67*8807) N−1)` imply the two exact local `NoCarry (dig 67 F t) (Exp.exp 51−2)` facts.

`FixedGraphLocalNoCarry.graph_local_nocarry` joins this to the previously selected symbolic graph band, its Boolean selector/copy inputs, bounded copy word and zero entering carry. Its assumptions are positive graph coordinates and literal graph zero at fixed symbolic ports with `paramKernel rho`. The independently obtained high-saturation witness is not identified with N: its N-independent global NoCarry conclusion is rewritten using the selected witness's existing `v 0=rep(67*8807) N` relation.

Author-only compiler sessions 43135, 21066 and 29150 actually exited 0 without warnings or `sorryAx`; natural target list reports use `propext` and model reports use `propext`, `Classical.choice`, `Quot.sound`. Session 55569 exited 1 with list-simp failures and linter warnings; its source/log and failure-derived `sorryAx` reports are retained. All compiles use the same author overlay and dependencies recorded in 9403a827c7, 9c585b5828 and db88bbcec8. This is exploratory evidence, not a paired replay or independent artifact audit.

The local decoder conclusion and row/machine semantics are not asserted in this packet. Retained K/port-byte binding, global machine equivalence and internal iPRA remain open.
