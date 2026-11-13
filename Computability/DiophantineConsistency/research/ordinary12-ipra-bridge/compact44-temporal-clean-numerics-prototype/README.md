# Exploratory temporal shift and conditional clean bound

`TemporalShiftSplit.reduced` proves in any IΣ₁ model, for n>0, `E % (67*n) = 67*((E/67)%n) + E%67`, with the quotient phase <n and remainder <67. `TemporalCleanNumerics` proves that for r<67, Boolean x,y, and the explicit two-digit target and predecessor equations displayed in the source, the target is zero and the predecessor is at most `Exp.exp 66`. The quotient/remainder are internal model operations, not extrapolated finite checks.

Author-only sessions 81652 and 63988 actually exited 0 with no warnings or `sorryAx`; reports use `propext`, `Classical.choice`, `Quot.sound`. Session 78283 actually exited 1 on a model inequality rewrite; its exact source/log and failure-derived `sorryAx` reports are retained. Both sources use the same fresh author overlay documented in ae249d0592. This is exploratory evidence, not a paired replay or independent artifact audit.

The two temporal rotation digit formulas remain explicit hypotheses; neither their derivation for the graph witnesses nor a clean carry or graph column follows yet. Retained-K binding, machine equivalence and internal iPRA remain open.
