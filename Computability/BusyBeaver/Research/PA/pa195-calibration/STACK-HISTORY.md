# PA194 source child lookups in a recursive history

`PA194StackHistory.lean` gives an explicit primitive-recursive history whose
stage `n+1` pushes the output of an arbitrary supplied two-argument update
code at stage `n`. A parameterized `translationCode` evaluates that update
against the history. It also gives a primitive-recursive lookup and distance
`n - (j+1)`. In every model of the candidate PRA, the history at stage `n`
returns the value computed at any earlier stage `j<n`; the proof uses open
induction in the candidate PRA language and works for nonstandard `j` and
`n`.

The first and second PA194 source-decoder child codes are strictly smaller
than any positive source code. `modelHistoryFirstChild` and
`modelHistorySecondChild` use that fact and the explicit lookup code to read
the exact child values from the history. `modelTranslationFirstChild` and
`modelTranslationSecondChild` identify them with the corresponding
`translationCode` values. These theorems assume candidate-PRA
certificates for the decoder and pair-projection codes; the theorem
`PRA_has_historyComponents` proves that suitable codes exist, without
serializing them.

These results do not yet define the source-formula update code, prove that
its outputs are well-formed translated formulas, or establish an iPRA
consistency implication. They do not assume IΣ₁. Rebuild using the same
pinned overlays as the surrounding calibration work:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-stack-history.sh
```
