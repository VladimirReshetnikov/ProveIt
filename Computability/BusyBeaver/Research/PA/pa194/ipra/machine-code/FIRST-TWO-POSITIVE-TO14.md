# First-value-two positive marker path to state 14

`markerFirstTwoPositiveBlankTo14` in `PA194FirstTwoPositiveTo14.lean` follows
the first non-first marker with first register value two and a positive
selected value to dense state 14. It assumes the stated intermediate marker
layout, the fixed eight-block remaining file, and its blank tail. The result
holds in arbitrary candidate-PRA models, including nonstandard values and
run times, and retains a relation between the final right tape half and the
last file block.

`PA194HalfFileScan.lean` proves a reusable model-length scan of one register
block, preserving the remainder of the file. `PA194HalfFileSix.lean` composes
six concrete physical controller states from 71 to 14. The marker theorem
joins this with the previously checked path to state 71. Lean compiled all
three modules against retained prerequisite objects, and the reported theorem
axioms contain no `sorryAx`.

The later [state-16 theorem](FIRST-TWO-POSITIVE-TO16.md) continues this
conditional path, followed by the [state-24 theorem](FIRST-TWO-POSITIVE-TO24.md).
These results do not show that the blank-start machine reaches the marker
layout or establish a source-frame correspondence or an iPRA consistency
implication.

A full nested `check-first-two-positive-two-returns.sh` replay also passed
with no `sorryAx`, rebuilding its machine-code chain against retained
prerequisite overlays.
