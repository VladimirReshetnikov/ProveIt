# First-value-two positive marker path to state 16

`markerFirstTwoPositiveBlankTo16` in `PA194FirstTwoPositiveTo16.lean` follows
the first non-first marker to dense state 16 when the first register value is
two, the selected value is positive, and the stated fixed eight-block marker
layout has a blank tail. It applies to arbitrary candidate-PRA models,
including nonstandard values and run times. The final time and tape halves
are existential.

The proof exports the required shape of the left tape after the six file
scans, derives the final right tape's odd parity from the last file block,
and checks the three literal transitions through states 14 and 15 to 16.
The five new modules were compiled against retained prerequisite objects;
the printed theorem axioms contain no `sorryAx`.

The later [state-24 theorem](FIRST-TWO-POSITIVE-TO24.md) completes the
conditional positive return. Source-frame correspondence and blank-start
reachability remain open, so this does not establish either consistency
implication for the literal machine.

A full nested `check-first-two-positive-two-returns.sh` replay also passed
with no `sorryAx`, rebuilding its machine-code chain against retained
prerequisite overlays.
