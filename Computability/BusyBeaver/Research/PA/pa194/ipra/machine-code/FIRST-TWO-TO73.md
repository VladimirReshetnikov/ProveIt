# First-value-two marker path to state 73

For the first non-first marker and first register value two,
`markerFirstTwoTo73` in `PA194FirstTwoFirstTo73.lean` follows the literal
transition table through dense states 35, 86, and 73, with exact tape halves
and a specified model-valued clock. The selected value and file contents are
arbitrary, including nonstandard values, in any candidate-PRA model. The
result assumes the explicit intermediate marker layout; it does not require a
blank file tail for this segment.

Lean compiled all three modules against previously checked prerequisite
objects; the printed theorem axioms contain no `sorryAx`. The later [all-selected theorem](FIRST-AT-LEAST-TWO-TO24.md) continues
this conditional path to state 24. Blank-start reachability and the
physical-to-source connection remain open.

A full nested `check-first-two-positive-two-returns.sh` replay also passed
with no `sorryAx`, rebuilding its machine-code chain against retained
prerequisite overlays.
