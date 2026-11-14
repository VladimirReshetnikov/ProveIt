# First-value-two marker path to state 73

For the first non-first marker and first register value two,
`markerFirstTwoTo73` in `PA194FirstTwoFirstTo73.lean` follows the literal
transition table through dense states 35, 86, and 73, with exact tape halves
and a specified model-valued clock. The selected value and file contents are
arbitrary, including nonstandard values, in any candidate-PRA model. The
result assumes the explicit intermediate marker layout; it does not require a
blank file tail for this segment.

Lean compiled all three modules against previously checked prerequisite
objects; the printed theorem axioms contain no `sorryAx`. The nested wrapper
was syntax checked but not run for this change. Continuing the state-73 path,
reaching the intermediate configuration from blank tape, and connecting the
physical run to the source scheduler remain open.
