# First-value-two zero-selected file return

`markerFirstTwoZeroBlankReturn` in `PA194FirstTwoZeroReturn.lean` traces the
first non-first marker with first register value two and selected value zero
through the file and back to dense state 7. It assumes the stated intermediate
marker layout, the fixed eight-block file, and a blank tail, and holds in
arbitrary candidate-PRA models. The conclusion retains the exact returned tape
shape and an existential model-valued time.

The four new modules follow the state-59 branch, the state-1 and state-3
scans, the file carry, and the return across the remaining file. Lean compiled
them against retained prerequisite objects; the printed theorem axioms contain
no `sorryAx`. The nested replay wrapper was syntax checked but not run for
these modules. The remaining return to state 24, blank-start reachability, and
the source-frame correspondence are open.
