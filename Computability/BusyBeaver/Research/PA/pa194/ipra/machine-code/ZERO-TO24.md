# PA194 zero-branch physical return

`PA194TwoPassesZeroTo24.twoPassesZeroTo24` composes the previous source-header
and selected-zero results from state 24 all the way back to state 24. It
assumes only that logical register 8 is zero; every other logical register,
physical spare, and the complete file suffix may be an arbitrary element of
any candidate PRA model. The result has left half 1 and an exact named right
half and model-valued clock. The proof uses model-uniform state-12/13 scans and
state-14/15 and controller return lemmas. It does not use a blank-suffix
assumption.

`check-zero-to24.sh` rebuilds the complete suffix of 23 new modules, with the
same five overlays described in `TWO-HEADER-PASSES.md`, and checks the printed
axioms. The supplied overlays must have an independently audited, coherent
transitive import closure; direct object hash checks are not such an audit.
`PA194_TWO_PASSES_SOURCE_DIR` can designate an external source directory.

This theorem gives an exact transformed physical root configuration. It does
not by itself identify the result as site 27, establish all source steps, or
prove a consistency implication in iPRA. A separate site-27 numeric tape
identity is being developed.
