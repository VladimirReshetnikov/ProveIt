# Candidate-PRA code for PA194 universal-rule search

`numericSearch` decodes a natural number as a list of natural-number formula
codes, searches it using the proved primitive-recursive formula shift, and
encodes the optional result. Lean proves this total binary numeric function
primitive recursive, including its default behavior on invalid list codes.

`search_has_PRA_code` obtains an existential finite candidate-PRA `Code 2`
whose standard natural-number evaluation equals the search function.
`search_PRA_code_correct` relates that evaluation to the exact formula chosen
by the list-based Foundation LK universal-rule compiler on actual source
sequents and its membership hypothesis.

All three theorems report `[propext, Classical.choice, Quot.sound]` and no
`sorryAx` in the ordered overlay check, using freshly rebuilt pinned candidate-
PRA code sources from the preceding package. The full nested standalone
script remains untested.

The finite function-code witness is existential, not printed. Its behavior in
nonstandard candidate-PRA models and arithmetic-internal correctness of the
compiler are not proved. This result alone does not establish the PA194
machine calibration or a PA/PRA consistency equivalence.

To rebuild from the repository root, set `IPRA_FOUNDATION_OVERLAY` to the
audited current Foundation object overlay and run
`bash Computability/BusyBeaver/Research/PA/pa194-search-pra-code/check.sh`.
