# PA194 native-table quotient

`PA194Global.lean` proves `PA194LocalQuotient.halts_iff_any_tape`: the exact
unfolded 201-control parent and folded 194-control native table from the PA194
packet halt equivalently at native start 74 and halt 254, for every initial
head position and complete binary tape. The proof combines the finite local
checks, arbitrary-tape simulation, incoming-history invariant, parent-control
totality, and generic deterministic trace theorem.

This is a standard-Lean finite-run theorem, not a theorem in PRA or iPRA and
not a consistency equivalence. For a complete fresh build including the dense
state-map binding, run `../pa194-dense/check.sh` from the repository root.
