# PA194 site-25 positive selected-register branch

`PA194TwoPassesPositiveTo6.twoPassesPositiveTo6` composes the common state-4
run with its positive row, assuming only `args 8 = m+1`. All other logical
registers and the complete physical suffix may be arbitrary model elements.
It reaches state 6 with exact tape and clock. `twoPassesPositiveTo7` continues
one literal step to state 7.

`PA194PositiveRewind.positiveRewind` proves a state-7 to state-6 rollback of
an arbitrary model-length unary block in exactly `n+1` steps. It includes the
zero-length case and nonstandard values. The composed theorem
`PA194TwoPassesPositiveRewind.twoPassesPositiveRewind` applies it to the
preceding physical register, retaining its exact transformed tape, model-valued
clock, and entire remaining suffix. The result is an intermediate physical
configuration, not yet a source-frame decrement result or an iPRA derivation.

`check-positive-rewind.sh` recompiles these four modules and the preceding
incremental suffix, with the five audited input overlays documented in
`TWO-HEADER-PASSES.md`. The input overlays require an independently audited
coherent transitive import closure; direct object hashes alone do not provide
one. `PA194_TWO_PASSES_SOURCE_DIR` can specify external sources.
